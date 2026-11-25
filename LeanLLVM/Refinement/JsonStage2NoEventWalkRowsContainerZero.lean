/-
The no-event walk's depth-zero container row: the empty pair at `%sp = 0` is
terminal, not a continuation.

At the top level the container route does not grow the stack.  The head's
dispatch reads `[` or `{`, `if.end45.peel`/`if.end19` take their zero-depth arms
(nothing is stored), and the empty pair's counts reach `after_value` with
`%sp.4 = 0`.  There `%cmp355` holds, `if.then357` dispatches on
`%cmp358 = (%k.6 < %nep)` and the walk either refuses the trailing input
(`if.then360`'s zero stores) or accepts.  `Stage2NoEventWalkCycleSrc` requires a
non-zero depth on both sides, so no `cont` row exists for a top-level `[]`/`{}`:
the row is `Stage2NoEventWalkRow.terminal`.

The module supplies the nine `[]` blocks and the eleven `{}` blocks (`if.then81`'s
counts included) as routes that stop at `after_value`, at prices nine and
eleven; the `after_value` depth-zero dispatch's own two blocks are added and
costed in the terminals (eleven and thirteen), together with the two terminal
exits at `k + 2` (`Stage2NoEventWalkExit.accept` when `k + 2 = K.nep`, `refuse`
when `k + 2 < K.nep`).  A route's price is claimed only at a strictly bounded
closer index, by its own `…ZeroRoute_price` corollary, so the accept branch (at
`k + 2 = K.nep`) never exhibits an entry there.  The terminal tier's
acceptance/refusal words (`hreport`) are the caller's post evidence, not the
route's; the routes supply every other field of TerminalA's constructors.
-/
import LeanLLVM.Refinement.JsonStage2NoEventWalkRowsBrace
import LeanLLVM.Refinement.JsonStage2NoEventWalkTerminalA
import LeanLLVM.Refinement.JsonStage2NoEventWalkValue

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 1600000
set_option pp.maxSteps 200000

namespace LeanLLVM.Refinement

open LeanLLVM
open LeanLLVM.JSON
open LeanLLVM.Refinement.JsonStage2NoEventIR
open LeanLLVM.Refinement.JsonEntryIR (readLanes32)
open LeanLLVM.Refinement.BlockEval

/-! ### `if.then357`

The block has no instructions: it is the terminal dispatch's test on `%cmp358`,
to the refusal's zero-store block or to the acceptance. -/

/-- `if.then357`, pinned. -/
def ifThen357Block : Block :=
  { name := "if.then357", instrs := [],
    term := Term.condbr (Operand.reg "%cmp358") "if.then360" "accept" }

theorem ifThen357Block_find :
    stage2NoEventBody.findBlock "if.then357" = some ifThen357Block := by
  decide

/-- **`if.then357` at a trailing entry**: the refusal arm, to `if.then360`. -/
theorem link_ifThen357_true {calls : Calls} {K : Stage2NoEventWalkCarry}
    {mem : Mem} {s : State}
    (h : Stage2NoEventWalkInv K mem s) (hpc : s.pc = "if.then357")
    (hc : lookupName s.env "%cmp358" = some (.int 1 1)) :
    Stage2NoEventWalkLink calls K mem s K
      (stage2NoEventWalkNext s.env s "if.then360") := by
  have hcode : denoteCode calls ifThen357Block.instrs (stateAt s.env s) =
      some (stateAt s.env s) := by
    simp only [ifThen357Block, denoteCode_nil]
  exact stage2NoEventWalkLink_condbr_true (env' := s.env)
    h (by rw [hpc]; exact ifThen357Block_find) hcode rfl hc

/-- **`if.then357` at the last entry**: the acceptance arm, to `accept`. -/
theorem link_ifThen357_false {calls : Calls} {K : Stage2NoEventWalkCarry}
    {mem : Mem} {s : State}
    (h : Stage2NoEventWalkInv K mem s) (hpc : s.pc = "if.then357")
    (hc : lookupName s.env "%cmp358" = some (.int 1 0)) :
    Stage2NoEventWalkLink calls K mem s K
      (stage2NoEventWalkNext s.env s "accept") := by
  have hcode : denoteCode calls ifThen357Block.instrs (stateAt s.env s) =
      some (stateAt s.env s) := by
    simp only [ifThen357Block, denoteCode_nil]
  exact stage2NoEventWalkLink_condbr_false (env' := s.env)
    h (by rw [hpc]; exact ifThen357Block_find) hcode rfl hc

/-! ### The depth-zero `after_value` dispatch

The `phi` run is the shared seven-cell one; the two tests are the same
instruction list, but at `%sp.4 = 0` the depth test holds and `%cmp358` carries
the trailing-entry test.  The dispatch's cell list is `%cmp358`'s value over
`%cmp355 = 1`. -/

/-- The depth-zero dispatch's two cells, newest first. -/
def afterValueZeroDispatchCells (c : BitVec 1) : List (String × Value) :=
  [("%cmp358", .int 1 c), ("%cmp355", .int 1 1)]

/-- **`icmp ult` is zero at or above the `Nat` order.** -/
theorem stage2NoEventICmp_ult_zero {w : Nat} {x y : Nat}
    (hx : x < 2 ^ w) (hy : y < 2 ^ w) (h : ¬ x < y) :
    evalICmp .ult (BitVec.ofNat w x) (BitVec.ofNat w y) = 0 := by
  have hx' : (BitVec.ofNat w x).toNat = x := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx]
  have hy' : (BitVec.ofNat w y).toNat = y := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hy]
  have hult : BitVec.ult (BitVec.ofNat w x) (BitVec.ofNat w y) = false := by
    rw [BitVec.ult, hx', hy']
    simp only [decide_eq_false_iff_not]
    omega
  simp only [evalICmp, hult]
  rfl

/-- **The depth test and the trailing-entry test at `%sp.4 = 0`.** -/
theorem afterValue_zero_dispatch_denote (calls : Calls) (env : Env) (s : State)
    {k nep : Nat}
    (hk : lookupName env "%k.6" = some (.int 64 (BitVec.ofNat 64 k)))
    (hnep : lookupName env "%nep" = some (.int 64 (BitVec.ofNat 64 nep)))
    (hsp : lookupName env "%sp.4" = some (.int 32 (BitVec.ofNat 32 0))) :
    denoteCode calls afterValueDispatchInstrs (stateAt env s) =
      some (stateAt
        (cells (afterValueZeroDispatchCells
          (evalICmp .ult (BitVec.ofNat 64 k) (BitVec.ofNat 64 nep))) env) s) := by
  rw [afterValueDispatchInstrs]
  rw [stage2NoEventWalk_denote_icmp_imm (calls := calls) (env := env) (s := s)
    (d := "%cmp355") (a := "%sp.4") (p := .eq) (w := 32)
    (x := BitVec.ofNat 32 0) (c := BitVec.ofNat 32 0) hsp
    (is := [Instr.icmp "%cmp358" IPred.ult 64 (Operand.reg "%k.6")
      (Operand.reg "%nep")])]
  rw [show evalICmp .eq (BitVec.ofNat 32 0) (BitVec.ofNat 32 0) = 1 from by decide]
  rw [stage2NoEventWalk_denote_icmp_reg (calls := calls)
    (env := ("%cmp355", Value.int 1 (1 : BitVec 1)) :: env) (s := s)
    (d := "%cmp358") (a := "%k.6") (b := "%nep") (p := IPred.ult) (w := 64)
    (x := BitVec.ofNat 64 k) (y := BitVec.ofNat 64 nep) ?_ ?_ (is := [])]
  · simp only [afterValueZeroDispatchCells, cells, denoteCode_nil]
  · rw [lookupName_cons_ne _ _ (by decide)]; exact hk
  · rw [lookupName_cons_ne _ _ (by decide)]; exact hnep

/-- **The `after_value` block at `%sp.4 = 0`**: the shared `phi` run at the
`close_arr`/`close_obj` edge's values, then the two tests. -/
theorem afterValue_zero_denote {calls : Calls} {env : Env} {s : State} {p : String}
    {fr k alen arena terms tok nep : Nat}
    (hpre : s.pre = some p)
    (hsel : PhiSelects (stateAt env s) p afterValuePhiSpecs
      [("%frame.6", .int 8 (BitVec.ofNat 8 fr)),
       ("%sp.4", .int 32 (BitVec.ofNat 32 0)),
       ("%k.6", .int 64 (BitVec.ofNat 64 k)),
       ("%alen.8", .int 64 (BitVec.ofNat 64 alen)),
       ("%arena.10", .int 64 (BitVec.ofNat 64 arena)),
       ("%terms.8", .int 64 (BitVec.ofNat 64 terms)),
       ("%tokens.8", .int 64 (BitVec.ofNat 64 tok))])
    (hnep : lookupName env "%nep" = some (.int 64 (BitVec.ofNat 64 nep))) :
    denoteCode calls afterValueBlock.instrs (stateAt env s) =
      some (stateAt
        (cells (afterValueZeroDispatchCells
          (evalICmp .ult (BitVec.ofNat 64 k) (BitVec.ofNat 64 nep)))
          (cells (afterValuePhiCells fr 0 k alen arena terms tok) env)) s) := by
  have hphi := afterValue_phi_denote (calls := calls) (s := s) (env := env)
    (p := p) (fr := fr) (sp := 0) (k := k) (alen := alen) (arena := arena)
    (terms := terms) (tok := tok) hpre hsel
  rw [afterValueBlock]
  rw [denoteCode_append_apply (a := afterValuePhiInstrs)
    (b := afterValueDispatchInstrs) (s := stateAt env s)
    (s' := stateAt (cells (afterValuePhiCells fr 0 k alen arena terms tok) env) s)
    hphi (by decide)]
  rw [afterValue_zero_dispatch_denote (calls := calls)
    (env := cells (afterValuePhiCells fr 0 k alen arena terms tok) env) (s := s)
    (k := k) (nep := nep)
    (by exact cells_lookup_of_mem _ _ (by simp [afterValuePhiCells]) (by
      rw [show (afterValuePhiCells fr 0 k alen arena terms tok).map (·.1) =
        ["%tokens.8", "%terms.8", "%arena.10", "%alen.8", "%k.6", "%sp.4",
          "%frame.6"] from rfl]
      decide))
    (by
      rw [cells_lookup_of_notin _ _ (by
        rw [show (afterValuePhiCells fr 0 k alen arena terms tok).map (·.1) =
          ["%tokens.8", "%terms.8", "%arena.10", "%alen.8", "%k.6", "%sp.4",
            "%frame.6"] from rfl]
        decide)]
      exact hnep)
    (by exact cells_lookup_of_mem _ _ (by simp [afterValuePhiCells]) (by
      rw [show (afterValuePhiCells fr 0 k alen arena terms tok).map (·.1) =
        ["%tokens.8", "%terms.8", "%arena.10", "%alen.8", "%k.6", "%sp.4",
          "%frame.6"] from rfl]
      decide))]

/-- **The `[]` edge's `after_value` link at the zero depth**: the `phi` run from
`close_arr`, the two tests, and the true arm to `if.then357`. -/
theorem link_afterValue_zero_close_arr {calls : Calls}
    {K : Stage2NoEventWalkCarry} {mem : Mem} {s : State}
    {fr k alen arena terms tok nep : Nat}
    (h : Stage2NoEventWalkInv K mem s) (hpc : s.pc = "after_value")
    (hpre : s.pre = some "close_arr")
    (hframe : lookupName s.env "%frame.4" = some (.int 8 (BitVec.ofNat 8 fr)))
    (hsp : lookupName s.env "%sp.3" = some (.int 32 (BitVec.ofNat 32 0)))
    (hk : lookupName s.env "%k.5" = some (.int 64 (BitVec.ofNat 64 k)))
    (halen : lookupName s.env "%alen.7" = some (.int 64 (BitVec.ofNat 64 alen)))
    (harena : lookupName s.env "%arena.9" = some (.int 64 (BitVec.ofNat 64 arena)))
    (hterms : lookupName s.env "%terms.7" = some (.int 64 (BitVec.ofNat 64 terms)))
    (htok : lookupName s.env "%tokens.7" = some (.int 64 (BitVec.ofNat 64 tok)))
    (hnep : lookupName s.env "%nep" = some (.int 64 (BitVec.ofNat 64 nep))) :
    Stage2NoEventWalkLink calls K mem s K
      (stage2NoEventWalkNext
        (cells (afterValueZeroDispatchCells
          (evalICmp .ult (BitVec.ofNat 64 k) (BitVec.ofNat 64 nep)))
          (cells (afterValuePhiCells fr 0 k alen arena terms tok) s.env))
        s "if.then357") := by
  have hsel : PhiSelects (stateAt s.env s) "close_arr" afterValuePhiSpecs
      [("%frame.6", .int 8 (BitVec.ofNat 8 fr)),
       ("%sp.4", .int 32 (BitVec.ofNat 32 0)),
       ("%k.6", .int 64 (BitVec.ofNat 64 k)),
       ("%alen.8", .int 64 (BitVec.ofNat 64 alen)),
       ("%arena.10", .int 64 (BitVec.ofNat 64 arena)),
       ("%terms.8", .int 64 (BitVec.ofNat 64 terms)),
       ("%tokens.8", .int 64 (BitVec.ofNat 64 tok))] := by
    refine PhiSelects.cons (op := .reg "%frame.4") (by decide) ?_
      (PhiSelects.cons (op := .reg "%sp.3") (by decide) ?_
        (PhiSelects.cons (op := .reg "%k.5") (by decide) ?_
          (PhiSelects.cons (op := .reg "%alen.7") (by decide) ?_
            (PhiSelects.cons (op := .reg "%arena.9") (by decide) ?_
              (PhiSelects.cons (op := .reg "%terms.7") (by decide) ?_
                (PhiSelects.cons (op := .reg "%tokens.7") (by decide) ?_
                  PhiSelects.nil))))))
    all_goals
      simp only [stateAt, evalOperand, hframe, hsp, hk, halen, harena, hterms, htok]
  have hcode := afterValue_zero_denote (calls := calls) (env := s.env) (s := s)
    (p := "close_arr") hpre hsel hnep
  refine stage2NoEventWalkLink_condbr_true
    (env' := cells (afterValueZeroDispatchCells
      (evalICmp .ult (BitVec.ofNat 64 k) (BitVec.ofNat 64 nep)))
      (cells (afterValuePhiCells fr 0 k alen arena terms tok) s.env))
    h (by rw [hpc]; exact afterValueBlock_find) hcode rfl ?_
  simp only [afterValueZeroDispatchCells, cells]
  rw [lookupName_cons_ne _ _ (by decide)]
  exact lookupName_cons_self _ _ _

/-- **The `{}` edge's `after_value` link at the zero depth**: the `phi` run from
`close_obj`, the two tests, and the true arm to `if.then357`.  The `close_obj`
edge's frame is the constant zero and its depth word is `%dec`. -/
theorem link_afterValue_zero_close_obj {calls : Calls}
    {K : Stage2NoEventWalkCarry} {mem : Mem} {s : State}
    {k alen arena terms tok nep : Nat} {dec : BitVec 32}
    (h : Stage2NoEventWalkInv K mem s) (hpc : s.pc = "after_value")
    (hpre : s.pre = some "close_obj")
    (hdec : lookupName s.env "%dec" = some (.int 32 dec))
    (hdec0 : dec = BitVec.ofNat 32 0)
    (hk : lookupName s.env "%k.4" = some (.int 64 (BitVec.ofNat 64 k)))
    (halen : lookupName s.env "%alen.6" = some (.int 64 (BitVec.ofNat 64 alen)))
    (harena : lookupName s.env "%arena.8" = some (.int 64 (BitVec.ofNat 64 arena)))
    (hterms : lookupName s.env "%terms.6" = some (.int 64 (BitVec.ofNat 64 terms)))
    (htok : lookupName s.env "%tokens.6" = some (.int 64 (BitVec.ofNat 64 tok)))
    (hnep : lookupName s.env "%nep" = some (.int 64 (BitVec.ofNat 64 nep))) :
    Stage2NoEventWalkLink calls K mem s K
      (stage2NoEventWalkNext
        (cells (afterValueZeroDispatchCells
          (evalICmp .ult (BitVec.ofNat 64 k) (BitVec.ofNat 64 nep)))
          (cells (afterValuePhiCells 0 0 k alen arena terms tok) s.env))
        s "if.then357") := by
  have hsel : PhiSelects (stateAt s.env s) "close_obj" afterValuePhiSpecs
      [("%frame.6", .int 8 (BitVec.ofNat 8 0)),
       ("%sp.4", .int 32 (BitVec.ofNat 32 0)),
       ("%k.6", .int 64 (BitVec.ofNat 64 k)),
       ("%alen.8", .int 64 (BitVec.ofNat 64 alen)),
       ("%arena.10", .int 64 (BitVec.ofNat 64 arena)),
       ("%terms.8", .int 64 (BitVec.ofNat 64 terms)),
       ("%tokens.8", .int 64 (BitVec.ofNat 64 tok))] := by
    refine PhiSelects.cons (op := .imm (.int 8 (BitVec.ofNat 8 0))) (by decide) ?_
      (PhiSelects.cons (op := .reg "%dec") (by decide) ?_
        (PhiSelects.cons (op := .reg "%k.4") (by decide) ?_
          (PhiSelects.cons (op := .reg "%alen.6") (by decide) ?_
            (PhiSelects.cons (op := .reg "%arena.8") (by decide) ?_
              (PhiSelects.cons (op := .reg "%terms.6") (by decide) ?_
                (PhiSelects.cons (op := .reg "%tokens.6") (by decide) ?_
                  PhiSelects.nil))))))
    all_goals
      simp only [stateAt, evalOperand, Const.toValue, hdec, hdec0, hk, halen,
        harena, hterms, htok]
  have hcode := afterValue_zero_denote (calls := calls) (env := s.env) (s := s)
    (p := "close_obj") hpre hsel hnep
  refine stage2NoEventWalkLink_condbr_true
    (env' := cells (afterValueZeroDispatchCells
      (evalICmp .ult (BitVec.ofNat 64 k) (BitVec.ofNat 64 nep)))
      (cells (afterValuePhiCells 0 0 k alen arena terms tok) s.env))
    h (by rw [hpc]; exact afterValueBlock_find) hcode rfl ?_
  simp only [afterValueZeroDispatchCells, cells]
  rw [lookupName_cons_ne _ _ (by decide)]
  exact lookupName_cons_self _ _ _

/-! ### `close_obj` at the zero depth

The six `phi`s and the decrement are the committed ones; at `%dec = 0` the test
holds and the block goes straight to `after_value` with no pop. -/

/-- **`close_obj`'s zero-depth arm**: the six-`phi` run, the decrement, and the
true arm to `after_value`. -/
theorem link_closeObj_zero {calls : Calls} {K : Stage2NoEventWalkCarry}
    {mem : Mem} {s : State} {sp2 : BitVec 32} {k4 alen arena terms6 toks : BitVec 64}
    (h : Stage2NoEventWalkInv K mem s) (hpc : s.pc = "close_obj")
    (hpre : s.pre = some "if.then81")
    (hsp2 : lookupName s.env "%inc24" = some (.int 32 sp2))
    (hk4 : lookupName s.env "%inc82" = some (.int 64 k4))
    (halen : lookupName s.env "%alen.0.ph1405" = some (.int 64 alen))
    (harena : lookupName s.env "%arena.0.ph1406" = some (.int 64 arena))
    (hterms : lookupName s.env "%add85" = some (.int 64 terms6))
    (htoks : lookupName s.env "%inc84" = some (.int 64 toks))
    (hdec : (sp2 + BitVec.ofNat 32 4294967295).toNat = 0) :
    Stage2NoEventWalkLink calls K mem s K
      (stage2NoEventWalkNext
        (cells (closeObjTail sp2 ++
          braceCloseObjCells sp2 k4 alen arena terms6 toks) s.env) s "after_value") := by
  have h1 := closeObjPhi_denote (calls := calls) (env := s.env) (s := s)
    hpre hsp2 hk4 halen harena hterms htoks
  have h2 := braceCloseObjRest_denote (calls := calls) (env := s.env) (s := s)
    (sp2 := sp2) (k4 := k4) (alen := alen) (arena := arena)
    (terms6 := terms6) (toks := toks)
  have h0 : sp2 + BitVec.ofNat 32 4294967295 = BitVec.ofNat 32 0 :=
    BitVec.eq_of_toNat_eq (by
      rw [BitVec.toNat_ofNat]
      exact hdec)
  have hbit : evalICmp .eq (sp2 + BitVec.ofNat 32 4294967295) (BitVec.ofNat 32 0)
      = (1 : BitVec 1) := by
    rw [h0]
    decide
  refine stage2NoEventWalkLink_condbr_true
    (env' := cells (closeObjTail sp2 ++
      braceCloseObjCells sp2 k4 alen arena terms6 toks) s.env)
    h (by rw [hpc]; exact closeObjBlock_find) ?_ rfl ?_
  · rw [closeObj_split,
      denoteCode_append_apply (a := closeObjPhiInstrs) (b := closeObjRest) h1 (by decide)]
    exact h2
  · rw [cells_append]
    show lookupName
      (("%tobool342.not", .int 1 (evalICmp .eq
          (sp2 + BitVec.ofNat 32 4294967295) (BitVec.ofNat 32 0))) ::
        ("%dec", .int 32 (sp2 + BitVec.ofNat 32 4294967295)) ::
          cells (braceCloseObjCells sp2 k4 alen arena terms6 toks) s.env)
      "%tobool342.not" = some (.int 1 1)
    rw [lookupName_cons_self, hbit]

/-! ### The `[]` route to the depth-zero endpoint

Nine blocks: the head's dispatch to `if.then35.peel`, the true `if.end45.peel`,
`if.end51.peel`, the `]` read at `if.end327.peel`, the `]` count at
`if.then334`, and `close_arr`'s zero-depth arm to `after_value`.  No stack write
or read occurs.  The route stops at `after_value` in nine blocks; its price is
stated separately, at a strictly bounded closer index. -/

/-- **The `[]` zero-depth route**, as a nine-block segment to `after_value`. -/
theorem stage2NoEventWalkBracketZeroRoute {calls : Calls}
    {K : Stage2NoEventWalkCarry} {mem : Mem} {k : Nat} {s : State}
    (h : Stage2NoEventWalkHead K mem k s)
    (htrace : Stage2NoEventWalkTrace K)
    {lane : Nat} {byte : UInt8}
    (hk : K.ent[k]? = some lane) (hbs : K.bs[lane]? = some byte) (hb : byte.toNat = 91)
    {next : Nat} {nextByte : UInt8}
    (hbs1 : K.bs[next]? = some nextByte)
    (hb1 : nextByte.toNat = 93)
    (hspZ : lookupName s.env "%sp.0.ph1403" =
      some (.int 32 (BitVec.ofNat 32 0)))
    (hkbound : k + 2 ≤ K.nep) (hk63 : k + 3 < 2 ^ 63)
    {bs4 : List UInt8}
    (hlane : readBytes s.mem (K.ep + (BitVec.ofNat 64 (k + 1)).toNat * 4) 4 = some bs4)
    (hval4lt : bytesToNat bs4 < 2 ^ 32)
    (hbyte1 : readBytes s.mem
      (K.b + (BitVec.signExtend 64 (BitVec.ofNat 64 (bytesToNat bs4))).toNat) 1
      = some [nextByte]) :
    ∃ sE, Stage2NoEventWalkSegment calls mem K s
        { K with tok := K.tok + 2, terms := K.terms + 7 } sE 9 ∧
      sE.pc = "after_value" ∧ sE.pre = some "close_arr" ∧
      lookupName sE.env "%frame.4" = some (.int 8 (BitVec.ofNat 8 1)) ∧
      lookupName sE.env "%sp.3" = some (.int 32 (BitVec.ofNat 32 0)) ∧
      lookupName sE.env "%k.5" = some (.int 64 (BitVec.ofNat 64 (k + 2))) ∧
      lookupName sE.env "%alen.7" = some (.int 64 (BitVec.ofNat 64 K.arena.length)) ∧
      lookupName sE.env "%arena.9" = some (.int 64 (BitVec.ofNat 64 K.arenaWord)) ∧
      lookupName sE.env "%terms.7" =
        some (.int 64 (BitVec.ofNat 64 K.terms + BitVec.ofNat 64 7)) ∧
      lookupName sE.env "%tokens.7" =
        some (.int 64 (BitVec.ofNat 64 K.tok + BitVec.ofNat 64 2)) ∧
      lookupName sE.env "%nep" = some (.int 64 (BitVec.ofNat 64 K.nep)) ∧
      sE.mem = s.mem ∧
      Stage2NoEventWalkBaseLookups
        { K with tok := K.tok + 2, terms := K.terms + 7 } sE ∧
      Stage2NoEventWalkTrace
        { K with tok := K.tok + 2, terms := K.terms + 7 } := by
  classical
  have h3 : lookupName s.env "%3" = some (.int 8 (BitVec.ofNat 8 91)) :=
    h.bracketCell hk hbs hb
  have hstk : lookupName s.env "%stk" = some (.ptr K.stk) := h.stk
  have hnep : lookupName s.env "%nep" = some (.int 64 (BitVec.ofNat 64 K.nep)) := h.nepI
  have hep : lookupName s.env "%ep" = some (.ptr K.ep) := h.epPtr
  have hbPtr : lookupName s.env "%b" = some (.ptr K.b) := h.bPtr
  have hincH : lookupName s.env "%inc.peel" =
      some (.int 64 (BitVec.ofNat 64 (k + 1))) := by
    obtain ⟨-, -, -, -, -, -, -, -, hinc, -, -, -⟩ := h.laneRead
    exact hinc
  let sp3 : BitVec 32 := BitVec.ofNat 32 0
  have hzero : sp3.toNat = 0 := rfl
  have hle : sp3.toNat ≤ 519 := by decide
  have hincLt : (BitVec.ofNat 64 (k + 1)).toNat < 2 ^ 63 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : k + 1 < 2 ^ 64)]
    omega
  have hult : BitVec.ult (BitVec.ofNat 64 (k + 1)) (BitVec.ofNat 64 K.nep) = true := by
    refine BitVec.ult_iff_toNat_lt.2 ?_
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : k + 1 < 2 ^ 64),
      Nat.mod_eq_of_lt h.inv.nepLt]
    omega
  have hguard : K.tok + 2 ≤ K.n :=
    Stage2NoEventWalkInv.tok_add_le h.inv h.count hkbound
  -- the nine blocks
  let S1 := stage2NoEventWalkNext (("%Pivot6", .int 1 0) :: s.env) s "NodeBlock"
  let S2 := stage2NoEventWalkNext (("%Pivot", .int 1 1) :: S1.env) S1 "LeafBlock1"
  let S3 := stage2NoEventWalkNext (("%SwitchLeaf2", .int 1 1) :: S2.env) S2
    "if.then35.peel"
  let S4 := stage2NoEventWalkNext (("%exitcond.peel", .int 1 0) :: S3.env) S3
    "if.end45.peel"
  let S5 := stage2NoEventWalkNext (("%tobool46.not.peel", .int 1 1) :: S4.env) S4
    "if.end51.peel"
  let S6 := stage2NoEventWalkNext (("%cmp319.not.peel", .int 1 1) :: S5.env) S5
    "if.end327.peel"
  let S7 := bracketEntry S6 (BitVec.ofNat 64 (k + 1)) K.ep K.b bs4 [nextByte]
  let S8 := bracketCounts S7 sp3 (BitVec.ofNat 64 k) (BitVec.ofNat 64 K.tok)
    (BitVec.ofNat 64 K.terms)
  let S9 := bracketArrValue S8 sp3 (BitVec.ofNat 64 (k + 2))
    (BitVec.ofNat 64 K.arena.length) (BitVec.ofNat 64 K.arenaWord)
    (BitVec.ofNat 64 K.terms + BitVec.ofNat 64 7)
    (BitVec.ofNat 64 K.tok + BitVec.ofNat 64 2)
  have L1 : Stage2NoEventWalkLink calls K mem s K S1 :=
    link_nodeBlock5_false h.inv h.pc h3 (by decide)
  have h3a : lookupName (("%Pivot6", .int 1 0) :: s.env) "%3"
      = some (.int 8 (BitVec.ofNat 8 91)) :=
    lookupName_cons_other _ _ _ (by decide) h3
  have L2 : Stage2NoEventWalkLink calls K mem S1 K S2 :=
    link_nodeBlock_true L1.inv' (by simp only [S1, stage2NoEventWalkNext]) h3a (by decide)
  have h3b : lookupName (("%Pivot", .int 1 1) :: ("%Pivot6", .int 1 0) :: s.env) "%3"
      = some (.int 8 (BitVec.ofNat 8 91)) :=
    lookupName_cons_other _ _ _ (by decide) h3a
  have L3 : Stage2NoEventWalkLink calls K mem S2 K S3 :=
    link_leafBlock1_true L2.inv' (by simp only [S2, S1, stage2NoEventWalkNext])
      h3b (by decide)
  have hsp3 : lookupName S3.env "%sp.0.ph1403" =
      some (.int 32 (BitVec.ofNat 32 0)) := by
    simp only [S3, S2, S1, stage2NoEventWalkNext]
    exact lookupName_cons_other _ _ _ (by decide)
      (lookupName_cons_other _ _ _ (by decide)
        (lookupName_cons_other _ _ _ (by decide) hspZ))
  have L4 : Stage2NoEventWalkLink calls K mem S3 K S4 :=
    link_ifThen35peel L3.inv' (by simp only [S3, S2, S1, stage2NoEventWalkNext])
      hsp3 hle
  have hsp4 : lookupName S4.env "%sp.0.ph1403" =
      some (.int 32 (BitVec.ofNat 32 0)) := by
    simp only [S4, S3, S2, S1, stage2NoEventWalkNext]
    exact lookupName_cons_other _ _ _ (by decide)
      (lookupName_cons_other _ _ _ (by decide)
        (lookupName_cons_other _ _ _ (by decide)
          (lookupName_cons_other _ _ _ (by decide) hspZ)))
  have L5 : Stage2NoEventWalkLink calls K mem S4 K S5 :=
    link_ifEnd45peel_true L4.inv' (by simp only [S4, S3, S2, S1, stage2NoEventWalkNext])
      hsp4 hzero
  have hinc5 : lookupName S5.env "%inc.peel"
      = some (.int 64 (BitVec.ofNat 64 (k + 1))) := by
    simp only [S5, S4, S3, S2, S1, stage2NoEventWalkNext]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact hincH
  have hnep5 : lookupName S5.env "%nep"
      = some (.int 64 (BitVec.ofNat 64 K.nep)) := by
    simp only [S5, S4, S3, S2, S1, stage2NoEventWalkNext]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact hnep
  have L6 : Stage2NoEventWalkLink calls K mem S5 K S6 :=
    link_ifEnd51peel L5.inv' (by simp only [S5, S4, S3, S2, S1, stage2NoEventWalkNext])
      hinc5 hnep5 hult
  have hinc6 : lookupName S6.env "%inc.peel"
      = some (.int 64 (BitVec.ofNat 64 (k + 1))) := by
    simp only [S6, S5, S4, S3, S2, S1, stage2NoEventWalkNext]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact hincH
  have hep6 : lookupName S6.env "%ep" = some (.ptr K.ep) := by
    simp only [S6, S5, S4, S3, S2, S1, stage2NoEventWalkNext]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact hep
  have hb6 : lookupName S6.env "%b" = some (.ptr K.b) := by
    simp only [S6, S5, S4, S3, S2, S1, stage2NoEventWalkNext]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact hbPtr
  have L7 : Stage2NoEventWalkLink calls K mem S6 K S7 :=
    link_ifEnd327peel L6.inv' rfl hinc6 hep6 hb6 hincLt
      (by simpa only [S6, S5, S4, S3, S2, S1, stage2NoEventWalkNext] using hlane)
      hval4lt
      (by simpa only [S6, S5, S4, S3, S2, S1, stage2NoEventWalkNext] using hbyte1)
      (by rw [stage2NoEventWalkBytesToNat_single]; exact hb1)
  have hsp7 : lookupName S7.env "%sp.0.ph1403" =
      some (.int 32 (BitVec.ofNat 32 0)) := by
    simp only [S7, bracketEntry, stage2NoEventWalkNext]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact hspZ
  have hk7 : lookupName S7.env "%k.0.ph1404"
      = some (.int 64 (BitVec.ofNat 64 k)) := by
    simp only [S7, bracketEntry, stage2NoEventWalkNext]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact h.kEq
  have htr7 : lookupName S7.env "%terms.0.ph1407"
      = some (.int 64 (BitVec.ofNat 64 K.terms)) := by
    simp only [S7, bracketEntry, stage2NoEventWalkNext]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact h.termsPhi
  have htok7 : lookupName S7.env "%tokens.0.ph1408"
      = some (.int 64 (BitVec.ofNat 64 K.tok)) := by
    simp only [S7, bracketEntry, stage2NoEventWalkNext]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact h.tokensPhi
  have L8 : Stage2NoEventWalkLink calls K mem S7
      { K with tok := K.tok + 2, terms := K.terms + 7 } S8 :=
    link_ifThen334 L7.inv'
      (by simp only [S7, bracketEntry, stage2NoEventWalkNext]) rfl
      hsp7 hk7 htr7 htok7 hguard
  have hpre8 : S8.pre = some "if.then334" := rfl
  have hnd8 : ((ifThen334AllCells sp3 (BitVec.ofNat 64 k) (BitVec.ofNat 64 K.tok)
      (BitVec.ofNat 64 K.terms)).map (·.1)).Nodup := by
    simp only [ifThen334AllCells, ifThen334Cells, ifThen334PhiCells,
      List.map_append, List.map_cons, List.map_nil]
    decide
  have hsp8 : lookupName S8.env "%sp.0.lcssa1096.wide" =
      some (.int 32 (BitVec.ofNat 32 0)) := by
    simp only [S8, bracketCounts, stage2NoEventWalkNext]
    exact stage2NoEventWalkCells_some (cs := ifThen334AllCells sp3 (BitVec.ofNat 64 k)
      (BitVec.ofNat 64 K.tok) (BitVec.ofNat 64 K.terms))
      (n := "%sp.0.lcssa1096.wide") (v := .int 32 sp3)
      (by simp only [ifThen334AllCells, ifThen334Cells, ifThen334PhiCells,
        List.mem_append, List.mem_cons, List.not_mem_nil, or_false]; tauto) hnd8
  have hinc335 : lookupName S8.env "%inc335"
      = some (.int 64 (BitVec.ofNat 64 (k + 2))) := by
    have hc : lookupName S8.env "%inc335"
        = some (.int 64 (BitVec.ofNat 64 k + BitVec.ofNat 64 2)) := by
      simp only [S8, bracketCounts, stage2NoEventWalkNext]
      exact stage2NoEventWalkCells_some (cs := ifThen334AllCells sp3
        (BitVec.ofNat 64 k) (BitVec.ofNat 64 K.tok) (BitVec.ofNat 64 K.terms))
        (n := "%inc335") (v := .int 64 (BitVec.ofNat 64 k + BitVec.ofNat 64 2))
        (by simp only [ifThen334AllCells, ifThen334Cells, ifThen334PhiCells,
          List.mem_append, List.mem_cons, List.not_mem_nil, or_false]; tauto) hnd8
    simpa only [stage2NoEventWalkOfNat_add] using hc
  have halen8 : lookupName S8.env "%alen.0.ph1405"
      = some (.int 64 (BitVec.ofNat 64 K.arena.length)) := by
    simp only [S8, bracketCounts, stage2NoEventWalkNext]
    rw [stage2NoEventWalkCells_notin (cs := ifThen334AllCells sp3
      (BitVec.ofNat 64 k) (BitVec.ofNat 64 K.tok) (BitVec.ofNat 64 K.terms))
      (n := "%alen.0.ph1405") (env := S7.env)
      (by simp only [ifThen334AllCells, ifThen334Cells, ifThen334PhiCells]; simp)]
    simp only [S7, bracketEntry, stage2NoEventWalkNext]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact h.alenPhi
  have harena8 : lookupName S8.env "%arena.0.ph1406"
      = some (.int 64 (BitVec.ofNat 64 K.arenaWord)) := by
    simp only [S8, bracketCounts, stage2NoEventWalkNext]
    rw [stage2NoEventWalkCells_notin (cs := ifThen334AllCells sp3
      (BitVec.ofNat 64 k) (BitVec.ofNat 64 K.tok) (BitVec.ofNat 64 K.terms))
      (n := "%arena.0.ph1406") (env := S7.env)
      (by simp only [ifThen334AllCells, ifThen334Cells, ifThen334PhiCells]; simp)]
    simp only [S7, bracketEntry, stage2NoEventWalkNext]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact h.arenaPhi
  have hadd338 : lookupName S8.env "%add338"
      = some (.int 64 (BitVec.ofNat 64 K.terms + BitVec.ofNat 64 7)) := by
    simp only [S8, bracketCounts, stage2NoEventWalkNext]
    exact stage2NoEventWalkCells_some (cs := ifThen334AllCells sp3
      (BitVec.ofNat 64 k) (BitVec.ofNat 64 K.tok) (BitVec.ofNat 64 K.terms))
      (n := "%add338") (v := .int 64 (BitVec.ofNat 64 K.terms + BitVec.ofNat 64 7))
      (by simp only [ifThen334AllCells, ifThen334Cells, ifThen334PhiCells,
        List.mem_append, List.mem_cons, List.not_mem_nil, or_false]; tauto) hnd8
  have hinc337 : lookupName S8.env "%inc337"
      = some (.int 64 (BitVec.ofNat 64 K.tok + BitVec.ofNat 64 2)) := by
    simp only [S8, bracketCounts, stage2NoEventWalkNext]
    exact stage2NoEventWalkCells_some (cs := ifThen334AllCells sp3
      (BitVec.ofNat 64 k) (BitVec.ofNat 64 K.tok) (BitVec.ofNat 64 K.terms))
      (n := "%inc337") (v := .int 64 (BitVec.ofNat 64 K.tok + BitVec.ofNat 64 2))
      (by simp only [ifThen334AllCells, ifThen334Cells, ifThen334PhiCells,
        List.mem_append, List.mem_cons, List.not_mem_nil, or_false]; tauto) hnd8
  have L9 : Stage2NoEventWalkLink calls { K with tok := K.tok + 2, terms := K.terms + 7 }
      mem S8 { K with tok := K.tok + 2, terms := K.terms + 7 } S9 :=
    link_closeArr_true (sp3 := sp3) (k5 := BitVec.ofNat 64 (k + 2))
      (alen := BitVec.ofNat 64 K.arena.length)
      (arena := BitVec.ofNat 64 K.arenaWord)
      (terms7 := BitVec.ofNat 64 K.terms + BitVec.ofNat 64 7)
      (toks := BitVec.ofNat 64 K.tok + BitVec.ofNat 64 2)
      L8.inv' (by simp only [S8, bracketCounts, stage2NoEventWalkNext])
      hpre8 hsp8 hinc335 halen8 harena8 hadd338 hinc337 hzero
  have hrun : ∀ n, runFuel calls (9 + n) stage2NoEventBody s =
      runFuel calls n stage2NoEventBody S9 := by
    intro n
    rw [show 9 + n = 1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + n))))))))
      from by omega]
    rw [stage2NoEventWalkLink_runFuel L1, stage2NoEventWalkLink_runFuel L2,
      stage2NoEventWalkLink_runFuel L3, stage2NoEventWalkLink_runFuel L4,
      stage2NoEventWalkLink_runFuel L5, stage2NoEventWalkLink_runFuel L6,
      stage2NoEventWalkLink_runFuel L7, stage2NoEventWalkLink_runFuel L8,
      stage2NoEventWalkLink_runFuel L9]
  have hnd9 : ((closeArrAllCells sp3 (BitVec.ofNat 64 (k + 2))
      (BitVec.ofNat 64 K.arena.length) (BitVec.ofNat 64 K.arenaWord)
      (BitVec.ofNat 64 K.terms + BitVec.ofNat 64 7)
      (BitVec.ofNat 64 K.tok + BitVec.ofNat 64 2)).map (·.1)).Nodup := by
    simp only [closeArrAllCells, closeArrTail, closeArrPhiCells,
      List.map_append, List.map_cons, List.map_nil]
    decide
  refine ⟨S9, ⟨hrun, L9.inv'⟩, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_⟩
  · rfl
  · simp only [S9, bracketArrValue, stage2NoEventWalkNext]
    exact stage2NoEventWalkCells_some (cs := closeArrAllCells sp3
      (BitVec.ofNat 64 (k + 2)) (BitVec.ofNat 64 K.arena.length)
      (BitVec.ofNat 64 K.arenaWord) (BitVec.ofNat 64 K.terms + BitVec.ofNat 64 7)
      (BitVec.ofNat 64 K.tok + BitVec.ofNat 64 2))
      (n := "%frame.4") (v := .int 8 (BitVec.ofNat 8 1))
      (by simp only [closeArrAllCells, closeArrTail, closeArrPhiCells,
        List.mem_append, List.mem_cons, List.not_mem_nil, or_false]; tauto) hnd9
  · simp only [S9, bracketArrValue, stage2NoEventWalkNext]
    exact stage2NoEventWalkCells_some (cs := closeArrAllCells sp3
      (BitVec.ofNat 64 (k + 2)) (BitVec.ofNat 64 K.arena.length)
      (BitVec.ofNat 64 K.arenaWord) (BitVec.ofNat 64 K.terms + BitVec.ofNat 64 7)
      (BitVec.ofNat 64 K.tok + BitVec.ofNat 64 2))
      (n := "%sp.3") (v := .int 32 sp3)
      (by simp only [closeArrAllCells, closeArrTail, closeArrPhiCells,
        List.mem_append, List.mem_cons, List.not_mem_nil, or_false]; tauto) hnd9
  · simp only [S9, bracketArrValue, stage2NoEventWalkNext]
    exact stage2NoEventWalkCells_some (cs := closeArrAllCells sp3
      (BitVec.ofNat 64 (k + 2)) (BitVec.ofNat 64 K.arena.length)
      (BitVec.ofNat 64 K.arenaWord) (BitVec.ofNat 64 K.terms + BitVec.ofNat 64 7)
      (BitVec.ofNat 64 K.tok + BitVec.ofNat 64 2))
      (n := "%k.5") (v := .int 64 (BitVec.ofNat 64 (k + 2)))
      (by simp only [closeArrAllCells, closeArrTail, closeArrPhiCells,
        List.mem_append, List.mem_cons, List.not_mem_nil, or_false]; tauto) hnd9
  · simp only [S9, bracketArrValue, stage2NoEventWalkNext]
    exact stage2NoEventWalkCells_some (cs := closeArrAllCells sp3
      (BitVec.ofNat 64 (k + 2)) (BitVec.ofNat 64 K.arena.length)
      (BitVec.ofNat 64 K.arenaWord) (BitVec.ofNat 64 K.terms + BitVec.ofNat 64 7)
      (BitVec.ofNat 64 K.tok + BitVec.ofNat 64 2))
      (n := "%alen.7") (v := .int 64 (BitVec.ofNat 64 K.arena.length))
      (by simp only [closeArrAllCells, closeArrTail, closeArrPhiCells,
        List.mem_append, List.mem_cons, List.not_mem_nil, or_false]; tauto) hnd9
  · simp only [S9, bracketArrValue, stage2NoEventWalkNext]
    exact stage2NoEventWalkCells_some (cs := closeArrAllCells sp3
      (BitVec.ofNat 64 (k + 2)) (BitVec.ofNat 64 K.arena.length)
      (BitVec.ofNat 64 K.arenaWord) (BitVec.ofNat 64 K.terms + BitVec.ofNat 64 7)
      (BitVec.ofNat 64 K.tok + BitVec.ofNat 64 2))
      (n := "%arena.9") (v := .int 64 (BitVec.ofNat 64 K.arenaWord))
      (by simp only [closeArrAllCells, closeArrTail, closeArrPhiCells,
        List.mem_append, List.mem_cons, List.not_mem_nil, or_false]; tauto) hnd9
  · simp only [S9, bracketArrValue, stage2NoEventWalkNext]
    exact stage2NoEventWalkCells_some (cs := closeArrAllCells sp3
      (BitVec.ofNat 64 (k + 2)) (BitVec.ofNat 64 K.arena.length)
      (BitVec.ofNat 64 K.arenaWord) (BitVec.ofNat 64 K.terms + BitVec.ofNat 64 7)
      (BitVec.ofNat 64 K.tok + BitVec.ofNat 64 2))
      (n := "%terms.7") (v := .int 64 (BitVec.ofNat 64 K.terms + BitVec.ofNat 64 7))
      (by simp only [closeArrAllCells, closeArrTail, closeArrPhiCells,
        List.mem_append, List.mem_cons, List.not_mem_nil, or_false]; tauto) hnd9
  · simp only [S9, bracketArrValue, stage2NoEventWalkNext]
    exact stage2NoEventWalkCells_some (cs := closeArrAllCells sp3
      (BitVec.ofNat 64 (k + 2)) (BitVec.ofNat 64 K.arena.length)
      (BitVec.ofNat 64 K.arenaWord) (BitVec.ofNat 64 K.terms + BitVec.ofNat 64 7)
      (BitVec.ofNat 64 K.tok + BitVec.ofNat 64 2))
      (n := "%tokens.7") (v := .int 64 (BitVec.ofNat 64 K.tok + BitVec.ofNat 64 2))
      (by simp only [closeArrAllCells, closeArrTail, closeArrPhiCells,
        List.mem_append, List.mem_cons, List.not_mem_nil, or_false]; tauto) hnd9
  · simp only [S9, bracketArrValue, stage2NoEventWalkNext]
    rw [stage2NoEventWalkCells_notin (cs := closeArrAllCells sp3
      (BitVec.ofNat 64 (k + 2)) (BitVec.ofNat 64 K.arena.length)
      (BitVec.ofNat 64 K.arenaWord) (BitVec.ofNat 64 K.terms + BitVec.ofNat 64 7)
      (BitVec.ofNat 64 K.tok + BitVec.ofNat 64 2))
      (n := "%nep") (env := S8.env)
      (by simp only [closeArrAllCells, closeArrTail, closeArrPhiCells]; simp)]
    simp only [S8, bracketCounts, stage2NoEventWalkNext]
    rw [stage2NoEventWalkCells_notin (cs := ifThen334AllCells sp3
      (BitVec.ofNat 64 k) (BitVec.ofNat 64 K.tok) (BitVec.ofNat 64 K.terms))
      (n := "%nep") (env := S7.env)
      (by simp only [ifThen334AllCells, ifThen334Cells, ifThen334PhiCells]; simp)]
    simp only [S7, bracketEntry, S6, S5, S4, S3, S2, S1,
      stage2NoEventWalkNext]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact hnep
  · simp only [S9, bracketArrValue, bracketCounts, bracketEntry, S8, S7, S6, S5,
      S4, S3, S2, S1, stage2NoEventWalkNext]
  · have b1 := stage2NoEventCycleBase
      (K := { K with tok := K.tok + 2, terms := K.terms + 7 }) (env := s.env)
      h.baseLookups (cs := [("%Pivot6", .int 1 0)]) (names := ["%Pivot6"])
      rfl (by decide)
    have b2 := stage2NoEventCycleBase
      (K := { K with tok := K.tok + 2, terms := K.terms + 7 }) (env := S1.env)
      b1 (cs := [("%Pivot", .int 1 1)]) (names := ["%Pivot"]) rfl (by decide)
    have b3 := stage2NoEventCycleBase
      (K := { K with tok := K.tok + 2, terms := K.terms + 7 }) (env := S2.env)
      b2 (cs := [("%SwitchLeaf2", .int 1 1)]) (names := ["%SwitchLeaf2"])
      rfl (by decide)
    have b4 := stage2NoEventCycleBase
      (K := { K with tok := K.tok + 2, terms := K.terms + 7 }) (env := S3.env)
      b3 (cs := [("%exitcond.peel", .int 1 0)]) (names := ["%exitcond.peel"])
      rfl (by decide)
    have b5 := stage2NoEventCycleBase
      (K := { K with tok := K.tok + 2, terms := K.terms + 7 }) (env := S4.env)
      b4 (cs := [("%tobool46.not.peel", .int 1 1)])
      (names := ["%tobool46.not.peel"]) rfl (by decide)
    have b6 := stage2NoEventCycleBase
      (K := { K with tok := K.tok + 2, terms := K.terms + 7 }) (env := S5.env)
      b5 (cs := [("%cmp319.not.peel", .int 1 1)])
      (names := ["%cmp319.not.peel"]) rfl (by decide)
    have b7 := stage2NoEventCycleBase
      (K := { K with tok := K.tok + 2, terms := K.terms + 7 }) (env := S6.env)
      b6 (cs := [("%cmp332.peel", .int 1 1),
        ("%6", .int 8 (BitVec.ofNat 8 (bytesToNat [nextByte]))),
        ("%arrayidx330.peel", .ptr (K.b +
          (BitVec.signExtend 64 (BitVec.ofNat 64 (bytesToNat bs4))).toNat)),
        ("%idxprom329.peel", .int 64 (BitVec.ofNat 64 (bytesToNat bs4))),
        ("%5", .int 32 (BitVec.ofNat 32 (bytesToNat bs4))),
        ("%arrayidx328.peel", .ptr (K.ep + (BitVec.ofNat 64 (k + 1)).toNat * 4))])
      (names := ["%cmp332.peel", "%6", "%arrayidx330.peel", "%idxprom329.peel",
        "%5", "%arrayidx328.peel"]) rfl (by decide)
    have b8 := stage2NoEventCycleBase
      (K := { K with tok := K.tok + 2, terms := K.terms + 7 }) (env := S7.env)
      b7 (cs := ifThen334AllCells sp3 (BitVec.ofNat 64 k) (BitVec.ofNat 64 K.tok)
        (BitVec.ofNat 64 K.terms))
      (names := (ifThen334AllCells sp3 (BitVec.ofNat 64 k) (BitVec.ofNat 64 K.tok)
        (BitVec.ofNat 64 K.terms)).map (·.1)) rfl
      (by simp only [ifThen334AllCells, ifThen334Cells, ifThen334PhiCells,
        List.map_append, List.map_cons, List.map_nil]; decide)
    have b9 := stage2NoEventCycleBase
      (K := { K with tok := K.tok + 2, terms := K.terms + 7 }) (env := S8.env)
      b8 (cs := closeArrAllCells sp3 (BitVec.ofNat 64 (k + 2))
        (BitVec.ofNat 64 K.arena.length) (BitVec.ofNat 64 K.arenaWord)
        (BitVec.ofNat 64 K.terms + BitVec.ofNat 64 7)
        (BitVec.ofNat 64 K.tok + BitVec.ofNat 64 2))
      (names := (closeArrAllCells sp3 (BitVec.ofNat 64 (k + 2))
        (BitVec.ofNat 64 K.arena.length) (BitVec.ofNat 64 K.arenaWord)
        (BitVec.ofNat 64 K.terms + BitVec.ofNat 64 7)
        (BitVec.ofNat 64 K.tok + BitVec.ofNat 64 2)).map (·.1)) rfl
      (by simp only [closeArrAllCells, closeArrTail, closeArrPhiCells,
        List.map_append, List.map_cons, List.map_nil]; decide)
    exact b9
  · have hbsOpen : K.bs[lane]? = some (0x5B : UInt8) := by
      have hy : byte = (0x5B : UInt8) :=
        stage2NoEventWalk_uint8_eq_of_toNat (by rw [hb]; decide)
      simpa [hy] using hbs
    have hbsClose : K.bs[next]? = some (0x5D : UInt8) := by
      have hy : nextByte = (0x5D : UInt8) :=
        stage2NoEventWalk_uint8_eq_of_toNat (by rw [hb1]; decide)
      simpa [hy] using hbs1
    exact Stage2NoEventWalkTrace.emptyArray htrace hbsOpen hbsClose

/-- **The `[]` route's price**, at a closer index strictly below the entry count. -/
theorem stage2NoEventWalkBracketZeroRoute_price
    {K : Stage2NoEventWalkCarry} {mem : Mem} {k : Nat} {s : State}
    (h : Stage2NoEventWalkHead K mem k s) (hkbound : k + 2 < K.nep) :
    9 + stage2NoEventWalkPotential
        { K with tok := K.tok + 2, terms := K.terms + 7 } (k + 2) ≤
      stage2NoEventWalkPotential K k := by
  have hk2 : k + 2 ≤ K.nep := Nat.le_of_lt hkbound
  have hlen : K.ent.length = K.nep :=
    readLanes32_length mem K.ep K.nep K.ent h.inv.entries
  have hentle : K.ent.getD k 0 ≤ K.ent.getD (k + 2) 0 :=
    stage2NoEventEnt_getD_le h.inv.order (by omega) (by rw [hlen]; omega)
  have hadd := stage2NoEventWalkPotential_add (K := K) (k := k) (d := 2) hk2 hentle
  have hpot : stage2NoEventWalkPotential
      { K with tok := K.tok + 2, terms := K.terms + 7 } (k + 2) =
      stage2NoEventWalkPotential K (k + 2) := rfl
  rw [hpot]
  omega

/-! ### The `{}` route to the depth-zero endpoint

Eleven blocks at the top level: the head's dispatch to `if.then9`, that head's
carried seven-`phi` run and stack test, the zero-depth `if.end19` arm (no store),
`if.end23`, the next entry's read at `if.end74`, the `}` dispatch, the counts at
`if.then81`, and `close_obj`'s zero-depth arm to `after_value`.  No stack write
or read occurs; the two carried counts reach the endpoint as `tok + 2` and
`terms + 3`. -/

/-- **The `{}` zero-depth route**, as an eleven-block segment to `after_value`. -/
theorem stage2NoEventWalkBraceZeroRoute {calls : Calls}
    {K : Stage2NoEventWalkCarry} {mem : Mem} {k : Nat} {s : State}
    (h : Stage2NoEventWalkHead K mem k s)
    (htrace : Stage2NoEventWalkTrace K)
    {lane : Nat} {byte : UInt8}
    (hk : K.ent[k]? = some lane) (hbs : K.bs[lane]? = some byte) (hb : byte.toNat = 123)
    {next : Nat} {nextByte : UInt8}
    (hbs1 : K.bs[next]? = some nextByte)
    (hb1 : nextByte.toNat = 125)
    (hspZ : lookupName s.env "%sp.0.ph1403" =
      some (.int 32 (BitVec.ofNat 32 0)))
    (hkbound : k + 2 ≤ K.nep) (hk63 : k + 3 < 2 ^ 63)
    {bs4 : List UInt8}
    (hlane : readBytes s.mem (K.ep + (BitVec.ofNat 64 (k + 1)).toNat * 4) 4 = some bs4)
    (hval4lt : bytesToNat bs4 < 2 ^ 32)
    (hbyte : readBytes s.mem
      (K.b + (BitVec.signExtend 64 (BitVec.ofNat 64 (bytesToNat bs4))).toNat) 1
      = some [nextByte]) :
    ∃ sE, Stage2NoEventWalkSegment calls mem K s
        { K with tok := K.tok + 2, terms := K.terms + 3 } sE 11 ∧
      sE.pc = "after_value" ∧ sE.pre = some "close_obj" ∧
      lookupName sE.env "%dec" =
        some (.int 32 (BitVec.ofNat 32 0 + BitVec.ofNat 32 1 +
          BitVec.ofNat 32 4294967295)) ∧
      lookupName sE.env "%k.4" = some (.int 64 (BitVec.ofNat 64 (k + 2))) ∧
      lookupName sE.env "%alen.6" = some (.int 64 (BitVec.ofNat 64 K.arena.length)) ∧
      lookupName sE.env "%arena.8" = some (.int 64 (BitVec.ofNat 64 K.arenaWord)) ∧
      lookupName sE.env "%terms.6" = some (.int 64 (BitVec.ofNat 64 (K.terms + 3))) ∧
      lookupName sE.env "%tokens.6" = some (.int 64 (BitVec.ofNat 64 (K.tok + 2))) ∧
      lookupName sE.env "%nep" = some (.int 64 (BitVec.ofNat 64 K.nep)) ∧
      sE.mem = s.mem ∧
      Stage2NoEventWalkBaseLookups
        { K with tok := K.tok + 2, terms := K.terms + 3 } sE ∧
      Stage2NoEventWalkTrace
        { K with tok := K.tok + 2, terms := K.terms + 3 } := by
  classical
  have h3 : lookupName s.env "%3" = some (.int 8 (BitVec.ofNat 8 123)) :=
    h.braceCell hk hbs hb
  have hnep : lookupName s.env "%nep" = some (.int 64 (BitVec.ofNat 64 K.nep)) := h.nepI
  have hep : lookupName s.env "%ep" = some (.ptr K.ep) := h.epPtr
  have hbPtr : lookupName s.env "%b" = some (.ptr K.b) := h.bPtr
  have hincH : lookupName s.env "%inc.peel" =
      some (.int 64 (BitVec.ofNat 64 (k + 1))) := by
    obtain ⟨-, -, -, -, -, -, -, -, hinc, -, -, -⟩ := h.laneRead
    exact hinc
  have hidxH : lookupName s.env "%idxprom.peel" =
      some (.int 64 (BitVec.ofNat 64 lane)) := by
    obtain ⟨laneR, _byte, hent, _hlt, _hbs, _hread, _h2, hidx, _hinc, _ha1,
      _ha2, _h3⟩ := h.laneRead
    have hlane : laneR = lane := Option.some.inj (hent.symm.trans hk)
    simpa only [hlane] using hidx
  obtain ⟨fr, hfrH⟩ := h.framePhi
  let sp3 : BitVec 32 := BitVec.ofNat 32 0
  let inc : BitVec 64 := BitVec.ofNat 64 (k + 1)
  let k64 : BitVec 64 := BitVec.ofNat 64 k
  let terms64 : BitVec 64 := BitVec.ofNat 64 K.terms
  let tok64 : BitVec 64 := BitVec.ofNat 64 K.tok
  have hzero : sp3.toNat = 0 := rfl
  have hle : sp3.toNat ≤ 519 := by decide
  have hguard : K.tok + 2 ≤ K.n :=
    Stage2NoEventWalkInv.tok_add_le h.inv h.count hkbound
  have hincLt : inc.toNat < 2 ^ 63 := by
    show (BitVec.ofNat 64 (k + 1)).toNat < 2 ^ 63
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : k + 1 < 2 ^ 64)]
    omega
  have hult : BitVec.ult inc (BitVec.ofNat 64 K.nep) = true := by
    refine BitVec.ult_iff_toNat_lt.2 ?_
    show (BitVec.ofNat 64 (k + 1)).toNat < (BitVec.ofNat 64 K.nep).toNat
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : k + 1 < 2 ^ 64),
      Nat.mod_eq_of_lt h.inv.nepLt]
    omega
  -- the eleven blocks
  let S1 := stage2NoEventWalkNext (("%Pivot6", .int 1 0) :: s.env) s "NodeBlock"
  let S2 := stage2NoEventWalkNext (("%Pivot", .int 1 0) :: S1.env) S1 "LeafBlock3"
  let S3 := stage2NoEventWalkNext (("%SwitchLeaf4", .int 1 1) :: S2.env) S2 "if.then9"
  let S4 := stage2NoEventWalkNext
    (braceIfThen9Cells S3.env inc (BitVec.ofNat 64 lane) (BitVec.ofNat 8 fr) sp3
      k64 terms64 tok64) S3 "if.end19"
  let S5 := openZeroEnd23 S4
  let S6 := openZeroEnd74 S4 sp3
  let S7 := braceCountState S6 K.ep K.b terms64 tok64 inc bs4 [nextByte]
  let S8 := braceDispatchState S6 K.ep K.b terms64 tok64 inc bs4 [nextByte]
  let S9 := braceSelectState S6 K.ep K.b terms64 tok64 inc bs4 [nextByte]
  let sp2 : BitVec 32 := BitVec.ofNat 32 0 + BitVec.ofNat 32 1
  let S10 := braceCloseState S6 K.ep K.b terms64 tok64 inc k64 bs4 [nextByte]
  let S11 := stage2NoEventWalkNext
    (cells (closeObjTail sp2 ++ braceCloseObjCells sp2
      (BitVec.ofNat 64 k + BitVec.ofNat 64 2) (BitVec.ofNat 64 K.arena.length)
      (BitVec.ofNat 64 K.arenaWord) (BitVec.ofNat 64 K.terms + BitVec.ofNat 64 3)
      (BitVec.ofNat 64 K.tok + BitVec.ofNat 64 2)) S10.env)
    S10 "after_value"
  have L1 : Stage2NoEventWalkLink calls K mem s K S1 :=
    link_nodeBlock5_false h.inv h.pc h3 (by decide)
  have h3a : lookupName (("%Pivot6", .int 1 0) :: s.env) "%3"
      = some (.int 8 (BitVec.ofNat 8 123)) :=
    lookupName_cons_other _ _ _ (by decide) h3
  have L2 : Stage2NoEventWalkLink calls K mem S1 K S2 :=
    link_nodeBlock_false L1.inv' (by simp only [S1, stage2NoEventWalkNext])
      h3a (by decide)
  have h3b : lookupName (("%Pivot", .int 1 0) :: ("%Pivot6", .int 1 0) :: s.env) "%3"
      = some (.int 8 (BitVec.ofNat 8 123)) :=
    lookupName_cons_other _ _ _ (by decide) h3a
  have L3 : Stage2NoEventWalkLink calls K mem S2 K S3 :=
    link_leafBlock3_true L2.inv' (by simp only [S2, S1, stage2NoEventWalkNext])
      h3b (by decide)
  have hk3 : lookupName S3.env "%k.0.ph1404" = some (.int 64 k64) := by
    simp only [S3, S2, S1, stage2NoEventWalkNext, cells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact h.kEq
  have hinc3 : lookupName S3.env "%inc.peel" = some (.int 64 inc) := by
    simp only [S3, S2, S1, stage2NoEventWalkNext, cells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact hincH
  have hidx3 : lookupName S3.env "%idxprom.peel"
      = some (.int 64 (BitVec.ofNat 64 lane)) := by
    simp only [S3, S2, S1, stage2NoEventWalkNext, cells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact hidxH
  have hfr3 : lookupName S3.env "%frame.0.ph1402"
      = some (.int 8 (BitVec.ofNat 8 fr)) := by
    simp only [S3, S2, S1, stage2NoEventWalkNext, cells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact hfrH
  have hsp3 : lookupName S3.env "%sp.0.ph1403" = some (.int 32 sp3) := by
    simp only [S3, S2, S1, stage2NoEventWalkNext, cells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact hspZ
  have htr3 : lookupName S3.env "%terms.0.ph1407" = some (.int 64 terms64) := by
    simp only [S3, S2, S1, stage2NoEventWalkNext, cells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact h.termsPhi
  have htok3 : lookupName S3.env "%tokens.0.ph1408" = some (.int 64 tok64) := by
    simp only [S3, S2, S1, stage2NoEventWalkNext, cells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact h.tokensPhi
  have hguard9 : evalICmp .ugt sp3 (BitVec.ofNat 32 519) = 0 := by
    show evalICmp .ugt (BitVec.ofNat 32 0) (BitVec.ofNat 32 519) = 0
    decide
  have L4 : Stage2NoEventWalkLink calls K mem S3 K S4 :=
    link_braceIfThen9_false L3.inv'
      (by simp only [S3, S2, S1, stage2NoEventWalkNext]) rfl
      hk3 hinc3 hidx3 hfr3 hsp3 htr3 htok3 hguard9
  have hsp4 : lookupName S4.env "%sp.0.lcssa1092.wide" = some (.int 32 sp3) := by
    simp only [S4, braceIfThen9Cells, stage2NoEventWalkNext]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact lookupName_cons_self _ _ _
  have L5 : Stage2NoEventWalkLink calls K mem S4 K S5 :=
    link_ifEnd19_true L4.inv' (by simp only [S4, stage2NoEventWalkNext])
      hsp4 hzero
  have hsp5 : lookupName S5.env "%sp.0.lcssa1092.wide" = some (.int 32 sp3) := by
    simp only [S5, openZeroEnd23, stage2NoEventWalkNext]
    exact lookupName_cons_other _ _ _ (by decide) hsp4
  have hinc5 : lookupName S5.env "%inc.lcssa1129" = some (.int 64 inc) := by
    simp only [S5, openZeroEnd23, S4, braceIfThen9Cells, stage2NoEventWalkNext]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact lookupName_cons_self _ _ _
  have hnep5 : lookupName S5.env "%nep" = some (.int 64 (BitVec.ofNat 64 K.nep)) := by
    simp only [S5, openZeroEnd23, S4, braceIfThen9Cells, S3, S2, S1,
      stage2NoEventWalkNext]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact hnep
  have L6 : Stage2NoEventWalkLink calls K mem S5 K S6 :=
    link_ifEnd23 L5.inv' (by simp only [S5, openZeroEnd23, stage2NoEventWalkNext])
      hsp5 hinc5 hnep5 hult
  have hsp6 : lookupName S6.env "%sp.0.lcssa1092.wide" = some (.int 32 sp3) := by
    simp only [S6, openZeroEnd74, openZeroEnd23, S5, S4, braceIfThen9Cells,
      stage2NoEventWalkNext, cells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact lookupName_cons_self _ _ _
  have hterms6 : lookupName S6.env "%terms.0.lcssa1080"
      = some (.int 64 terms64) := by
    simp only [S6, openZeroEnd74, openZeroEnd23, S5, S4, braceIfThen9Cells,
      S3, S2, S1, stage2NoEventWalkNext, cells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact lookupName_cons_self _ _ _
  have htok6 : lookupName S6.env "%tokens.0.lcssa1074"
      = some (.int 64 tok64) := by
    simp only [S6, openZeroEnd74, openZeroEnd23, S5, S4, braceIfThen9Cells,
      S3, S2, S1, stage2NoEventWalkNext, cells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact lookupName_cons_self _ _ _
  have hep6 : lookupName S6.env "%ep" = some (.ptr K.ep) := by
    simp only [S6, openZeroEnd74, openZeroEnd23, S5, S4, braceIfThen9Cells,
      S3, S2, S1, stage2NoEventWalkNext, cells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact hep
  have hb6 : lookupName S6.env "%b" = some (.ptr K.b) := by
    simp only [S6, openZeroEnd74, openZeroEnd23, S5, S4, braceIfThen9Cells,
      S3, S2, S1, stage2NoEventWalkNext, cells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact hbPtr
  have hinc6 : lookupName S6.env "%inc.lcssa1129" = some (.int 64 inc) := by
    simp only [S6, openZeroEnd74, openZeroEnd23, S5, S4, braceIfThen9Cells,
      S3, S2, S1, stage2NoEventWalkNext, cells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact lookupName_cons_self _ _ _
  have L7 : Stage2NoEventWalkLink calls K mem S6 K S7 :=
    link_ifEnd74 L6.inv' (by simp only [S6, openZeroEnd74, stage2NoEventWalkNext])
      hterms6 htok6 hep6 hb6 hinc6 hincLt hlane hval4lt
      (by simpa only [S6, openZeroEnd74, openZeroEnd23, S5, S4, S3, S2, S1,
        stage2NoEventWalkNext] using hbyte)
  have hnd74 : ((ifEnd74Cells K.ep K.b terms64 tok64 inc bs4 [nextByte]).map (·.1)).Nodup := by
    simp only [ifEnd74Cells, List.map_cons, List.map_nil]; decide
  have h11_7 : lookupName S7.env "%11"
      = some (.int 8 (BitVec.ofNat 8 (bytesToNat [nextByte]))) := by
    simp only [S7, braceCountState, stage2NoEventWalkNext]
    exact stage2NoEventWalkCells_some (cs := ifEnd74Cells K.ep K.b terms64 tok64 inc
      bs4 [nextByte]) (n := "%11")
      (v := .int 8 (BitVec.ofNat 8 (bytesToNat [nextByte])))
      (by simp [ifEnd74Cells]) hnd74
  have h11_8 : lookupName S8.env "%11"
      = some (.int 8 (BitVec.ofNat 8 (bytesToNat [nextByte]))) := by
    simp only [S8, braceDispatchState, stage2NoEventWalkNext]
    rw [lookupName_cons_ne _ _ (by decide)]
    exact h11_7
  have h11_7' : evalICmp .slt (BitVec.ofNat 8 (bytesToNat [nextByte]))
      (BitVec.ofNat 8 125) = 0 := by
    rw [stage2NoEventWalkBytesToNat_single, hb1]; decide
  have L8 : Stage2NoEventWalkLink calls K mem S7 K S8 :=
    link_nodeBlock21_false L7.inv' (by simp only [S7, braceCountState,
      stage2NoEventWalkNext]) h11_7 h11_7'
  have h11_9' : evalICmp .eq (BitVec.ofNat 8 (bytesToNat [nextByte]))
      (BitVec.ofNat 8 125) = 1 := by
    rw [stage2NoEventWalkBytesToNat_single, hb1]; decide
  have L9 : Stage2NoEventWalkLink calls K mem S8 K S9 :=
    link_leafBlock19_true L8.inv' (by simp only [S8, braceDispatchState,
      stage2NoEventWalkNext]) h11_8 h11_9'
  have hk9 : lookupName S9.env "%k.0.lcssa1086" = some (.int 64 k64) := by
    simp only [S9, braceSelectState, S8, braceDispatchState, S7, braceCountState,
      ifEnd74Out, S6, openZeroEnd74, openZeroEnd23, S5, S4, braceIfThen9Cells,
      S3, S2, S1, stage2NoEventWalkNext, cells, ifEnd74Cells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact lookupName_cons_self _ _ _
  have htr9 : lookupName S9.env "%terms.0.lcssa1080" = some (.int 64 terms64) := by
    simp only [S9, braceSelectState, S8, braceDispatchState, S7, braceCountState,
      ifEnd74Out, S6, openZeroEnd74, openZeroEnd23, S5, S4, braceIfThen9Cells,
      S3, S2, S1, stage2NoEventWalkNext, cells, ifEnd74Cells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact lookupName_cons_self _ _ _
  have htok9 : lookupName S9.env "%tokens.0.lcssa1074" = some (.int 64 tok64) := by
    simp only [S9, braceSelectState, S8, braceDispatchState, S7, braceCountState,
      ifEnd74Out, S6, openZeroEnd74, openZeroEnd23, S5, S4, braceIfThen9Cells,
      S3, S2, S1, stage2NoEventWalkNext, cells, ifEnd74Cells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact lookupName_cons_self _ _ _
  have L10 : Stage2NoEventWalkLink calls K mem S9
      { K with tok := K.tok + 2, terms := K.terms + 3 } S10 :=
    link_ifThen81 L9.inv' (by simp only [S9, braceSelectState, stage2NoEventWalkNext])
      (by simp only [S10, braceCloseState, braceCountsOut, ifThen81Out,
        S9, braceSelectState, S8, braceDispatchState, S7, braceCountState,
        stage2NoEventWalkNext])
      hk9 htok9 htr9 hguard
  have hsp10 : lookupName S10.env "%inc24" = some (.int 32 sp2) := by
    simp only [S10, braceCloseState, braceCountsOut, ifThen81Out, S9,
      braceSelectState, S8, braceDispatchState, S7, braceCountState, ifEnd74Out,
      S6, openZeroEnd74, openZeroEnd23, S5, S4, braceIfThen9Cells, S3, S2, S1,
      stage2NoEventWalkNext, cells, ifEnd74Cells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact lookupName_cons_self _ _ _
  have hk4_10 : lookupName S10.env "%inc82"
      = some (.int 64 (BitVec.ofNat 64 k + BitVec.ofNat 64 2)) := by
    simp only [S10, braceCloseState, braceCountsOut, ifThen81Out,
      stage2NoEventWalkNext, cells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    rw [lookupName_cons_self]
  have halen10 : lookupName S10.env "%alen.0.ph1405"
      = some (.int 64 (BitVec.ofNat 64 K.arena.length)) := by
    simp only [S10, braceCloseState, braceCountsOut, ifThen81Out, S9,
      braceSelectState, S8, braceDispatchState, S7, braceCountState, ifEnd74Out,
      S6, openZeroEnd74, openZeroEnd23, S5, S4, braceIfThen9Cells, S3, S2, S1,
      stage2NoEventWalkNext, cells, ifEnd74Cells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact h.alenPhi
  have harena10 : lookupName S10.env "%arena.0.ph1406"
      = some (.int 64 (BitVec.ofNat 64 K.arenaWord)) := by
    simp only [S10, braceCloseState, braceCountsOut, ifThen81Out, S9,
      braceSelectState, S8, braceDispatchState, S7, braceCountState, ifEnd74Out,
      S6, openZeroEnd74, openZeroEnd23, S5, S4, braceIfThen9Cells, S3, S2, S1,
      stage2NoEventWalkNext, cells, ifEnd74Cells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact h.arenaPhi
  have hterms10 : lookupName S10.env "%add85"
      = some (.int 64 (BitVec.ofNat 64 K.terms + BitVec.ofNat 64 3)) := by
    simp only [S10, braceCloseState, braceCountsOut, ifThen81Out,
      stage2NoEventWalkNext, cells]
    rw [lookupName_cons_self]
  have htok10 : lookupName S10.env "%inc84"
      = some (.int 64 (BitVec.ofNat 64 K.tok + BitVec.ofNat 64 2)) := by
    simp only [S10, braceCloseState, braceCountsOut, ifThen81Out,
      stage2NoEventWalkNext, cells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    rw [lookupName_cons_self]
  have hdec10 : (sp2 + BitVec.ofNat 32 4294967295).toNat = 0 := by
    show (BitVec.ofNat 32 0 + BitVec.ofNat 32 1 + BitVec.ofNat 32 4294967295).toNat = 0
    decide
  have L11 : Stage2NoEventWalkLink calls
      { K with tok := K.tok + 2, terms := K.terms + 3 } mem S10
      { K with tok := K.tok + 2, terms := K.terms + 3 } S11 :=
    link_closeObj_zero (sp2 := sp2) (k4 := BitVec.ofNat 64 k + BitVec.ofNat 64 2)
      (alen := BitVec.ofNat 64 K.arena.length)
      (arena := BitVec.ofNat 64 K.arenaWord)
      (terms6 := BitVec.ofNat 64 K.terms + BitVec.ofNat 64 3)
      (toks := BitVec.ofNat 64 K.tok + BitVec.ofNat 64 2)
      L10.inv' (by simp only [S10, braceCloseState, stage2NoEventWalkNext]) rfl
      hsp10 hk4_10 halen10 harena10 hterms10 htok10 hdec10
  have hrun : ∀ n, runFuel calls (11 + n) stage2NoEventBody s =
      runFuel calls n stage2NoEventBody S11 := by
    intro n
    rw [show 11 + n = 1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 +
      (1 + n)))))))))) from by omega]
    rw [stage2NoEventWalkLink_runFuel L1, stage2NoEventWalkLink_runFuel L2,
      stage2NoEventWalkLink_runFuel L3, stage2NoEventWalkLink_runFuel L4,
      stage2NoEventWalkLink_runFuel L5, stage2NoEventWalkLink_runFuel L6,
      stage2NoEventWalkLink_runFuel L7, stage2NoEventWalkLink_runFuel L8,
      stage2NoEventWalkLink_runFuel L9, stage2NoEventWalkLink_runFuel L10,
      stage2NoEventWalkLink_runFuel L11]
  have hnd11 : ((closeObjTail sp2 ++ braceCloseObjCells sp2
      (BitVec.ofNat 64 k + BitVec.ofNat 64 2) (BitVec.ofNat 64 K.arena.length)
      (BitVec.ofNat 64 K.arenaWord) (BitVec.ofNat 64 K.terms + BitVec.ofNat 64 3)
      (BitVec.ofNat 64 K.tok + BitVec.ofNat 64 2)).map (·.1)).Nodup := by
    simp only [closeObjTail, braceCloseObjCells, List.map_append, List.map_cons,
      List.map_nil]
    decide
  have hget : ∀ (n : String) (v : Value),
      (n, v) ∈ closeObjTail sp2 ++ braceCloseObjCells sp2
        (BitVec.ofNat 64 k + BitVec.ofNat 64 2) (BitVec.ofNat 64 K.arena.length)
        (BitVec.ofNat 64 K.arenaWord) (BitVec.ofNat 64 K.terms + BitVec.ofNat 64 3)
        (BitVec.ofNat 64 K.tok + BitVec.ofNat 64 2) →
      lookupName S11.env n = some v := by
    intro n v hv
    simp only [S11, stage2NoEventWalkNext]
    exact stage2NoEventWalkCells_some (cs := closeObjTail sp2 ++ braceCloseObjCells sp2
      (BitVec.ofNat 64 k + BitVec.ofNat 64 2) (BitVec.ofNat 64 K.arena.length)
      (BitVec.ofNat 64 K.arenaWord) (BitVec.ofNat 64 K.terms + BitVec.ofNat 64 3)
      (BitVec.ofNat 64 K.tok + BitVec.ofNat 64 2)) hv hnd11
  refine ⟨S11, ⟨hrun, L11.inv'⟩, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_⟩
  · rfl
  · exact hget "%dec" (.int 32 (sp2 + BitVec.ofNat 32 4294967295))
      (by apply List.mem_append_left
          simp only [closeObjTail, List.mem_cons, List.not_mem_nil, or_false, or_true, true_or])
  · have hk := hget "%k.4" (.int 64 (k64 + BitVec.ofNat 64 2))
      (by apply List.mem_append_right
          simp only [k64, braceCloseObjCells, List.mem_cons, List.not_mem_nil,
            or_false, or_true, true_or])
    simpa only [k64, stage2NoEventWalkOfNat_add] using hk
  · exact hget "%alen.6" (.int 64 (BitVec.ofNat 64 K.arena.length))
      (by apply List.mem_append_right
          simp only [braceCloseObjCells, List.mem_cons, List.not_mem_nil, or_false, or_true, true_or])
  · exact hget "%arena.8" (.int 64 (BitVec.ofNat 64 K.arenaWord))
      (by apply List.mem_append_right
          simp only [braceCloseObjCells, List.mem_cons, List.not_mem_nil, or_false, or_true, true_or])
  · have ht := hget "%terms.6" (.int 64 (terms64 + BitVec.ofNat 64 3))
      (by apply List.mem_append_right
          simp only [terms64, braceCloseObjCells, List.mem_cons, List.not_mem_nil,
            or_false, or_true, true_or])
    simpa only [terms64, stage2NoEventWalkOfNat_add] using ht
  · have ht := hget "%tokens.6" (.int 64 (tok64 + BitVec.ofNat 64 2))
      (by apply List.mem_append_right
          simp only [tok64, braceCloseObjCells, List.mem_cons, List.not_mem_nil,
            or_false, or_true, true_or])
    simpa only [tok64, stage2NoEventWalkOfNat_add] using ht
  · simp only [S11, stage2NoEventWalkNext]
    rw [stage2NoEventWalkCells_notin (cs := closeObjTail sp2 ++ braceCloseObjCells sp2
      (BitVec.ofNat 64 k + BitVec.ofNat 64 2) (BitVec.ofNat 64 K.arena.length)
      (BitVec.ofNat 64 K.arenaWord) (BitVec.ofNat 64 K.terms + BitVec.ofNat 64 3)
      (BitVec.ofNat 64 K.tok + BitVec.ofNat 64 2))
      (n := "%nep") (env := S10.env) (by simp [closeObjTail, braceCloseObjCells])]
    simp only [S10, braceCloseState, braceCountsOut, ifThen81Out, S9,
      braceSelectState, S8, braceDispatchState, S7, braceCountState, ifEnd74Out,
      S6, openZeroEnd74, openZeroEnd23, S5, S4, braceIfThen9Cells, S3, S2, S1,
      stage2NoEventWalkNext, cells, ifEnd74Cells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact hnep
  · simp only [S11, braceCloseState, braceCountsOut, ifThen81Out,
      braceSelectState, braceDispatchState, braceCountState, ifEnd74Out,
      openZeroEnd74, openZeroEnd23, braceIfThen9Cells, S10, S9, S8, S7, S6, S5,
      S4, S3, S2, S1, stage2NoEventWalkNext]
  · have b1 := stage2NoEventCycleBase
      (K := { K with tok := K.tok + 2, terms := K.terms + 3 }) (env := s.env)
      h.baseLookups (cs := [("%Pivot6", .int 1 0)]) (names := ["%Pivot6"])
      rfl (by decide)
    have b2 := stage2NoEventCycleBase
      (K := { K with tok := K.tok + 2, terms := K.terms + 3 }) (env := S1.env)
      b1 (cs := [("%Pivot", .int 1 0)]) (names := ["%Pivot"]) rfl (by decide)
    have b3 := stage2NoEventCycleBase
      (K := { K with tok := K.tok + 2, terms := K.terms + 3 }) (env := S2.env)
      b2 (cs := [("%SwitchLeaf4", .int 1 1)]) (names := ["%SwitchLeaf4"])
      rfl (by decide)
    have b4 := stage2NoEventCycleBase
      (K := { K with tok := K.tok + 2, terms := K.terms + 3 }) (env := S3.env)
      b3 (cs := [("%cmp10", .int 1 0),
        ("%tokens.0.lcssa1074", .int 64 tok64),
        ("%terms.0.lcssa1080", .int 64 terms64),
        ("%k.0.lcssa1086", .int 64 k64),
        ("%sp.0.lcssa1092.wide", .int 32 sp3),
        ("%frame.0.lcssa1098", .int 8 (BitVec.ofNat 8 fr)),
        ("%idxprom.lcssa1108", .int 64 (BitVec.ofNat 64 lane)),
        ("%inc.lcssa1129", .int 64 inc)])
      (names := ["%cmp10", "%tokens.0.lcssa1074", "%terms.0.lcssa1080",
        "%k.0.lcssa1086", "%sp.0.lcssa1092.wide", "%frame.0.lcssa1098",
        "%idxprom.lcssa1108", "%inc.lcssa1129"]) rfl (by decide)
    have b5 := stage2NoEventCycleBase
      (K := { K with tok := K.tok + 2, terms := K.terms + 3 }) (env := S4.env)
      b4 (cs := [("%cmp66.not", .int 1 1),
        ("%inc24", .int 32 (sp3 + BitVec.ofNat 32 1)),
        ("%tobool.not", .int 1 1)])
      (names := ["%cmp66.not", "%inc24", "%tobool.not"]) rfl (by decide)
    have b6 := stage2NoEventCycleBase
      (K := { K with tok := K.tok + 2, terms := K.terms + 3 }) (env := S6.env)
      b5 (cs := ifEnd74Cells K.ep K.b terms64 tok64 inc bs4 [nextByte])
      (names := (ifEnd74Cells K.ep K.b terms64 tok64 inc bs4 [nextByte]).map
        (·.1)) rfl
      (by simp only [ifEnd74Cells, List.map_cons, List.map_nil]; decide)
    have b7 := stage2NoEventCycleBase
      (K := { K with tok := K.tok + 2, terms := K.terms + 3 }) (env := S7.env)
      b6 (cs := [("%Pivot22", .int 1 0)]) (names := ["%Pivot22"]) rfl
      (by decide)
    have b8 := stage2NoEventCycleBase
      (K := { K with tok := K.tok + 2, terms := K.terms + 3 }) (env := S8.env)
      b7 (cs := [("%SwitchLeaf20", .int 1 1)]) (names := ["%SwitchLeaf20"]) rfl
      (by decide)
    have b9 := stage2NoEventCycleBase
      (K := { K with tok := K.tok + 2, terms := K.terms + 3 }) (env := S9.env)
      b8 (cs := [("%add85", .int 64 (terms64 + BitVec.ofNat 64 3)),
        ("%inc84", .int 64 (tok64 + BitVec.ofNat 64 2)),
        ("%inc82", .int 64 (k64 + BitVec.ofNat 64 2))])
      (names := ["%add85", "%inc84", "%inc82"]) rfl (by decide)
    have b10 := stage2NoEventCycleBase
      (K := { K with tok := K.tok + 2, terms := K.terms + 3 }) (env := S10.env)
      b9 (cs := closeObjTail sp2 ++ braceCloseObjCells sp2
        (BitVec.ofNat 64 k + BitVec.ofNat 64 2) (BitVec.ofNat 64 K.arena.length)
        (BitVec.ofNat 64 K.arenaWord) (BitVec.ofNat 64 K.terms + BitVec.ofNat 64 3)
        (BitVec.ofNat 64 K.tok + BitVec.ofNat 64 2))
      (names := (closeObjTail sp2 ++ braceCloseObjCells sp2
        (BitVec.ofNat 64 k + BitVec.ofNat 64 2) (BitVec.ofNat 64 K.arena.length)
        (BitVec.ofNat 64 K.arenaWord) (BitVec.ofNat 64 K.terms + BitVec.ofNat 64 3)
        (BitVec.ofNat 64 K.tok + BitVec.ofNat 64 2)).map (·.1)) rfl
      (by simp only [closeObjTail, braceCloseObjCells, List.map_append,
        List.map_cons, List.map_nil]; decide)
    exact b10
  · have hbsOpen : K.bs[lane]? = some (0x7B : UInt8) := by
      have hy : byte = (0x7B : UInt8) :=
        stage2NoEventWalk_uint8_eq_of_toNat (by rw [hb]; decide)
      simpa [hy] using hbs
    have hbsClose : K.bs[next]? = some (0x7D : UInt8) := by
      have hy : nextByte = (0x7D : UInt8) :=
        stage2NoEventWalk_uint8_eq_of_toNat (by rw [hb1]; decide)
      simpa [hy] using hbs1
    exact Stage2NoEventWalkTrace.emptyObject htrace hbsOpen hbsClose

/-- **The `{}` route's price**, at a closer index strictly below the entry count. -/
theorem stage2NoEventWalkBraceZeroRoute_price
    {K : Stage2NoEventWalkCarry} {mem : Mem} {k : Nat} {s : State}
    (h : Stage2NoEventWalkHead K mem k s) (hkbound : k + 2 < K.nep) :
    11 + stage2NoEventWalkPotential
        { K with tok := K.tok + 2, terms := K.terms + 3 } (k + 2) ≤
      stage2NoEventWalkPotential K k := by
  have hk2 : k + 2 ≤ K.nep := Nat.le_of_lt hkbound
  have hlen : K.ent.length = K.nep :=
    readLanes32_length mem K.ep K.nep K.ent h.inv.entries
  have hentle : K.ent.getD k 0 ≤ K.ent.getD (k + 2) 0 :=
    stage2NoEventEnt_getD_le h.inv.order (by omega) (by rw [hlen]; omega)
  have hadd := stage2NoEventWalkPotential_add (K := K) (k := k) (d := 2) hk2 hentle
  have hpot : stage2NoEventWalkPotential
      { K with tok := K.tok + 2, terms := K.terms + 3 } (k + 2) =
      stage2NoEventWalkPotential K (k + 2) := rfl
  rw [hpot]
  omega

/-! ### The depth-zero terminal row

Both pairs' depth-zero route lands at `after_value` with `%sp.4 = 0`.  There the
`%cmp355` test holds, `%cmp358` carries `k + 2 < nep`, and `if.then357` sends the
walk to `accept` when `k + 2 = nep` or to `if.then360`'s refusal when
`k + 2 < nep`.  No `Stage2NoEventWalkCycleSrc` exists at depth zero (`spNe` is
refuted by `%sp.4 = 0`), so the row is `Stage2NoEventWalkRow.terminal` in both
cases.

The record's two post words — `Stage2NoEventRun` at the returned memory and the
boundary there — are the caller's evidence, at the exact memories the two arms
return; they are the only fields the route cannot supply.  The refusal's index
read `%ep[%k.6]` is the route's own: `readLanes32`'s lane at `k + 2` is the word
`if.then360` loads, so its bound is the invariant's `inside`.  `cleanup580` reads
`%xj`, which `Head` binds at `K.next0` (the entry block's first allocation) while
`Locals` names `K.xj`; the two agree at every head, so the equality is
`Head.inv`'s (`h.inv.xjNext0`) and is read from the head rather than taken beside
it. -/

/-- **The base lookups give the parameters.** -/
theorem stage2NoEventWalkBaseLookups_params {K : Stage2NoEventWalkCarry} {s : State}
    (h : Stage2NoEventWalkBaseLookups K s) : Stage2NoEventWalkParams K s where
  b := h _ _ (by simp [stage2NoEventWalkBaseValues, stage2NoEventWalkParamEntries])
  n := h _ _ (by simp [stage2NoEventWalkBaseValues, stage2NoEventWalkParamEntries])
  ep := h _ _ (by simp [stage2NoEventWalkBaseValues, stage2NoEventWalkParamEntries])
  nep := h _ _ (by simp [stage2NoEventWalkBaseValues, stage2NoEventWalkParamEntries])
  xp := h _ _ (by simp [stage2NoEventWalkBaseValues, stage2NoEventWalkParamEntries])
  nxp := h _ _ (by simp [stage2NoEventWalkBaseValues, stage2NoEventWalkParamEntries])
  scratch := h _ _ (by simp [stage2NoEventWalkBaseValues, stage2NoEventWalkParamEntries])
  scratchcap :=
    h _ _ (by simp [stage2NoEventWalkBaseValues, stage2NoEventWalkParamEntries])
  tokensOut :=
    h _ _ (by simp [stage2NoEventWalkBaseValues, stage2NoEventWalkParamEntries])
  valuesOut :=
    h _ _ (by simp [stage2NoEventWalkBaseValues, stage2NoEventWalkParamEntries])
  sumOut := h _ _ (by simp [stage2NoEventWalkBaseValues, stage2NoEventWalkParamEntries])
  err := h _ _ (by simp [stage2NoEventWalkBaseValues, stage2NoEventWalkParamEntries])
  stk := h _ _ (by simp [stage2NoEventWalkBaseValues, stage2NoEventWalkParamEntries])
  e := h _ _ (by simp [stage2NoEventWalkBaseValues, stage2NoEventWalkParamEntries])
  c := h _ _ (by simp [stage2NoEventWalkBaseValues, stage2NoEventWalkParamEntries])
  d := h _ _ (by simp [stage2NoEventWalkBaseValues, stage2NoEventWalkParamEntries])

/-- **The base lookups give the entry block's locals**, at a carry whose cursor
`%xj` is the entry's first allocation (`K.xj = K.next0`); a producer reads that
equality from the head's invariant (`Head.inv.xjNext0`). -/
theorem stage2NoEventWalkBaseLookups_locals {K : Stage2NoEventWalkCarry} {s : State}
    (h : Stage2NoEventWalkBaseLookups K s) (hcur : K.xj = K.next0) :
    Stage2NoEventWalkLocals K s where
  xj := by
    rw [hcur]
    exact h "%xj" (.ptr K.next0)
      (by simp [stage2NoEventWalkBaseValues, stage2NoEventWalkBaseCellValues,
        preHeaderCells, entryCells1, entryCells2, entryCells3, entryCells4])
  off := h "%off" (.ptr (K.e + 8))
    (by simp [stage2NoEventWalkBaseValues, stage2NoEventWalkBaseCellValues,
      preHeaderCells, entryCells1, entryCells2, entryCells3, entryCells4])

/-- **The empty array at depth zero is a terminal row**: the acceptance when the
closer's entry is the last, the refusal otherwise. -/
noncomputable def stage2NoEventWalkBracketZeroTerminal {gap : Calls}
    {mem : Mem} {F : Nat} {K : Stage2NoEventWalkCarry} {k : Nat} {s : State}
    (h : Stage2NoEventWalkHead K mem k s)
    (htrace : Stage2NoEventWalkTrace K)
    {lane : Nat} {byte : UInt8}
    (hk : K.ent[k]? = some lane) (hbs : K.bs[lane]? = some byte) (hb : byte.toNat = 91)
    {next : Nat} {nextByte : UInt8}
    (hbs1 : K.bs[next]? = some nextByte)
    (hb1 : nextByte.toNat = 93)
    (hspZ : lookupName s.env "%sp.0.ph1403" =
      some (.int 32 (BitVec.ofNat 32 0)))
    (hkbound : k + 2 ≤ K.nep) (hk63 : k + 3 < 2 ^ 63)
    {bs4 : List UInt8}
    (hlane : readBytes s.mem (K.ep + (BitVec.ofNat 64 (k + 1)).toNat * 4) 4 = some bs4)
    (hval4lt : bytesToNat bs4 < 2 ^ 32)
    (hbyte1 : readBytes s.mem
      (K.b + (BitVec.signExtend 64 (BitVec.ofNat 64 (bytesToNat bs4))).toNat) 1
      = some [nextByte])
    (hreportAcc : Stage2NoEventRun K.a12 mem
      (stage2NoEventAcceptMem s.mem K.tokensOut K.valuesOut K.sumOut
        (BitVec.ofNat 64 (K.tok + 2))
        (BitVec.ofNat 64 (K.terms + 7) + BitVec.ofNat 64 K.arenaWord)))
    (hboundAcc : stage2NoEventBoundary K.a12 mem K.next0
      (stage2NoEventAcceptMem s.mem K.tokensOut K.valuesOut K.sumOut
        (BitVec.ofNat 64 (K.tok + 2))
        (BitVec.ofNat 64 (K.terms + 7) + BitVec.ofNat 64 K.arenaWord))
      (.int 64 1))
    (hreportRef : ∀ q : Nat, K.ent[k + 2]? = some q →
      Stage2NoEventRun K.a12 mem
        (stage2NoEventErrMem s.mem K.tokensOut K.valuesOut K.sumOut K.err
          (BitVec.ofNat 64 q))) :
    Stage2NoEventWalkRow (stage2NoEventCalls gap) mem F K k s := by
  refine Classical.choice ?_
  classical
  have stateAt_self : ∀ s : State, stateAt s.env s = s := by
    intro s; cases s; rfl
  let K' : Stage2NoEventWalkCarry := { K with tok := K.tok + 2, terms := K.terms + 7 }
  obtain ⟨sE, hseg0, hpcE, hpreE, hframe4, hsp3, hk5, halen7, harena9, hterms7,
    htok7, hnepE, hmemE, hbaseE0, htraceE0⟩ :=
    stage2NoEventWalkBracketZeroRoute (calls := stage2NoEventCalls gap)
      h htrace hk hbs hb hbs1 hb1 hspZ hkbound hk63 hlane hval4lt hbyte1
  have hseg : Stage2NoEventWalkSegment (stage2NoEventCalls gap) mem K s K' sE 9 := hseg0
  have hbaseE : Stage2NoEventWalkBaseLookups K' sE := hbaseE0
  have htraceE : Stage2NoEventWalkTrace K' := htraceE0
  let c0 : BitVec 1 :=
    evalICmp .ult (BitVec.ofNat 64 (k + 2)) (BitVec.ofNat 64 K.nep)
  let sA : State := stage2NoEventWalkNext
    (cells (afterValueZeroDispatchCells c0)
      (cells (afterValuePhiCells 1 0 (k + 2) K.arena.length K.arenaWord
        (K.terms + 7) (K.tok + 2)) sE.env)) sE "if.then357"
  have hA : Stage2NoEventWalkLink (stage2NoEventCalls gap) K' mem sE K' sA := by
    have hl := link_afterValue_zero_close_arr (calls := stage2NoEventCalls gap)
      (K := K') (s := sE) (fr := 1) (k := k + 2) (alen := K.arena.length)
      (arena := K.arenaWord) (terms := K.terms + 7) (tok := K.tok + 2)
      (nep := K.nep) hseg.inv' hpcE hpreE hframe4 hsp3 hk5 halen7 harena9
      (by simpa only [stage2NoEventWalkOfNat_add] using hterms7)
      (by simpa only [stage2NoEventWalkOfNat_add] using htok7) hnepE
    simpa only [sA, K'] using hl
  have hcmpA : lookupName sA.env "%cmp358" = some (.int 1 c0) := by
    simp only [sA, stage2NoEventWalkNext, afterValueZeroDispatchCells, cells]
    exact lookupName_cons_self _ _ _
  have hbaseA : Stage2NoEventWalkBaseLookups K' sA := by
    have hphi := stage2NoEventCycleBase (K := K') (env := sE.env) hbaseE
      (cs := afterValuePhiCells 1 0 (k + 2) K.arena.length K.arenaWord
        (K.terms + 7) (K.tok + 2))
      (names := ["%tokens.8", "%terms.8", "%arena.10", "%alen.8", "%k.6",
        "%sp.4", "%frame.6"]) rfl (by decide)
    exact stage2NoEventCycleBase (K := K')
      (env := cells (afterValuePhiCells 1 0 (k + 2) K.arena.length K.arenaWord
        (K.terms + 7) (K.tok + 2)) sE.env)
      hphi (cs := afterValueZeroDispatchCells c0) (names := ["%cmp358", "%cmp355"])
      rfl (by decide)
  by_cases hlast : k + 2 = K.nep
  · have hc0 : c0 = 0 := by
      show evalICmp .ult (BitVec.ofNat 64 (k + 2)) (BitVec.ofNat 64 K.nep) = 0
      rw [← hlast]
      exact stage2NoEventICmp_ult_zero (w := 64) (x := k + 2) (y := k + 2)
        (by omega) (by omega) (by omega)
    let sB : State := stage2NoEventWalkNext sA.env sA "accept"
    have hT : Stage2NoEventWalkLink (stage2NoEventCalls gap) K' mem sA K' sB := by
      have hl := link_ifThen357_false (calls := stage2NoEventCalls gap) (K := K')
        hA.inv' (by simp only [sA, stage2NoEventWalkNext])
        (by rw [hcmpA, hc0])
      simpa only [sB] using hl
    have hbaseB : Stage2NoEventWalkBaseLookups K sB := hbaseA
    have hparB : Stage2NoEventWalkParams K sB :=
      stage2NoEventWalkBaseLookups_params hbaseB
    have hlocB : Stage2NoEventWalkLocals K sB :=
      stage2NoEventWalkBaseLookups_locals hbaseB h.inv.xjNext0
    have htok8 : lookupName sB.env "%tokens.8" =
        some (.int 64 (BitVec.ofNat 64 (K.tok + 2))) := by
      simp only [sB, sA, stage2NoEventWalkNext, afterValueZeroDispatchCells,
        afterValuePhiCells, cells]
      rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide)]
      exact lookupName_cons_self _ _ _
    have hterms8 : lookupName sB.env "%terms.8" =
        some (.int 64 (BitVec.ofNat 64 (K.terms + 7))) := by
      simp only [sB, sA, stage2NoEventWalkNext, afterValueZeroDispatchCells,
        afterValuePhiCells, cells]
      rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
        lookupName_cons_ne _ _ (by decide)]
      exact lookupName_cons_self _ _ _
    have harena10 : lookupName sB.env "%arena.10" =
        some (.int 64 (BitVec.ofNat 64 K.arenaWord)) := by
      simp only [sB, sA, stage2NoEventWalkNext, afterValueZeroDispatchCells,
        afterValuePhiCells, cells]
      rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
        lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide)]
      exact lookupName_cons_self _ _ _
    have haccB : Stage2NoEventWalkAcceptAcc K' sB := ⟨htok8, hterms8, harena10⟩
    have hmemB : sB.mem = s.mem := by
      simp only [sB, sA, stage2NoEventWalkNext]
      exact hmemE
    let acceptMem : Mem := stage2NoEventAcceptMem s.mem K.tokensOut K.valuesOut K.sumOut
      (BitVec.ofNat 64 (K.tok + 2))
      (BitVec.ofNat 64 (K.terms + 7) + BitVec.ofNat 64 K.arenaWord)
    let sT : State := stateAt
      (("%add579", .int 64 (BitVec.ofNat 64 (K.terms + 7) +
        BitVec.ofNat 64 K.arenaWord)) :: sB.env)
      (stage2NoEventJumpState sB acceptMem sB.next "cleanup580" "accept")
    have hstep : step (stage2NoEventCalls gap) stage2NoEventBody sB = .jump sT := by
      have hl := stage2NoEventAccept_step (gap := gap) sB.env sB
        (tok := K.tok + 2) (terms := K.terms + 7) (arenaWord := K.arenaWord)
        (tokensOut := K.tokensOut) (valuesOut := K.valuesOut) (sumOut := K.sumOut)
        (by simp only [sB, stage2NoEventWalkNext]) haccB.tokens haccB.terms
        haccB.arena hparB.tokensOut hparB.valuesOut hparB.sumOut
      rw [← stateAt_self sB]
      rw [hmemB] at hl
      exact hl
    have hinc1 : phiIncoming "accept" cleanup580Incoming =
        some (.imm (.int 64 1)) := by decide
    let sR : State := stateAt (("%retval.14", .int 64 1) :: sT.env) sT
    have hclean : step (stage2NoEventCalls gap) stage2NoEventBody sT =
        .ret (some (.int 64 1)) sR := by
      have hl := stage2NoEventCleanup_step (gap := gap) sT.env sT "accept"
        (by simp only [sT, stage2NoEventJumpState, stateAt])
        (by simp only [sT, stage2NoEventJumpState, stateAt]) hinc1
        (by
          simp only [sT, stage2NoEventJumpState, stateAt]
          rw [lookupName_cons_ne _ _ (by decide)]
          exact hparB.c)
        (by
          simp only [sT, stage2NoEventJumpState, stateAt]
          rw [lookupName_cons_ne _ _ (by decide)]
          exact hparB.e)
        (by
          simp only [sT, stage2NoEventJumpState, stateAt]
          rw [lookupName_cons_ne _ _ (by decide)]
          exact hparB.stk)
        (by
          simp only [sT, stage2NoEventJumpState, stateAt]
          rw [lookupName_cons_ne _ _ (by decide)]
          exact hlocB.xj)
      rw [← stateAt_self sT]
      exact hl
    have hmR : sR.mem = acceptMem := by
      simp only [sR, sT, stateAt, stage2NoEventJumpState]
    have hcost : 11 + 1 ≤ stage2NoEventWalkPotential K k + F := by
      have hpot : 64 ≤ stage2NoEventWalkPotential K k := by
        unfold stage2NoEventWalkPotential
        have hge : 2 ≤ K.nep - k := by omega
        have hmul : 32 * 2 ≤ 32 * (K.nep - k) := Nat.mul_le_mul_left 32 hge
        omega
      omega
    obtain ⟨obs, toks, hrel, hobsLen, htermsEq, -⟩ := htraceE
    have hj : ∀ n, runFuel (stage2NoEventCalls gap) (11 + n) stage2NoEventBody s =
        runFuel (stage2NoEventCalls gap) n stage2NoEventBody sB := by
      intro n
      rw [show 11 + n = 9 + (2 + n) from by omega, hseg.run (2 + n),
        show 2 + n = 1 + (1 + n) from by omega,
        stage2NoEventWalkLink_runFuel hA (1 + n),
        stage2NoEventWalkLink_runFuel hT n]
    have haccT : Stage2NoEventWalkAcceptAcc K' sT := by
      refine ⟨?_, ?_, ?_⟩
      · simp only [sT, stage2NoEventJumpState, stateAt]
        rw [lookupName_cons_ne _ _ (by decide)]
        exact htok8
      · simp only [sT, stage2NoEventJumpState, stateAt]
        rw [lookupName_cons_ne _ _ (by decide)]
        exact hterms8
      · simp only [sT, stage2NoEventJumpState, stateAt]
        rw [lookupName_cons_ne _ _ (by decide)]
        exact harena10
    exact ⟨stage2NoEventWalkTerminalRow
      (stage2NoEventAccept_exit (gap := gap) (K := K) (K' := K') (s := s)
        (sE := sB) (sT := sT) (sR := sR) (j := 11) (m := acceptMem)
        (obs := obs) (toks := toks) hj hstep hclean hmR hcost
        (by show K.tok < K.tok + 2; omega) rfl rfl
        haccT hrel hobsLen htermsEq hreportAcc hboundAcc)⟩
  · have hlt : k + 2 < K.nep := by omega
    have hc1 : c0 = 1 := by
      show evalICmp .ult (BitVec.ofNat 64 (k + 2)) (BitVec.ofNat 64 K.nep) = 1
      exact stage2NoEventICmp_ult_one (w := 64) (x := k + 2) (y := K.nep)
        (by omega) (by simpa using h.inv.nepLt) (by omega)
    let sB : State := stage2NoEventWalkNext sA.env sA "if.then360"
    have hT : Stage2NoEventWalkLink (stage2NoEventCalls gap) K' mem sA K' sB := by
      have hl := link_ifThen357_true (calls := stage2NoEventCalls gap) (K := K')
        hA.inv' (by simp only [sA, stage2NoEventWalkNext])
        (by rw [hcmpA, hc1])
      simpa only [sB] using hl
    have hbaseB : Stage2NoEventWalkBaseLookups K sB := hbaseA
    have hparB : Stage2NoEventWalkParams K sB :=
      stage2NoEventWalkBaseLookups_params hbaseB
    have hlocB : Stage2NoEventWalkLocals K sB :=
      stage2NoEventWalkBaseLookups_locals hbaseB h.inv.xjNext0
    have hk6B : lookupName sB.env "%k.6" =
        some (.int 64 (BitVec.ofNat 64 (k + 2))) := by
      simp only [sB, sA, stage2NoEventWalkNext, afterValueZeroDispatchCells,
        afterValuePhiCells, cells]
      rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
        lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
        lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide)]
      exact lookupName_cons_self _ _ _
    have hepB : lookupName sB.env "%ep" = some (.ptr K.ep) := hparB.ep
    obtain ⟨q, bs, hq2, hq32, hread', hval⟩ := h.laneAt (i := k + 2) (by omega)
    have hlenbs : bs.length = 4 := readBytes_length_some hread'
    have hbsq : natToBytes q 4 = bs := by
      rw [← hval, ← hlenbs]
      have h := natToBytes_bytesToNat bs bs.length (Nat.le_refl _)
      have hl : (natToBytes (bytesToNat bs) bs.length).length ≤ bs.length := by
        rw [natToBytes_length]
      rw [List.take_of_length_le hl] at h
      exact h
    have hsign : ((BitVec.ofNat 64 (k + 2)).signExtend 64).toNat = k + 2 := by
      simp only [BitVec.signExtend_eq, BitVec.setWidth_eq, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega : k + 2 < 2 ^ 64)]
    have hmemB : sB.mem = s.mem := by
      simp only [sB, sA, stage2NoEventWalkNext]
      exact hmemE
    have htoNat32 : (BitVec.ofNat 32 q).toNat = q := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : q < 2 ^ 32)]
    have hreadB : readBytes sB.mem
        (K.ep + ((BitVec.ofNat 64 (k + 2)).signExtend 64).toNat * 4) 4
        = some (natToBytes (BitVec.ofNat 32 q).toNat 4) := by
      rw [hmemB, hsign, show K.ep + (k + 2) * 4 = K.ep + 4 * (k + 2) from by omega,
        htoNat32, hbsq]
      exact hread'
    have hpos : ((BitVec.ofNat 64 (k + 2)).signExtend 64).toNat < 2 ^ 63 := by
      rw [hsign]; omega
    have htoNatq : (BitVec.ofNat 64 q).toNat = q := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : q < 2 ^ 64)]
    have hle : (BitVec.ofNat 64 q).toNat ≤ K.n := by
      rw [htoNatq]
      have hmemq : q ∈ K.ent := by
        obtain ⟨hlt2, hget2⟩ := List.getElem?_eq_some_iff.mp hq2
        simpa only [hget2] using List.getElem_mem hlt2
      exact Nat.le_of_lt (h.inv.inside q hmemq)
    have hconv : (BitVec.ofNat 64 q) =
        BitVec.ofNat 64 (BitVec.ofNat 32 q).toNat := by
      rw [htoNat32]
    have hj : ∀ n, runFuel (stage2NoEventCalls gap) (11 + n) stage2NoEventBody s =
        runFuel (stage2NoEventCalls gap) n stage2NoEventBody sB := by
      intro n
      rw [show 11 + n = 9 + (2 + n) from by omega, hseg.run (2 + n),
        show 2 + n = 1 + (1 + n) from by omega,
        stage2NoEventWalkLink_runFuel hA (1 + n),
        stage2NoEventWalkLink_runFuel hT n]
    have hcost : 11 + 1 ≤ stage2NoEventWalkPotential K k + F := by
      have hpot : 64 ≤ stage2NoEventWalkPotential K k := by
        unfold stage2NoEventWalkPotential
        have hge : 2 ≤ K.nep - k := by omega
        have hmul : 32 * 2 ≤ 32 * (K.nep - k) := Nat.mul_le_mul_left 32 hge
        omega
      omega
    have hrouteFrame : UnchangedOutside s.mem sB.mem
        (stage2NoEventRunRegions K.scratch K.scratchcap K.stk K.e K.c K.d ++
          [(K.next0, K.nextEnd - K.next0)]) := by
      rw [hmemB]
      exact UnchangedOutside.refl' s.mem _
    have hreportRefB : Stage2NoEventRun K.a12 mem
        (stage2NoEventErrMem sB.mem K.tokensOut K.valuesOut K.sumOut K.err
          (BitVec.ofNat 64 q)) := by
      rw [hmemB]
      exact hreportRef q hq2
    exact ⟨stage2NoEventWalkTerminalRow
      (stage2NoEventIfThen360_exit (gap := gap) (K := K) (s := s) (sE := sB)
        (j := 11) (idx6 := BitVec.ofNat 64 (k + 2)) (x32 := BitVec.ofNat 32 q)
        (x64 := BitVec.ofNat 64 q) hj (by simp only [sB, stage2NoEventWalkNext])
        hepB hk6B hpos hreadB hconv (by decide) hparB hlocB hle hcost hreportRefB
        htrace hrouteFrame h.inv)⟩

/-- **The empty object at depth zero is a terminal row**: the acceptance when the
closer's entry is the last, the refusal otherwise. -/
noncomputable def stage2NoEventWalkBraceZeroTerminal {gap : Calls}
    {mem : Mem} {F : Nat} {K : Stage2NoEventWalkCarry} {k : Nat} {s : State}
    (h : Stage2NoEventWalkHead K mem k s)
    (htrace : Stage2NoEventWalkTrace K)
    {lane : Nat} {byte : UInt8}
    (hk : K.ent[k]? = some lane) (hbs : K.bs[lane]? = some byte) (hb : byte.toNat = 123)
    {next : Nat} {nextByte : UInt8}
    (hbs1 : K.bs[next]? = some nextByte)
    (hb1 : nextByte.toNat = 125)
    (hspZ : lookupName s.env "%sp.0.ph1403" =
      some (.int 32 (BitVec.ofNat 32 0)))
    (hkbound : k + 2 ≤ K.nep) (hk63 : k + 3 < 2 ^ 63)
    {bs4 : List UInt8}
    (hlane : readBytes s.mem (K.ep + (BitVec.ofNat 64 (k + 1)).toNat * 4) 4 = some bs4)
    (hval4lt : bytesToNat bs4 < 2 ^ 32)
    (hbyte1 : readBytes s.mem
      (K.b + (BitVec.signExtend 64 (BitVec.ofNat 64 (bytesToNat bs4))).toNat) 1
      = some [nextByte])
    (hreportAcc : Stage2NoEventRun K.a12 mem
      (stage2NoEventAcceptMem s.mem K.tokensOut K.valuesOut K.sumOut
        (BitVec.ofNat 64 (K.tok + 2))
        (BitVec.ofNat 64 (K.terms + 3) + BitVec.ofNat 64 K.arenaWord)))
    (hboundAcc : stage2NoEventBoundary K.a12 mem K.next0
      (stage2NoEventAcceptMem s.mem K.tokensOut K.valuesOut K.sumOut
        (BitVec.ofNat 64 (K.tok + 2))
        (BitVec.ofNat 64 (K.terms + 3) + BitVec.ofNat 64 K.arenaWord))
      (.int 64 1))
    (hreportRef : ∀ q : Nat, K.ent[k + 2]? = some q →
      Stage2NoEventRun K.a12 mem
        (stage2NoEventErrMem s.mem K.tokensOut K.valuesOut K.sumOut K.err
          (BitVec.ofNat 64 q))) :
    Stage2NoEventWalkRow (stage2NoEventCalls gap) mem F K k s := by
  refine Classical.choice ?_
  classical
  have stateAt_self : ∀ s : State, stateAt s.env s = s := by
    intro s; cases s; rfl
  let K' : Stage2NoEventWalkCarry := { K with tok := K.tok + 2, terms := K.terms + 3 }
  obtain ⟨sE, hseg0, hpcE, hpreE, hdecE, hk4E, halenE, harenaE, htermsE, htokE,
    hnepE, hmemE, hbaseE0, htraceE0⟩ :=
    stage2NoEventWalkBraceZeroRoute (calls := stage2NoEventCalls gap)
      h htrace hk hbs hb hbs1 hb1 hspZ hkbound hk63 hlane hval4lt hbyte1
  have hseg : Stage2NoEventWalkSegment (stage2NoEventCalls gap) mem K s K' sE 11 := hseg0
  have hbaseE : Stage2NoEventWalkBaseLookups K' sE := hbaseE0
  have htraceE : Stage2NoEventWalkTrace K' := htraceE0
  have hdec0 : (BitVec.ofNat 32 0 + BitVec.ofNat 32 1 +
      BitVec.ofNat 32 4294967295) = BitVec.ofNat 32 0 := by decide
  let c0 : BitVec 1 :=
    evalICmp .ult (BitVec.ofNat 64 (k + 2)) (BitVec.ofNat 64 K.nep)
  let sA : State := stage2NoEventWalkNext
    (cells (afterValueZeroDispatchCells c0)
      (cells (afterValuePhiCells 0 0 (k + 2) K.arena.length K.arenaWord
        (K.terms + 3) (K.tok + 2)) sE.env)) sE "if.then357"
  have hA : Stage2NoEventWalkLink (stage2NoEventCalls gap) K' mem sE K' sA := by
    have hl := link_afterValue_zero_close_obj (calls := stage2NoEventCalls gap)
      (K := K') (s := sE) (k := k + 2) (alen := K.arena.length)
      (arena := K.arenaWord) (terms := K.terms + 3) (tok := K.tok + 2)
      (nep := K.nep) (dec := BitVec.ofNat 32 0 + BitVec.ofNat 32 1 +
        BitVec.ofNat 32 4294967295)
      hseg.inv' hpcE hpreE hdecE hdec0 hk4E halenE harenaE
      (by simpa only [stage2NoEventWalkOfNat_add] using htermsE)
      (by simpa only [stage2NoEventWalkOfNat_add] using htokE) hnepE
    simpa only [sA, K'] using hl
  have hcmpA : lookupName sA.env "%cmp358" = some (.int 1 c0) := by
    simp only [sA, stage2NoEventWalkNext, afterValueZeroDispatchCells, cells]
    exact lookupName_cons_self _ _ _
  have hbaseA : Stage2NoEventWalkBaseLookups K' sA := by
    have hphi := stage2NoEventCycleBase (K := K') (env := sE.env) hbaseE
      (cs := afterValuePhiCells 0 0 (k + 2) K.arena.length K.arenaWord
        (K.terms + 3) (K.tok + 2))
      (names := ["%tokens.8", "%terms.8", "%arena.10", "%alen.8", "%k.6",
        "%sp.4", "%frame.6"]) rfl (by decide)
    exact stage2NoEventCycleBase (K := K')
      (env := cells (afterValuePhiCells 0 0 (k + 2) K.arena.length K.arenaWord
        (K.terms + 3) (K.tok + 2)) sE.env)
      hphi (cs := afterValueZeroDispatchCells c0) (names := ["%cmp358", "%cmp355"])
      rfl (by decide)
  by_cases hlast : k + 2 = K.nep
  · have hc0 : c0 = 0 := by
      show evalICmp .ult (BitVec.ofNat 64 (k + 2)) (BitVec.ofNat 64 K.nep) = 0
      rw [← hlast]
      exact stage2NoEventICmp_ult_zero (w := 64) (x := k + 2) (y := k + 2)
        (by omega) (by omega) (by omega)
    let sB : State := stage2NoEventWalkNext sA.env sA "accept"
    have hT : Stage2NoEventWalkLink (stage2NoEventCalls gap) K' mem sA K' sB := by
      have hl := link_ifThen357_false (calls := stage2NoEventCalls gap) (K := K')
        hA.inv' (by simp only [sA, stage2NoEventWalkNext])
        (by rw [hcmpA, hc0])
      simpa only [sB] using hl
    have hbaseB : Stage2NoEventWalkBaseLookups K sB := hbaseA
    have hparB : Stage2NoEventWalkParams K sB :=
      stage2NoEventWalkBaseLookups_params hbaseB
    have hlocB : Stage2NoEventWalkLocals K sB :=
      stage2NoEventWalkBaseLookups_locals hbaseB h.inv.xjNext0
    have htok8 : lookupName sB.env "%tokens.8" =
        some (.int 64 (BitVec.ofNat 64 (K.tok + 2))) := by
      simp only [sB, sA, stage2NoEventWalkNext, afterValueZeroDispatchCells,
        afterValuePhiCells, cells]
      rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide)]
      exact lookupName_cons_self _ _ _
    have hterms8 : lookupName sB.env "%terms.8" =
        some (.int 64 (BitVec.ofNat 64 (K.terms + 3))) := by
      simp only [sB, sA, stage2NoEventWalkNext, afterValueZeroDispatchCells,
        afterValuePhiCells, cells]
      rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
        lookupName_cons_ne _ _ (by decide)]
      exact lookupName_cons_self _ _ _
    have harena10 : lookupName sB.env "%arena.10" =
        some (.int 64 (BitVec.ofNat 64 K.arenaWord)) := by
      simp only [sB, sA, stage2NoEventWalkNext, afterValueZeroDispatchCells,
        afterValuePhiCells, cells]
      rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
        lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide)]
      exact lookupName_cons_self _ _ _
    have haccB : Stage2NoEventWalkAcceptAcc K' sB := ⟨htok8, hterms8, harena10⟩
    have hmemB : sB.mem = s.mem := by
      simp only [sB, sA, stage2NoEventWalkNext]
      exact hmemE
    let acceptMem : Mem := stage2NoEventAcceptMem s.mem K.tokensOut K.valuesOut K.sumOut
      (BitVec.ofNat 64 (K.tok + 2))
      (BitVec.ofNat 64 (K.terms + 3) + BitVec.ofNat 64 K.arenaWord)
    let sT : State := stateAt
      (("%add579", .int 64 (BitVec.ofNat 64 (K.terms + 3) +
        BitVec.ofNat 64 K.arenaWord)) :: sB.env)
      (stage2NoEventJumpState sB acceptMem sB.next "cleanup580" "accept")
    have hstep : step (stage2NoEventCalls gap) stage2NoEventBody sB = .jump sT := by
      have hl := stage2NoEventAccept_step (gap := gap) sB.env sB
        (tok := K.tok + 2) (terms := K.terms + 3) (arenaWord := K.arenaWord)
        (tokensOut := K.tokensOut) (valuesOut := K.valuesOut) (sumOut := K.sumOut)
        (by simp only [sB, stage2NoEventWalkNext]) haccB.tokens haccB.terms
        haccB.arena hparB.tokensOut hparB.valuesOut hparB.sumOut
      rw [← stateAt_self sB]
      rw [hmemB] at hl
      exact hl
    have hinc1 : phiIncoming "accept" cleanup580Incoming =
        some (.imm (.int 64 1)) := by decide
    let sR : State := stateAt (("%retval.14", .int 64 1) :: sT.env) sT
    have hclean : step (stage2NoEventCalls gap) stage2NoEventBody sT =
        .ret (some (.int 64 1)) sR := by
      have hl := stage2NoEventCleanup_step (gap := gap) sT.env sT "accept"
        (by simp only [sT, stage2NoEventJumpState, stateAt])
        (by simp only [sT, stage2NoEventJumpState, stateAt]) hinc1
        (by
          simp only [sT, stage2NoEventJumpState, stateAt]
          rw [lookupName_cons_ne _ _ (by decide)]
          exact hparB.c)
        (by
          simp only [sT, stage2NoEventJumpState, stateAt]
          rw [lookupName_cons_ne _ _ (by decide)]
          exact hparB.e)
        (by
          simp only [sT, stage2NoEventJumpState, stateAt]
          rw [lookupName_cons_ne _ _ (by decide)]
          exact hparB.stk)
        (by
          simp only [sT, stage2NoEventJumpState, stateAt]
          rw [lookupName_cons_ne _ _ (by decide)]
          exact hlocB.xj)
      rw [← stateAt_self sT]
      exact hl
    have hmR : sR.mem = acceptMem := by
      simp only [sR, sT, stateAt, stage2NoEventJumpState]
    have hcost : 13 + 1 ≤ stage2NoEventWalkPotential K k + F := by
      have hpot : 64 ≤ stage2NoEventWalkPotential K k := by
        unfold stage2NoEventWalkPotential
        have hge : 2 ≤ K.nep - k := by omega
        have hmul : 32 * 2 ≤ 32 * (K.nep - k) := Nat.mul_le_mul_left 32 hge
        omega
      omega
    obtain ⟨obs, toks, hrel, hobsLen, htermsEq, -⟩ := htraceE
    have hj : ∀ n, runFuel (stage2NoEventCalls gap) (13 + n) stage2NoEventBody s =
        runFuel (stage2NoEventCalls gap) n stage2NoEventBody sB := by
      intro n
      rw [show 13 + n = 11 + (2 + n) from by omega, hseg.run (2 + n),
        show 2 + n = 1 + (1 + n) from by omega,
        stage2NoEventWalkLink_runFuel hA (1 + n),
        stage2NoEventWalkLink_runFuel hT n]
    have haccT : Stage2NoEventWalkAcceptAcc K' sT := by
      refine ⟨?_, ?_, ?_⟩
      · simp only [sT, stage2NoEventJumpState, stateAt]
        rw [lookupName_cons_ne _ _ (by decide)]
        exact htok8
      · simp only [sT, stage2NoEventJumpState, stateAt]
        rw [lookupName_cons_ne _ _ (by decide)]
        exact hterms8
      · simp only [sT, stage2NoEventJumpState, stateAt]
        rw [lookupName_cons_ne _ _ (by decide)]
        exact harena10
    exact ⟨stage2NoEventWalkTerminalRow
      (stage2NoEventAccept_exit (gap := gap) (K := K) (K' := K') (s := s)
        (sE := sB) (sT := sT) (sR := sR) (j := 13) (m := acceptMem)
        (obs := obs) (toks := toks) hj hstep hclean hmR hcost
        (by show K.tok < K.tok + 2; omega) rfl rfl
        haccT hrel hobsLen htermsEq hreportAcc hboundAcc)⟩
  · have hlt : k + 2 < K.nep := by omega
    have hc1 : c0 = 1 := by
      show evalICmp .ult (BitVec.ofNat 64 (k + 2)) (BitVec.ofNat 64 K.nep) = 1
      exact stage2NoEventICmp_ult_one (w := 64) (x := k + 2) (y := K.nep)
        (by omega) (by simpa using h.inv.nepLt) (by omega)
    let sB : State := stage2NoEventWalkNext sA.env sA "if.then360"
    have hT : Stage2NoEventWalkLink (stage2NoEventCalls gap) K' mem sA K' sB := by
      have hl := link_ifThen357_true (calls := stage2NoEventCalls gap) (K := K')
        hA.inv' (by simp only [sA, stage2NoEventWalkNext])
        (by rw [hcmpA, hc1])
      simpa only [sB] using hl
    have hbaseB : Stage2NoEventWalkBaseLookups K sB := hbaseA
    have hparB : Stage2NoEventWalkParams K sB :=
      stage2NoEventWalkBaseLookups_params hbaseB
    have hlocB : Stage2NoEventWalkLocals K sB :=
      stage2NoEventWalkBaseLookups_locals hbaseB h.inv.xjNext0
    have hk6B : lookupName sB.env "%k.6" =
        some (.int 64 (BitVec.ofNat 64 (k + 2))) := by
      simp only [sB, sA, stage2NoEventWalkNext, afterValueZeroDispatchCells,
        afterValuePhiCells, cells]
      rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
        lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
        lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide)]
      exact lookupName_cons_self _ _ _
    have hepB : lookupName sB.env "%ep" = some (.ptr K.ep) := hparB.ep
    obtain ⟨q, bs, hq2, hq32, hread', hval⟩ := h.laneAt (i := k + 2) (by omega)
    have hlenbs : bs.length = 4 := readBytes_length_some hread'
    have hbsq : natToBytes q 4 = bs := by
      rw [← hval, ← hlenbs]
      have h := natToBytes_bytesToNat bs bs.length (Nat.le_refl _)
      have hl : (natToBytes (bytesToNat bs) bs.length).length ≤ bs.length := by
        rw [natToBytes_length]
      rw [List.take_of_length_le hl] at h
      exact h
    have hsign : ((BitVec.ofNat 64 (k + 2)).signExtend 64).toNat = k + 2 := by
      simp only [BitVec.signExtend_eq, BitVec.setWidth_eq, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega : k + 2 < 2 ^ 64)]
    have hmemB : sB.mem = s.mem := by
      simp only [sB, sA, stage2NoEventWalkNext]
      exact hmemE
    have htoNat32 : (BitVec.ofNat 32 q).toNat = q := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : q < 2 ^ 32)]
    have hreadB : readBytes sB.mem
        (K.ep + ((BitVec.ofNat 64 (k + 2)).signExtend 64).toNat * 4) 4
        = some (natToBytes (BitVec.ofNat 32 q).toNat 4) := by
      rw [hmemB, hsign, show K.ep + (k + 2) * 4 = K.ep + 4 * (k + 2) from by omega,
        htoNat32, hbsq]
      exact hread'
    have hpos : ((BitVec.ofNat 64 (k + 2)).signExtend 64).toNat < 2 ^ 63 := by
      rw [hsign]; omega
    have htoNatq : (BitVec.ofNat 64 q).toNat = q := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : q < 2 ^ 64)]
    have hle : (BitVec.ofNat 64 q).toNat ≤ K.n := by
      rw [htoNatq]
      have hmemq : q ∈ K.ent := by
        obtain ⟨hlt2, hget2⟩ := List.getElem?_eq_some_iff.mp hq2
        simpa only [hget2] using List.getElem_mem hlt2
      exact Nat.le_of_lt (h.inv.inside q hmemq)
    have hconv : (BitVec.ofNat 64 q) =
        BitVec.ofNat 64 (BitVec.ofNat 32 q).toNat := by
      rw [htoNat32]
    have hj : ∀ n, runFuel (stage2NoEventCalls gap) (13 + n) stage2NoEventBody s =
        runFuel (stage2NoEventCalls gap) n stage2NoEventBody sB := by
      intro n
      rw [show 13 + n = 11 + (2 + n) from by omega, hseg.run (2 + n),
        show 2 + n = 1 + (1 + n) from by omega,
        stage2NoEventWalkLink_runFuel hA (1 + n),
        stage2NoEventWalkLink_runFuel hT n]
    have hcost : 13 + 1 ≤ stage2NoEventWalkPotential K k + F := by
      have hpot : 64 ≤ stage2NoEventWalkPotential K k := by
        unfold stage2NoEventWalkPotential
        have hge : 2 ≤ K.nep - k := by omega
        have hmul : 32 * 2 ≤ 32 * (K.nep - k) := Nat.mul_le_mul_left 32 hge
        omega
      omega
    have hrouteFrame : UnchangedOutside s.mem sB.mem
        (stage2NoEventRunRegions K.scratch K.scratchcap K.stk K.e K.c K.d ++
          [(K.next0, K.nextEnd - K.next0)]) := by
      rw [hmemB]
      exact UnchangedOutside.refl' s.mem _
    have hreportRefB : Stage2NoEventRun K.a12 mem
        (stage2NoEventErrMem sB.mem K.tokensOut K.valuesOut K.sumOut K.err
          (BitVec.ofNat 64 q)) := by
      rw [hmemB]
      exact hreportRef q hq2
    exact ⟨stage2NoEventWalkTerminalRow
      (stage2NoEventIfThen360_exit (gap := gap) (K := K) (s := s) (sE := sB)
        (j := 13) (idx6 := BitVec.ofNat 64 (k + 2)) (x32 := BitVec.ofNat 32 q)
        (x64 := BitVec.ofNat 64 q) hj (by simp only [sB, stage2NoEventWalkNext])
        hepB hk6B hpos hreadB hconv (by decide) hparB hlocB hle hcost hreportRefB
        htrace hrouteFrame h.inv)⟩

/-! ### Axiom footprints -/

#print axioms stage2NoEventWalkBracketZeroRoute
#print axioms stage2NoEventWalkBraceZeroRoute
#print axioms stage2NoEventWalkBracketZeroRoute_price
#print axioms stage2NoEventWalkBraceZeroRoute_price
#print axioms stage2NoEventWalkBracketZeroTerminal
#print axioms stage2NoEventWalkBraceZeroTerminal
