/-
The no-event walk's object-member pair: the second half of the shared cycle.

The class rows end where a value has been consumed; the cycle module
(`JsonStage2NoEventWalkCycleA`) takes the after-value endpoint back to the next
head with an index delta of one.  The object-member path does not reach the
backedge through `after_value` at all: it reaches it from `if.end303`, the block
between `expect_colon` and the value.

    key route → expect_colon → if.end303 → value.outer.backedge
      → if.end.peel → NodeBlock5

`if.end303` adds the key's own contribution to the two readings
(`%terms.2 = %add177.pn + %terms.1`, `%tokens.2 = %tokens.1 + 1`), advances the
index by four (`%inc304 = %k.1.in + 4` — the entry after the colon), reads the
entry after the key's closing quote and requires its document byte to be `:`,
and takes `value.outer.backedge` on that test.  The backedge and the head are the
same blocks the after-value path uses; only the edge and the seven carried
readings differ (`%frame.0.ph.be = imm 0`, `%k.0.ph.be = %inc304`, and the four
readings at `%alen.2`/`%arena.3`/`%terms.2`/`%tokens.2`).

This module owns that block's denotation, its `PhiSelects` at the `if.end303`
edge, and a `d = 4` instance of `Stage2NoEventWalkCycle`: from the state at
`if.end303`'s entry — the class lane's pair endpoint — to the head at index
`k + 4`, with the delta the block's two adds give and the credit discharged from
`Φ K k`.  The step count is three (the block, the backedge, the head read).  The
backedge's `phi` run and its five computed cells, and the head's read, are
`JsonStage2NoEventWalkCycleA`'s lemmas (`outerBackedge_phi_denote`,
`outerBackedge_tail_denote`, `loopHeadBackedge_denote`), instantiated at the
pair's readings; what this module adds at the backedge is the edge's
`PhiSelects` and the block's two-step composition
(`outerBackedge_ifEnd303_denote`), because `CycleA` bundles that composition at
`LeafBlock37`'s edge only.  There is no second cycle structure.

**The carry's index.**  The structure's `K` is the carry at the *target* head:
the block's two adds are the pair's contribution, so the endpoint's leftover
`%terms.1`/`%tokens.1` are related to `K` by `Stage2NoEventWalkPairSrc.termsEq`/
`tokEq` rather than being equal to it.  The invariant does not pin the two
counts, so it holds at the endpoint under the target's carry.

**What this module does not prove.**  The key route itself is the container
lane's, in both shapes that reach `expect_colon`: the first member's
`if.end.peel → NodeBlock5 → LeafBlock3 → if.then9 → if.end74 → NodeBlock21
→ LeafBlock17 → key_body → if.end136 → for.cond.cleanup`/`do.body172
→ expect_colon`, and the later members' comma route (`if.end409 → if.end111
→ key_body`).  Neither runs `after_value`, so the endpoint carries no
`%frame.6` and this module requires none: the backedge's frame reading is the
immediate zero (`if.end303`'s incoming operand for `%frame.0.ph.be`).  This
module takes the endpoint as `Stage2NoEventWalkPairSrc` and reads only its
registers and the invariant.  The test's false arm — `%cmp309.not = 0` taking
`if.then311`, which stores `%idxprom306` into `%err` — is the terminal lane's
refusal (the plan's `zeroStore` shape), not this block's continuing run.  The
empty-container closers (`if.then81`'s `{}` and `if.then334`'s `[]`, `+2` each)
do not come here: they reach the backedge through `close_obj`/`close_arr` and
`after_value`, i.e. the delivered `d = 1` cycle.  So no class takes a `d = 2`
cycle; the plan's `d = 2` container pair is that closer route's own index
delta, and the cycle it composes with is the after-value one.
-/
import LeanLLVM.Refinement.JsonStage2NoEventWalkCycleA

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 1600000

namespace LeanLLVM.Refinement

open LeanLLVM
open LeanLLVM.Refinement.JsonStage2NoEventIR
open LeanLLVM.Refinement.JsonEntryIR (readLanes32)
open LeanLLVM.Refinement.BlockEval
open LeanLLVM.Refinement.JsonEntrySteps (readBytes_one readBytes_length)

/-! ### Arithmetic on the model's words -/

/-- **A sum of two model words is the sum's word.**  `BitVec.ofNat` is the
remainder class, so this holds without a bound on the numbers. -/
theorem stage2NoEventOfNatAdd {x y : Nat} :
    BitVec.ofNat 64 x + BitVec.ofNat 64 y = BitVec.ofNat 64 (x + y) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  exact (Nat.add_mod x y (2 ^ 64)).symm

/-- **The colon's comparison is one.** -/
theorem stage2NoEventICmp_eq_colon :
    evalICmp .eq (BitVec.ofNat 8 58) (BitVec.ofNat 8 58) = 1 := by decide

/-! ### `if.end303` -/

/-- `if.end303`'s nine instructions: the pair's two adds, the index advance, the
colon's entry read and its document byte, and the test on `:`. -/
def ifEnd303Instrs : List Instr :=
  [ Instr.binop "%terms.2" BinOp.add 64 (Operand.reg "%add177.pn")
      (Operand.reg "%terms.1"),
    Instr.binop "%tokens.2" BinOp.add 64 (Operand.reg "%tokens.1")
      (Operand.imm (.int 64 (BitVec.ofNat 64 1))),
    Instr.binop "%inc304" BinOp.add 64 (Operand.reg "%k.1.in")
      (Operand.imm (.int 64 (BitVec.ofNat 64 4))),
    Instr.gep "%arrayidx305" (Ty.int 32) (Operand.reg "%ep") (Operand.reg "%inc137"),
    Instr.load "%43" (Ty.int 32) (Operand.reg "%arrayidx305"),
    Instr.zext "%idxprom306" 32 64 (Operand.reg "%43"),
    Instr.gep "%arrayidx307" (Ty.int 8) (Operand.reg "%b")
      (Operand.reg "%idxprom306"),
    Instr.load "%44" (Ty.int 8) (Operand.reg "%arrayidx307"),
    Instr.icmp "%cmp309.not" IPred.eq 8 (Operand.reg "%44")
      (Operand.imm (.int 8 (BitVec.ofNat 8 58))) ]

/-- `if.end303`, pinned: on the colon's byte the walk takes the backedge. -/
def ifEnd303Block : Block :=
  { name := "if.end303", instrs := ifEnd303Instrs,
    term := Term.condbr (Operand.reg "%cmp309.not") "value.outer.backedge"
      "if.then311" }

theorem ifEnd303Block_find :
    stage2NoEventBody.findBlock "if.end303" = some ifEnd303Block := by
  decide

/-- The block's nine cells, newest first, at the readings it computes and the
colon's entry lane and byte. -/
def ifEnd303Cells (addpn terms tok k ep b inc137 lane : Nat) (x : Nat) :
    List (String × Value) :=
  [("%cmp309.not", .int 1 (evalICmp .eq (BitVec.ofNat 8 x) (BitVec.ofNat 8 58))),
   ("%44", .int 8 (BitVec.ofNat 8 x)),
   ("%arrayidx307", .ptr (b + lane)),
   ("%idxprom306", .int 64 (BitVec.ofNat 64 lane)),
   ("%43", .int 32 (BitVec.ofNat 32 lane)),
   ("%arrayidx305", .ptr (ep + 4 * inc137)),
   ("%inc304", .int 64 (BitVec.ofNat 64 (k + 4))),
   ("%tokens.2", .int 64 (BitVec.ofNat 64 (tok + 1))),
   ("%terms.2", .int 64 (BitVec.ofNat 64 (addpn + terms)))]

/-- **`if.end303`'s run**: the pair's two adds, the index advance, the colon's
entry and document read, and the test against `:`. -/
theorem ifEnd303_denote (calls : Calls) (env : Env) (s : State)
    {addpn terms tok k ep b inc137 lane x : Nat} {bs4 bs1 : List UInt8}
    (haddpn : lookupName env "%add177.pn" = some (.int 64 (BitVec.ofNat 64 addpn)))
    (hterms : lookupName env "%terms.1" = some (.int 64 (BitVec.ofNat 64 terms)))
    (htok : lookupName env "%tokens.1" = some (.int 64 (BitVec.ofNat 64 tok)))
    (hk : lookupName env "%k.1.in" = some (.int 64 (BitVec.ofNat 64 k)))
    (hinc : lookupName env "%inc137" = some (.int 64 (BitVec.ofNat 64 inc137)))
    (hep : lookupName env "%ep" = some (.ptr ep))
    (hb : lookupName env "%b" = some (.ptr b))
    (hincAddr : inc137 < 2 ^ 63)
    (hbs4 : bytesToNat bs4 = lane) (hLaneLt : lane < 2 ^ 32)
    (hlane : readBytes s.mem (ep + 4 * inc137) 4 = some bs4)
    (hbs1 : bytesToNat bs1 = x)
    (hbyte : readBytes s.mem (b + lane) 1 = some bs1) :
    denoteCode calls ifEnd303Instrs (stateAt env s) =
      some (stateAt (cells (ifEnd303Cells addpn terms tok k ep b inc137 lane x) env)
        s) := by
  rw [ifEnd303Instrs]
  rw [denoteCode_add_reg (calls := calls) (env := env) (s := s) (d := "%terms.2")
    (a := "%add177.pn") (b := "%terms.1") (ha := haddpn) (hb := hterms)]
  rw [show BitVec.ofNat 64 addpn + BitVec.ofNat 64 terms =
    BitVec.ofNat 64 (addpn + terms) from stage2NoEventOfNatAdd]
  rw [denoteCode_add_imm (calls := calls)
    (env := ("%terms.2", .int 64 (BitVec.ofNat 64 (addpn + terms))) :: env) (s := s)
    (d := "%tokens.2") (a := "%tokens.1") (ha := by cycle_lk)]
  rw [show BitVec.ofNat 64 tok + BitVec.ofNat 64 1 =
    BitVec.ofNat 64 (tok + 1) from stage2NoEventOfNatAdd]
  rw [denoteCode_add_imm (calls := calls)
    (env := ("%tokens.2", .int 64 (BitVec.ofNat 64 (tok + 1))) ::
      ("%terms.2", .int 64 (BitVec.ofNat 64 (addpn + terms))) :: env) (s := s)
    (d := "%inc304") (a := "%k.1.in") (ha := by cycle_lk)]
  rw [show BitVec.ofNat 64 k + BitVec.ofNat 64 4 =
    BitVec.ofNat 64 (k + 4) from stage2NoEventOfNatAdd]
  rw [stage2NoEventWalk_denote_gep32 (calls := calls)
    (env := ("%inc304", .int 64 (BitVec.ofNat 64 (k + 4))) ::
      ("%tokens.2", .int 64 (BitVec.ofNat 64 (tok + 1))) ::
      ("%terms.2", .int 64 (BitVec.ofNat 64 (addpn + terms))) :: env) (s := s)
    (d := "%arrayidx305") (base := "%ep") (off := "%inc137") (hb := hep) (ho := hinc)
    (hs := by rw [stage2NoEventSignExtend_toNat (by omega)]; exact hincAddr)]
  rw [show ep + ((BitVec.ofNat 64 inc137).signExtend 64).toNat * 4 = ep + 4 * inc137
    from by rw [stage2NoEventSignExtend_toNat (by omega), Nat.mul_comm]]
  rw [stage2NoEventWalk_denote_load_int (calls := calls)
    (env := ("%arrayidx305", .ptr (ep + 4 * inc137)) ::
      ("%inc304", .int 64 (BitVec.ofNat 64 (k + 4))) ::
      ("%tokens.2", .int 64 (BitVec.ofNat 64 (tok + 1))) ::
      ("%terms.2", .int 64 (BitVec.ofNat 64 (addpn + terms))) :: env) (s := s)
    (d := "%43") (p := "%arrayidx305") (w := 32) (hw := by decide)
    (hp := by cycle_lk) (hv := hlane)]
  rw [hbs4]
  rw [denoteCode_zext (calls := calls)
    (env := ("%43", .int 32 (BitVec.ofNat 32 lane)) ::
      ("%arrayidx305", .ptr (ep + 4 * inc137)) ::
      ("%inc304", .int 64 (BitVec.ofNat 64 (k + 4))) ::
      ("%tokens.2", .int 64 (BitVec.ofNat 64 (tok + 1))) ::
      ("%terms.2", .int 64 (BitVec.ofNat 64 (addpn + terms))) :: env) (s := s)
    (d := "%idxprom306") (v := "%43") (wIn := 32) (wOut := 64) (hv := by cycle_lk)]
  rw [stage2NoEventOfNat32_toNat hLaneLt]
  rw [denoteCode_gep8_reg (calls := calls)
    (env := ("%idxprom306", .int 64 (BitVec.ofNat 64 lane)) ::
      ("%43", .int 32 (BitVec.ofNat 32 lane)) ::
      ("%arrayidx305", .ptr (ep + 4 * inc137)) ::
      ("%inc304", .int 64 (BitVec.ofNat 64 (k + 4))) ::
      ("%tokens.2", .int 64 (BitVec.ofNat 64 (tok + 1))) ::
      ("%terms.2", .int 64 (BitVec.ofNat 64 (addpn + terms))) :: env) (s := s)
    (d := "%arrayidx307") (base := "%b") (off := "%idxprom306") (hb := hb)
    (ho := by cycle_lk) (hpos := stage2NoEventLane_signExtend_lt hLaneLt)]
  rw [stage2NoEventSignExtend_toNat (by omega)]
  rw [stage2NoEventWalk_denote_load_int (calls := calls)
    (env := ("%arrayidx307", .ptr (b + lane)) ::
      ("%idxprom306", .int 64 (BitVec.ofNat 64 lane)) ::
      ("%43", .int 32 (BitVec.ofNat 32 lane)) ::
      ("%arrayidx305", .ptr (ep + 4 * inc137)) ::
      ("%inc304", .int 64 (BitVec.ofNat 64 (k + 4))) ::
      ("%tokens.2", .int 64 (BitVec.ofNat 64 (tok + 1))) ::
      ("%terms.2", .int 64 (BitVec.ofNat 64 (addpn + terms))) :: env) (s := s)
    (d := "%44") (p := "%arrayidx307") (w := 8) (hw := by decide)
    (hp := by cycle_lk) (hv := hbyte)]
  rw [hbs1]
  rw [stage2NoEventWalk_denote_icmp_imm (calls := calls)
    (env := ("%44", .int 8 (BitVec.ofNat 8 x)) ::
      ("%arrayidx307", .ptr (b + lane)) ::
      ("%idxprom306", .int 64 (BitVec.ofNat 64 lane)) ::
      ("%43", .int 32 (BitVec.ofNat 32 lane)) ::
      ("%arrayidx305", .ptr (ep + 4 * inc137)) ::
      ("%inc304", .int 64 (BitVec.ofNat 64 (k + 4))) ::
      ("%tokens.2", .int 64 (BitVec.ofNat 64 (tok + 1))) ::
      ("%terms.2", .int 64 (BitVec.ofNat 64 (addpn + terms))) :: env) (s := s)
    (d := "%cmp309.not") (a := "%44") (p := .eq) (w := 8) (ha := by cycle_lk)]
  simp only [ifEnd303Cells, cells, denoteCode_nil]

/-! ### The backedge at the `if.end303` edge

The seven carried readings are the block's own cells: the frame is the immediate
zero, and the index is the advanced one. -/
theorem outerBackedge_ifEnd303_phiSelects {env : Env} {s : State}
    {sp k alen arena terms tok : Nat}
    (hsp : lookupName env "%sp.1" = some (.int 32 (BitVec.ofNat 32 sp)))
    (hk : lookupName env "%inc304" = some (.int 64 (BitVec.ofNat 64 k)))
    (halen : lookupName env "%alen.2" = some (.int 64 (BitVec.ofNat 64 alen)))
    (harena : lookupName env "%arena.3" = some (.int 64 (BitVec.ofNat 64 arena)))
    (hterms : lookupName env "%terms.2" = some (.int 64 (BitVec.ofNat 64 terms)))
    (htok : lookupName env "%tokens.2" = some (.int 64 (BitVec.ofNat 64 tok))) :
    PhiSelects (stateAt env s) "if.end303" outerBackedgePhiSpecs
      [("%frame.0.ph.be", .int 8 (BitVec.ofNat 8 0)),
       ("%sp.0.ph.be", .int 32 (BitVec.ofNat 32 sp)),
       ("%k.0.ph.be", .int 64 (BitVec.ofNat 64 k)),
       ("%alen.0.ph.be", .int 64 (BitVec.ofNat 64 alen)),
       ("%arena.0.ph.be", .int 64 (BitVec.ofNat 64 arena)),
       ("%terms.0.ph.be", .int 64 (BitVec.ofNat 64 terms)),
       ("%tokens.0.ph.be", .int 64 (BitVec.ofNat 64 tok))] := by
  refine PhiSelects.cons (op := .imm (.int 8 (BitVec.ofNat 8 0))) (by decide) ?_
    (PhiSelects.cons (op := .reg "%sp.1") (by decide) ?_
      (PhiSelects.cons (op := .reg "%inc304") (by decide) ?_
        (PhiSelects.cons (op := .reg "%alen.2") (by decide) ?_
          (PhiSelects.cons (op := .reg "%arena.3") (by decide) ?_
            (PhiSelects.cons (op := .reg "%terms.2") (by decide) ?_
              (PhiSelects.cons (op := .reg "%tokens.2") (by decide) ?_
                PhiSelects.nil))))))
  all_goals
    simp only [stateAt, evalOperand, Const.toValue, hsp, hk, halen, harena, hterms,
      htok]

/-- **`value.outer.backedge`'s run at `if.end303`'s edge**: its `phi` run and its
five computed cells. -/
theorem outerBackedge_ifEnd303_denote {calls : Calls} {env : Env} {s : State}
    {sp k alen arena terms tok nep : Nat}
    (hpre : s.pre = some "if.end303")
    (hsp : lookupName env "%sp.1" = some (.int 32 (BitVec.ofNat 32 sp)))
    (hk : lookupName env "%inc304" = some (.int 64 (BitVec.ofNat 64 k)))
    (halen : lookupName env "%alen.2" = some (.int 64 (BitVec.ofNat 64 alen)))
    (harena : lookupName env "%arena.3" = some (.int 64 (BitVec.ofNat 64 arena)))
    (hterms : lookupName env "%terms.2" = some (.int 64 (BitVec.ofNat 64 terms)))
    (htok : lookupName env "%tokens.2" = some (.int 64 (BitVec.ofNat 64 tok)))
    (hnep : lookupName env "%nep" = some (.int 64 (BitVec.ofNat 64 nep)))
    (hspLt : sp < 2 ^ 32) (hk'Lt : k < nep) (hnepLt : nep < 2 ^ 64) :
    denoteCode calls outerBackedgeBlock.instrs (stateAt env s) =
      some (stateAt
        (cells (outerBackedgeTailCells sp k)
          (cells (outerBackedgePhiCells 0 sp k alen arena terms tok) env)) s) := by
  have hsel := outerBackedge_ifEnd303_phiSelects (s := s) (sp := sp) (k := k)
    (alen := alen) (arena := arena) (terms := terms) (tok := tok) hsp hk halen harena
    hterms htok
  have hphi := outerBackedge_phi_denote (calls := calls) (env := env) (s := s)
    (fr := 0) (sp := sp) (k := k) (alen := alen) (arena := arena) (terms := terms)
    (tok := tok) hpre hsel
  rw [outerBackedgeBlock]
  rw [denoteCode_append_apply (a := outerBackedgePhiInstrs)
    (b := outerBackedgeTailInstrs) (s := stateAt env s)
    (s' := stateAt (cells (outerBackedgePhiCells 0 sp k alen arena terms tok) env) s)
    hphi (by decide)]
  rw [outerBackedge_tail_denote (calls := calls)
    (env := cells (outerBackedgePhiCells 0 sp k alen arena terms tok) env) (s := s)
    (sp := sp) (k := k) (nep := nep)
    (by
      exact cells_lookup_of_mem _ _ (by simp [outerBackedgePhiCells]) (by
        rw [show (outerBackedgePhiCells 0 sp k alen arena terms tok).map (·.1) =
          ["%tokens.0.ph.be", "%terms.0.ph.be", "%arena.0.ph.be", "%alen.0.ph.be",
            "%k.0.ph.be", "%sp.0.ph.be", "%frame.0.ph.be"] from rfl]
        decide))
    (by
      exact cells_lookup_of_mem _ _ (by simp [outerBackedgePhiCells]) (by
        rw [show (outerBackedgePhiCells 0 sp k alen arena terms tok).map (·.1) =
          ["%tokens.0.ph.be", "%terms.0.ph.be", "%arena.0.ph.be", "%alen.0.ph.be",
            "%k.0.ph.be", "%sp.0.ph.be", "%frame.0.ph.be"] from rfl]
        decide))
    (by
      rw [cells_lookup_of_notin _ _ (by
        rw [show (outerBackedgePhiCells 0 sp k alen arena terms tok).map (·.1) =
          ["%tokens.0.ph.be", "%terms.0.ph.be", "%arena.0.ph.be", "%alen.0.ph.be",
            "%k.0.ph.be", "%sp.0.ph.be", "%frame.0.ph.be"] from rfl]
        decide)]
      exact hnep)
    hspLt hk'Lt hnepLt]

/-! ### The pair endpoint

The state `if.end303` runs from: the key route's last block (`expect_colon`) has
handed off, and the state carries the key's leftover readings beside the base's
live-ins.  The carry is the target head's, so the two adds are related to it by
`termsEq`/`tokEq`. -/
structure Stage2NoEventWalkPairSrc (calls : Calls) (mem : Mem)
    (K : Stage2NoEventWalkCarry) (k : Nat) (s : State) : Type where
  /-- The invariant at the endpoint. -/
  inv : Stage2NoEventWalkInv K mem s
  /-- `if.end303` is the next block to run. -/
  pc : s.pc = "if.end303"
  /-- The depth word the backedge carries. -/
  sp : Nat
  spLt : sp < 2 ^ 32
  /-- The colon's entry index.  The class lane supplies the route's own
  definition, `%inc137 = add i64 %k.1.in, 3`. -/
  inc137 : Nat
  incEq : inc137 = k + 3
  /-- The key's leftover readings, before the pair's own adds. -/
  terms1 : Nat
  tokens1 : Nat
  addpn : Nat
  /-- The pair's two adds are the delta to the target's carry. -/
  termsEq : K.terms = terms1 + addpn
  tokEq : K.tok = tokens1 + 1
  /-- The next head's index fits the arithmetic and the entry stream. -/
  kAddr : k + 4 < 2 ^ 63
  klt : k + 4 < K.nep
  /-- The consumed-count bound at the endpoint's index.  The pair's `+1` token
  is already inside `K` (`tokEq`) while `%k.1.in` still reads the source head's
  `k`, so the bound is at `k + 1`; the cycle's step then carries it to `k + 4`. -/
  count : Stage2NoEventWalkCount K (k + 1)
  /-- The key route's registers.  The endpoint never runs `after_value`, so no
  `%frame.6` is among them. -/
  kin : lookupName s.env "%k.1.in" = some (.int 64 (BitVec.ofNat 64 k))
  termsv : lookupName s.env "%terms.1" = some (.int 64 (BitVec.ofNat 64 terms1))
  tokensv : lookupName s.env "%tokens.1" = some (.int 64 (BitVec.ofNat 64 tokens1))
  addpnv : lookupName s.env "%add177.pn" = some (.int 64 (BitVec.ofNat 64 addpn))
  incv : lookupName s.env "%inc137" = some (.int 64 (BitVec.ofNat 64 inc137))
  spv : lookupName s.env "%sp.1" = some (.int 32 (BitVec.ofNat 32 sp))
  alenv : lookupName s.env "%alen.2" = some (.int 64 (BitVec.ofNat 64 K.arena.length))
  arenav : lookupName s.env "%arena.3" = some (.int 64 (BitVec.ofNat 64 K.arenaWord))
  /-- The entry chain's live-ins survived the key route. -/
  baseLookups : Stage2NoEventWalkBaseLookups K s
  /-- The report's base is at least one. -/
  bPos : 1 ≤ K.b
  /-- The class route's output evidence. -/
  trace : Stage2NoEventWalkTrace K
  /-- The byte at the colon's entry is the colon. -/
  colon : ∀ lane, K.ent[inc137]? = some lane → K.bs.getD lane 0 = 58

/-- **The pair's cycle at a delta of four**: `if.end303`, the backedge and the
head read, from the pair endpoint to the head at `k + 4`. -/
theorem stage2NoEventWalkCycle_of_pair {calls : Calls} {mem : Mem}
    {K : Stage2NoEventWalkCarry} {k : Nat} {s : State}
    (h : Stage2NoEventWalkPairSrc calls mem K k s) :
    ∃ (s' : State) (p : Nat), Stage2NoEventWalkCycle calls mem K k s 4 s' p := by
  obtain ⟨inv, hpc, sp, hspLt, inc137, hincEq, terms1, tokens1, addpn, htermsEq,
    htokEq, hkAddr, hklt, hcount, hkin, htermsv, htokensv, haddpnv, hincv, hspv, halenv,
    harenav, hbase, hbpos, htrace, hcolon⟩ := h
  have hincLt : inc137 < K.nep := by omega
  have hincAddr : inc137 < 2 ^ 63 := by omega
  have hnepLt : K.nep < 2 ^ 64 := inv.nepLt
  have hk64 : k + 4 < 2 ^ 64 := by omega
  -- the base's own registers
  have hb : lookupName s.env "%b" = some (.ptr K.b) :=
    hbase "%b" _ (by simp [stage2NoEventWalkBaseValues, stage2NoEventWalkParamEntries])
  have hep : lookupName s.env "%ep" = some (.ptr K.ep) :=
    hbase "%ep" _ (by simp [stage2NoEventWalkBaseValues, stage2NoEventWalkParamEntries])
  have hnep : lookupName s.env "%nep" =
      some (.int 64 (BitVec.ofNat 64 K.nep)) :=
    hbase "%nep" _ (by simp [stage2NoEventWalkBaseValues, stage2NoEventWalkParamEntries])
  -- the entry stream and the colon's entry
  have hlanes : readLanes32 s.mem K.ep K.nep = some K.ent :=
    inv.readLanes_off (stage2NoEventCycleOutLane inv) inv.entries
  obtain ⟨hlen, -⟩ := stage2NoEventCycleLanes hlanes
  obtain ⟨colonLane, bsC, hgetC, hreadC, hvalC, hltC⟩ :=
    stage2NoEventCycleEnt_lane hlanes hincLt
  have hinsC : colonLane < K.n := inv.inside colonLane (List.mem_of_getElem? hgetC)
  have hdocC : readBytes s.mem (K.b + colonLane) 1 = some [K.bs.getD colonLane 0] :=
    inv.readBytes_off (K := K) (a := K.b + colonLane) (N := 1)
      (bs := [K.bs.getD colonLane 0]) (stage2NoEventCycleOutDoc inv hinsC) (by
        rw [readBytes_one, readByte_of_readBytes inv.doc hinsC]
        rfl)
  have hcolonC : K.bs.getD colonLane 0 = 58 := hcolon colonLane hgetC
  have hbyteC : readBytes s.mem (K.b + colonLane) 1 = some [58] := by
    rw [hcolonC] at hdocC
    exact hdocC
  -- the next head's entry
  obtain ⟨laneNX, bsNX, hgetNX, hreadNX, hvalNX, hltNX⟩ :=
    stage2NoEventCycleEnt_lane hlanes hklt
  have hinsNX : laneNX < K.n := inv.inside laneNX (List.mem_of_getElem? hgetNX)
  have hdocNX : readBytes s.mem (K.b + laneNX) 1 = some [K.bs.getD laneNX 0] :=
    inv.readBytes_off (K := K) (a := K.b + laneNX) (N := 1)
      (bs := [K.bs.getD laneNX 0]) (stage2NoEventCycleOutDoc inv hinsNX) (by
        rw [readBytes_one, readByte_of_readBytes inv.doc hinsNX]
        rfl)
  have hbsgetNX : K.bs[laneNX]? = some (K.bs.getD laneNX 0) := by
    have hlt : laneNX < K.bs.length := by
      rw [readBytes_length mem K.b K.n (bs := K.bs) inv.doc]
      exact hinsNX
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt]
    simp
  -- the two adds are the target's readings
  have htermsEq' : K.terms = addpn + terms1 := by rw [htermsEq, Nat.add_comm]
  -- the chain's states
  let e1 : Env := cells (ifEnd303Cells addpn terms1 tokens1 k K.ep K.b inc137
    colonLane 58) s.env
  let r1 : State := stage2NoEventWalkNext e1 s "value.outer.backedge"
  let e2 : Env := cells (outerBackedgeTailCells sp (k + 4))
    (cells (outerBackedgePhiCells 0 sp (k + 4) K.arena.length K.arenaWord
      (addpn + terms1) (tokens1 + 1)) e1)
  let r2 : State := stage2NoEventWalkNext e2 r1 "if.end.peel"
  let e3 : Env := cells
    (loopHeadReadCellsAt K (k + 4) sp 0 sp (max sp 520) laneNX
      (K.bs.getD laneNX 0))
    (cells (loopHeadPhiCellsAt K (k + 4) sp 0 sp (max sp 520)) e2)
  let r3 : State := stage2NoEventWalkNext e3 r2 "NodeBlock5"
  -- the first hop: the pair's own block
  have hpre1 : r1.pre = some "if.end303" := by
    rw [show r1.pre = some s.pc from rfl, hpc]
  have l1 : Stage2NoEventWalkLink calls K mem s K r1 :=
    stage2NoEventWalkLink_condbr_true inv
      (by rw [hpc]; exact ifEnd303Block_find)
      (ifEnd303_denote (calls := calls) (env := s.env) (s := s)
        (addpn := addpn) (terms := terms1) (tok := tokens1) (k := k) (ep := K.ep)
        (b := K.b) (inc137 := inc137) (lane := colonLane) (x := 58)
        (bs4 := bsC) (bs1 := [58]) haddpnv htermsv htokensv hkin hincv hep hb
        hincAddr hvalC hltC hreadC (by rw [stage2NoEventBytesToNat_singleton]; decide)
        hbyteC)
      rfl
      (by
        simp only [e1, ifEnd303Cells, cells, lookupName_cons_self,
          stage2NoEventICmp_eq_colon])
  -- the second hop: the backedge at the `if.end303` edge
  have l2 : Stage2NoEventWalkLink calls K mem r1 K r2 :=
    stage2NoEventWalkLink_condbr_true l1.inv'
      (by rw [show r1.pc = "value.outer.backedge" from rfl]
          exact outerBackedgeBlock_find)
      (outerBackedge_ifEnd303_denote (calls := calls) (env := e1) (s := r1)
        (sp := sp) (k := k + 4) (alen := K.arena.length) (arena := K.arenaWord)
        (terms := addpn + terms1) (tok := tokens1 + 1) (nep := K.nep)
        hpre1 (by cycle_lk) (by cycle_lk) (by cycle_lk) (by cycle_lk)
        (by cycle_lk) (by cycle_lk) (by cycle_lk) hspLt hklt hnepLt)
      rfl (by cycle_lk)
  -- the third hop: the head read at the backedge's edge
  have hpre2 : r2.pre = some "value.outer.backedge" := rfl
  have hwide2 : lookupName e2 "%wide.trip.count" =
      some (.int 64 (BitVec.ofNat 64 (max sp 520))) := by cycle_lk
  have h45 : lookupName e2 "%45" = some (.int 64 (BitVec.ofNat 64 sp)) := by cycle_lk
  have htokBE : lookupName e2 "%tokens.0.ph.be" =
      some (.int 64 (BitVec.ofNat 64 K.tok)) := by
    rw [htokEq]
    cycle_lk
  have htermsBE : lookupName e2 "%terms.0.ph.be" =
      some (.int 64 (BitVec.ofNat 64 K.terms)) := by
    rw [htermsEq']
    cycle_lk
  have harenaBE : lookupName e2 "%arena.0.ph.be" =
      some (.int 64 (BitVec.ofNat 64 K.arenaWord)) := by cycle_lk
  have halenBE : lookupName e2 "%alen.0.ph.be" =
      some (.int 64 (BitVec.ofNat 64 K.arena.length)) := by cycle_lk
  have hkBE : lookupName e2 "%k.0.ph.be" =
      some (.int 64 (BitVec.ofNat 64 (k + 4))) := by cycle_lk
  have hspBE : lookupName e2 "%sp.0.ph.be" =
      some (.int 32 (BitVec.ofNat 32 sp)) := by cycle_lk
  have hfrBE : lookupName e2 "%frame.0.ph.be" =
      some (.int 8 (BitVec.ofNat 8 0)) := by cycle_lk
  have l3 : Stage2NoEventWalkLink calls K mem r2 K r3 :=
    stage2NoEventWalkLink_br l2.inv'
      (by rw [show r2.pc = "if.end.peel" from rfl]; exact loopHeadBlock_find)
      (loopHeadBackedge_denote (calls := calls) (env := e2) (s := r2) (K := K)
        (k := k + 4) (sp := sp) (fr := 0) (wide := max sp 520) (lane := laneNX)
        (bs4 := bsNX) (byte := K.bs.getD laneNX 0) hpre2 hwide2 h45 htokBE htermsBE
        harenaBE halenBE hkBE hspBE hfrBE (by cycle_lk) (by cycle_lk) hkAddr
        hvalNX hltNX hreadNX hdocNX)
      rfl
  -- the run, at the three steps' own fuel
  have hrun : ∀ n, runFuel calls (3 + n) stage2NoEventBody s =
      runFuel calls n stage2NoEventBody r3 := by
    intro n
    rw [show 3 + n = 1 + (1 + (1 + n)) from by omega,
      stage2NoEventWalkLink_runFuel l1, stage2NoEventWalkLink_runFuel l2,
      stage2NoEventWalkLink_runFuel l3]
  -- the credit, at four entries' allowance
  have hent : K.ent.getD k 0 ≤ K.ent.getD (k + 4) 0 :=
    stage2NoEventEnt_getD_le (l := K.ent) inv.order (d := 0) (i := k) (j := k + 4)
      (by omega) (by rw [hlen]; omega)
  have hcred : 3 + stage2NoEventWalkPotential K (k + 4) ≤
      stage2NoEventWalkPotential K k := by
    have h32 := stage2NoEventWalkPotential_add (K := K) (k := k) (d := 4)
      (by omega) hent
    omega
  -- the target's head
  have hhead : Stage2NoEventWalkHead K mem (k + 4) r3 :=
    { inv := Stage2NoEventWalkInv.mem_congr inv rfl
      pc := rfl
      klt := hklt
      count := by
        have hc := Stage2NoEventWalkCount.step (a := 0) (b := 3) hcount rfl rfl
          (by omega : (0 : Nat) ≤ 3)
        unfold Stage2NoEventWalkCount at hc ⊢
        omega
      bPos := hbpos
      layers := ⟨e2, sp, 0, sp, max sp 520, laneNX, K.bs.getD laneNX 0, rfl, hgetNX,
        hltNX, hbsgetNX, hdocNX, hspLt, by decide, rfl, rfl⟩
      baseLookups := by
        have h1 := stage2NoEventCycleBase (K := K) (env := s.env) hbase
          (cs := ifEnd303Cells addpn terms1 tokens1 k K.ep K.b inc137 colonLane 58)
          (names := ["%cmp309.not", "%44", "%arrayidx307", "%idxprom306", "%43",
            "%arrayidx305", "%inc304", "%tokens.2", "%terms.2"]) rfl (by decide)
        have h2 := stage2NoEventCycleBase (K := K) h1
          (cs := outerBackedgePhiCells 0 sp (k + 4) K.arena.length K.arenaWord
            (addpn + terms1) (tokens1 + 1))
          (names := ["%tokens.0.ph.be", "%terms.0.ph.be", "%arena.0.ph.be",
            "%alen.0.ph.be", "%k.0.ph.be", "%sp.0.ph.be", "%frame.0.ph.be"])
          rfl (by decide)
        have h3 := stage2NoEventCycleBase (K := K) h2
          (cs := outerBackedgeTailCells sp (k + 4))
          (names := ["%cmp.not.peel", "%wide.trip.count", "%umax", "%umax.max",
            "%45"]) rfl (by decide)
        have h4 := stage2NoEventCycleBase (K := K) h3
          (cs := loopHeadPhiCellsAt K (k + 4) sp 0 sp (max sp 520))
          (names := loopHeadPhiCellNames) rfl (by decide)
        have h5 := stage2NoEventCycleBase (K := K) h4
          (cs := loopHeadReadCellsAt K (k + 4) sp 0 sp (max sp 520) laneNX
            (K.bs.getD laneNX 0))
          (names := loopHeadReadCellNames) rfl (by decide)
        exact h5 }
  exact ⟨r3, 3, ⟨⟨⟨hrun, l3.inv'⟩, hhead, htrace⟩, hcred⟩⟩

/-- **The pair's cycle, with the head named**: the same theorem, its target head
projected. -/
theorem stage2NoEventWalkCycle_pair_head {calls : Calls} {mem : Mem}
    {K : Stage2NoEventWalkCarry} {k : Nat} {s : State}
    (h : Stage2NoEventWalkPairSrc calls mem K k s) :
    ∃ (s' : State) (p : Nat), Stage2NoEventWalkCycle calls mem K k s 4 s' p ∧
      Stage2NoEventWalkHead K mem (k + 4) s' := by
  obtain ⟨s', p, hc⟩ := stage2NoEventWalkCycle_of_pair h
  exact ⟨s', p, hc, hc.headPriced.seg.head'⟩

/-! ### Axiom footprints -/

#print axioms stage2NoEventOfNatAdd
#print axioms ifEnd303Block_find
#print axioms ifEnd303_denote
#print axioms outerBackedge_ifEnd303_phiSelects
#print axioms outerBackedge_ifEnd303_denote
#print axioms stage2NoEventWalkCycle_of_pair
#print axioms stage2NoEventWalkCycle_pair_head

end LeanLLVM.Refinement
