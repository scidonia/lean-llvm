/-
The stage-2 walk's `phi`-headed merges: class E's remaining twelve blocks.

`JsonStage2WalkRest` and `JsonStage2WalkEntry` give the pure transfers and the
scan entries.  What is left of class E is the instance work: each merge's leading
`phi` run written into its outgoing environment, the straight-line instructions
that follow the run, and the edge's transfer.  Nine of the twelve are pure — four
scan landing blocks (`land.rhs.i`, `land.rhs.i103`, `land.rhs71.i`,
`land.rhs457.i`), the three remaining merges (`if.end245.i`, `if.end290.i`,
`while.end.i`), the literal latch's entry (`for.body.i.i`) and the dispatch's
close (`cleanup478.i`); three write memory (`if.end372.i` at the token's end
slot, and the two refusal exits `if.then57.i` and `while.end78.i` at `%e + 8`).

The four landing blocks are one lemma's instances: a counter `phi`, the document
byte at it, and a `br` to the dispatch node that compares the byte.  The three
pure merges whose targets are leaves of the measure take both `WalkLocal` facts as
`simp [WalkLocal]`; `for.body.i.i` is the exception, since its `for.inc.i.i` edge
is the measure's own guard and is built from the invariant's disjunctive landing
fact.

Of the three store blocks, the two refusal exits have class C's shape with a
`phi` (and, at `if.then57.i`, an `add`) in front, so their carry advances
`eoff`/`refusal` exactly as `WalkLink.refusalStore`'s does, and `if.end372.i`
writes the scan's end position at the token's slot `%t352.i + 8`, which no clause
of `WalkInv` names: its write is carried by `frame` alone.

**What waits on F.**  `if.end290.i`'s first `phi` takes `%32` — the arena
reserve's decoded length, loaded from `%outn.i` — as an incoming operand, so its
link takes that register's binding as the caller's fact, exactly as class A takes
`%8`'s.  The binding's *production* is `s2_string_body`'s write and the walk's
`%len`/`%cap` reads are the log's two staged words; `JsonStage2Helpers`'s
`s2StringBody_outn_le` is the datum that produces it.  No other E block reads a
callee's write.
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

/-! ### Two steps the merges need

`JsonStage2WalkScope`'s `denoteCode_icmp_eq_imm_w` is the `eq`-with-literal case;
the merges test `ne` and `ult` against one.  The `getelementptr` at a literal
offset is stated at a state (its cell list is a `State.bind`); the merges reach it
after a `phi` run, at a built environment, so the same step is written at
`stateAt`. -/

/-- A literal's value is the constructor it names. -/
@[simp] theorem walkConst_toValue_int (w : Nat) (v : BitVec w) :
    (Const.int w v).toValue = Value.int w v := rfl

/-- `%d = icmp <p> <w> %a, <c>` for any predicate and width. -/
theorem walkDenoteCode_icmp_imm (calls : Calls) (env : Env) (s : State) (d a : String)
    (p : IPred) (w : Nat) {x c : BitVec w}
    (ha : lookupName env a = some (.int w x)) (is : List Instr) :
    denoteCode calls (.icmp d p w (.reg a) (.imm (.int w c)) :: is) (stateAt env s) =
      denoteCode calls is (stateAt ((d, .int 1 (evalICmp p x c)) :: env) s) := by
  rw [denoteCode_cons_of _ _ _ _ _ (by
    rw [LeanLLVM.Refinement.JsonS1MasksIR.evalInstr_icmp (s := stateAt env s)
      (ha := evalOperand_reg_of env s a (.int w x) ha)
      (hb := evalOperand_lit_of (stateAt env s) w c)])]
  simp only [stateAt, State.bind]

/-- `%d = getelementptr i8, ptr %base, i64 <c>` at a built environment. -/
theorem walkDenoteCode_gep8_imm_at (calls : Calls) (env : Env) (s : State) (d base : String)
    {a c : Nat} (hb : lookupName env base = some (.ptr a)) (hc : c < 2 ^ 63)
    (is : List Instr) :
    denoteCode calls
        (.gep d (.int 8) (.reg base) (.imm (.int 64 (BitVec.ofNat 64 c))) :: is)
        (stateAt env s) =
      denoteCode calls is (stateAt ((d, .ptr (a + c)) :: env) s) := by
  have h := walkDenoteCode_gep8_imm (calls := calls) (s := stateAt env s) (d := d)
    (base := base) (a := a) (c := c) hb hc is
  rw [h]
  rfl

/-- The head of an environment, at `Value` rather than a schematic `α`, so a
dotted constructor (`.ptr`, `.int`) resolves without an expected type. -/
theorem walkLookup_cons_self (k : String) (v : Value) (rest : Env) :
    lookupName ((k, v) :: rest) k = some v :=
  lookupName_cons_self k v rest

/-! ### An `add` of two registers

`if.then57.i` sums its `phi`'s counter with `%idxprom.i`; the tree's `add` steps are
the immediate and one-operand ones, so the register pair is written here. -/

/-- `%d = add <w> %a, %b`. -/
theorem walkStep_add_reg_w (calls : Calls) (env : Env) (s : State) (d a b : String)
    (w : Nat) {x y : BitVec w}
    (ha : lookupName env a = some (.int w x)) (hb : lookupName env b = some (.int w y)) :
    evalInstr calls (stateAt env s) (.binop d .add w (.reg a) (.reg b)) =
      some (stateAt ((d, .int w (x + y)) :: env) s) := by
  simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq, stateAt, State.bind]
    using LeanLLVM.Refinement.JsonS1MasksIR.evalInstr_binop (r := (x + y).toNat)
      (ha := LeanLLVM.Refinement.BlockEval.evalOperand_reg_of env s a (.int w x) ha)
      (hb := LeanLLVM.Refinement.BlockEval.evalOperand_reg_of env s b (.int w y) hb)
      (hr := by simp [evalBinopNat, evalBinop, BitVec.ofNat_toNat])

theorem walkDenoteCode_add_reg_w (calls : Calls) (env : Env) (s : State) (d a b : String)
    (w : Nat) {x y : BitVec w}
    (ha : lookupName env a = some (.int w x)) (hb : lookupName env b = some (.int w y))
    (is : List Instr) :
    denoteCode calls (.binop d .add w (.reg a) (.reg b) :: is) (stateAt env s) =
      denoteCode calls is (stateAt ((d, .int w (x + y)) :: env) s) := by
  rw [denoteCode_cons_of _ _ _ _ _ (walkStep_add_reg_w calls env s d a b w ha hb)]

/-! ### The token's extent, for the scan's end store

`if.end372.i` writes eight bytes at `%t352.i + 8` (`%end.i`).  No clause of
`WalkInv` reads the token, so the write owes only `frame`: the pair
`(tok, stage2TokenExtent)` is one of the staged regions, and the log, the event
stream and the arena's cursor are separate from it. -/

/-- The token and the log are separate regions of the staging. -/
theorem walkTok_z_sep {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {s : State}
    (_h : WalkInv G C s) :
    C.stage.tok + stage2TokenExtent ≤ C.stage.z ∨
      C.stage.z + stage2LogExtent ≤ C.stage.tok := by
  have hpair : (stage2WalkRegions G.b G.n G.ep G.nep G.xp G.nxp G.dst G.ndst0 G.ev
      G.evcap G.ndst G.nev G.err C.stage.c C.stage.ctype C.stage.cst C.stage.tok
      C.stage.s C.stage.z C.stage.e).Pairwise
      (fun r q => r.1 + r.2 ≤ q.1 ∨ q.1 + q.2 ≤ r.1) := by
    have hsep := C.stage.separate
    unfold DisjointRegions at hsep
    rw [stage2StagedRegions] at hsep
    exact (List.pairwise_append.mp hsep).1
  have hlen : (stage2WalkRegions G.b G.n G.ep G.nep G.xp G.nxp G.dst G.ndst0 G.ev
      G.evcap G.ndst G.nev G.err C.stage.c C.stage.ctype C.stage.cst C.stage.tok
      C.stage.s C.stage.z C.stage.e).length = 15 := by
    simp [stage2WalkRegions, stage2Regions, stage2StagedWrites]
  have h' := List.pairwise_iff_getElem.mp hpair 11 13 (by omega) (by omega) (by omega)
  simpa [stage2WalkRegions, stage2Regions, stage2StagedWrites] using h'

/-- The token and the event stream are separate regions of the staging. -/
theorem walkTok_ev_sep {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {s : State}
    (_h : WalkInv G C s) :
    C.stage.tok + stage2TokenExtent ≤ G.ev ∨ G.ev + G.evcap ≤ C.stage.tok := by
  have hpair : (stage2WalkRegions G.b G.n G.ep G.nep G.xp G.nxp G.dst G.ndst0 G.ev
      G.evcap G.ndst G.nev G.err C.stage.c C.stage.ctype C.stage.cst C.stage.tok
      C.stage.s C.stage.z C.stage.e).Pairwise
      (fun r q => r.1 + r.2 ≤ q.1 ∨ q.1 + q.2 ≤ r.1) := by
    have hsep := C.stage.separate
    unfold DisjointRegions at hsep
    rw [stage2StagedRegions] at hsep
    exact (List.pairwise_append.mp hsep).1
  have hlen : (stage2WalkRegions G.b G.n G.ep G.nep G.xp G.nxp G.dst G.ndst0 G.ev
      G.evcap G.ndst G.nev G.err C.stage.c C.stage.ctype C.stage.cst C.stage.tok
      C.stage.s C.stage.z C.stage.e).length = 15 := by
    simp [stage2WalkRegions, stage2Regions, stage2StagedWrites]
  have h' := List.pairwise_iff_getElem.mp hpair 4 11 (by omega) (by omega) (by omega)
  simpa [stage2WalkRegions, stage2Regions, stage2StagedWrites] using h'.symm

/-- Byte `j` of the token's end-slot store is inside the token's extent. -/
theorem walkTok_inside {c ctype cst tok s z e j : Nat} (hj : j < 8) :
    inRegions (stage2StagedWrites c ctype cst tok s z e) (tok + 8 + j) :=
  ⟨(tok, stage2TokenExtent), by simp [stage2StagedWrites], by omega,
    by simp [stage2TokenExtent]; omega⟩

/-- A write at the token's end slot leaves the log alone. -/
theorem walkReadBytes_log_of_tok_write {m : Mem} {tok z off N : Nat} {x : BitVec 64}
    (htz : tok + stage2TokenExtent ≤ z ∨ z + stage2LogExtent ≤ tok)
    (hoff : off + N ≤ stage2LogExtent) :
    readBytes (writeBytes m (tok + 8) (natToBytes x.toNat 8)) (z + off) N =
      readBytes m (z + off) N := by
  refine walkReadBytes_writeBytes_outside (start := tok + 8) ?_
  have hw : (natToBytes x.toNat 8).length = 8 := by simp [natToBytes_length]
  rcases htz with h | h
  · refine Or.inr ?_
    simp only [stage2TokenExtent, stage2LogExtent] at *
    omega
  · refine Or.inl ?_
    omega

/-- A refusal store of a computed word leaves the log alone. -/
theorem walkReadBytes_log_of_refusal_write {m : Mem} {e z off N : Nat} {x : BitVec 64}
    (hez : e + stage2ErrorExtent ≤ z ∨ z + stage2LogExtent ≤ e)
    (hoff : off + N ≤ stage2LogExtent) :
    readBytes (writeBytes m (e + 8) (natToBytes x.toNat 8)) (z + off) N =
      readBytes m (z + off) N := by
  simpa [wordBytes] using
    walkReadBytes_log_of_eoff_write (m := m) (e := e) (z := z) (off := off)
      (j := x.toNat) (N := N) hez hoff

/-- A refusal store of a computed word leaves the event stream's prefix alone. -/
theorem walkReadBytes_ev_of_refusal_write {m : Mem} {e ev evcap nev0 N : Nat}
    {x : BitVec 64}
    (hev : e + stage2ErrorExtent ≤ ev ∨ ev + evcap ≤ e) (hN : nev0 + N ≤ evcap) :
    readBytes (writeBytes m (e + 8) (natToBytes x.toNat 8)) (ev + nev0) N =
      readBytes m (ev + nev0) N := by
  simpa [wordBytes] using
    walkReadBytes_ev_of_eoff_write (m := m) (e := e) (ev := ev) (evcap := evcap)
      (nev0 := nev0) (j := x.toNat) (N := N) hev hN

/-- A write at the token's end slot leaves the event stream's prefix alone. -/
theorem walkReadBytes_ev_of_tok_write {m : Mem} {tok ev evcap nev0 N : Nat} {x : BitVec 64}
    (htev : tok + stage2TokenExtent ≤ ev ∨ ev + evcap ≤ tok)
    (hN : nev0 + N ≤ evcap) :
    readBytes (writeBytes m (tok + 8) (natToBytes x.toNat 8)) (ev + nev0) N =
      readBytes m (ev + nev0) N := by
  refine walkReadBytes_writeBytes_outside (start := tok + 8) ?_
  have hw : (natToBytes x.toNat 8).length = 8 := by simp [natToBytes_length]
  rcases htev with h | h
  · refine Or.inr ?_
    simp only [stage2TokenExtent] at *
    omega
  · refine Or.inl ?_
    omega

/-! ### The four scan landing blocks

One lemma: a counter `phi`, the document byte at the counter, and the `br` into the
dispatch node that compares it.  The byte is the caller's: `land.rhs*` reads the
document through `%3` at an index the invariant does not bind, exactly as class G's
document read takes its byte. -/

/-- **A scan's landing block**: the counter `phi` from the scan's latch or entry,
the document byte at it, and the jump into the dispatch node. -/
theorem WalkLink.scanLanding {calls : Calls} {m0 : Mem} (G : WalkGeom m0)
    (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    {B : Block} (hfind : stage2Body.findBlock C.block = some B)
    {d g ld t : String} {ty : Ty} {inc : List (String × Operand)}
    (hinstrs : B.instrs =
      [Instr.phi d ty inc,
       Instr.gep g (.int 8) (.reg "%3") (.reg d),
       Instr.load ld (.int 8) (.reg g)])
    (hterm : B.term = Term.br t)
    (hfree : walkCarried B.instrs)
    (hd3 : d ≠ "%3")
    {p : String} {op : Operand} {e : BitVec 64} {b : UInt8}
    (hpre : s.pre = some p) (hin : phiIncoming p inc = some op)
    (hv : evalOperand s op = some (.int 64 e))
    (hpos : (e.signExtend 64).toNat < 2 ^ 63)
    (hread : readBytes s.mem (G.b + (e.signExtend 64).toNat) 1 = some [b])
    (hloc : WalkLocal { C with block := t }
      { stateAt ((ld, .int 8 (BitVec.ofNat 8 b.toNat)) ::
          (g, .ptr (G.b + (e.signExtend 64).toNat)) ::
          (d, .int 64 e) :: s.env) s with pc := t, pre := some s.pc }) :
    ∃ s', WalkLink calls G C s { C with block := t } s' := by
  have hspecs : B.instrs =
      ([{ dst := d, ty := ty, incoming := inc }].map PhiSpec.instr) ++
        [Instr.gep g (.int 8) (.reg "%3") (.reg d),
         Instr.load ld (.int 8) (.reg g)] := by
    rw [hinstrs]; simp [PhiSpec.instr]
  have hden : denoteCode calls B.instrs s =
      some (stateAt ((ld, .int 8 (BitVec.ofNat 8 b.toNat)) ::
          (g, .ptr (G.b + (e.signExtend 64).toNat)) ::
          (d, .int 64 e) :: s.env) s) := by
    rw [hspecs, denoteCode_phiRun
      (specs :=
        [{ dst := d, ty := ty, incoming := inc }])
      (vs := [(d, .int 64 e)])
      (rest := [Instr.gep g (.int 8) (.reg "%3") (.reg d),
        Instr.load ld (.int 8) (.reg g)])
      hpre (PhiSelects.cons hin hv PhiSelects.nil) (by rfl)]
    rw [show s.bindAll [(d, .int 64 e)] = stateAt ((d, .int 64 e) :: s.env) s from rfl]
    rw [denoteCode_gep8_reg (calls := calls) (env := (d, .int 64 e) :: s.env) (s := s)
      (d := g) (base := "%3") (off := d) (a := G.b) (idx := e)
      (by rw [lookupName_cons_ne _ _ hd3]; exact hInv.ptrs.1)
      (by exact walkLookup_cons_self d (.int 64 e) s.env) hpos]
    rw [denoteCode_load8_single (calls := calls)
      (env := (g, .ptr (G.b + (e.signExtend 64).toNat)) :: (d, .int 64 e) :: s.env)
      (s := s) (d := ld) (p := g) (a := G.b + (e.signExtend 64).toNat)
      (by exact walkLookup_cons_self g (.ptr (G.b + (e.signExtend 64).toNat)) ((d, .int 64 e) :: s.env)) hread]
    rfl
  exact WalkLink.pureJumpCore (G := G) (C := C) (s := s) hInv
    (B := B) hfind hden hfree rfl rfl hterm hloc

/-- `land.rhs.i`: the whitespace skip's counter and the byte at it. -/
def walkLand_rhs_i : Block :=
  { name := "land.rhs.i",
    instrs := [
      Instr.phi "%ee.0.i238" (Ty.int 64)
        [("while.body370.i", (Operand.reg "%inc371.i")),
         ("land.rhs.i.preheader", (Operand.reg "%idxprom.i"))],
      Instr.gep "%arrayidx367.i" (Ty.int 8) (Operand.reg "%3") (Operand.reg "%ee.0.i238"),
      Instr.load "%36" (Ty.int 8) (Operand.reg "%arrayidx367.i")
    ],
    term := Term.br "NodeBlock52" }

theorem walkLand_rhs_i_find : stage2Body.findBlock "land.rhs.i" = some walkLand_rhs_i := by
  simp [stage2Body, Function.findBlock, findBlockList, walkLand_rhs_i]

/-- **`land.rhs.i` as a link.** -/
theorem WalkLink.land_rhs_i {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "land.rhs.i")
    {p : String} {op : Operand} {e : BitVec 64} {b : UInt8}
    (hpre : s.pre = some p)
    (hin : phiIncoming p [("while.body370.i", (Operand.reg "%inc371.i")),
      ("land.rhs.i.preheader", (Operand.reg "%idxprom.i"))] = some op)
    (hv : evalOperand s op = some (.int 64 e))
    (hpos : (e.signExtend 64).toNat < 2 ^ 63)
    (hread : readBytes s.mem (G.b + (e.signExtend 64).toNat) 1 = some [b]) :
    ∃ s', WalkLink calls G C s { C with block := "NodeBlock52" } s' := by
  refine WalkLink.scanLanding (G := G) (C := C) (s := s) hInv
    (B := walkLand_rhs_i) (by rw [hblock]; exact walkLand_rhs_i_find)
    (d := "%ee.0.i238") (g := "%arrayidx367.i") (ld := "%36") (ty := Ty.int 64)
    (inc := [("while.body370.i", (Operand.reg "%inc371.i")),
      ("land.rhs.i.preheader", (Operand.reg "%idxprom.i"))])
    ?_ rfl ?_ (by decide) hpre hin hv hpos hread ?_
  · simp [walkLand_rhs_i]
  · unfold walkCarried; decide
  · simp [WalkLocal]

/-- `land.rhs.i103`: the string scan's counter and the byte at it. -/
def walkLand_rhs_i103 : Block :=
  { name := "land.rhs.i103",
    instrs := [
      Instr.phi "%ee.011.i" (Ty.int 64)
        [("while.body.i104", (Operand.reg "%inc.i105")),
         ("cond.end.i96", (Operand.reg "%idxprom.i"))],
      Instr.gep "%arrayidx5.i" (Ty.int 8) (Operand.reg "%3") (Operand.reg "%ee.011.i"),
      Instr.load "%40" (Ty.int 8) (Operand.reg "%arrayidx5.i")
    ],
    term := Term.br "NodeBlock73" }

theorem walkLand_rhs_i103_find :
    stage2Body.findBlock "land.rhs.i103" = some walkLand_rhs_i103 := by
  simp [stage2Body, Function.findBlock, findBlockList, walkLand_rhs_i103]

/-- **`land.rhs.i103` as a link.** -/
theorem WalkLink.land_rhs_i103 {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "land.rhs.i103")
    {p : String} {op : Operand} {e : BitVec 64} {b : UInt8}
    (hpre : s.pre = some p)
    (hin : phiIncoming p [("while.body.i104", (Operand.reg "%inc.i105")),
      ("cond.end.i96", (Operand.reg "%idxprom.i"))] = some op)
    (hv : evalOperand s op = some (.int 64 e))
    (hpos : (e.signExtend 64).toNat < 2 ^ 63)
    (hread : readBytes s.mem (G.b + (e.signExtend 64).toNat) 1 = some [b]) :
    ∃ s', WalkLink calls G C s { C with block := "NodeBlock73" } s' := by
  refine WalkLink.scanLanding (G := G) (C := C) (s := s) hInv
    (B := walkLand_rhs_i103) (by rw [hblock]; exact walkLand_rhs_i103_find)
    (d := "%ee.011.i") (g := "%arrayidx5.i") (ld := "%40") (ty := Ty.int 64)
    (inc := [("while.body.i104", (Operand.reg "%inc.i105")),
      ("cond.end.i96", (Operand.reg "%idxprom.i"))])
    ?_ rfl ?_ (by decide) hpre hin hv hpos hread ?_
  · simp [walkLand_rhs_i103]
  · unfold walkCarried; decide
  · simp [WalkLocal]

/-- `land.rhs71.i`: the escape scan's counter and the byte at it. -/
def walkLand_rhs71_i : Block :=
  { name := "land.rhs71.i",
    instrs := [
      Instr.phi "%s2.020.i" (Ty.int 64)
        [("while.body76.i", (Operand.reg "%inc77.i")),
         ("if.end67.i", (Operand.reg "%ee.0.lcssa.i"))],
      Instr.gep "%arrayidx72.i" (Ty.int 8) (Operand.reg "%3") (Operand.reg "%s2.020.i"),
      Instr.load "%46" (Ty.int 8) (Operand.reg "%arrayidx72.i")
    ],
    term := Term.br "NodeBlock94" }

theorem walkLand_rhs71_i_find :
    stage2Body.findBlock "land.rhs71.i" = some walkLand_rhs71_i := by
  simp [stage2Body, Function.findBlock, findBlockList, walkLand_rhs71_i]

/-- **`land.rhs71.i` as a link.** -/
theorem WalkLink.land_rhs71_i {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "land.rhs71.i")
    {p : String} {op : Operand} {e : BitVec 64} {b : UInt8}
    (hpre : s.pre = some p)
    (hin : phiIncoming p [("while.body76.i", (Operand.reg "%inc77.i")),
      ("if.end67.i", (Operand.reg "%ee.0.lcssa.i"))] = some op)
    (hv : evalOperand s op = some (.int 64 e))
    (hpos : (e.signExtend 64).toNat < 2 ^ 63)
    (hread : readBytes s.mem (G.b + (e.signExtend 64).toNat) 1 = some [b]) :
    ∃ s', WalkLink calls G C s { C with block := "NodeBlock94" } s' := by
  refine WalkLink.scanLanding (G := G) (C := C) (s := s) hInv
    (B := walkLand_rhs71_i) (by rw [hblock]; exact walkLand_rhs71_i_find)
    (d := "%s2.020.i") (g := "%arrayidx72.i") (ld := "%46") (ty := Ty.int 64)
    (inc := [("while.body76.i", (Operand.reg "%inc77.i")),
      ("if.end67.i", (Operand.reg "%ee.0.lcssa.i"))])
    ?_ rfl ?_ (by decide) hpre hin hv hpos hread ?_
  · simp [walkLand_rhs71_i]
  · unfold walkCarried; decide
  · simp [WalkLocal]

/-- `land.rhs457.i`: the extra-token scan's counter and the byte at it. -/
def walkLand_rhs457_i : Block :=
  { name := "land.rhs457.i",
    instrs := [
      Instr.phi "%q.0.i246" (Ty.int 64)
        [("while.body462.i", (Operand.reg "%inc463.i")),
         ("if.then447.i", (Operand.reg "%ee.1.i"))],
      Instr.gep "%arrayidx458.i" (Ty.int 8) (Operand.reg "%3") (Operand.reg "%q.0.i246"),
      Instr.load "%47" (Ty.int 8) (Operand.reg "%arrayidx458.i")
    ],
    term := Term.br "NodeBlock105" }

theorem walkLand_rhs457_i_find :
    stage2Body.findBlock "land.rhs457.i" = some walkLand_rhs457_i := by
  simp [stage2Body, Function.findBlock, findBlockList, walkLand_rhs457_i]

/-- **`land.rhs457.i` as a link.** -/
theorem WalkLink.land_rhs457_i {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "land.rhs457.i")
    {p : String} {op : Operand} {e : BitVec 64} {b : UInt8}
    (hpre : s.pre = some p)
    (hin : phiIncoming p [("while.body462.i", (Operand.reg "%inc463.i")),
      ("if.then447.i", (Operand.reg "%ee.1.i"))] = some op)
    (hv : evalOperand s op = some (.int 64 e))
    (hpos : (e.signExtend 64).toNat < 2 ^ 63)
    (hread : readBytes s.mem (G.b + (e.signExtend 64).toNat) 1 = some [b]) :
    ∃ s', WalkLink calls G C s { C with block := "NodeBlock105" } s' := by
  refine WalkLink.scanLanding (G := G) (C := C) (s := s) hInv
    (B := walkLand_rhs457_i) (by rw [hblock]; exact walkLand_rhs457_i_find)
    (d := "%q.0.i246") (g := "%arrayidx458.i") (ld := "%47") (ty := Ty.int 64)
    (inc := [("while.body462.i", (Operand.reg "%inc463.i")),
      ("if.then447.i", (Operand.reg "%ee.1.i"))])
    ?_ rfl ?_ (by decide) hpre hin hv hpos hread ?_
  · simp [walkLand_rhs457_i]
  · unfold walkCarried; decide
  · simp [WalkLocal]

/-! ### The three pure merges -/

/-- `if.end245.i`: the nest's `phi`, the callee's return word, and the select of
`%or.cond523.i`. -/
def walkIf_end245_i : Block :=
  { name := "if.end245.i",
    instrs := [
      Instr.phi "%key.1.i" (Ty.int 1)
        [("if.then231.i", (Operand.reg "%or.cond.i")),
         ("land.lhs.true.i", (Operand.imm (.int 1 (BitVec.ofNat 1 0)))),
         ("if.then219.i", (Operand.imm (.int 1 (BitVec.ofNat 1 0))))],
      Instr.icmp "%tobool248.i" IPred.ne 32 (Operand.reg "%call222.i")
        (Operand.imm (.int 32 (BitVec.ofNat 32 0))),
      Instr.select "%or.cond523.i" (Ty.int 1) (Operand.reg "%key.1.i")
        (Operand.imm (.int 1 (BitVec.ofNat 1 1))) (Operand.reg "%tobool248.i")
    ],
    term := Term.condbr (Operand.reg "%or.cond523.i") "if.end256.i" "if.then249.i" }

theorem walkIf_end245_i_find : stage2Body.findBlock "if.end245.i" = some walkIf_end245_i := by
  simp [stage2Body, Function.findBlock, findBlockList, walkIf_end245_i]

/-- **`if.end245.i` as a link.**  `%call222.i` is `s2_value_pos`'s return word, so
the link takes its binding as the caller's fact, as class A takes `%8`'s. -/
theorem WalkLink.if_end245_i {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "if.end245.i")
    {p : String} {op : Operand} {k : BitVec 1} {x : BitVec 32}
    (hpre : s.pre = some p)
    (hin : phiIncoming p [("if.then231.i", (Operand.reg "%or.cond.i")),
      ("land.lhs.true.i", (Operand.imm (.int 1 (BitVec.ofNat 1 0)))),
      ("if.then219.i", (Operand.imm (.int 1 (BitVec.ofNat 1 0))))] = some op)
    (hv : evalOperand s op = some (.int 1 k))
    (hcall : lookupName s.env "%call222.i" = some (.int 32 x)) :
    ∃ s', WalkLink calls G C s
      { C with block := (if (if k = 1 then (1 : BitVec 1)
          else evalICmp .ne x (BitVec.ofNat 32 0)) = 1 then "if.end256.i" else "if.then249.i") } s' := by
  have hspecs : walkIf_end245_i.instrs =
      ([{ dst := "%key.1.i", ty := Ty.int 1,
          incoming := [("if.then231.i", (Operand.reg "%or.cond.i")),
            ("land.lhs.true.i", (Operand.imm (.int 1 (BitVec.ofNat 1 0)))),
            ("if.then219.i", (Operand.imm (.int 1 (BitVec.ofNat 1 0))))] }].map PhiSpec.instr) ++
        [Instr.icmp "%tobool248.i" IPred.ne 32 (Operand.reg "%call222.i")
           (Operand.imm (.int 32 (BitVec.ofNat 32 0))),
         Instr.select "%or.cond523.i" (Ty.int 1) (Operand.reg "%key.1.i")
           (Operand.imm (.int 1 (BitVec.ofNat 1 1))) (Operand.reg "%tobool248.i")] := by
    simp [walkIf_end245_i, PhiSpec.instr]
  have hden : denoteCode calls walkIf_end245_i.instrs s =
      some (stateAt (("%or.cond523.i", .int 1 (if k = 1 then BitVec.ofNat 1 1
            else evalICmp .ne x (BitVec.ofNat 32 0))) ::
        ("%tobool248.i", .int 1 (evalICmp .ne x (BitVec.ofNat 32 0))) ::
        ("%key.1.i", .int 1 k) :: s.env) s) := by
    rw [hspecs, denoteCode_phiRun
      (specs :=
        [{ dst := "%key.1.i", ty := Ty.int 1,
            incoming := [("if.then231.i", (Operand.reg "%or.cond.i")),
          ("land.lhs.true.i", (Operand.imm (.int 1 (BitVec.ofNat 1 0)))),
          ("if.then219.i", (Operand.imm (.int 1 (BitVec.ofNat 1 0))))] }])
      (vs := [("%key.1.i", .int 1 k)])
      (rest := [Instr.icmp "%tobool248.i" IPred.ne 32 (Operand.reg "%call222.i")
          (Operand.imm (.int 32 (BitVec.ofNat 32 0))),
        Instr.select "%or.cond523.i" (Ty.int 1) (Operand.reg "%key.1.i")
          (Operand.imm (.int 1 (BitVec.ofNat 1 1))) (Operand.reg "%tobool248.i")])
      hpre (PhiSelects.cons hin hv PhiSelects.nil) (by rfl)]
    rw [show s.bindAll [("%key.1.i", .int 1 k)] = stateAt (("%key.1.i", .int 1 k) :: s.env) s from rfl]
    rw [walkDenoteCode_icmp_imm (calls := calls) (env := ("%key.1.i", .int 1 k) :: s.env)
      (s := s) (d := "%tobool248.i") (a := "%call222.i") IPred.ne 32
      (x := x) (c := BitVec.ofNat 32 0)
      (by rw [lookupName_cons_ne _ _ (by decide)]; exact hcall)]
    rw [denoteCode_select_bit_imm_reg_w (calls := calls)
      (env := ("%tobool248.i", .int 1 (evalICmp .ne x (BitVec.ofNat 32 0))) ::
        ("%key.1.i", .int 1 k) :: s.env) (s := s)
      (d := "%or.cond523.i") (c := "%key.1.i") (b := "%tobool248.i") 1
      (bb := k) (x := BitVec.ofNat 1 1) (y := evalICmp .ne x (BitVec.ofNat 32 0))
      (by rw [lookupName_cons_ne _ _ (by decide)]
          exact walkLookup_cons_self "%key.1.i" (.int 1 k) s.env)
      (by exact walkLookup_cons_self "%tobool248.i" (.int 1 (evalICmp .ne x (BitVec.ofNat 32 0))) (("%key.1.i", .int 1 k) :: s.env))]
    rfl
  exact WalkLink.pureCore (G := G) (C := C) (s := s) hInv
    (B := walkIf_end245_i) (by rw [hblock]; exact walkIf_end245_i_find) hden
    (by unfold walkCarried; decide) rfl rfl rfl
    (bit := if k = 1 then BitVec.ofNat 1 1 else evalICmp .ne x (BitVec.ofNat 32 0))
    (by simp [stateAt]) (by simp [WalkLocal]) (by simp [WalkLocal])

/-- `while.end.i`: the string scan's landing `phi` and its exit test. -/
def walkWhile_end_i : Block :=
  { name := "while.end.i",
    instrs := [
      Instr.phi "%ee.0.lcssa.i" (Ty.int 64)
        [("cond.end.i96", (Operand.reg "%idxprom.i")),
         ("LeafBlock64", (Operand.reg "%ee.011.i")),
         ("LeafBlock67", (Operand.reg "%ee.011.i")),
         ("LeafBlock69", (Operand.reg "%ee.011.i"))],
      Instr.icmp "%cmp6.i" IPred.eq 64 (Operand.reg "%ee.0.lcssa.i") (Operand.reg "%cond.i")
    ],
    term := Term.condbr (Operand.reg "%cmp6.i") "cleanup474.i" "if.end.i97" }

theorem walkWhile_end_i_find : stage2Body.findBlock "while.end.i" = some walkWhile_end_i := by
  simp [stage2Body, Function.findBlock, findBlockList, walkWhile_end_i]

/-- **`while.end.i` as a link.** -/
theorem WalkLink.while_end_i {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "while.end.i")
    {p : String} {op : Operand} {e c : BitVec 64}
    (hpre : s.pre = some p)
    (hin : phiIncoming p [("cond.end.i96", (Operand.reg "%idxprom.i")),
      ("LeafBlock64", (Operand.reg "%ee.011.i")),
      ("LeafBlock67", (Operand.reg "%ee.011.i")),
      ("LeafBlock69", (Operand.reg "%ee.011.i"))] = some op)
    (hv : evalOperand s op = some (.int 64 e))
    (hcond : lookupName s.env "%cond.i" = some (.int 64 c)) :
    ∃ s', WalkLink calls G C s
      { C with block := (if evalICmp .eq e c = 1 then "cleanup474.i" else "if.end.i97") } s' := by
  have hspecs : walkWhile_end_i.instrs =
      ([{ dst := "%ee.0.lcssa.i", ty := Ty.int 64,
          incoming := [("cond.end.i96", (Operand.reg "%idxprom.i")),
            ("LeafBlock64", (Operand.reg "%ee.011.i")),
            ("LeafBlock67", (Operand.reg "%ee.011.i")),
            ("LeafBlock69", (Operand.reg "%ee.011.i"))] }].map PhiSpec.instr) ++
        [Instr.icmp "%cmp6.i" IPred.eq 64 (Operand.reg "%ee.0.lcssa.i") (Operand.reg "%cond.i")] := by
    simp [walkWhile_end_i, PhiSpec.instr]
  have hden : denoteCode calls walkWhile_end_i.instrs s =
      some (stateAt (("%cmp6.i", .int 1 (evalICmp .eq e c)) ::
        ("%ee.0.lcssa.i", .int 64 e) :: s.env) s) := by
    rw [hspecs, denoteCode_phiRun
      (specs :=
        [{ dst := "%ee.0.lcssa.i", ty := Ty.int 64,
            incoming := [("cond.end.i96", (Operand.reg "%idxprom.i")),
          ("LeafBlock64", (Operand.reg "%ee.011.i")),
          ("LeafBlock67", (Operand.reg "%ee.011.i")),
          ("LeafBlock69", (Operand.reg "%ee.011.i"))] }])
      (vs := [("%ee.0.lcssa.i", .int 64 e)])
      (rest := [Instr.icmp "%cmp6.i" IPred.eq 64 (Operand.reg "%ee.0.lcssa.i")
        (Operand.reg "%cond.i")])
      hpre (PhiSelects.cons hin hv PhiSelects.nil) (by rfl)]
    rw [show s.bindAll [("%ee.0.lcssa.i", .int 64 e)] =
      stateAt (("%ee.0.lcssa.i", .int 64 e) :: s.env) s from rfl]
    rw [denoteCode_icmp_reg_w (calls := calls)
      (env := ("%ee.0.lcssa.i", .int 64 e) :: s.env) (s := s)
      (d := "%cmp6.i") (a := "%ee.0.lcssa.i") (b := "%cond.i") IPred.eq 64
      (x := e) (y := c) (by exact walkLookup_cons_self "%ee.0.lcssa.i" (.int 64 e) s.env)
      (by rw [lookupName_cons_ne _ _ (by decide)]; exact hcond)]
    rfl
  exact WalkLink.pureCore (G := G) (C := C) (s := s) hInv
    (B := walkWhile_end_i) (by rw [hblock]; exact walkWhile_end_i_find) hden
    (by unfold walkCarried; decide) rfl rfl rfl
    (bit := evalICmp .eq e c)
    (by simp [stateAt]) (by simp [WalkLocal]) (by simp [WalkLocal])

/-- `cleanup478.i`: the dispatch's close — the depth and index `phi`s and the
entry-stream test. -/
def walkCleanup478_i : Block :=
  { name := "cleanup478.i",
    instrs := [
      Instr.phi "%sp.i.1" (Ty.int 32)
        [("if.end473.i", (Operand.reg "%sp.i.0248")),
         ("if.end150.i", (Operand.reg "%sp.i.0248")),
         ("if.end162.i", (Operand.reg "%sp.i.0248")),
         ("if.end195.i", (Operand.reg "%sp.i.0248")),
         ("if.else334.i", (Operand.reg "%sp.i.0248")),
         ("if.then330.i", (Operand.reg "%sp.i.0248")),
         ("if.then.i.i", (Operand.reg "%inc33.i")),
         ("out_reserve.exit.i.i", (Operand.reg "%inc33.i")),
         ("if.then.i.i50", (Operand.reg "%sub.i")),
         ("out_reserve.exit.i.i60", (Operand.reg "%sub.i"))],
      Instr.phi "%k.2.i" (Ty.int 64)
        [("if.end473.i", (Operand.reg "%inc.i")),
         ("if.end150.i", (Operand.reg "%inc.i")),
         ("if.end162.i", (Operand.reg "%inc.i")),
         ("if.end195.i", (Operand.reg "%inc.i")),
         ("if.else334.i", (Operand.reg "%inc208.i")),
         ("if.then330.i", (Operand.reg "%inc208.i")),
         ("if.then.i.i", (Operand.reg "%inc.i")),
         ("out_reserve.exit.i.i", (Operand.reg "%inc.i")),
         ("if.then.i.i50", (Operand.reg "%inc.i")),
         ("out_reserve.exit.i.i60", (Operand.reg "%inc.i"))],
      Instr.icmp "%cmp.i" IPred.ult 64 (Operand.reg "%k.2.i") (Operand.reg "%nep")
    ],
    term := Term.condbr (Operand.reg "%cmp.i") "while.body.i" "if.then485.i" }

theorem walkCleanup478_i_find : stage2Body.findBlock "cleanup478.i" = some walkCleanup478_i := by
  simp [stage2Body, Function.findBlock, findBlockList, walkCleanup478_i]

/-- **`cleanup478.i` as a link.** -/
theorem WalkLink.cleanup478_i {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "cleanup478.i")
    {p : String} {op₁ op₂ : Operand} {sv : BitVec 32} {kv nv : BitVec 64}
    (hpre : s.pre = some p)
    (hin₁ : phiIncoming p
      [("if.end473.i", (Operand.reg "%sp.i.0248")),
       ("if.end150.i", (Operand.reg "%sp.i.0248")),
       ("if.end162.i", (Operand.reg "%sp.i.0248")),
       ("if.end195.i", (Operand.reg "%sp.i.0248")),
       ("if.else334.i", (Operand.reg "%sp.i.0248")),
       ("if.then330.i", (Operand.reg "%sp.i.0248")),
       ("if.then.i.i", (Operand.reg "%inc33.i")),
       ("out_reserve.exit.i.i", (Operand.reg "%inc33.i")),
       ("if.then.i.i50", (Operand.reg "%sub.i")),
       ("out_reserve.exit.i.i60", (Operand.reg "%sub.i"))] = some op₁)
    (hv₁ : evalOperand s op₁ = some (.int 32 sv))
    (hin₂ : phiIncoming p
      [("if.end473.i", (Operand.reg "%inc.i")),
       ("if.end150.i", (Operand.reg "%inc.i")),
       ("if.end162.i", (Operand.reg "%inc.i")),
       ("if.end195.i", (Operand.reg "%inc.i")),
       ("if.else334.i", (Operand.reg "%inc208.i")),
       ("if.then330.i", (Operand.reg "%inc208.i")),
       ("if.then.i.i", (Operand.reg "%inc.i")),
       ("out_reserve.exit.i.i", (Operand.reg "%inc.i")),
       ("if.then.i.i50", (Operand.reg "%inc.i")),
       ("out_reserve.exit.i.i60", (Operand.reg "%inc.i"))] = some op₂)
    (hv₂ : evalOperand s op₂ = some (.int 64 kv))
    (hnep : lookupName s.env "%nep" = some (.int 64 nv)) :
    ∃ s', WalkLink calls G C s
      { C with block := (if evalICmp .ult kv nv = 1 then "while.body.i" else "if.then485.i") } s' := by
  have hspecs : walkCleanup478_i.instrs =
      ([{ dst := "%sp.i.1", ty := Ty.int 32,
          incoming := [("if.end473.i", (Operand.reg "%sp.i.0248")),
            ("if.end150.i", (Operand.reg "%sp.i.0248")),
            ("if.end162.i", (Operand.reg "%sp.i.0248")),
            ("if.end195.i", (Operand.reg "%sp.i.0248")),
            ("if.else334.i", (Operand.reg "%sp.i.0248")),
            ("if.then330.i", (Operand.reg "%sp.i.0248")),
            ("if.then.i.i", (Operand.reg "%inc33.i")),
            ("out_reserve.exit.i.i", (Operand.reg "%inc33.i")),
            ("if.then.i.i50", (Operand.reg "%sub.i")),
            ("out_reserve.exit.i.i60", (Operand.reg "%sub.i"))] },
       { dst := "%k.2.i", ty := Ty.int 64,
          incoming := [("if.end473.i", (Operand.reg "%inc.i")),
            ("if.end150.i", (Operand.reg "%inc.i")),
            ("if.end162.i", (Operand.reg "%inc.i")),
            ("if.end195.i", (Operand.reg "%inc.i")),
            ("if.else334.i", (Operand.reg "%inc208.i")),
            ("if.then330.i", (Operand.reg "%inc208.i")),
            ("if.then.i.i", (Operand.reg "%inc.i")),
            ("out_reserve.exit.i.i", (Operand.reg "%inc.i")),
            ("if.then.i.i50", (Operand.reg "%inc.i")),
            ("out_reserve.exit.i.i60", (Operand.reg "%inc.i"))] }].map PhiSpec.instr) ++
        [Instr.icmp "%cmp.i" IPred.ult 64 (Operand.reg "%k.2.i") (Operand.reg "%nep")] := by
    simp [walkCleanup478_i, PhiSpec.instr]
  have hden : denoteCode calls walkCleanup478_i.instrs s =
      some (stateAt (("%cmp.i", .int 1 (evalICmp .ult kv nv)) ::
        ("%k.2.i", .int 64 kv) :: ("%sp.i.1", .int 32 sv) :: s.env) s) := by
    rw [hspecs, denoteCode_phiRun
      (specs :=
        [{ dst := "%sp.i.1", ty := Ty.int 32,
           incoming := [("if.end473.i", (Operand.reg "%sp.i.0248")),
            ("if.end150.i", (Operand.reg "%sp.i.0248")),
            ("if.end162.i", (Operand.reg "%sp.i.0248")),
            ("if.end195.i", (Operand.reg "%sp.i.0248")),
            ("if.else334.i", (Operand.reg "%sp.i.0248")),
            ("if.then330.i", (Operand.reg "%sp.i.0248")),
            ("if.then.i.i", (Operand.reg "%inc33.i")),
            ("out_reserve.exit.i.i", (Operand.reg "%inc33.i")),
            ("if.then.i.i50", (Operand.reg "%sub.i")),
            ("out_reserve.exit.i.i60", (Operand.reg "%sub.i"))] },
       { dst := "%k.2.i", ty := Ty.int 64,
          incoming := [("if.end473.i", (Operand.reg "%inc.i")),
            ("if.end150.i", (Operand.reg "%inc.i")),
            ("if.end162.i", (Operand.reg "%inc.i")),
            ("if.end195.i", (Operand.reg "%inc.i")),
            ("if.else334.i", (Operand.reg "%inc208.i")),
            ("if.then330.i", (Operand.reg "%inc208.i")),
            ("if.then.i.i", (Operand.reg "%inc.i")),
            ("out_reserve.exit.i.i", (Operand.reg "%inc.i")),
            ("if.then.i.i50", (Operand.reg "%inc.i")),
            ("out_reserve.exit.i.i60", (Operand.reg "%inc.i"))] }])
      (vs := [("%sp.i.1", .int 32 sv), ("%k.2.i", .int 64 kv)])
      (rest := [Instr.icmp "%cmp.i" IPred.ult 64 (Operand.reg "%k.2.i") (Operand.reg "%nep")])
      hpre (PhiSelects.cons hin₁ hv₁ (PhiSelects.cons hin₂ hv₂ PhiSelects.nil)) (by rfl)]
    rw [show s.bindAll [("%sp.i.1", .int 32 sv), ("%k.2.i", .int 64 kv)] =
      stateAt (("%k.2.i", .int 64 kv) :: ("%sp.i.1", .int 32 sv) :: s.env) s from rfl]
    rw [denoteCode_icmp_reg_w (calls := calls)
      (env := ("%k.2.i", .int 64 kv) :: ("%sp.i.1", .int 32 sv) :: s.env) (s := s)
      (d := "%cmp.i") (a := "%k.2.i") (b := "%nep") IPred.ult 64
      (x := kv) (y := nv)
      (by exact walkLookup_cons_self "%k.2.i" (.int 64 kv) (("%sp.i.1", .int 32 sv) :: s.env))
      (by rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide)]
          exact hnep)]
    rfl
  exact WalkLink.pureCore (G := G) (C := C) (s := s) hInv
    (B := walkCleanup478_i) (by rw [hblock]; exact walkCleanup478_i_find) hden
    (by unfold walkCarried; decide) rfl rfl rfl
    (bit := evalICmp .ult kv nv)
    (by simp [stateAt]) (by simp [WalkLocal]) (by simp [WalkLocal])

/-- `if.end290.i`: the arena merge's two `phi`s and the thirteen-byte reserve
test. -/
def walkIf_end290_i : Block :=
  { name := "if.end290.i",
    instrs := [
      Instr.phi "%conv286.i.sink.in" (Ty.int 64)
        [("if.then281.i", (Operand.reg "%sub260.i")), ("if.else285.i", (Operand.reg "%32"))],
      Instr.phi "%.sink" (Ty.int 64)
        [("if.then281.i", (Operand.reg "%or.i")), ("if.else285.i", (Operand.reg "%z.val36"))],
      Instr.load "%z.val" (Ty.int 64) (Operand.reg "%len"),
      Instr.load "%z.val33" (Ty.int 64) (Operand.reg "%cap"),
      Instr.binop "%add.i84" BinOp.add 64 (Operand.reg "%z.val")
        (Operand.imm (.int 64 (BitVec.ofNat 64 13))),
      Instr.icmp "%cmp.not.i85" IPred.ugt 64 (Operand.reg "%add.i84") (Operand.reg "%z.val33")
    ],
    term := Term.condbr (Operand.reg "%cmp.not.i85") "if.end.i86" "if.then328.i" }

theorem walkIf_end290_i_find : stage2Body.findBlock "if.end290.i" = some walkIf_end290_i := by
  simp [stage2Body, Function.findBlock, findBlockList, walkIf_end290_i]

/-- **`if.end290.i` as a link.**  The second `phi`'s `%32` operand is the arena
reserve's decoded length, loaded from `%outn.i`; the link takes that register's
binding as the caller's fact — its *production* is `s2_string_body`'s write
(`s2StringBody_outn_le`), which is F's side of the edge.  The two log words are the
caller's too, read at the staging's `%z + 8` and `%z + 16`. -/
theorem WalkLink.if_end290_i {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "if.end290.i")
    {p : String} {op₁ op₂ : Operand} {e1 e2 nl nc : BitVec 64}
    (hpre : s.pre = some p)
    (hin₁ : phiIncoming p [("if.then281.i", (Operand.reg "%sub260.i")),
      ("if.else285.i", (Operand.reg "%32"))] = some op₁)
    (hv₁ : evalOperand s op₁ = some (.int 64 e1))
    (hin₂ : phiIncoming p [("if.then281.i", (Operand.reg "%or.i")),
      ("if.else285.i", (Operand.reg "%z.val36"))] = some op₂)
    (hv₂ : evalOperand s op₂ = some (.int 64 e2))
    (hlen : lookupName s.env "%len" = some (.ptr (C.stage.z + 8)))
    (hcap : lookupName s.env "%cap" = some (.ptr (C.stage.z + 16)))
    (hreadL : readBytes s.mem (C.stage.z + 8) 8 = some (natToBytes nl.toNat 8))
    (hreadC : readBytes s.mem (C.stage.z + 16) 8 = some (natToBytes nc.toNat 8)) :
    ∃ s', WalkLink calls G C s
      { C with block := (if evalICmp .ugt (nl + BitVec.ofNat 64 13) nc = 1
          then "if.end.i86" else "if.then328.i") } s' := by
  have hspecs : walkIf_end290_i.instrs =
      ([{ dst := "%conv286.i.sink.in", ty := Ty.int 64,
          incoming := [("if.then281.i", (Operand.reg "%sub260.i")),
            ("if.else285.i", (Operand.reg "%32"))] },
       { dst := "%.sink", ty := Ty.int 64,
          incoming := [("if.then281.i", (Operand.reg "%or.i")),
            ("if.else285.i", (Operand.reg "%z.val36"))] }].map PhiSpec.instr) ++
        [Instr.load "%z.val" (Ty.int 64) (Operand.reg "%len"),
         Instr.load "%z.val33" (Ty.int 64) (Operand.reg "%cap"),
         Instr.binop "%add.i84" BinOp.add 64 (Operand.reg "%z.val")
           (Operand.imm (.int 64 (BitVec.ofNat 64 13))),
         Instr.icmp "%cmp.not.i85" IPred.ugt 64 (Operand.reg "%add.i84")
           (Operand.reg "%z.val33")] := by
    simp [walkIf_end290_i, PhiSpec.instr]
  have hden : denoteCode calls walkIf_end290_i.instrs s =
      some (stateAt (("%cmp.not.i85", .int 1 (evalICmp .ugt
            (nl + BitVec.ofNat 64 13) nc)) ::
        ("%add.i84", .int 64 (nl + BitVec.ofNat 64 13)) ::
        ("%z.val33", .int 64 nc) :: ("%z.val", .int 64 nl) ::
        ("%.sink", .int 64 e2) :: ("%conv286.i.sink.in", .int 64 e1) :: s.env) s) := by
    rw [hspecs, denoteCode_phiRun
      (specs :=
        [{ dst := "%conv286.i.sink.in", ty := Ty.int 64,
           incoming := [("if.then281.i", (Operand.reg "%sub260.i")),
            ("if.else285.i", (Operand.reg "%32"))] },
            { dst := "%.sink", ty := Ty.int 64,
              incoming := [("if.then281.i", (Operand.reg "%or.i")),
            ("if.else285.i", (Operand.reg "%z.val36"))] }])
      (vs := [("%conv286.i.sink.in", .int 64 e1), ("%.sink", .int 64 e2)])
      (rest := [Instr.load "%z.val" (Ty.int 64) (Operand.reg "%len"),
        Instr.load "%z.val33" (Ty.int 64) (Operand.reg "%cap"),
        Instr.binop "%add.i84" BinOp.add 64 (Operand.reg "%z.val")
          (Operand.imm (.int 64 (BitVec.ofNat 64 13))),
        Instr.icmp "%cmp.not.i85" IPred.ugt 64 (Operand.reg "%add.i84")
          (Operand.reg "%z.val33")])
      hpre (PhiSelects.cons hin₁ hv₁ (PhiSelects.cons hin₂ hv₂ PhiSelects.nil)) (by rfl)]
    rw [show s.bindAll [("%conv286.i.sink.in", .int 64 e1), ("%.sink", .int 64 e2)] =
      stateAt (("%.sink", .int 64 e2) :: ("%conv286.i.sink.in", .int 64 e1) :: s.env) s
      from rfl]
    rw [denoteCode_load64 (calls := calls)
      (env := ("%.sink", .int 64 e2) :: ("%conv286.i.sink.in", .int 64 e1) :: s.env)
      (s := s) (d := "%z.val") (p := "%len") (a := C.stage.z + 8) (v := nl)
      (by rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide)]
          exact hlen) hreadL]
    rw [denoteCode_load64 (calls := calls)
      (env := ("%z.val", .int 64 nl) :: ("%.sink", .int 64 e2) ::
        ("%conv286.i.sink.in", .int 64 e1) :: s.env)
      (s := s) (d := "%z.val33") (p := "%cap") (a := C.stage.z + 16) (v := nc)
      (by rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
            lookupName_cons_ne _ _ (by decide)]
          exact hcap) hreadC]
    rw [walkDenoteCode_add_imm_w (calls := calls)
      (env := ("%z.val33", .int 64 nc) :: ("%z.val", .int 64 nl) ::
        ("%.sink", .int 64 e2) :: ("%conv286.i.sink.in", .int 64 e1) :: s.env) (s := s)
      (d := "%add.i84") (a := "%z.val") (w := 64) (x := nl) (c := BitVec.ofNat 64 13)
      (by exact walkLookup_cons_self "%z.val" (.int 64 nl) (("%.sink", .int 64 e2) :: ("%conv286.i.sink.in", .int 64 e1) :: s.env))]
    rw [denoteCode_icmp_reg_w (calls := calls)
      (env := ("%add.i84", .int 64 (nl + BitVec.ofNat 64 13)) ::
        ("%z.val33", .int 64 nc) :: ("%z.val", .int 64 nl) ::
        ("%.sink", .int 64 e2) :: ("%conv286.i.sink.in", .int 64 e1) :: s.env) (s := s)
      (d := "%cmp.not.i85") (a := "%add.i84") (b := "%z.val33") IPred.ugt 64
      (x := nl + BitVec.ofNat 64 13) (y := nc)
      (by exact walkLookup_cons_self "%add.i84" (.int 64 (nl + BitVec.ofNat 64 13)) (("%z.val33", .int 64 nc) :: ("%z.val", .int 64 nl) :: ("%.sink", .int 64 e2) :: ("%conv286.i.sink.in", .int 64 e1) :: s.env))
      (by rw [lookupName_cons_ne _ _ (by decide)]
          exact walkLookup_cons_self "%z.val33" (.int 64 nc)
            (("%z.val", .int 64 nl) :: ("%.sink", .int 64 e2) ::
              ("%conv286.i.sink.in", .int 64 e1) :: s.env))]
    rfl
  exact WalkLink.pureCore (G := G) (C := C) (s := s) hInv
    (B := walkIf_end290_i) (by rw [hblock]; exact walkIf_end290_i_find) hden
    (by unfold walkCarried; decide) rfl rfl rfl
    (bit := evalICmp .ugt (nl + BitVec.ofNat 64 13) nc)
    (by simp [stateAt]) (by simp [WalkLocal]) (by simp [WalkLocal])

/-- `WalkLocal` at the literal comparison's entry block. -/
theorem walkLocal_forBody_i_i {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {s : State}
    (h : C.block = "for.body.i.i") :
    WalkLocal C s =
      ((∃ i c : Nat, c - i ≤ C.inner ∧ i < c ∧ c < 2 ^ 64 ∧
          s.pre = some "for.inc.i.i" ∧
          lookupName s.env "%inc.i.i" = some (.int 64 (BitVec.ofNat 64 i)) ∧
          lookupName s.env "%cond.i.i" = some (.int 64 (BitVec.ofNat 64 c))) ∨
        (∃ c : Nat, c ≤ C.inner ∧ 0 < c ∧ c < 2 ^ 64 ∧
          s.pre = some "if.end48.i" ∧
          lookupName s.env "%cond.i.i" = some (.int 64 (BitVec.ofNat 64 c)))) := by
  simp [WalkLocal, h]

/-- `for.body.i.i`: the literal comparison's `phi`, the two bytes, and the test. -/
def walkFor_body_i_i : Block :=
  { name := "for.body.i.i",
    instrs := [
      Instr.phi "%i.029.i.i" (Ty.int 64)
        [("for.inc.i.i", (Operand.reg "%inc.i.i")),
         ("if.end48.i", (Operand.imm (.int 64 (BitVec.ofNat 64 0))))],
      Instr.gep "%arrayidx.i.i" (Ty.int 8) (Operand.reg "%arrayidx10.i")
        (Operand.reg "%i.029.i.i"),
      Instr.load "%44" (Ty.int 8) (Operand.reg "%arrayidx.i.i"),
      Instr.gep "%arrayidx6.i.i" (Ty.int 8) (Operand.reg "%lit.0.i")
        (Operand.reg "%i.029.i.i"),
      Instr.load "%45" (Ty.int 8) (Operand.reg "%arrayidx6.i.i"),
      Instr.icmp "%cmp8.not.i.i" IPred.eq 8 (Operand.reg "%44") (Operand.reg "%45")
    ],
    term := Term.condbr (Operand.reg "%cmp8.not.i.i") "for.inc.i.i" "if.then57.i" }

theorem walkFor_body_i_i_find :
    stage2Body.findBlock "for.body.i.i" = some walkFor_body_i_i := by
  simp [stage2Body, Function.findBlock, findBlockList, walkFor_body_i_i]

/-- **`for.body.i.i` as a link.**  The `for.inc.i.i` edge is the measure's guard: its
local fact is read off the invariant's disjunctive landing fact — the latch's
increment on the back edge, the entry's zero on the other — and the `phi`'s
selection is which of the two the counter carries. -/
theorem WalkLink.for_body_i_i {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "for.body.i.i")
    {p : String} {op : Operand} {iv : BitVec 64} {da dl : Nat} {b1 b2 : UInt8}
    (hpre : s.pre = some p)
    (hin : phiIncoming p [("for.inc.i.i", (Operand.reg "%inc.i.i")),
      ("if.end48.i", (Operand.imm (.int 64 (BitVec.ofNat 64 0))))] = some op)
    (hv : evalOperand s op = some (.int 64 iv))
    (hdoc : lookupName s.env "%arrayidx10.i" = some (.ptr da))
    (hlit : lookupName s.env "%lit.0.i" = some (.ptr dl))
    (hpos : (iv.signExtend 64).toNat < 2 ^ 63)
    (hread1 : readBytes s.mem (da + (iv.signExtend 64).toNat) 1 = some [b1])
    (hread2 : readBytes s.mem (dl + (iv.signExtend 64).toNat) 1 = some [b2]) :
    ∃ s', WalkLink calls G C s
      { C with block := (if evalICmp .eq (BitVec.ofNat 8 b1.toNat)
          (BitVec.ofNat 8 b2.toNat) = 1 then "for.inc.i.i" else "if.then57.i") } s' := by
  have hspecs : walkFor_body_i_i.instrs =
      ([{ dst := "%i.029.i.i", ty := Ty.int 64,
          incoming := [("for.inc.i.i", (Operand.reg "%inc.i.i")),
            ("if.end48.i", (Operand.imm (.int 64 (BitVec.ofNat 64 0))))] }].map PhiSpec.instr) ++
        [Instr.gep "%arrayidx.i.i" (Ty.int 8) (Operand.reg "%arrayidx10.i")
           (Operand.reg "%i.029.i.i"),
         Instr.load "%44" (Ty.int 8) (Operand.reg "%arrayidx.i.i"),
         Instr.gep "%arrayidx6.i.i" (Ty.int 8) (Operand.reg "%lit.0.i")
           (Operand.reg "%i.029.i.i"),
         Instr.load "%45" (Ty.int 8) (Operand.reg "%arrayidx6.i.i"),
         Instr.icmp "%cmp8.not.i.i" IPred.eq 8 (Operand.reg "%44") (Operand.reg "%45")] := by
    simp [walkFor_body_i_i, PhiSpec.instr]
  have hden : denoteCode calls walkFor_body_i_i.instrs s =
      some (stateAt (("%cmp8.not.i.i", .int 1 (evalICmp .eq
            (BitVec.ofNat 8 b1.toNat) (BitVec.ofNat 8 b2.toNat))) ::
        ("%45", .int 8 (BitVec.ofNat 8 b2.toNat)) ::
        ("%arrayidx6.i.i", .ptr (dl + (iv.signExtend 64).toNat)) ::
        ("%44", .int 8 (BitVec.ofNat 8 b1.toNat)) ::
        ("%arrayidx.i.i", .ptr (da + (iv.signExtend 64).toNat)) ::
        ("%i.029.i.i", .int 64 iv) :: s.env) s) := by
    rw [hspecs, denoteCode_phiRun
      (specs :=
        [{ dst := "%i.029.i.i", ty := Ty.int 64,
            incoming := [("for.inc.i.i", (Operand.reg "%inc.i.i")),
          ("if.end48.i", (Operand.imm (.int 64 (BitVec.ofNat 64 0))))] }])
      (vs := [("%i.029.i.i", .int 64 iv)])
      (rest := [Instr.gep "%arrayidx.i.i" (Ty.int 8) (Operand.reg "%arrayidx10.i")
          (Operand.reg "%i.029.i.i"),
        Instr.load "%44" (Ty.int 8) (Operand.reg "%arrayidx.i.i"),
        Instr.gep "%arrayidx6.i.i" (Ty.int 8) (Operand.reg "%lit.0.i")
          (Operand.reg "%i.029.i.i"),
        Instr.load "%45" (Ty.int 8) (Operand.reg "%arrayidx6.i.i"),
        Instr.icmp "%cmp8.not.i.i" IPred.eq 8 (Operand.reg "%44") (Operand.reg "%45")])
      hpre (PhiSelects.cons hin hv PhiSelects.nil) (by rfl)]
    rw [show s.bindAll [("%i.029.i.i", .int 64 iv)] =
      stateAt (("%i.029.i.i", .int 64 iv) :: s.env) s from rfl]
    rw [denoteCode_gep8_reg (calls := calls)
      (env := ("%i.029.i.i", .int 64 iv) :: s.env) (s := s)
      (d := "%arrayidx.i.i") (base := "%arrayidx10.i") (off := "%i.029.i.i") (a := da)
      (idx := iv)
      (by rw [lookupName_cons_ne _ _ (by decide)]; exact hdoc)
      (by exact walkLookup_cons_self "%i.029.i.i" (.int 64 iv) s.env)
      hpos]
    rw [denoteCode_load8_single (calls := calls)
      (env := ("%arrayidx.i.i", .ptr (da + (iv.signExtend 64).toNat)) ::
        ("%i.029.i.i", .int 64 iv) :: s.env) (s := s)
      (d := "%44") (p := "%arrayidx.i.i") (a := da + (iv.signExtend 64).toNat)
      (by exact walkLookup_cons_self "%arrayidx.i.i" (.ptr (da + (iv.signExtend 64).toNat)) (("%i.029.i.i", .int 64 iv) :: s.env)) hread1]
    rw [denoteCode_gep8_reg (calls := calls)
      (env := ("%44", .int 8 (BitVec.ofNat 8 b1.toNat)) ::
        ("%arrayidx.i.i", .ptr (da + (iv.signExtend 64).toNat)) ::
        ("%i.029.i.i", .int 64 iv) :: s.env) (s := s)
      (d := "%arrayidx6.i.i") (base := "%lit.0.i") (off := "%i.029.i.i") (a := dl)
      (idx := iv)
      (by rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide)]
          exact hlit)
      (by rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide)]
          exact walkLookup_cons_self "%i.029.i.i" (.int 64 iv) s.env)
      hpos]
    rw [denoteCode_load8_single (calls := calls)
      (env := ("%arrayidx6.i.i", .ptr (dl + (iv.signExtend 64).toNat)) ::
        ("%44", .int 8 (BitVec.ofNat 8 b1.toNat)) ::
        ("%arrayidx.i.i", .ptr (da + (iv.signExtend 64).toNat)) ::
        ("%i.029.i.i", .int 64 iv) :: s.env) (s := s)
      (d := "%45") (p := "%arrayidx6.i.i") (a := dl + (iv.signExtend 64).toNat)
      (by exact walkLookup_cons_self "%arrayidx6.i.i" (.ptr (dl + (iv.signExtend 64).toNat)) ((("%44", .int 8 (BitVec.ofNat 8 b1.toNat))) :: ("%arrayidx.i.i", .ptr (da + (iv.signExtend 64).toNat)) :: ("%i.029.i.i", .int 64 iv) :: s.env)) hread2]
    rw [denoteCode_icmp_reg_w (calls := calls)
      (env := ("%45", .int 8 (BitVec.ofNat 8 b2.toNat)) ::
        ("%arrayidx6.i.i", .ptr (dl + (iv.signExtend 64).toNat)) ::
        ("%44", .int 8 (BitVec.ofNat 8 b1.toNat)) ::
        ("%arrayidx.i.i", .ptr (da + (iv.signExtend 64).toNat)) ::
        ("%i.029.i.i", .int 64 iv) :: s.env) (s := s)
      (d := "%cmp8.not.i.i") (a := "%44") (b := "%45") IPred.eq 8
      (x := BitVec.ofNat 8 b1.toNat) (y := BitVec.ofNat 8 b2.toNat)
      (by rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide)]
          exact walkLookup_cons_self "%44" (.int 8 (BitVec.ofNat 8 b1.toNat))
            (("%arrayidx.i.i", .ptr (da + (iv.signExtend 64).toNat)) ::
              ("%i.029.i.i", .int 64 iv) :: s.env))
      (by exact walkLookup_cons_self "%45" (.int 8 (BitVec.ofNat 8 b2.toNat)) (("%arrayidx6.i.i", .ptr (dl + (iv.signExtend 64).toNat)) :: ("%44", .int 8 (BitVec.ofNat 8 b1.toNat)) :: ("%arrayidx.i.i", .ptr (da + (iv.signExtend 64).toNat)) :: ("%i.029.i.i", .int 64 iv) :: s.env))]
    rfl
  refine WalkLink.pureCore (G := G) (C := C) (s := s) hInv
    (B := walkFor_body_i_i) (by rw [hblock]; exact walkFor_body_i_i_find) hden
    (by unfold walkCarried; decide) rfl rfl rfl
    (bit := evalICmp .eq (BitVec.ofNat 8 b1.toNat) (BitVec.ofNat 8 b2.toNat))
    (by simp [stateAt]) ?_ (by simp [WalkLocal])
  -- the `for.inc.i.i` edge: the measure's guard, from the invariant's landing fact
  have hloc := hInv.blockLocal
  rw [walkLocal_forBody_i_i hblock] at hloc
  simp [WalkLocal]
  rcases hloc with
    ⟨i0, c0, hbud, hlt, hc64, hpre0, hinc, hcondi⟩ |
    ⟨c0, hbud, hpos0, hc64, hpre0, hcondi⟩
  · -- landed: the phi selected the latch's increment
    have hp : p = "for.inc.i.i" := by
      rw [hpre] at hpre0
      exact Option.some.inj hpre0
    have hop : op = Operand.reg "%inc.i.i" := by
      rw [hp] at hin
      simpa [phiIncoming] using hin.symm
    have hsel : lookupName s.env "%inc.i.i" = some (.int 64 iv) := by
      have h := hv
      rw [hop] at h
      simpa [evalOperand] using h
    have hiv : iv = BitVec.ofNat 64 i0 := by
      rw [hsel] at hinc
      have h2 : (Value.int 64 iv : Value) = Value.int 64 (BitVec.ofNat 64 i0) :=
        Option.some.inj hinc
      injection h2 with _ h3
    refine ⟨i0, c0, ?_, hlt, hc64, ?_, ?_⟩
    · omega
    · simp only [stateAt]
      rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
        lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
        lookupName_cons_ne _ _ (by decide)]
      rw [lookupName_cons_self]
      rw [hiv]
    · simp only [stateAt]
      rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
        lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
        lookupName_cons_ne _ _ (by decide)]
      exact hcondi
  · -- entered: the phi selected zero
    have hp : p = "if.end48.i" := by
      rw [hpre] at hpre0
      exact Option.some.inj hpre0
    have hop : op = Operand.imm (.int 64 (BitVec.ofNat 64 0)) := by
      rw [hp] at hin
      simpa [phiIncoming] using hin.symm
    have hsel : iv = 0 := by
      have h := hv
      rw [hop] at h
      simpa [evalOperand] using h.symm
    refine ⟨0, c0, ?_, hpos0, hc64, ?_, ?_⟩
    · omega
    · simp only [stateAt]
      rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
        lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
        lookupName_cons_ne _ _ (by decide)]
      rw [lookupName_cons_self, hsel]
      rfl
    · simp only [stateAt]
      rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
        lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
        lookupName_cons_ne _ _ (by decide)]
      exact hcondi

/-! ### The three store blocks -/

/-- `if.end372.i`: the scan's end `phi`, its store at the token's end slot, and the
literal test that follows. -/
def walkIf_end372_i : Block :=
  { name := "if.end372.i",
    instrs := [
      Instr.phi "%ee.1.i" (Ty.int 64)
        [("cond.end349.i", (Operand.reg "%idxprom.i")),
         ("while.body370.i", (Operand.reg "%cond350.i")),
         ("LeafBlock43", (Operand.reg "%ee.0.i238")),
         ("LeafBlock46", (Operand.reg "%ee.0.i238")),
         ("LeafBlock48", (Operand.reg "%ee.0.i238")),
         ("LeafBlock33", (Operand.reg "%cond350.i")),
         ("LeafBlock35", (Operand.reg "%cond350.i")),
         ("LeafBlock37", (Operand.reg "%cond350.i"))],
      Instr.store (Ty.int 64) (Operand.reg "%ee.1.i") (Operand.reg "%end.i"),
      Instr.icmp "%cmp376.i" IPred.eq 8 (Operand.reg "%8")
        (Operand.imm (.int 8 (BitVec.ofNat 8 45))),
      Instr.binop "%37" BinOp.add 8 (Operand.reg "%8")
        (Operand.imm (.int 8 (BitVec.ofNat 8 208))),
      Instr.icmp "%or.cond524.i" IPred.ult 8 (Operand.reg "%37")
        (Operand.imm (.int 8 (BitVec.ofNat 8 10))),
      Instr.binop "%or.cond677.i" BinOp.or 1 (Operand.reg "%cmp376.i")
        (Operand.reg "%or.cond524.i")
    ],
    term := Term.condbr (Operand.reg "%or.cond677.i") "if.then413.i" "if.else387.i" }

theorem walkIf_end372_i_find : stage2Body.findBlock "if.end372.i" = some walkIf_end372_i := by
  simp [stage2Body, Function.findBlock, findBlockList, walkIf_end372_i]

/-- **`if.end372.i` as a link.**  The store writes the scan's end position at
`%end.i` (`%t352.i + 8`), inside the token's extent; no `WalkInv` clause names the
token, so `frame` is the only clause the write touches. -/
theorem WalkLink.if_end372_i {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "if.end372.i")
    {p : String} {op : Operand} {e : BitVec 64} {b8 : BitVec 8}
    (hpre : s.pre = some p)
    (hin : phiIncoming p
      [("cond.end349.i", (Operand.reg "%idxprom.i")),
       ("while.body370.i", (Operand.reg "%cond350.i")),
       ("LeafBlock43", (Operand.reg "%ee.0.i238")),
       ("LeafBlock46", (Operand.reg "%ee.0.i238")),
       ("LeafBlock48", (Operand.reg "%ee.0.i238")),
       ("LeafBlock33", (Operand.reg "%cond350.i")),
       ("LeafBlock35", (Operand.reg "%cond350.i")),
       ("LeafBlock37", (Operand.reg "%cond350.i"))] = some op)
    (hv : evalOperand s op = some (.int 64 e))
    (hend : lookupName s.env "%end.i" = some (.ptr (C.stage.tok + 8)))
    (h8 : lookupName s.env "%8" = some (.int 8 b8)) :
    ∃ s', WalkLink calls G C s
      { C with block := (if (evalICmp .eq b8 (BitVec.ofNat 8 45) |||
            evalICmp .ult (b8 + BitVec.ofNat 8 208) (BitVec.ofNat 8 10)) = 1 then
          "if.then413.i" else "if.else387.i") } s' := by
  have hfree : walkCarried walkIf_end372_i.instrs := by unfold walkCarried; decide
  let m' : Mem := writeBytes s.mem (C.stage.tok + 8) (natToBytes e.toNat 8)
  let sFin : State :=
    stateAt (("%or.cond677.i", .int 1 (evalICmp .eq b8 (BitVec.ofNat 8 45) |||
            evalICmp .ult (b8 + BitVec.ofNat 8 208) (BitVec.ofNat 8 10))) ::
        ("%or.cond524.i", .int 1 (evalICmp .ult (b8 + BitVec.ofNat 8 208)
          (BitVec.ofNat 8 10))) ::
        ("%37", .int 8 (b8 + BitVec.ofNat 8 208)) ::
        ("%cmp376.i", .int 1 (evalICmp .eq b8 (BitVec.ofNat 8 45))) ::
        ("%ee.1.i", .int 64 e) :: s.env) { s with mem := m' }
  have hspecs : walkIf_end372_i.instrs =
      ([{ dst := "%ee.1.i", ty := Ty.int 64,
          incoming := [("cond.end349.i", (Operand.reg "%idxprom.i")),
            ("while.body370.i", (Operand.reg "%cond350.i")),
            ("LeafBlock43", (Operand.reg "%ee.0.i238")),
            ("LeafBlock46", (Operand.reg "%ee.0.i238")),
            ("LeafBlock48", (Operand.reg "%ee.0.i238")),
            ("LeafBlock33", (Operand.reg "%cond350.i")),
            ("LeafBlock35", (Operand.reg "%cond350.i")),
            ("LeafBlock37", (Operand.reg "%cond350.i"))] }].map PhiSpec.instr) ++
        [Instr.store (Ty.int 64) (Operand.reg "%ee.1.i") (Operand.reg "%end.i"),
         Instr.icmp "%cmp376.i" IPred.eq 8 (Operand.reg "%8")
           (Operand.imm (.int 8 (BitVec.ofNat 8 45))),
         Instr.binop "%37" BinOp.add 8 (Operand.reg "%8")
           (Operand.imm (.int 8 (BitVec.ofNat 8 208))),
         Instr.icmp "%or.cond524.i" IPred.ult 8 (Operand.reg "%37")
           (Operand.imm (.int 8 (BitVec.ofNat 8 10))),
         Instr.binop "%or.cond677.i" BinOp.or 1 (Operand.reg "%cmp376.i")
           (Operand.reg "%or.cond524.i")] := by
    simp [walkIf_end372_i, PhiSpec.instr]
  have hden : denoteCode calls walkIf_end372_i.instrs s = some sFin := by
    rw [hspecs, denoteCode_phiRun
      (specs :=
        [{ dst := "%ee.1.i", ty := Ty.int 64,
            incoming := [("cond.end349.i", (Operand.reg "%idxprom.i")),
          ("while.body370.i", (Operand.reg "%cond350.i")),
          ("LeafBlock43", (Operand.reg "%ee.0.i238")),
          ("LeafBlock46", (Operand.reg "%ee.0.i238")),
          ("LeafBlock48", (Operand.reg "%ee.0.i238")),
          ("LeafBlock33", (Operand.reg "%cond350.i")),
          ("LeafBlock35", (Operand.reg "%cond350.i")),
          ("LeafBlock37", (Operand.reg "%cond350.i"))] }])
      (vs := [("%ee.1.i", .int 64 e)])
      (rest := [Instr.store (Ty.int 64) (Operand.reg "%ee.1.i") (Operand.reg "%end.i"),
        Instr.icmp "%cmp376.i" IPred.eq 8 (Operand.reg "%8")
          (Operand.imm (.int 8 (BitVec.ofNat 8 45))),
        Instr.binop "%37" BinOp.add 8 (Operand.reg "%8")
          (Operand.imm (.int 8 (BitVec.ofNat 8 208))),
        Instr.icmp "%or.cond524.i" IPred.ult 8 (Operand.reg "%37")
          (Operand.imm (.int 8 (BitVec.ofNat 8 10))),
        Instr.binop "%or.cond677.i" BinOp.or 1 (Operand.reg "%cmp376.i")
          (Operand.reg "%or.cond524.i")])
      hpre (PhiSelects.cons hin hv PhiSelects.nil) (by rfl)]
    rw [show s.bindAll [("%ee.1.i", .int 64 e)] =
      stateAt (("%ee.1.i", .int 64 e) :: s.env) s from rfl]
    rw [denoteCode_store64 (calls := calls)
      (env := ("%ee.1.i", .int 64 e) :: s.env) (s := s)
      (v := "%ee.1.i") (p := "%end.i") (x := e) (a := C.stage.tok + 8)
      (by exact walkLookup_cons_self "%ee.1.i" (.int 64 e) s.env) hend]
    rw [denoteCode_icmp_eq_imm_w (calls := calls)
      (env := ("%ee.1.i", .int 64 e) :: s.env) (s := { s with mem := m' }) (d := "%cmp376.i") (a := "%8") 8
      (x := b8) (c := BitVec.ofNat 8 45)
      (by rw [lookupName_cons_ne _ _ (by decide)]; exact h8)]
    rw [walkDenoteCode_add_imm_w (calls := calls)
      (env := ("%cmp376.i", .int 1 (evalICmp .eq b8 (BitVec.ofNat 8 45))) ::
        ("%ee.1.i", .int 64 e) :: s.env) (s := { s with mem := m' })
      (d := "%37") (a := "%8") (w := 8) (x := b8) (c := BitVec.ofNat 8 208)
      (by rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide)]
          exact h8)]
    rw [walkDenoteCode_icmp_imm (calls := calls)
      (env := ("%37", .int 8 (b8 + BitVec.ofNat 8 208)) ::
        ("%cmp376.i", .int 1 (evalICmp .eq b8 (BitVec.ofNat 8 45))) ::
        ("%ee.1.i", .int 64 e) :: s.env) (s := { s with mem := m' })
      (d := "%or.cond524.i") (a := "%37") IPred.ult 8
      (x := b8 + BitVec.ofNat 8 208) (c := BitVec.ofNat 8 10)
      (by exact walkLookup_cons_self "%37" (.int 8 (b8 + BitVec.ofNat 8 208)) (("%cmp376.i", .int 1 (evalICmp .eq b8 (BitVec.ofNat 8 45))) :: ("%ee.1.i", .int 64 e) :: s.env))]
    rw [denoteCode_or_reg_w (calls := calls)
      (env := ("%or.cond524.i", .int 1 (evalICmp .ult (b8 + BitVec.ofNat 8 208)
          (BitVec.ofNat 8 10))) ::
        ("%37", .int 8 (b8 + BitVec.ofNat 8 208)) ::
        ("%cmp376.i", .int 1 (evalICmp .eq b8 (BitVec.ofNat 8 45))) ::
        ("%ee.1.i", .int 64 e) :: s.env) (s := { s with mem := m' })
      (d := "%or.cond677.i") (a := "%cmp376.i") (b := "%or.cond524.i") (w := 1)
      (x := evalICmp .eq b8 (BitVec.ofNat 8 45))
      (y := evalICmp .ult (b8 + BitVec.ofNat 8 208) (BitVec.ofNat 8 10))
      (by rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide)]
          exact walkLookup_cons_self "%cmp376.i" (.int 1 (evalICmp .eq b8 (BitVec.ofNat 8 45)))
            (("%ee.1.i", .int 64 e) :: s.env))
      (by exact walkLookup_cons_self "%or.cond524.i" (.int 1 (evalICmp .ult (b8 + BitVec.ofNat 8 208) (BitVec.ofNat 8 10))) (("%37", .int 8 (b8 + BitVec.ofNat 8 208)) :: ("%cmp376.i", .int 1 (evalICmp .eq b8 (BitVec.ofNat 8 45))) :: ("%ee.1.i", .int 64 e) :: s.env))]
    rfl
  have hpc : s.pc = C.block := hInv.pc_eq
  have hfind : stage2Body.findBlock C.block = some walkIf_end372_i := by
    rw [hblock]; exact walkIf_end372_i_find
  have hfind' : stage2Body.findBlock s.pc = some walkIf_end372_i := by
    rw [hpc]; exact hfind
  have hterm : walkIf_end372_i.term =
      Term.condbr (Operand.reg "%or.cond677.i") "if.then413.i" "if.else387.i" := rfl
  let s' : State := { sFin with pc :=
    (if evalICmp .eq b8 (BitVec.ofNat 8 45) ||| evalICmp .ult
        (b8 + BitVec.ofNat 8 208) (BitVec.ofNat 8 10) = 1 then
      "if.then413.i" else "if.else387.i"), pre := some s.pc }
  have hstep : LeanLLVM.step calls stage2Body s = Ctrl.jump s' := by
    simp only [LeanLLVM.step, hfind', hden, hterm]
    rw [walkExecTerm_condbr (d := "%or.cond677.i") (tl := "if.then413.i")
      (fl := "if.else387.i")
      (bit := evalICmp .eq b8 (BitVec.ofNat 8 45) |||
        evalICmp .ult (b8 + BitVec.ofNat 8 208) (BitVec.ofNat 8 10))
      (by exact walkLookup_cons_self "%or.cond677.i" (.int 1 (evalICmp .eq b8 (BitVec.ofNat 8 45) ||| evalICmp .ult (b8 + BitVec.ofNat 8 208) (BitVec.ofNat 8 10))) (("%or.cond524.i", .int 1 (evalICmp .ult (b8 + BitVec.ofNat 8 208) (BitVec.ofNat 8 10))) :: ("%37", .int 8 (b8 + BitVec.ofNat 8 208)) :: ("%cmp376.i", .int 1 (evalICmp .eq b8 (BitVec.ofNat 8 45))) :: ("%ee.1.i", .int 64 e) :: s.env))]
    dsimp only [s', sFin, m', stateAt]
  refine ⟨s', ⟨hInv, hstep, ?_, ?_⟩⟩
  refine
    { pc_eq := rfl
      blockIndex := ?_
      k_le := hInv.k_le
      events_le := hInv.events_le
      evlen_eq := hInv.evlen_eq
      evBytes := ?_
      alen_le_sum := hInv.alen_le_sum
      alen_ge := hInv.alen_ge
      spans_order := hInv.spans_order
      spans_inside := hInv.spans_inside
      pending_at := hInv.pending_at
      pending_cursor := hInv.pending_cursor
      eoff_le := hInv.eoff_le
      inner_cap := hInv.inner_cap
      depth_cap := hInv.depth_cap
      depth_reg := ?_
      ptrs := ?_
      log_hash := ?_
      log_len := ?_
      log_cap := ?_
      log_alen := ?_
      log_acap := ?_
      owned := walkStaged_write rfl hInv.owned
      frame := ?_
      blockLocal := by split <;> simp [WalkLocal] }
  · dsimp only [s', sFin]
    rw [denoteCode_lookupName calls walkIf_end372_i.instrs "%k.0.i249"
      (fun i hi => (hfree i hi).1) s sFin hden]
    exact hInv.blockIndex
  · dsimp only [s', sFin, m', stateAt]
    have hlen : (C.events.map EventRecord.encodedBytes).flatten.length =
        (C.events.map EventRecord.encodedSize).sum := by
      simp only [List.length_flatten, List.map_map]; rfl
    have hsum := EventRecord.sum_encodedSize_le C.events
    simp only [stage2RecordBytes] at hsum
    have hroom := G.evRoom
    simp only [stage2RecordBytes] at hroom
    have hN : G.nev0 + (C.events.map EventRecord.encodedBytes).flatten.length ≤ G.evcap := by
      have h1 := hInv.events_le
      have h2 := hInv.k_le
      have h3 := G.nep_le
      rw [hlen]; omega
    rw [walkReadBytes_ev_of_tok_write (tok := C.stage.tok) (ev := G.ev) (evcap := G.evcap)
      (nev0 := G.nev0) (N := _) (x := e) (walkTok_ev_sep hInv) hN]
    exact hInv.evBytes
  · dsimp only [s', sFin]
    rw [denoteCode_lookupName calls walkIf_end372_i.instrs "%sp.i.0248"
      (fun i hi => (hfree i hi).2.1) s sFin hden]
    exact hInv.depth_reg
  · dsimp only [s', sFin]
    exact WalkPtrs.of_run hInv.ptrs hfree hden
  · dsimp only [s', sFin, m', stateAt]
    rw [walkReadBytes_log_of_tok_write (tok := C.stage.tok) (z := C.stage.z) (off := 32)
      (N := 4) (x := e) (walkTok_z_sep hInv) (by decide)]
    exact hInv.log_hash
  · dsimp only [s', sFin, m', stateAt]
    rw [walkReadBytes_log_of_tok_write (tok := C.stage.tok) (z := C.stage.z) (off := 8)
      (N := 8) (x := e) (walkTok_z_sep hInv) (by decide)]
    exact hInv.log_len
  · dsimp only [s', sFin, m', stateAt]
    rw [walkReadBytes_log_of_tok_write (tok := C.stage.tok) (z := C.stage.z) (off := 16)
      (N := 8) (x := e) (walkTok_z_sep hInv) (by decide)]
    exact hInv.log_cap
  · dsimp only [s', sFin, m', stateAt]
    rw [walkReadBytes_log_of_tok_write (tok := C.stage.tok) (z := C.stage.z) (off := 48)
      (N := 8) (x := e) (walkTok_z_sep hInv) (by decide)]
    exact hInv.log_alen
  · dsimp only [s', sFin, m', stateAt]
    rw [walkReadBytes_log_of_tok_write (tok := C.stage.tok) (z := C.stage.z) (off := 56)
      (N := 8) (x := e) (walkTok_z_sep hInv) (by decide)]
    exact hInv.log_acap
  · dsimp only [s', sFin, m', stateAt]
    refine walkFrame_write_inside hInv.frame ?_
    intro k hk
    refine walkWide_of_seven ?_
    exact walkTok_inside (by
      have hk' : k < (natToBytes e.toNat 8).length := hk
      rw [natToBytes_length] at hk'
      exact hk')
  · simp [walkMeasure]

/-- `if.then57.i`: the literal scan's refusal store, after the `phi` and the `add`. -/
def walkIf_then57_i : Block :=
  { name := "if.then57.i",
    instrs := [
      Instr.phi "%ei49.0.ph.i" (Ty.int 64)
        [("for.end.i.i", (Operand.reg "%cond.i.i")),
         ("for.body.i.i", (Operand.reg "%i.029.i.i"))],
      Instr.binop "%add60.i" BinOp.add 64 (Operand.reg "%ei49.0.ph.i")
        (Operand.reg "%idxprom.i"),
      Instr.gep "%off1.i131.i" (Ty.int 8) (Operand.reg "%e")
        (Operand.imm (.int 64 (BitVec.ofNat 64 8))),
      Instr.store (Ty.int 64) (Operand.reg "%add60.i") (Operand.reg "%off1.i131.i")
    ],
    term := Term.br "cleanup474.i" }

theorem walkIf_then57_i_find : stage2Body.findBlock "if.then57.i" = some walkIf_then57_i := by
  simp [stage2Body, Function.findBlock, findBlockList, walkIf_then57_i]

/-- **`if.then57.i` as a link**: the refusal's offset, with class C's carry update. -/
theorem WalkLink.if_then57_i {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "if.then57.i")
    {p : String} {op : Operand} {x ix : BitVec 64}
    (hpre : s.pre = some p)
    (hin : phiIncoming p [("for.end.i.i", (Operand.reg "%cond.i.i")),
      ("for.body.i.i", (Operand.reg "%i.029.i.i"))] = some op)
    (hv : evalOperand s op = some (.int 64 x))
    (hidx : lookupName s.env "%idxprom.i" = some (.int 64 ix))
    (he : lookupName s.env "%e" = some (.ptr C.stage.e))
    (hj : (x + ix).toNat ≤ G.n) :
    ∃ s', WalkLink calls G C s
      { C with block := "cleanup474.i", eoff := (x + ix).toNat, refusal := true } s' := by
  have hfree : walkCarried walkIf_then57_i.instrs := by unfold walkCarried; decide
  let m' : Mem := writeBytes s.mem (C.stage.e + 8) (natToBytes (x + ix).toNat 8)
  let sFin : State :=
    stateAt (("%off1.i131.i", .ptr (C.stage.e + 8)) ::
      ("%add60.i", .int 64 (x + ix)) ::
      ("%ei49.0.ph.i", .int 64 x) :: s.env) { s with mem := m' }
  have hspecs : walkIf_then57_i.instrs =
      ([{ dst := "%ei49.0.ph.i", ty := Ty.int 64,
          incoming := [("for.end.i.i", (Operand.reg "%cond.i.i")),
            ("for.body.i.i", (Operand.reg "%i.029.i.i"))] }].map PhiSpec.instr) ++
        [Instr.binop "%add60.i" BinOp.add 64 (Operand.reg "%ei49.0.ph.i")
           (Operand.reg "%idxprom.i"),
         Instr.gep "%off1.i131.i" (Ty.int 8) (Operand.reg "%e")
           (Operand.imm (.int 64 (BitVec.ofNat 64 8))),
         Instr.store (Ty.int 64) (Operand.reg "%add60.i") (Operand.reg "%off1.i131.i")] := by
    simp [walkIf_then57_i, PhiSpec.instr]
  have hden : denoteCode calls walkIf_then57_i.instrs s = some sFin := by
    rw [hspecs, denoteCode_phiRun
      (specs :=
        [{ dst := "%ei49.0.ph.i", ty := Ty.int 64,
            incoming := [("for.end.i.i", (Operand.reg "%cond.i.i")),
          ("for.body.i.i", (Operand.reg "%i.029.i.i"))] }])
      (vs := [("%ei49.0.ph.i", .int 64 x)])
      (rest := [Instr.binop "%add60.i" BinOp.add 64 (Operand.reg "%ei49.0.ph.i")
          (Operand.reg "%idxprom.i"),
        Instr.gep "%off1.i131.i" (Ty.int 8) (Operand.reg "%e")
          (Operand.imm (.int 64 (BitVec.ofNat 64 8))),
        Instr.store (Ty.int 64) (Operand.reg "%add60.i") (Operand.reg "%off1.i131.i")])
      hpre (PhiSelects.cons hin hv PhiSelects.nil) (by rfl)]
    rw [show s.bindAll [("%ei49.0.ph.i", .int 64 x)] =
      stateAt (("%ei49.0.ph.i", .int 64 x) :: s.env) s from rfl]
    rw [walkDenoteCode_add_reg_w (calls := calls)
      (env := ("%ei49.0.ph.i", .int 64 x) :: s.env) (s := s)
      (d := "%add60.i") (a := "%ei49.0.ph.i") (b := "%idxprom.i") 64
      (x := x) (y := ix)
      (by exact walkLookup_cons_self "%ei49.0.ph.i" (.int 64 x) s.env)
      (by rw [lookupName_cons_ne _ _ (by decide)]; exact hidx)]
    rw [walkDenoteCode_gep8_imm_at (calls := calls)
      (env := ("%add60.i", .int 64 (x + ix)) :: ("%ei49.0.ph.i", .int 64 x) :: s.env)
      (s := s) (d := "%off1.i131.i") (base := "%e") (a := C.stage.e) (c := 8)
      (by rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide)]
          exact he) (by decide)]
    rw [denoteCode_store64 (calls := calls)
      (env := ("%off1.i131.i", .ptr (C.stage.e + 8)) ::
        ("%add60.i", .int 64 (x + ix)) :: ("%ei49.0.ph.i", .int 64 x) :: s.env)
      (s := s) (v := "%add60.i") (p := "%off1.i131.i") (x := x + ix)
      (a := C.stage.e + 8)
      (by exact walkLookup_cons_self "%add60.i" (.int 64 (x + ix)) (("%ei49.0.ph.i", .int 64 x) :: s.env))
      (by exact walkLookup_cons_self "%off1.i131.i" (.ptr (C.stage.e + 8)) (("%add60.i", .int 64 (x + ix)) :: ("%ei49.0.ph.i", .int 64 x) :: s.env))]
    rfl
  have hpc : s.pc = C.block := hInv.pc_eq
  have hfind : stage2Body.findBlock C.block = some walkIf_then57_i := by
    rw [hblock]; exact walkIf_then57_i_find
  have hfind' : stage2Body.findBlock s.pc = some walkIf_then57_i := by
    rw [hpc]; exact hfind
  have hterm : walkIf_then57_i.term = Term.br "cleanup474.i" := rfl
  let s' : State := { sFin with pc := "cleanup474.i", pre := some s.pc }
  have hstep : LeanLLVM.step calls stage2Body s = Ctrl.jump s' := by
    simp only [LeanLLVM.step, hfind', hden, hterm, execTerm]
    dsimp only [s', sFin, m', stateAt]
  refine ⟨s', ⟨hInv, hstep, ?_, ?_⟩⟩
  refine
    { pc_eq := rfl
      blockIndex := ?_
      k_le := hInv.k_le
      events_le := hInv.events_le
      evlen_eq := hInv.evlen_eq
      evBytes := ?_
      alen_le_sum := hInv.alen_le_sum
      alen_ge := hInv.alen_ge
      spans_order := hInv.spans_order
      spans_inside := hInv.spans_inside
      pending_at := hInv.pending_at
      pending_cursor := hInv.pending_cursor
      eoff_le := hj
      inner_cap := hInv.inner_cap
      depth_cap := hInv.depth_cap
      depth_reg := ?_
      ptrs := ?_
      log_hash := ?_
      log_len := ?_
      log_cap := ?_
      log_alen := ?_
      log_acap := ?_
      owned := walkStaged_write rfl hInv.owned
      frame := ?_
      blockLocal := by simp [WalkLocal] }
  · dsimp only [s', sFin]
    rw [denoteCode_lookupName calls walkIf_then57_i.instrs "%k.0.i249"
      (fun i hi => (hfree i hi).1) s sFin hden]
    exact hInv.blockIndex
  · dsimp only [s', sFin, m', stateAt]
    have hlen : (C.events.map EventRecord.encodedBytes).flatten.length =
        (C.events.map EventRecord.encodedSize).sum := by
      simp only [List.length_flatten, List.map_map]; rfl
    have hsum := EventRecord.sum_encodedSize_le C.events
    simp only [stage2RecordBytes] at hsum
    have hroom := G.evRoom
    simp only [stage2RecordBytes] at hroom
    have hN : G.nev0 + (C.events.map EventRecord.encodedBytes).flatten.length ≤ G.evcap := by
      have h1 := hInv.events_le
      have h2 := hInv.k_le
      have h3 := G.nep_le
      rw [hlen]; omega
    rw [walkReadBytes_ev_of_refusal_write (e := C.stage.e) (ev := G.ev) (evcap := G.evcap)
      (nev0 := G.nev0) (x := x + ix) (N := _) (e_ev_sep hInv) hN]
    exact hInv.evBytes
  · dsimp only [s', sFin]
    rw [denoteCode_lookupName calls walkIf_then57_i.instrs "%sp.i.0248"
      (fun i hi => (hfree i hi).2.1) s sFin hden]
    exact hInv.depth_reg
  · dsimp only [s', sFin]
    exact WalkPtrs.of_run hInv.ptrs hfree hden
  · dsimp only [s', sFin, m', stateAt]
    rw [walkReadBytes_log_of_refusal_write (e := C.stage.e) (z := C.stage.z) (off := 32)
      (x := x + ix) (N := 4) (e_z_sep hInv) (by decide)]
    exact hInv.log_hash
  · dsimp only [s', sFin, m', stateAt]
    rw [walkReadBytes_log_of_refusal_write (e := C.stage.e) (z := C.stage.z) (off := 8)
      (x := x + ix) (N := 8) (e_z_sep hInv) (by decide)]
    exact hInv.log_len
  · dsimp only [s', sFin, m', stateAt]
    rw [walkReadBytes_log_of_refusal_write (e := C.stage.e) (z := C.stage.z) (off := 16)
      (x := x + ix) (N := 8) (e_z_sep hInv) (by decide)]
    exact hInv.log_cap
  · dsimp only [s', sFin, m', stateAt]
    rw [walkReadBytes_log_of_refusal_write (e := C.stage.e) (z := C.stage.z) (off := 48)
      (x := x + ix) (N := 8) (e_z_sep hInv) (by decide)]
    exact hInv.log_alen
  · dsimp only [s', sFin, m', stateAt]
    rw [walkReadBytes_log_of_refusal_write (e := C.stage.e) (z := C.stage.z) (off := 56)
      (x := x + ix) (N := 8) (e_z_sep hInv) (by decide)]
    exact hInv.log_acap
  · dsimp only [s', sFin, m', stateAt]
    refine walkFrame_write_inside hInv.frame ?_
    intro k hk
    rw [natToBytes_length] at hk
    exact walkWide_of_seven (eoff_inside hk)
  · simp [walkMeasure]

/-- `while.end78.i`: the escape scan's refusal store. -/
def walkWhile_end78_i : Block :=
  { name := "while.end78.i",
    instrs := [
      Instr.phi "%s2.0.lcssa.i" (Ty.int 64)
        [("if.end67.i", (Operand.reg "%ee.0.lcssa.i")),
         ("while.body76.i", (Operand.reg "%cond.i")),
         ("LeafBlock85", (Operand.reg "%s2.020.i")),
         ("LeafBlock88", (Operand.reg "%s2.020.i")),
         ("LeafBlock90", (Operand.reg "%s2.020.i"))],
      Instr.gep "%off1.i137.i" (Ty.int 8) (Operand.reg "%e")
        (Operand.imm (.int 64 (BitVec.ofNat 64 8))),
      Instr.store (Ty.int 64) (Operand.reg "%s2.0.lcssa.i") (Operand.reg "%off1.i137.i")
    ],
    term := Term.br "cleanup474.i" }

theorem walkWhile_end78_i_find :
    stage2Body.findBlock "while.end78.i" = some walkWhile_end78_i := by
  simp [stage2Body, Function.findBlock, findBlockList, walkWhile_end78_i]

/-- **`while.end78.i` as a link**: the refusal's offset, with class C's carry update. -/
theorem WalkLink.while_end78_i {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "while.end78.i")
    {p : String} {op : Operand} {x : BitVec 64}
    (hpre : s.pre = some p)
    (hin : phiIncoming p [("if.end67.i", (Operand.reg "%ee.0.lcssa.i")),
      ("while.body76.i", (Operand.reg "%cond.i")),
      ("LeafBlock85", (Operand.reg "%s2.020.i")),
      ("LeafBlock88", (Operand.reg "%s2.020.i")),
      ("LeafBlock90", (Operand.reg "%s2.020.i"))] = some op)
    (hv : evalOperand s op = some (.int 64 x))
    (he : lookupName s.env "%e" = some (.ptr C.stage.e))
    (hj : x.toNat ≤ G.n) :
    ∃ s', WalkLink calls G C s
      { C with block := "cleanup474.i", eoff := x.toNat, refusal := true } s' := by
  have hfree : walkCarried walkWhile_end78_i.instrs := by unfold walkCarried; decide
  let m' : Mem := writeBytes s.mem (C.stage.e + 8) (natToBytes x.toNat 8)
  let sFin : State :=
    stateAt (("%off1.i137.i", .ptr (C.stage.e + 8)) ::
      ("%s2.0.lcssa.i", .int 64 x) :: s.env) { s with mem := m' }
  have hspecs : walkWhile_end78_i.instrs =
      ([{ dst := "%s2.0.lcssa.i", ty := Ty.int 64,
          incoming := [("if.end67.i", (Operand.reg "%ee.0.lcssa.i")),
            ("while.body76.i", (Operand.reg "%cond.i")),
            ("LeafBlock85", (Operand.reg "%s2.020.i")),
            ("LeafBlock88", (Operand.reg "%s2.020.i")),
            ("LeafBlock90", (Operand.reg "%s2.020.i"))] }].map PhiSpec.instr) ++
        [Instr.gep "%off1.i137.i" (Ty.int 8) (Operand.reg "%e")
           (Operand.imm (.int 64 (BitVec.ofNat 64 8))),
         Instr.store (Ty.int 64) (Operand.reg "%s2.0.lcssa.i") (Operand.reg "%off1.i137.i")] := by
    simp [walkWhile_end78_i, PhiSpec.instr]
  have hden : denoteCode calls walkWhile_end78_i.instrs s = some sFin := by
    rw [hspecs, denoteCode_phiRun
      (specs :=
        [{ dst := "%s2.0.lcssa.i", ty := Ty.int 64,
            incoming := [("if.end67.i", (Operand.reg "%ee.0.lcssa.i")),
          ("while.body76.i", (Operand.reg "%cond.i")),
          ("LeafBlock85", (Operand.reg "%s2.020.i")),
          ("LeafBlock88", (Operand.reg "%s2.020.i")),
          ("LeafBlock90", (Operand.reg "%s2.020.i"))] }])
      (vs := [("%s2.0.lcssa.i", .int 64 x)])
      (rest := [Instr.gep "%off1.i137.i" (Ty.int 8) (Operand.reg "%e")
          (Operand.imm (.int 64 (BitVec.ofNat 64 8))),
        Instr.store (Ty.int 64) (Operand.reg "%s2.0.lcssa.i") (Operand.reg "%off1.i137.i")])
      hpre (PhiSelects.cons hin hv PhiSelects.nil) (by rfl)]
    rw [show s.bindAll [("%s2.0.lcssa.i", .int 64 x)] =
      stateAt (("%s2.0.lcssa.i", .int 64 x) :: s.env) s from rfl]
    rw [walkDenoteCode_gep8_imm_at (calls := calls)
      (env := ("%s2.0.lcssa.i", .int 64 x) :: s.env) (s := s)
      (d := "%off1.i137.i") (base := "%e") (a := C.stage.e) (c := 8)
      (by rw [lookupName_cons_ne _ _ (by decide)]; exact he) (by decide)]
    rw [denoteCode_store64 (calls := calls)
      (env := ("%off1.i137.i", .ptr (C.stage.e + 8)) ::
        ("%s2.0.lcssa.i", .int 64 x) :: s.env) (s := s)
      (v := "%s2.0.lcssa.i") (p := "%off1.i137.i") (x := x) (a := C.stage.e + 8)
      (by exact walkLookup_cons_self "%s2.0.lcssa.i" (.int 64 x) s.env)
      (by exact walkLookup_cons_self "%off1.i137.i" (.ptr (C.stage.e + 8)) (("%s2.0.lcssa.i", .int 64 x) :: s.env))]
    rfl
  have hpc : s.pc = C.block := hInv.pc_eq
  have hfind : stage2Body.findBlock C.block = some walkWhile_end78_i := by
    rw [hblock]; exact walkWhile_end78_i_find
  have hfind' : stage2Body.findBlock s.pc = some walkWhile_end78_i := by
    rw [hpc]; exact hfind
  have hterm : walkWhile_end78_i.term = Term.br "cleanup474.i" := rfl
  let s' : State := { sFin with pc := "cleanup474.i", pre := some s.pc }
  have hstep : LeanLLVM.step calls stage2Body s = Ctrl.jump s' := by
    simp only [LeanLLVM.step, hfind', hden, hterm, execTerm]
    dsimp only [s', sFin, m', stateAt]
  refine ⟨s', ⟨hInv, hstep, ?_, ?_⟩⟩
  refine
    { pc_eq := rfl
      blockIndex := ?_
      k_le := hInv.k_le
      events_le := hInv.events_le
      evlen_eq := hInv.evlen_eq
      evBytes := ?_
      alen_le_sum := hInv.alen_le_sum
      alen_ge := hInv.alen_ge
      spans_order := hInv.spans_order
      spans_inside := hInv.spans_inside
      pending_at := hInv.pending_at
      pending_cursor := hInv.pending_cursor
      eoff_le := hj
      inner_cap := hInv.inner_cap
      depth_cap := hInv.depth_cap
      depth_reg := ?_
      ptrs := ?_
      log_hash := ?_
      log_len := ?_
      log_cap := ?_
      log_alen := ?_
      log_acap := ?_
      owned := walkStaged_write rfl hInv.owned
      frame := ?_
      blockLocal := by simp [WalkLocal] }
  · dsimp only [s', sFin]
    rw [denoteCode_lookupName calls walkWhile_end78_i.instrs "%k.0.i249"
      (fun i hi => (hfree i hi).1) s sFin hden]
    exact hInv.blockIndex
  · dsimp only [s', sFin, m', stateAt]
    have hlen : (C.events.map EventRecord.encodedBytes).flatten.length =
        (C.events.map EventRecord.encodedSize).sum := by
      simp only [List.length_flatten, List.map_map]; rfl
    have hsum := EventRecord.sum_encodedSize_le C.events
    simp only [stage2RecordBytes] at hsum
    have hroom := G.evRoom
    simp only [stage2RecordBytes] at hroom
    have hN : G.nev0 + (C.events.map EventRecord.encodedBytes).flatten.length ≤ G.evcap := by
      have h1 := hInv.events_le
      have h2 := hInv.k_le
      have h3 := G.nep_le
      rw [hlen]; omega
    rw [walkReadBytes_ev_of_refusal_write (e := C.stage.e) (ev := G.ev) (evcap := G.evcap)
      (nev0 := G.nev0) (x := x) (N := _) (e_ev_sep hInv) hN]
    exact hInv.evBytes
  · dsimp only [s', sFin]
    rw [denoteCode_lookupName calls walkWhile_end78_i.instrs "%sp.i.0248"
      (fun i hi => (hfree i hi).2.1) s sFin hden]
    exact hInv.depth_reg
  · dsimp only [s', sFin]
    exact WalkPtrs.of_run hInv.ptrs hfree hden
  · dsimp only [s', sFin, m', stateAt]
    rw [walkReadBytes_log_of_refusal_write (e := C.stage.e) (z := C.stage.z) (off := 32)
      (x := x) (N := 4) (e_z_sep hInv) (by decide)]
    exact hInv.log_hash
  · dsimp only [s', sFin, m', stateAt]
    rw [walkReadBytes_log_of_refusal_write (e := C.stage.e) (z := C.stage.z) (off := 8)
      (x := x) (N := 8) (e_z_sep hInv) (by decide)]
    exact hInv.log_len
  · dsimp only [s', sFin, m', stateAt]
    rw [walkReadBytes_log_of_refusal_write (e := C.stage.e) (z := C.stage.z) (off := 16)
      (x := x) (N := 8) (e_z_sep hInv) (by decide)]
    exact hInv.log_cap
  · dsimp only [s', sFin, m', stateAt]
    rw [walkReadBytes_log_of_refusal_write (e := C.stage.e) (z := C.stage.z) (off := 48)
      (x := x) (N := 8) (e_z_sep hInv) (by decide)]
    exact hInv.log_alen
  · dsimp only [s', sFin, m', stateAt]
    rw [walkReadBytes_log_of_refusal_write (e := C.stage.e) (z := C.stage.z) (off := 56)
      (x := x) (N := 8) (e_z_sep hInv) (by decide)]
    exact hInv.log_acap
  · dsimp only [s', sFin, m', stateAt]
    refine walkFrame_write_inside hInv.frame ?_
    intro k hk
    rw [natToBytes_length] at hk
    exact walkWide_of_seven (eoff_inside hk)
  · simp [walkMeasure]


/-! ### The instrument

The module's declarations' axiom footprints, measured rather than asserted.  The
two ends are `JsonStage2WalkScope`'s for the walk: `walkLookup_cons_self` (the
environment read the runs are built from) and the store links (the deepest
invariant rebuild in the class). -/
/-- info: 'LeanLLVM.Refinement.WalkScope.walkLookup_cons_self' depends on axioms: [propext] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.WalkScope.walkLookup_cons_self

/-- info: 'LeanLLVM.Refinement.WalkScope.walkDenoteCode_icmp_imm' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.WalkScope.walkDenoteCode_icmp_imm

/-- info: 'LeanLLVM.Refinement.WalkScope.walkTok_ev_sep' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.WalkScope.walkTok_ev_sep

/-- info: 'LeanLLVM.Refinement.WalkScope.WalkLink.scanLanding' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.WalkScope.WalkLink.scanLanding

/-- info: 'LeanLLVM.Refinement.WalkScope.WalkLink.for_body_i_i' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.WalkScope.WalkLink.for_body_i_i

/-- info: 'LeanLLVM.Refinement.WalkScope.WalkLink.if_end290_i' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.WalkScope.WalkLink.if_end290_i

/-- info: 'LeanLLVM.Refinement.WalkScope.WalkLink.if_end372_i' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.WalkScope.WalkLink.if_end372_i

/-- info: 'LeanLLVM.Refinement.WalkScope.WalkLink.if_then57_i' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.WalkScope.WalkLink.if_then57_i

/-- info: 'LeanLLVM.Refinement.WalkScope.WalkLink.while_end78_i' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.WalkScope.WalkLink.while_end78_i

end WalkScope
end LeanLLVM.Refinement
