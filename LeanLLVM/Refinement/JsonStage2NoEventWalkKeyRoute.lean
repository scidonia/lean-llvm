/-
The no-event walk's object-member key route.

An object's member is a key, a colon and a value.  The walk has two entries into
the key's own blocks, and both are real:

* **entry A**, the first member: the `{` head's dispatch (`if.then9`), the
  bracket's next-entry read (`if.end74`), and the byte's dispatch
  (`NodeBlock21 → LeafBlock17`) land in `key_body` with `%k.1.in` reading the
  head's `k`; the prologue is the brace class's and this module owns its last
  two links;
* **entry B**, a later member: the frame-0 after-value arm's `,`
  (`if.end378 → if.then384 → NodeBlock35 → LeafBlock31 → if.end409`), then
  `if.end111`'s next-entry read and quote test, land in `key_body` with
  `%k.1.in` reading the comma's index.

Both entries hand `key_body` the same seven `phi` selections, so the route from
`key_body`'s entry is one object parameterised by `%k.1.in`'s value `v`: the
entry's index register, not a head's.  This module states that tail and proves
it, then reads the pair endpoint's `Stage2NoEventWalkPairSrc` off its final
state.  The two entries are separate producers: this module proves `if.end111`'s
hop (`link_ifEnd111_true`) and the eight-block tail.  The arrival at `if.end111`
is the committed `Stage2NoEventWalkFrameZeroCommaBoundary`'s `,` arm; the `{`
head's prologue is the brace class's (`Stage2NoEventWalkEntryAPrologue` bundles
its output), and this module proves the two links that prologue was missing —
`NodeBlock21`'s true arm and `LeafBlock17`'s quote test — plus the tail.

The tail's blocks are the walk's own key scanner (`probe fixture :321-672`):

    key_body  %k.1 = %k.1.in + 2; %cmp127.not = %k.1 < nep
    if.end136 %inc137 = %k.1.in + 3; entry at %k.1; store %inc137 at %k219
    if.end150 the key's byte extent and the scratch guard
    if.end159 the lifetime marker, the source slot and @s2_string_body
    NodeBlock25/LeafBlock23  the call's result's two tests
    do.body172 the plain arm's record field (the escape-free key)
    expect_colon  %alen.2/%arena.3/%add177.pn and the colon's entry bound
    if.end303  (the cycle's block; one link past `expect_colon`)

**The index.**  `v` is `%k.1.in`: the entry *before* the key.  The key's quote is
at `v+1`, its closing quote at `v+2`, and the colon at `v+3` (`%inc137`), so the
register `v` is the pair's `k` and the pair's next head is at `v+4`
(`%inc304 = %k.1.in + 4`).  The pair's one token is the key's, and the endpoint's
consumed-count bound is therefore at `v+1`: the carry counts the key while
`%k.1.in` still reads `v`.

**The scanner's arms.**  `LeafBlock23` splits on the call's result: `1` is the
escape-free key (`do.body172`, whose `%add177` is the record's field), and a
larger result is the arena arm (`for.cond.preheader`'s byte-sum loop, whose
`%add191` is the field and whose `%add187` advances `alen`).  This module proves
only the escape-free arm (`do.body172`); the arena arm is **not covered here**
— its loop is the string class's arena body at the key's block names, and no
slice of it is stated in this module.

**What is the caller's.**  The invariant, the base table, the source count and
the `Inv` transport across the route's memory-neutral links are derived here.
What the blocks cannot supply, and what stays a hypothesis of the source
(`Stage2NoEventWalkKeySrc`), is:

* `key_body`'s and `expect_colon`'s lifetime markers' outcomes — derivable from
  `stage2Calls_lifetime` once the selection is `stage2Calls`, premises over an
  abstract `Calls`;
* the call `@s2_string_body`'s outcome and memory frame — M2's
  `stage2Calls_s2_string_body` supplies them; no `Inv` field mentions a callee;
* the scanner's answer `1` (`rRet`, the escape-free arm's selection) — the
  call's result, not a fact about the invariant;
* the endpoint's `Stage2NoEventWalkTrace` — the key's record is the class
  route's output evidence (`strPlain` with `key := true`);
* the pair endpoint's colon byte, at `v+3`, and the scratch guard — the class's
  staging facts, not `Head` facts.

**What the exporter supplies.**  The eight blocks from the `{` head to
`NodeBlock21`'s entry are the brace class's, and
`stage2NoEventWalkBracePrologue` (there) states them once: from a `Head` at `{`
and the staged reads it yields the state's cells.  This module's entry A is its
reader at the opening quote — `Stage2NoEventWalkBracePrologueCells.toEntryA`
turns the exporter's cells into the predicate below — so a caller holding the
`Head` needs no prologue of its own.  `stage2NoEventWalkKeyRoute_of_head` is
that composition: the eight links, the two below, and the tail, in one segment.
-/
import LeanLLVM.Refinement.JsonStage2NoEventWalkCyclePairA
import LeanLLVM.Refinement.JsonStage2NoEventWalkRowsBrace
import LeanLLVM.Refinement.JsonStage2NoEventWalkString

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 1600000
set_option pp.maxSteps 200000

namespace LeanLLVM.Refinement

open LeanLLVM
open LeanLLVM.JSON
open LeanLLVM.Refinement.JsonStage2NoEventIR
open LeanLLVM.Refinement.JsonEntryIR (readLanes32)
open LeanLLVM.Refinement.JsonEntrySteps (readBytes_length)
open LeanLLVM.Refinement.BlockEval
open LeanLLVM.Refinement.JsonS1MasksIR (evalInstr_binop)

/-! ### A 32-bit sum and the `i32` add step

`%add175` is the key scanner's only `i32` arithmetic: `%p.0 + 1`, the key's
opening-quote lane with the body's first byte behind it.  The 64-bit step
lemmas do not cover it, so the block layer states it once. -/

/-- **A sum of two 32-bit `ofNat` words is the sum's word.** -/
theorem stage2NoEventOfNat32Add {x y : Nat} :
    BitVec.ofNat 32 x + BitVec.ofNat 32 y = BitVec.ofNat 32 (x + y) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    ← Nat.add_mod]

/-- `%d = add i32 %a, <c>`. -/
theorem stage2NoEventWalk_step_add32_imm (calls : Calls) (env : Env) (s : State)
    (d a : String) {x c : BitVec 32}
    (ha : lookupName env a = some (.int 32 x)) :
    evalInstr calls (stateAt env s) (.binop d .add 32 (.reg a) (.imm (.int 32 c))) =
      some (stateAt ((d, .int 32 (x + c)) :: env) s) := by
  simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq, stateAt, withEnv, State.bind]
    using evalInstr_binop (r := (x + c).toNat)
      (ha := evalOperand_reg_of env s a (.int 32 x) ha)
      (hb := evalOperand_lit_of _ 32 c)
      (hr := by simp [evalBinopNat, evalBinop, BitVec.ofNat_toNat])

/-- The `i32` add's chain step. -/
theorem stage2NoEventWalk_denote_add32_imm (calls : Calls) (env : Env) (s : State)
    (d a : String) {x c : BitVec 32}
    (ha : lookupName env a = some (.int 32 x)) (is : List Instr) :
    denoteCode calls (.binop d .add 32 (.reg a) (.imm (.int 32 c)) :: is)
        (stateAt env s) =
      denoteCode calls is (stateAt ((d, .int 32 (x + c)) :: env) s) := by
  rw [denoteCode_cons_of _ _ _ _ _
    (stage2NoEventWalk_step_add32_imm calls env s d a (x := x) (c := c) ha)]

/-- A lookup through a stack of cell layers at a name none of them binds. -/
theorem keyRoute_lookup_layers {n : String} {v : Value} :
    ∀ (layers : List (List (String × Value))) (env : Env),
      (∀ cs ∈ layers, n ∉ cs.map (·.1)) →
      lookupName env n = some v →
      lookupName (layers.foldr cells env) n = some v
  | [], env, _, h => h
  | cs :: rest, env, hd, h => by
      show lookupName (cells cs (List.foldr cells env rest)) n = some v
      rw [cells_lookup_of_notin cs _ (hd cs (by simp))]
      exact keyRoute_lookup_layers rest env (fun c hc => hd c (by simp [hc])) h

/-- A cell list's own binding. -/
theorem keyRoute_lookup_of_mem {cs : List (String × Value)} {env : Env}
    {n : String} {v : Value} (hm : (n, v) ∈ cs) (hnd : (cs.map (·.1)).Nodup) :
    lookupName (cells cs env) n = some v :=
  cells_lookup_of_mem cs env hm hnd

/-! ### `if.end111` -/

/-- `if.end111`'s six instructions. -/
def ifEnd111Instrs : List Instr :=
  [ Instr.gep "%arrayidx112" (Ty.int 32) (Operand.reg "%ep") (Operand.reg "%inc379"),
    Instr.load "%12" (Ty.int 32) (Operand.reg "%arrayidx112"),
    Instr.zext "%idxprom113" 32 64 (Operand.reg "%12"),
    Instr.gep "%arrayidx114" (Ty.int 8) (Operand.reg "%b")
      (Operand.reg "%idxprom113"),
    Instr.load "%13" (Ty.int 8) (Operand.reg "%arrayidx114"),
    Instr.icmp "%cmp116.not" IPred.eq 8 (Operand.reg "%13")
      (Operand.imm (.int 8 (BitVec.ofNat 8 34))) ]

/-- `if.end111`, pinned. -/
def ifEnd111Block : Block :=
  { name := "if.end111", instrs := ifEnd111Instrs,
    term := Term.condbr (Operand.reg "%cmp116.not") "key_body" "if.then118" }

theorem ifEnd111Block_find :
    stage2NoEventBody.findBlock "if.end111" = some ifEnd111Block := by
  decide

/-- The cells `if.end111` binds, newest first. -/
def ifEnd111CellList (ep b inc lane x : Nat) : List (String × Value) :=
  [("%cmp116.not", .int 1 (evalICmp .eq (BitVec.ofNat 8 x) (BitVec.ofNat 8 34))),
   ("%13", .int 8 (BitVec.ofNat 8 x)),
   ("%arrayidx114", .ptr (b + lane)),
   ("%idxprom113", .int 64 (BitVec.ofNat 64 lane)),
   ("%12", .int 32 (BitVec.ofNat 32 lane)),
   ("%arrayidx112", .ptr (ep + 4 * inc))]

/-- **`if.end111`'s run**. -/
theorem ifEnd111_denote (calls : Calls) (env : Env) (s : State)
    {ep b inc lane x : Nat} {bs4 bs1 : List UInt8}
    (hep : lookupName env "%ep" = some (.ptr ep))
    (hb : lookupName env "%b" = some (.ptr b))
    (hinc : lookupName env "%inc379" = some (.int 64 (BitVec.ofNat 64 inc)))
    (hincAddr : inc < 2 ^ 63)
    (hbs4 : bytesToNat bs4 = lane) (hLaneLt : lane < 2 ^ 32)
    (hlane : readBytes s.mem (ep + 4 * inc) 4 = some bs4)
    (hbs1 : bytesToNat bs1 = x)
    (hbyte : readBytes s.mem (b + lane) 1 = some bs1) :
    denoteCode calls ifEnd111Instrs (stateAt env s) =
      some (stateAt (cells (ifEnd111CellList ep b inc lane x) env) s) := by
  rw [ifEnd111Instrs]
  rw [stage2NoEventWalk_denote_gep32 (calls := calls) (env := env) (s := s)
    (d := "%arrayidx112") (base := "%ep") (off := "%inc379")
    (a := ep) (o := BitVec.ofNat 64 inc) (hb := hep) (ho := hinc)
    (hs := by rw [stage2NoEventSignExtend_ofNat hincAddr]; exact hincAddr)]
  rw [show ep + ((BitVec.ofNat 64 inc).signExtend 64).toNat * 4 = ep + 4 * inc
    from by rw [stage2NoEventSignExtend_ofNat hincAddr, Nat.mul_comm]]
  rw [stage2NoEventWalk_denote_load_int (calls := calls)
    (env := ("%arrayidx112", .ptr (ep + 4 * inc)) :: env) (s := s)
    (d := "%12") (p := "%arrayidx112") (w := 32) (a := ep + 4 * inc) (bs := bs4)
    (hw := by decide) (hp := by simp only [lookupName_cons_self]) (hv := hlane)]
  rw [hbs4]
  rw [denoteCode_zext (calls := calls)
    (env := ("%12", .int 32 (BitVec.ofNat 32 lane)) ::
      ("%arrayidx112", .ptr (ep + 4 * inc)) :: env) (s := s)
    (d := "%idxprom113") (v := "%12") (wIn := 32) (wOut := 64)
    (x := BitVec.ofNat 32 lane) (hv := by simp only [lookupName_cons_self])]
  rw [stage2NoEventOfNat32_toNat hLaneLt]
  rw [denoteCode_gep8_reg (calls := calls)
    (env := ("%idxprom113", .int 64 (BitVec.ofNat 64 lane)) ::
      ("%12", .int 32 (BitVec.ofNat 32 lane)) ::
      ("%arrayidx112", .ptr (ep + 4 * inc)) :: env) (s := s)
    (d := "%arrayidx114") (base := "%b") (off := "%idxprom113")
    (a := b) (idx := BitVec.ofNat 64 lane) (hb := hb)
    (ho := by simp only [lookupName_cons_self])
    (hpos := stage2NoEventLane_signExtend_lt hLaneLt)]
  rw [stage2NoEventSignExtend_toNat (by omega)]
  rw [stage2NoEventWalk_denote_load_int (calls := calls)
    (env := ("%arrayidx114", .ptr (b + lane)) ::
      ("%idxprom113", .int 64 (BitVec.ofNat 64 lane)) ::
      ("%12", .int 32 (BitVec.ofNat 32 lane)) ::
      ("%arrayidx112", .ptr (ep + 4 * inc)) :: env) (s := s)
    (d := "%13") (p := "%arrayidx114") (w := 8) (a := b + lane) (bs := bs1)
    (hw := by decide) (hp := by simp only [lookupName_cons_self]) (hv := hbyte)]
  rw [hbs1]
  rw [stage2NoEventWalk_denote_icmp_imm (calls := calls)
    (env := ("%13", .int 8 (BitVec.ofNat 8 x)) ::
      ("%arrayidx114", .ptr (b + lane)) ::
      ("%idxprom113", .int 64 (BitVec.ofNat 64 lane)) ::
      ("%12", .int 32 (BitVec.ofNat 32 lane)) ::
      ("%arrayidx112", .ptr (ep + 4 * inc)) :: env) (s := s)
    (d := "%cmp116.not") (a := "%13") (p := .eq) (w := 8)
    (c := BitVec.ofNat 8 34) (x := BitVec.ofNat 8 x)
    (ha := by simp only [lookupName_cons_self])]
  simp only [ifEnd111CellList, cells, denoteCode_nil]

/-- **`if.end111` at the quote**: the true arm, to `key_body`. -/
theorem link_ifEnd111_true {calls : Calls} {K : Stage2NoEventWalkCarry} {mem : Mem}
    {s : State} {ep b inc lane x : Nat} {bs4 bs1 : List UInt8}
    (h : Stage2NoEventWalkInv K mem s) (hpc : s.pc = "if.end111")
    (hep : lookupName s.env "%ep" = some (.ptr ep))
    (hb : lookupName s.env "%b" = some (.ptr b))
    (hinc : lookupName s.env "%inc379" = some (.int 64 (BitVec.ofNat 64 inc)))
    (hincAddr : inc < 2 ^ 63)
    (hbs4 : bytesToNat bs4 = lane) (hLaneLt : lane < 2 ^ 32)
    (hlane : readBytes s.mem (ep + 4 * inc) 4 = some bs4)
    (hbs1 : bytesToNat bs1 = x)
    (hbyte : readBytes s.mem (b + lane) 1 = some bs1)
    (hy : evalICmp .eq (BitVec.ofNat 8 x) (BitVec.ofNat 8 34) = 1) :
    Stage2NoEventWalkLink calls K mem s K
      (stage2NoEventWalkNext (cells (ifEnd111CellList ep b inc lane x) s.env)
        s "key_body") := by
  have hcode : denoteCode calls ifEnd111Instrs (stateAt s.env s) =
      some (stateAt (cells (ifEnd111CellList ep b inc lane x) s.env) s) :=
    ifEnd111_denote (calls := calls) s.env s hep hb hinc hincAddr hbs4 hLaneLt hlane
      hbs1 hbyte
  refine stage2NoEventWalkLink_condbr_true
    (env' := cells (ifEnd111CellList ep b inc lane x) s.env)
    h (by rw [hpc]; exact ifEnd111Block_find) hcode rfl ?_
  simp only [ifEnd111CellList, cells, lookupName_cons_self, hy]

/-! ### `key_body` -/

/-- `key_body`'s seven `phi`s, as specs. -/
def keyBodyPhiSpecs : List PhiSpec :=
  [ { dst := "%p.0", ty := Ty.int 32,
      incoming := [("LeafBlock17", Operand.reg "%10"),
        ("if.end111", Operand.reg "%12")] },
    { dst := "%sp.1", ty := Ty.int 32,
      incoming := [("LeafBlock17", Operand.reg "%inc24"),
        ("if.end111", Operand.reg "%sp.4")] },
    { dst := "%k.1.in", ty := Ty.int 64,
      incoming := [("LeafBlock17", Operand.reg "%k.0.lcssa1086"),
        ("if.end111", Operand.reg "%k.6")] },
    { dst := "%alen.1", ty := Ty.int 64,
      incoming := [("LeafBlock17", Operand.reg "%alen.0.ph1405"),
        ("if.end111", Operand.reg "%alen.8")] },
    { dst := "%arena.1", ty := Ty.int 64,
      incoming := [("LeafBlock17", Operand.reg "%arena.0.ph1406"),
        ("if.end111", Operand.reg "%arena.10")] },
    { dst := "%terms.1", ty := Ty.int 64,
      incoming := [("LeafBlock17", Operand.reg "%add"),
        ("if.end111", Operand.reg "%terms.8")] },
    { dst := "%tokens.1", ty := Ty.int 64,
      incoming := [("LeafBlock17", Operand.reg "%inc26"),
        ("if.end111", Operand.reg "%tokens.8")] } ]

/-- The block's `phi` instructions. -/
def keyBodyPhiInstrs : List Instr :=
  [ Instr.phi "%p.0" (Ty.int 32) [("LeafBlock17", (Operand.reg "%10")),
      ("if.end111", (Operand.reg "%12"))],
    Instr.phi "%sp.1" (Ty.int 32) [("LeafBlock17", (Operand.reg "%inc24")),
      ("if.end111", (Operand.reg "%sp.4"))],
    Instr.phi "%k.1.in" (Ty.int 64) [("LeafBlock17", (Operand.reg "%k.0.lcssa1086")),
      ("if.end111", (Operand.reg "%k.6"))],
    Instr.phi "%alen.1" (Ty.int 64) [("LeafBlock17", (Operand.reg "%alen.0.ph1405")),
      ("if.end111", (Operand.reg "%alen.8"))],
    Instr.phi "%arena.1" (Ty.int 64) [("LeafBlock17", (Operand.reg "%arena.0.ph1406")),
      ("if.end111", (Operand.reg "%arena.10"))],
    Instr.phi "%terms.1" (Ty.int 64) [("LeafBlock17", (Operand.reg "%add")),
      ("if.end111", (Operand.reg "%terms.8"))],
    Instr.phi "%tokens.1" (Ty.int 64) [("LeafBlock17", (Operand.reg "%inc26")),
      ("if.end111", (Operand.reg "%tokens.8"))] ]

theorem keyBodyPhi_eq : keyBodyPhiInstrs = List.map PhiSpec.instr keyBodyPhiSpecs := by
  decide

/-- `key_body`'s three instructions after the run. -/
def keyBodyRestInstrs : List Instr :=
  [ Instr.binop "%k.1" BinOp.add 64 (Operand.reg "%k.1.in")
      (Operand.imm (.int 64 (BitVec.ofNat 64 2))),
    Instr.callVoid "llvm.lifetime.start.p0"
      [((Ty.int 64), (Operand.imm (.int 64 (BitVec.ofNat 64 8)))),
       (Ty.ptr, (Operand.reg "%outn"))],
    Instr.icmp "%cmp127.not" IPred.ult 64 (Operand.reg "%k.1") (Operand.reg "%nep") ]

/-- `key_body`'s instructions: the seven selections and the three after them. -/
def keyBodyInstrs : List Instr := keyBodyPhiInstrs ++ keyBodyRestInstrs

/-- `key_body`, pinned. -/
def keyBodyBlock : Block :=
  { name := "key_body", instrs := keyBodyInstrs,
    term := Term.condbr (Operand.reg "%cmp127.not") "if.end136" "if.then129" }

theorem keyBodyBlock_find :
    stage2NoEventBody.findBlock "key_body" = some keyBodyBlock := by
  decide

/-- The seven `phi` readings, in the block's order. -/
def keyBodyVs (p sp v alen arena terms1 toks1 : Nat) : List (String × Value) :=
  [("%p.0", .int 32 (BitVec.ofNat 32 p)),
   ("%sp.1", .int 32 (BitVec.ofNat 32 sp)),
   ("%k.1.in", .int 64 (BitVec.ofNat 64 v)),
   ("%alen.1", .int 64 (BitVec.ofNat 64 alen)),
   ("%arena.1", .int 64 (BitVec.ofNat 64 arena)),
   ("%terms.1", .int 64 (BitVec.ofNat 64 terms1)),
   ("%tokens.1", .int 64 (BitVec.ofNat 64 toks1))]

/-- The cell list `key_body` leaves, newest first. -/
def keyBodyCellList (p sp v alen arena terms1 toks1 : Nat) (nep : BitVec 64) :
    List (String × Value) :=
  [("%cmp127.not", .int 1 (evalICmp .ult (BitVec.ofNat 64 (v + 2)) nep)),
   ("%k.1", .int 64 (BitVec.ofNat 64 (v + 2))),
   ("%tokens.1", .int 64 (BitVec.ofNat 64 toks1)),
   ("%terms.1", .int 64 (BitVec.ofNat 64 terms1)),
   ("%arena.1", .int 64 (BitVec.ofNat 64 arena)),
   ("%alen.1", .int 64 (BitVec.ofNat 64 alen)),
   ("%k.1.in", .int 64 (BitVec.ofNat 64 v)),
   ("%sp.1", .int 32 (BitVec.ofNat 32 sp)),
   ("%p.0", .int 32 (BitVec.ofNat 32 p))]

/-- **`key_body`'s run** at the predecessor edge `pred`. -/
theorem keyBody_denote (calls : Calls) (env : Env) (s : State)
    {pred : String} {p sp v alen arena terms1 toks1 : Nat} {o : Nat}
    {nep : BitVec 64} {r : CallOutcome}
    (hpre : s.pre = some pred)
    (hsel : PhiSelects (stateAt env s) pred keyBodyPhiSpecs
      (keyBodyVs p sp v alen arena terms1 toks1))
    (houtn : lookupName env "%outn" = some (.ptr o))
    (hnep : lookupName env "%nep" = some (.int 64 nep))
    (hc : calls "llvm.lifetime.start.p0"
      [.int 64 (BitVec.ofNat 64 8), .ptr o] s.mem s.next = some r) :
    denoteCode calls keyBodyInstrs (stateAt env s) =
      some (stateAt (cells (keyBodyCellList p sp v alen arena terms1 toks1 nep) env)
        { s with mem := r.mem, next := r.next }) := by
  rw [show keyBodyInstrs = keyBodyPhiInstrs ++ keyBodyRestInstrs from rfl, keyBodyPhi_eq]
  rw [denoteCode_phiRun (s := stateAt env s) (p := pred) (specs := keyBodyPhiSpecs)
    (vs := keyBodyVs p sp v alen arena terms1 toks1)
    (rest := keyBodyRestInstrs) (hpre := hpre) (hsel := hsel) (hrest := rfl)]
  rw [stateAt_bindAll_runCells]
  rw [keyBodyRestInstrs]
  have hkin : lookupName (runCells (keyBodyVs p sp v alen arena terms1 toks1) env)
      "%k.1.in" = some (.int 64 (BitVec.ofNat 64 v)) := by
    rw [keyBodyVs]
    simp only [runCells]
    rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
      lookupName_cons_self]
  have houtnRun : lookupName (runCells (keyBodyVs p sp v alen arena terms1 toks1) env)
      "%outn" = some (.ptr o) := by
    rw [keyBodyVs]
    simp only [runCells]
    rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide), houtn]
  have hnepRun : lookupName (runCells (keyBodyVs p sp v alen arena terms1 toks1) env)
      "%nep" = some (.int 64 nep) := by
    rw [keyBodyVs]
    simp only [runCells]
    rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide), hnep]
  rw [denoteCode_add_imm (calls := calls)
    (env := runCells (keyBodyVs p sp v alen arena terms1 toks1) env) (s := s)
    (d := "%k.1") (a := "%k.1.in") (x := BitVec.ofNat 64 v) (c := BitVec.ofNat 64 2)
    (ha := hkin)]
  rw [stage2NoEventOfNatAdd]
  have hkin2 : lookupName (("%k.1", .int 64 (BitVec.ofNat 64 (v + 2))) ::
      runCells (keyBodyVs p sp v alen arena terms1 toks1) env) "%k.1" =
      some (.int 64 (BitVec.ofNat 64 (v + 2))) := by
    rw [lookupName_cons_self]
  have houtn2 : lookupName (("%k.1", .int 64 (BitVec.ofNat 64 (v + 2))) ::
      runCells (keyBodyVs p sp v alen arena terms1 toks1) env) "%outn" =
      some (.ptr o) := by
    rw [lookupName_cons_ne _ _ (by decide)]
    exact houtnRun
  have hnep2 : lookupName (("%k.1", .int 64 (BitVec.ofNat 64 (v + 2))) ::
      runCells (keyBodyVs p sp v alen arena terms1 toks1) env) "%nep" =
      some (.int 64 nep) := by
    rw [lookupName_cons_ne _ _ (by decide)]
    exact hnepRun
  rw [denoteCode_callVoid2 (calls := calls)
    (env := ("%k.1", .int 64 (BitVec.ofNat 64 (v + 2))) ::
      runCells (keyBodyVs p sp v alen arena terms1 toks1) env)
    (s := s) (callee := "llvm.lifetime.start.p0") (c := BitVec.ofNat 64 8)
    (o2 := .reg "%outn") (v2 := .ptr o) (r := r)
    (by simp only [stateAt, evalOperand, houtn2])
    hc]
  rw [denoteCode_icmp_ult_reg (calls := calls)
    (env := ("%k.1", .int 64 (BitVec.ofNat 64 (v + 2))) ::
      runCells (keyBodyVs p sp v alen arena terms1 toks1) env) (s := _)
    (d := "%cmp127.not") (a := "%k.1") (b := "%nep")
    (x := BitVec.ofNat 64 (v + 2)) (y := nep)
    (ha := hkin2)
    (hb := hnep2)]
  simp only [keyBodyCellList, keyBodyVs, cells, runCells, denoteCode_nil]

/-- **`key_body` at the closing quote inside the stream**: the true arm, to
`if.end136`.  The lifetime marker's call is the caller's outcome, and it leaves
memory and cursor unchanged. -/
theorem link_keyBody_true {calls : Calls} {K : Stage2NoEventWalkCarry} {mem : Mem}
    {s : State} {pred : String} {p sp v alen arena terms1 toks1 : Nat} {o : Nat}
    {nep : BitVec 64} {r : CallOutcome}
    (h : Stage2NoEventWalkInv K mem s) (hpc : s.pc = "key_body")
    (hpre : s.pre = some pred)
    (hsel : PhiSelects (stateAt s.env s) pred keyBodyPhiSpecs
      (keyBodyVs p sp v alen arena terms1 toks1))
    (houtn : lookupName s.env "%outn" = some (.ptr o))
    (hnep : lookupName s.env "%nep" = some (.int 64 nep))
    (hc : calls "llvm.lifetime.start.p0"
      [.int 64 (BitVec.ofNat 64 8), .ptr o] s.mem s.next = some r)
    (hmem : r.mem = s.mem) (hnext : r.next = s.next)
    (hy : evalICmp .ult (BitVec.ofNat 64 (v + 2)) nep = 1) :
    Stage2NoEventWalkLink calls K mem s K
      (stage2NoEventWalkNext
        (cells (keyBodyCellList p sp v alen arena terms1 toks1 nep) s.env)
        s "if.end136") := by
  have hblock : keyBodyBlock.instrs = keyBodyInstrs := rfl
  have hcode : denoteCode calls keyBodyBlock.instrs (stateAt s.env s) =
      some (stateAt (cells (keyBodyCellList p sp v alen arena terms1 toks1 nep) s.env)
        { s with mem := r.mem, next := r.next }) := by
    rw [hblock]
    exact keyBody_denote (calls := calls) s.env s hpre hsel houtn hnep hc
  refine ⟨h, ?_, Stage2NoEventWalkInv.mem_congr h rfl⟩
  have hcmp : lookupName (cells (keyBodyCellList p sp v alen arena terms1 toks1 nep) s.env)
      "%cmp127.not" = some (.int 1 1) := by
    simp only [keyBodyCellList, cells]
    rw [lookupName_cons_self, hy]
  have hstep := stage2NoEventWalk_step_condbr_true (f := stage2NoEventBody)
    (by simp only [stateAt]; rw [hpc]; exact keyBodyBlock_find) hcode rfl
    (by simpa only [stateAt] using hcmp)
  simpa only [stage2NoEventWalkNext, stateAt, hmem, hnext] using hstep

/-! ### `if.end136` -/

/-- `if.end136`'s seven instructions. -/
def ifEnd136Instrs : List Instr :=
  [ Instr.binop "%inc137" BinOp.add 64 (Operand.reg "%k.1.in")
      (Operand.imm (.int 64 (BitVec.ofNat 64 3))),
    Instr.gep "%arrayidx138" (Ty.int 32) (Operand.reg "%ep") (Operand.reg "%k.1"),
    Instr.load "%14" (Ty.int 32) (Operand.reg "%arrayidx138"),
    Instr.store (Ty.int 64) (Operand.reg "%inc137") (Operand.reg "%k219"),
    Instr.zext "%conv140" 32 64 (Operand.reg "%14"),
    Instr.icmp "%cmp141.not" IPred.ugt 64 (Operand.reg "%n")
      (Operand.reg "%conv140"),
    Instr.zext "%conv152" 32 64 (Operand.reg "%p.0") ]

/-- `if.end136`, pinned. -/
def ifEnd136Block : Block :=
  { name := "if.end136", instrs := ifEnd136Instrs,
    term := Term.condbr (Operand.reg "%cmp141.not") "if.end150" "if.then143" }

theorem ifEnd136Block_find :
    stage2NoEventBody.findBlock "if.end136" = some ifEnd136Block := by
  decide

/-- The cells `if.end136` binds, newest first. -/
def ifEnd136CellList (ep v p k1 close : Nat) (n : BitVec 64) :
    List (String × Value) :=
  [("%conv152", .int 64 (BitVec.ofNat 64 (BitVec.ofNat 32 p).toNat)),
   ("%cmp141.not", .int 1 (evalICmp .ugt n (BitVec.ofNat 64 close))),
   ("%conv140", .int 64 (BitVec.ofNat 64 close)),
   ("%14", .int 32 (BitVec.ofNat 32 close)),
   ("%arrayidx138", .ptr (ep + 4 * k1)),
   ("%inc137", .int 64 (BitVec.ofNat 64 (v + 3)))]

/-- **`if.end136`'s run**. -/
theorem ifEnd136_denote (calls : Calls) (env : Env) (s : State)
    {ep : Nat} {v p k1 close : Nat} {a : Nat} {bs4 : List UInt8} {n : BitVec 64}
    (hv : lookupName env "%k.1.in" = some (.int 64 (BitVec.ofNat 64 v)))
    (hk1 : lookupName env "%k.1" = some (.int 64 (BitVec.ofNat 64 k1)))
    (hk1Addr : k1 < 2 ^ 63)
    (hep : lookupName env "%ep" = some (.ptr ep))
    (hopen : lookupName env "%p.0" = some (.int 32 (BitVec.ofNat 32 p)))
    (hk219 : lookupName env "%k219" = some (.ptr a))
    (hn : lookupName env "%n" = some (.int 64 n))
    (hbs4 : bytesToNat bs4 = close) (hcloseLt : close < 2 ^ 32)
    (hlane : readBytes s.mem (ep + 4 * k1) 4 = some bs4) :
    denoteCode calls ifEnd136Instrs (stateAt env s) =
      some (stateAt (cells (ifEnd136CellList ep v p k1 close n) env)
        { env := s.env, mem := writeBytes s.mem a (natToBytes (BitVec.ofNat 64 (v + 3)).toNat 8), next := s.next, pc := s.pc, pre := s.pre }) := by
  rw [ifEnd136Instrs]
  rw [denoteCode_add_imm (calls := calls) (env := env) (s := s)
    (d := "%inc137") (a := "%k.1.in") (x := BitVec.ofNat 64 v)
    (c := BitVec.ofNat 64 3) hv]
  rw [stage2NoEventOfNatAdd]
  rw [stage2NoEventWalk_denote_gep32 (calls := calls)
    (env := ("%inc137", .int 64 (BitVec.ofNat 64 (v + 3))) :: env) (s := s)
    (d := "%arrayidx138") (base := "%ep") (off := "%k.1")
    (a := ep) (o := BitVec.ofNat 64 k1) (hb := hep) (ho := hk1)
    (hs := by
      rw [stage2NoEventSignExtend_ofNat hk1Addr]
      exact hk1Addr)]
  rw [show ep + ((BitVec.ofNat 64 k1).signExtend 64).toNat * 4 = ep + 4 * k1
    from by rw [stage2NoEventSignExtend_ofNat hk1Addr, Nat.mul_comm]]
  rw [stage2NoEventWalk_denote_load_int (calls := calls)
    (env := ("%arrayidx138", .ptr (ep + 4 * k1)) ::
      ("%inc137", .int 64 (BitVec.ofNat 64 (v + 3))) :: env) (s := s)
    (d := "%14") (p := "%arrayidx138") (w := 32) (a := ep + 4 * k1) (bs := bs4)
    (hw := by decide) (hp := by simp only [lookupName_cons_self]) (hv := hlane)]
  rw [hbs4]
  rw [denoteCode_store64 (calls := calls)
    (env := ("%14", .int 32 (BitVec.ofNat 32 close)) ::
      ("%arrayidx138", .ptr (ep + 4 * k1)) ::
      ("%inc137", .int 64 (BitVec.ofNat 64 (v + 3))) :: env) (s := s)
    (v := "%inc137") (p := "%k219") (x := BitVec.ofNat 64 (v + 3)) (a := a)
    (by rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
      lookupName_cons_self])
    (by rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide), hk219])]
  rw [denoteCode_zext (calls := calls)
    (env := ("%14", .int 32 (BitVec.ofNat 32 close)) ::
      ("%arrayidx138", .ptr (ep + 4 * k1)) ::
      ("%inc137", .int 64 (BitVec.ofNat 64 (v + 3))) :: env) (s := { env := s.env, mem := writeBytes s.mem a (natToBytes (BitVec.ofNat 64 (v + 3)).toNat 8), next := s.next, pc := s.pc, pre := s.pre })
    (d := "%conv140") (v := "%14") (wIn := 32) (wOut := 64)
    (x := BitVec.ofNat 32 close) (hv := by simp only [lookupName_cons_self])]
  rw [stage2NoEventOfNat32_toNat hcloseLt]
  rw [stage2NoEventWalk_denote_icmp_reg (calls := calls)
    (env := ("%conv140", .int 64 (BitVec.ofNat 64 close)) ::
      ("%14", .int 32 (BitVec.ofNat 32 close)) ::
      ("%arrayidx138", .ptr (ep + 4 * k1)) ::
      ("%inc137", .int 64 (BitVec.ofNat 64 (v + 3))) :: env) (s := { env := s.env, mem := writeBytes s.mem a (natToBytes (BitVec.ofNat 64 (v + 3)).toNat 8), next := s.next, pc := s.pc, pre := s.pre })
    (d := "%cmp141.not") (a := "%n") (b := "%conv140") (p := .ugt) (w := 64)
    (x := n) (y := BitVec.ofNat 64 close)
    (ha := by rw [lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide), hn])
    (hb := by simp only [lookupName_cons_self])
    (is := [Instr.zext "%conv152" 32 64 (Operand.reg "%p.0")])]
  rw [denoteCode_zext (calls := calls)
    (env := ("%cmp141.not", .int 1 (evalICmp .ugt n (BitVec.ofNat 64 close))) ::
      ("%conv140", .int 64 (BitVec.ofNat 64 close)) ::
      ("%14", .int 32 (BitVec.ofNat 32 close)) ::
      ("%arrayidx138", .ptr (ep + 4 * k1)) ::
      ("%inc137", .int 64 (BitVec.ofNat 64 (v + 3))) :: env) (s := { env := s.env, mem := writeBytes s.mem a (natToBytes (BitVec.ofNat 64 (v + 3)).toNat 8), next := s.next, pc := s.pc, pre := s.pre })
    (d := "%conv152") (v := "%p.0") (wIn := 32) (wOut := 64)
    (x := BitVec.ofNat 32 p)
    (hv := by rw [lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
      hopen])]
  simp only [ifEnd136CellList, cells, denoteCode_nil]

/-- **`if.end136` at an offset inside the document**: the true arm, to
`if.end150`.  The `%k219` store is inside the cursor record's region. -/
theorem link_ifEnd136_true {calls : Calls} {K : Stage2NoEventWalkCarry} {mem : Mem}
    {s : State} {ep : Nat} {v p k1 close : Nat} {a : Nat} {bs4 : List UInt8}
    {n : BitVec 64}
    (h : Stage2NoEventWalkInv K mem s) (hpc : s.pc = "if.end136")
    (hv : lookupName s.env "%k.1.in" = some (.int 64 (BitVec.ofNat 64 v)))
    (hk1 : lookupName s.env "%k.1" = some (.int 64 (BitVec.ofNat 64 k1)))
    (hk1Addr : k1 < 2 ^ 63)
    (hep : lookupName s.env "%ep" = some (.ptr ep))
    (hopen : lookupName s.env "%p.0" = some (.int 32 (BitVec.ofNat 32 p)))
    (hk219 : lookupName s.env "%k219" = some (.ptr a))
    (hn : lookupName s.env "%n" = some (.int 64 n))
    (hbs4 : bytesToNat bs4 = close) (hcloseLt : close < 2 ^ 32)
    (hlane : readBytes s.mem (ep + 4 * k1) 4 = some bs4)
    (hw : ∀ j, j < (natToBytes (BitVec.ofNat 64 (v + 3)).toNat 8).length →
      inRegions (stage2NoEventRunRegions K.scratch K.scratchcap K.stk K.e K.c K.d ++
        [(K.next0, K.nextEnd - K.next0)]) (a + j))
    (hy : evalICmp .ugt n (BitVec.ofNat 64 close) = 1) :
    Stage2NoEventWalkLink calls K mem s K
      (stage2NoEventWalkStored (cells (ifEnd136CellList ep v p k1 close n) s.env) s
        (writeBytes s.mem a (natToBytes (BitVec.ofNat 64 (v + 3)).toNat 8))
        "if.end150") := by
  have hcode : denoteCode calls ifEnd136Instrs (stateAt s.env s) =
      some (stateAt (cells (ifEnd136CellList ep v p k1 close n) s.env)
        { env := s.env, mem := writeBytes s.mem a (natToBytes (BitVec.ofNat 64 (v + 3)).toNat 8), next := s.next, pc := s.pc, pre := s.pre }) :=
    ifEnd136_denote (calls := calls) s.env s hv hk1 hk1Addr hep hopen hk219 hn hbs4
      hcloseLt hlane
  refine ⟨h, ?_, Stage2NoEventWalkInv.mem_congr
    (Stage2NoEventWalkInv.stack_write h hw) rfl⟩
  have hblock : ifEnd136Block.instrs = ifEnd136Instrs := rfl
  have hcode' : denoteCode calls ifEnd136Block.instrs (stateAt s.env s) =
      some (stateAt (cells (ifEnd136CellList ep v p k1 close n) s.env)
        { env := s.env, mem := writeBytes s.mem a (natToBytes (BitVec.ofNat 64 (v + 3)).toNat 8), next := s.next, pc := s.pc, pre := s.pre }) := by
    rw [hblock]; exact hcode
  have hstep := stage2NoEventWalk_step_condbr_true (f := stage2NoEventBody)
    (by simp only [stateAt]; rw [hpc]; exact ifEnd136Block_find) hcode' rfl
    (by show lookupName (cells (ifEnd136CellList ep v p k1 close n) s.env)
          "%cmp141.not" = some (.int 1 1)
        simp only [ifEnd136CellList, cells]
        rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_self, hy])
  simpa only [stage2NoEventWalkStored, stateAt] using hstep

/-! ### `if.end150` -/

/-- `if.end150`'s four instructions. -/
def ifEnd150Instrs : List Instr :=
  [ Instr.binop "%15" BinOp.xor 64 (Operand.reg "%conv152")
      (Operand.imm (.int 64 (BitVec.ofNat 64 18446744073709551615))),
    Instr.binop "%sub154" BinOp.add 64 (Operand.reg "%conv140") (Operand.reg "%15"),
    Instr.binop "%add155" BinOp.add 64 (Operand.reg "%sub154")
      (Operand.imm (.int 64 (BitVec.ofNat 64 64))),
    Instr.icmp "%cmp156" IPred.ugt 64 (Operand.reg "%add155")
      (Operand.reg "%scratchcap") ]

/-- `if.end150`, pinned. -/
def ifEnd150Block : Block :=
  { name := "if.end150", instrs := ifEnd150Instrs,
    term := Term.condbr (Operand.reg "%cmp156") "if.then158" "if.end159" }

theorem ifEnd150Block_find :
    stage2NoEventBody.findBlock "if.end150" = some ifEnd150Block := by
  decide

/-- The cells `if.end150` binds, newest first. -/
def ifEnd150CellList (opn close : Nat) (sc : BitVec 64) : List (String × Value) :=
  [("%cmp156", .int 1 (evalICmp .ugt
      (BitVec.ofNat 64 close +
        (BitVec.ofNat 64 (BitVec.ofNat 32 opn).toNat ^^^
          BitVec.ofNat 64 18446744073709551615) + BitVec.ofNat 64 64) sc)),
   ("%add155", .int 64 (BitVec.ofNat 64 close +
      (BitVec.ofNat 64 (BitVec.ofNat 32 opn).toNat ^^^
        BitVec.ofNat 64 18446744073709551615) + BitVec.ofNat 64 64)),
   ("%sub154", .int 64 (BitVec.ofNat 64 close +
      (BitVec.ofNat 64 (BitVec.ofNat 32 opn).toNat ^^^
        BitVec.ofNat 64 18446744073709551615))),
   ("%15", .int 64 (BitVec.ofNat 64 (BitVec.ofNat 32 opn).toNat ^^^
      BitVec.ofNat 64 18446744073709551615))]

/-- **`if.end150`'s run**. -/
theorem ifEnd150_denote (calls : Calls) (env : Env) (s : State)
    {opn close : Nat} {sc : BitVec 64}
    (hopen : lookupName env "%conv152" =
      some (.int 64 (BitVec.ofNat 64 (BitVec.ofNat 32 opn).toNat)))
    (hclose : lookupName env "%conv140" = some (.int 64 (BitVec.ofNat 64 close)))
    (hsc : lookupName env "%scratchcap" = some (.int 64 sc)) :
    denoteCode calls ifEnd150Instrs (stateAt env s) =
      some (stateAt (cells (ifEnd150CellList opn close sc) env) s) := by
  rw [ifEnd150Instrs]
  rw [denoteCode_xor_imm (calls := calls) (env := env) (s := s)
    (d := "%15") (a := "%conv152")
    (x := BitVec.ofNat 64 (BitVec.ofNat 32 opn).toNat)
    (c := BitVec.ofNat 64 18446744073709551615) (ha := hopen)]
  rw [denoteCode_add_reg (calls := calls)
    (env := ("%15", .int 64 (BitVec.ofNat 64 (BitVec.ofNat 32 opn).toNat ^^^
      BitVec.ofNat 64 18446744073709551615)) :: env) (s := s)
    (d := "%sub154") (a := "%conv140") (b := "%15")
    (x := BitVec.ofNat 64 close)
    (y := BitVec.ofNat 64 (BitVec.ofNat 32 opn).toNat ^^^
      BitVec.ofNat 64 18446744073709551615)
    (ha := by rw [lookupName_cons_ne _ _ (by decide)]; exact hclose)
    (hb := by simp only [lookupName_cons_self])]
  rw [denoteCode_add_imm (calls := calls)
    (env := ("%sub154", .int 64 (BitVec.ofNat 64 close +
        (BitVec.ofNat 64 (BitVec.ofNat 32 opn).toNat ^^^
          BitVec.ofNat 64 18446744073709551615))) ::
      ("%15", .int 64 (BitVec.ofNat 64 (BitVec.ofNat 32 opn).toNat ^^^
        BitVec.ofNat 64 18446744073709551615)) :: env) (s := s)
    (d := "%add155") (a := "%sub154")
    (x := BitVec.ofNat 64 close +
      (BitVec.ofNat 64 (BitVec.ofNat 32 opn).toNat ^^^
        BitVec.ofNat 64 18446744073709551615))
    (c := BitVec.ofNat 64 64) (ha := by simp only [lookupName_cons_self])]
  rw [stage2NoEventWalk_denote_icmp_reg (calls := calls)
    (env := ("%add155", .int 64 (BitVec.ofNat 64 close +
        (BitVec.ofNat 64 (BitVec.ofNat 32 opn).toNat ^^^
          BitVec.ofNat 64 18446744073709551615) + BitVec.ofNat 64 64)) ::
      ("%sub154", .int 64 (BitVec.ofNat 64 close +
        (BitVec.ofNat 64 (BitVec.ofNat 32 opn).toNat ^^^
          BitVec.ofNat 64 18446744073709551615))) ::
      ("%15", .int 64 (BitVec.ofNat 64 (BitVec.ofNat 32 opn).toNat ^^^
        BitVec.ofNat 64 18446744073709551615)) :: env) (s := s)
    (d := "%cmp156") (a := "%add155") (b := "%scratchcap") (p := .ugt) (w := 64)
    (x := BitVec.ofNat 64 close +
      (BitVec.ofNat 64 (BitVec.ofNat 32 opn).toNat ^^^
        BitVec.ofNat 64 18446744073709551615) + BitVec.ofNat 64 64) (y := sc)
    (ha := by simp only [lookupName_cons_self])
    (hb := by rw [lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide), hsc])]
  simp only [ifEnd150CellList, cells, denoteCode_nil]

/-- **`if.end150` at a body the scratch holds**: the false arm, to `if.end159`. -/
theorem link_ifEnd150_false {calls : Calls} {K : Stage2NoEventWalkCarry} {mem : Mem}
    {s : State} {opn close : Nat} {sc : BitVec 64}
    (h : Stage2NoEventWalkInv K mem s) (hpc : s.pc = "if.end150")
    (hopen : lookupName s.env "%conv152" =
      some (.int 64 (BitVec.ofNat 64 (BitVec.ofNat 32 opn).toNat)))
    (hclose : lookupName s.env "%conv140" = some (.int 64 (BitVec.ofNat 64 close)))
    (hsc : lookupName s.env "%scratchcap" = some (.int 64 sc))
    (hy : evalICmp .ugt
      (BitVec.ofNat 64 close +
        (BitVec.ofNat 64 (BitVec.ofNat 32 opn).toNat ^^^
          BitVec.ofNat 64 18446744073709551615) + BitVec.ofNat 64 64) sc = 0) :
    Stage2NoEventWalkLink calls K mem s K
      (stage2NoEventWalkNext (cells (ifEnd150CellList opn close sc) s.env)
        s "if.end159") := by
  have hcode : denoteCode calls ifEnd150Instrs (stateAt s.env s) =
      some (stateAt (cells (ifEnd150CellList opn close sc) s.env) s) :=
    ifEnd150_denote (calls := calls) s.env s hopen hclose hsc
  refine stage2NoEventWalkLink_condbr_false
    (env' := cells (ifEnd150CellList opn close sc) s.env)
    h (by rw [hpc]; exact ifEnd150Block_find) hcode rfl ?_
  simp only [ifEnd150CellList, cells, lookupName_cons_self, hy]

/-! ### `if.end159`: the key scanner's call

The block clears the staging word, forms the callee's cursor at `%b + 1 + p`
(`%invariant.gep` is the entry block's `%b + 1`), and calls `@s2_string_body`
with the eight arguments the emitted call passes.  Its answer and the memory it
leaves are the selection's `CallOutcome`; the invariant at the result state is
the route's own premise (`callInv`), because the callee's writes are outside the
run's frame. -/

/-- `if.end159`'s three instructions. -/
def ifEnd159Instrs : List Instr :=
  [ Instr.store (Ty.int 64) (Operand.imm (.int 64 (BitVec.ofNat 64 0)))
      (Operand.reg "%outn"),
    Instr.gep "%gep1071" (Ty.int 8) (Operand.reg "%invariant.gep")
      (Operand.reg "%conv152"),
    Instr.call "%call161" (Ty.int 32) "s2_string_body"
      [(Ty.ptr, (Operand.reg "%c")), (Ty.ptr, (Operand.reg "%gep1071")),
       ((Ty.int 64), (Operand.reg "%sub154")), (Ty.ptr, (Operand.reg "%scratch")),
       (Ty.ptr, (Operand.reg "%outn")), (Ty.ptr, (Operand.reg "%xp")),
       (Ty.ptr, (Operand.reg "%xj")), ((Ty.int 64), (Operand.reg "%nxp"))] ]

/-- `if.end159`, pinned. -/
def ifEnd159Block : Block :=
  { name := "if.end159", instrs := ifEnd159Instrs, term := Term.br "NodeBlock25" }

theorem ifEnd159Block_find :
    stage2NoEventBody.findBlock "if.end159" = some ifEnd159Block := by
  decide

/-- The env `if.end159` leaves: the callee's cursor and its result. -/
def ifEnd159Cells (env : Env) (g : Nat) (idx : BitVec 64) (r : CallOutcome) : Env :=
  ("%call161", r.ret) :: ("%gep1071", .ptr (g + (idx.signExtend 64).toNat)) :: env

/-- **`if.end159`'s run at the selection's answer for `s2_string_body`**: the
zero store at `%outn`, the callee's cursor, the eight-argument call, and its
`CallOutcome`. -/
theorem ifEnd159_denote (calls : Calls) (env : Env) (s : State)
    {g outn c scratch xp xj : Nat} {idx sub nxp : BitVec 64} {r : CallOutcome}
    (houtn : lookupName env "%outn" = some (.ptr outn))
    (hg : lookupName env "%invariant.gep" = some (.ptr g))
    (hidx : lookupName env "%conv152" = some (.int 64 idx))
    (hpos : (idx.signExtend 64).toNat < 2 ^ 63)
    (hsub : lookupName env "%sub154" = some (.int 64 sub))
    (hcP : lookupName env "%c" = some (.ptr c))
    (hsc : lookupName env "%scratch" = some (.ptr scratch))
    (hxp : lookupName env "%xp" = some (.ptr xp))
    (hxj : lookupName env "%xj" = some (.ptr xj))
    (hnxp : lookupName env "%nxp" = some (.int 64 nxp))
    (hc : calls "s2_string_body"
      [.ptr c, .ptr (g + (idx.signExtend 64).toNat), .int 64 sub, .ptr scratch,
       .ptr outn, .ptr xp, .ptr xj, .int 64 nxp]
      (writeBytes s.mem outn (natToBytes 0 8)) s.next = some r) :
    denoteCode calls ifEnd159Instrs (stateAt env s) =
      some (stateAt (ifEnd159Cells env g idx r)
        { s with mem := r.mem, next := r.next }) := by
  unfold ifEnd159Instrs
  rw [stage2NoEventWalk_denote_store64_imm (calls := calls) (env := env) (s := s)
    (x := BitVec.ofNat 64 0) (p := "%outn") houtn]
  simp only [BitVec.toNat_ofNat, Nat.zero_mod]
  rw [denoteCode_gep8_reg (calls := calls) (env := env) (s := _)
    (d := "%gep1071") (base := "%invariant.gep") (off := "%conv152")
    (a := g) (idx := idx) hg hidx hpos]
  rw [denoteCode_call8 (calls := calls)
    (env := ("%gep1071", .ptr (g + (idx.signExtend 64).toNat)) :: env) (s := _)
    (d := "%call161") (callee := "s2_string_body")
    (o1 := .reg "%c") (o2 := .reg "%gep1071") (o3 := .reg "%sub154")
    (o4 := .reg "%scratch") (o5 := .reg "%outn") (o6 := .reg "%xp")
    (o7 := .reg "%xj") (o8 := .reg "%nxp")
    (v1 := .ptr c) (v2 := .ptr (g + (idx.signExtend 64).toNat)) (v3 := .int 64 sub)
    (v4 := .ptr scratch) (v5 := .ptr outn) (v6 := .ptr xp) (v7 := .ptr xj)
    (v8 := .int 64 nxp) (r := r) (is := [])
    (by simp only [stateAt, evalOperand]; rw [lookupName_cons_ne _ _ (by decide)];
        simp only [hcP])
    (by simp only [stateAt, evalOperand, lookupName_cons_self])
    (by simp only [stateAt, evalOperand]; rw [lookupName_cons_ne _ _ (by decide)];
        simp only [hsub])
    (by simp only [stateAt, evalOperand]; rw [lookupName_cons_ne _ _ (by decide)];
        simp only [hsc])
    (by simp only [stateAt, evalOperand]; rw [lookupName_cons_ne _ _ (by decide)];
        simp only [houtn])
    (by simp only [stateAt, evalOperand]; rw [lookupName_cons_ne _ _ (by decide)];
        simp only [hxp])
    (by simp only [stateAt, evalOperand]; rw [lookupName_cons_ne _ _ (by decide)];
        simp only [hxj])
    (by simp only [stateAt, evalOperand]; rw [lookupName_cons_ne _ _ (by decide)];
        simp only [hnxp])
    hc]
  simp only [denoteCode_nil, ifEnd159Cells]

/-- **`if.end159` at the selection's answer**: the control step to `NodeBlock25`,
the callee's memory and cursor, and the invariant the caller supplies at the
result. -/
theorem link_ifEnd159 {calls : Calls} {K : Stage2NoEventWalkCarry} {mem : Mem}
    {s : State} {g outn c scratch xp xj : Nat} {idx sub nxp : BitVec 64}
    {r : CallOutcome}
    (h : Stage2NoEventWalkInv K mem s) (hpc : s.pc = "if.end159")
    (houtn : lookupName s.env "%outn" = some (.ptr outn))
    (hg : lookupName s.env "%invariant.gep" = some (.ptr g))
    (hidx : lookupName s.env "%conv152" = some (.int 64 idx))
    (hpos : (idx.signExtend 64).toNat < 2 ^ 63)
    (hsub : lookupName s.env "%sub154" = some (.int 64 sub))
    (hcP : lookupName s.env "%c" = some (.ptr c))
    (hsc : lookupName s.env "%scratch" = some (.ptr scratch))
    (hxp : lookupName s.env "%xp" = some (.ptr xp))
    (hxj : lookupName s.env "%xj" = some (.ptr xj))
    (hnxp : lookupName s.env "%nxp" = some (.int 64 nxp))
    (hc : calls "s2_string_body"
      [.ptr c, .ptr (g + (idx.signExtend 64).toNat), .int 64 sub, .ptr scratch,
       .ptr outn, .ptr xp, .ptr xj, .int 64 nxp]
      (writeBytes s.mem outn (natToBytes 0 8)) s.next = some r)
    (hinv : Stage2NoEventWalkInv K mem { s with mem := r.mem, next := r.next }) :
    Stage2NoEventWalkLink calls K mem s K
      (stage2NoEventWalkNext (ifEnd159Cells s.env g idx r)
        { s with mem := r.mem, next := r.next } "NodeBlock25") := by
  have hcode := ifEnd159_denote (calls := calls) (env := s.env) (s := s) houtn hg
    hidx hpos hsub hcP hsc hxp hxj hnxp hc
  refine ⟨h, ?_, ?_⟩
  · have hstep := stage2NoEventWalk_step_br (f := stage2NoEventBody)
      (by rw [hpc]; exact ifEnd159Block_find) hcode rfl
    exact hstep
  · exact Stage2NoEventWalkInv.mem_congr hinv rfl

/-! ### The result's dispatch: `NodeBlock25` and `LeafBlock23`

`NodeBlock25` compares the answer with one (`slt`), and `LeafBlock23` tests the
equality: the escape-free key is the answer `1`, which this route takes. -/

/-- `NodeBlock25`: the result against one. -/
def nodeBlock25Instrs : List Instr :=
  [ Instr.icmp "%Pivot26" IPred.slt 32 (Operand.reg "%call161")
      (Operand.imm (.int 32 (BitVec.ofNat 32 1))) ]

/-- `NodeBlock25`, pinned. -/
def nodeBlock25Block : Block :=
  { name := "NodeBlock25", instrs := nodeBlock25Instrs,
    term := Term.condbr (Operand.reg "%Pivot26") "do.body164" "LeafBlock23" }

theorem nodeBlock25Block_find :
    stage2NoEventBody.findBlock "NodeBlock25" = some nodeBlock25Block := by
  decide

/-- **`NodeBlock25`'s run** at the call's answer. -/
theorem nodeBlock25_denote (calls : Calls) (env : Env) (s : State)
    {x : BitVec 32}
    (hcall : lookupName env "%call161" = some (.int 32 x)) :
    denoteCode calls nodeBlock25Instrs (stateAt env s) =
      some (stateAt (("%Pivot26",
        .int 1 (evalICmp .slt x (BitVec.ofNat 32 1))) :: env) s) := by
  rw [nodeBlock25Instrs, stage2NoEventWalk_denote_icmp_imm (calls := calls)
    (env := env) (s := s) (d := "%Pivot26") (a := "%call161") (p := .slt) (w := 32)
    (c := BitVec.ofNat 32 1) hcall (is := [])]
  simp only [denoteCode_nil]

/-- **`NodeBlock25` at the escape-free answer**: `slt 1 1` is zero, so the block
falls to `LeafBlock23`. -/
theorem link_nodeBlock25_false {calls : Calls} {K : Stage2NoEventWalkCarry}
    {mem : Mem} {s : State}
    (h : Stage2NoEventWalkInv K mem s) (hpc : s.pc = "NodeBlock25")
    (hcall : lookupName s.env "%call161" = some (.int 32 (BitVec.ofNat 32 1))) :
    Stage2NoEventWalkLink calls K mem s K
      (stage2NoEventWalkNext
        (("%Pivot26", .int 1 (evalICmp .slt (BitVec.ofNat 32 1)
          (BitVec.ofNat 32 1))) :: s.env) s "LeafBlock23") := by
  have hcode : denoteCode calls nodeBlock25Block.instrs (stateAt s.env s) =
      some (stateAt (("%Pivot26", .int 1 (evalICmp .slt (BitVec.ofNat 32 1)
        (BitVec.ofNat 32 1))) :: s.env) s) := by
    rw [show nodeBlock25Block.instrs = nodeBlock25Instrs from rfl]
    exact nodeBlock25_denote (calls := calls) s.env s hcall
  refine ⟨h, ?_, Stage2NoEventWalkInv.mem_congr h rfl⟩
  have hstep := stage2NoEventWalk_step_condbr_false (f := stage2NoEventBody)
    (by simp only [stateAt]; rw [hpc]; exact nodeBlock25Block_find) hcode rfl
    (by
      have hy : evalICmp .slt (BitVec.ofNat 32 1) (BitVec.ofNat 32 1) = 0 := by
        decide
      simp only [stateAt, lookupName_cons_self, hy])
  simpa only [stage2NoEventWalkNext, stateAt] using hstep

/-- `LeafBlock23`: the result against one, the escape-free arm's own test. -/
def leafBlock23Instrs : List Instr :=
  [ Instr.icmp "%SwitchLeaf24" IPred.eq 32 (Operand.reg "%call161")
      (Operand.imm (.int 32 (BitVec.ofNat 32 1))) ]

/-- `LeafBlock23`, pinned. -/
def leafBlock23Block : Block :=
  { name := "LeafBlock23", instrs := leafBlock23Instrs,
    term := Term.condbr (Operand.reg "%SwitchLeaf24") "do.body172"
      "for.cond.preheader" }

theorem leafBlock23Block_find :
    stage2NoEventBody.findBlock "LeafBlock23" = some leafBlock23Block := by
  decide

/-- **`LeafBlock23`'s run** at the call's answer. -/
theorem leafBlock23_denote (calls : Calls) (env : Env) (s : State)
    {x : BitVec 32}
    (hcall : lookupName env "%call161" = some (.int 32 x)) :
    denoteCode calls leafBlock23Instrs (stateAt env s) =
      some (stateAt (("%SwitchLeaf24",
        .int 1 (evalICmp .eq x (BitVec.ofNat 32 1))) :: env) s) := by
  rw [leafBlock23Instrs, stage2NoEventWalk_denote_icmp_imm (calls := calls)
    (env := env) (s := s) (d := "%SwitchLeaf24") (a := "%call161") (p := .eq)
    (w := 32) (c := BitVec.ofNat 32 1) hcall (is := [])]
  simp only [denoteCode_nil]

/-- **`LeafBlock23` at the escape-free answer**: `eq 1 1` is one, so the block
takes `do.body172`. -/
theorem link_leafBlock23_true {calls : Calls} {K : Stage2NoEventWalkCarry}
    {mem : Mem} {s : State}
    (h : Stage2NoEventWalkInv K mem s) (hpc : s.pc = "LeafBlock23")
    (hcall : lookupName s.env "%call161" = some (.int 32 (BitVec.ofNat 32 1))) :
    Stage2NoEventWalkLink calls K mem s K
      (stage2NoEventWalkNext
        (("%SwitchLeaf24", .int 1 (evalICmp .eq (BitVec.ofNat 32 1)
          (BitVec.ofNat 32 1))) :: s.env) s "do.body172") := by
  have hcode : denoteCode calls leafBlock23Block.instrs (stateAt s.env s) =
      some (stateAt (("%SwitchLeaf24", .int 1 (evalICmp .eq (BitVec.ofNat 32 1)
        (BitVec.ofNat 32 1))) :: s.env) s) := by
    rw [show leafBlock23Block.instrs = leafBlock23Instrs from rfl]
    exact leafBlock23_denote (calls := calls) s.env s hcall
  refine ⟨h, ?_, Stage2NoEventWalkInv.mem_congr h rfl⟩
  have hstep := stage2NoEventWalk_step_condbr_true (f := stage2NoEventBody)
    (by simp only [stateAt]; rw [hpc]; exact leafBlock23Block_find) hcode rfl
    (by
      have hy : evalICmp .eq (BitVec.ofNat 32 1) (BitVec.ofNat 32 1) = 1 := by
        decide
      simp only [stateAt, lookupName_cons_self, hy])
  simpa only [stage2NoEventWalkNext, stateAt] using hstep

/-! ### `do.body172`: the escape-free key's record field

The plain arm advances the key's position (`%add175 = %p.0 + 1`), sign-sets it
with the arena tag's word (`%or`), and adds the key's length (`%add177`).  The
`%or` instruction is an `add` in the body, so its word is the sum's. -/

/-- `do.body172`'s four instructions. -/
def doBody172Instrs : List Instr :=
  [ Instr.binop "%add175" BinOp.add 32 (Operand.reg "%p.0")
      (Operand.imm (.int 32 (BitVec.ofNat 32 1))),
    Instr.zext "%conv176" 32 64 (Operand.reg "%add175"),
    Instr.binop "%or" BinOp.add 64 (Operand.reg "%conv176")
      (Operand.imm (.int 64 (BitVec.ofNat 64 9223372036854775813))),
    Instr.binop "%add177" BinOp.add 64 (Operand.reg "%or")
      (Operand.reg "%sub154") ]

/-- `do.body172`, pinned. -/
def doBody172Block : Block :=
  { name := "do.body172", instrs := doBody172Instrs, term := Term.br "expect_colon" }

theorem doBody172Block_find :
    stage2NoEventBody.findBlock "do.body172" = some doBody172Block := by
  decide

/-- The key's position advanced by one, at `i32`. -/
def keyAdd175 (p : Nat) : BitVec 32 :=
  BitVec.ofNat 32 p + BitVec.ofNat 32 1

/-- The advanced position zero-extended to a word. -/
def keyConv176 (p : Nat) : BitVec 64 :=
  BitVec.ofNat 64 (keyAdd175 p).toNat

/-- The tag word added to the advanced position. -/
def keyOr (p : Nat) : BitVec 64 :=
  keyConv176 p + BitVec.ofNat 64 9223372036854775813

/-- The key's record field: the tagged position plus the key's length. -/
def keyAdd177 (p : Nat) (sb : BitVec 64) : BitVec 64 :=
  keyOr p + sb

/-- The cells `do.body172` binds, newest first. -/
def doBody172CellList (p : Nat) (sb : BitVec 64) : List (String × Value) :=
  [("%add177", .int 64 (keyAdd177 p sb)),
   ("%or", .int 64 (keyOr p)),
   ("%conv176", .int 64 (keyConv176 p)),
   ("%add175", .int 32 (keyAdd175 p))]

/-- **`do.body172`'s run**: the advanced position, its tag, and the key's
record field. -/
theorem doBody172_denote (calls : Calls) (env : Env) (s : State)
    {p : Nat} {sb : BitVec 64}
    (hp0 : lookupName env "%p.0" = some (.int 32 (BitVec.ofNat 32 p)))
    (hsub : lookupName env "%sub154" = some (.int 64 sb)) :
    denoteCode calls doBody172Instrs (stateAt env s) =
      some (stateAt (cells (doBody172CellList p sb) env) s) := by
  unfold doBody172Instrs
  rw [stage2NoEventWalk_denote_add_imm_w (calls := calls) (env := env) (s := s)
    (d := "%add175") (a := "%p.0") (w := 32) (x := BitVec.ofNat 32 p)
    (c := BitVec.ofNat 32 1) hp0]
  rw [denoteCode_zext (calls := calls)
    (env := ("%add175", .int 32 (BitVec.ofNat 32 p + BitVec.ofNat 32 1)) :: env)
    (s := s)
    (d := "%conv176") (v := "%add175") (wIn := 32) (wOut := 64)
    (x := BitVec.ofNat 32 p + BitVec.ofNat 32 1)
    (hv := by simp only [lookupName_cons_self])]
  rw [denoteCode_add_imm (calls := calls)
    (env := ("%conv176", .int 64 (BitVec.ofNat 64
        (BitVec.ofNat 32 p + BitVec.ofNat 32 1).toNat)) ::
      ("%add175", .int 32 (BitVec.ofNat 32 p + BitVec.ofNat 32 1)) :: env) (s := s)
    (d := "%or") (a := "%conv176")
    (x := BitVec.ofNat 64 (BitVec.ofNat 32 p + BitVec.ofNat 32 1).toNat)
    (c := BitVec.ofNat 64 9223372036854775813)
    (ha := by simp only [lookupName_cons_self])]
  rw [denoteCode_add_reg (calls := calls)
    (env := ("%or", .int 64 (BitVec.ofNat 64
        (BitVec.ofNat 32 p + BitVec.ofNat 32 1).toNat +
          BitVec.ofNat 64 9223372036854775813)) ::
      ("%conv176", .int 64 (BitVec.ofNat 64
        (BitVec.ofNat 32 p + BitVec.ofNat 32 1).toNat)) ::
      ("%add175", .int 32 (BitVec.ofNat 32 p + BitVec.ofNat 32 1)) :: env)
    (s := s)
    (d := "%add177") (a := "%or") (b := "%sub154")
    (x := BitVec.ofNat 64 (BitVec.ofNat 32 p + BitVec.ofNat 32 1).toNat +
      BitVec.ofNat 64 9223372036854775813) (y := sb)
    (ha := by simp only [lookupName_cons_self])
    (hb := by rw [lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide), hsub])]
  simp only [doBody172CellList, keyAdd177, keyOr, keyConv176, keyAdd175, cells,
    denoteCode_nil]

/-- **`do.body172`'s control step**: the block branches to `expect_colon` with no
memory effect. -/
theorem link_doBody172 {calls : Calls} {K : Stage2NoEventWalkCarry} {mem : Mem}
    {s : State} {p : Nat} {sb : BitVec 64}
    (h : Stage2NoEventWalkInv K mem s) (hpc : s.pc = "do.body172")
    (hp0 : lookupName s.env "%p.0" = some (.int 32 (BitVec.ofNat 32 p)))
    (hsub : lookupName s.env "%sub154" = some (.int 64 sb)) :
    Stage2NoEventWalkLink calls K mem s K
      (stage2NoEventWalkNext (cells (doBody172CellList p sb) s.env) s
        "expect_colon") := by
  have hcode : denoteCode calls doBody172Block.instrs (stateAt s.env s) =
      some (stateAt (cells (doBody172CellList p sb) s.env) s) := by
    rw [show doBody172Block.instrs = doBody172Instrs from rfl]
    exact doBody172_denote (calls := calls) s.env s hp0 hsub
  refine ⟨h, ?_, Stage2NoEventWalkInv.mem_congr h rfl⟩
  have hstep := stage2NoEventWalk_step_br (f := stage2NoEventBody)
    (by simp only [stateAt]; rw [hpc]; exact doBody172Block_find) hcode rfl
  simpa only [stage2NoEventWalkNext, stateAt] using hstep

/-! ### `expect_colon`

The three `phi`s select the escape-free arm's readings, the lifetime marker is
closed, and the entry after the key's closing quote is tested against `%nep`.
The block's `,`-armed continuation is `if.end303`'s pair run, which the committed
pair module owns. -/

/-- `expect_colon`'s three `phi`s, in the order the block writes them. -/
def expectColonPhiSpecs : List PhiSpec :=
  [ { dst := "%alen.2", ty := Ty.int 64,
      incoming := [("do.body172", Operand.reg "%alen.1"),
        ("for.cond.cleanup", Operand.reg "%add187")] },
    { dst := "%arena.3", ty := Ty.int 64,
      incoming := [("do.body172", Operand.reg "%arena.1"),
        ("for.cond.cleanup", Operand.reg "%arena.2.lcssa")] },
    { dst := "%add177.pn", ty := Ty.int 64,
      incoming := [("do.body172", Operand.reg "%add177"),
        ("for.cond.cleanup", Operand.reg "%add191")] } ]

/-- The block's `phi` instructions. -/
def expectColonPhiInstrs : List Instr :=
  [ Instr.phi "%alen.2" (Ty.int 64) [("do.body172", (Operand.reg "%alen.1")),
      ("for.cond.cleanup", (Operand.reg "%add187"))],
    Instr.phi "%arena.3" (Ty.int 64) [("do.body172", (Operand.reg "%arena.1")),
      ("for.cond.cleanup", (Operand.reg "%arena.2.lcssa"))],
    Instr.phi "%add177.pn" (Ty.int 64) [("do.body172", (Operand.reg "%add177")),
      ("for.cond.cleanup", (Operand.reg "%add191"))] ]

theorem expectColonPhi_eq :
    expectColonPhiInstrs = List.map PhiSpec.instr expectColonPhiSpecs := by
  decide

/-- `expect_colon`'s two instructions after the run. -/
def expectColonRestInstrs : List Instr :=
  [ Instr.callVoid "llvm.lifetime.end.p0"
      [((Ty.int 64), (Operand.imm (.int 64 (BitVec.ofNat 64 8)))),
       (Ty.ptr, (Operand.reg "%outn"))],
    Instr.icmp "%cmp295.not" IPred.ult 64 (Operand.reg "%inc137")
      (Operand.reg "%nep") ]

/-- `expect_colon`'s instructions: the three selections and the two after them. -/
def expectColonInstrs : List Instr := expectColonPhiInstrs ++ expectColonRestInstrs

/-- `expect_colon`, pinned. -/
def expectColonBlock : Block :=
  { name := "expect_colon", instrs := expectColonInstrs,
    term := Term.condbr (Operand.reg "%cmp295.not") "if.end303" "if.then297" }

theorem expectColonBlock_find :
    stage2NoEventBody.findBlock "expect_colon" = some expectColonBlock := by
  decide

/-- The cells `expect_colon` binds, newest first. -/
def expectColonCellList (alen arena : Nat) (addpn inc nep : BitVec 64) :
    List (String × Value) :=
  [("%cmp295.not", .int 1 (evalICmp .ult inc nep)),
   ("%add177.pn", .int 64 addpn),
   ("%arena.3", .int 64 (BitVec.ofNat 64 arena)),
   ("%alen.2", .int 64 (BitVec.ofNat 64 alen))]

/-- **`expect_colon`'s run at the escape-free edge**: the three `phi`s, the
lifetime marker's close, and the next entry's test. -/
theorem expectColon_denote (calls : Calls) (env : Env) (s : State)
    {alen arena : Nat} {addpn inc nep : BitVec 64} {outn : Nat} {r : CallOutcome}
    (hpre : s.pre = some "do.body172")
    (hsel : PhiSelects (stateAt env s) "do.body172" expectColonPhiSpecs
      [("%alen.2", .int 64 (BitVec.ofNat 64 alen)),
       ("%arena.3", .int 64 (BitVec.ofNat 64 arena)),
       ("%add177.pn", .int 64 addpn)])
    (houtn : lookupName env "%outn" = some (.ptr outn))
    (hinc : lookupName env "%inc137" = some (.int 64 inc))
    (hnep : lookupName env "%nep" = some (.int 64 nep))
    (hc : calls "llvm.lifetime.end.p0"
      [.int 64 (BitVec.ofNat 64 8), .ptr outn] s.mem s.next = some r) :
    denoteCode calls expectColonInstrs (stateAt env s) =
      some (stateAt (cells (expectColonCellList alen arena addpn inc nep) env)
        { s with mem := r.mem, next := r.next }) := by
  rw [show expectColonInstrs = expectColonPhiInstrs ++ expectColonRestInstrs
    from rfl, expectColonPhi_eq]
  rw [denoteCode_phiRun (s := stateAt env s) (p := "do.body172")
    (specs := expectColonPhiSpecs)
    (vs := [("%alen.2", .int 64 (BitVec.ofNat 64 alen)),
      ("%arena.3", .int 64 (BitVec.ofNat 64 arena)),
      ("%add177.pn", .int 64 addpn)])
    (rest := expectColonRestInstrs) (hpre := hpre) (hsel := hsel) (hrest := rfl)]
  rw [stateAt_bindAll_runCells]
  rw [expectColonRestInstrs]
  have houtnRun : lookupName (runCells
      [("%alen.2", .int 64 (BitVec.ofNat 64 alen)),
       ("%arena.3", .int 64 (BitVec.ofNat 64 arena)),
       ("%add177.pn", .int 64 addpn)] env) "%outn" = some (.ptr outn) := by
    simp only [runCells]
    rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide), houtn]
  have hincRun : lookupName (runCells
      [("%alen.2", .int 64 (BitVec.ofNat 64 alen)),
       ("%arena.3", .int 64 (BitVec.ofNat 64 arena)),
       ("%add177.pn", .int 64 addpn)] env) "%inc137" = some (.int 64 inc) := by
    simp only [runCells]
    rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide), hinc]
  have hnepRun : lookupName (runCells
      [("%alen.2", .int 64 (BitVec.ofNat 64 alen)),
       ("%arena.3", .int 64 (BitVec.ofNat 64 arena)),
       ("%add177.pn", .int 64 addpn)] env) "%nep" = some (.int 64 nep) := by
    simp only [runCells]
    rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide), hnep]
  rw [denoteCode_callVoid2 (calls := calls)
    (env := runCells [("%alen.2", .int 64 (BitVec.ofNat 64 alen)),
      ("%arena.3", .int 64 (BitVec.ofNat 64 arena)),
      ("%add177.pn", .int 64 addpn)] env) (s := s)
    (callee := "llvm.lifetime.end.p0") (c := BitVec.ofNat 64 8)
    (o2 := .reg "%outn") (v2 := .ptr outn) (r := r)
    (by simp only [stateAt, evalOperand, houtnRun]) hc]
  rw [stage2NoEventWalk_denote_icmp_reg (calls := calls)
    (env := runCells [("%alen.2", .int 64 (BitVec.ofNat 64 alen)),
      ("%arena.3", .int 64 (BitVec.ofNat 64 arena)),
      ("%add177.pn", .int 64 addpn)] env) (s := _)
    (d := "%cmp295.not") (a := "%inc137") (b := "%nep") (p := .ult) (w := 64)
    (x := inc) (y := nep) (ha := hincRun) (hb := hnepRun) (is := [])]
  simp only [expectColonCellList, runCells, cells, denoteCode_nil]

/-- **`expect_colon` at the next entry's existence**: the true arm, to
`if.end303`.  The lifetime marker's close is the caller's outcome and leaves the
memory and cursor unchanged. -/
theorem link_expectColon_true {calls : Calls} {K : Stage2NoEventWalkCarry}
    {mem : Mem} {s : State} {alen arena : Nat} {addpn inc nep : BitVec 64}
    {outn : Nat} {r : CallOutcome}
    (h : Stage2NoEventWalkInv K mem s) (hpc : s.pc = "expect_colon")
    (hpre : s.pre = some "do.body172")
    (hsel : PhiSelects (stateAt s.env s) "do.body172" expectColonPhiSpecs
      [("%alen.2", .int 64 (BitVec.ofNat 64 alen)),
       ("%arena.3", .int 64 (BitVec.ofNat 64 arena)),
       ("%add177.pn", .int 64 addpn)])
    (houtn : lookupName s.env "%outn" = some (.ptr outn))
    (hinc : lookupName s.env "%inc137" = some (.int 64 inc))
    (hnep : lookupName s.env "%nep" = some (.int 64 nep))
    (hc : calls "llvm.lifetime.end.p0"
      [.int 64 (BitVec.ofNat 64 8), .ptr outn] s.mem s.next = some r)
    (hinv : Stage2NoEventWalkInv K mem { s with mem := r.mem, next := r.next })
    (hy : evalICmp .ult inc nep = 1) :
    Stage2NoEventWalkLink calls K mem s K
      (stage2NoEventWalkNext
        (cells (expectColonCellList alen arena addpn inc nep) s.env)
        { s with mem := r.mem, next := r.next } "if.end303") := by
  have hcode : denoteCode calls expectColonBlock.instrs (stateAt s.env s) =
      some (stateAt (cells (expectColonCellList alen arena addpn inc nep) s.env)
        { s with mem := r.mem, next := r.next }) := by
    rw [show expectColonBlock.instrs = expectColonInstrs from rfl]
    exact expectColon_denote (calls := calls) s.env s hpre hsel houtn hinc hnep hc
  refine ⟨h, ?_, ?_⟩
  · have hstep := stage2NoEventWalk_step_condbr_true (f := stage2NoEventBody)
      (by simp only [stateAt]; rw [hpc]; exact expectColonBlock_find) hcode rfl
      (by simp only [expectColonCellList, cells, stateAt, lookupName_cons_self, hy])
    exact hstep
  · exact Stage2NoEventWalkInv.mem_congr hinv rfl

/-! ### The key route's price and its source

The route's blocks are the walk's own key scanner: `key_body`, `if.end136`,
`if.end150`, `if.end159`, `NodeBlock25`, `LeafBlock23`, `do.body172` and
`expect_colon`, eight steps from `key_body`'s entry to `if.end303`'s.  The two
entries differ only in the `phi` edge that selects `key_body`'s seven readings
(`LeafBlock17` for the first member, `if.end111` for a later one) and in the
index they hand over, so the source below is parameterised by `%k.1.in`'s value
`v` and by the entry's key position `p`.

The key's one token and its record field are the pair carry's delta, so the
target carry is `keyCarry`: one token, and the terms the record field adds. -/

/-- The key's length word `%sub154`: the closing quote's lane and the complement
of the key's open position. -/
def keySub (p close : Nat) : BitVec 64 :=
  BitVec.ofNat 64 close +
    (BitVec.ofNat 64 (BitVec.ofNat 32 p).toNat ^^^
      BitVec.ofNat 64 18446744073709551615)

/-- The carry the key's record moves the source to: the source registers' token
count plus one, and their terms plus the record field's. -/
def keyCarry (K : Stage2NoEventWalkCarry) (p cl terms1 toks1 : Nat) :
    Stage2NoEventWalkCarry :=
  { K with tok := toks1 + 1, terms := terms1 + (keyAdd177 p (keySub p cl)).toNat }

/-- **A word is its own `Nat` representative's word.** -/
theorem keyOfNat_toNat {w : Nat} (x : BitVec w) : BitVec.ofNat w x.toNat = x := by
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]

/-- **The key route's source**: `key_body`'s entry, its entry edge, and the
caller's staging facts (the two lifetime markers' outcomes, the scanner call's
outcome and frame, the endpoint's trace, and the colon's byte). -/
structure Stage2NoEventWalkKeySrc (calls : Calls) (mem : Mem)
    (K : Stage2NoEventWalkCarry) (s : State) : Type where
  /-- The invariant at the entry. -/
  inv : Stage2NoEventWalkInv K mem s
  pc : s.pc = "key_body"
  /-- The `phi` edge the entry came from. -/
  pred : String
  pre : s.pre = some pred
  /-- The key's open position. -/
  p : Nat
  /-- `%k.1.in`'s value: the entry before the key. -/
  v : Nat
  /-- The source registers' two counts (`%terms.1`/`%tokens.1`). -/
  terms1 : Nat
  toks1 : Nat
  /-- The opener's token already in the source registers (`0` on the comma
  entry, `1` on the `{` head's). -/
  d : Nat
  dLe : d ≤ 3
  /-- The depth `key_body` selects. -/
  sp : Nat
  pLt : p < 2 ^ 32
  spLt : sp < 2 ^ 32
  /-- The next head's index fits the arithmetic and the entry stream. -/
  vAddr : v + 4 < 2 ^ 63
  vNext : v + 4 < K.nep
  hsel : PhiSelects (stateAt s.env s) pred keyBodyPhiSpecs
    (keyBodyVs p sp v K.arena.length K.arenaWord terms1 toks1)
  /-- The entry chain's live-ins. -/
  hbase : Stage2NoEventWalkBaseLookups K s
  bPos : 1 ≤ K.b
  /-- The source registers' count, at the opener's token offset. -/
  htoks : toks1 ≤ v + d
  /-- The scratch guard: the key's byte extent fits the buffer. -/
  hscratch : evalICmp .ugt
    (BitVec.ofNat 64 (K.ent.getD (v + 2) 0) +
      (BitVec.ofNat 64 (BitVec.ofNat 32 p).toNat ^^^
        BitVec.ofNat 64 18446744073709551615) + BitVec.ofNat 64 64)
    (BitVec.ofNat 64 K.scratchcap) = 0
  /-- `key_body`'s lifetime marker. -/
  r0 : CallOutcome
  hstart : calls "llvm.lifetime.start.p0"
    [.int 64 (BitVec.ofNat 64 8), .ptr (K.next0 + 8)] s.mem s.next = some r0
  hstartMem : r0.mem = s.mem
  hstartNext : r0.next = s.next
  /-- The scanner's call, at the memory the `%k219` store leaves. -/
  r : CallOutcome
  hcall : calls "s2_string_body"
    [.ptr K.c, .ptr (K.b + 1 + p),
     .int 64 (keySub p (K.ent.getD (v + 2) 0)),
     .ptr K.scratch, .ptr (K.next0 + 8), .ptr K.xp, .ptr K.next0,
     .int 64 (BitVec.ofNat 64 K.nxp)]
    (writeBytes (writeBytes s.mem (K.c + 32)
      (natToBytes (BitVec.ofNat 64 (v + 3)).toNat 8))
      (K.next0 + 8) (natToBytes 0 8)) s.next = some r
  /-- The escape-free key: the scanner's answer is one. -/
  rRet : r.ret = .int 32 (BitVec.ofNat 32 1)
  /-- The invariant at the call's result. -/
  callInv : Stage2NoEventWalkInv K mem
    { s with mem := r.mem, next := r.next }
  /-- `expect_colon`'s lifetime marker. -/
  lend : CallOutcome
  hlend : calls "llvm.lifetime.end.p0"
    [.int 64 (BitVec.ofNat 64 8), .ptr (K.next0 + 8)] r.mem r.next = some lend
  hlendMem : lend.mem = r.mem
  /-- The endpoint's output evidence: the key's record is the class route's. -/
  traceEnd : Stage2NoEventWalkTrace (keyCarry K p (K.ent.getD (v + 2) 0) terms1 toks1)
  /-- The byte at the colon's entry is the colon. -/
  colon : ∀ lane, K.ent[v + 3]? = some lane → K.bs.getD lane 0 = 58

/-- A lookup through one cell layer at a name the layer does not bind. -/
theorem keyRoute_through {cs : List (String × Value)} {env : Env} {n : String}
    {v : Value} (h : n ∉ cs.map (·.1)) (hl : lookupName env n = some v) :
    lookupName (cells cs env) n = some v := by
  rw [stage2NoEventWalkCells_notin cs n env h]; exact hl

/-- **The key route**: eight blocks from `key_body`'s entry to `if.end303`'s,
ending at the pair endpoint.  The target carry is the key's: one token and
the record field's terms. -/
theorem stage2NoEventWalkKeyRoute {calls : Calls} {mem : Mem}
    {K : Stage2NoEventWalkCarry} {s : State}
    (h : Stage2NoEventWalkKeySrc calls mem K s) :
    ∃ (s' : State),
      Stage2NoEventWalkSegment calls mem K s
          (keyCarry K h.p (K.ent.getD (h.v + 2) 0) h.terms1 h.toks1) s' 8 ∧
      Nonempty (Stage2NoEventWalkPairSrc calls mem
        (keyCarry K h.p (K.ent.getD (h.v + 2) 0) h.terms1 h.toks1) h.v s') := by
  obtain ⟨inv, hpc, pred, hpre, p, v, terms1, toks1, d, hdLe, sp, hpLt, hspLt,
    hvAddr, hvNext, hsel, hbase, hbpos, htoks, hscratch, r0, hstart,
    hstartMem, hstartNext, r, hcall, hrRet, hcallInv, lend, hlend, hlendMem,
    htraceEnd, hcolon⟩ := h
  have hnepLt : K.nep < 2 ^ 64 := inv.nepLt
  have hnLt : K.n < 2 ^ 64 := inv.nLt
  -- the base table's two halves
  have hparam : ∀ n x, (n, x) ∈ stage2NoEventWalkParamEntries K →
      lookupName s.env n = some x :=
    fun n x hx => hbase n x (List.mem_append_left _ hx)
  have hcell : ∀ n x, (n, x) ∈ stage2NoEventWalkBaseCellValues K →
      lookupName s.env n = some x :=
    fun n x hx => hbase n x (List.mem_append_right _ hx)
  have hB : lookupName s.env "%b" = some (.ptr K.b) :=
    hparam "%b" _ (by simp [stage2NoEventWalkParamEntries])
  have hEp : lookupName s.env "%ep" = some (.ptr K.ep) :=
    hparam "%ep" _ (by simp [stage2NoEventWalkParamEntries])
  have hN : lookupName s.env "%n" = some (.int 64 (BitVec.ofNat 64 K.n)) :=
    hparam "%n" _ (by simp [stage2NoEventWalkParamEntries])
  have hNep : lookupName s.env "%nep" = some (.int 64 (BitVec.ofNat 64 K.nep)) :=
    hparam "%nep" _ (by simp [stage2NoEventWalkParamEntries])
  have hScr : lookupName s.env "%scratch" = some (.ptr K.scratch) :=
    hparam "%scratch" _ (by simp [stage2NoEventWalkParamEntries])
  have hScrCap : lookupName s.env "%scratchcap" =
      some (.int 64 (BitVec.ofNat 64 K.scratchcap)) :=
    hparam "%scratchcap" _ (by simp [stage2NoEventWalkParamEntries])
  have hC : lookupName s.env "%c" = some (.ptr K.c) :=
    hparam "%c" _ (by simp [stage2NoEventWalkParamEntries])
  have hXp : lookupName s.env "%xp" = some (.ptr K.xp) :=
    hparam "%xp" _ (by simp [stage2NoEventWalkParamEntries])
  have hNxp : lookupName s.env "%nxp" = some (.int 64 (BitVec.ofNat 64 K.nxp)) :=
    hparam "%nxp" _ (by simp [stage2NoEventWalkParamEntries])
  have hcellsBase : ∀ n x, (n, x) ∈ stage2NoEventWalkBaseCellValues K →
      lookupName s.env n = some x := hcell
  have hXj : lookupName s.env "%xj" = some (.ptr K.next0) :=
    hcell "%xj" _ (by simp [stage2NoEventWalkBaseCellValues, preHeaderCells,
      entryCells1, entryCells2, entryCells3, entryCells4])
  have hOutn : lookupName s.env "%outn" = some (.ptr (K.next0 + 8)) :=
    hcell "%outn" _ (by simp [stage2NoEventWalkBaseCellValues, preHeaderCells,
      entryCells1, entryCells2, entryCells3, entryCells4])
  have hGep : lookupName s.env "%invariant.gep" = some (.ptr (K.b + 1)) :=
    hcell "%invariant.gep" _ (by simp [stage2NoEventWalkBaseCellValues,
      preHeaderCells, entryCells1, entryCells2, entryCells3, entryCells4])
  have hK219 : lookupName s.env "%k219" = some (.ptr (K.c + 32)) :=
    hcell "%k219" _ (by simp [stage2NoEventWalkBaseCellValues, preHeaderCells,
      entryCells1, entryCells2, entryCells3, entryCells4])
  -- the entry stream and the key's closing quote's lane
  have hlanes : readLanes32 s.mem K.ep K.nep = some K.ent :=
    inv.readLanes_off (stage2NoEventCycleOutLane inv) inv.entries
  obtain ⟨lane2, bsC, hgetC, hreadC, hvalC, hltC⟩ :=
    stage2NoEventCycleEnt_lane hlanes (by omega : v + 2 < K.nep)
  have hcloseDef : K.ent.getD (v + 2) 0 = lane2 := by
    rw [List.getD_eq_getElem?_getD, hgetC]; rfl
  have hcloseMem : lane2 ∈ K.ent := List.mem_of_getElem? hgetC
  have hcloseLt : lane2 < K.n := inv.inside lane2 hcloseMem
  have hcloseLt32 : lane2 < 2 ^ 32 := by
    have hlt := stage2NoEventBytesToNat_lt_32
      (readBytes_length s.mem (K.ep + 4 * (v + 2)) 4 (bs := bsC) hreadC)
    rw [← hvalC]; exact hlt
  -- the source's staging facts at the derived lane
  have hscratch' : evalICmp .ugt
      (BitVec.ofNat 64 lane2 +
        (BitVec.ofNat 64 (BitVec.ofNat 32 p).toNat ^^^
          BitVec.ofNat 64 18446744073709551615) + BitVec.ofNat 64 64)
      (BitVec.ofNat 64 K.scratchcap) = 0 := by
    simpa only [hcloseDef] using hscratch
  have hcall' : calls "s2_string_body"
      [.ptr K.c, .ptr (K.b + 1 + p), .int 64 (keySub p lane2),
       .ptr K.scratch, .ptr (K.next0 + 8), .ptr K.xp, .ptr K.next0,
       .int 64 (BitVec.ofNat 64 K.nxp)]
      (writeBytes (writeBytes s.mem (K.c + 32)
        (natToBytes (BitVec.ofNat 64 (v + 3)).toNat 8))
        (K.next0 + 8) (natToBytes 0 8)) s.next = some r := by
    simpa only [hcloseDef] using hcall
  have htraceEnd' : Stage2NoEventWalkTrace (keyCarry K p lane2 terms1 toks1) := by
    simpa only [hcloseDef] using htraceEnd
  -- `key_body`'s link
  let S1 : State := stage2NoEventWalkNext
    (cells (keyBodyCellList p sp v K.arena.length K.arenaWord terms1 toks1
      (BitVec.ofNat 64 K.nep)) s.env) s "if.end136"
  have hultKey : evalICmp .ult (BitVec.ofNat 64 (v + 2)) (BitVec.ofNat 64 K.nep) = 1 :=
    stage2NoEventICmp_ult_one (by omega) (by omega) (by omega)
  have L1 : Stage2NoEventWalkLink calls K mem s K S1 :=
    link_keyBody_true (calls := calls) (K := K) (mem := mem) (s := s)
      (pred := pred) (p := p) (sp := sp) (v := v) (alen := K.arena.length)
      (arena := K.arenaWord) (terms1 := terms1) (toks1 := toks1)
      (o := K.next0 + 8) (nep := BitVec.ofNat 64 K.nep) (r := r0)
      inv hpc hpre hsel hOutn hNep hstart hstartMem hstartNext hultKey
  -- the key's cells at `key_body`'s exit
  have hKin1 : lookupName S1.env "%k.1.in" =
      some (.int 64 (BitVec.ofNat 64 v)) :=
    stage2NoEventWalkCells_some (cs := keyBodyCellList p sp v K.arena.length
      K.arenaWord terms1 toks1 (BitVec.ofNat 64 K.nep)) (n := "%k.1.in")
      (v := .int 64 (BitVec.ofNat 64 v)) (by simp [keyBodyCellList]) (by simp only [keyBodyCellList, List.map_cons, List.map_nil]; decide)
  have hK1 : lookupName S1.env "%k.1" =
      some (.int 64 (BitVec.ofNat 64 (v + 2))) :=
    stage2NoEventWalkCells_some (cs := keyBodyCellList p sp v K.arena.length
      K.arenaWord terms1 toks1 (BitVec.ofNat 64 K.nep)) (n := "%k.1")
      (v := .int 64 (BitVec.ofNat 64 (v + 2))) (by simp [keyBodyCellList])
      (by simp only [keyBodyCellList, List.map_cons, List.map_nil]; decide)
  have hP01 : lookupName S1.env "%p.0" = some (.int 32 (BitVec.ofNat 32 p)) :=
    stage2NoEventWalkCells_some (cs := keyBodyCellList p sp v K.arena.length
      K.arenaWord terms1 toks1 (BitVec.ofNat 64 K.nep)) (n := "%p.0")
      (v := .int 32 (BitVec.ofNat 32 p)) (by simp [keyBodyCellList]) (by simp only [keyBodyCellList, List.map_cons, List.map_nil]; decide)
  have hEp1 : lookupName S1.env "%ep" = some (.ptr K.ep) :=
    keyRoute_through (cs := keyBodyCellList p sp v K.arena.length K.arenaWord
      terms1 toks1 (BitVec.ofNat 64 K.nep)) (by simp only [keyBodyCellList, List.map_cons, List.map_nil]; decide) hEp
  have hN1 : lookupName S1.env "%n" = some (.int 64 (BitVec.ofNat 64 K.n)) :=
    keyRoute_through (cs := keyBodyCellList p sp v K.arena.length K.arenaWord
      terms1 toks1 (BitVec.ofNat 64 K.nep)) (by simp only [keyBodyCellList, List.map_cons, List.map_nil]; decide) hN
  have hK2191 : lookupName S1.env "%k219" = some (.ptr (K.c + 32)) :=
    keyRoute_through (cs := keyBodyCellList p sp v K.arena.length K.arenaWord
      terms1 toks1 (BitVec.ofNat 64 K.nep)) (by simp only [keyBodyCellList, List.map_cons, List.map_nil]; decide) hK219
  have hreadS1 : readBytes S1.mem (K.ep + 4 * (v + 2)) 4 = some bsC := by
    simp only [S1, stage2NoEventWalkNext]
    exact hreadC
  have hvalC' : bytesToNat bsC = lane2 := hvalC
  -- `if.end136`'s link
  let S2 : State := stage2NoEventWalkStored
    (cells (ifEnd136CellList K.ep v p (v + 2) lane2 (BitVec.ofNat 64 K.n))
      S1.env) S1
    (writeBytes S1.mem (K.c + 32)
      (natToBytes (BitVec.ofNat 64 (v + 3)).toNat 8)) "if.end150"
  have hwInc : ∀ j, j < (natToBytes (BitVec.ofNat 64 (v + 3)).toNat 8).length →
      inRegions (stage2NoEventRunRegions K.scratch K.scratchcap K.stk K.e K.c
        K.d ++ [(K.next0, K.nextEnd - K.next0)]) (K.c + 32 + j) := by
    intro j hj
    refine ⟨(K.c, stage2NoEventCursorExtent), ?_, ?_⟩
    · simp [stage2NoEventRunRegions, stage2NoEventStagedRegions]
    · simp only [stage2NoEventCursorExtent]
      simp only [natToBytes_length] at hj
      omega
  have hguard136 : evalICmp .ugt (BitVec.ofNat 64 K.n)
      (BitVec.ofNat 64 lane2) = 1 :=
    stage2NoEventICmp_ugt_one inv.nLt (by omega) hcloseLt
  have L2 : Stage2NoEventWalkLink calls K mem S1 K S2 :=
    link_ifEnd136_true (calls := calls) (K := K) (mem := mem) (s := S1)
      (ep := K.ep) (v := v) (p := p) (k1 := v + 2) (close := lane2)
      (a := K.c + 32) (bs4 := bsC) (n := BitVec.ofNat 64 K.n)
      L1.inv' rfl hKin1 hK1 (by omega) hEp1 hP01 hK2191 hN1 hvalC' hcloseLt32
      hreadS1 hwInc hguard136
  -- `if.end150`'s link
  let S3 : State := stage2NoEventWalkNext
    (cells (ifEnd150CellList p lane2 (BitVec.ofNat 64 K.scratchcap)) S2.env)
    S2 "if.end159"
  have hConv152_2 : lookupName S2.env "%conv152" =
      some (.int 64 (BitVec.ofNat 64 (BitVec.ofNat 32 p).toNat)) :=
    stage2NoEventWalkCells_some (cs := ifEnd136CellList K.ep v p (v + 2) lane2
      (BitVec.ofNat 64 K.n)) (n := "%conv152")
      (v := .int 64 (BitVec.ofNat 64 (BitVec.ofNat 32 p).toNat))
      (by simp [ifEnd136CellList]) (by simp only [ifEnd136CellList, List.map_cons, List.map_nil]; decide)
  have hConv140_2 : lookupName S2.env "%conv140" =
      some (.int 64 (BitVec.ofNat 64 lane2)) :=
    stage2NoEventWalkCells_some (cs := ifEnd136CellList K.ep v p (v + 2) lane2
      (BitVec.ofNat 64 K.n)) (n := "%conv140")
      (v := .int 64 (BitVec.ofNat 64 lane2)) (by simp [ifEnd136CellList])
      (by simp only [ifEnd136CellList, List.map_cons, List.map_nil]; decide)
  have hScrCap2 : lookupName S2.env "%scratchcap" =
      some (.int 64 (BitVec.ofNat 64 K.scratchcap)) :=
    keyRoute_through (cs := ifEnd136CellList K.ep v p (v + 2) lane2
      (BitVec.ofNat 64 K.n)) (by simp only [ifEnd136CellList, List.map_cons, List.map_nil]; decide)
      (keyRoute_through (cs := keyBodyCellList p sp v K.arena.length K.arenaWord
        terms1 toks1 (BitVec.ofNat 64 K.nep)) (by simp only [keyBodyCellList, List.map_cons, List.map_nil]; decide) hScrCap)
  have L3 : Stage2NoEventWalkLink calls K mem S2 K S3 :=
    link_ifEnd150_false (calls := calls) (K := K) (mem := mem) (s := S2)
      (opn := p) (close := lane2) (sc := BitVec.ofNat 64 K.scratchcap)
      L2.inv' rfl hConv152_2 hConv140_2 hScrCap2 hscratch'
  -- `if.end159`'s link
  let S4 : State := stage2NoEventWalkNext
    (ifEnd159Cells S3.env (K.b + 1) (BitVec.ofNat 64 (BitVec.ofNat 32 p).toNat) r)
    { S3 with mem := r.mem, next := r.next } "NodeBlock25"
  have hOutn3 : lookupName S3.env "%outn" = some (.ptr (K.next0 + 8)) :=
    keyRoute_through (cs := ifEnd150CellList p lane2 (BitVec.ofNat 64 K.scratchcap))
      (by simp only [ifEnd150CellList, List.map_cons, List.map_nil]; decide)
      (keyRoute_through (cs := ifEnd136CellList K.ep v p (v + 2) lane2
        (BitVec.ofNat 64 K.n)) (by simp only [ifEnd136CellList, List.map_cons, List.map_nil]; decide)
        (keyRoute_through (cs := keyBodyCellList p sp v K.arena.length
          K.arenaWord terms1 toks1 (BitVec.ofNat 64 K.nep)) (by simp only [keyBodyCellList, List.map_cons, List.map_nil]; decide) hOutn))
  have hGep3 : lookupName S3.env "%invariant.gep" = some (.ptr (K.b + 1)) :=
    keyRoute_through (cs := ifEnd150CellList p lane2 (BitVec.ofNat 64 K.scratchcap))
      (by simp only [ifEnd150CellList, List.map_cons, List.map_nil]; decide)
      (keyRoute_through (cs := ifEnd136CellList K.ep v p (v + 2) lane2
        (BitVec.ofNat 64 K.n)) (by simp only [ifEnd136CellList, List.map_cons, List.map_nil]; decide)
        (keyRoute_through (cs := keyBodyCellList p sp v K.arena.length
          K.arenaWord terms1 toks1 (BitVec.ofNat 64 K.nep)) (by simp only [keyBodyCellList, List.map_cons, List.map_nil]; decide) hGep))
  have hC3 : lookupName S3.env "%c" = some (.ptr K.c) :=
    keyRoute_through (cs := ifEnd150CellList p lane2 (BitVec.ofNat 64 K.scratchcap))
      (by simp only [ifEnd150CellList, List.map_cons, List.map_nil]; decide)
      (keyRoute_through (cs := ifEnd136CellList K.ep v p (v + 2) lane2
        (BitVec.ofNat 64 K.n)) (by simp only [ifEnd136CellList, List.map_cons, List.map_nil]; decide)
        (keyRoute_through (cs := keyBodyCellList p sp v K.arena.length
          K.arenaWord terms1 toks1 (BitVec.ofNat 64 K.nep)) (by simp only [keyBodyCellList, List.map_cons, List.map_nil]; decide) hC))
  have hScr3 : lookupName S3.env "%scratch" = some (.ptr K.scratch) :=
    keyRoute_through (cs := ifEnd150CellList p lane2 (BitVec.ofNat 64 K.scratchcap))
      (by simp only [ifEnd150CellList, List.map_cons, List.map_nil]; decide)
      (keyRoute_through (cs := ifEnd136CellList K.ep v p (v + 2) lane2
        (BitVec.ofNat 64 K.n)) (by simp only [ifEnd136CellList, List.map_cons, List.map_nil]; decide)
        (keyRoute_through (cs := keyBodyCellList p sp v K.arena.length
          K.arenaWord terms1 toks1 (BitVec.ofNat 64 K.nep)) (by simp only [keyBodyCellList, List.map_cons, List.map_nil]; decide) hScr))
  have hXp3 : lookupName S3.env "%xp" = some (.ptr K.xp) :=
    keyRoute_through (cs := ifEnd150CellList p lane2 (BitVec.ofNat 64 K.scratchcap))
      (by simp only [ifEnd150CellList, List.map_cons, List.map_nil]; decide)
      (keyRoute_through (cs := ifEnd136CellList K.ep v p (v + 2) lane2
        (BitVec.ofNat 64 K.n)) (by simp only [ifEnd136CellList, List.map_cons, List.map_nil]; decide)
        (keyRoute_through (cs := keyBodyCellList p sp v K.arena.length
          K.arenaWord terms1 toks1 (BitVec.ofNat 64 K.nep)) (by simp only [keyBodyCellList, List.map_cons, List.map_nil]; decide) hXp))
  have hXj3 : lookupName S3.env "%xj" = some (.ptr K.next0) :=
    keyRoute_through (cs := ifEnd150CellList p lane2 (BitVec.ofNat 64 K.scratchcap))
      (by simp only [ifEnd150CellList, List.map_cons, List.map_nil]; decide)
      (keyRoute_through (cs := ifEnd136CellList K.ep v p (v + 2) lane2
        (BitVec.ofNat 64 K.n)) (by simp only [ifEnd136CellList, List.map_cons, List.map_nil]; decide)
        (keyRoute_through (cs := keyBodyCellList p sp v K.arena.length
          K.arenaWord terms1 toks1 (BitVec.ofNat 64 K.nep)) (by simp only [keyBodyCellList, List.map_cons, List.map_nil]; decide) hXj))
  have hNxp3 : lookupName S3.env "%nxp" = some (.int 64 (BitVec.ofNat 64 K.nxp)) :=
    keyRoute_through (cs := ifEnd150CellList p lane2 (BitVec.ofNat 64 K.scratchcap))
      (by simp only [ifEnd150CellList, List.map_cons, List.map_nil]; decide)
      (keyRoute_through (cs := ifEnd136CellList K.ep v p (v + 2) lane2
        (BitVec.ofNat 64 K.n)) (by simp only [ifEnd136CellList, List.map_cons, List.map_nil]; decide)
        (keyRoute_through (cs := keyBodyCellList p sp v K.arena.length
          K.arenaWord terms1 toks1 (BitVec.ofNat 64 K.nep)) (by simp only [keyBodyCellList, List.map_cons, List.map_nil]; decide) hNxp))
  have hConv152_3 : lookupName S3.env "%conv152" =
      some (.int 64 (BitVec.ofNat 64 (BitVec.ofNat 32 p).toNat)) :=
    keyRoute_through (cs := ifEnd150CellList p lane2 (BitVec.ofNat 64 K.scratchcap))
      (by simp only [ifEnd150CellList, List.map_cons, List.map_nil]; decide) hConv152_2
  have hSub3 : lookupName S3.env "%sub154" = some (.int 64 (keySub p lane2)) :=
    stage2NoEventWalkCells_some (cs := ifEnd150CellList p lane2
      (BitVec.ofNat 64 K.scratchcap)) (n := "%sub154")
      (v := .int 64 (keySub p lane2))
      (by simp [ifEnd150CellList, keySub]) (by simp only [ifEnd150CellList, List.map_cons, List.map_nil]; decide)
  have hpos159 : ((BitVec.ofNat 64 (BitVec.ofNat 32 p).toNat).signExtend 64).toNat
      < 2 ^ 63 := by
    rw [stage2NoEventOfNat32_toNat hpLt]
    exact stage2NoEventLane_signExtend_lt hpLt
  have hidx159 : ((BitVec.ofNat 64 (BitVec.ofNat 32 p).toNat).signExtend 64).toNat
      = p := by
    rw [stage2NoEventOfNat32_toNat hpLt]
    exact stage2NoEventSignExtend_toNat (by omega : p < 2 ^ 64)
  have hcallMem : S3.mem = writeBytes s.mem (K.c + 32)
      (natToBytes (BitVec.ofNat 64 (v + 3)).toNat 8) := by
    simp only [S3, S2, S1, stage2NoEventWalkNext, stage2NoEventWalkStored]
  have hcallNext : S3.next = s.next := by
    simp only [S3, S2, S1, stage2NoEventWalkNext, stage2NoEventWalkStored]
  have hcall'' : calls "s2_string_body"
      [.ptr K.c,
       .ptr ((K.b + 1) +
         ((BitVec.ofNat 64 (BitVec.ofNat 32 p).toNat).signExtend 64).toNat),
       .int 64 (keySub p lane2), .ptr K.scratch, .ptr (K.next0 + 8),
       .ptr K.xp, .ptr K.next0, .int 64 (BitVec.ofNat 64 K.nxp)]
      (writeBytes S3.mem (K.next0 + 8) (natToBytes 0 8)) S3.next = some r := by
    rw [hcallMem, hcallNext]
    simpa only [hidx159] using hcall'
  have L4 : Stage2NoEventWalkLink calls K mem S3 K S4 :=
    link_ifEnd159 (calls := calls) (K := K) (mem := mem) (s := S3)
      (g := K.b + 1) (outn := K.next0 + 8) (c := K.c) (scratch := K.scratch)
      (xp := K.xp) (xj := K.next0)
      (idx := BitVec.ofNat 64 (BitVec.ofNat 32 p).toNat) (sub := keySub p lane2)
      (nxp := BitVec.ofNat 64 K.nxp) (r := r)
      L3.inv' rfl hOutn3 hGep3 hConv152_3 hpos159 hSub3 hC3 hScr3 hXp3 hXj3
      hNxp3 hcall'' (Stage2NoEventWalkInv.mem_congr hcallInv rfl)
  -- the result's two tests
  let S5 : State := stage2NoEventWalkNext
    (("%Pivot26", .int 1 (evalICmp .slt (BitVec.ofNat 32 1)
      (BitVec.ofNat 32 1))) :: S4.env) S4 "LeafBlock23"
  have hCall4 : lookupName S4.env "%call161" =
      some (.int 32 (BitVec.ofNat 32 1)) := by
    simp only [S4, stage2NoEventWalkNext, ifEnd159Cells, lookupName_cons_self,
      hrRet]
  have L5 : Stage2NoEventWalkLink calls K mem S4 K S5 :=
    link_nodeBlock25_false (calls := calls) (K := K) (mem := mem) (s := S4)
      L4.inv' rfl hCall4
  let S6 : State := stage2NoEventWalkNext
    (("%SwitchLeaf24", .int 1 (evalICmp .eq (BitVec.ofNat 32 1)
      (BitVec.ofNat 32 1))) :: S5.env) S5 "do.body172"
  have hCall5 : lookupName S5.env "%call161" =
      some (.int 32 (BitVec.ofNat 32 1)) := by
    rw [show S5.env = ("%Pivot26", .int 1 (evalICmp .slt (BitVec.ofNat 32 1)
      (BitVec.ofNat 32 1))) :: S4.env from rfl]
    rw [lookupName_cons_ne _ _ (by decide)]
    exact hCall4
  have L6 : Stage2NoEventWalkLink calls K mem S5 K S6 :=
    link_leafBlock23_true (calls := calls) (K := K) (mem := mem) (s := S5)
      L5.inv' rfl hCall5
  -- `do.body172`'s link
  let S7 : State := stage2NoEventWalkNext
    (cells (doBody172CellList p (keySub p lane2)) S6.env) S6 "expect_colon"
  have hP06 : lookupName S6.env "%p.0" = some (.int 32 (BitVec.ofNat 32 p)) := by
    rw [show S6.env = ("%SwitchLeaf24", .int 1 (evalICmp .eq (BitVec.ofNat 32 1)
      (BitVec.ofNat 32 1))) :: S5.env from rfl]
    rw [lookupName_cons_ne _ _ (by decide)]
    rw [show S5.env = ("%Pivot26", .int 1 (evalICmp .slt (BitVec.ofNat 32 1)
      (BitVec.ofNat 32 1))) :: S4.env from rfl]
    rw [lookupName_cons_ne _ _ (by decide)]
    rw [show S4.env = ifEnd159Cells S3.env (K.b + 1)
      (BitVec.ofNat 64 (BitVec.ofNat 32 p).toNat) r from rfl]
    simp only [ifEnd159Cells]
    rw [lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide)]
    exact keyRoute_through (cs := ifEnd150CellList p lane2
      (BitVec.ofNat 64 K.scratchcap)) (by simp only [ifEnd150CellList, List.map_cons, List.map_nil]; decide)
      (keyRoute_through (cs := ifEnd136CellList K.ep v p (v + 2) lane2
        (BitVec.ofNat 64 K.n)) (by simp only [ifEnd136CellList, List.map_cons, List.map_nil]; decide) hP01)
  have hSub6 : lookupName S6.env "%sub154" = some (.int 64 (keySub p lane2)) := by
    rw [show S6.env = ("%SwitchLeaf24", .int 1 (evalICmp .eq (BitVec.ofNat 32 1)
      (BitVec.ofNat 32 1))) :: S5.env from rfl]
    rw [lookupName_cons_ne _ _ (by decide)]
    rw [show S5.env = ("%Pivot26", .int 1 (evalICmp .slt (BitVec.ofNat 32 1)
      (BitVec.ofNat 32 1))) :: S4.env from rfl]
    rw [lookupName_cons_ne _ _ (by decide)]
    rw [show S4.env = ifEnd159Cells S3.env (K.b + 1)
      (BitVec.ofNat 64 (BitVec.ofNat 32 p).toNat) r from rfl]
    simp only [ifEnd159Cells]
    rw [lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide)]
    exact hSub3
  have L7 : Stage2NoEventWalkLink calls K mem S6 K S7 :=
    link_doBody172 (calls := calls) (K := K) (mem := mem) (s := S6)
      (p := p) (sb := keySub p lane2) L6.inv' rfl hP06 hSub6
  -- `expect_colon`'s link
  let S8 : State := stage2NoEventWalkNext
    (cells (expectColonCellList K.arena.length K.arenaWord
      (keyAdd177 p (keySub p lane2)) (BitVec.ofNat 64 (v + 3))
      (BitVec.ofNat 64 K.nep)) S7.env)
    { S7 with mem := lend.mem, next := lend.next } "if.end303"
  -- the lookups at `do.body172`'s exit
  have hOutn6 : lookupName S6.env "%outn" = some (.ptr (K.next0 + 8)) := by
    rw [show S6.env = ("%SwitchLeaf24", .int 1 (evalICmp .eq (BitVec.ofNat 32 1)
      (BitVec.ofNat 32 1))) :: S5.env from rfl]
    rw [lookupName_cons_ne _ _ (by decide)]
    rw [show S5.env = ("%Pivot26", .int 1 (evalICmp .slt (BitVec.ofNat 32 1)
      (BitVec.ofNat 32 1))) :: S4.env from rfl]
    rw [lookupName_cons_ne _ _ (by decide)]
    rw [show S4.env = ifEnd159Cells S3.env (K.b + 1)
      (BitVec.ofNat 64 (BitVec.ofNat 32 p).toNat) r from rfl]
    simp only [ifEnd159Cells]
    rw [lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide)]
    exact hOutn3
  have hInc137_6 : lookupName S6.env "%inc137" =
      some (.int 64 (BitVec.ofNat 64 (v + 3))) := by
    rw [show S6.env = ("%SwitchLeaf24", .int 1 (evalICmp .eq (BitVec.ofNat 32 1)
      (BitVec.ofNat 32 1))) :: S5.env from rfl]
    rw [lookupName_cons_ne _ _ (by decide)]
    rw [show S5.env = ("%Pivot26", .int 1 (evalICmp .slt (BitVec.ofNat 32 1)
      (BitVec.ofNat 32 1))) :: S4.env from rfl]
    rw [lookupName_cons_ne _ _ (by decide)]
    rw [show S4.env = ifEnd159Cells S3.env (K.b + 1)
      (BitVec.ofNat 64 (BitVec.ofNat 32 p).toNat) r from rfl]
    simp only [ifEnd159Cells]
    rw [lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide)]
    exact keyRoute_through (cs := ifEnd150CellList p lane2
      (BitVec.ofNat 64 K.scratchcap)) (by simp only [ifEnd150CellList, List.map_cons, List.map_nil]; decide)
      (stage2NoEventWalkCells_some (cs := ifEnd136CellList K.ep v p (v + 2)
        lane2 (BitVec.ofNat 64 K.n)) (n := "%inc137")
        (v := .int 64 (BitVec.ofNat 64 (v + 3)))
        (by simp [ifEnd136CellList]) (by simp only [ifEnd136CellList, List.map_cons, List.map_nil]; decide))
  have hNep6 : lookupName S6.env "%nep" =
      some (.int 64 (BitVec.ofNat 64 K.nep)) := by
    rw [show S6.env = ("%SwitchLeaf24", .int 1 (evalICmp .eq (BitVec.ofNat 32 1)
      (BitVec.ofNat 32 1))) :: S5.env from rfl]
    rw [lookupName_cons_ne _ _ (by decide)]
    rw [show S5.env = ("%Pivot26", .int 1 (evalICmp .slt (BitVec.ofNat 32 1)
      (BitVec.ofNat 32 1))) :: S4.env from rfl]
    rw [lookupName_cons_ne _ _ (by decide)]
    rw [show S4.env = ifEnd159Cells S3.env (K.b + 1)
      (BitVec.ofNat 64 (BitVec.ofNat 32 p).toNat) r from rfl]
    simp only [ifEnd159Cells]
    rw [lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide)]
    exact keyRoute_through (cs := ifEnd150CellList p lane2
      (BitVec.ofNat 64 K.scratchcap)) (by simp only [ifEnd150CellList, List.map_cons, List.map_nil]; decide)
      (keyRoute_through (cs := ifEnd136CellList K.ep v p (v + 2) lane2
        (BitVec.ofNat 64 K.n)) (by simp only [ifEnd136CellList, List.map_cons, List.map_nil]; decide)
        (keyRoute_through (cs := keyBodyCellList p sp v K.arena.length
          K.arenaWord terms1 toks1 (BitVec.ofNat 64 K.nep)) (by simp only [keyBodyCellList, List.map_cons, List.map_nil]; decide) hNep))
  have hAlen6 : lookupName S6.env "%alen.1" =
      some (.int 64 (BitVec.ofNat 64 K.arena.length)) := by
    rw [show S6.env = ("%SwitchLeaf24", .int 1 (evalICmp .eq (BitVec.ofNat 32 1)
      (BitVec.ofNat 32 1))) :: S5.env from rfl]
    rw [lookupName_cons_ne _ _ (by decide)]
    rw [show S5.env = ("%Pivot26", .int 1 (evalICmp .slt (BitVec.ofNat 32 1)
      (BitVec.ofNat 32 1))) :: S4.env from rfl]
    rw [lookupName_cons_ne _ _ (by decide)]
    rw [show S4.env = ifEnd159Cells S3.env (K.b + 1)
      (BitVec.ofNat 64 (BitVec.ofNat 32 p).toNat) r from rfl]
    simp only [ifEnd159Cells]
    rw [lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide)]
    exact keyRoute_through (cs := ifEnd150CellList p lane2
      (BitVec.ofNat 64 K.scratchcap)) (by simp only [ifEnd150CellList, List.map_cons, List.map_nil]; decide)
      (keyRoute_through (cs := ifEnd136CellList K.ep v p (v + 2) lane2
        (BitVec.ofNat 64 K.n)) (by simp only [ifEnd136CellList, List.map_cons, List.map_nil]; decide)
        (stage2NoEventWalkCells_some (cs := keyBodyCellList p sp v
          K.arena.length K.arenaWord terms1 toks1 (BitVec.ofNat 64 K.nep))
          (n := "%alen.1") (v := .int 64 (BitVec.ofNat 64 K.arena.length))
          (by simp [keyBodyCellList]) (by simp only [keyBodyCellList, List.map_cons, List.map_nil]; decide)))
  have hArena6 : lookupName S6.env "%arena.1" =
      some (.int 64 (BitVec.ofNat 64 K.arenaWord)) := by
    rw [show S6.env = ("%SwitchLeaf24", .int 1 (evalICmp .eq (BitVec.ofNat 32 1)
      (BitVec.ofNat 32 1))) :: S5.env from rfl]
    rw [lookupName_cons_ne _ _ (by decide)]
    rw [show S5.env = ("%Pivot26", .int 1 (evalICmp .slt (BitVec.ofNat 32 1)
      (BitVec.ofNat 32 1))) :: S4.env from rfl]
    rw [lookupName_cons_ne _ _ (by decide)]
    rw [show S4.env = ifEnd159Cells S3.env (K.b + 1)
      (BitVec.ofNat 64 (BitVec.ofNat 32 p).toNat) r from rfl]
    simp only [ifEnd159Cells]
    rw [lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide)]
    exact keyRoute_through (cs := ifEnd150CellList p lane2
      (BitVec.ofNat 64 K.scratchcap)) (by simp only [ifEnd150CellList, List.map_cons, List.map_nil]; decide)
      (keyRoute_through (cs := ifEnd136CellList K.ep v p (v + 2) lane2
        (BitVec.ofNat 64 K.n)) (by simp only [ifEnd136CellList, List.map_cons, List.map_nil]; decide)
        (stage2NoEventWalkCells_some (cs := keyBodyCellList p sp v
          K.arena.length K.arenaWord terms1 toks1 (BitVec.ofNat 64 K.nep))
          (n := "%arena.1") (v := .int 64 (BitVec.ofNat 64 K.arenaWord))
          (by simp [keyBodyCellList]) (by simp only [keyBodyCellList, List.map_cons, List.map_nil]; decide)))
  -- the same at `expect_colon`'s entry
  have hOutn7 : lookupName S7.env "%outn" = some (.ptr (K.next0 + 8)) := by
    rw [show S7.env = cells (doBody172CellList p (keySub p lane2)) S6.env from rfl]
    exact keyRoute_through (cs := doBody172CellList p (keySub p lane2))
      (by simp only [doBody172CellList, List.map_cons, List.map_nil]; decide) hOutn6
  have hInc137_7 : lookupName S7.env "%inc137" =
      some (.int 64 (BitVec.ofNat 64 (v + 3))) := by
    rw [show S7.env = cells (doBody172CellList p (keySub p lane2)) S6.env from rfl]
    exact keyRoute_through (cs := doBody172CellList p (keySub p lane2))
      (by simp only [doBody172CellList, List.map_cons, List.map_nil]; decide) hInc137_6
  have hNep7 : lookupName S7.env "%nep" =
      some (.int 64 (BitVec.ofNat 64 K.nep)) := by
    rw [show S7.env = cells (doBody172CellList p (keySub p lane2)) S6.env from rfl]
    exact keyRoute_through (cs := doBody172CellList p (keySub p lane2))
      (by simp only [doBody172CellList, List.map_cons, List.map_nil]; decide) hNep6
  have hAlen7 : lookupName S7.env "%alen.1" =
      some (.int 64 (BitVec.ofNat 64 K.arena.length)) := by
    rw [show S7.env = cells (doBody172CellList p (keySub p lane2)) S6.env from rfl]
    exact keyRoute_through (cs := doBody172CellList p (keySub p lane2))
      (by simp only [doBody172CellList, List.map_cons, List.map_nil]; decide) hAlen6
  have hArena7 : lookupName S7.env "%arena.1" =
      some (.int 64 (BitVec.ofNat 64 K.arenaWord)) := by
    rw [show S7.env = cells (doBody172CellList p (keySub p lane2)) S6.env from rfl]
    exact keyRoute_through (cs := doBody172CellList p (keySub p lane2))
      (by simp only [doBody172CellList, List.map_cons, List.map_nil]; decide) hArena6
  have hAdd177_7 : lookupName S7.env "%add177" =
      some (.int 64 (keyAdd177 p (keySub p lane2))) :=
    stage2NoEventWalkCells_some (cs := doBody172CellList p (keySub p lane2))
      (n := "%add177") (v := .int 64 (keyAdd177 p (keySub p lane2)))
      (by simp [doBody172CellList]) (by simp only [doBody172CellList, List.map_cons, List.map_nil]; decide)
  have hselExp : PhiSelects (stateAt S7.env S7) "do.body172" expectColonPhiSpecs
      [("%alen.2", .int 64 (BitVec.ofNat 64 K.arena.length)),
       ("%arena.3", .int 64 (BitVec.ofNat 64 K.arenaWord)),
       ("%add177.pn", .int 64 (keyAdd177 p (keySub p lane2)))] := by
    refine PhiSelects.cons (op := .reg "%alen.1") (by decide) ?_
      (PhiSelects.cons (op := .reg "%arena.1") (by decide) ?_
        (PhiSelects.cons (op := .reg "%add177") (by decide) ?_ PhiSelects.nil))
    all_goals simp only [stateAt, evalOperand]
    · exact hAlen7
    · exact hArena7
    · exact hAdd177_7
  have hpre7 : S7.pre = some "do.body172" := rfl
  have hUlt7 : evalICmp .ult (BitVec.ofNat 64 (v + 3))
      (BitVec.ofNat 64 K.nep) = 1 :=
    stage2NoEventICmp_ult_one (by omega) (by omega) (by omega)
  have hlend7 : calls "llvm.lifetime.end.p0"
      [.int 64 (BitVec.ofNat 64 8), .ptr (K.next0 + 8)] S7.mem S7.next
      = some lend := by
    have hm : S7.mem = r.mem := by
      simp only [S7, S6, S5, S4, S3, S2, S1, stage2NoEventWalkNext,
        stage2NoEventWalkStored]
    have hn : S7.next = r.next := by
      simp only [S7, S6, S5, S4, S3, S2, S1, stage2NoEventWalkNext,
        stage2NoEventWalkStored]
    rw [hm, hn]; exact hlend
  have hinv7 : Stage2NoEventWalkInv K mem
      { S7 with mem := lend.mem, next := lend.next } := by
    have hm : ({ S7 with mem := lend.mem, next := lend.next } : State).mem
        = r.mem := by
      simp only [hlendMem]
    exact Stage2NoEventWalkInv.mem_congr hcallInv hm
  have L8 : Stage2NoEventWalkLink calls K mem S7 K S8 :=
    link_expectColon_true (calls := calls) (K := K) (mem := mem) (s := S7)
      (alen := K.arena.length) (arena := K.arenaWord)
      (addpn := keyAdd177 p (keySub p lane2)) (inc := BitVec.ofNat 64 (v + 3))
      (nep := BitVec.ofNat 64 K.nep) (outn := K.next0 + 8) (r := lend)
      L7.inv' rfl hpre7 hselExp hOutn7 hInc137_7 hNep7 hlend7 hinv7 hUlt7
  -- the run, at the eight steps' own fuel
  have hrun : ∀ n, runFuel calls (8 + n) stage2NoEventBody s =
      runFuel calls n stage2NoEventBody S8 := by
    intro n
    rw [show 8 + n = 1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + n)))))))
      from by omega]
    rw [stage2NoEventWalkLink_runFuel L1, stage2NoEventWalkLink_runFuel L2,
      stage2NoEventWalkLink_runFuel L3, stage2NoEventWalkLink_runFuel L4,
      stage2NoEventWalkLink_runFuel L5, stage2NoEventWalkLink_runFuel L6,
      stage2NoEventWalkLink_runFuel L7, stage2NoEventWalkLink_runFuel L8]
  -- the target carry's invariant
  let Kt := keyCarry K p lane2 terms1 toks1
  have hS8mem : S8.mem = r.mem := by
    simp only [S8, stage2NoEventWalkNext, hlendMem]
  have hInvK : Stage2NoEventWalkInv K mem S8 :=
    Stage2NoEventWalkInv.mem_congr hcallInv hS8mem
  have htokLe : Kt.tok ≤ Kt.n := by
    have hne := inv.nepLe
    simp only [Kt, keyCarry]
    omega
  have hInvKt : Stage2NoEventWalkInv Kt mem S8 :=
    { hInvK with tokLe := htokLe }
  -- the pair endpoint's readings
  have hKin6 : lookupName S6.env "%k.1.in" =
      some (.int 64 (BitVec.ofNat 64 v)) := by
    rw [show S6.env = ("%SwitchLeaf24", .int 1 (evalICmp .eq (BitVec.ofNat 32 1)
      (BitVec.ofNat 32 1))) :: S5.env from rfl]
    rw [lookupName_cons_ne _ _ (by decide)]
    rw [show S5.env = ("%Pivot26", .int 1 (evalICmp .slt (BitVec.ofNat 32 1)
      (BitVec.ofNat 32 1))) :: S4.env from rfl]
    rw [lookupName_cons_ne _ _ (by decide)]
    rw [show S4.env = ifEnd159Cells S3.env (K.b + 1)
      (BitVec.ofNat 64 (BitVec.ofNat 32 p).toNat) r from rfl]
    simp only [ifEnd159Cells]
    rw [lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide)]
    exact keyRoute_through (cs := ifEnd150CellList p lane2
      (BitVec.ofNat 64 K.scratchcap)) (by simp only [ifEnd150CellList, List.map_cons, List.map_nil]; decide)
      (keyRoute_through (cs := ifEnd136CellList K.ep v p (v + 2) lane2
        (BitVec.ofNat 64 K.n)) (by simp only [ifEnd136CellList, List.map_cons, List.map_nil]; decide) hKin1)
  have hKin8 : lookupName S8.env "%k.1.in" =
      some (.int 64 (BitVec.ofNat 64 v)) := by
    rw [show S8.env = cells (expectColonCellList K.arena.length K.arenaWord
      (keyAdd177 p (keySub p lane2)) (BitVec.ofNat 64 (v + 3))
      (BitVec.ofNat 64 K.nep)) S7.env from rfl]
    exact keyRoute_through (cs := expectColonCellList K.arena.length
      K.arenaWord (keyAdd177 p (keySub p lane2)) (BitVec.ofNat 64 (v + 3))
      (BitVec.ofNat 64 K.nep)) (by simp only [expectColonCellList, List.map_cons, List.map_nil]; decide)
      (keyRoute_through (cs := doBody172CellList p (keySub p lane2))
        (by simp only [doBody172CellList, List.map_cons, List.map_nil]; decide) hKin6)
  have hTerms6 : lookupName S6.env "%terms.1" =
      some (.int 64 (BitVec.ofNat 64 terms1)) := by
    rw [show S6.env = ("%SwitchLeaf24", .int 1 (evalICmp .eq (BitVec.ofNat 32 1)
      (BitVec.ofNat 32 1))) :: S5.env from rfl]
    rw [lookupName_cons_ne _ _ (by decide)]
    rw [show S5.env = ("%Pivot26", .int 1 (evalICmp .slt (BitVec.ofNat 32 1)
      (BitVec.ofNat 32 1))) :: S4.env from rfl]
    rw [lookupName_cons_ne _ _ (by decide)]
    rw [show S4.env = ifEnd159Cells S3.env (K.b + 1)
      (BitVec.ofNat 64 (BitVec.ofNat 32 p).toNat) r from rfl]
    simp only [ifEnd159Cells]
    rw [lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide)]
    exact keyRoute_through (cs := ifEnd150CellList p lane2
      (BitVec.ofNat 64 K.scratchcap)) (by simp only [ifEnd150CellList, List.map_cons, List.map_nil]; decide)
      (keyRoute_through (cs := ifEnd136CellList K.ep v p (v + 2) lane2
        (BitVec.ofNat 64 K.n)) (by simp only [ifEnd136CellList, List.map_cons, List.map_nil]; decide)
        (stage2NoEventWalkCells_some (cs := keyBodyCellList p sp v
          K.arena.length K.arenaWord terms1 toks1 (BitVec.ofNat 64 K.nep))
          (n := "%terms.1") (v := .int 64 (BitVec.ofNat 64 terms1))
          (by simp [keyBodyCellList]) (by simp only [keyBodyCellList, List.map_cons, List.map_nil]; decide)))
  have hTerms7 : lookupName S7.env "%terms.1" =
      some (.int 64 (BitVec.ofNat 64 terms1)) := by
    rw [show S7.env = cells (doBody172CellList p (keySub p lane2)) S6.env from rfl]
    exact keyRoute_through (cs := doBody172CellList p (keySub p lane2))
      (by simp only [doBody172CellList, List.map_cons, List.map_nil]; decide) hTerms6
  have hTerms8 : lookupName S8.env "%terms.1" =
      some (.int 64 (BitVec.ofNat 64 terms1)) := by
    rw [show S8.env = cells (expectColonCellList K.arena.length K.arenaWord
      (keyAdd177 p (keySub p lane2)) (BitVec.ofNat 64 (v + 3))
      (BitVec.ofNat 64 K.nep)) S7.env from rfl]
    exact keyRoute_through (cs := expectColonCellList K.arena.length
      K.arenaWord (keyAdd177 p (keySub p lane2)) (BitVec.ofNat 64 (v + 3))
      (BitVec.ofNat 64 K.nep)) (by simp only [expectColonCellList, List.map_cons, List.map_nil]; decide) hTerms7
  have hToks6 : lookupName S6.env "%tokens.1" =
      some (.int 64 (BitVec.ofNat 64 toks1)) := by
    rw [show S6.env = ("%SwitchLeaf24", .int 1 (evalICmp .eq (BitVec.ofNat 32 1)
      (BitVec.ofNat 32 1))) :: S5.env from rfl]
    rw [lookupName_cons_ne _ _ (by decide)]
    rw [show S5.env = ("%Pivot26", .int 1 (evalICmp .slt (BitVec.ofNat 32 1)
      (BitVec.ofNat 32 1))) :: S4.env from rfl]
    rw [lookupName_cons_ne _ _ (by decide)]
    rw [show S4.env = ifEnd159Cells S3.env (K.b + 1)
      (BitVec.ofNat 64 (BitVec.ofNat 32 p).toNat) r from rfl]
    simp only [ifEnd159Cells]
    rw [lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide)]
    exact keyRoute_through (cs := ifEnd150CellList p lane2
      (BitVec.ofNat 64 K.scratchcap)) (by simp only [ifEnd150CellList, List.map_cons, List.map_nil]; decide)
      (keyRoute_through (cs := ifEnd136CellList K.ep v p (v + 2) lane2
        (BitVec.ofNat 64 K.n)) (by simp only [ifEnd136CellList, List.map_cons, List.map_nil]; decide)
        (stage2NoEventWalkCells_some (cs := keyBodyCellList p sp v
          K.arena.length K.arenaWord terms1 toks1 (BitVec.ofNat 64 K.nep))
          (n := "%tokens.1") (v := .int 64 (BitVec.ofNat 64 toks1))
          (by simp [keyBodyCellList]) (by simp only [keyBodyCellList, List.map_cons, List.map_nil]; decide)))
  have hToks7 : lookupName S7.env "%tokens.1" =
      some (.int 64 (BitVec.ofNat 64 toks1)) := by
    rw [show S7.env = cells (doBody172CellList p (keySub p lane2)) S6.env from rfl]
    exact keyRoute_through (cs := doBody172CellList p (keySub p lane2))
      (by simp only [doBody172CellList, List.map_cons, List.map_nil]; decide) hToks6
  have hToks8 : lookupName S8.env "%tokens.1" =
      some (.int 64 (BitVec.ofNat 64 toks1)) := by
    rw [show S8.env = cells (expectColonCellList K.arena.length K.arenaWord
      (keyAdd177 p (keySub p lane2)) (BitVec.ofNat 64 (v + 3))
      (BitVec.ofNat 64 K.nep)) S7.env from rfl]
    exact keyRoute_through (cs := expectColonCellList K.arena.length
      K.arenaWord (keyAdd177 p (keySub p lane2)) (BitVec.ofNat 64 (v + 3))
      (BitVec.ofNat 64 K.nep)) (by simp only [expectColonCellList, List.map_cons, List.map_nil]; decide) hToks7
  have hAdd177pn8 : lookupName S8.env "%add177.pn" =
      some (.int 64 (BitVec.ofNat 64 (keyAdd177 p (keySub p lane2)).toNat)) := by
    rw [show S8.env = cells (expectColonCellList K.arena.length K.arenaWord
      (keyAdd177 p (keySub p lane2)) (BitVec.ofNat 64 (v + 3))
      (BitVec.ofNat 64 K.nep)) S7.env from rfl]
    rw [keyOfNat_toNat]
    exact stage2NoEventWalkCells_some (cs := expectColonCellList K.arena.length
      K.arenaWord (keyAdd177 p (keySub p lane2)) (BitVec.ofNat 64 (v + 3))
      (BitVec.ofNat 64 K.nep)) (n := "%add177.pn")
      (v := .int 64 (keyAdd177 p (keySub p lane2)))
      (by simp [expectColonCellList]) (by simp only [expectColonCellList, List.map_cons, List.map_nil]; decide)
  have hInc8 : lookupName S8.env "%inc137" =
      some (.int 64 (BitVec.ofNat 64 (v + 3))) := by
    rw [show S8.env = cells (expectColonCellList K.arena.length K.arenaWord
      (keyAdd177 p (keySub p lane2)) (BitVec.ofNat 64 (v + 3))
      (BitVec.ofNat 64 K.nep)) S7.env from rfl]
    exact keyRoute_through (cs := expectColonCellList K.arena.length
      K.arenaWord (keyAdd177 p (keySub p lane2)) (BitVec.ofNat 64 (v + 3))
      (BitVec.ofNat 64 K.nep)) (by simp only [expectColonCellList, List.map_cons, List.map_nil]; decide) hInc137_7
  have hSp6 : lookupName S6.env "%sp.1" =
      some (.int 32 (BitVec.ofNat 32 sp)) := by
    rw [show S6.env = ("%SwitchLeaf24", .int 1 (evalICmp .eq (BitVec.ofNat 32 1)
      (BitVec.ofNat 32 1))) :: S5.env from rfl]
    rw [lookupName_cons_ne _ _ (by decide)]
    rw [show S5.env = ("%Pivot26", .int 1 (evalICmp .slt (BitVec.ofNat 32 1)
      (BitVec.ofNat 32 1))) :: S4.env from rfl]
    rw [lookupName_cons_ne _ _ (by decide)]
    rw [show S4.env = ifEnd159Cells S3.env (K.b + 1)
      (BitVec.ofNat 64 (BitVec.ofNat 32 p).toNat) r from rfl]
    simp only [ifEnd159Cells]
    rw [lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide)]
    exact keyRoute_through (cs := ifEnd150CellList p lane2
      (BitVec.ofNat 64 K.scratchcap)) (by simp only [ifEnd150CellList, List.map_cons, List.map_nil]; decide)
      (keyRoute_through (cs := ifEnd136CellList K.ep v p (v + 2) lane2
        (BitVec.ofNat 64 K.n)) (by simp only [ifEnd136CellList, List.map_cons, List.map_nil]; decide)
        (stage2NoEventWalkCells_some (cs := keyBodyCellList p sp v
          K.arena.length K.arenaWord terms1 toks1 (BitVec.ofNat 64 K.nep))
          (n := "%sp.1") (v := .int 32 (BitVec.ofNat 32 sp))
          (by simp [keyBodyCellList]) (by simp only [keyBodyCellList, List.map_cons, List.map_nil]; decide)))
  have hSp8 : lookupName S8.env "%sp.1" =
      some (.int 32 (BitVec.ofNat 32 sp)) := by
    rw [show S8.env = cells (expectColonCellList K.arena.length K.arenaWord
      (keyAdd177 p (keySub p lane2)) (BitVec.ofNat 64 (v + 3))
      (BitVec.ofNat 64 K.nep)) S7.env from rfl]
    exact keyRoute_through (cs := expectColonCellList K.arena.length
      K.arenaWord (keyAdd177 p (keySub p lane2)) (BitVec.ofNat 64 (v + 3))
      (BitVec.ofNat 64 K.nep)) (by simp only [expectColonCellList, List.map_cons, List.map_nil]; decide)
      (keyRoute_through (cs := doBody172CellList p (keySub p lane2))
        (by simp only [doBody172CellList, List.map_cons, List.map_nil]; decide) hSp6)
  have hAlen8 : lookupName S8.env "%alen.2" =
      some (.int 64 (BitVec.ofNat 64 K.arena.length)) := by
    rw [show S8.env = cells (expectColonCellList K.arena.length K.arenaWord
      (keyAdd177 p (keySub p lane2)) (BitVec.ofNat 64 (v + 3))
      (BitVec.ofNat 64 K.nep)) S7.env from rfl]
    exact stage2NoEventWalkCells_some (cs := expectColonCellList K.arena.length
      K.arenaWord (keyAdd177 p (keySub p lane2)) (BitVec.ofNat 64 (v + 3))
      (BitVec.ofNat 64 K.nep)) (n := "%alen.2")
      (v := .int 64 (BitVec.ofNat 64 K.arena.length))
      (by simp [expectColonCellList]) (by simp only [expectColonCellList, List.map_cons, List.map_nil]; decide)
  have hArena8 : lookupName S8.env "%arena.3" =
      some (.int 64 (BitVec.ofNat 64 K.arenaWord)) := by
    rw [show S8.env = cells (expectColonCellList K.arena.length K.arenaWord
      (keyAdd177 p (keySub p lane2)) (BitVec.ofNat 64 (v + 3))
      (BitVec.ofNat 64 K.nep)) S7.env from rfl]
    exact stage2NoEventWalkCells_some (cs := expectColonCellList K.arena.length
      K.arenaWord (keyAdd177 p (keySub p lane2)) (BitVec.ofNat 64 (v + 3))
      (BitVec.ofNat 64 K.nep)) (n := "%arena.3")
      (v := .int 64 (BitVec.ofNat 64 K.arenaWord))
      (by simp [expectColonCellList]) (by simp only [expectColonCellList, List.map_cons, List.map_nil]; decide)
  -- the base table through the eight layers
  have hbaseS8 : Stage2NoEventWalkBaseLookups K S8 := by
    have hcs1 : (keyBodyCellList p sp v K.arena.length K.arenaWord terms1 toks1
        (BitVec.ofNat 64 K.nep)).map (·.1) =
        ["%cmp127.not", "%k.1", "%tokens.1", "%terms.1", "%arena.1",
         "%alen.1", "%k.1.in", "%sp.1", "%p.0"] := by rfl
    have hd1 : stage2NoEventWalkBaseNames.all (fun n => !decide (n ∈
        ["%cmp127.not", "%k.1", "%tokens.1", "%terms.1", "%arena.1",
         "%alen.1", "%k.1.in", "%sp.1", "%p.0"])) = true := by decide
    have b1 := stage2NoEventCycleBase hbase hcs1 hd1
    have hcs2 : (ifEnd136CellList K.ep v p (v + 2) lane2
        (BitVec.ofNat 64 K.n)).map (·.1) =
        ["%conv152", "%cmp141.not", "%conv140", "%14", "%arrayidx138",
         "%inc137"] := by rfl
    have hd2 : stage2NoEventWalkBaseNames.all (fun n => !decide (n ∈
        ["%conv152", "%cmp141.not", "%conv140", "%14", "%arrayidx138",
         "%inc137"])) = true := by decide
    have b2 := stage2NoEventCycleBase b1 hcs2 hd2
    have hcs3 : (ifEnd150CellList p lane2
        (BitVec.ofNat 64 K.scratchcap)).map (·.1) =
        ["%cmp156", "%add155", "%sub154", "%15"] := by rfl
    have hd3 : stage2NoEventWalkBaseNames.all (fun n => !decide (n ∈
        ["%cmp156", "%add155", "%sub154", "%15"])) = true := by decide
    have b3 := stage2NoEventCycleBase b2 hcs3 hd3
    have hcs4 : ([("%call161", r.ret),
        ("%gep1071", .ptr ((K.b + 1) +
          ((BitVec.ofNat 64 (BitVec.ofNat 32 p).toNat).signExtend 64).toNat))] :
        List (String × Value)).map (·.1) = ["%call161", "%gep1071"] := by rfl
    have hd4 : stage2NoEventWalkBaseNames.all (fun n => !decide (n ∈
        ["%call161", "%gep1071"])) = true := by decide
    have b4 := stage2NoEventCycleBase b3 hcs4 hd4
    have hcs5 : ([("%Pivot26", .int 1 (evalICmp .slt (BitVec.ofNat 32 1)
        (BitVec.ofNat 32 1)))] : List (String × Value)).map (·.1) =
        ["%Pivot26"] := by rfl
    have hd5 : stage2NoEventWalkBaseNames.all (fun n => !decide (n ∈
        ["%Pivot26"])) = true := by decide
    have b5 := stage2NoEventCycleBase b4 hcs5 hd5
    have hcs6 : ([("%SwitchLeaf24", .int 1 (evalICmp .eq (BitVec.ofNat 32 1)
        (BitVec.ofNat 32 1)))] : List (String × Value)).map (·.1) =
        ["%SwitchLeaf24"] := by rfl
    have hd6 : stage2NoEventWalkBaseNames.all (fun n => !decide (n ∈
        ["%SwitchLeaf24"])) = true := by decide
    have b6 := stage2NoEventCycleBase b5 hcs6 hd6
    have hcs7 : (doBody172CellList p (keySub p lane2)).map (·.1) =
        ["%add177", "%or", "%conv176", "%add175"] := by rfl
    have hd7 : stage2NoEventWalkBaseNames.all (fun n => !decide (n ∈
        ["%add177", "%or", "%conv176", "%add175"])) = true := by decide
    have b7 := stage2NoEventCycleBase b6 hcs7 hd7
    have hcs8 : (expectColonCellList K.arena.length K.arenaWord
        (keyAdd177 p (keySub p lane2)) (BitVec.ofNat 64 (v + 3))
        (BitVec.ofNat 64 K.nep)).map (·.1) =
        ["%cmp295.not", "%add177.pn", "%arena.3", "%alen.2"] := by rfl
    have hd8 : stage2NoEventWalkBaseNames.all (fun n => !decide (n ∈
        ["%cmp295.not", "%add177.pn", "%arena.3", "%alen.2"])) = true := by decide
    exact fun n v1 hv => stage2NoEventCycleBase b7 hcs8 hd8 n v1 hv
  -- the pair endpoint
  have hcountKt : Stage2NoEventWalkCount Kt (v + 1 + d) := by
    unfold Stage2NoEventWalkCount
    simp only [Kt, keyCarry]
    omega
  have hpair : Stage2NoEventWalkPairSrc calls mem Kt v S8 :=
    { inv := hInvKt
      pc := rfl
      sp := sp
      spLt := hspLt
      inc137 := v + 3
      incEq := rfl
      terms1 := terms1
      tokens1 := toks1
      addpn := (keyAdd177 p (keySub p lane2)).toNat
      termsEq := rfl
      tokEq := rfl
      kAddr := hvAddr
      klt := hvNext
      d := d
      dLe := hdLe
      count := hcountKt
      kin := hKin8
      termsv := hTerms8
      tokensv := hToks8
      addpnv := hAdd177pn8
      incv := hInc8
      spv := hSp8
      alenv := hAlen8
      arenav := hArena8
      baseLookups := hbaseS8
      bPos := hbpos
      trace := htraceEnd'
      colon := hcolon }
  rw [hcloseDef]
  exact ⟨S8, ⟨hrun, hInvKt⟩, ⟨hpair⟩⟩

/-! ### The two entries, and what entry A needs

The route above is stated at `key_body`'s entry, parameterised by `%k.1.in`'s
value `v` and by the entry's key position `p`, so it is the shared tail of both
of the walk's entries.  This module's own entry producer is **entry B**, the
later member's comma route: the frame-zero after-value arm's `,` reaches
`if.end111` (committed as `Stage2NoEventWalkFrameZeroCommaBoundary`), and
`link_ifEnd111_true` hands `key_body` its seven selections with
`%k.1.in = %k.6 = k` and `%p.0 = %12`, the lane at `k + 1`.  The row that
composes this module is therefore the object-member class's, at `v = k` and `p`
the entry at `k + 1`; with `link_ifEnd111_true` in front of the eight blocks the
composed route is nine steps from the comma boundary to `if.end303`.

**Entry A**, the first member, is the brace class's: `if.then9`, its push,
`if.end74`, `NodeBlock21`, then `LeafBlock17`'s quote test into `key_body`, with
`%k.1.in = %k.0.lcssa1086` and `%p.0 = %10`.  `JsonStage2NoEventWalkRowsBrace`
proves that prologue up to `NodeBlock21` and takes its **false** arm to
`LeafBlock19` (the `}` byte against `125`).  It does not prove the clause entry A
needs: `NodeBlock21`'s true arm, `%Pivot22 = (%11 slt 125) = 1`, and
`LeafBlock17`'s `%SwitchLeaf18 = (%11 eq 34) = 1` into `key_body` — that the
head's next entry is the member's opening quote rather than the closer.  The
`%11` cell is both blocks' test input; `key_body`'s seven `phi` inputs are the
brace row's other prologue cells (`%10`, `%inc24`, `%k.0.lcssa1086`,
`%alen.0.ph1405`, `%arena.0.ph1406`, `%add`, `%inc26`), which
`Stage2NoEventWalkEntryAPrologue` bundles.  With those two links the tail above
applies unchanged with `pred = "LeafBlock17"`.
-/

/-! ### Entry A: `NodeBlock21`'s true arm and `LeafBlock17`'s quote test

The `{` head hands `if.end74` the next entry's lane (`%10`) and byte (`%11`); its
`NodeBlock21` tests the byte's signed order against `125`, and `LeafBlock17` tests
equality with `34`.  The committed brace row takes `NodeBlock21`'s false arm to
`LeafBlock19` (the `}` byte); the two links below are the other arm, from the same
prologue cells to `key_body`.

**The count registers entry A brings.**  `if.end74` writes
`%inc26 = %tokens.0.lcssa1074 + 1` and `%add = %terms.0.lcssa1080 + 1`, and
`LeafBlock17` selects them as `key_body`'s `%tokens.1`/`%terms.1`.  So the pair
endpoint's target carry has `tok = K.tok + 2` (the `{` token is already in the
register), while `Stage2NoEventWalkPairSrc.count` bounds the target by `k + 1`;
at the first member (`K.tok = 0`, `k = 0`) that is `2 ≤ 1`.  `PairSrc` therefore
carries the opener's token count `d`: its endpoint is `Count K (k + 1 + d)`, `d = 0`
on the comma entry and `d = 1` here, and the pair cycle steps from `k + 1 + d` to
`k + 4` at `b = 3 - d`.  The lemma below records why the old `k + 1` bound was
refutable. -/

/-- **The old `k + 1` endpoint bound is refutable at the first member**: entry
A's target carries `K.tok + 2`, so the pre-`d` interface could not represent it. -/
theorem stage2NoEventWalkEntryA_countOffByOne {K : Stage2NoEventWalkCarry} {k : Nat}
    (h : K.tok = 0) (hk : k = 0) :
    ¬ Stage2NoEventWalkCount { K with tok := K.tok + 2 } (k + 1) := by
  intro hc
  unfold Stage2NoEventWalkCount at hc
  simp only [h, hk] at hc
  omega

/-- **`NodeBlock21` at the quote**: the true arm, to `LeafBlock17`.  The byte is
the prologue's `%11`, below `125` in the signed order. -/
theorem link_nodeBlock21_true {calls : Calls} {K : Stage2NoEventWalkCarry}
    {mem : Mem} {s : State} {y : BitVec 8}
    (h : Stage2NoEventWalkInv K mem s) (hpc : s.pc = "NodeBlock21")
    (h11 : lookupName s.env "%11" = some (.int 8 y))
    (hy : evalICmp .slt y (BitVec.ofNat 8 125) = 1) :
    Stage2NoEventWalkLink calls K mem s K
      (stage2NoEventWalkNext (("%Pivot22", .int 1 1) :: s.env) s "LeafBlock17") := by
  have hcode : denoteCode calls nodeBlock21Block.instrs (stateAt s.env s) =
      some (stateAt (("%Pivot22", .int 1 1) :: s.env) s) := by
    rw [nodeBlock21Block, nodeBlock21Instrs,
      stage2NoEventWalk_denote_icmp_imm (calls := calls) (env := s.env) (s := s)
      (d := "%Pivot22") (a := "%11") (p := .slt) (w := 8)
      (c := BitVec.ofNat 8 125) h11 (is := [])]
    simp only [hy, denoteCode_nil]
  exact stage2NoEventWalkLink_condbr_true (env' := ("%Pivot22", .int 1 1) :: s.env)
    h (by rw [hpc]; exact nodeBlock21Block_find) hcode rfl (by rw [lookupName_cons_self])

/-- `LeafBlock17`: the byte against 34, selecting `key_body`. -/
def leafBlock17Instrs : List Instr :=
  [ Instr.icmp "%SwitchLeaf18" IPred.eq 8 (Operand.reg "%11")
      (Operand.imm (.int 8 (BitVec.ofNat 8 34))) ]

/-- `LeafBlock17`, pinned. -/
def leafBlock17Block : Block :=
  { name := "LeafBlock17", instrs := leafBlock17Instrs,
    term := Term.condbr (Operand.reg "%SwitchLeaf18") "key_body" "if.then94" }

theorem leafBlock17Block_find :
    stage2NoEventBody.findBlock "LeafBlock17" = some leafBlock17Block := by
  decide

/-- **`LeafBlock17`'s run** at the prologue's byte. -/
theorem leafBlock17_denote (calls : Calls) (env : Env) (s : State) {y : BitVec 8}
    (h11 : lookupName env "%11" = some (.int 8 y)) :
    denoteCode calls leafBlock17Instrs (stateAt env s) =
      some (stateAt (("%SwitchLeaf18",
        .int 1 (evalICmp .eq y (BitVec.ofNat 8 34))) :: env) s) := by
  rw [leafBlock17Instrs, stage2NoEventWalk_denote_icmp_imm (calls := calls)
    (env := env) (s := s) (d := "%SwitchLeaf18") (a := "%11") (p := .eq) (w := 8)
    (c := BitVec.ofNat 8 34) h11 (is := [])]
  simp only [denoteCode_nil]

/-- **`LeafBlock17` at the opening quote**: the true arm, to `key_body`'s entry. -/
theorem link_leafBlock17_true {calls : Calls} {K : Stage2NoEventWalkCarry}
    {mem : Mem} {s : State} {y : BitVec 8}
    (h : Stage2NoEventWalkInv K mem s) (hpc : s.pc = "LeafBlock17")
    (h11 : lookupName s.env "%11" = some (.int 8 y))
    (hy : evalICmp .eq y (BitVec.ofNat 8 34) = 1) :
    Stage2NoEventWalkLink calls K mem s K
      (stage2NoEventWalkNext (("%SwitchLeaf18", .int 1 1) :: s.env) s "key_body") := by
  have hcode : denoteCode calls leafBlock17Block.instrs (stateAt s.env s) =
      some (stateAt (("%SwitchLeaf18", .int 1 1) :: s.env) s) := by
    rw [leafBlock17Block, leafBlock17Instrs,
      stage2NoEventWalk_denote_icmp_imm (calls := calls) (env := s.env) (s := s)
      (d := "%SwitchLeaf18") (a := "%11") (p := .eq) (w := 8)
      (c := BitVec.ofNat 8 34) h11 (is := [])]
    simp only [hy, denoteCode_nil]
  exact stage2NoEventWalkLink_condbr_true (env' := ("%SwitchLeaf18", .int 1 1) :: s.env)
    h (by rw [hpc]; exact leafBlock17Block_find) hcode rfl (by rw [lookupName_cons_self])

/-- **Entry A's two readings**, from `if.end74`'s own cells: the cells
`LeafBlock17` selects as `key_body`'s `%tokens.1`/`%terms.1` are one above the
head's carry readings. -/
theorem stage2NoEventWalkEntryA_readings (env : Env) (ep b : Nat)
    (terms tok inc : BitVec 64) (bs4 bs1 : List UInt8) :
    lookupName (ifEnd74Out env ep b terms tok inc bs4 bs1) "%inc26" =
      some (.int 64 (tok + BitVec.ofNat 64 1)) ∧
    lookupName (ifEnd74Out env ep b terms tok inc bs4 bs1) "%add" =
      some (.int 64 (terms + BitVec.ofNat 64 1)) := by
  constructor
  · simp only [ifEnd74Out, ifEnd74Cells, cells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    rw [lookupName_cons_self]
  · simp only [ifEnd74Out, ifEnd74Cells, cells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    rw [lookupName_cons_self]

/-! ### Entry A end to end

With `PairSrc` carrying the opener's token count `d` and the source registers as
fields, the `{` head's member route is the same tail: `NodeBlock21`'s true arm,
`LeafBlock17`'s quote test, then `stage2NoEventWalkKeyRoute`.  The prologue's
output is the class predicate below — the cells `if.end74` and `if.then9` bind
(`%10` lane, `%11` byte, `%k.0.lcssa1086` index, `%inc24` depth, the two `phi`
readings, and `if.end74`'s `%add`/`%inc26` counts, one above the head's carry).
The brace class exports the eight links that establish it
(`stage2NoEventWalkBracePrologue`), so this predicate is that export's cells at
the opening quote; `stage2NoEventWalkKeyRoute_of_head` composes the two. -/

/-- **The `{` head's prologue at `NodeBlock21`'s entry**: the cells the committed
brace prologue binds, with the two count registers already one above the head's
carry. -/
structure Stage2NoEventWalkEntryAPrologue (K : Stage2NoEventWalkCarry) (mem : Mem)
    (k : Nat) (s : State) : Type where
  inv : Stage2NoEventWalkInv K mem s
  pc : s.pc = "NodeBlock21"
  /-- The next entry's lane (`%10`) and depth (`%inc24`). -/
  lane : Nat
  sp : Nat
  laneLt : lane < 2 ^ 32
  spLt : sp < 2 ^ 32
  /-- The next entry's byte (`%11`), the member's opening quote. -/
  h11 : lookupName s.env "%11" = some (.int 8 (BitVec.ofNat 8 34))
  h10 : lookupName s.env "%10" = some (.int 32 (BitVec.ofNat 32 lane))
  hinc24 : lookupName s.env "%inc24" = some (.int 32 (BitVec.ofNat 32 sp))
  /-- The head's index and the carried readings. -/
  hk : lookupName s.env "%k.0.lcssa1086" = some (.int 64 (BitVec.ofNat 64 k))
  halen : lookupName s.env "%alen.0.ph1405" =
    some (.int 64 (BitVec.ofNat 64 K.arena.length))
  harena : lookupName s.env "%arena.0.ph1406" =
    some (.int 64 (BitVec.ofNat 64 K.arenaWord))
  /-- `if.end74`'s two counts: the head's readings plus one. -/
  hadd : lookupName s.env "%add" = some (.int 64 (BitVec.ofNat 64 (K.terms + 1)))
  hinc26 : lookupName s.env "%inc26" = some (.int 64 (BitVec.ofNat 64 (K.tok + 1)))
  hbase : Stage2NoEventWalkBaseLookups K s
  bPos : 1 ≤ K.b
  count : Stage2NoEventWalkCount K k

/-- **Entry A's prologue from the brace class's exported cells.**  The exporter
in `JsonStage2NoEventWalkRowsBrace` binds the same cells at the state's own lane
and depth; at the opening quote (`b = 34`) they are this predicate, so the two
links below consume the exporter's output directly. -/
def Stage2NoEventWalkBracePrologueCells.toEntryA {K : Stage2NoEventWalkCarry}
    {mem : Mem} {k : Nat} {s : State} {b lane sp : Nat}
    (C : Stage2NoEventWalkBracePrologueCells K mem k s b lane sp) (hb : b = 34) :
    Stage2NoEventWalkEntryAPrologue K mem k s where
  inv := C.inv
  pc := C.pc
  lane := lane
  sp := sp
  laneLt := C.laneLt
  spLt := C.spLt
  h11 := by simpa only [hb] using C.h11
  h10 := C.h10
  hinc24 := C.hinc24
  hk := C.hk
  halen := C.halen
  harena := C.harena
  hadd := C.hadd
  hinc26 := C.hinc26
  hbase := C.hbase
  bPos := C.bPos
  count := C.count

/-- **The `{` head's member route**: from the prologue's `NodeBlock21` entry,
through the quote test and the key route, to the pair endpoint with `d = 1`. -/
theorem stage2NoEventWalkKeyRoute_of_leafBlock17 {calls : Calls} {mem : Mem}
    {K : Stage2NoEventWalkCarry} {k : Nat} {s : State}
    (P : Stage2NoEventWalkEntryAPrologue K mem k s)
    (hvAddr : k + 4 < 2 ^ 63) (hvNext : k + 4 < K.nep)
    (hscratch : evalICmp .ugt
      (BitVec.ofNat 64 (K.ent.getD (k + 2) 0) +
        (BitVec.ofNat 64 (BitVec.ofNat 32 P.lane).toNat ^^^
          BitVec.ofNat 64 18446744073709551615) + BitVec.ofNat 64 64)
      (BitVec.ofNat 64 K.scratchcap) = 0)
    (r0 : CallOutcome)
    (hstart : calls "llvm.lifetime.start.p0"
      [.int 64 (BitVec.ofNat 64 8), .ptr (K.next0 + 8)] s.mem s.next = some r0)
    (hstartMem : r0.mem = s.mem) (hstartNext : r0.next = s.next)
    (r : CallOutcome)
    (hcall : calls "s2_string_body"
      [.ptr K.c, .ptr (K.b + 1 + P.lane),
       .int 64 (keySub P.lane (K.ent.getD (k + 2) 0)),
       .ptr K.scratch, .ptr (K.next0 + 8), .ptr K.xp, .ptr K.next0,
       .int 64 (BitVec.ofNat 64 K.nxp)]
      (writeBytes (writeBytes s.mem (K.c + 32)
        (natToBytes (BitVec.ofNat 64 (k + 3)).toNat 8))
        (K.next0 + 8) (natToBytes 0 8)) s.next = some r)
    (hrRet : r.ret = .int 32 (BitVec.ofNat 32 1))
    (hcallInv : Stage2NoEventWalkInv K mem
      { s with mem := r.mem, next := r.next })
    (lend : CallOutcome)
    (hlend : calls "llvm.lifetime.end.p0"
      [.int 64 (BitVec.ofNat 64 8), .ptr (K.next0 + 8)] r.mem r.next
      = some lend)
    (hlendMem : lend.mem = r.mem)
    (htraceEnd : Stage2NoEventWalkTrace
      (keyCarry K P.lane (K.ent.getD (k + 2) 0) (K.terms + 1) (K.tok + 1)))
    (hcolon : ∀ lane, K.ent[k + 3]? = some lane → K.bs.getD lane 0 = 58) :
    ∃ (s' : State),
      Stage2NoEventWalkSegment calls mem K s
          (keyCarry K P.lane (K.ent.getD (k + 2) 0) (K.terms + 1) (K.tok + 1))
          s' 10 ∧
      Nonempty (Stage2NoEventWalkPairSrc calls mem
        (keyCarry K P.lane (K.ent.getD (k + 2) 0) (K.terms + 1) (K.tok + 1))
        k s') := by
  -- the two entry blocks
  let S1 : State := stage2NoEventWalkNext
    (("%Pivot22", .int 1 1) :: s.env) s "LeafBlock17"
  have L1 : Stage2NoEventWalkLink calls K mem s K S1 :=
    link_nodeBlock21_true (calls := calls) (K := K) (mem := mem) (s := s)
      (y := BitVec.ofNat 8 34) P.inv P.pc P.h11 (by decide)
  have h11_1 : lookupName S1.env "%11" =
      some (.int 8 (BitVec.ofNat 8 34)) := by
    simp only [S1, stage2NoEventWalkNext]
    rw [lookupName_cons_ne _ _ (by decide)]
    exact P.h11
  let S2 : State := stage2NoEventWalkNext
    (("%SwitchLeaf18", .int 1 1) :: S1.env) S1 "key_body"
  have L2 : Stage2NoEventWalkLink calls K mem S1 K S2 :=
    link_leafBlock17_true (calls := calls) (K := K) (mem := mem) (s := S1)
      (y := BitVec.ofNat 8 34) L1.inv' rfl h11_1 (by decide)
  -- the prologue's cells at `key_body`'s entry
  have h10_2 : lookupName S2.env "%10" =
      some (.int 32 (BitVec.ofNat 32 P.lane)) := by
    simp only [S2, S1, stage2NoEventWalkNext]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact P.h10
  have hsp_2 : lookupName S2.env "%inc24" =
      some (.int 32 (BitVec.ofNat 32 P.sp)) := by
    simp only [S2, S1, stage2NoEventWalkNext]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact P.hinc24
  have hk_2 : lookupName S2.env "%k.0.lcssa1086" =
      some (.int 64 (BitVec.ofNat 64 k)) := by
    simp only [S2, S1, stage2NoEventWalkNext]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact P.hk
  have halen_2 : lookupName S2.env "%alen.0.ph1405" =
      some (.int 64 (BitVec.ofNat 64 K.arena.length)) := by
    simp only [S2, S1, stage2NoEventWalkNext]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact P.halen
  have harena_2 : lookupName S2.env "%arena.0.ph1406" =
      some (.int 64 (BitVec.ofNat 64 K.arenaWord)) := by
    simp only [S2, S1, stage2NoEventWalkNext]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact P.harena
  have hadd_2 : lookupName S2.env "%add" =
      some (.int 64 (BitVec.ofNat 64 (K.terms + 1))) := by
    simp only [S2, S1, stage2NoEventWalkNext]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact P.hadd
  have hinc26_2 : lookupName S2.env "%inc26" =
      some (.int 64 (BitVec.ofNat 64 (K.tok + 1))) := by
    simp only [S2, S1, stage2NoEventWalkNext]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact P.hinc26
  have hsel : PhiSelects (stateAt S2.env S2) "LeafBlock17" keyBodyPhiSpecs
      (keyBodyVs P.lane P.sp k K.arena.length K.arenaWord (K.terms + 1)
        (K.tok + 1)) := by
    refine PhiSelects.cons (op := .reg "%10") (by decide) ?_
      (PhiSelects.cons (op := .reg "%inc24") (by decide) ?_
        (PhiSelects.cons (op := .reg "%k.0.lcssa1086") (by decide) ?_
          (PhiSelects.cons (op := .reg "%alen.0.ph1405") (by decide) ?_
            (PhiSelects.cons (op := .reg "%arena.0.ph1406") (by decide) ?_
              (PhiSelects.cons (op := .reg "%add") (by decide) ?_
                (PhiSelects.cons (op := .reg "%inc26") (by decide) ?_
                  PhiSelects.nil))))))
    all_goals
      simp only [stateAt, evalOperand, h10_2, hsp_2, hk_2, halen_2, harena_2,
        hadd_2, hinc26_2]
  have hbase2 : Stage2NoEventWalkBaseLookups K S2 := by
    have hb1 := stage2NoEventCycleBase P.hbase
      (cs := [("%Pivot22", .int 1 1)]) (names := ["%Pivot22"]) rfl (by decide)
    have hb2 := stage2NoEventCycleBase hb1
      (cs := [("%SwitchLeaf18", .int 1 1)]) (names := ["%SwitchLeaf18"]) rfl
      (by decide)
    exact fun n v hv => hb2 n v hv
  -- the source
  have htoksSrc : K.tok + 1 ≤ k + 1 := by
    have hc : K.tok ≤ k := P.count
    omega
  have hroute := stage2NoEventWalkKeyRoute (calls := calls) (mem := mem) (K := K)
    (s := S2)
    { inv := L2.inv'
      pc := rfl
      pred := "LeafBlock17"
      pre := rfl
      p := P.lane
      v := k
      terms1 := K.terms + 1
      toks1 := K.tok + 1
      d := 1
      dLe := by omega
      sp := P.sp
      pLt := P.laneLt
      spLt := P.spLt
      vAddr := hvAddr
      vNext := hvNext
      hsel := hsel
      hbase := hbase2
      bPos := P.bPos
      htoks := htoksSrc
      hscratch := hscratch
      r0 := r0
      hstart := hstart
      hstartMem := hstartMem
      hstartNext := hstartNext
      r := r
      hcall := hcall
      rRet := hrRet
      callInv := Stage2NoEventWalkInv.mem_congr hcallInv rfl
      lend := lend
      hlend := hlend
      hlendMem := hlendMem
      traceEnd := htraceEnd
      colon := hcolon }
  obtain ⟨s', hseg8, hpair⟩ := hroute
  have hrun2 : ∀ n, runFuel calls (2 + n) stage2NoEventBody s =
      runFuel calls n stage2NoEventBody S2 := by
    intro n
    rw [show 2 + n = 1 + (1 + n) from by omega,
      stage2NoEventWalkLink_runFuel L1, stage2NoEventWalkLink_runFuel L2]
  have hseg2 : Stage2NoEventWalkSegment calls mem K s K S2 2 := ⟨hrun2, L2.inv'⟩
  exact ⟨s', hseg2.trans hseg8, hpair⟩

/-! ### Entry A from a head

`Stage2NoEventWalkHead` at the `{` plus the staged reads are all the exporter
needs; the two links above and the tail follow.  A caller holding the head
obtains the pair endpoint at `d = 1` without a prologue value of its own.
-/

/-- **The `{` head's member route, from the head**: the eight prologue links, the
quote test, and the key route, to the pair endpoint at `d = 1`, as one segment. -/
theorem stage2NoEventWalkKeyRoute_of_head {calls : Calls} {mem : Mem}
    {K : Stage2NoEventWalkCarry} {k : Nat} {s : State}
    (h : Stage2NoEventWalkHead K mem k s)
    {lane : Nat} {byte nextByte : UInt8}
    (hk : K.ent[k]? = some lane) (hbs : K.bs[lane]? = some byte) (hb : byte.toNat = 123)
    (hb1 : nextByte.toNat = 34)
    {sp fr : Nat}
    (hspH : lookupName s.env "%sp.0.ph1403" = some (.int 32 (BitVec.ofNat 32 sp)))
    (hfrH : lookupName s.env "%frame.0.ph1402" = some (.int 8 (BitVec.ofNat 8 fr)))
    (hspPos : 1 ≤ sp) (hspLe : sp ≤ 519) (hspLt : sp < 2 ^ 32)
    {bs4 : List UInt8}
    (hlaneW : readBytes (writeBytes s.mem (bracePushAddr K (BitVec.ofNat 32 sp))
      (natToBytes ((BitVec.ofNat 8 fr).toNat) 1))
      (K.ep + (BitVec.ofNat 64 (k + 1)).toNat * 4) 4 = some bs4)
    (hval4lt : bytesToNat bs4 < 2 ^ 32)
    (hbyte1W : readBytes (writeBytes s.mem (bracePushAddr K (BitVec.ofNat 32 sp))
      (natToBytes ((BitVec.ofNat 8 fr).toNat) 1))
      (K.b + (BitVec.signExtend 64 (BitVec.ofNat 64 (bytesToNat bs4))).toNat) 1
      = some [nextByte])
    (hvAddr : k + 4 < 2 ^ 63) (hvNext : k + 4 < K.nep)
    (hscratch : evalICmp .ugt
      (BitVec.ofNat 64 (K.ent.getD (k + 2) 0) +
        (BitVec.ofNat 64 (BitVec.ofNat 32 (bytesToNat bs4)).toNat ^^^
          BitVec.ofNat 64 18446744073709551615) + BitVec.ofNat 64 64)
      (BitVec.ofNat 64 K.scratchcap) = 0)
    (r0 : CallOutcome)
    (hstart : calls "llvm.lifetime.start.p0"
      [.int 64 (BitVec.ofNat 64 8), .ptr (K.next0 + 8)]
      (writeBytes s.mem (bracePushAddr K (BitVec.ofNat 32 sp))
        (natToBytes ((BitVec.ofNat 8 fr).toNat) 1)) s.next = some r0)
    (hstartMem : r0.mem = writeBytes s.mem (bracePushAddr K (BitVec.ofNat 32 sp))
      (natToBytes ((BitVec.ofNat 8 fr).toNat) 1))
    (hstartNext : r0.next = s.next)
    (r : CallOutcome)
    (hcall : calls "s2_string_body"
      [.ptr K.c, .ptr (K.b + 1 + bytesToNat bs4),
       .int 64 (keySub (bytesToNat bs4) (K.ent.getD (k + 2) 0)),
       .ptr K.scratch, .ptr (K.next0 + 8), .ptr K.xp, .ptr K.next0,
       .int 64 (BitVec.ofNat 64 K.nxp)]
      (writeBytes (writeBytes
        (writeBytes s.mem (bracePushAddr K (BitVec.ofNat 32 sp))
          (natToBytes ((BitVec.ofNat 8 fr).toNat) 1)) (K.c + 32)
        (natToBytes (BitVec.ofNat 64 (k + 3)).toNat 8))
        (K.next0 + 8) (natToBytes 0 8)) s.next = some r)
    (hrRet : r.ret = .int 32 (BitVec.ofNat 32 1))
    (hcallInv : Stage2NoEventWalkInv K mem
      { s with mem := r.mem, next := r.next })
    (lend : CallOutcome)
    (hlend : calls "llvm.lifetime.end.p0"
      [.int 64 (BitVec.ofNat 64 8), .ptr (K.next0 + 8)] r.mem r.next
      = some lend)
    (hlendMem : lend.mem = r.mem)
    (htraceEnd : Stage2NoEventWalkTrace
      (keyCarry K (bytesToNat bs4) (K.ent.getD (k + 2) 0) (K.terms + 1) (K.tok + 1)))
    (hcolon : ∀ lane, K.ent[k + 3]? = some lane → K.bs.getD lane 0 = 58) :
    ∃ (s' : State),
      Stage2NoEventWalkSegment calls mem K s
          (keyCarry K (bytesToNat bs4) (K.ent.getD (k + 2) 0) (K.terms + 1) (K.tok + 1))
          s' 18 ∧
      Nonempty (Stage2NoEventWalkPairSrc calls mem
        (keyCarry K (bytesToNat bs4) (K.ent.getD (k + 2) 0) (K.terms + 1) (K.tok + 1))
        k s') := by
  obtain ⟨⟨S8, hseg8, hmem, hnext, C⟩⟩ :=
    stage2NoEventWalkBracePrologue (calls := calls) h hk hbs hb
      hspH hfrH hspPos hspLe hspLt (by omega) (by omega) hlaneW hval4lt hbyte1W
  -- the prologue's memory and cursor are the push's and the head's
  have hstart' : calls "llvm.lifetime.start.p0"
      [.int 64 (BitVec.ofNat 64 8), .ptr (K.next0 + 8)] S8.mem S8.next = some r0 := by
    simpa only [hmem, hnext] using hstart
  have hstartMem' : r0.mem = S8.mem := by
    simpa only [hmem] using hstartMem
  have hstartNext' : r0.next = S8.next := by
    simpa only [hnext] using hstartNext
  have hcall' : calls "s2_string_body"
      [.ptr K.c, .ptr (K.b + 1 + bytesToNat bs4),
       .int 64 (keySub (bytesToNat bs4) (K.ent.getD (k + 2) 0)),
       .ptr K.scratch, .ptr (K.next0 + 8), .ptr K.xp, .ptr K.next0,
       .int 64 (BitVec.ofNat 64 K.nxp)]
      (writeBytes (writeBytes S8.mem (K.c + 32)
        (natToBytes (BitVec.ofNat 64 (k + 3)).toNat 8))
        (K.next0 + 8) (natToBytes 0 8)) S8.next = some r := by
    simpa only [hmem, hnext] using hcall
  have hcallInv' : Stage2NoEventWalkInv K mem
      { S8 with mem := r.mem, next := r.next } :=
    Stage2NoEventWalkInv.mem_congr hcallInv rfl
  obtain ⟨s', hseg10, hpair⟩ :=
    stage2NoEventWalkKeyRoute_of_leafBlock17 (calls := calls) (mem := mem) (K := K)
      (k := k) (s := S8) (C.toEntryA hb1) hvAddr hvNext hscratch r0 hstart'
      hstartMem' hstartNext' r hcall' hrRet hcallInv' lend hlend hlendMem htraceEnd
      hcolon
  exact ⟨s', hseg8.trans hseg10, hpair⟩

/-! ### Axiom footprints -/

#print axioms Stage2NoEventWalkBracePrologueCells.toEntryA
#print axioms stage2NoEventWalkKeyRoute_of_head
