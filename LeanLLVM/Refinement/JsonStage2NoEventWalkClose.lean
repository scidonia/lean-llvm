/-
The no-event walk's closers, part one: the count stores and the depth tests.

`JsonStage2NoEventWalkLoop` states the head's dispatch, the two openers' push
rows, and the `]` entry link `link_ifEnd327peel`.  This module begins the closer
family (decisions (w6), (w7), (w8)): the `}` counts (`if.then81`), the `]` counts
(`if.then334`), and the two depth tests after the edges' `phi` runs (`close_obj`,
`close_arr`).

**The declaration shape (w8).**  A closer environment has four to seven cells and
a `%stk + …` address; a declaration whose type carried those tripped the kernel's
reduction on term size.  So every environment is a named `def` and a declaration's
type mentions it only through a variable with a defining equation.  The builder's
lookups are resolved at the **builder level** — `lookupName_cells_of_some` and
`lookupName_cells_of_notin` — never by unfolding `cells` inside a goal (a
`simp`-only unfolding of the right fold made no progress; the builder lemmas are
the tree's idiom: `PipelineBodyStep.lean:1702`, and a second copy at
`JsonStage2WalkScopeGeom.lean:989`).  One copy is restated here rather than
importing either module, and the two canonical sites are named so the
duplication is visible.

**The counts and `htok`.**  `if.then81` moves the carry's `tok` by two and
`terms` by three; `if.then334` by two and seven.  `Stage2NoEventWalkInv.count` is
the transport, and the counts' guard is derived once rather than assumed:
`Stage2NoEventWalkInv.htok` gives `K.tok + c ≤ K.n` from the invariant's entry
bound (`inside`, through `pos_lt`) and the count-token relation
`K.tok + c ≤ K.pos`, and `link_ifThen81_of_bound`/`link_ifThen334_of_bound` are
the two count links with that derivation supplying the guard.  The raw `htok`
hypothesis survives only inside those two `_of_bound` proofs.

**The read rows.**  `if.then343` and `if.then350` wrap their 32-bit depth word
into `%stk`'s address and load one byte.  Each is three declarations — the
depth+`zext`, the `gep i8` at an abstract `{a}`, and the `load8` at `a` — composed
by `denoteCode_append_apply`, with `ha : a = closeReadAddr stk X` keeping the
address term out of every type.  That is decisions (w8)–(w10): the split removes
the composed term, the abstract address keeps the load row small, and the
composition splits the list once through the tree's `denoteCode_append` (imported
from `JsonEntrySteps`; the apply form is restated here).

**The base step and the head.**  The imported bootstrap covers the entry block's
first twelve instructions; the rest of the block is the five entry-suffix
sub-rows composed by `denoteCode_append_apply`, its terminator's `execTerm`, the
preheader's fourteen geps and its `br`, and the head's own run (`loopHead_denote`,
`link_loopHead`).  `baseHeadPhi_denote` states the head's nine-`phi` zero seed,
and `chain_open123`/`chain_close125` are the head's two dispatch chains to their
arms' entries.

**The `if.then9` link and the joins.**  `link_ifThen9` composes the seven-`phi`
run, the depth guard at the phi cells (`ifThen9Env1`), and the false arm to
`if.end19`.  From there the open arm is a depth case split: `link_ifEnd19_true`
at the zero depth and `stage2NoEventRow_bracePush` at a live one both reach
`if.end23`, then `if.end74`'s next-entry read (`link_ifEnd74`), the
`NodeBlock21`/`LeafBlock19` dispatch, and the empty-object close at `if.then81`
(`stage2NoEventRow_braceCloseTail`).  The close arm is the bracket's push
(`stage2NoEventRow_bracketPush`), the next-entry `]` read
(`link_ifEnd327peel`), the derived count row (`row_closeBracket_of_bound`), and
the pop (`link_closeArr`/`link_ifThen350`) in `stage2NoEventRow_closePush`.

**The container class.**  `stage2NoEventWalkContainerClass` is the class's one
theorem: from the head state it runs `{`'s dispatch and the `if.then9` guard into
the zero-depth arm, reaching `close_obj` with `K` to `{tok + 2, terms + 3}`, and
`[`'s dispatch and the zero-depth bracket arm through the `]` count to
`after_value` with `K` to `{tok + 2, terms + 7}`, each with
`Stage2NoEventWalkInv` at its own exit.  The live-depth arms are
`stage2NoEventRow_openBrace`'s push branch and `stage2NoEventRow_closePush`; the
`Stage2NoEventWalkContainerClass` structure is the intermediate arms-entries
statement.  The class statement is the invariant's own fields at the exit — no
`Is` instance and no external counter — and the count guards are the
bound-derived ones.
-/
import LeanLLVM.Refinement.JsonStage2NoEventWalkLoop
import LeanLLVM.Refinement.JsonEntrySteps

set_option autoImplicit false
set_option maxRecDepth 8192

namespace LeanLLVM.Refinement

open LeanLLVM
open LeanLLVM.Refinement.JsonStage2NoEventIR
open LeanLLVM.Refinement.BlockEval
open LeanLLVM.Refinement.JsonS1MasksIR (evalInstr_store evalOperands_cons)

/-! ### Lookups through the builder

`cells` is a right fold whose cons equation is definitional.  These are the
builder-level lookups the rows use; canonical copies are `PipelineBodyStep`'s and
`JsonStage2WalkScopeGeom`'s, restated here so this module does not import either.
-/

/-- A list-level lookup reads through the builder. -/
private theorem lookupName_cells_of_some :
    ∀ (cs : List (String × Value)) (n : String) (env : Env) {v : Value},
      lookupName cs n = some v → lookupName (cells cs env) n = some v
  | [], n, env, v, h => by simp only [lookupName_nil] at h; cases h
  | (k, w) :: cs, n, env, v, h => by
      by_cases hkn : k = n
      · subst hkn
        simp only [lookupName_cons_self] at h
        cases h
        exact lookupName_cons_self k w (cells cs env)
      · simp only [lookupName_cons_ne w cs hkn] at h
        simp only [cells, lookupName_cons_ne w (cells cs env) hkn]
        exact lookupName_cells_of_some cs n env h

/-- A name the builder does not bind reads through to the incoming environment. -/
private theorem lookupName_cells_of_notin :
    ∀ (cs : List (String × Value)) (n : String) (env : Env),
      n ∉ cs.map (·.1) → lookupName (cells cs env) n = lookupName env n
  | [], _, _, _ => rfl
  | (k, v) :: cs, n, env, h => by
      have hk : k ≠ n := by intro hkn; exact h (by subst hkn; simp)
      simp only [cells, lookupName_cons_ne v (cells cs env) hk]
      exact lookupName_cells_of_notin cs n env (fun hc => h (List.mem_cons_of_mem _ hc))

/-- A lookup in a cell list, at its head or behind bindings of other names. -/
macro "cells_lk" : tactic => `(tactic|
  (repeat rw [lookupName_cons_ne _ _ (by decide)]
   first | rw [lookupName_cons_self] | rfl))

/-! ### The carry across a count store -/

/-- The invariant across a count store: only `tokLe` moves, and `htok` is it. -/
theorem Stage2NoEventWalkInv.count {K : Stage2NoEventWalkCarry} {mem : Mem}
    {s : State} (h : Stage2NoEventWalkInv K mem s) {t c : Nat}
    (htok : K.tok + t ≤ K.n) :
    Stage2NoEventWalkInv { K with tok := K.tok + t, terms := K.terms + c } mem s := by
  refine { h with tokLe := ?_ }
  exact htok

/-! ### The `}` blocks, pinned -/

/-- `if.then81`: the brace's closer counts. -/
def ifThen81Block : Block :=
  { name := "if.then81",
    instrs :=
      [ Instr.binop "%inc82" BinOp.add 64 (Operand.reg "%k.0.lcssa1086")
          (Operand.imm (.int 64 (BitVec.ofNat 64 2))),
        Instr.binop "%inc84" BinOp.add 64 (Operand.reg "%tokens.0.lcssa1074")
          (Operand.imm (.int 64 (BitVec.ofNat 64 2))),
        Instr.binop "%add85" BinOp.add 64 (Operand.reg "%terms.0.lcssa1080")
          (Operand.imm (.int 64 (BitVec.ofNat 64 3))) ],
    term := Term.br "close_obj" }

theorem ifThen81Block_find :
    stage2NoEventBody.findBlock "if.then81" = some ifThen81Block := by
  decide

/-- `close_obj`'s six-`phi` run, the edge's. -/
def closeObjPhiInstrs : List Instr :=
  [ Instr.phi "%sp.2" (Ty.int 32)
      [("if.then81", (Operand.reg "%inc24")), ("do.body391", (Operand.reg "%sp.4"))],
    Instr.phi "%k.4" (Ty.int 64)
      [("if.then81", (Operand.reg "%inc82")), ("do.body391", (Operand.reg "%inc379"))],
    Instr.phi "%alen.6" (Ty.int 64)
      [("if.then81", (Operand.reg "%alen.0.ph1405")),
       ("do.body391", (Operand.reg "%alen.8"))],
    Instr.phi "%arena.8" (Ty.int 64)
      [("if.then81", (Operand.reg "%arena.0.ph1406")),
       ("do.body391", (Operand.reg "%arena.10"))],
    Instr.phi "%terms.6" (Ty.int 64)
      [("if.then81", (Operand.reg "%add85")), ("do.body391", (Operand.reg "%add393"))],
    Instr.phi "%tokens.6" (Ty.int 64)
      [("if.then81", (Operand.reg "%inc84")), ("do.body391", (Operand.reg "%inc392"))] ]

/-- `close_obj`'s two instructions after the `phi` run. -/
def closeObjRest : List Instr :=
  [ Instr.binop "%dec" BinOp.add 32 (Operand.reg "%sp.2")
      (Operand.imm (.int 32 (BitVec.ofNat 32 4294967295))),
    Instr.icmp "%tobool342.not" IPred.eq 32 (Operand.reg "%dec")
      (Operand.imm (.int 32 (BitVec.ofNat 32 0))) ]

/-- `close_obj`, pinned. -/
def closeObjBlock : Block :=
  { name := "close_obj", instrs := closeObjPhiInstrs ++ closeObjRest,
    term := Term.condbr (Operand.reg "%tobool342.not") "after_value" "if.then343" }

theorem closeObjBlock_find :
    stage2NoEventBody.findBlock "close_obj" = some closeObjBlock := by
  decide

/-- The block's split: the edge's `phi` run, then the decrement and its test. -/
theorem closeObj_split : closeObjBlock.instrs = closeObjPhiInstrs ++ closeObjRest := rfl

/-! ### The `]` blocks, pinned -/

/-- `if.then334`'s four-`phi` run, the edge's. -/
def ifThen334PhiInstrs : List Instr :=
  [ Instr.phi "%sp.0.lcssa1096.wide" (Ty.int 32)
      [("if.end327.peel", (Operand.reg "%sp.0.ph1403")),
       ("if.then334.loopexit", (Operand.reg "%48"))],
    Instr.phi "%k.0.lcssa1090" (Ty.int 64)
      [("if.end327.peel", (Operand.reg "%k.0.ph1404")),
       ("if.then334.loopexit", (Operand.reg "%k.0"))],
    Instr.phi "%terms.0.lcssa1084" (Ty.int 64)
      [("if.end327.peel", (Operand.reg "%terms.0.ph1407")),
       ("if.then334.loopexit", (Operand.reg "%terms.0"))],
    Instr.phi "%tokens.0.lcssa1078" (Ty.int 64)
      [("if.end327.peel", (Operand.reg "%tokens.0.ph1408")),
       ("if.then334.loopexit", (Operand.reg "%tokens.0"))] ]

/-- `if.then334`'s three counts after its `phi` run. -/
def ifThen334Rest : List Instr :=
  [ Instr.binop "%inc335" BinOp.add 64 (Operand.reg "%k.0.lcssa1090")
      (Operand.imm (.int 64 (BitVec.ofNat 64 2))),
    Instr.binop "%inc337" BinOp.add 64 (Operand.reg "%tokens.0.lcssa1078")
      (Operand.imm (.int 64 (BitVec.ofNat 64 2))),
    Instr.binop "%add338" BinOp.add 64 (Operand.reg "%terms.0.lcssa1084")
      (Operand.imm (.int 64 (BitVec.ofNat 64 7))) ]

/-- `if.then334`, pinned. -/
def ifThen334Block : Block :=
  { name := "if.then334", instrs := ifThen334PhiInstrs ++ ifThen334Rest,
    term := Term.br "close_arr" }

theorem ifThen334Block_find :
    stage2NoEventBody.findBlock "if.then334" = some ifThen334Block := by
  decide

/-- The block's split: the edge's `phi` run, then the counts. -/
theorem ifThen334_split :
    ifThen334Block.instrs = ifThen334PhiInstrs ++ ifThen334Rest := rfl

/-- `close_arr`'s seven-`phi` run, the edge's. -/
def closeArrPhiInstrs : List Instr :=
  [ Instr.phi "%frame.4" (Ty.int 8)
      [("do.body417", (Operand.reg "%frame.6")),
       ("if.then334", (Operand.imm (.int 8 (BitVec.ofNat 8 1))))],
    Instr.phi "%sp.3" (Ty.int 32)
      [("do.body417", (Operand.reg "%54")),
       ("if.then334", (Operand.reg "%sp.0.lcssa1096.wide"))],
    Instr.phi "%k.5" (Ty.int 64)
      [("do.body417", (Operand.reg "%inc379")),
       ("if.then334", (Operand.reg "%inc335"))],
    Instr.phi "%alen.7" (Ty.int 64)
      [("do.body417", (Operand.reg "%alen.8")),
       ("if.then334", (Operand.reg "%alen.0.ph1405"))],
    Instr.phi "%arena.9" (Ty.int 64)
      [("do.body417", (Operand.reg "%arena.10")),
       ("if.then334", (Operand.reg "%arena.0.ph1406"))],
    Instr.phi "%terms.7" (Ty.int 64)
      [("do.body417", (Operand.reg "%add419")),
       ("if.then334", (Operand.reg "%add338"))],
    Instr.phi "%tokens.7" (Ty.int 64)
      [("do.body417", (Operand.reg "%inc418")),
       ("if.then334", (Operand.reg "%inc337"))] ]

/-- `close_arr`'s one instruction after its `phi` run. -/
def closeArrRest : List Instr :=
  [ Instr.icmp "%tobool349.not" IPred.eq 32 (Operand.reg "%sp.3")
      (Operand.imm (.int 32 (BitVec.ofNat 32 0))) ]

/-- `close_arr`, pinned. -/
def closeArrBlock : Block :=
  { name := "close_arr", instrs := closeArrPhiInstrs ++ closeArrRest,
    term := Term.condbr (Operand.reg "%tobool349.not") "after_value" "if.then350" }

theorem closeArrBlock_find :
    stage2NoEventBody.findBlock "close_arr" = some closeArrBlock := by
  decide

/-- The block's split: the edge's `phi` run, then the zero test. -/
theorem closeArr_split :
    closeArrBlock.instrs = closeArrPhiInstrs ++ closeArrRest := rfl

-- The four pins are the parsed body's.
#guard decide (stage2NoEventBody.findBlock "if.then81" ≠ none)
#guard decide (stage2NoEventBody.findBlock "close_obj" ≠ none)
#guard decide (stage2NoEventBody.findBlock "if.then334" ≠ none)
#guard decide (stage2NoEventBody.findBlock "close_arr" ≠ none)
#guard decide (stage2NoEventBody.findBlock "if.then343" ≠ none)
#guard decide (stage2NoEventBody.findBlock "if.then350" ≠ none)

/-- `if.then343`: the frame byte below the depth. -/
def ifThen343Block : Block :=
  { name := "if.then343",
    instrs :=
      [ Instr.binop "%sub344" BinOp.add 32 (Operand.reg "%sp.2")
          (Operand.imm (.int 32 (BitVec.ofNat 32 4294967294))),
        Instr.zext "%idxprom345" 32 64 (Operand.reg "%sub344"),
        Instr.gep "%arrayidx346" (Ty.int 8) (Operand.reg "%stk")
          (Operand.reg "%idxprom345"),
        Instr.load "%49" (Ty.int 8) (Operand.reg "%arrayidx346") ],
    term := Term.br "after_value" }

theorem ifThen343Block_find :
    stage2NoEventBody.findBlock "if.then343" = some ifThen343Block := by
  decide

/-- `if.then350`: the frame byte below the depth. -/
def ifThen350Block : Block :=
  { name := "if.then350",
    instrs :=
      [ Instr.binop "%sub351" BinOp.add 32 (Operand.reg "%sp.3")
          (Operand.imm (.int 32 (BitVec.ofNat 32 4294967295))),
        Instr.zext "%idxprom352" 32 64 (Operand.reg "%sub351"),
        Instr.gep "%arrayidx353" (Ty.int 8) (Operand.reg "%stk")
          (Operand.reg "%idxprom352"),
        Instr.load "%50" (Ty.int 8) (Operand.reg "%arrayidx353") ],
    term := Term.br "after_value" }

theorem ifThen350Block_find :
    stage2NoEventBody.findBlock "if.then350" = some ifThen350Block := by
  decide

/-! ### The named environments -/

/-- The cell list `if.then81` binds. -/
def ifThen81Cells (k tok terms : BitVec 64) : List (String × Value) :=
  [("%add85", .int 64 (terms + BitVec.ofNat 64 3)),
   ("%inc84", .int 64 (tok + BitVec.ofNat 64 2)),
   ("%inc82", .int 64 (k + BitVec.ofNat 64 2))]

/-- The environment the edge's `phi` run delivers at `close_obj`, as a cell list. -/
def closeObjCells (sp2 : BitVec 32) (k4 alen arena terms6 toks : BitVec 64) :
    List (String × Value) :=
  [("%sp.2", .int 32 sp2), ("%k.4", .int 64 k4), ("%alen.6", .int 64 alen),
   ("%arena.8", .int 64 arena), ("%terms.6", .int 64 terms6),
   ("%tokens.6", .int 64 toks)]

/-- The cells `close_obj`'s suffix adds. -/
def closeObjTail (sp2 : BitVec 32) : List (String × Value) :=
  [("%tobool342.not", .int 1 (evalICmp .eq
      (sp2 + BitVec.ofNat 32 4294967295) (BitVec.ofNat 32 0))),
   ("%dec", .int 32 (sp2 + BitVec.ofNat 32 4294967295))]

/-- The cell list `if.then334`'s counts bind. -/
def ifThen334Cells (k tok terms : BitVec 64) : List (String × Value) :=
  [("%add338", .int 64 (terms + BitVec.ofNat 64 7)),
   ("%inc337", .int 64 (tok + BitVec.ofNat 64 2)),
   ("%inc335", .int 64 (k + BitVec.ofNat 64 2))]

/-- The environment the edge's `phi` run delivers at `close_arr`, as a cell list. -/
def closeArrCells (frame : BitVec 8) (sp3 : BitVec 32)
    (k5 alen arena terms7 toks : BitVec 64) : List (String × Value) :=
  [("%frame.4", .int 8 frame), ("%sp.3", .int 32 sp3),
   ("%k.5", .int 64 k5), ("%alen.7", .int 64 alen), ("%arena.9", .int 64 arena),
   ("%terms.7", .int 64 terms7), ("%tokens.7", .int 64 toks)]

/-- The cells `close_arr`'s suffix adds. -/
def closeArrTail (sp3 : BitVec 32) : List (String × Value) :=
  [("%tobool349.not", .int 1 (evalICmp .eq sp3 (BitVec.ofNat 32 0)))]

/-! ### The `}` rows -/

/-- `if.then81`'s three counts. -/
theorem ifThen81_denote (calls : Calls) (env : Env) (s : State)
    {k tok terms : BitVec 64}
    (hk : lookupName env "%k.0.lcssa1086" = some (.int 64 k))
    (htokr : lookupName env "%tokens.0.lcssa1074" = some (.int 64 tok))
    (htr : lookupName env "%terms.0.lcssa1080" = some (.int 64 terms)) :
    denoteCode calls ifThen81Block.instrs (stateAt env s) =
      some (stateAt (cells (ifThen81Cells k tok terms) env) s) := by
  rw [ifThen81Block]
  rw [stage2NoEventWalk_denote_add_imm_w (calls := calls) (env := env) (s := s)
    (d := "%inc82") (a := "%k.0.lcssa1086") (w := 64) hk]
  rw [stage2NoEventWalk_denote_add_imm_w (calls := calls) (env := _) (s := s)
    (d := "%inc84") (a := "%tokens.0.lcssa1074") (w := 64) (x := tok)
    (by rw [lookupName_cons_ne _ _ (by decide)]; exact htokr)]
  rw [stage2NoEventWalk_denote_add_imm_w (calls := calls) (env := _) (s := s)
    (d := "%add85") (a := "%terms.0.lcssa1080") (w := 64) (x := terms)
    (by rw [lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide)]; exact htr)]
  simp only [ifThen81Cells, cells, denoteCode_nil]

/-- `close_obj`'s suffix: the decrement and its test, at the edge's environment. -/
theorem closeObjRest_denote (calls : Calls) (env : Env) (s : State)
    {sp2 : BitVec 32} {k4 alen arena terms6 toks : BitVec 64} :
    denoteCode calls closeObjRest
        (stateAt (cells (closeObjCells sp2 k4 alen arena terms6 toks) env) s) =
      some (stateAt (cells (closeObjTail sp2 ++
        closeObjCells sp2 k4 alen arena terms6 toks) env) s) := by
  rw [closeObjRest]
  rw [stage2NoEventWalk_denote_add_imm_w (calls := calls)
    (env := cells (closeObjCells sp2 k4 alen arena terms6 toks) env) (s := s)
    (d := "%dec") (a := "%sp.2") (w := 32) (x := sp2)
    (lookupName_cells_of_some (cs := closeObjCells sp2 k4 alen arena terms6 toks)
      (n := "%sp.2") (env := env) (by rw [closeObjCells]; cells_lk))]
  rw [stage2NoEventWalk_denote_icmp_imm (calls := calls) (env := _) (s := s)
    (d := "%tobool342.not") (a := "%dec") (p := .eq) (w := 32)
    (x := sp2 + BitVec.ofNat 32 4294967295) (c := BitVec.ofNat 32 0)
    (by simp only [lookupName_cons_self]) (is := [])]
  rw [closeObjTail, denoteCode_nil]
  rfl

/-! ### The `]` rows -/

/-- The cell list the edge's `phi` run delivers at `if.then334`. -/
def ifThen334InCells (sp : BitVec 32) (k tok terms : BitVec 64) : List (String × Value) :=
  [("%sp.0.lcssa1096.wide", .int 32 sp), ("%k.0.lcssa1090", .int 64 k),
   ("%terms.0.lcssa1084", .int 64 terms), ("%tokens.0.lcssa1078", .int 64 tok)]

/-- `if.then334`'s three counts after the edge's `phi` run. -/
theorem ifThen334_denote (calls : Calls) (env : Env) (s : State)
    {sp : BitVec 32} {k tok terms : BitVec 64} :
    denoteCode calls ifThen334Rest
        (stateAt (cells (ifThen334InCells sp k tok terms) env) s) =
      some (stateAt (cells (ifThen334Cells k tok terms ++
        ifThen334InCells sp k tok terms) env) s) := by
  rw [ifThen334Rest]
  rw [stage2NoEventWalk_denote_add_imm_w (calls := calls)
    (env := cells (ifThen334InCells sp k tok terms) env) (s := s)
    (d := "%inc335") (a := "%k.0.lcssa1090") (w := 64) (x := k)
    (lookupName_cells_of_some (cs := ifThen334InCells sp k tok terms)
      (n := "%k.0.lcssa1090") (env := env) (by rw [ifThen334InCells]; cells_lk))]
  rw [stage2NoEventWalk_denote_add_imm_w (calls := calls)
    (env := ("%inc335", .int 64 (k + BitVec.ofNat 64 2)) ::
      cells (ifThen334InCells sp k tok terms) env) (s := s)
    (d := "%inc337") (a := "%tokens.0.lcssa1078") (w := 64) (x := tok)
    (by rw [lookupName_cons_ne _ _ (by decide),
      lookupName_cells_of_some (cs := ifThen334InCells sp k tok terms)
        (n := "%tokens.0.lcssa1078") (env := env) (by rw [ifThen334InCells]; cells_lk)])]
  rw [stage2NoEventWalk_denote_add_imm_w (calls := calls)
    (env := ("%inc337", .int 64 (tok + BitVec.ofNat 64 2)) ::
      ("%inc335", .int 64 (k + BitVec.ofNat 64 2)) ::
      cells (ifThen334InCells sp k tok terms) env) (s := s)
    (d := "%add338") (a := "%terms.0.lcssa1084") (w := 64) (x := terms)
    (by rw [lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide),
      lookupName_cells_of_some (cs := ifThen334InCells sp k tok terms)
        (n := "%terms.0.lcssa1084") (env := env) (by rw [ifThen334InCells]; cells_lk)])]
  rw [ifThen334Cells, denoteCode_nil]
  rfl

/-- `close_arr`'s suffix: the zero test of the popped depth. -/
theorem closeArrRest_denote (calls : Calls) (env : Env) (s : State)
    {frame : BitVec 8} {sp3 : BitVec 32} {k5 alen arena terms7 toks : BitVec 64} :
    denoteCode calls closeArrRest
        (stateAt (cells (closeArrCells frame sp3 k5 alen arena terms7 toks) env) s) =
      some (stateAt (cells (closeArrTail sp3 ++
        closeArrCells frame sp3 k5 alen arena terms7 toks) env) s) := by
  rw [closeArrRest]
  rw [stage2NoEventWalk_denote_icmp_imm (calls := calls)
    (env := cells (closeArrCells frame sp3 k5 alen arena terms7 toks) env) (s := s)
    (d := "%tobool349.not") (a := "%sp.3") (p := .eq) (w := 32)
    (x := sp3) (c := BitVec.ofNat 32 0)
    (lookupName_cells_of_some (cs := closeArrCells frame sp3 k5 alen arena terms7 toks)
      (n := "%sp.3") (env := env) (by rw [closeArrCells]; cells_lk)) (is := [])]
  rw [closeArrTail, denoteCode_nil]
  rfl


/-! ### The read rows: three declarations, composed by the split lemma

A read wraps a 32-bit depth word into the stack's address and loads one byte at
it.  Stated whole, the address and the environment sat in one declaration's type
and the kernel's reduction ran out of room (decision (w8)); a single address split
still carried the address in the `gep` lemma's conclusion, so (decisions (w9),
(w10)) the row is three declarations composed by transitivity, and the address is
a **variable** with an equation:

| declaration | what it computes |
|---|---|
| `…_addzext_denote` | the depth word and its `zext` |
| `…_gep_denote` | the `gep i8` at an abstract address `a` |
| `…_load_denote` | the one byte at `a` |

The composition splits the instruction list once, through the tree's
`denoteCode_append_apply` shape (`JsonS1BlocksRefine.lean:2740`, base
`denoteCode_append` at `JsonEntrySteps.lean:93`), restated here rather than
importing either module — the same precedent as the builder lookups above. -/

/-- A straight-line sequence splits at a known state: `JsonS1BlocksRefine`'s
`denoteCode_append_apply`, restated on the base lemma now imported. -/
theorem denoteCode_append_apply {calls : Calls} {a b : List Instr} {s s' : State}
    (h : denoteCode calls a s = some s') (hb : startsWithPhi b = false) :
    denoteCode calls (a ++ b) s = denoteCode calls b s' := by
  rw [LeanLLVM.Refinement.JsonEntrySteps.denoteCode_append (hb := hb), h]
  rfl

/-- The address a closer reads the frame byte at. -/
def closeReadAddr (stk : Nat) (dp : Nat) : Nat := stk + dp

/-- The cells the address computation's first half binds. -/
def closeIdxCells (sub : BitVec 32) : List (String × Value) :=
  [("%idxprom345", .int 64 (BitVec.ofNat 64 sub.toNat)), ("%sub344", .int 32 sub)]

/-- The one cell the `gep i8` binds. -/
def closeGepCells (a : Nat) : List (String × Value) :=
  [("%arrayidx346", .ptr a)]

/-- `if.then343`: the depth word and its zero extension. -/
theorem ifThen343_addzext_denote (calls : Calls) (env : Env) (s : State)
    {sp2 : BitVec 32}
    (hsp2 : lookupName env "%sp.2" = some (.int 32 sp2)) :
    denoteCode calls
        [ Instr.binop "%sub344" BinOp.add 32 (Operand.reg "%sp.2")
            (Operand.imm (.int 32 (BitVec.ofNat 32 4294967294))),
          Instr.zext "%idxprom345" 32 64 (Operand.reg "%sub344") ]
        (stateAt env s) =
      some (stateAt (cells (closeIdxCells (sp2 + BitVec.ofNat 32 4294967294)) env) s) := by
  rw [stage2NoEventWalk_denote_add_imm_w (calls := calls) (env := env) (s := s)
    (d := "%sub344") (a := "%sp.2") (w := 32) (x := sp2) hsp2]
  rw [denoteCode_zext (calls := calls) (env := _) (s := s) (d := "%idxprom345")
    (v := "%sub344") (wIn := 32) (wOut := 64)
    (x := sp2 + BitVec.ofNat 32 4294967294) (by simp only [lookupName_cons_self])]
  rw [closeIdxCells, denoteCode_nil]
  rfl

/-- `if.then343`: the `gep i8` at an abstract address. -/
theorem ifThen343_gep_denote (calls : Calls) (env : Env) (s : State) {stk : Nat}
    {sub : BitVec 32} {a : Nat}
    (ha : a = closeReadAddr stk sub.toNat)
    (hstk : lookupName env "%stk" = some (.ptr stk)) :
    denoteCode calls
        [ Instr.gep "%arrayidx346" (Ty.int 8) (Operand.reg "%stk")
            (Operand.reg "%idxprom345") ]
        (stateAt (cells (closeIdxCells sub) env) s) =
      some (stateAt (cells (closeGepCells a) (cells (closeIdxCells sub) env)) s) := by
  rw [denoteCode_gep8_reg (calls := calls)
    (env := cells (closeIdxCells sub) env) (s := s)
    (d := "%arrayidx346") (base := "%stk") (off := "%idxprom345") (a := stk)
    (idx := BitVec.ofNat 64 sub.toNat)
    (by rw [lookupName_cells_of_notin (cs := closeIdxCells sub) (n := "%stk")
      (env := env) (by rw [closeIdxCells]; simp)]; exact hstk)
    (lookupName_cells_of_some (cs := closeIdxCells sub) (n := "%idxprom345")
      (env := env) (by rw [closeIdxCells]; cells_lk))
    (by
      have hx : sub.toNat < 2 ^ 63 := by have := sub.isLt; omega
      rw [stage2NoEventSignExtend_ofNat hx]
      exact hx)]
  rw [closeGepCells, closeIdxCells, denoteCode_nil]
  have hsig : (BitVec.signExtend 64 (BitVec.ofNat 64 sub.toNat)).toNat = sub.toNat :=
    stage2NoEventSignExtend_ofNat (by have := sub.isLt; omega)
  have harg : stk + (BitVec.signExtend 64 (BitVec.ofNat 64 sub.toNat)).toNat
      = closeReadAddr stk sub.toNat := by rw [hsig]; rfl
  have haddr : stk + (BitVec.signExtend 64 (BitVec.ofNat 64 sub.toNat)).toNat = a :=
    harg.trans ha.symm
  rw [haddr]
  rfl

/-- `if.then343`: the one byte at an abstract address. -/
theorem ifThen343_load_denote (calls : Calls) (env : Env) (s : State) {a : Nat}
    {bs : List UInt8}
    (hbyte : readBytes s.mem a 1 = some bs) :
    denoteCode calls
        [ Instr.load "%49" (Ty.int 8) (Operand.reg "%arrayidx346") ]
        (stateAt (cells (closeGepCells a) env) s) =
      some (stateAt (cells
        (("%49", .int 8 (BitVec.ofNat 8 (bytesToNat bs))) :: closeGepCells a) env) s) := by
  rw [stage2NoEventWalk_denote_load_int (calls := calls)
    (env := cells (closeGepCells a) env) (s := s)
    (d := "%49") (p := "%arrayidx346") (a := a) (w := 8) (bs := bs) (hw := by decide)
    (lookupName_cells_of_some (cs := closeGepCells a) (n := "%arrayidx346") (env := env)
      (by rw [closeGepCells]; cells_lk))
    (by simpa using hbyte)]
  rw [closeGepCells, denoteCode_nil]
  rfl

/-- `if.then343` whole, composed by the split lemma. -/
theorem ifThen343_denote (calls : Calls) (env : Env) (s : State) {stk : Nat}
    {sp2 : BitVec 32} {a : Nat} {bs : List UInt8}
    (ha : a = closeReadAddr stk (sp2 + BitVec.ofNat 32 4294967294).toNat)
    (hsp2 : lookupName env "%sp.2" = some (.int 32 sp2))
    (hstk : lookupName env "%stk" = some (.ptr stk))
    (hbyte : readBytes s.mem a 1 = some bs) :
    denoteCode calls ifThen343Block.instrs (stateAt env s) =
      some (stateAt (cells (("%49", .int 8 (BitVec.ofNat 8 (bytesToNat bs))) ::
        closeGepCells a ++ closeIdxCells (sp2 + BitVec.ofNat 32 4294967294)) env) s) := by
  have h1 := ifThen343_addzext_denote (calls := calls) (env := env) (s := s) hsp2
  have h2 := ifThen343_gep_denote (calls := calls) (env := env) (s := s)
    (stk := stk) (sub := sp2 + BitVec.ofNat 32 4294967294) (a := a) ha
    hstk
  have h3 := ifThen343_load_denote (calls := calls)
    (env := cells (closeIdxCells (sp2 + BitVec.ofNat 32 4294967294)) env) (s := s)
    (a := a) hbyte
  rw [ifThen343Block, show ([Instr.binop "%sub344" BinOp.add 32 (Operand.reg "%sp.2")
        (Operand.imm (.int 32 (BitVec.ofNat 32 4294967294))),
      Instr.zext "%idxprom345" 32 64 (Operand.reg "%sub344"),
      Instr.gep "%arrayidx346" (Ty.int 8) (Operand.reg "%stk") (Operand.reg "%idxprom345"),
      Instr.load "%49" (Ty.int 8) (Operand.reg "%arrayidx346")] : List Instr)
      = [Instr.binop "%sub344" BinOp.add 32 (Operand.reg "%sp.2")
          (Operand.imm (.int 32 (BitVec.ofNat 32 4294967294))),
        Instr.zext "%idxprom345" 32 64 (Operand.reg "%sub344")] ++
        ([Instr.gep "%arrayidx346" (Ty.int 8) (Operand.reg "%stk")
          (Operand.reg "%idxprom345")] ++
          [Instr.load "%49" (Ty.int 8) (Operand.reg "%arrayidx346")]) from rfl]
  rw [denoteCode_append_apply (a := [Instr.binop "%sub344" BinOp.add 32
        (Operand.reg "%sp.2") (Operand.imm (.int 32 (BitVec.ofNat 32 4294967294))),
      Instr.zext "%idxprom345" 32 64 (Operand.reg "%sub344")])
      (b := [Instr.gep "%arrayidx346" (Ty.int 8) (Operand.reg "%stk")
        (Operand.reg "%idxprom345")] ++
        [Instr.load "%49" (Ty.int 8) (Operand.reg "%arrayidx346")]) h1 (by decide)]
  rw [denoteCode_append_apply (a := [Instr.gep "%arrayidx346" (Ty.int 8)
        (Operand.reg "%stk") (Operand.reg "%idxprom345")])
      (b := [Instr.load "%49" (Ty.int 8) (Operand.reg "%arrayidx346")]) h2 (by decide)]
  exact h3



/-- The cells `if.then350`'s address computation binds. -/
def closeIdxCells50 (sub : BitVec 32) : List (String × Value) :=
  [("%idxprom352", .int 64 (BitVec.ofNat 64 sub.toNat)), ("%sub351", .int 32 sub)]

/-- The one cell `if.then350`'s `gep i8` binds. -/
def closeGepCells50 (a : Nat) : List (String × Value) :=
  [("%arrayidx353", .ptr a)]

/-- `if.then350`: the depth word and its zero extension. -/
theorem ifThen350_addzext_denote (calls : Calls) (env : Env) (s : State)
    {sp3 : BitVec 32}
    (hsp3 : lookupName env "%sp.3" = some (.int 32 sp3)) :
    denoteCode calls
        [ Instr.binop "%sub351" BinOp.add 32 (Operand.reg "%sp.3")
            (Operand.imm (.int 32 (BitVec.ofNat 32 4294967295))),
          Instr.zext "%idxprom352" 32 64 (Operand.reg "%sub351") ]
        (stateAt env s) =
      some (stateAt (cells (closeIdxCells50 (sp3 + BitVec.ofNat 32 4294967295)) env) s) := by
  rw [stage2NoEventWalk_denote_add_imm_w (calls := calls) (env := env) (s := s)
    (d := "%sub351") (a := "%sp.3") (w := 32) (x := sp3) hsp3]
  rw [denoteCode_zext (calls := calls) (env := _) (s := s) (d := "%idxprom352")
    (v := "%sub351") (wIn := 32) (wOut := 64)
    (x := sp3 + BitVec.ofNat 32 4294967295) (by simp only [lookupName_cons_self])]
  rw [closeIdxCells50, denoteCode_nil]
  rfl

/-- `if.then350`: the `gep i8` at an abstract address. -/
theorem ifThen350_gep_denote (calls : Calls) (env : Env) (s : State) {stk : Nat}
    {sub : BitVec 32} {a : Nat}
    (ha : a = closeReadAddr stk sub.toNat)
    (hstk : lookupName env "%stk" = some (.ptr stk)) :
    denoteCode calls
        [ Instr.gep "%arrayidx353" (Ty.int 8) (Operand.reg "%stk")
            (Operand.reg "%idxprom352") ]
        (stateAt (cells (closeIdxCells50 sub) env) s) =
      some (stateAt (cells (closeGepCells50 a) (cells (closeIdxCells50 sub) env)) s) := by
  rw [denoteCode_gep8_reg (calls := calls)
    (env := cells (closeIdxCells50 sub) env) (s := s)
    (d := "%arrayidx353") (base := "%stk") (off := "%idxprom352") (a := stk)
    (idx := BitVec.ofNat 64 sub.toNat)
    (by rw [lookupName_cells_of_notin (cs := closeIdxCells50 sub) (n := "%stk")
      (env := env) (by rw [closeIdxCells50]; simp)]; exact hstk)
    (lookupName_cells_of_some (cs := closeIdxCells50 sub) (n := "%idxprom352")
      (env := env) (by rw [closeIdxCells50]; cells_lk))
    (by
      have hx : sub.toNat < 2 ^ 63 := by have := sub.isLt; omega
      rw [stage2NoEventSignExtend_ofNat hx]
      exact hx)]
  rw [closeGepCells50, closeIdxCells50, denoteCode_nil]
  have hsig : (BitVec.signExtend 64 (BitVec.ofNat 64 sub.toNat)).toNat = sub.toNat :=
    stage2NoEventSignExtend_ofNat (by have := sub.isLt; omega)
  have harg : stk + (BitVec.signExtend 64 (BitVec.ofNat 64 sub.toNat)).toNat
      = closeReadAddr stk sub.toNat := by rw [hsig]; rfl
  have haddr : stk + (BitVec.signExtend 64 (BitVec.ofNat 64 sub.toNat)).toNat = a :=
    harg.trans ha.symm
  rw [haddr]
  rfl

/-- `if.then350`: the one byte at an abstract address. -/
theorem ifThen350_load_denote (calls : Calls) (env : Env) (s : State) {a : Nat}
    {bs : List UInt8}
    (hbyte : readBytes s.mem a 1 = some bs) :
    denoteCode calls
        [ Instr.load "%50" (Ty.int 8) (Operand.reg "%arrayidx353") ]
        (stateAt (cells (closeGepCells50 a) env) s) =
      some (stateAt (cells
        (("%50", .int 8 (BitVec.ofNat 8 (bytesToNat bs))) :: closeGepCells50 a) env) s) := by
  rw [stage2NoEventWalk_denote_load_int (calls := calls)
    (env := cells (closeGepCells50 a) env) (s := s)
    (d := "%50") (p := "%arrayidx353") (a := a) (w := 8) (bs := bs) (hw := by decide)
    (lookupName_cells_of_some (cs := closeGepCells50 a) (n := "%arrayidx353") (env := env)
      (by rw [closeGepCells50]; cells_lk))
    (by simpa using hbyte)]
  rw [closeGepCells50, denoteCode_nil]
  rfl

/-- `if.then350` whole, composed by the split lemma. -/
theorem ifThen350_denote (calls : Calls) (env : Env) (s : State) {stk : Nat}
    {sp3 : BitVec 32} {a : Nat} {bs : List UInt8}
    (ha : a = closeReadAddr stk (sp3 + BitVec.ofNat 32 4294967295).toNat)
    (hsp3 : lookupName env "%sp.3" = some (.int 32 sp3))
    (hstk : lookupName env "%stk" = some (.ptr stk))
    (hbyte : readBytes s.mem a 1 = some bs) :
    denoteCode calls ifThen350Block.instrs (stateAt env s) =
      some (stateAt (cells (("%50", .int 8 (BitVec.ofNat 8 (bytesToNat bs))) ::
        closeGepCells50 a ++ closeIdxCells50 (sp3 + BitVec.ofNat 32 4294967295)) env) s) := by
  have h1 := ifThen350_addzext_denote (calls := calls) (env := env) (s := s) hsp3
  have h2 := ifThen350_gep_denote (calls := calls) (env := env) (s := s)
    (stk := stk) (sub := sp3 + BitVec.ofNat 32 4294967295) (a := a) ha hstk
  have h3 := ifThen350_load_denote (calls := calls)
    (env := cells (closeIdxCells50 (sp3 + BitVec.ofNat 32 4294967295)) env) (s := s)
    (a := a) hbyte
  rw [ifThen350Block, show ([Instr.binop "%sub351" BinOp.add 32 (Operand.reg "%sp.3")
        (Operand.imm (.int 32 (BitVec.ofNat 32 4294967295))),
      Instr.zext "%idxprom352" 32 64 (Operand.reg "%sub351"),
      Instr.gep "%arrayidx353" (Ty.int 8) (Operand.reg "%stk") (Operand.reg "%idxprom352"),
      Instr.load "%50" (Ty.int 8) (Operand.reg "%arrayidx353")] : List Instr)
      = [Instr.binop "%sub351" BinOp.add 32 (Operand.reg "%sp.3")
          (Operand.imm (.int 32 (BitVec.ofNat 32 4294967295))),
        Instr.zext "%idxprom352" 32 64 (Operand.reg "%sub351")] ++
        ([Instr.gep "%arrayidx353" (Ty.int 8) (Operand.reg "%stk")
          (Operand.reg "%idxprom352")] ++
          [Instr.load "%50" (Ty.int 8) (Operand.reg "%arrayidx353")]) from rfl]
  rw [denoteCode_append_apply (a := [Instr.binop "%sub351" BinOp.add 32
        (Operand.reg "%sp.3") (Operand.imm (.int 32 (BitVec.ofNat 32 4294967295))),
      Instr.zext "%idxprom352" 32 64 (Operand.reg "%sub351")])
      (b := [Instr.gep "%arrayidx353" (Ty.int 8) (Operand.reg "%stk")
        (Operand.reg "%idxprom352")] ++
        [Instr.load "%50" (Ty.int 8) (Operand.reg "%arrayidx353")]) h1 (by decide)]
  rw [denoteCode_append_apply (a := [Instr.gep "%arrayidx353" (Ty.int 8)
        (Operand.reg "%stk") (Operand.reg "%idxprom352")])
      (b := [Instr.load "%50" (Ty.int 8) (Operand.reg "%arrayidx353")]) h2 (by decide)]
  exact h3


/-! ### The `]` closer

The `]` path from the entry test to `after_value`: `if.then334`'s four `phi`s and
its counts, `close_arr`'s seven `phi`s and the depth test, and `if.then350`'s frame
read.  The `phi` runs are the edges' and are rows of their own; each block's
denotation is its `phi` row followed by its suffix row, split once through
`denoteCode_append_apply`; and the blocks chain as links, so `pre` is always the
one the previous terminator set.

Every per-hop lookup goes through the builder lemmas with the **cell list named**
(`ifThen334AllCells`/`closeArrAllCells`), never by unfolding `cells` over an
append.  The entry link `link_ifEnd327peel` moved here from
`JsonStage2NoEventWalkLoop` (decision (w6)). -/

/-- The cells `if.then334`'s `phi` run binds, newest first. -/
def ifThen334PhiCells (sp : BitVec 32) (k tok terms : BitVec 64) : List (String × Value) :=
  [("%tokens.0.lcssa1078", .int 64 tok), ("%terms.0.lcssa1084", .int 64 terms),
   ("%k.0.lcssa1090", .int 64 k), ("%sp.0.lcssa1096.wide", .int 32 sp)]

/-- The cells `close_arr`'s `phi` run binds, newest first. -/
def closeArrPhiCells (frame : BitVec 8) (sp3 : BitVec 32)
    (k5 alen arena terms7 toks : BitVec 64) : List (String × Value) :=
  [("%tokens.7", .int 64 toks), ("%terms.7", .int 64 terms7),
   ("%arena.9", .int 64 arena), ("%alen.7", .int 64 alen), ("%k.5", .int 64 k5),
   ("%sp.3", .int 32 sp3), ("%frame.4", .int 8 frame)]

/-- `if.then334`'s four `phi`s, as specs. -/
def ifThen334PhiSpecs : List PhiSpec :=
  [ ⟨"%sp.0.lcssa1096.wide", Ty.int 32,
      [("if.end327.peel", .reg "%sp.0.ph1403"), ("if.then334.loopexit", .reg "%48")]⟩,
    ⟨"%k.0.lcssa1090", Ty.int 64,
      [("if.end327.peel", .reg "%k.0.ph1404"), ("if.then334.loopexit", .reg "%k.0")]⟩,
    ⟨"%terms.0.lcssa1084", Ty.int 64,
      [("if.end327.peel", .reg "%terms.0.ph1407"), ("if.then334.loopexit", .reg "%terms.0")]⟩,
    ⟨"%tokens.0.lcssa1078", Ty.int 64,
      [("if.end327.peel", .reg "%tokens.0.ph1408"), ("if.then334.loopexit", .reg "%tokens.0")]⟩ ]

theorem ifThen334_phi_eq :
    ifThen334PhiInstrs = ifThen334PhiSpecs.map PhiSpec.instr := rfl

/-- `if.then334`'s `phi` run at the `]` entry. -/
theorem ifThen334_phi_denote (calls : Calls) (env : Env) (s : State)
    {sp : BitVec 32} {k terms tok : BitVec 64}
    (hpre : s.pre = some "if.end327.peel")
    (hsp : lookupName env "%sp.0.ph1403" = some (.int 32 sp))
    (hk : lookupName env "%k.0.ph1404" = some (.int 64 k))
    (htr : lookupName env "%terms.0.ph1407" = some (.int 64 terms))
    (htokr : lookupName env "%tokens.0.ph1408" = some (.int 64 tok)) :
    denoteCode calls ifThen334PhiInstrs (stateAt env s) =
      some (stateAt (cells (ifThen334PhiCells sp k tok terms) env) s) := by
  have hsel : PhiSelects (stateAt env s) "if.end327.peel" ifThen334PhiSpecs
      [("%sp.0.lcssa1096.wide", .int 32 sp), ("%k.0.lcssa1090", .int 64 k),
       ("%terms.0.lcssa1084", .int 64 terms), ("%tokens.0.lcssa1078", .int 64 tok)] := by
    refine PhiSelects.cons (op := .reg "%sp.0.ph1403") (by decide) ?_
      (PhiSelects.cons (op := .reg "%k.0.ph1404") (by decide) ?_
        (PhiSelects.cons (op := .reg "%terms.0.ph1407") (by decide) ?_
          (PhiSelects.cons (op := .reg "%tokens.0.ph1408") (by decide) ?_ PhiSelects.nil)))
    all_goals simp only [stateAt, evalOperand, hsp, hk, htr, htokr]
  rw [ifThen334_phi_eq, ← List.append_nil (List.map PhiSpec.instr ifThen334PhiSpecs),
    denoteCode_phiRun (s := stateAt env s) (p := "if.end327.peel")
      (specs := ifThen334PhiSpecs) (rest := [])
      (hpre := hpre) (hsel := hsel) (hrest := rfl)]
  simp only [State.bindAll, State.bind, ifThen334PhiCells, cells]
  rfl

/-- `close_arr`'s seven `phi`s, as specs. -/
def closeArrPhiSpecs : List PhiSpec :=
  [ ⟨"%frame.4", Ty.int 8,
      [("do.body417", .reg "%frame.6"),
       ("if.then334", .imm (.int 8 (BitVec.ofNat 8 1)))]⟩,
    ⟨"%sp.3", Ty.int 32,
      [("do.body417", .reg "%54"), ("if.then334", .reg "%sp.0.lcssa1096.wide")]⟩,
    ⟨"%k.5", Ty.int 64,
      [("do.body417", .reg "%inc379"), ("if.then334", .reg "%inc335")]⟩,
    ⟨"%alen.7", Ty.int 64,
      [("do.body417", .reg "%alen.8"), ("if.then334", .reg "%alen.0.ph1405")]⟩,
    ⟨"%arena.9", Ty.int 64,
      [("do.body417", .reg "%arena.10"), ("if.then334", .reg "%arena.0.ph1406")]⟩,
    ⟨"%terms.7", Ty.int 64,
      [("do.body417", .reg "%add419"), ("if.then334", .reg "%add338")]⟩,
    ⟨"%tokens.7", Ty.int 64,
      [("do.body417", .reg "%inc418"), ("if.then334", .reg "%inc337")]⟩ ]

theorem closeArr_phi_eq : closeArrPhiInstrs = closeArrPhiSpecs.map PhiSpec.instr := rfl

/-- `close_arr`'s `phi` run at the counts' exit. -/
theorem closeArr_phi_denote (calls : Calls) (env : Env) (s : State)
    {sp3 : BitVec 32} {k5 alen arena terms7 toks : BitVec 64}
    (hpre : s.pre = some "if.then334")
    (hsp : lookupName env "%sp.0.lcssa1096.wide" = some (.int 32 sp3))
    (hinc335 : lookupName env "%inc335" = some (.int 64 k5))
    (halen : lookupName env "%alen.0.ph1405" = some (.int 64 alen))
    (harena : lookupName env "%arena.0.ph1406" = some (.int 64 arena))
    (hadd338 : lookupName env "%add338" = some (.int 64 terms7))
    (hinc337 : lookupName env "%inc337" = some (.int 64 toks)) :
    denoteCode calls closeArrPhiInstrs (stateAt env s) =
      some (stateAt (cells (closeArrPhiCells (BitVec.ofNat 8 1) sp3 k5 alen arena
        terms7 toks) env) s) := by
  have hsel : PhiSelects (stateAt env s) "if.then334" closeArrPhiSpecs
      [("%frame.4", .int 8 (BitVec.ofNat 8 1)), ("%sp.3", .int 32 sp3),
       ("%k.5", .int 64 k5), ("%alen.7", .int 64 alen), ("%arena.9", .int 64 arena),
       ("%terms.7", .int 64 terms7), ("%tokens.7", .int 64 toks)] := by
    refine PhiSelects.cons (op := .imm (.int 8 (BitVec.ofNat 8 1))) (by decide) ?_
      (PhiSelects.cons (op := .reg "%sp.0.lcssa1096.wide") (by decide) ?_
        (PhiSelects.cons (op := .reg "%inc335") (by decide) ?_
          (PhiSelects.cons (op := .reg "%alen.0.ph1405") (by decide) ?_
            (PhiSelects.cons (op := .reg "%arena.0.ph1406") (by decide) ?_
              (PhiSelects.cons (op := .reg "%add338") (by decide) ?_
                (PhiSelects.cons (op := .reg "%inc337") (by decide) ?_ PhiSelects.nil))))))
    all_goals
      first
      | (simp only [stateAt, evalOperand]; rfl)
      | (simp only [stateAt, evalOperand, hsp, hinc335, halen, harena, hadd338, hinc337])
  rw [closeArr_phi_eq, ← List.append_nil (List.map PhiSpec.instr closeArrPhiSpecs),
    denoteCode_phiRun (s := stateAt env s) (p := "if.then334")
      (specs := closeArrPhiSpecs) (rest := [])
      (hpre := hpre) (hsel := hsel) (hrest := rfl)]
  simp only [State.bindAll, State.bind, closeArrPhiCells, cells]
  rfl

/-- The composed cell list `if.then334`'s counts and its edge bind. -/
def ifThen334AllCells (sp : BitVec 32) (k tok terms : BitVec 64) : List (String × Value) :=
  ifThen334Cells k tok terms ++ ifThen334PhiCells sp k tok terms

/-- The composed cell list `close_arr`'s test and its edge bind. -/
def closeArrAllCells (sp3 : BitVec 32) (k5 alen arena terms7 toks : BitVec 64) :
    List (String × Value) :=
  closeArrTail sp3 ++ closeArrPhiCells (BitVec.ofNat 8 1) sp3 k5 alen arena terms7 toks

/-- `if.then334`'s counts at the `phi` run's cells. -/
theorem ifThen334_counts_denote (calls : Calls) (env : Env) (s : State)
    {sp : BitVec 32} {k terms tok : BitVec 64} :
    denoteCode calls ifThen334Rest
        (stateAt (cells (ifThen334PhiCells sp k tok terms) env) s) =
      some (stateAt (cells (ifThen334AllCells sp k tok terms) env) s) := by
  rw [ifThen334Rest]
  rw [stage2NoEventWalk_denote_add_imm_w (calls := calls)
    (env := cells (ifThen334PhiCells sp k tok terms) env) (s := s)
    (d := "%inc335") (a := "%k.0.lcssa1090") (w := 64) (x := k)
    (lookupName_cells_of_some (cs := ifThen334PhiCells sp k tok terms)
      (n := "%k.0.lcssa1090") (env := env)
      (by rw [ifThen334PhiCells]; cells_lk))]
  rw [stage2NoEventWalk_denote_add_imm_w (calls := calls) (env := _) (s := s)
    (d := "%inc337") (a := "%tokens.0.lcssa1078") (w := 64) (x := tok)
    (by rw [lookupName_cons_ne _ _ (by decide),
      lookupName_cells_of_some (cs := ifThen334PhiCells sp k tok terms)
        (n := "%tokens.0.lcssa1078") (env := env)
        (by rw [ifThen334PhiCells]; cells_lk)])]
  rw [stage2NoEventWalk_denote_add_imm_w (calls := calls) (env := _) (s := s)
    (d := "%add338") (a := "%terms.0.lcssa1084") (w := 64) (x := terms)
    (by rw [lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide),
      lookupName_cells_of_some (cs := ifThen334PhiCells sp k tok terms)
        (n := "%terms.0.lcssa1084") (env := env)
        (by rw [ifThen334PhiCells]; cells_lk)])]
  rw [ifThen334AllCells, ifThen334Cells, ifThen334PhiCells, cells, denoteCode_nil]
  rfl

/-- `close_arr`'s depth test at the `phi` run's cells. -/
theorem closeArr_test_denote (calls : Calls) (env : Env) (s : State)
    {sp3 : BitVec 32} {k5 alen arena terms7 toks : BitVec 64} :
    denoteCode calls closeArrRest
        (stateAt (cells (closeArrPhiCells (BitVec.ofNat 8 1) sp3 k5 alen arena
          terms7 toks) env) s) =
      some (stateAt (cells (closeArrAllCells sp3 k5 alen arena terms7 toks) env) s) := by
  rw [closeArrRest]
  rw [stage2NoEventWalk_denote_icmp_imm (calls := calls)
    (env := cells (closeArrPhiCells (BitVec.ofNat 8 1) sp3 k5 alen arena terms7 toks)
      env) (s := s)
    (d := "%tobool349.not") (a := "%sp.3") (p := .eq) (w := 32) (x := sp3)
    (c := BitVec.ofNat 32 0)
    (lookupName_cells_of_some (cs := closeArrPhiCells (BitVec.ofNat 8 1) sp3 k5 alen
      arena terms7 toks) (n := "%sp.3") (env := env)
      (by rw [closeArrPhiCells]; cells_lk)) (is := [])]
  rw [closeArrAllCells, closeArrTail, closeArrPhiCells, cells, denoteCode_nil]
  rfl

/-- The state `link_ifEnd327peel` delivers. -/
def bracketEntry (s : State) (inc : BitVec 64) (ep b : Nat)
    (bs4 bs1 : List UInt8) : State :=
  stage2NoEventWalkNext
    (("%cmp332.peel", .int 1 1) ::
      ("%6", .int 8 (BitVec.ofNat 8 (bytesToNat bs1))) ::
      ("%arrayidx330.peel",
        .ptr (b + (BitVec.signExtend 64 (BitVec.ofNat 64 (bytesToNat bs4))).toNat)) ::
      ("%idxprom329.peel", .int 64 (BitVec.ofNat 64 (bytesToNat bs4))) ::
      ("%5", .int 32 (BitVec.ofNat 32 (bytesToNat bs4))) ::
      ("%arrayidx328.peel", .ptr (ep + inc.toNat * 4)) :: s.env) s "if.then334"

/-- The state `if.then334` delivers. -/
def bracketCounts (s1 : State) (sp : BitVec 32) (k tok terms : BitVec 64) : State :=
  stage2NoEventWalkNext (cells (ifThen334AllCells sp k tok terms) s1.env) s1 "close_arr"

/-- The state `close_arr` delivers. -/
def bracketArr (s2 : State) (sp3 : BitVec 32) (k5 alen arena terms7 toks : BitVec 64) :
    State :=
  stage2NoEventWalkNext (cells (closeArrAllCells sp3 k5 alen arena terms7 toks) s2.env)
    s2 "if.then350"

/-- The state `if.then350` delivers. -/
def bracketRead (s3 : State) (sp3 : BitVec 32) (a : Nat) (bs : List UInt8) : State :=
  stage2NoEventWalkNext
    (cells (("%50", .int 8 (BitVec.ofNat 8 (bytesToNat bs))) ::
      closeGepCells50 a ++ closeIdxCells50 (sp3 + BitVec.ofNat 32 4294967295)) s3.env)
    s3 "after_value"

/-- `if.end327.peel` at a `]`: the closer's arm, to `if.then334`. -/
def ifEnd327peelBlock : Block :=
  { name := "if.end327.peel",
    instrs :=
      [ Instr.gep "%arrayidx328.peel" (Ty.int 32) (Operand.reg "%ep")
          (Operand.reg "%inc.peel"),
        Instr.load "%5" (Ty.int 32) (Operand.reg "%arrayidx328.peel"),
        Instr.zext "%idxprom329.peel" 32 64 (Operand.reg "%5"),
        Instr.gep "%arrayidx330.peel" (Ty.int 8) (Operand.reg "%b")
          (Operand.reg "%idxprom329.peel"),
        Instr.load "%6" (Ty.int 8) (Operand.reg "%arrayidx330.peel"),
        Instr.icmp "%cmp332.peel" IPred.eq 8 (Operand.reg "%6")
          (Operand.imm (.int 8 (BitVec.ofNat 8 93))) ],
    term := Term.condbr (Operand.reg "%cmp332.peel") "if.then334" "if.end" }

theorem ifEnd327peelBlock_find :
    stage2NoEventBody.findBlock "if.end327.peel" = some ifEnd327peelBlock := by
  decide

/-- `if.end327.peel` at a `]`: the closer's arm, to `if.then334`. -/
theorem link_ifEnd327peel {calls : Calls} {K : Stage2NoEventWalkCarry} {mem : Mem}
    {s : State} {inc : BitVec 64} {ep b : Nat} {bs4 bs1 : List UInt8}
    (h : Stage2NoEventWalkInv K mem s) (hpc : s.pc = "if.end327.peel")
    (hinc : lookupName s.env "%inc.peel" = some (.int 64 inc))
    (hep : lookupName s.env "%ep" = some (.ptr ep))
    (hb : lookupName s.env "%b" = some (.ptr b))
    (hincLt : inc.toNat < 2 ^ 63)
    (hlane : readBytes s.mem (ep + inc.toNat * 4) 4 = some bs4)
    (hlanelt : bytesToNat bs4 < 2 ^ 32)
    (hbyte : readBytes s.mem
      (b + (BitVec.signExtend 64 (BitVec.ofNat 64 (bytesToNat bs4))).toNat) 1 = some bs1)
    (hb93 : bytesToNat bs1 = 93) :
    Stage2NoEventWalkLink calls K mem s K (bracketEntry s inc ep b bs4 bs1) := by
  have hbit : evalICmp .eq (BitVec.ofNat 8 (bytesToNat bs1)) (BitVec.ofNat 8 93)
      = (1 : BitVec 1) := by
    rw [hb93]
    decide
  have hcode : denoteCode calls ifEnd327peelBlock.instrs (stateAt s.env s) =
      some (stateAt
        (("%cmp332.peel", .int 1 1) ::
          ("%6", .int 8 (BitVec.ofNat 8 (bytesToNat bs1))) ::
          ("%arrayidx330.peel",
            .ptr (b + (BitVec.signExtend 64
              (BitVec.ofNat 64 (bytesToNat bs4))).toNat)) ::
          ("%idxprom329.peel", .int 64 (BitVec.ofNat 64 (bytesToNat bs4))) ::
          ("%5", .int 32 (BitVec.ofNat 32 (bytesToNat bs4))) ::
          ("%arrayidx328.peel", .ptr (ep + inc.toNat * 4)) :: s.env) s) := by
    rw [ifEnd327peelBlock]
    rw [stage2NoEventWalk_denote_gep32 (calls := calls) (env := s.env) (s := s)
      (d := "%arrayidx328.peel") (base := "%ep") (off := "%inc.peel")
      (a := ep) (o := inc) hep hinc
      (by rw [stage2NoEventSignExtend_self]; exact hincLt)]
    rw [stage2NoEventSignExtend_self]
    rw [stage2NoEventWalk_denote_load_int (calls := calls) (env := _) (s := s)
      (d := "%5") (p := "%arrayidx328.peel") (a := ep + inc.toNat * 4) (w := 32)
      (bs := bs4) (hw := by decide) (by simp only [lookupName_cons_self])
      (by simpa using hlane)]
    rw [denoteCode_zext (calls := calls) (env := _) (s := s) (d := "%idxprom329.peel")
      (v := "%5") (wIn := 32) (wOut := 64) (x := BitVec.ofNat 32 (bytesToNat bs4))
      (by simp only [lookupName_cons_self])]
    rw [stage2NoEventOfNat32_toNat hlanelt]
    rw [denoteCode_gep8_reg (calls := calls) (env := _) (s := s)
      (d := "%arrayidx330.peel") (base := "%b") (off := "%idxprom329.peel")
      (a := b) (idx := BitVec.ofNat 64 (bytesToNat bs4))
      (by rw [lookupName_cons_ne _ _ (by decide),
        lookupName_cons_ne _ _ (by decide),
        lookupName_cons_ne _ _ (by decide)]; exact hb)
      (by simp only [lookupName_cons_self])
      (by
        have hx : (bytesToNat bs4) < 2 ^ 63 := by omega
        rw [stage2NoEventSignExtend_ofNat hx]
        exact hx)]
    rw [stage2NoEventWalk_denote_load_int (calls := calls) (env := _) (s := s)
      (d := "%6") (p := "%arrayidx330.peel")
      (a := b + (BitVec.signExtend 64 (BitVec.ofNat 64 (bytesToNat bs4))).toNat)
      (w := 8) (bs := bs1) (hw := by decide)
      (by simp only [lookupName_cons_self]) (by simpa using hbyte)]
    rw [stage2NoEventWalk_denote_icmp_imm (calls := calls) (env := _) (s := s)
      (d := "%cmp332.peel") (a := "%6") (p := .eq) (w := 8)
      (x := BitVec.ofNat 8 (bytesToNat bs1))
      (c := BitVec.ofNat 8 93) (by simp only [lookupName_cons_self]) (is := [])]
    simp only [hbit, denoteCode_nil]
  refine ⟨h, ?_, ?_⟩
  · have hstep := stage2NoEventWalk_step_condbr_true (f := stage2NoEventBody)
      (by rw [hpc]; exact ifEnd327peelBlock_find)
      (by simpa only [stateAt] using hcode) rfl
      (by rw [lookupName_cons_self])
    simpa only [bracketEntry, stage2NoEventWalkNext, stateAt] using hstep
  · exact Stage2NoEventWalkInv.mem_congr h rfl

/-- `if.then334`: the `phi` run and the counts, `K` to `{tok+2, terms+7}`. -/
theorem link_ifThen334 {calls : Calls} {K : Stage2NoEventWalkCarry} {mem : Mem}
    {s : State} {sp : BitVec 32} {k terms tok : BitVec 64}
    (h : Stage2NoEventWalkInv K mem s) (hpc : s.pc = "if.then334")
    (hpre : s.pre = some "if.end327.peel")
    (hsp : lookupName s.env "%sp.0.ph1403" = some (.int 32 sp))
    (hk : lookupName s.env "%k.0.ph1404" = some (.int 64 k))
    (htr : lookupName s.env "%terms.0.ph1407" = some (.int 64 terms))
    (htokr : lookupName s.env "%tokens.0.ph1408" = some (.int 64 tok))
    (htok : K.tok + 2 ≤ K.n) :
    Stage2NoEventWalkLink calls K mem s
      { K with tok := K.tok + 2, terms := K.terms + 7 }
      (bracketCounts s sp k tok terms) := by
  have h1 := ifThen334_phi_denote (calls := calls) (env := s.env) (s := s)
    (sp := sp) (k := k) (terms := terms) (tok := tok) hpre hsp hk htr htokr
  have h2 := ifThen334_counts_denote (calls := calls) (env := s.env) (s := s)
    (sp := sp) (k := k) (terms := terms) (tok := tok)
  have hcode : denoteCode calls ifThen334Block.instrs (stateAt s.env s) =
      some (stateAt (cells (ifThen334AllCells sp k tok terms) s.env) s) := by
    rw [ifThen334_split]
    rw [denoteCode_append_apply (a := ifThen334PhiInstrs) (b := ifThen334Rest)
      h1 (by decide)]
    exact h2
  refine ⟨h, ?_, ?_⟩
  · have hstep := stage2NoEventWalk_step_br (s := s) (f := stage2NoEventBody)
      (by rw [hpc]; exact ifThen334Block_find)
      (by simpa only [stateAt] using hcode) rfl
    simpa only [bracketCounts, stage2NoEventWalkNext, stateAt] using hstep
  · exact Stage2NoEventWalkInv.mem_congr (Stage2NoEventWalkInv.count h htok) rfl

/-- `close_arr`: the `phi` run and the depth test, at a depth above one. -/
theorem link_closeArr {calls : Calls} {K : Stage2NoEventWalkCarry} {mem : Mem}
    {s : State} {sp3 : BitVec 32} {k5 alen arena terms7 toks : BitVec 64}
    (h : Stage2NoEventWalkInv K mem s) (hpc : s.pc = "close_arr")
    (hpre : s.pre = some "if.then334")
    (hsp : lookupName s.env "%sp.0.lcssa1096.wide" = some (.int 32 sp3))
    (hinc335 : lookupName s.env "%inc335" = some (.int 64 k5))
    (halen : lookupName s.env "%alen.0.ph1405" = some (.int 64 alen))
    (harena : lookupName s.env "%arena.0.ph1406" = some (.int 64 arena))
    (hadd338 : lookupName s.env "%add338" = some (.int 64 terms7))
    (hinc337 : lookupName s.env "%inc337" = some (.int 64 toks))
    (hpos : sp3.toNat ≠ 0) :
    Stage2NoEventWalkLink calls K mem s K
      (bracketArr s sp3 k5 alen arena terms7 toks) := by
  have h1 := closeArr_phi_denote (calls := calls) (env := s.env) (s := s)
    (sp3 := sp3) (k5 := k5) (alen := alen) (arena := arena) (terms7 := terms7)
    (toks := toks) hpre hsp hinc335 halen harena hadd338 hinc337
  have h2 := closeArr_test_denote (calls := calls) (env := s.env) (s := s)
    (sp3 := sp3) (k5 := k5) (alen := alen) (arena := arena) (terms7 := terms7)
    (toks := toks)
  have hbit : evalICmp .eq sp3 (BitVec.ofNat 32 0) = (0 : BitVec 1) :=
    stage2NoEventEq0_zero hpos
  have hcode : denoteCode calls closeArrBlock.instrs (stateAt s.env s) =
      some (stateAt (cells (closeArrAllCells sp3 k5 alen arena terms7 toks) s.env) s) := by
    rw [closeArr_split]
    rw [denoteCode_append_apply (a := closeArrPhiInstrs) (b := closeArrRest)
      h1 (by decide)]
    exact h2
  refine ⟨h, ?_, ?_⟩
  · have hstep := stage2NoEventWalk_step_condbr_false (f := stage2NoEventBody)
      (by rw [hpc]; exact closeArrBlock_find)
      (by simpa only [stateAt] using hcode) rfl
      (by
        rw [lookupName_cells_of_some (cs := closeArrAllCells sp3 k5 alen arena terms7 toks)
          (n := "%tobool349.not") (env := s.env)
          (by rw [closeArrAllCells, closeArrTail, closeArrPhiCells]; cells_lk)]
        rw [hbit])
    simpa only [bracketArr, stage2NoEventWalkNext, stateAt] using hstep
  · exact Stage2NoEventWalkInv.mem_congr h rfl

/-- `if.then350`: the frame read, to `after_value`. -/
theorem link_ifThen350 {calls : Calls} {K : Stage2NoEventWalkCarry} {mem : Mem}
    {s : State} {stk : Nat} {sp3 : BitVec 32} {a : Nat} {bs : List UInt8}
    (h : Stage2NoEventWalkInv K mem s) (hpc : s.pc = "if.then350")
    (hsp3 : lookupName s.env "%sp.3" = some (.int 32 sp3))
    (hstk : lookupName s.env "%stk" = some (.ptr stk))
    (hbyte : readBytes s.mem a 1 = some bs)
    (ha : a = closeReadAddr stk (sp3 + BitVec.ofNat 32 4294967295).toNat) :
    Stage2NoEventWalkLink calls K mem s K (bracketRead s sp3 a bs) := by
  have hcode : denoteCode calls ifThen350Block.instrs (stateAt s.env s) =
      some (stateAt
        (cells (("%50", .int 8 (BitVec.ofNat 8 (bytesToNat bs))) ::
          closeGepCells50 a ++ closeIdxCells50 (sp3 + BitVec.ofNat 32 4294967295))
          s.env) s) :=
    ifThen350_denote (calls := calls) (env := s.env) (s := s)
      (stk := stk) (sp3 := sp3) (a := a) (bs := bs) ha hsp3 hstk hbyte
  refine ⟨h, ?_, ?_⟩
  · have hstep := stage2NoEventWalk_step_br (s := s) (f := stage2NoEventBody)
      (by rw [hpc]; exact ifThen350Block_find)
      (by simpa only [stateAt] using hcode) rfl
    simpa only [bracketRead, stage2NoEventWalkNext, stateAt] using hstep
  · exact Stage2NoEventWalkInv.mem_congr h rfl

/-- **The `]` closer**: `link_ifEnd327peel` → `link_ifThen334` → `link_closeArr` →
`link_ifThen350`. -/
theorem row_closeBracket {calls : Calls} {K : Stage2NoEventWalkCarry} {mem : Mem}
    {s : State} {inc : BitVec 64} {ep b : Nat} {bs4 bs1 : List UInt8}
    {sp : BitVec 32} {k terms tok : BitVec 64} {alen arena : BitVec 64}
    {stk : Nat} {a : Nat} {bs : List UInt8}
    (h : Stage2NoEventWalkInv K mem s) (hpc : s.pc = "if.end327.peel")
    (hinc : lookupName s.env "%inc.peel" = some (.int 64 inc))
    (hep : lookupName s.env "%ep" = some (.ptr ep))
    (hb : lookupName s.env "%b" = some (.ptr b))
    (hincLt : inc.toNat < 2 ^ 63)
    (hlane : readBytes s.mem (ep + inc.toNat * 4) 4 = some bs4)
    (hlanelt : bytesToNat bs4 < 2 ^ 32)
    (hbyte1 : readBytes s.mem
      (b + (BitVec.signExtend 64 (BitVec.ofNat 64 (bytesToNat bs4))).toNat) 1 = some bs1)
    (hb93 : bytesToNat bs1 = 93)
    (hsp : lookupName s.env "%sp.0.ph1403" = some (.int 32 sp))
    (hk : lookupName s.env "%k.0.ph1404" = some (.int 64 k))
    (htr : lookupName s.env "%terms.0.ph1407" = some (.int 64 terms))
    (htokr : lookupName s.env "%tokens.0.ph1408" = some (.int 64 tok))
    (htok : K.tok + 2 ≤ K.n)
    (halen : lookupName s.env "%alen.0.ph1405" = some (.int 64 alen))
    (harena : lookupName s.env "%arena.0.ph1406" = some (.int 64 arena))
    (hstk : lookupName s.env "%stk" = some (.ptr stk))
    (hposS : sp.toNat ≠ 0)
    (hbyte : readBytes s.mem a 1 = some bs)
    (ha : a = closeReadAddr stk (sp + BitVec.ofNat 32 4294967295).toNat) :
    Stage2NoEventWalkChain calls mem K s
      { K with tok := K.tok + 2, terms := K.terms + 7 }
      (bracketRead (bracketArr (bracketCounts (bracketEntry s inc ep b bs4 bs1)
        sp k tok terms) sp (k + BitVec.ofNat 64 2) alen arena
        (terms + BitVec.ofNat 64 7) (tok + BitVec.ofNat 64 2)) sp a bs) := by
  let S1 := bracketEntry s inc ep b bs4 bs1
  let S2 := bracketCounts S1 sp k tok terms
  let S3 := bracketArr S2 sp (k + BitVec.ofNat 64 2) alen arena
    (terms + BitVec.ofNat 64 7) (tok + BitVec.ofNat 64 2)
  let K1 : Stage2NoEventWalkCarry := { K with tok := K.tok + 2, terms := K.terms + 7 }
  have L0 : Stage2NoEventWalkLink calls K mem s K S1 :=
    link_ifEnd327peel h hpc hinc hep hb hincLt hlane hlanelt hbyte1 hb93
  have hsp1 : lookupName S1.env "%sp.0.ph1403" = some (.int 32 sp) := by
    simp only [S1, bracketEntry, stage2NoEventWalkNext]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact hsp
  have hk1 : lookupName S1.env "%k.0.ph1404" = some (.int 64 k) := by
    simp only [S1, bracketEntry, stage2NoEventWalkNext]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact hk
  have htr1 : lookupName S1.env "%terms.0.ph1407" = some (.int 64 terms) := by
    simp only [S1, bracketEntry, stage2NoEventWalkNext]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact htr
  have htokr1 : lookupName S1.env "%tokens.0.ph1408" = some (.int 64 tok) := by
    simp only [S1, bracketEntry, stage2NoEventWalkNext]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact htokr
  have L1 : Stage2NoEventWalkLink calls K mem S1 K1 S2 :=
    link_ifThen334 (sp := sp) (k := k) (terms := terms) (tok := tok)
      L0.inv' (by simp only [S1, bracketEntry, stage2NoEventWalkNext])
      (by simp only [S1, bracketEntry, stage2NoEventWalkNext]; rw [hpc])
      hsp1 hk1 htr1 htokr1 htok
  have hsp2 : lookupName S2.env "%sp.0.lcssa1096.wide" = some (.int 32 sp) := by
    simp only [S2, bracketCounts, stage2NoEventWalkNext]
    exact lookupName_cells_of_some (cs := ifThen334AllCells sp k tok terms)
      (n := "%sp.0.lcssa1096.wide") (env := S1.env)
      (by rw [ifThen334AllCells, ifThen334Cells, ifThen334PhiCells]; cells_lk)
  have hinc335 : lookupName S2.env "%inc335"
      = some (.int 64 (k + BitVec.ofNat 64 2)) := by
    simp only [S2, bracketCounts, stage2NoEventWalkNext]
    exact lookupName_cells_of_some (cs := ifThen334AllCells sp k tok terms)
      (n := "%inc335") (env := S1.env)
      (by rw [ifThen334AllCells, ifThen334Cells, ifThen334PhiCells]; cells_lk)
  have halen2 : lookupName S2.env "%alen.0.ph1405" = some (.int 64 alen) := by
    simp only [S2, bracketCounts, stage2NoEventWalkNext]
    rw [lookupName_cells_of_notin (cs := ifThen334AllCells sp k tok terms)
      (n := "%alen.0.ph1405") (env := S1.env)
      (by rw [ifThen334AllCells, ifThen334Cells, ifThen334PhiCells]; simp)]
    simp only [S1, bracketEntry, stage2NoEventWalkNext]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact halen
  have harena2 : lookupName S2.env "%arena.0.ph1406" = some (.int 64 arena) := by
    simp only [S2, bracketCounts, stage2NoEventWalkNext]
    rw [lookupName_cells_of_notin (cs := ifThen334AllCells sp k tok terms)
      (n := "%arena.0.ph1406") (env := S1.env)
      (by rw [ifThen334AllCells, ifThen334Cells, ifThen334PhiCells]; simp)]
    simp only [S1, bracketEntry, stage2NoEventWalkNext]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact harena
  have hadd338 : lookupName S2.env "%add338"
      = some (.int 64 (terms + BitVec.ofNat 64 7)) := by
    simp only [S2, bracketCounts, stage2NoEventWalkNext]
    exact lookupName_cells_of_some (cs := ifThen334AllCells sp k tok terms)
      (n := "%add338") (env := S1.env)
      (by rw [ifThen334AllCells, ifThen334Cells, ifThen334PhiCells]; cells_lk)
  have hinc337 : lookupName S2.env "%inc337"
      = some (.int 64 (tok + BitVec.ofNat 64 2)) := by
    simp only [S2, bracketCounts, stage2NoEventWalkNext]
    exact lookupName_cells_of_some (cs := ifThen334AllCells sp k tok terms)
      (n := "%inc337") (env := S1.env)
      (by rw [ifThen334AllCells, ifThen334Cells, ifThen334PhiCells]; cells_lk)
  have L2 : Stage2NoEventWalkLink calls K1 mem S2 K1 S3 :=
    link_closeArr (sp3 := sp) (k5 := k + BitVec.ofNat 64 2)
      (terms7 := terms + BitVec.ofNat 64 7) (toks := tok + BitVec.ofNat 64 2)
      L1.inv' (by simp only [S2, bracketCounts, stage2NoEventWalkNext])
      (by simp only [S2, bracketCounts, stage2NoEventWalkNext, S1, bracketEntry])
      hsp2 hinc335 halen2 harena2
      hadd338 hinc337 hposS
  have hsp3 : lookupName S3.env "%sp.3" = some (.int 32 sp) := by
    simp only [S3, bracketArr, stage2NoEventWalkNext]
    exact lookupName_cells_of_some
      (cs := closeArrAllCells sp (k + BitVec.ofNat 64 2) alen arena
        (terms + BitVec.ofNat 64 7) (tok + BitVec.ofNat 64 2))
      (n := "%sp.3") (env := S2.env)
      (by rw [closeArrAllCells, closeArrTail, closeArrPhiCells]; cells_lk)
  have hstk3 : lookupName S3.env "%stk" = some (.ptr stk) := by
    simp only [S3, bracketArr, stage2NoEventWalkNext]
    rw [lookupName_cells_of_notin
      (cs := closeArrAllCells sp (k + BitVec.ofNat 64 2) alen arena
        (terms + BitVec.ofNat 64 7) (tok + BitVec.ofNat 64 2))
      (n := "%stk") (env := S2.env)
      (by rw [closeArrAllCells, closeArrTail, closeArrPhiCells]; simp)]
    simp only [S2, bracketCounts, stage2NoEventWalkNext]
    rw [lookupName_cells_of_notin (cs := ifThen334AllCells sp k tok terms)
      (n := "%stk") (env := S1.env)
      (by rw [ifThen334AllCells, ifThen334Cells, ifThen334PhiCells]; simp)]
    simp only [S1, bracketEntry, stage2NoEventWalkNext]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact hstk
  have hbyte3 : readBytes S3.mem a 1 = some bs := by
    simpa only [S3, bracketArr, S2, bracketCounts, S1, bracketEntry,
      stage2NoEventWalkNext] using hbyte
  have L3 : Stage2NoEventWalkLink calls K1 mem S3 K1
      (bracketRead S3 sp a bs) :=
    link_ifThen350 (sp3 := sp) L2.inv'
      (by simp only [S3, bracketArr, stage2NoEventWalkNext])
      hsp3 hstk3 hbyte3 ha
  simpa only [S1, S2, S3, K1] using
    (Stage2NoEventWalkChain.tail L0 (Stage2NoEventWalkChain.tail L1
      (Stage2NoEventWalkChain.tail L2 (Stage2NoEventWalkChain.tail L3
        (Stage2NoEventWalkChain.nil L3.inv')))))



/-- The cells `if.then81`'s counts bind. -/
def ifThen81Out (env : Env) (k tok terms : BitVec 64) : Env :=
  cells [("%add85", .int 64 (terms + BitVec.ofNat 64 3)),
    ("%inc84", .int 64 (tok + BitVec.ofNat 64 2)),
    ("%inc82", .int 64 (k + BitVec.ofNat 64 2))] env

/-- `if.then81`: the counts, `K` to `{tok+2, terms+3}`, to `close_obj`. -/
theorem link_ifThen81 {calls : Calls} {K : Stage2NoEventWalkCarry} {mem : Mem}
    {s : State} {out : Env} {k tok terms : BitVec 64}
    (h : Stage2NoEventWalkInv K mem s) (hpc : s.pc = "if.then81")
    (hout : out = ifThen81Out s.env k tok terms)
    (hk : lookupName s.env "%k.0.lcssa1086" = some (.int 64 k))
    (htokr : lookupName s.env "%tokens.0.lcssa1074" = some (.int 64 tok))
    (htr : lookupName s.env "%terms.0.lcssa1080" = some (.int 64 terms))
    (htok : K.tok + 2 ≤ K.n) :
    Stage2NoEventWalkLink calls K mem s
      { K with tok := K.tok + 2, terms := K.terms + 3 }
      (stage2NoEventWalkNext out s "close_obj") := by
  have h1 : denoteCode calls ifThen81Block.instrs (stateAt s.env s) =
      some (stateAt out s) := by
    rw [hout, ifThen81Out]
    rw [ifThen81Block]
    rw [stage2NoEventWalk_denote_add_imm_w (calls := calls) (env := s.env) (s := s)
      (d := "%inc82") (a := "%k.0.lcssa1086") (w := 64) hk]
    rw [stage2NoEventWalk_denote_add_imm_w (calls := calls) (env := _) (s := s)
      (d := "%inc84") (a := "%tokens.0.lcssa1074") (w := 64) (x := tok)
      (by rw [lookupName_cons_ne _ _ (by decide)]; exact htokr)]
    rw [stage2NoEventWalk_denote_add_imm_w (calls := calls) (env := _) (s := s)
      (d := "%add85") (a := "%terms.0.lcssa1080") (w := 64) (x := terms)
      (by rw [lookupName_cons_ne _ _ (by decide),
        lookupName_cons_ne _ _ (by decide)]; exact htr)]
    rw [cells, denoteCode_nil]
    rfl
  refine ⟨h, ?_, ?_⟩
  · have hstep := stage2NoEventWalk_step_br (s := s) (f := stage2NoEventBody)
      (by rw [hpc]; exact ifThen81Block_find)
      (by simpa only [stateAt] using h1) rfl
    simpa only [stage2NoEventWalkNext, stateAt] using hstep
  · exact Stage2NoEventWalkInv.mem_congr (Stage2NoEventWalkInv.count h htok) rfl

/-! ### The count class's one `htok` derivation

The two count-bearing links take `htok : K.tok + c ≤ K.n`.  That guard is not a
hypothesis of the class: it follows once from the invariant's entry bound
(`inside`, which places every entry below the document's length) and the
count-token relation `K.tok + c ≤ K.pos`.  The links are then re-checked against
the derived form, so nothing in the class leaves `htok` underived. -/

/-- The carried token index is below the document's length, when it is an entry. -/
theorem Stage2NoEventWalkInv.pos_lt {K : Stage2NoEventWalkCarry} {mem : Mem}
    {s : State} (h : Stage2NoEventWalkInv K mem s) (hmem : K.pos ∈ K.ent) :
    K.pos < K.n :=
  h.inside K.pos hmem

/-- **The count guard, derived once**: the entry bound plus the count-token
relation give `K.tok + c ≤ K.n`. -/
theorem Stage2NoEventWalkInv.htok {K : Stage2NoEventWalkCarry} {mem : Mem}
    {s : State} (h : Stage2NoEventWalkInv K mem s) {c : Nat}
    (hmem : K.pos ∈ K.ent) (hrel : K.tok + c ≤ K.pos) :
    K.tok + c ≤ K.n :=
  le_trans hrel (le_of_lt (h.pos_lt hmem))

/-- `if.then81`'s count with the guard derived, not assumed. -/
theorem link_ifThen81_of_bound {calls : Calls} {K : Stage2NoEventWalkCarry}
    {mem : Mem} {s : State} {out : Env} {k tok terms : BitVec 64}
    (h : Stage2NoEventWalkInv K mem s) (hpc : s.pc = "if.then81")
    (hout : out = ifThen81Out s.env k tok terms)
    (hk : lookupName s.env "%k.0.lcssa1086" = some (.int 64 k))
    (htokr : lookupName s.env "%tokens.0.lcssa1074" = some (.int 64 tok))
    (htr : lookupName s.env "%terms.0.lcssa1080" = some (.int 64 terms))
    (hmem : K.pos ∈ K.ent) (hrel : K.tok + 2 ≤ K.pos) :
    Stage2NoEventWalkLink calls K mem s
      { K with tok := K.tok + 2, terms := K.terms + 3 }
      (stage2NoEventWalkNext out s "close_obj") :=
  link_ifThen81 h hpc hout hk htokr htr (Stage2NoEventWalkInv.htok h hmem hrel)

/-- `if.then334`'s count with the guard derived, not assumed. -/
theorem link_ifThen334_of_bound {calls : Calls} {K : Stage2NoEventWalkCarry}
    {mem : Mem} {s : State} {sp : BitVec 32} {k terms tok : BitVec 64}
    (h : Stage2NoEventWalkInv K mem s) (hpc : s.pc = "if.then334")
    (hpre : s.pre = some "if.end327.peel")
    (hsp : lookupName s.env "%sp.0.ph1403" = some (.int 32 sp))
    (hk : lookupName s.env "%k.0.ph1404" = some (.int 64 k))
    (htr : lookupName s.env "%terms.0.ph1407" = some (.int 64 terms))
    (htokr : lookupName s.env "%tokens.0.ph1408" = some (.int 64 tok))
    (hmem : K.pos ∈ K.ent) (hrel : K.tok + 2 ≤ K.pos) :
    Stage2NoEventWalkLink calls K mem s
      { K with tok := K.tok + 2, terms := K.terms + 7 }
      (bracketCounts s sp k tok terms) :=
  link_ifThen334 h hpc hpre hsp hk htr htokr (Stage2NoEventWalkInv.htok h hmem hrel)


/-! ### The base step: the head's carrier-zero bindings

The walk is entered through `if.end.peel.preheader`, which binds the head's nine
`phi`s from immediates: the zero counters, the zero depth and frame, and the
`520` budget.  This is the "carry zeros" half of the base step, stated at the
head's `phi` run; the entry block's remainder (the record's stores, the memset and
the terminator) and the preheader's geps precede it, and the head's read row
(`stage2NoEventLoopHead_denote`) follows it. -/

/-- The cells the head's `phi` run binds on the preheader edge, newest first. -/
def loopHeadPhiCells : List (String × Value) :=
  [("%frame.0.ph1402", .int 8 0), ("%sp.0.ph1403", .int 32 0),
   ("%k.0.ph1404", .int 64 0), ("%alen.0.ph1405", .int 64 0),
   ("%arena.0.ph1406", .int 64 0), ("%terms.0.ph1407", .int 64 0),
   ("%tokens.0.ph1408", .int 64 0), ("%1", .int 64 0),
   ("%wide.trip.count1409", .int 64 520)]

/-- The head's nine `phi`s on the preheader edge, as specs. -/
def loopHeadPhiSpecs : List PhiSpec :=
  [ ⟨"%wide.trip.count1409", Ty.int 64,
      [("value.outer.backedge", .reg "%wide.trip.count"),
       ("if.end.peel.preheader", .imm (.int 64 (BitVec.ofNat 64 520)))]⟩,
    ⟨"%1", Ty.int 64,
      [("value.outer.backedge", .reg "%45"),
       ("if.end.peel.preheader", .imm (.int 64 (BitVec.ofNat 64 0)))]⟩,
    ⟨"%tokens.0.ph1408", Ty.int 64,
      [("value.outer.backedge", .reg "%tokens.0.ph.be"),
       ("if.end.peel.preheader", .imm (.int 64 (BitVec.ofNat 64 0)))]⟩,
    ⟨"%terms.0.ph1407", Ty.int 64,
      [("value.outer.backedge", .reg "%terms.0.ph.be"),
       ("if.end.peel.preheader", .imm (.int 64 (BitVec.ofNat 64 0)))]⟩,
    ⟨"%arena.0.ph1406", Ty.int 64,
      [("value.outer.backedge", .reg "%arena.0.ph.be"),
       ("if.end.peel.preheader", .imm (.int 64 (BitVec.ofNat 64 0)))]⟩,
    ⟨"%alen.0.ph1405", Ty.int 64,
      [("value.outer.backedge", .reg "%alen.0.ph.be"),
       ("if.end.peel.preheader", .imm (.int 64 (BitVec.ofNat 64 0)))]⟩,
    ⟨"%k.0.ph1404", Ty.int 64,
      [("value.outer.backedge", .reg "%k.0.ph.be"),
       ("if.end.peel.preheader", .imm (.int 64 (BitVec.ofNat 64 0)))]⟩,
    ⟨"%sp.0.ph1403", Ty.int 32,
      [("value.outer.backedge", .reg "%sp.0.ph.be"),
       ("if.end.peel.preheader", .imm (.int 32 (BitVec.ofNat 32 0)))]⟩,
    ⟨"%frame.0.ph1402", Ty.int 8,
      [("value.outer.backedge", .reg "%frame.0.ph.be"),
       ("if.end.peel.preheader", .imm (.int 8 (BitVec.ofNat 8 0)))]⟩ ]

theorem loopHeadPhi_eq : loopHeadPhiInstrs = loopHeadPhiSpecs.map PhiSpec.instr := rfl

/-- **The base step's zero bindings**: the head's `phi` run at the preheader edge,
with every carried counter zero and the budget `520`. -/
theorem baseHeadPhi_denote (calls : Calls) (env : Env) (s : State)
    (hpre : s.pre = some "if.end.peel.preheader") :
    denoteCode calls loopHeadPhiInstrs (stateAt env s) =
      some (stateAt (cells loopHeadPhiCells env) s) := by
  have hsel : PhiSelects (stateAt env s) "if.end.peel.preheader" loopHeadPhiSpecs
      [("%wide.trip.count1409", .int 64 (BitVec.ofNat 64 520)),
       ("%1", .int 64 (BitVec.ofNat 64 0)),
       ("%tokens.0.ph1408", .int 64 (BitVec.ofNat 64 0)),
       ("%terms.0.ph1407", .int 64 (BitVec.ofNat 64 0)),
       ("%arena.0.ph1406", .int 64 (BitVec.ofNat 64 0)),
       ("%alen.0.ph1405", .int 64 (BitVec.ofNat 64 0)),
       ("%k.0.ph1404", .int 64 (BitVec.ofNat 64 0)),
       ("%sp.0.ph1403", .int 32 (BitVec.ofNat 32 0)),
       ("%frame.0.ph1402", .int 8 (BitVec.ofNat 8 0))] := by
    refine PhiSelects.cons (op := .imm (.int 64 (BitVec.ofNat 64 520))) (by decide) ?_
      (PhiSelects.cons (op := .imm (.int 64 (BitVec.ofNat 64 0))) (by decide) ?_
        (PhiSelects.cons (op := .imm (.int 64 (BitVec.ofNat 64 0))) (by decide) ?_
          (PhiSelects.cons (op := .imm (.int 64 (BitVec.ofNat 64 0))) (by decide) ?_
            (PhiSelects.cons (op := .imm (.int 64 (BitVec.ofNat 64 0))) (by decide) ?_
              (PhiSelects.cons (op := .imm (.int 64 (BitVec.ofNat 64 0))) (by decide) ?_
                (PhiSelects.cons (op := .imm (.int 64 (BitVec.ofNat 64 0))) (by decide) ?_
                  (PhiSelects.cons (op := .imm (.int 32 (BitVec.ofNat 32 0))) (by decide) ?_
                    (PhiSelects.cons (op := .imm (.int 8 (BitVec.ofNat 8 0))) (by decide) ?_
                      PhiSelects.nil))))))))
    all_goals
      simp only [stateAt, evalOperand, Const.toValue]
  rw [loopHeadPhi_eq, ← List.append_nil (List.map PhiSpec.instr loopHeadPhiSpecs),
    denoteCode_phiRun (s := stateAt env s) (p := "if.end.peel.preheader")
      (specs := loopHeadPhiSpecs) (rest := [])
      (hpre := hpre) (hsel := hsel) (hrest := rfl)]
  simp only [State.bindAll, State.bind, loopHeadPhiCells, cells]
  rfl


/-! ### The base step: the entry suffix as sub-rows

Decision (w16): the seventeen instructions are five sub-rows of at most four, each
concluding at a named `cells` state, composed by `denoteCode_append_apply` with
`startsWithPhi … = false` at each boundary.  The per-step lookups stay at cons
depths three and below, as every existing row proves. -/

/-- The entry block's instructions after the bootstrap's twelve. -/
def entrySuffixInstrs : List Instr :=
  [ Instr.gep "%msg" (Ty.int 8) (Operand.reg "%e")
      (Operand.imm (.int 64 (BitVec.ofNat 64 16))),
    Instr.store Ty.ptr (Operand.imm .null) (Operand.reg "%msg"),
    Instr.gep "%0" (Ty.int 8) (Operand.reg "%c")
      (Operand.imm (.int 64 (BitVec.ofNat 64 32))),
    Instr.callVoid "llvm.memset.p0.i64"
      [(Ty.ptr, (Operand.reg "%0")), ((Ty.int 8), (Operand.imm (.int 8 (BitVec.ofNat 8 0)))),
       ((Ty.int 64), (Operand.imm (.int 64 (BitVec.ofNat 64 1160)))),
       ((Ty.int 1), (Operand.imm (.int 1 (BitVec.ofNat 1 0))))],
    Instr.store Ty.ptr (Operand.reg "%b") (Operand.reg "%c"),
    Instr.gep "%n2" (Ty.int 8) (Operand.reg "%c")
      (Operand.imm (.int 64 (BitVec.ofNat 64 8))),
    Instr.store (Ty.int 64) (Operand.reg "%n") (Operand.reg "%n2"),
    Instr.gep "%ix" (Ty.int 8) (Operand.reg "%c")
      (Operand.imm (.int 64 (BitVec.ofNat 64 16))),
    Instr.store Ty.ptr (Operand.reg "%ep") (Operand.reg "%ix"),
    Instr.gep "%nix" (Ty.int 8) (Operand.reg "%c")
      (Operand.imm (.int 64 (BitVec.ofNat 64 24))),
    Instr.store (Ty.int 64) (Operand.reg "%nep") (Operand.reg "%nix"),
    Instr.gep "%e3" (Ty.int 8) (Operand.reg "%c")
      (Operand.imm (.int 64 (BitVec.ofNat 64 1112))),
    Instr.store Ty.ptr (Operand.reg "%e") (Operand.reg "%e3"),
    Instr.gep "%invariant.gep" (Ty.int 8) (Operand.reg "%b")
      (Operand.imm (.int 64 (BitVec.ofNat 64 1))),
    Instr.gep "%invariant.gep1068" (Ty.int 8) (Operand.reg "%b")
      (Operand.imm (.int 64 (BitVec.ofNat 64 18446744073709551615))),
    Instr.gep "%k219" (Ty.int 8) (Operand.reg "%c")
      (Operand.imm (.int 64 (BitVec.ofNat 64 32))),
    Instr.icmp "%cmp.not.peel1401.not" IPred.eq 64 (Operand.reg "%nep")
      (Operand.imm (.int 64 (BitVec.ofNat 64 0))) ]

theorem entrySuffix_split :
    (stage2NoEventBody.findBlock "entry").map (fun b => b.instrs.drop 12)
      = some entrySuffixInstrs := by
  decide

/-- Sub-row A: the message slot, the whole-record `memset`, and `%0`. -/
def entryA1 : List Instr :=
  [ Instr.gep "%msg" (Ty.int 8) (Operand.reg "%e")
      (Operand.imm (.int 64 (BitVec.ofNat 64 16))),
    Instr.store Ty.ptr (Operand.imm .null) (Operand.reg "%msg"),
    Instr.gep "%0" (Ty.int 8) (Operand.reg "%c")
      (Operand.imm (.int 64 (BitVec.ofNat 64 32))),
    Instr.callVoid "llvm.memset.p0.i64"
      [(Ty.ptr, (Operand.reg "%0")), ((Ty.int 8), (Operand.imm (.int 8 (BitVec.ofNat 8 0)))),
       ((Ty.int 64), (Operand.imm (.int 64 (BitVec.ofNat 64 1160)))),
       ((Ty.int 1), (Operand.imm (.int 1 (BitVec.ofNat 1 0))))] ]

/-- Sub-row B: the document pointer and length. -/
def entryA2 : List Instr :=
  [ Instr.store Ty.ptr (Operand.reg "%b") (Operand.reg "%c"),
    Instr.gep "%n2" (Ty.int 8) (Operand.reg "%c")
      (Operand.imm (.int 64 (BitVec.ofNat 64 8))),
    Instr.store (Ty.int 64) (Operand.reg "%n") (Operand.reg "%n2"),
    Instr.gep "%ix" (Ty.int 8) (Operand.reg "%c")
      (Operand.imm (.int 64 (BitVec.ofNat 64 16))) ]

/-- Sub-row C: the entry pointer and count. -/
def entryA3 : List Instr :=
  [ Instr.store Ty.ptr (Operand.reg "%ep") (Operand.reg "%ix"),
    Instr.gep "%nix" (Ty.int 8) (Operand.reg "%c")
      (Operand.imm (.int 64 (BitVec.ofNat 64 24))),
    Instr.store (Ty.int 64) (Operand.reg "%nep") (Operand.reg "%nix"),
    Instr.gep "%e3" (Ty.int 8) (Operand.reg "%c")
      (Operand.imm (.int 64 (BitVec.ofNat 64 1112))) ]

/-- Sub-row D: the record pointer and the next-entry addresses. -/
def entryA4 : List Instr :=
  [ Instr.store Ty.ptr (Operand.reg "%e") (Operand.reg "%e3"),
    Instr.gep "%invariant.gep" (Ty.int 8) (Operand.reg "%b")
      (Operand.imm (.int 64 (BitVec.ofNat 64 1))),
    Instr.gep "%invariant.gep1068" (Ty.int 8) (Operand.reg "%b")
      (Operand.imm (.int 64 (BitVec.ofNat 64 18446744073709551615))),
    Instr.gep "%k219" (Ty.int 8) (Operand.reg "%c")
      (Operand.imm (.int 64 (BitVec.ofNat 64 32))) ]

/-- Sub-row E: the depth's zero test. -/
def entryA5 : List Instr :=
  [ Instr.icmp "%cmp.not.peel1401.not" IPred.eq 64 (Operand.reg "%nep")
      (Operand.imm (.int 64 (BitVec.ofNat 64 0))) ]

theorem entrySuffix_pieces :
    entrySuffixInstrs = entryA1 ++ (entryA2 ++ (entryA3 ++ (entryA4 ++ entryA5))) := by
  decide

/-- The cells and memory after sub-row A. -/
def entryCells1 (c e : Nat) : List (String × Value) :=
  [("%0", .ptr (c + 32)), ("%msg", .ptr (e + 16))]
def entryMem1 (c e : Nat) (m : Mem) : Mem :=
  writeBytes (writeBytes m (e + 16) (natToBytes 0 8)) (c + 32)
    (List.replicate 1160 (0 : UInt8))

/-- The cells and memory after sub-row B. -/
def entryCells2 (b c : Nat) : List (String × Value) :=
  [("%ix", .ptr (c + 16)), ("%n2", .ptr (c + 8))]
def entryMem2 (b n c : Nat) (m : Mem) : Mem :=
  writeBytes (writeBytes m c (natToBytes b 8)) (c + 8) (natToBytes n 8)

/-- The cells and memory after sub-row C. -/
def entryCells3 (ep c : Nat) : List (String × Value) :=
  [("%e3", .ptr (c + 1112)), ("%nix", .ptr (c + 24))]
def entryMem3 (ep nep c : Nat) (m : Mem) : Mem :=
  writeBytes (writeBytes m (c + 16) (natToBytes ep 8)) (c + 24) (natToBytes nep 8)

/-- The cells and memory after sub-row D. -/
def entryCells4 (b c : Nat) : List (String × Value) :=
  [("%k219", .ptr (c + 32)),
   ("%invariant.gep1068", .ptr (b - 1)),
   ("%invariant.gep", .ptr (b + 1))]
def entryMem4 (e c : Nat) (m : Mem) : Mem :=
  writeBytes m (c + 1112) (natToBytes e 8)

/-- The cells sub-row E binds. -/
def entryCells5 (nep : Nat) : List (String × Value) :=
  [("%cmp.not.peel1401.not", .int 1 (evalICmp .eq (BitVec.ofNat 64 nep)
      (BitVec.ofNat 64 0)))]

/-- A pointer store, as a chain step. -/
theorem stage2NoEventWalk_denote_store_ptr (calls : Calls) (env : Env) (s : State)
    (v p : String) {x a : Nat}
    (hv : lookupName env v = some (.ptr x))
    (hp : lookupName env p = some (.ptr a)) (is : List Instr) :
    denoteCode calls (.store Ty.ptr (.reg v) (.reg p) :: is) (stateAt env s) =
      denoteCode calls is (stateAt env
        (stage2NoEventStepState s (writeBytes s.mem a (natToBytes x 8)) s.next)) := by
  have hstep : evalInstr calls (stateAt env s) (.store Ty.ptr (.reg v) (.reg p)) =
      some (stateAt env
        (stage2NoEventStepState s (writeBytes s.mem a (natToBytes x 8)) s.next)) := by
    rw [evalInstr_store (vv := .ptr x) (a := a)
      (s' := stateAt env
        (stage2NoEventStepState s (writeBytes s.mem a (natToBytes x 8)) s.next))
      (hv := by simp only [stateAt, evalOperand, hv])
      (hp := by simp only [stateAt, evalOperand, hp])]
    simp [storeValue, stateAt, State.bind, stage2NoEventStepState]
  rw [denoteCode_cons_of _ _ _ _ _ hstep]

/-- A null pointer store, as a chain step. -/
theorem stage2NoEventWalk_denote_store_null (calls : Calls) (env : Env) (s : State)
    (p : String) {a : Nat}
    (hp : lookupName env p = some (.ptr a)) (is : List Instr) :
    denoteCode calls (.store Ty.ptr (Operand.imm .null) (.reg p) :: is) (stateAt env s) =
      denoteCode calls is (stateAt env
        (stage2NoEventStepState s (writeBytes s.mem a (natToBytes 0 8)) s.next)) := by
  have hstep : evalInstr calls (stateAt env s) (.store Ty.ptr (Operand.imm .null) (.reg p)) =
      some (stateAt env
        (stage2NoEventStepState s (writeBytes s.mem a (natToBytes 0 8)) s.next)) := by
    rw [evalInstr_store (vv := .ptr 0) (a := a)
      (s' := stateAt env
        (stage2NoEventStepState s (writeBytes s.mem a (natToBytes 0 8)) s.next))
      (hv := by simp only [stateAt, evalOperand, Const.toValue])
      (hp := by simp only [stateAt, evalOperand, hp])]
    simp [storeValue, stateAt, State.bind, stage2NoEventStepState]
  rw [denoteCode_cons_of _ _ _ _ _ hstep]

/-- The `memset` call's one step. -/
theorem stage2NoEventWalk_step_memset {gap : Calls} (env : Env) (s : State)
    {p : String} {n : BitVec 64} {a : Nat}
    (hp : lookupName env p = some (.ptr a)) :
    evalInstr (stage2NoEventCalls gap) (stateAt env s)
        (.callVoid "llvm.memset.p0.i64"
          [(Ty.ptr, .reg p), (Ty.int 8, .imm (.int 8 (BitVec.ofNat 8 0))),
           (Ty.int 64, .imm (.int 64 n)),
           (Ty.int 1, .imm (.int 1 (BitVec.ofNat 1 0)))]) =
      some (stateAt env (stage2NoEventStepState s
        (writeBytes s.mem a (List.replicate n.toNat (0 : UInt8))) s.next)) := by
  have hp' : evalOperand (stateAt env s) (.reg p) = some (.ptr a) :=
    evalOperand_reg_of env s p (.ptr a) hp
  have h0 : evalOperands (stateAt env s) ([] : List (Ty × Operand)) = some [] := rfl
  have h1 : evalOperands (stateAt env s)
      [(Ty.int 1, .imm (.int 1 (BitVec.ofNat 1 0)))] =
      some [.int 1 (BitVec.ofNat 1 0)] := by
    rw [evalOperands_cons (v := .int 1 (BitVec.ofNat 1 0))
      (by simp only [evalOperand, Const.toValue]) h0]
  have h2 : evalOperands (stateAt env s)
      [(Ty.int 64, .imm (.int 64 n)), (Ty.int 1, .imm (.int 1 (BitVec.ofNat 1 0)))] =
      some [.int 64 n, .int 1 (BitVec.ofNat 1 0)] := by
    rw [evalOperands_cons (v := .int 64 n)
      (by simp only [evalOperand, Const.toValue]) h1]
  have h3 : evalOperands (stateAt env s)
      [(Ty.int 8, .imm (.int 8 (BitVec.ofNat 8 0))),
       (Ty.int 64, .imm (.int 64 n)),
       (Ty.int 1, .imm (.int 1 (BitVec.ofNat 1 0)))] =
      some [.int 8 (BitVec.ofNat 8 0), .int 64 n, .int 1 (BitVec.ofNat 1 0)] := by
    rw [evalOperands_cons (v := .int 8 (BitVec.ofNat 8 0))
      (by simp only [evalOperand, Const.toValue]) h2]
  have hargs : evalOperands (State.mk env s.mem s.next s.pc s.pre)
      [(Ty.ptr, .reg p), (Ty.int 8, .imm (.int 8 (BitVec.ofNat 8 0))),
       (Ty.int 64, .imm (.int 64 n)),
       (Ty.int 1, .imm (.int 1 (BitVec.ofNat 1 0)))] =
      some [.ptr a, .int 8 (BitVec.ofNat 8 0), .int 64 n,
        .int 1 (BitVec.ofNat 1 0)] := by
    have hst : (State.mk env s.mem s.next s.pc s.pre) = stateAt env s := rfl
    rw [hst, evalOperands_cons (v := .ptr a) hp' h3]
  have hc : stage2NoEventCalls gap "llvm.memset.p0.i64"
      [.ptr a, .int 8 (BitVec.ofNat 8 0), .int 64 n, .int 1 (BitVec.ofNat 1 0)]
      s.mem s.next =
      some { ret := .int 1 0,
             mem := writeBytes s.mem a (List.replicate n.toNat (0 : UInt8)),
             next := s.next } := by
    simp only [stage2NoEventCalls,
      if_neg (by decide : "llvm.memset.p0.i64" ≠ "od_gap_recover"),
      JsonStage2IR.stage2Calls]
  simp only [evalInstr, hargs, hc, stateAt_mem, stateAt_next,
    stage2NoEventStepState, stateAt]

/-- The `memset` call, as a chain step. -/
theorem stage2NoEventWalk_denote_memset {gap : Calls} (env : Env) (s : State)
    {p : String} {n : BitVec 64} {a : Nat}
    (hp : lookupName env p = some (.ptr a)) (is : List Instr) :
    denoteCode (stage2NoEventCalls gap)
        (.callVoid "llvm.memset.p0.i64"
          [(Ty.ptr, .reg p), (Ty.int 8, .imm (.int 8 (BitVec.ofNat 8 0))),
           (Ty.int 64, .imm (.int 64 n)),
           (Ty.int 1, .imm (.int 1 (BitVec.ofNat 1 0)))] :: is) (stateAt env s) =
      denoteCode (stage2NoEventCalls gap) is (stateAt env
        (stage2NoEventStepState s (writeBytes s.mem a (List.replicate n.toNat (0 : UInt8)))
          s.next)) := by
  rw [denoteCode_cons_of _ _ _ _ _ (stage2NoEventWalk_step_memset env s hp)]

/-- The cells chain composes: the append form is the nested form.  Proved once
so the rows and the composition keep the canonical `cells (a ++ b) env` shape. -/
theorem cells_append (a b : List (String × Value)) (env : Env) :
    cells (a ++ b) env = cells a (cells b env) := by
  induction a with
  | nil => rfl
  | cons c cs ih => simp only [List.cons_append, cells, ih]

/-- Two chained step states are the one-step state with the last memory: the
nest's fields are the same record.  Proved by fields, not by unfolding the
writtenness predicates, so the sub-rows' closings stay cheap. -/
theorem stage2NoEventStepState_nest (s : State) (m₁ m₂ : Mem) (n : Nat) :
    stage2NoEventStepState (stage2NoEventStepState s m₁ n) m₂ n
      = stage2NoEventStepState s m₂ n := rfl

/-- The step state's memory field. -/
theorem stage2NoEventStepState_mem (s : State) (m : Mem) (n : Nat) :
    (stage2NoEventStepState s m n).mem = m := rfl

/-- The step state's allocator field. -/
theorem stage2NoEventStepState_next (s : State) (m : Mem) (n : Nat) :
    (stage2NoEventStepState s m n).next = n := rfl

/-- A backward `i8` offset: the sign-extended index is at or above `2 ^ 63` and
its magnitude does not exceed the base.  The certified `step_gep8_imm_back`
shape, restated for this walk's call selection. -/
theorem stage2NoEventWalk_step_gep8_imm_back (calls : Calls) (env : Env) (s : State)
    (d base : String) (c : BitVec 64) {a : Nat}
    (hb : lookupName env base = some (.ptr a))
    (hneg : ¬ (c.signExtend 64).toNat < 2 ^ 63)
    (hk : (2 ^ 64 - (c.signExtend 64).toNat) ≤ a) :
    evalInstr calls (stateAt env s) (.gep d (.int 8) (.reg base) (.imm (.int 64 c))) =
      some (stateAt ((d, .ptr (a - (2 ^ 64 - (c.signExtend 64).toNat))) :: env) s) := by
  have h1 : (8 + 7) / 8 = 1 := by decide
  rw [evalInstr_gep_back (elemTy := .int 8)
    (hb := BlockEval.evalOperand_reg_of env s base (.ptr a) hb)
    (ho := BlockEval.evalOperand_lit_of _ 64 c) hneg (by simpa [Ty.sizeBytes] using hk)]
  simp only [stateAt, State.bind, Ty.sizeBytes, h1, Nat.mul_one]

/-- The backward `getelementptr i8` chain step, at the `-1` the hand-off reads. -/
theorem stage2NoEventWalk_denote_gep8_imm_m1 (calls : Calls) (env : Env) (s : State)
    (d base : String) {a : Nat} (hb : lookupName env base = some (.ptr a))
    (hk : 1 ≤ a) (is : List Instr) :
    denoteCode calls
        (.gep d (.int 8) (.reg base) (.imm (.int 64 0xffffffffffffffff#64)) :: is)
        (stateAt env s) =
      denoteCode calls is (stateAt ((d, .ptr (a - 1)) :: env) s) := by
  have hneg : ¬ ((BitVec.allOnes 64).signExtend 64).toNat < 2 ^ 63 := by decide
  have hk' : (2 ^ 64 - ((BitVec.allOnes 64).signExtend 64).toNat) ≤ a := by simpa using hk
  have hstep := stage2NoEventWalk_step_gep8_imm_back calls env s d base
    (BitVec.allOnes 64) hb hneg hk'
  rw [denoteCode_cons_of _ _ _ _ _ (by simpa using hstep)]

/-- Sub-row A's run. -/
theorem entryA1_denote {gap : Calls} (env : Env) (s : State) {c e : Nat}
    (hc : lookupName env "%c" = some (.ptr c))
    (he : lookupName env "%e" = some (.ptr e)) :
    denoteCode (stage2NoEventCalls gap) entryA1 (stateAt env s) =
      some (stateAt (cells (entryCells1 c e) env)
        (stage2NoEventStepState s (entryMem1 c e s.mem) s.next)) := by
  unfold entryA1
  rw [stage2NoEventWalk_denote_gep8_imm (calls := stage2NoEventCalls gap)
    (env := env) (s := s) (a := e) (bytes := 16) "%msg" "%e"
    (BitVec.ofNat 64 16) he (by decide) (by decide)]
  rw [stage2NoEventWalk_denote_store_null (calls := stage2NoEventCalls gap)
    (env := _) (s := _) (a := e + 16) "%msg"
    (by simp only [lookupName_cons_self])]
  rw [stage2NoEventWalk_denote_gep8_imm (calls := stage2NoEventCalls gap)
    (env := _) (s := _) (a := c) (bytes := 32) "%0" "%c"
    (BitVec.ofNat 64 32)
    (by rw [lookupName_cons_ne _ _ (by decide)]; exact hc) (by decide) (by decide)]
  rw [stage2NoEventWalk_denote_memset (env := _) (s := _) (a := c + 32)
    (n := BitVec.ofNat 64 1160) (by simp only [lookupName_cons_self])]
  rw [entryCells1, entryMem1, denoteCode_nil]
  rfl

/-- Sub-row B's run. -/
theorem entryA2_denote {gap : Calls} (env : Env) (s : State) {b n c e : Nat}
    (hb : lookupName env "%b" = some (.ptr b))
    (hn : lookupName env "%n" = some (.int 64 (BitVec.ofNat 64 n)))
    (hc : lookupName env "%c" = some (.ptr c)) :
    denoteCode (stage2NoEventCalls gap) entryA2
        (stateAt (cells (entryCells1 c e) env)
          (stage2NoEventStepState s (entryMem1 c e s.mem) s.next)) =
      some (stateAt (cells (entryCells2 b c ++ entryCells1 c e) env)
        (stage2NoEventStepState s
          (writeBytes (writeBytes (entryMem1 c e s.mem) c (natToBytes b 8))
            (c + 8) (natToBytes (BitVec.ofNat 64 n).toNat 8)) s.next)) := by
  unfold entryA2
  rw [stage2NoEventWalk_denote_store_ptr (calls := stage2NoEventCalls gap)
    (env := _) (s := _) (x := b) (a := c) "%b" "%c"
    (by rw [lookupName_cells_of_notin (cs := entryCells1 c e) (n := "%b")
        (env := env) (by rw [entryCells1]; simp)]; exact hb)
    (by rw [lookupName_cells_of_notin (cs := entryCells1 c e) (n := "%c")
        (env := env) (by rw [entryCells1]; simp)]; exact hc)]
  rw [stage2NoEventWalk_denote_gep8_imm (calls := stage2NoEventCalls gap)
    (env := _) (s := _) (a := c) (bytes := 8) "%n2" "%c"
    (BitVec.ofNat 64 8)
    (by rw [lookupName_cells_of_notin (cs := entryCells1 c e) (n := "%c")
      (env := env) (by rw [entryCells1]; simp)]; exact hc) (by decide) (by decide)]
  rw [stage2NoEventWalk_denote_store_int (calls := stage2NoEventCalls gap)
    (env := _) (s := _) (w := 64) (x := BitVec.ofNat 64 n) (a := c + 8) "%n" "%n2"
    (by rw [lookupName_cons_ne _ _ (by decide),
      lookupName_cells_of_notin (cs := entryCells1 c e) (n := "%n")
        (env := env) (by rw [entryCells1]; simp)]; exact hn)
    (by simp only [lookupName_cons_self])]
  rw [stage2NoEventWalk_denote_gep8_imm (calls := stage2NoEventCalls gap)
    (env := _) (s := _) (a := c) (bytes := 16) "%ix" "%c"
    (BitVec.ofNat 64 16)
    (by rw [lookupName_cons_ne _ _ (by decide),
      lookupName_cells_of_notin (cs := entryCells1 c e) (n := "%c")
        (env := env) (by rw [entryCells1]; simp)]; exact hc) (by decide) (by decide)]
  rw [entryCells1, entryCells2, entryMem1, denoteCode_nil]
  rw [cells_append]
  simp only [stage2NoEventStepState_mem]
  simp only [stage2NoEventStepState_next]
  simp only [stage2NoEventStepState_nest]
  rfl

/-- Sub-row C's run. -/
theorem entryA3_denote {gap : Calls} (env : Env) (s : State) {b n ep nep c e : Nat}
    (hb : lookupName env "%b" = some (.ptr b))
    (hn : lookupName env "%n" = some (.int 64 (BitVec.ofNat 64 n)))
    (hep : lookupName env "%ep" = some (.ptr ep))
    (hnep : lookupName env "%nep" = some (.int 64 (BitVec.ofNat 64 nep)))
    (hc : lookupName env "%c" = some (.ptr c)) :
    denoteCode (stage2NoEventCalls gap) entryA3
        (stateAt (cells (entryCells2 b c ++ entryCells1 c e) env)
          (stage2NoEventStepState s
            (writeBytes (writeBytes (entryMem1 c e s.mem) c (natToBytes b 8))
              (c + 8) (natToBytes (BitVec.ofNat 64 n).toNat 8)) s.next)) =
      some (stateAt (cells (entryCells3 ep c ++ entryCells2 b c ++ entryCells1 c e) env)
        (stage2NoEventStepState s
          (writeBytes (writeBytes
            (writeBytes (writeBytes (entryMem1 c e s.mem) c (natToBytes b 8))
              (c + 8) (natToBytes (BitVec.ofNat 64 n).toNat 8))
            (c + 16) (natToBytes ep 8))
            (c + 24) (natToBytes (BitVec.ofNat 64 nep).toNat 8)) s.next)) := by
  unfold entryA3
  rw [stage2NoEventWalk_denote_store_ptr (calls := stage2NoEventCalls gap)
    (env := _) (s := _) (x := ep) (a := c + 16) "%ep" "%ix"
    (by repeat rw [lookupName_cons_ne _ _ (by decide)]
        rw [lookupName_cells_of_notin (cs := entryCells2 b c ++ entryCells1 c e)
          (n := "%ep") (env := env) (by rw [entryCells1, entryCells2, List.map_append]; simp only [List.map_cons, List.map_nil]; decide)]
        exact hep)
    (by rw [cells_append, entryCells2]
        simp only [cells, List.cons_append, List.nil_append, lookupName_cons_self])]
  rw [stage2NoEventWalk_denote_gep8_imm (calls := stage2NoEventCalls gap)
    (env := _) (s := _) (a := c) (bytes := 24) "%nix" "%c"
    (BitVec.ofNat 64 24)
    (by repeat rw [lookupName_cons_ne _ _ (by decide)]
        rw [lookupName_cells_of_notin (cs := entryCells2 b c ++ entryCells1 c e)
          (n := "%c") (env := env) (by rw [entryCells1, entryCells2, List.map_append]; simp only [List.map_cons, List.map_nil]; decide)]
        exact hc) (by decide) (by decide)]
  rw [stage2NoEventWalk_denote_store_int (calls := stage2NoEventCalls gap)
    (env := _) (s := _) (w := 64) (x := BitVec.ofNat 64 nep) (a := c + 24) "%nep" "%nix"
    (by repeat rw [lookupName_cons_ne _ _ (by decide)]
        rw [lookupName_cells_of_notin (cs := entryCells2 b c ++ entryCells1 c e)
          (n := "%nep") (env := env) (by rw [entryCells1, entryCells2, List.map_append]; simp only [List.map_cons, List.map_nil]; decide)]
        exact hnep)
    (by simp only [lookupName_cons_self])]
  rw [stage2NoEventWalk_denote_gep8_imm (calls := stage2NoEventCalls gap)
    (env := _) (s := _) (a := c) (bytes := 1112) "%e3" "%c"
    (BitVec.ofNat 64 1112)
    (by repeat rw [lookupName_cons_ne _ _ (by decide)]
        rw [lookupName_cells_of_notin (cs := entryCells2 b c ++ entryCells1 c e)
          (n := "%c") (env := env) (by rw [entryCells1, entryCells2, List.map_append]; simp only [List.map_cons, List.map_nil]; decide)]
        exact hc) (by decide) (by decide)]
  rw [entryCells1, entryCells2, entryCells3, entryMem1, denoteCode_nil]
  rw [cells_append]
  simp only [stage2NoEventStepState_mem]
  simp only [stage2NoEventStepState_next]
  simp only [stage2NoEventStepState_nest]
  rfl

/-- Sub-row D's run. -/
theorem entryA4_denote {gap : Calls} (env : Env) (s : State) {b n ep nep c e : Nat}
    (hb : lookupName env "%b" = some (.ptr b))
    (hn : lookupName env "%n" = some (.int 64 (BitVec.ofNat 64 n)))
    (hep : lookupName env "%ep" = some (.ptr ep))
    (hnep : lookupName env "%nep" = some (.int 64 (BitVec.ofNat 64 nep)))
    (hc : lookupName env "%c" = some (.ptr c))
    (he : lookupName env "%e" = some (.ptr e)) (hb1 : 1 ≤ b) :
    denoteCode (stage2NoEventCalls gap) entryA4
        (stateAt (cells (entryCells3 ep c ++ entryCells2 b c ++ entryCells1 c e) env)
          (stage2NoEventStepState s
            (writeBytes (writeBytes
              (writeBytes (writeBytes (entryMem1 c e s.mem) c (natToBytes b 8))
                (c + 8) (natToBytes (BitVec.ofNat 64 n).toNat 8))
              (c + 16) (natToBytes ep 8))
              (c + 24) (natToBytes (BitVec.ofNat 64 nep).toNat 8)) s.next)) =
      some (stateAt (cells (entryCells4 b c ++ entryCells3 ep c ++ entryCells2 b c ++ entryCells1 c e) env)
        (stage2NoEventStepState s
          (writeBytes
            (writeBytes (writeBytes
              (writeBytes (writeBytes (entryMem1 c e s.mem) c (natToBytes b 8))
                (c + 8) (natToBytes (BitVec.ofNat 64 n).toNat 8))
              (c + 16) (natToBytes ep 8))
              (c + 24) (natToBytes (BitVec.ofNat 64 nep).toNat 8))
            (c + 1112) (natToBytes e 8)) s.next)) := by
  unfold entryA4
  rw [stage2NoEventWalk_denote_store_ptr (calls := stage2NoEventCalls gap)
    (env := _) (s := _) (x := e) (a := c + 1112) "%e" "%e3"
    (by repeat rw [lookupName_cons_ne _ _ (by decide)]
        rw [lookupName_cells_of_notin (cs := entryCells3 ep c ++ entryCells2 b c ++ entryCells1 c e)
          (n := "%e") (env := env) (by rw [entryCells1, entryCells2, entryCells3, List.map_append, List.map_append]; simp only [List.map_cons, List.map_nil]; decide)]
        exact he)
    (by rw [cells_append, cells_append, entryCells3]
        simp only [cells, List.cons_append, List.nil_append, lookupName_cons_self])]
  rw [stage2NoEventWalk_denote_gep8_imm (calls := stage2NoEventCalls gap)
    (env := _) (s := _) (a := b) (bytes := 1) "%invariant.gep" "%b"
    (BitVec.ofNat 64 1)
    (by repeat rw [lookupName_cons_ne _ _ (by decide)]
        rw [lookupName_cells_of_notin (cs := entryCells3 ep c ++ entryCells2 b c ++ entryCells1 c e)
          (n := "%b") (env := env) (by rw [entryCells1, entryCells2, entryCells3, List.map_append, List.map_append]; simp only [List.map_cons, List.map_nil]; decide)]
        exact hb) (by decide) (by decide)]
  rw [stage2NoEventWalk_denote_gep8_imm_m1 (calls := stage2NoEventCalls gap)
    (env := _) (s := _) (a := b) "%invariant.gep1068" "%b"
    (by repeat rw [lookupName_cons_ne _ _ (by decide)]
        rw [lookupName_cells_of_notin (cs := entryCells3 ep c ++ entryCells2 b c ++ entryCells1 c e)
          (n := "%b") (env := env) (by rw [entryCells1, entryCells2, entryCells3, List.map_append, List.map_append]; simp only [List.map_cons, List.map_nil]; decide)]
        exact hb) hb1]
  rw [stage2NoEventWalk_denote_gep8_imm (calls := stage2NoEventCalls gap)
    (env := _) (s := _) (a := c) (bytes := 32) "%k219" "%c"
    (BitVec.ofNat 64 32)
    (by repeat rw [lookupName_cons_ne _ _ (by decide)]
        rw [lookupName_cells_of_notin (cs := entryCells3 ep c ++ entryCells2 b c ++ entryCells1 c e)
          (n := "%c") (env := env) (by rw [entryCells1, entryCells2, entryCells3, List.map_append, List.map_append]; simp only [List.map_cons, List.map_nil]; decide)]
        exact hc) (by decide) (by decide)]
  rw [entryCells1, entryCells2, entryCells3, entryCells4, entryMem1, denoteCode_nil]
  rw [cells_append]
  simp only [stage2NoEventStepState_mem]
  simp only [stage2NoEventStepState_next]
  simp only [stage2NoEventStepState_nest]
  rfl

/-- Sub-row E's run. -/
theorem entryA5_denote {gap : Calls} (env : Env) (s : State)
    {b n ep nep c e : Nat}
    (hnep : lookupName env "%nep" = some (.int 64 (BitVec.ofNat 64 nep))) :
    denoteCode (stage2NoEventCalls gap) entryA5
        (stateAt (cells (entryCells4 b c ++ entryCells3 ep c ++ entryCells2 b c ++ entryCells1 c e) env)
          (stage2NoEventStepState s
            (writeBytes
              (writeBytes (writeBytes
                (writeBytes (writeBytes (entryMem1 c e s.mem) c (natToBytes b 8))
                  (c + 8) (natToBytes (BitVec.ofNat 64 n).toNat 8))
                (c + 16) (natToBytes ep 8))
                (c + 24) (natToBytes (BitVec.ofNat 64 nep).toNat 8))
              (c + 1112) (natToBytes e 8)) s.next)) =
      some (stateAt (cells (entryCells5 nep ++ entryCells4 b c ++ entryCells3 ep c ++
          entryCells2 b c ++ entryCells1 c e) env)
        (stage2NoEventStepState s
          (writeBytes
            (writeBytes (writeBytes
              (writeBytes (writeBytes (entryMem1 c e s.mem) c (natToBytes b 8))
                (c + 8) (natToBytes (BitVec.ofNat 64 n).toNat 8))
              (c + 16) (natToBytes ep 8))
              (c + 24) (natToBytes (BitVec.ofNat 64 nep).toNat 8))
            (c + 1112) (natToBytes e 8)) s.next)) := by
  unfold entryA5
  rw [stage2NoEventWalk_denote_icmp_imm (calls := stage2NoEventCalls gap)
    (env := _) (s := _) (d := "%cmp.not.peel1401.not") (a := "%nep")
    (p := IPred.eq) (w := 64) (x := BitVec.ofNat 64 nep) (c := BitVec.ofNat 64 0)
    (by repeat rw [lookupName_cons_ne _ _ (by decide)]
        rw [lookupName_cells_of_notin (cs := entryCells4 b c ++ entryCells3 ep c ++ entryCells2 b c ++ entryCells1 c e)
          (n := "%nep") (env := env)
          (by rw [entryCells1, entryCells2, entryCells3, entryCells4, List.map_append, List.map_append, List.map_append]; simp only [List.map_cons, List.map_nil]; decide)]
        exact hnep)]
  rw [entryCells1, entryCells2, entryCells3, entryCells4, entryCells5, denoteCode_nil]
  rw [cells_append]
  rfl

/-- The whole entry suffix: the five sub-rows composed. -/
theorem entrySuffix_denote {gap : Calls} (env : Env) (s : State)
    {b n ep nep c e : Nat}
    (hb : lookupName env "%b" = some (.ptr b))
    (hn : lookupName env "%n" = some (.int 64 (BitVec.ofNat 64 n)))
    (hep : lookupName env "%ep" = some (.ptr ep))
    (hnep : lookupName env "%nep" = some (.int 64 (BitVec.ofNat 64 nep)))
    (hc : lookupName env "%c" = some (.ptr c))
    (he : lookupName env "%e" = some (.ptr e))
    (hb1 : 1 ≤ b) :
    denoteCode (stage2NoEventCalls gap) entrySuffixInstrs (stateAt env s) =
      some (stateAt
        (cells (entryCells5 nep ++ entryCells4 b c ++ entryCells3 ep c ++
          entryCells2 b c ++ entryCells1 c e) env)
        (stage2NoEventStepState s
          (writeBytes
            (writeBytes (writeBytes
              (writeBytes (writeBytes (entryMem1 c e s.mem) c (natToBytes b 8))
                (c + 8) (natToBytes (BitVec.ofNat 64 n).toNat 8))
              (c + 16) (natToBytes ep 8))
              (c + 24) (natToBytes (BitVec.ofNat 64 nep).toNat 8))
            (c + 1112) (natToBytes e 8)) s.next)) := by
  rw [entrySuffix_pieces]
  rw [denoteCode_append_apply (h := entryA1_denote (env := env) (s := s) hc he)
    (hb := by decide)]
  rw [denoteCode_append_apply (h := entryA2_denote (env := env) (s := s) hb hn hc)
    (hb := by decide)]
  rw [denoteCode_append_apply (h := entryA3_denote (env := env) (s := s) hb hn hep hnep hc)
    (hb := by decide)]
  rw [denoteCode_append_apply (h := entryA4_denote (env := env) (s := s) hb hn hep hnep hc he hb1)
    (hb := by decide)]
  exact entryA5_denote (env := env) (s := s) hnep

/-- The entry terminator's `nep ≠ 0` edge: the block hands off to the preheader. -/
theorem entrySuffix_jump {gap : Calls} (env : Env) (s : State)
    {b n ep nep c e : Nat} (mem : Mem)
    (hbit : evalICmp .eq (BitVec.ofNat 64 nep) (BitVec.ofNat 64 0) = BitVec.ofNat 1 0) :
    execTerm
        (stateAt
          (cells (entryCells5 nep ++ entryCells4 b c ++ entryCells3 ep c ++
            entryCells2 b c ++ entryCells1 c e) env)
          (stage2NoEventStepState s mem s.next))
        (.condbr (.reg "%cmp.not.peel1401.not") "if.then" "if.end.peel.preheader") =
      .jump { env := ("%cmp.not.peel1401.not", .int 1 (BitVec.ofNat 1 0)) ::
                cells (entryCells4 b c ++ entryCells3 ep c ++ entryCells2 b c ++
                  entryCells1 c e) env,
              mem := mem, next := s.next,
              pc := "if.end.peel.preheader", pre := some s.pc } := by
  simp only [execTerm, stateAt, evalOperand, entryCells5, cells,
    List.cons_append, List.nil_append, lookupName_cons_self, hbit,
    if_neg (by decide : (0 : BitVec 1) ≠ 1), if_pos (by decide : (0 : BitVec 1) = 0)]
  rfl

/-- The preheader's fourteen scratch addresses: `%scratch + 1 … 7`, twice. -/
def preHeaderInstrs : List Instr :=
  [     Instr.gep "%invariant.gep1650" (Ty.int 8) (Operand.reg "%scratch")
      (Operand.imm (.int 64 (BitVec.ofNat 64 1))),
    Instr.gep "%invariant.gep1652" (Ty.int 8) (Operand.reg "%scratch")
      (Operand.imm (.int 64 (BitVec.ofNat 64 2))),
    Instr.gep "%invariant.gep1654" (Ty.int 8) (Operand.reg "%scratch")
      (Operand.imm (.int 64 (BitVec.ofNat 64 3))),
    Instr.gep "%invariant.gep1656" (Ty.int 8) (Operand.reg "%scratch")
      (Operand.imm (.int 64 (BitVec.ofNat 64 4))),
    Instr.gep "%invariant.gep1658" (Ty.int 8) (Operand.reg "%scratch")
      (Operand.imm (.int 64 (BitVec.ofNat 64 5))),
    Instr.gep "%invariant.gep1660" (Ty.int 8) (Operand.reg "%scratch")
      (Operand.imm (.int 64 (BitVec.ofNat 64 6))),
    Instr.gep "%invariant.gep1662" (Ty.int 8) (Operand.reg "%scratch")
      (Operand.imm (.int 64 (BitVec.ofNat 64 7))),
    Instr.gep "%invariant.gep1664" (Ty.int 8) (Operand.reg "%scratch")
      (Operand.imm (.int 64 (BitVec.ofNat 64 1))),
    Instr.gep "%invariant.gep1666" (Ty.int 8) (Operand.reg "%scratch")
      (Operand.imm (.int 64 (BitVec.ofNat 64 2))),
    Instr.gep "%invariant.gep1668" (Ty.int 8) (Operand.reg "%scratch")
      (Operand.imm (.int 64 (BitVec.ofNat 64 3))),
    Instr.gep "%invariant.gep1670" (Ty.int 8) (Operand.reg "%scratch")
      (Operand.imm (.int 64 (BitVec.ofNat 64 4))),
    Instr.gep "%invariant.gep1672" (Ty.int 8) (Operand.reg "%scratch")
      (Operand.imm (.int 64 (BitVec.ofNat 64 5))),
    Instr.gep "%invariant.gep1674" (Ty.int 8) (Operand.reg "%scratch")
      (Operand.imm (.int 64 (BitVec.ofNat 64 6))),
    Instr.gep "%invariant.gep1676" (Ty.int 8) (Operand.reg "%scratch")
      (Operand.imm (.int 64 (BitVec.ofNat 64 7))) ]

theorem preHeader_split :
    (stage2NoEventBody.findBlock "if.end.peel.preheader").map (fun b => b.instrs)
      = some preHeaderInstrs := by
  decide

/-- The preheader's cells. -/
def preHeaderCells (a : Nat) : List (String × Value) :=
  [
   ("%invariant.gep1676", .ptr (a + 7)),
   ("%invariant.gep1674", .ptr (a + 6)),
   ("%invariant.gep1672", .ptr (a + 5)),
   ("%invariant.gep1670", .ptr (a + 4)),
   ("%invariant.gep1668", .ptr (a + 3)),
   ("%invariant.gep1666", .ptr (a + 2)),
   ("%invariant.gep1664", .ptr (a + 1)),
   ("%invariant.gep1662", .ptr (a + 7)),
   ("%invariant.gep1660", .ptr (a + 6)),
   ("%invariant.gep1658", .ptr (a + 5)),
   ("%invariant.gep1656", .ptr (a + 4)),
   ("%invariant.gep1654", .ptr (a + 3)),
   ("%invariant.gep1652", .ptr (a + 2)),
   ("%invariant.gep1650", .ptr (a + 1)),
   ]

/-- The preheader's fourteen scratch addresses, run from the entry suffix's state. -/
theorem preHeader_denote {gap : Calls} (env : Env) (s : State)
    {a b n ep nep c e : Nat}
    (hs : lookupName env "%scratch" = some (.ptr a)) :
    denoteCode (stage2NoEventCalls gap) preHeaderInstrs
        (stateAt (cells (entryCells5 nep ++ entryCells4 b c ++ entryCells3 ep c ++
          entryCells2 b c ++ entryCells1 c e) env) s) =
      some (stateAt (cells (preHeaderCells a ++ entryCells5 nep ++ entryCells4 b c ++
        entryCells3 ep c ++ entryCells2 b c ++ entryCells1 c e) env) s) := by
  unfold preHeaderInstrs
  rw [stage2NoEventWalk_denote_gep8_imm (calls := stage2NoEventCalls gap)
    (env := _) (s := _) (a := a) (bytes := 1) "%invariant.gep1650" "%scratch"
    (BitVec.ofNat 64 1)
    (by repeat rw [lookupName_cons_ne _ _ (by decide)]
        rw [lookupName_cells_of_notin (cs := entryCells5 nep ++ entryCells4 b c ++ entryCells3 ep c ++ entryCells2 b c ++ entryCells1 c e) (n := "%scratch") (env := env) (by rw [entryCells1, entryCells2, entryCells3, entryCells4, entryCells5, List.map_append, List.map_append, List.map_append, List.map_append]; simp only [List.map_cons, List.map_nil]; decide)]
        exact hs) (by decide) (by decide)]
  rw [stage2NoEventWalk_denote_gep8_imm (calls := stage2NoEventCalls gap)
    (env := _) (s := _) (a := a) (bytes := 2) "%invariant.gep1652" "%scratch"
    (BitVec.ofNat 64 2)
    (by repeat rw [lookupName_cons_ne _ _ (by decide)]
        rw [lookupName_cells_of_notin (cs := entryCells5 nep ++ entryCells4 b c ++ entryCells3 ep c ++ entryCells2 b c ++ entryCells1 c e) (n := "%scratch") (env := env) (by rw [entryCells1, entryCells2, entryCells3, entryCells4, entryCells5, List.map_append, List.map_append, List.map_append, List.map_append]; simp only [List.map_cons, List.map_nil]; decide)]
        exact hs) (by decide) (by decide)]
  rw [stage2NoEventWalk_denote_gep8_imm (calls := stage2NoEventCalls gap)
    (env := _) (s := _) (a := a) (bytes := 3) "%invariant.gep1654" "%scratch"
    (BitVec.ofNat 64 3)
    (by repeat rw [lookupName_cons_ne _ _ (by decide)]
        rw [lookupName_cells_of_notin (cs := entryCells5 nep ++ entryCells4 b c ++ entryCells3 ep c ++ entryCells2 b c ++ entryCells1 c e) (n := "%scratch") (env := env) (by rw [entryCells1, entryCells2, entryCells3, entryCells4, entryCells5, List.map_append, List.map_append, List.map_append, List.map_append]; simp only [List.map_cons, List.map_nil]; decide)]
        exact hs) (by decide) (by decide)]
  rw [stage2NoEventWalk_denote_gep8_imm (calls := stage2NoEventCalls gap)
    (env := _) (s := _) (a := a) (bytes := 4) "%invariant.gep1656" "%scratch"
    (BitVec.ofNat 64 4)
    (by repeat rw [lookupName_cons_ne _ _ (by decide)]
        rw [lookupName_cells_of_notin (cs := entryCells5 nep ++ entryCells4 b c ++ entryCells3 ep c ++ entryCells2 b c ++ entryCells1 c e) (n := "%scratch") (env := env) (by rw [entryCells1, entryCells2, entryCells3, entryCells4, entryCells5, List.map_append, List.map_append, List.map_append, List.map_append]; simp only [List.map_cons, List.map_nil]; decide)]
        exact hs) (by decide) (by decide)]
  rw [stage2NoEventWalk_denote_gep8_imm (calls := stage2NoEventCalls gap)
    (env := _) (s := _) (a := a) (bytes := 5) "%invariant.gep1658" "%scratch"
    (BitVec.ofNat 64 5)
    (by repeat rw [lookupName_cons_ne _ _ (by decide)]
        rw [lookupName_cells_of_notin (cs := entryCells5 nep ++ entryCells4 b c ++ entryCells3 ep c ++ entryCells2 b c ++ entryCells1 c e) (n := "%scratch") (env := env) (by rw [entryCells1, entryCells2, entryCells3, entryCells4, entryCells5, List.map_append, List.map_append, List.map_append, List.map_append]; simp only [List.map_cons, List.map_nil]; decide)]
        exact hs) (by decide) (by decide)]
  rw [stage2NoEventWalk_denote_gep8_imm (calls := stage2NoEventCalls gap)
    (env := _) (s := _) (a := a) (bytes := 6) "%invariant.gep1660" "%scratch"
    (BitVec.ofNat 64 6)
    (by repeat rw [lookupName_cons_ne _ _ (by decide)]
        rw [lookupName_cells_of_notin (cs := entryCells5 nep ++ entryCells4 b c ++ entryCells3 ep c ++ entryCells2 b c ++ entryCells1 c e) (n := "%scratch") (env := env) (by rw [entryCells1, entryCells2, entryCells3, entryCells4, entryCells5, List.map_append, List.map_append, List.map_append, List.map_append]; simp only [List.map_cons, List.map_nil]; decide)]
        exact hs) (by decide) (by decide)]
  rw [stage2NoEventWalk_denote_gep8_imm (calls := stage2NoEventCalls gap)
    (env := _) (s := _) (a := a) (bytes := 7) "%invariant.gep1662" "%scratch"
    (BitVec.ofNat 64 7)
    (by repeat rw [lookupName_cons_ne _ _ (by decide)]
        rw [lookupName_cells_of_notin (cs := entryCells5 nep ++ entryCells4 b c ++ entryCells3 ep c ++ entryCells2 b c ++ entryCells1 c e) (n := "%scratch") (env := env) (by rw [entryCells1, entryCells2, entryCells3, entryCells4, entryCells5, List.map_append, List.map_append, List.map_append, List.map_append]; simp only [List.map_cons, List.map_nil]; decide)]
        exact hs) (by decide) (by decide)]
  rw [stage2NoEventWalk_denote_gep8_imm (calls := stage2NoEventCalls gap)
    (env := _) (s := _) (a := a) (bytes := 1) "%invariant.gep1664" "%scratch"
    (BitVec.ofNat 64 1)
    (by repeat rw [lookupName_cons_ne _ _ (by decide)]
        rw [lookupName_cells_of_notin (cs := entryCells5 nep ++ entryCells4 b c ++ entryCells3 ep c ++ entryCells2 b c ++ entryCells1 c e) (n := "%scratch") (env := env) (by rw [entryCells1, entryCells2, entryCells3, entryCells4, entryCells5, List.map_append, List.map_append, List.map_append, List.map_append]; simp only [List.map_cons, List.map_nil]; decide)]
        exact hs) (by decide) (by decide)]
  rw [stage2NoEventWalk_denote_gep8_imm (calls := stage2NoEventCalls gap)
    (env := _) (s := _) (a := a) (bytes := 2) "%invariant.gep1666" "%scratch"
    (BitVec.ofNat 64 2)
    (by repeat rw [lookupName_cons_ne _ _ (by decide)]
        rw [lookupName_cells_of_notin (cs := entryCells5 nep ++ entryCells4 b c ++ entryCells3 ep c ++ entryCells2 b c ++ entryCells1 c e) (n := "%scratch") (env := env) (by rw [entryCells1, entryCells2, entryCells3, entryCells4, entryCells5, List.map_append, List.map_append, List.map_append, List.map_append]; simp only [List.map_cons, List.map_nil]; decide)]
        exact hs) (by decide) (by decide)]
  rw [stage2NoEventWalk_denote_gep8_imm (calls := stage2NoEventCalls gap)
    (env := _) (s := _) (a := a) (bytes := 3) "%invariant.gep1668" "%scratch"
    (BitVec.ofNat 64 3)
    (by repeat rw [lookupName_cons_ne _ _ (by decide)]
        rw [lookupName_cells_of_notin (cs := entryCells5 nep ++ entryCells4 b c ++ entryCells3 ep c ++ entryCells2 b c ++ entryCells1 c e) (n := "%scratch") (env := env) (by rw [entryCells1, entryCells2, entryCells3, entryCells4, entryCells5, List.map_append, List.map_append, List.map_append, List.map_append]; simp only [List.map_cons, List.map_nil]; decide)]
        exact hs) (by decide) (by decide)]
  rw [stage2NoEventWalk_denote_gep8_imm (calls := stage2NoEventCalls gap)
    (env := _) (s := _) (a := a) (bytes := 4) "%invariant.gep1670" "%scratch"
    (BitVec.ofNat 64 4)
    (by repeat rw [lookupName_cons_ne _ _ (by decide)]
        rw [lookupName_cells_of_notin (cs := entryCells5 nep ++ entryCells4 b c ++ entryCells3 ep c ++ entryCells2 b c ++ entryCells1 c e) (n := "%scratch") (env := env) (by rw [entryCells1, entryCells2, entryCells3, entryCells4, entryCells5, List.map_append, List.map_append, List.map_append, List.map_append]; simp only [List.map_cons, List.map_nil]; decide)]
        exact hs) (by decide) (by decide)]
  rw [stage2NoEventWalk_denote_gep8_imm (calls := stage2NoEventCalls gap)
    (env := _) (s := _) (a := a) (bytes := 5) "%invariant.gep1672" "%scratch"
    (BitVec.ofNat 64 5)
    (by repeat rw [lookupName_cons_ne _ _ (by decide)]
        rw [lookupName_cells_of_notin (cs := entryCells5 nep ++ entryCells4 b c ++ entryCells3 ep c ++ entryCells2 b c ++ entryCells1 c e) (n := "%scratch") (env := env) (by rw [entryCells1, entryCells2, entryCells3, entryCells4, entryCells5, List.map_append, List.map_append, List.map_append, List.map_append]; simp only [List.map_cons, List.map_nil]; decide)]
        exact hs) (by decide) (by decide)]
  rw [stage2NoEventWalk_denote_gep8_imm (calls := stage2NoEventCalls gap)
    (env := _) (s := _) (a := a) (bytes := 6) "%invariant.gep1674" "%scratch"
    (BitVec.ofNat 64 6)
    (by repeat rw [lookupName_cons_ne _ _ (by decide)]
        rw [lookupName_cells_of_notin (cs := entryCells5 nep ++ entryCells4 b c ++ entryCells3 ep c ++ entryCells2 b c ++ entryCells1 c e) (n := "%scratch") (env := env) (by rw [entryCells1, entryCells2, entryCells3, entryCells4, entryCells5, List.map_append, List.map_append, List.map_append, List.map_append]; simp only [List.map_cons, List.map_nil]; decide)]
        exact hs) (by decide) (by decide)]
  rw [stage2NoEventWalk_denote_gep8_imm (calls := stage2NoEventCalls gap)
    (env := _) (s := _) (a := a) (bytes := 7) "%invariant.gep1676" "%scratch"
    (BitVec.ofNat 64 7)
    (by repeat rw [lookupName_cons_ne _ _ (by decide)]
        rw [lookupName_cells_of_notin (cs := entryCells5 nep ++ entryCells4 b c ++ entryCells3 ep c ++ entryCells2 b c ++ entryCells1 c e) (n := "%scratch") (env := env) (by rw [entryCells1, entryCells2, entryCells3, entryCells4, entryCells5, List.map_append, List.map_append, List.map_append, List.map_append]; simp only [List.map_cons, List.map_nil]; decide)]
        exact hs) (by decide) (by decide)]
  rw [cells_append]
  rfl

/-- The preheader's terminator: an unconditional hand-off to the loop head. -/
theorem preHeader_jump (env : Env) (s : State) {a b n ep nep c e : Nat} :
    execTerm (stateAt (cells (preHeaderCells a ++ entryCells5 nep ++ entryCells4 b c ++
        entryCells3 ep c ++ entryCells2 b c ++ entryCells1 c e) env) s)
        (.br "if.end.peel") =
      .jump (stage2NoEventJumpState
        (stateAt (cells (preHeaderCells a ++ entryCells5 nep ++ entryCells4 b c ++
          entryCells3 ep c ++ entryCells2 b c ++ entryCells1 c e) env) s)
        s.mem s.next "if.end.peel" s.pc) := by
  simp only [execTerm, stage2NoEventJumpState, stateAt]

/-- One control step of the preheader: its fourteen addresses and its `br`. -/
theorem preHeader_step {gap : Calls} (env : Env) (s : State)
    {a b n ep nep c e : Nat}
    (hs : lookupName env "%scratch" = some (.ptr a))
    (hpc : s.pc = "if.end.peel.preheader") :
    step (stage2NoEventCalls gap) stage2NoEventBody
        (stateAt (cells (entryCells5 nep ++ entryCells4 b c ++ entryCells3 ep c ++
          entryCells2 b c ++ entryCells1 c e) env) s) =
      .jump (stage2NoEventJumpState
        (stateAt (cells (preHeaderCells a ++ entryCells5 nep ++ entryCells4 b c ++
          entryCells3 ep c ++ entryCells2 b c ++ entryCells1 c e) env) s)
        s.mem s.next "if.end.peel" s.pc) := by
  have hfind : stage2NoEventBody.findBlock s.pc = some
      { name := "if.end.peel.preheader", instrs := preHeaderInstrs,
        term := .br "if.end.peel" } := by
    rw [hpc, preHeaderInstrs]; decide
  exact stage2NoEventWalk_step_at_block hfind
    (preHeader_denote (env := env) (s := s) (n := 0) hs)
    (preHeader_jump (env := env) (s := s) (n := 0))

/-- The head's phis at the preheader's edge: the base step's last link. -/
theorem preHeader_phi {gap : Calls} (env : Env) (s : State)
    {a b n ep nep c e : Nat}
    (hpcp : s.pc = "if.end.peel.preheader") :
    denoteCode (stage2NoEventCalls gap) loopHeadPhiInstrs
        (stateAt (cells (preHeaderCells a ++ entryCells5 nep ++ entryCells4 b c ++
          entryCells3 ep c ++ entryCells2 b c ++ entryCells1 c e) env)
          (stage2NoEventJumpState s s.mem s.next "if.end.peel" "if.end.peel.preheader")) =
      some (stateAt (cells loopHeadPhiCells
        (cells (preHeaderCells a ++ entryCells5 nep ++ entryCells4 b c ++
          entryCells3 ep c ++ entryCells2 b c ++ entryCells1 c e) env))
        (stage2NoEventJumpState s s.mem s.next "if.end.peel" "if.end.peel.preheader")) :=
  baseHeadPhi_denote _ _ _ (by simp only [stage2NoEventJumpState])

/-- The loop head's terminator: its unconditional hand-off to the dispatch root. -/
theorem loopHead_jump (env : Env) (s : State) :
    execTerm (stateAt (cells loopHeadPhiCells env) s) (.br "NodeBlock5") =
      .jump (stage2NoEventJumpState (stateAt (cells loopHeadPhiCells env) s)
        s.mem s.next "NodeBlock5" s.pc) := by
  simp only [execTerm, stage2NoEventJumpState, stateAt]

/-- `LeafBlock`: the byte against 34. -/
def leafBlockInstrs : List Instr :=
  [ Instr.icmp "%SwitchLeaf" IPred.eq 8 (Operand.reg "%3")
      (Operand.imm (.int 8 (BitVec.ofNat 8 34))) ]

/-- The `LeafBlock` dispatch row. -/
theorem leafBlock_denote {calls : Calls} (env : Env) (s : State)
    {x : BitVec 8} (h3 : lookupName env "%3" = some (.int 8 x)) :
    denoteCode calls leafBlockInstrs (stateAt env s) =
      some (stateAt (("%SwitchLeaf", .int 1 (evalICmp .eq x (BitVec.ofNat 8 34))) :: env) s) := by
  unfold leafBlockInstrs
  rw [stage2NoEventWalk_denote_icmp_imm (calls := calls) (env := env) (s := s)
    (d := "%SwitchLeaf") (a := "%3") (p := IPred.eq) (w := 8) (x := x)
    (c := BitVec.ofNat 8 34) h3]
  rfl

/-- `LeafBlock`, pinned. -/
def leafBlockBlock : Block :=
  { name := "LeafBlock", instrs := leafBlockInstrs,
    term := Term.condbr (Operand.reg "%SwitchLeaf") "string_value" "scalar" }

theorem leafBlockBlock_find :
    stage2NoEventBody.findBlock "LeafBlock" = some leafBlockBlock := by
  decide

/-- `nodeBlock5`'s `%Pivot6` branch, taken (`LeafBlock`). -/
theorem nodeBlock5_branch_true {calls : Calls} (env : Env) (s : State)
    {x : BitVec 8} (h3 : lookupName env "%3" = some (.int 8 x))
    (hbit : evalICmp IPred.slt x (BitVec.ofNat 8 91) = BitVec.ofNat 1 1) :
    execTerm (stateAt (("%Pivot6", .int 1 (evalICmp IPred.slt x (BitVec.ofNat 8 91))) :: env) s)
        (.condbr (.reg "%Pivot6") "LeafBlock" "NodeBlock") =
      .jump (stage2NoEventJumpState
        (stateAt (("%Pivot6", .int 1 (evalICmp IPred.slt x (BitVec.ofNat 8 91))) :: env) s)
        s.mem s.next "LeafBlock" s.pc) := by
  have hop : evalOperand
      (stateAt (("%Pivot6", .int 1 (evalICmp IPred.slt x (BitVec.ofNat 8 91))) :: env) s)
      (.reg "%Pivot6") = some (.int 1 (evalICmp IPred.slt x (BitVec.ofNat 8 91))) :=
    BlockEval.evalOperand_reg_of _ _ "%Pivot6"
      (.int 1 (evalICmp IPred.slt x (BitVec.ofNat 8 91))) (by simp only [lookupName_cons_self])
  simp only [execTerm, hop, hbit, stage2NoEventJumpState, stage2NoEventStepState, stateAt]
  rfl


/-- `nodeBlock5`'s `%Pivot6` branch, taken (`NodeBlock`). -/
theorem nodeBlock5_branch_false {calls : Calls} (env : Env) (s : State)
    {x : BitVec 8} (h3 : lookupName env "%3" = some (.int 8 x))
    (hbit : evalICmp IPred.slt x (BitVec.ofNat 8 91) = BitVec.ofNat 1 0) :
    execTerm (stateAt (("%Pivot6", .int 1 (evalICmp IPred.slt x (BitVec.ofNat 8 91))) :: env) s)
        (.condbr (.reg "%Pivot6") "LeafBlock" "NodeBlock") =
      .jump (stage2NoEventJumpState
        (stateAt (("%Pivot6", .int 1 (evalICmp IPred.slt x (BitVec.ofNat 8 91))) :: env) s)
        s.mem s.next "NodeBlock" s.pc) := by
  have hop : evalOperand
      (stateAt (("%Pivot6", .int 1 (evalICmp IPred.slt x (BitVec.ofNat 8 91))) :: env) s)
      (.reg "%Pivot6") = some (.int 1 (evalICmp IPred.slt x (BitVec.ofNat 8 91))) :=
    BlockEval.evalOperand_reg_of _ _ "%Pivot6"
      (.int 1 (evalICmp IPred.slt x (BitVec.ofNat 8 91))) (by simp only [lookupName_cons_self])
  simp only [execTerm, hop, hbit, stage2NoEventJumpState, stage2NoEventStepState, stateAt]
  rfl


/-- `nodeBlock`'s `%Pivot` branch, taken (`LeafBlock1`). -/
theorem nodeBlock_branch_true {calls : Calls} (env : Env) (s : State)
    {x : BitVec 8} (h3 : lookupName env "%3" = some (.int 8 x))
    (hbit : evalICmp IPred.slt x (BitVec.ofNat 8 123) = BitVec.ofNat 1 1) :
    execTerm (stateAt (("%Pivot", .int 1 (evalICmp IPred.slt x (BitVec.ofNat 8 123))) :: env) s)
        (.condbr (.reg "%Pivot") "LeafBlock1" "LeafBlock3") =
      .jump (stage2NoEventJumpState
        (stateAt (("%Pivot", .int 1 (evalICmp IPred.slt x (BitVec.ofNat 8 123))) :: env) s)
        s.mem s.next "LeafBlock1" s.pc) := by
  have hop : evalOperand
      (stateAt (("%Pivot", .int 1 (evalICmp IPred.slt x (BitVec.ofNat 8 123))) :: env) s)
      (.reg "%Pivot") = some (.int 1 (evalICmp IPred.slt x (BitVec.ofNat 8 123))) :=
    BlockEval.evalOperand_reg_of _ _ "%Pivot"
      (.int 1 (evalICmp IPred.slt x (BitVec.ofNat 8 123))) (by simp only [lookupName_cons_self])
  simp only [execTerm, hop, hbit, stage2NoEventJumpState, stage2NoEventStepState, stateAt]
  rfl


/-- `nodeBlock`'s `%Pivot` branch, taken (`LeafBlock3`). -/
theorem nodeBlock_branch_false {calls : Calls} (env : Env) (s : State)
    {x : BitVec 8} (h3 : lookupName env "%3" = some (.int 8 x))
    (hbit : evalICmp IPred.slt x (BitVec.ofNat 8 123) = BitVec.ofNat 1 0) :
    execTerm (stateAt (("%Pivot", .int 1 (evalICmp IPred.slt x (BitVec.ofNat 8 123))) :: env) s)
        (.condbr (.reg "%Pivot") "LeafBlock1" "LeafBlock3") =
      .jump (stage2NoEventJumpState
        (stateAt (("%Pivot", .int 1 (evalICmp IPred.slt x (BitVec.ofNat 8 123))) :: env) s)
        s.mem s.next "LeafBlock3" s.pc) := by
  have hop : evalOperand
      (stateAt (("%Pivot", .int 1 (evalICmp IPred.slt x (BitVec.ofNat 8 123))) :: env) s)
      (.reg "%Pivot") = some (.int 1 (evalICmp IPred.slt x (BitVec.ofNat 8 123))) :=
    BlockEval.evalOperand_reg_of _ _ "%Pivot"
      (.int 1 (evalICmp IPred.slt x (BitVec.ofNat 8 123))) (by simp only [lookupName_cons_self])
  simp only [execTerm, hop, hbit, stage2NoEventJumpState, stage2NoEventStepState, stateAt]
  rfl


/-- `leafBlock3`'s `%SwitchLeaf4` branch, taken (`if.then9`). -/
theorem leafBlock3_branch_true {calls : Calls} (env : Env) (s : State)
    {x : BitVec 8} (h3 : lookupName env "%3" = some (.int 8 x))
    (hbit : evalICmp IPred.eq x (BitVec.ofNat 8 123) = BitVec.ofNat 1 1) :
    execTerm (stateAt (("%SwitchLeaf4", .int 1 (evalICmp IPred.eq x (BitVec.ofNat 8 123))) :: env) s)
        (.condbr (.reg "%SwitchLeaf4") "if.then9" "scalar") =
      .jump (stage2NoEventJumpState
        (stateAt (("%SwitchLeaf4", .int 1 (evalICmp IPred.eq x (BitVec.ofNat 8 123))) :: env) s)
        s.mem s.next "if.then9" s.pc) := by
  have hop : evalOperand
      (stateAt (("%SwitchLeaf4", .int 1 (evalICmp IPred.eq x (BitVec.ofNat 8 123))) :: env) s)
      (.reg "%SwitchLeaf4") = some (.int 1 (evalICmp IPred.eq x (BitVec.ofNat 8 123))) :=
    BlockEval.evalOperand_reg_of _ _ "%SwitchLeaf4"
      (.int 1 (evalICmp IPred.eq x (BitVec.ofNat 8 123))) (by simp only [lookupName_cons_self])
  simp only [execTerm, hop, hbit, stage2NoEventJumpState, stage2NoEventStepState, stateAt]
  rfl


/-- `leafBlock3`'s `%SwitchLeaf4` branch, taken (`scalar`). -/
theorem leafBlock3_branch_false {calls : Calls} (env : Env) (s : State)
    {x : BitVec 8} (h3 : lookupName env "%3" = some (.int 8 x))
    (hbit : evalICmp IPred.eq x (BitVec.ofNat 8 123) = BitVec.ofNat 1 0) :
    execTerm (stateAt (("%SwitchLeaf4", .int 1 (evalICmp IPred.eq x (BitVec.ofNat 8 123))) :: env) s)
        (.condbr (.reg "%SwitchLeaf4") "if.then9" "scalar") =
      .jump (stage2NoEventJumpState
        (stateAt (("%SwitchLeaf4", .int 1 (evalICmp IPred.eq x (BitVec.ofNat 8 123))) :: env) s)
        s.mem s.next "scalar" s.pc) := by
  have hop : evalOperand
      (stateAt (("%SwitchLeaf4", .int 1 (evalICmp IPred.eq x (BitVec.ofNat 8 123))) :: env) s)
      (.reg "%SwitchLeaf4") = some (.int 1 (evalICmp IPred.eq x (BitVec.ofNat 8 123))) :=
    BlockEval.evalOperand_reg_of _ _ "%SwitchLeaf4"
      (.int 1 (evalICmp IPred.eq x (BitVec.ofNat 8 123))) (by simp only [lookupName_cons_self])
  simp only [execTerm, hop, hbit, stage2NoEventJumpState, stage2NoEventStepState, stateAt]
  rfl


/-- `leafBlock1`'s `%SwitchLeaf2` branch, taken (`if.then35.peel`). -/
theorem leafBlock1_branch_true {calls : Calls} (env : Env) (s : State)
    {x : BitVec 8} (h3 : lookupName env "%3" = some (.int 8 x))
    (hbit : evalICmp IPred.eq x (BitVec.ofNat 8 91) = BitVec.ofNat 1 1) :
    execTerm (stateAt (("%SwitchLeaf2", .int 1 (evalICmp IPred.eq x (BitVec.ofNat 8 91))) :: env) s)
        (.condbr (.reg "%SwitchLeaf2") "if.then35.peel" "scalar") =
      .jump (stage2NoEventJumpState
        (stateAt (("%SwitchLeaf2", .int 1 (evalICmp IPred.eq x (BitVec.ofNat 8 91))) :: env) s)
        s.mem s.next "if.then35.peel" s.pc) := by
  have hop : evalOperand
      (stateAt (("%SwitchLeaf2", .int 1 (evalICmp IPred.eq x (BitVec.ofNat 8 91))) :: env) s)
      (.reg "%SwitchLeaf2") = some (.int 1 (evalICmp IPred.eq x (BitVec.ofNat 8 91))) :=
    BlockEval.evalOperand_reg_of _ _ "%SwitchLeaf2"
      (.int 1 (evalICmp IPred.eq x (BitVec.ofNat 8 91))) (by simp only [lookupName_cons_self])
  simp only [execTerm, hop, hbit, stage2NoEventJumpState, stage2NoEventStepState, stateAt]
  rfl


/-- `leafBlock1`'s `%SwitchLeaf2` branch, taken (`scalar`). -/
theorem leafBlock1_branch_false {calls : Calls} (env : Env) (s : State)
    {x : BitVec 8} (h3 : lookupName env "%3" = some (.int 8 x))
    (hbit : evalICmp IPred.eq x (BitVec.ofNat 8 91) = BitVec.ofNat 1 0) :
    execTerm (stateAt (("%SwitchLeaf2", .int 1 (evalICmp IPred.eq x (BitVec.ofNat 8 91))) :: env) s)
        (.condbr (.reg "%SwitchLeaf2") "if.then35.peel" "scalar") =
      .jump (stage2NoEventJumpState
        (stateAt (("%SwitchLeaf2", .int 1 (evalICmp IPred.eq x (BitVec.ofNat 8 91))) :: env) s)
        s.mem s.next "scalar" s.pc) := by
  have hop : evalOperand
      (stateAt (("%SwitchLeaf2", .int 1 (evalICmp IPred.eq x (BitVec.ofNat 8 91))) :: env) s)
      (.reg "%SwitchLeaf2") = some (.int 1 (evalICmp IPred.eq x (BitVec.ofNat 8 91))) :=
    BlockEval.evalOperand_reg_of _ _ "%SwitchLeaf2"
      (.int 1 (evalICmp IPred.eq x (BitVec.ofNat 8 91))) (by simp only [lookupName_cons_self])
  simp only [execTerm, hop, hbit, stage2NoEventJumpState, stage2NoEventStepState, stateAt]
  rfl


/-- `leafBlock`'s `%SwitchLeaf` branch, taken (`string_value`). -/
theorem leafBlock_branch_true {calls : Calls} (env : Env) (s : State)
    {x : BitVec 8} (h3 : lookupName env "%3" = some (.int 8 x))
    (hbit : evalICmp IPred.eq x (BitVec.ofNat 8 34) = BitVec.ofNat 1 1) :
    execTerm (stateAt (("%SwitchLeaf", .int 1 (evalICmp IPred.eq x (BitVec.ofNat 8 34))) :: env) s)
        (.condbr (.reg "%SwitchLeaf") "string_value" "scalar") =
      .jump (stage2NoEventJumpState
        (stateAt (("%SwitchLeaf", .int 1 (evalICmp IPred.eq x (BitVec.ofNat 8 34))) :: env) s)
        s.mem s.next "string_value" s.pc) := by
  have hop : evalOperand
      (stateAt (("%SwitchLeaf", .int 1 (evalICmp IPred.eq x (BitVec.ofNat 8 34))) :: env) s)
      (.reg "%SwitchLeaf") = some (.int 1 (evalICmp IPred.eq x (BitVec.ofNat 8 34))) :=
    BlockEval.evalOperand_reg_of _ _ "%SwitchLeaf"
      (.int 1 (evalICmp IPred.eq x (BitVec.ofNat 8 34))) (by simp only [lookupName_cons_self])
  simp only [execTerm, hop, hbit, stage2NoEventJumpState, stage2NoEventStepState, stateAt]
  rfl


/-- `leafBlock`'s `%SwitchLeaf` branch, taken (`scalar`). -/
theorem leafBlock_branch_false {calls : Calls} (env : Env) (s : State)
    {x : BitVec 8} (h3 : lookupName env "%3" = some (.int 8 x))
    (hbit : evalICmp IPred.eq x (BitVec.ofNat 8 34) = BitVec.ofNat 1 0) :
    execTerm (stateAt (("%SwitchLeaf", .int 1 (evalICmp IPred.eq x (BitVec.ofNat 8 34))) :: env) s)
        (.condbr (.reg "%SwitchLeaf") "string_value" "scalar") =
      .jump (stage2NoEventJumpState
        (stateAt (("%SwitchLeaf", .int 1 (evalICmp IPred.eq x (BitVec.ofNat 8 34))) :: env) s)
        s.mem s.next "scalar" s.pc) := by
  have hop : evalOperand
      (stateAt (("%SwitchLeaf", .int 1 (evalICmp IPred.eq x (BitVec.ofNat 8 34))) :: env) s)
      (.reg "%SwitchLeaf") = some (.int 1 (evalICmp IPred.eq x (BitVec.ofNat 8 34))) :=
    BlockEval.evalOperand_reg_of _ _ "%SwitchLeaf"
      (.int 1 (evalICmp IPred.eq x (BitVec.ofNat 8 34))) (by simp only [lookupName_cons_self])
  simp only [execTerm, hop, hbit, stage2NoEventJumpState, stage2NoEventStepState, stateAt]
  rfl

/-! ### The quote's row and the value path

`LeafBlock` is `NodeBlock5`'s true arm, so the quote's row is two links: the
`slt 91` true arm and the leaf's `eq 34` true arm.  Every other byte that the
three leaf tests reject reaches `scalar`, and the path it takes is the pivot
range it falls in: below 91 signed, the `LeafBlock` arm; between 91 and 123, the
`LeafBlock1` arm; at or above 123, the `LeafBlock3` arm.  Each arm's row carries
the invariant at its endpoint, and the value row is the disjunction of the three
because the handoff environment names the leaf it came through. -/

/-- `NodeBlock5` at a byte below 91: the true arm, to `LeafBlock`. -/
theorem link_nodeBlock5_true {calls : Calls} {K : Stage2NoEventWalkCarry}
    {mem : Mem} {s : State} {y : BitVec 8}
    (h : Stage2NoEventWalkInv K mem s) (hpc : s.pc = "NodeBlock5")
    (h3 : lookupName s.env "%3" = some (.int 8 y))
    (hy : evalICmp .slt y (BitVec.ofNat 8 91) = 1) :
    Stage2NoEventWalkLink calls K mem s K
      (stage2NoEventWalkNext (("%Pivot6", .int 1 1) :: s.env) s "LeafBlock") := by
  have hcode : denoteCode calls nodeBlock5Instrs (stateAt s.env s) =
      some (stateAt (("%Pivot6", .int 1 1) :: s.env) s) := by
    have hd := nodeBlock5_denote calls s.env s h3
    rw [hy] at hd
    exact hd
  exact stage2NoEventWalkLink_condbr_true (env' := ("%Pivot6", .int 1 1) :: s.env)
    h (by rw [hpc]; exact nodeBlock5Block_find) hcode rfl (by rw [lookupName_cons_self])

/-- `LeafBlock` at 34: the quote's arm, to `string_value`. -/
theorem link_leafBlock_true {calls : Calls} {K : Stage2NoEventWalkCarry}
    {mem : Mem} {s : State} {y : BitVec 8}
    (h : Stage2NoEventWalkInv K mem s) (hpc : s.pc = "LeafBlock")
    (h3 : lookupName s.env "%3" = some (.int 8 y))
    (hy : evalICmp .eq y (BitVec.ofNat 8 34) = 1) :
    Stage2NoEventWalkLink calls K mem s K
      (stage2NoEventWalkNext (("%SwitchLeaf", .int 1 1) :: s.env) s "string_value") := by
  have hcode : denoteCode calls leafBlockInstrs (stateAt s.env s) =
      some (stateAt (("%SwitchLeaf", .int 1 1) :: s.env) s) := by
    have hd := leafBlock_denote (calls := calls) s.env s h3
    rw [hy] at hd
    exact hd
  exact stage2NoEventWalkLink_condbr_true (env' := ("%SwitchLeaf", .int 1 1) :: s.env)
    h (by rw [hpc]; exact leafBlockBlock_find) hcode rfl (by rw [lookupName_cons_self])

/-- `LeafBlock` at a byte other than 34: the value path, `scalar`. -/
theorem link_leafBlock_false {calls : Calls} {K : Stage2NoEventWalkCarry}
    {mem : Mem} {s : State} {y : BitVec 8}
    (h : Stage2NoEventWalkInv K mem s) (hpc : s.pc = "LeafBlock")
    (h3 : lookupName s.env "%3" = some (.int 8 y))
    (hy : evalICmp .eq y (BitVec.ofNat 8 34) = 0) :
    Stage2NoEventWalkLink calls K mem s K
      (stage2NoEventWalkNext (("%SwitchLeaf", .int 1 0) :: s.env) s "scalar") := by
  have hcode : denoteCode calls leafBlockInstrs (stateAt s.env s) =
      some (stateAt (("%SwitchLeaf", .int 1 0) :: s.env) s) := by
    have hd := leafBlock_denote (calls := calls) s.env s h3
    rw [hy] at hd
    exact hd
  exact stage2NoEventWalkLink_condbr_false (env' := ("%SwitchLeaf", .int 1 0) :: s.env)
    h (by rw [hpc]; exact leafBlockBlock_find) hcode rfl (by rw [lookupName_cons_self])

/-- **`"` (34)**: the quote's dispatch, to `string_value`. -/
theorem stage2NoEventRow_string {calls : Calls} {K : Stage2NoEventWalkCarry}
    {mem : Mem} {s : State}
    (h : Stage2NoEventWalkInv K mem s) (hpc : s.pc = "NodeBlock5")
    (h3 : lookupName s.env "%3" = some (.int 8 (BitVec.ofNat 8 34))) :
    Stage2NoEventWalkChain calls mem K s K
      (stage2NoEventWalkAt
        (("%SwitchLeaf", .int 1 1) ::
          ("%Pivot6", .int 1 1) :: s.env) s
        "string_value" "LeafBlock") := by
  have h3₁ : lookupName (("%Pivot6", .int 1 (1 : BitVec 1)) :: s.env) "%3"
      = some (.int 8 (BitVec.ofNat 8 34)) :=
    lookupName_cons_other _ _ _ (by decide) h3
  let S1 := stage2NoEventWalkNext (("%Pivot6", .int 1 1) :: s.env) s "LeafBlock"
  have L1 : Stage2NoEventWalkLink calls K mem s K S1 :=
    link_nodeBlock5_true h hpc h3 (by decide)
  have L2 : Stage2NoEventWalkLink calls K mem S1 K
      (stage2NoEventWalkNext (("%SwitchLeaf", .int 1 1) ::
        ("%Pivot6", .int 1 1) :: s.env) S1 "string_value") :=
    link_leafBlock_true L1.inv' (by simp only [S1, stage2NoEventWalkNext]) h3₁ (by decide)
  simpa only [S1, stage2NoEventWalkNext, stage2NoEventWalkAt] using
    (Stage2NoEventWalkChain.tail L1 (Stage2NoEventWalkChain.tail L2
      (Stage2NoEventWalkChain.nil L2.inv')))

/-- `icmp slt` at one is the signed order on the byte's readings. -/
theorem stage2NoEvent_slt_one_of_toInt_lt {w : Nat} {x a : BitVec w}
    (h : x.toInt < a.toInt) : evalICmp .slt x a = 1 := by
  simp [evalICmp, BitVec.slt_eq_decide, h]

/-- `icmp slt` at zero is the negated signed order. -/
theorem stage2NoEvent_slt_zero_of_toInt_ge {w : Nat} {x a : BitVec w}
    (h : a.toInt ≤ x.toInt) : evalICmp .slt x a = 0 := by
  simp [evalICmp, BitVec.slt_eq_decide, not_lt.mpr h]

/-- `icmp eq` at zero, from the two words being unequal. -/
theorem stage2NoEvent_eq_zero_of_ne {w : Nat} {x c : BitVec w} (h : x ≠ c) :
    evalICmp .eq x c = 0 := by
  simp [evalICmp, h]

/-- **The value path through `LeafBlock`**: a byte below 91 that is not 34 reaches
`scalar`. -/
theorem stage2NoEventRow_valueLeaf {calls : Calls} {K : Stage2NoEventWalkCarry}
    {mem : Mem} {s : State} {y : BitVec 8}
    (h : Stage2NoEventWalkInv K mem s) (hpc : s.pc = "NodeBlock5")
    (h3 : lookupName s.env "%3" = some (.int 8 y))
    (hy91 : evalICmp .slt y (BitVec.ofNat 8 91) = 1)
    (hy34 : evalICmp .eq y (BitVec.ofNat 8 34) = 0) :
    Stage2NoEventWalkChain calls mem K s K
        (stage2NoEventWalkAt
          (("%SwitchLeaf", .int 1 0) ::
            ("%Pivot6", .int 1 1) :: s.env) s
          "scalar" "LeafBlock") ∧
      Stage2NoEventWalkInv K mem
        (stage2NoEventWalkAt
          (("%SwitchLeaf", .int 1 0) ::
            ("%Pivot6", .int 1 1) :: s.env) s
          "scalar" "LeafBlock") := by
  have h3₁ : lookupName (("%Pivot6", .int 1 (1 : BitVec 1)) :: s.env) "%3"
      = some (.int 8 y) :=
    lookupName_cons_other _ _ _ (by decide) h3
  let S1 := stage2NoEventWalkNext (("%Pivot6", .int 1 1) :: s.env) s "LeafBlock"
  have L1 : Stage2NoEventWalkLink calls K mem s K S1 :=
    link_nodeBlock5_true h hpc h3 hy91
  have L2 : Stage2NoEventWalkLink calls K mem S1 K
      (stage2NoEventWalkNext (("%SwitchLeaf", .int 1 0) ::
        ("%Pivot6", .int 1 1) :: s.env) S1 "scalar") :=
    link_leafBlock_false L1.inv' (by simp only [S1, stage2NoEventWalkNext]) h3₁ hy34
  refine ⟨?_, ?_⟩
  · simpa only [S1, stage2NoEventWalkNext, stage2NoEventWalkAt] using
      (Stage2NoEventWalkChain.tail L1 (Stage2NoEventWalkChain.tail L2
        (Stage2NoEventWalkChain.nil L2.inv')))
  · simpa only [S1, stage2NoEventWalkNext, stage2NoEventWalkAt] using L2.inv'

/-- **The value path through `LeafBlock1`**: a byte from 91 up to 123 signed that
is not 91 reaches `scalar`. -/
theorem stage2NoEventRow_valueLeaf1 {calls : Calls} {K : Stage2NoEventWalkCarry}
    {mem : Mem} {s : State} {y : BitVec 8}
    (h : Stage2NoEventWalkInv K mem s) (hpc : s.pc = "NodeBlock5")
    (h3 : lookupName s.env "%3" = some (.int 8 y))
    (hy91 : evalICmp .slt y (BitVec.ofNat 8 91) = 0)
    (hy123 : evalICmp .slt y (BitVec.ofNat 8 123) = 1)
    (hy91eq : evalICmp .eq y (BitVec.ofNat 8 91) = 0) :
    Stage2NoEventWalkChain calls mem K s K
        (stage2NoEventWalkAt
          (("%SwitchLeaf2", .int 1 0) ::
            ("%Pivot", .int 1 1) :: ("%Pivot6", .int 1 0) :: s.env) s
          "scalar" "LeafBlock1") ∧
      Stage2NoEventWalkInv K mem
        (stage2NoEventWalkAt
          (("%SwitchLeaf2", .int 1 0) ::
            ("%Pivot", .int 1 1) :: ("%Pivot6", .int 1 0) :: s.env) s
          "scalar" "LeafBlock1") := by
  have h3₁ : lookupName (("%Pivot6", .int 1 (0 : BitVec 1)) :: s.env) "%3"
      = some (.int 8 y) :=
    lookupName_cons_other _ _ _ (by decide) h3
  have h3₂ : lookupName (("%Pivot", .int 1 (1 : BitVec 1)) ::
      ("%Pivot6", .int 1 (0 : BitVec 1)) :: s.env) "%3" = some (.int 8 y) :=
    lookupName_cons_other _ _ _ (by decide) h3₁
  let S1 := stage2NoEventWalkNext (("%Pivot6", .int 1 0) :: s.env) s "NodeBlock"
  let S2 := stage2NoEventWalkNext
    (("%Pivot", .int 1 1) :: ("%Pivot6", .int 1 0) :: s.env) S1 "LeafBlock1"
  have L1 : Stage2NoEventWalkLink calls K mem s K S1 :=
    link_nodeBlock5_false h hpc h3 hy91
  have L2 : Stage2NoEventWalkLink calls K mem S1 K S2 :=
    link_nodeBlock_true L1.inv' (by simp only [S1, stage2NoEventWalkNext]) h3₁ hy123
  have L3 : Stage2NoEventWalkLink calls K mem S2 K
      (stage2NoEventWalkNext (("%SwitchLeaf2", .int 1 0) ::
        ("%Pivot", .int 1 1) :: ("%Pivot6", .int 1 0) :: s.env) S2 "scalar") :=
    link_leafBlock1_false L2.inv' (by simp only [S2, S1, stage2NoEventWalkNext])
      h3₂ hy91eq
  refine ⟨?_, ?_⟩
  · simpa only [S1, S2, stage2NoEventWalkNext, stage2NoEventWalkAt] using
      (Stage2NoEventWalkChain.tail L1 (Stage2NoEventWalkChain.tail L2
        (Stage2NoEventWalkChain.tail L3 (Stage2NoEventWalkChain.nil L3.inv'))))
  · simpa only [S1, S2, stage2NoEventWalkNext, stage2NoEventWalkAt] using L3.inv'

/-- **The value path through `LeafBlock3`**: a byte at or above 123 signed that
is not 123 reaches `scalar`. -/
theorem stage2NoEventRow_valueLeaf3 {calls : Calls} {K : Stage2NoEventWalkCarry}
    {mem : Mem} {s : State} {y : BitVec 8}
    (h : Stage2NoEventWalkInv K mem s) (hpc : s.pc = "NodeBlock5")
    (h3 : lookupName s.env "%3" = some (.int 8 y))
    (hy91 : evalICmp .slt y (BitVec.ofNat 8 91) = 0)
    (hy123 : evalICmp .slt y (BitVec.ofNat 8 123) = 0)
    (hy123eq : evalICmp .eq y (BitVec.ofNat 8 123) = 0) :
    Stage2NoEventWalkChain calls mem K s K
        (stage2NoEventWalkAt
          (("%SwitchLeaf4", .int 1 0) ::
            ("%Pivot", .int 1 0) :: ("%Pivot6", .int 1 0) :: s.env) s
          "scalar" "LeafBlock3") ∧
      Stage2NoEventWalkInv K mem
        (stage2NoEventWalkAt
          (("%SwitchLeaf4", .int 1 0) ::
            ("%Pivot", .int 1 0) :: ("%Pivot6", .int 1 0) :: s.env) s
          "scalar" "LeafBlock3") := by
  have h3₁ : lookupName (("%Pivot6", .int 1 (0 : BitVec 1)) :: s.env) "%3"
      = some (.int 8 y) :=
    lookupName_cons_other _ _ _ (by decide) h3
  have h3₂ : lookupName (("%Pivot", .int 1 (0 : BitVec 1)) ::
      ("%Pivot6", .int 1 (0 : BitVec 1)) :: s.env) "%3" = some (.int 8 y) :=
    lookupName_cons_other _ _ _ (by decide) h3₁
  let S1 := stage2NoEventWalkNext (("%Pivot6", .int 1 0) :: s.env) s "NodeBlock"
  let S2 := stage2NoEventWalkNext
    (("%Pivot", .int 1 0) :: ("%Pivot6", .int 1 0) :: s.env) S1 "LeafBlock3"
  have L1 : Stage2NoEventWalkLink calls K mem s K S1 :=
    link_nodeBlock5_false h hpc h3 hy91
  have L2 : Stage2NoEventWalkLink calls K mem S1 K S2 :=
    link_nodeBlock_false L1.inv' (by simp only [S1, stage2NoEventWalkNext]) h3₁ hy123
  have L3 : Stage2NoEventWalkLink calls K mem S2 K
      (stage2NoEventWalkNext (("%SwitchLeaf4", .int 1 0) ::
        ("%Pivot", .int 1 0) :: ("%Pivot6", .int 1 0) :: s.env) S2 "scalar") :=
    link_leafBlock3_false L2.inv' (by simp only [S2, S1, stage2NoEventWalkNext])
      h3₂ hy123eq
  refine ⟨?_, ?_⟩
  · simpa only [S1, S2, stage2NoEventWalkNext, stage2NoEventWalkAt] using
      (Stage2NoEventWalkChain.tail L1 (Stage2NoEventWalkChain.tail L2
        (Stage2NoEventWalkChain.tail L3 (Stage2NoEventWalkChain.nil L3.inv'))))
  · simpa only [S1, S2, stage2NoEventWalkNext, stage2NoEventWalkAt] using L3.inv'

/-- **The value path**: any byte other than `{`, `[` and `"` reaches `scalar`,
through the leaf its pivot range selects. -/
theorem stage2NoEventRow_value {calls : Calls} {K : Stage2NoEventWalkCarry}
    {mem : Mem} {s : State} {y : BitVec 8}
    (h : Stage2NoEventWalkInv K mem s) (hpc : s.pc = "NodeBlock5")
    (h3 : lookupName s.env "%3" = some (.int 8 y))
    (hy34 : y ≠ BitVec.ofNat 8 34) (hy91 : y ≠ BitVec.ofNat 8 91)
    (hy123 : y ≠ BitVec.ofNat 8 123) :
    (Stage2NoEventWalkChain calls mem K s K
        (stage2NoEventWalkAt
          (("%SwitchLeaf", .int 1 0) ::
            ("%Pivot6", .int 1 1) :: s.env) s
          "scalar" "LeafBlock") ∧
      Stage2NoEventWalkInv K mem
        (stage2NoEventWalkAt
          (("%SwitchLeaf", .int 1 0) ::
            ("%Pivot6", .int 1 1) :: s.env) s
          "scalar" "LeafBlock")) ∨
      (Stage2NoEventWalkChain calls mem K s K
        (stage2NoEventWalkAt
          (("%SwitchLeaf2", .int 1 0) ::
            ("%Pivot", .int 1 1) :: ("%Pivot6", .int 1 0) :: s.env) s
          "scalar" "LeafBlock1") ∧
      Stage2NoEventWalkInv K mem
        (stage2NoEventWalkAt
          (("%SwitchLeaf2", .int 1 0) ::
            ("%Pivot", .int 1 1) :: ("%Pivot6", .int 1 0) :: s.env) s
          "scalar" "LeafBlock1")) ∨
      (Stage2NoEventWalkChain calls mem K s K
        (stage2NoEventWalkAt
          (("%SwitchLeaf4", .int 1 0) ::
            ("%Pivot", .int 1 0) :: ("%Pivot6", .int 1 0) :: s.env) s
          "scalar" "LeafBlock3") ∧
      Stage2NoEventWalkInv K mem
        (stage2NoEventWalkAt
          (("%SwitchLeaf4", .int 1 0) ::
            ("%Pivot", .int 1 0) :: ("%Pivot6", .int 1 0) :: s.env) s
          "scalar" "LeafBlock3")) := by
  rcases lt_or_ge y.toInt (BitVec.ofNat 8 91).toInt with hlt | hge
  · exact Or.inl (stage2NoEventRow_valueLeaf h hpc h3
      (stage2NoEvent_slt_one_of_toInt_lt hlt) (stage2NoEvent_eq_zero_of_ne hy34))
  · rcases lt_or_ge y.toInt (BitVec.ofNat 8 123).toInt with hlt | hge'
    · exact Or.inr (Or.inl (stage2NoEventRow_valueLeaf1 h hpc h3
        (stage2NoEvent_slt_zero_of_toInt_ge hge) (stage2NoEvent_slt_one_of_toInt_lt hlt)
        (stage2NoEvent_eq_zero_of_ne hy91)))
    · exact Or.inr (Or.inr (stage2NoEventRow_valueLeaf3 h hpc h3
        (stage2NoEvent_slt_zero_of_toInt_ge hge)
        (stage2NoEvent_slt_zero_of_toInt_ge hge') (stage2NoEvent_eq_zero_of_ne hy123)))

/-! ### The continuation dispatch: `NodeBlock15` and its three leaves

After a completed key/value pair, `if.end` hands `%7` to the same three-way tree
the entry head uses, with loop-exit targets:

| byte | `NodeBlock15` (slt 91) | `NodeBlock13` (slt 123) | leaf | handoff |
|---|---|---|---|---|
| `{` 123 | false → `NodeBlock13` | false → `LeafBlock11` | eq 123 → `if.then9.loopexit` | the brace's exit phi run |
| `[` 91  | false → `NodeBlock13` | true → `LeafBlock9`  | eq 91 → `if.then35` | the bracket's exit phi run |
| `"` 34  | true → `LeafBlock7` | — | eq 34 → `string_value.loopexit` | the string exit phi run |
| else | as its pivot range selects | | eq false → `scalar.loopexit` | the value exit |

Each row ends at the exit block's entry; the `%idxprom.le*`/`%9` phis that follow
the jump belong to the exit blocks and not to these rows, and no row reads or
writes memory, so the invariant is transported by `mem_congr`. -/

/-- `NodeBlock15`: the continuation dispatch's root, the byte against 91. -/
def nodeBlock15Instrs : List Instr :=
  [ Instr.icmp "%Pivot16" IPred.slt 8 (Operand.reg "%7")
      (Operand.imm (.int 8 (BitVec.ofNat 8 91))) ]

/-- `NodeBlock15`, pinned. -/
def nodeBlock15Block : Block :=
  { name := "NodeBlock15", instrs := nodeBlock15Instrs,
    term := Term.condbr (Operand.reg "%Pivot16") "LeafBlock7" "NodeBlock13" }

theorem nodeBlock15Block_find :
    stage2NoEventBody.findBlock "NodeBlock15" = some nodeBlock15Block := by
  decide

/-- `NodeBlock13`: the continuation dispatch's inner node, the byte against 123. -/
def nodeBlock13Instrs : List Instr :=
  [ Instr.icmp "%Pivot14" IPred.slt 8 (Operand.reg "%7")
      (Operand.imm (.int 8 (BitVec.ofNat 8 123))) ]

/-- `NodeBlock13`, pinned. -/
def nodeBlock13Block : Block :=
  { name := "NodeBlock13", instrs := nodeBlock13Instrs,
    term := Term.condbr (Operand.reg "%Pivot14") "LeafBlock9" "LeafBlock11" }

theorem nodeBlock13Block_find :
    stage2NoEventBody.findBlock "NodeBlock13" = some nodeBlock13Block := by
  decide

/-- `LeafBlock11`: the byte against 123, the brace's exit leaf. -/
def leafBlock11Instrs : List Instr :=
  [ Instr.icmp "%SwitchLeaf12" IPred.eq 8 (Operand.reg "%7")
      (Operand.imm (.int 8 (BitVec.ofNat 8 123))) ]

/-- `LeafBlock11`, pinned. -/
def leafBlock11Block : Block :=
  { name := "LeafBlock11", instrs := leafBlock11Instrs,
    term := Term.condbr (Operand.reg "%SwitchLeaf12") "if.then9.loopexit" "scalar.loopexit" }

theorem leafBlock11Block_find :
    stage2NoEventBody.findBlock "LeafBlock11" = some leafBlock11Block := by
  decide

/-- `LeafBlock9`: the byte against 91, the bracket's exit leaf. -/
def leafBlock9Instrs : List Instr :=
  [ Instr.icmp "%SwitchLeaf10" IPred.eq 8 (Operand.reg "%7")
      (Operand.imm (.int 8 (BitVec.ofNat 8 91))) ]

/-- `LeafBlock9`, pinned. -/
def leafBlock9Block : Block :=
  { name := "LeafBlock9", instrs := leafBlock9Instrs,
    term := Term.condbr (Operand.reg "%SwitchLeaf10") "if.then35" "scalar.loopexit" }

theorem leafBlock9Block_find :
    stage2NoEventBody.findBlock "LeafBlock9" = some leafBlock9Block := by
  decide

/-- `LeafBlock7`: the byte against 34, the quote's exit leaf. -/
def leafBlock7Instrs : List Instr :=
  [ Instr.icmp "%SwitchLeaf8" IPred.eq 8 (Operand.reg "%7")
      (Operand.imm (.int 8 (BitVec.ofNat 8 34))) ]

/-- `LeafBlock7`, pinned. -/
def leafBlock7Block : Block :=
  { name := "LeafBlock7", instrs := leafBlock7Instrs,
    term := Term.condbr (Operand.reg "%SwitchLeaf8") "string_value.loopexit" "scalar.loopexit" }

theorem leafBlock7Block_find :
    stage2NoEventBody.findBlock "LeafBlock7" = some leafBlock7Block := by
  decide

theorem nodeBlock15_denote (calls : Calls) (env : Env) (s : State) {y : BitVec 8}
    (h7 : lookupName env "%7" = some (.int 8 y)) :
    denoteCode calls nodeBlock15Instrs (stateAt env s) =
      some (stateAt
        (("%Pivot16", .int 1 (evalICmp .slt y (BitVec.ofNat 8 91))) :: env) s) := by
  rw [nodeBlock15Instrs, stage2NoEventWalk_denote_icmp_imm (calls := calls)
    (env := env) (s := s) (d := "%Pivot16") (a := "%7") (p := .slt) (w := 8)
    (c := BitVec.ofNat 8 91) h7 (is := [])]
  simp only [denoteCode_nil]

theorem nodeBlock13_denote (calls : Calls) (env : Env) (s : State) {y : BitVec 8}
    (h7 : lookupName env "%7" = some (.int 8 y)) :
    denoteCode calls nodeBlock13Instrs (stateAt env s) =
      some (stateAt
        (("%Pivot14", .int 1 (evalICmp .slt y (BitVec.ofNat 8 123))) :: env) s) := by
  rw [nodeBlock13Instrs, stage2NoEventWalk_denote_icmp_imm (calls := calls)
    (env := env) (s := s) (d := "%Pivot14") (a := "%7") (p := .slt) (w := 8)
    (c := BitVec.ofNat 8 123) h7 (is := [])]
  simp only [denoteCode_nil]

theorem leafBlock11_denote (calls : Calls) (env : Env) (s : State) {y : BitVec 8}
    (h7 : lookupName env "%7" = some (.int 8 y)) :
    denoteCode calls leafBlock11Instrs (stateAt env s) =
      some (stateAt
        (("%SwitchLeaf12", .int 1 (evalICmp .eq y (BitVec.ofNat 8 123))) :: env) s) := by
  rw [leafBlock11Instrs, stage2NoEventWalk_denote_icmp_imm (calls := calls)
    (env := env) (s := s) (d := "%SwitchLeaf12") (a := "%7") (p := .eq) (w := 8)
    (c := BitVec.ofNat 8 123) h7 (is := [])]
  simp only [denoteCode_nil]

theorem leafBlock9_denote (calls : Calls) (env : Env) (s : State) {y : BitVec 8}
    (h7 : lookupName env "%7" = some (.int 8 y)) :
    denoteCode calls leafBlock9Instrs (stateAt env s) =
      some (stateAt
        (("%SwitchLeaf10", .int 1 (evalICmp .eq y (BitVec.ofNat 8 91))) :: env) s) := by
  rw [leafBlock9Instrs, stage2NoEventWalk_denote_icmp_imm (calls := calls)
    (env := env) (s := s) (d := "%SwitchLeaf10") (a := "%7") (p := .eq) (w := 8)
    (c := BitVec.ofNat 8 91) h7 (is := [])]
  simp only [denoteCode_nil]

theorem leafBlock7_denote (calls : Calls) (env : Env) (s : State) {y : BitVec 8}
    (h7 : lookupName env "%7" = some (.int 8 y)) :
    denoteCode calls leafBlock7Instrs (stateAt env s) =
      some (stateAt
        (("%SwitchLeaf8", .int 1 (evalICmp .eq y (BitVec.ofNat 8 34))) :: env) s) := by
  rw [leafBlock7Instrs, stage2NoEventWalk_denote_icmp_imm (calls := calls)
    (env := env) (s := s) (d := "%SwitchLeaf8") (a := "%7") (p := .eq) (w := 8)
    (c := BitVec.ofNat 8 34) h7 (is := [])]
  simp only [denoteCode_nil]

/-- `NodeBlock15` at a byte below 91: the true arm, to `LeafBlock7`. -/
theorem link_nodeBlock15_true {calls : Calls} {K : Stage2NoEventWalkCarry}
    {mem : Mem} {s : State} {y : BitVec 8}
    (h : Stage2NoEventWalkInv K mem s) (hpc : s.pc = "NodeBlock15")
    (h7 : lookupName s.env "%7" = some (.int 8 y))
    (hy : evalICmp .slt y (BitVec.ofNat 8 91) = 1) :
    Stage2NoEventWalkLink calls K mem s K
      (stage2NoEventWalkNext (("%Pivot16", .int 1 1) :: s.env) s "LeafBlock7") := by
  have hcode : denoteCode calls nodeBlock15Instrs (stateAt s.env s) =
      some (stateAt (("%Pivot16", .int 1 1) :: s.env) s) := by
    have hd := nodeBlock15_denote calls s.env s h7
    rw [hy] at hd
    exact hd
  exact stage2NoEventWalkLink_condbr_true (env' := ("%Pivot16", .int 1 1) :: s.env)
    h (by rw [hpc]; exact nodeBlock15Block_find) hcode rfl (by rw [lookupName_cons_self])

/-- `NodeBlock15` at a byte at or above 91: the false arm, to `NodeBlock13`. -/
theorem link_nodeBlock15_false {calls : Calls} {K : Stage2NoEventWalkCarry}
    {mem : Mem} {s : State} {y : BitVec 8}
    (h : Stage2NoEventWalkInv K mem s) (hpc : s.pc = "NodeBlock15")
    (h7 : lookupName s.env "%7" = some (.int 8 y))
    (hy : evalICmp .slt y (BitVec.ofNat 8 91) = 0) :
    Stage2NoEventWalkLink calls K mem s K
      (stage2NoEventWalkNext (("%Pivot16", .int 1 0) :: s.env) s "NodeBlock13") := by
  have hcode : denoteCode calls nodeBlock15Instrs (stateAt s.env s) =
      some (stateAt (("%Pivot16", .int 1 0) :: s.env) s) := by
    have hd := nodeBlock15_denote calls s.env s h7
    rw [hy] at hd
    exact hd
  exact stage2NoEventWalkLink_condbr_false (env' := ("%Pivot16", .int 1 0) :: s.env)
    h (by rw [hpc]; exact nodeBlock15Block_find) hcode rfl (by rw [lookupName_cons_self])

/-- `NodeBlock13` at a byte below 123: the true arm, to `LeafBlock9`. -/
theorem link_nodeBlock13_true {calls : Calls} {K : Stage2NoEventWalkCarry}
    {mem : Mem} {s : State} {y : BitVec 8}
    (h : Stage2NoEventWalkInv K mem s) (hpc : s.pc = "NodeBlock13")
    (h7 : lookupName s.env "%7" = some (.int 8 y))
    (hy : evalICmp .slt y (BitVec.ofNat 8 123) = 1) :
    Stage2NoEventWalkLink calls K mem s K
      (stage2NoEventWalkNext (("%Pivot14", .int 1 1) :: s.env) s "LeafBlock9") := by
  have hcode : denoteCode calls nodeBlock13Instrs (stateAt s.env s) =
      some (stateAt (("%Pivot14", .int 1 1) :: s.env) s) := by
    have hd := nodeBlock13_denote calls s.env s h7
    rw [hy] at hd
    exact hd
  exact stage2NoEventWalkLink_condbr_true (env' := ("%Pivot14", .int 1 1) :: s.env)
    h (by rw [hpc]; exact nodeBlock13Block_find) hcode rfl (by rw [lookupName_cons_self])

/-- `NodeBlock13` at a byte at or above 123: the false arm, to `LeafBlock11`. -/
theorem link_nodeBlock13_false {calls : Calls} {K : Stage2NoEventWalkCarry}
    {mem : Mem} {s : State} {y : BitVec 8}
    (h : Stage2NoEventWalkInv K mem s) (hpc : s.pc = "NodeBlock13")
    (h7 : lookupName s.env "%7" = some (.int 8 y))
    (hy : evalICmp .slt y (BitVec.ofNat 8 123) = 0) :
    Stage2NoEventWalkLink calls K mem s K
      (stage2NoEventWalkNext (("%Pivot14", .int 1 0) :: s.env) s "LeafBlock11") := by
  have hcode : denoteCode calls nodeBlock13Instrs (stateAt s.env s) =
      some (stateAt (("%Pivot14", .int 1 0) :: s.env) s) := by
    have hd := nodeBlock13_denote calls s.env s h7
    rw [hy] at hd
    exact hd
  exact stage2NoEventWalkLink_condbr_false (env' := ("%Pivot14", .int 1 0) :: s.env)
    h (by rw [hpc]; exact nodeBlock13Block_find) hcode rfl (by rw [lookupName_cons_self])

/-- `LeafBlock11` at 123: the brace's exit, to `if.then9.loopexit`. -/
theorem link_leafBlock11_true {calls : Calls} {K : Stage2NoEventWalkCarry}
    {mem : Mem} {s : State} {y : BitVec 8}
    (h : Stage2NoEventWalkInv K mem s) (hpc : s.pc = "LeafBlock11")
    (h7 : lookupName s.env "%7" = some (.int 8 y))
    (hy : evalICmp .eq y (BitVec.ofNat 8 123) = 1) :
    Stage2NoEventWalkLink calls K mem s K
      (stage2NoEventWalkNext (("%SwitchLeaf12", .int 1 1) :: s.env) s "if.then9.loopexit") := by
  have hcode : denoteCode calls leafBlock11Instrs (stateAt s.env s) =
      some (stateAt (("%SwitchLeaf12", .int 1 1) :: s.env) s) := by
    have hd := leafBlock11_denote calls s.env s h7
    rw [hy] at hd
    exact hd
  exact stage2NoEventWalkLink_condbr_true (env' := ("%SwitchLeaf12", .int 1 1) :: s.env)
    h (by rw [hpc]; exact leafBlock11Block_find) hcode rfl (by rw [lookupName_cons_self])

/-- `LeafBlock11` at a byte other than 123: the value exit, `scalar.loopexit`. -/
theorem link_leafBlock11_false {calls : Calls} {K : Stage2NoEventWalkCarry}
    {mem : Mem} {s : State} {y : BitVec 8}
    (h : Stage2NoEventWalkInv K mem s) (hpc : s.pc = "LeafBlock11")
    (h7 : lookupName s.env "%7" = some (.int 8 y))
    (hy : evalICmp .eq y (BitVec.ofNat 8 123) = 0) :
    Stage2NoEventWalkLink calls K mem s K
      (stage2NoEventWalkNext (("%SwitchLeaf12", .int 1 0) :: s.env) s "scalar.loopexit") := by
  have hcode : denoteCode calls leafBlock11Instrs (stateAt s.env s) =
      some (stateAt (("%SwitchLeaf12", .int 1 0) :: s.env) s) := by
    have hd := leafBlock11_denote calls s.env s h7
    rw [hy] at hd
    exact hd
  exact stage2NoEventWalkLink_condbr_false (env' := ("%SwitchLeaf12", .int 1 0) :: s.env)
    h (by rw [hpc]; exact leafBlock11Block_find) hcode rfl (by rw [lookupName_cons_self])

/-- `LeafBlock9` at 91: the bracket's exit, to `if.then35`. -/
theorem link_leafBlock9_true {calls : Calls} {K : Stage2NoEventWalkCarry}
    {mem : Mem} {s : State} {y : BitVec 8}
    (h : Stage2NoEventWalkInv K mem s) (hpc : s.pc = "LeafBlock9")
    (h7 : lookupName s.env "%7" = some (.int 8 y))
    (hy : evalICmp .eq y (BitVec.ofNat 8 91) = 1) :
    Stage2NoEventWalkLink calls K mem s K
      (stage2NoEventWalkNext (("%SwitchLeaf10", .int 1 1) :: s.env) s "if.then35") := by
  have hcode : denoteCode calls leafBlock9Instrs (stateAt s.env s) =
      some (stateAt (("%SwitchLeaf10", .int 1 1) :: s.env) s) := by
    have hd := leafBlock9_denote calls s.env s h7
    rw [hy] at hd
    exact hd
  exact stage2NoEventWalkLink_condbr_true (env' := ("%SwitchLeaf10", .int 1 1) :: s.env)
    h (by rw [hpc]; exact leafBlock9Block_find) hcode rfl (by rw [lookupName_cons_self])

/-- `LeafBlock9` at a byte other than 91: the value exit, `scalar.loopexit`. -/
theorem link_leafBlock9_false {calls : Calls} {K : Stage2NoEventWalkCarry}
    {mem : Mem} {s : State} {y : BitVec 8}
    (h : Stage2NoEventWalkInv K mem s) (hpc : s.pc = "LeafBlock9")
    (h7 : lookupName s.env "%7" = some (.int 8 y))
    (hy : evalICmp .eq y (BitVec.ofNat 8 91) = 0) :
    Stage2NoEventWalkLink calls K mem s K
      (stage2NoEventWalkNext (("%SwitchLeaf10", .int 1 0) :: s.env) s "scalar.loopexit") := by
  have hcode : denoteCode calls leafBlock9Instrs (stateAt s.env s) =
      some (stateAt (("%SwitchLeaf10", .int 1 0) :: s.env) s) := by
    have hd := leafBlock9_denote calls s.env s h7
    rw [hy] at hd
    exact hd
  exact stage2NoEventWalkLink_condbr_false (env' := ("%SwitchLeaf10", .int 1 0) :: s.env)
    h (by rw [hpc]; exact leafBlock9Block_find) hcode rfl (by rw [lookupName_cons_self])

/-- `LeafBlock7` at 34: the quote's exit, to `string_value.loopexit`. -/
theorem link_leafBlock7_true {calls : Calls} {K : Stage2NoEventWalkCarry}
    {mem : Mem} {s : State} {y : BitVec 8}
    (h : Stage2NoEventWalkInv K mem s) (hpc : s.pc = "LeafBlock7")
    (h7 : lookupName s.env "%7" = some (.int 8 y))
    (hy : evalICmp .eq y (BitVec.ofNat 8 34) = 1) :
    Stage2NoEventWalkLink calls K mem s K
      (stage2NoEventWalkNext (("%SwitchLeaf8", .int 1 1) :: s.env) s
        "string_value.loopexit") := by
  have hcode : denoteCode calls leafBlock7Instrs (stateAt s.env s) =
      some (stateAt (("%SwitchLeaf8", .int 1 1) :: s.env) s) := by
    have hd := leafBlock7_denote calls s.env s h7
    rw [hy] at hd
    exact hd
  exact stage2NoEventWalkLink_condbr_true (env' := ("%SwitchLeaf8", .int 1 1) :: s.env)
    h (by rw [hpc]; exact leafBlock7Block_find) hcode rfl (by rw [lookupName_cons_self])

/-- `LeafBlock7` at a byte other than 34: the value exit, `scalar.loopexit`. -/
theorem link_leafBlock7_false {calls : Calls} {K : Stage2NoEventWalkCarry}
    {mem : Mem} {s : State} {y : BitVec 8}
    (h : Stage2NoEventWalkInv K mem s) (hpc : s.pc = "LeafBlock7")
    (h7 : lookupName s.env "%7" = some (.int 8 y))
    (hy : evalICmp .eq y (BitVec.ofNat 8 34) = 0) :
    Stage2NoEventWalkLink calls K mem s K
      (stage2NoEventWalkNext (("%SwitchLeaf8", .int 1 0) :: s.env) s "scalar.loopexit") := by
  have hcode : denoteCode calls leafBlock7Instrs (stateAt s.env s) =
      some (stateAt (("%SwitchLeaf8", .int 1 0) :: s.env) s) := by
    have hd := leafBlock7_denote calls s.env s h7
    rw [hy] at hd
    exact hd
  exact stage2NoEventWalkLink_condbr_false (env' := ("%SwitchLeaf8", .int 1 0) :: s.env)
    h (by rw [hpc]; exact leafBlock7Block_find) hcode rfl (by rw [lookupName_cons_self])

/-- **`{` (123) at the continuation dispatch**, to `if.then9.loopexit`. -/
theorem stage2NoEventRow_loopExitBrace {calls : Calls} {K : Stage2NoEventWalkCarry}
    {mem : Mem} {s : State}
    (h : Stage2NoEventWalkInv K mem s) (hpc : s.pc = "NodeBlock15")
    (h7 : lookupName s.env "%7" = some (.int 8 (BitVec.ofNat 8 123))) :
    Stage2NoEventWalkChain calls mem K s K
      (stage2NoEventWalkAt
        (("%SwitchLeaf12", .int 1 1) ::
          ("%Pivot14", .int 1 0) :: ("%Pivot16", .int 1 0) :: s.env) s
        "if.then9.loopexit" "LeafBlock11") := by
  have h7₁ : lookupName (("%Pivot16", .int 1 (0 : BitVec 1)) :: s.env) "%7"
      = some (.int 8 (BitVec.ofNat 8 123)) :=
    lookupName_cons_other _ _ _ (by decide) h7
  have h7₂ : lookupName (("%Pivot14", .int 1 (0 : BitVec 1)) ::
      ("%Pivot16", .int 1 (0 : BitVec 1)) :: s.env) "%7"
      = some (.int 8 (BitVec.ofNat 8 123)) :=
    lookupName_cons_other _ _ _ (by decide) h7₁
  let S1 := stage2NoEventWalkNext (("%Pivot16", .int 1 0) :: s.env) s "NodeBlock13"
  let S2 := stage2NoEventWalkNext
    (("%Pivot14", .int 1 0) :: ("%Pivot16", .int 1 0) :: s.env) S1 "LeafBlock11"
  have L1 : Stage2NoEventWalkLink calls K mem s K S1 :=
    link_nodeBlock15_false h hpc h7 (by decide)
  have L2 : Stage2NoEventWalkLink calls K mem S1 K S2 :=
    link_nodeBlock13_false L1.inv' (by simp only [S1, stage2NoEventWalkNext]) h7₁ (by decide)
  have L3 : Stage2NoEventWalkLink calls K mem S2 K
      (stage2NoEventWalkNext (("%SwitchLeaf12", .int 1 1) ::
        ("%Pivot14", .int 1 0) :: ("%Pivot16", .int 1 0) :: s.env) S2
        "if.then9.loopexit") :=
    link_leafBlock11_true L2.inv' (by simp only [S2, S1, stage2NoEventWalkNext]) h7₂
      (by decide)
  simpa only [S1, S2, stage2NoEventWalkNext, stage2NoEventWalkAt] using
    (Stage2NoEventWalkChain.tail L1 (Stage2NoEventWalkChain.tail L2
      (Stage2NoEventWalkChain.tail L3 (Stage2NoEventWalkChain.nil L3.inv'))))

/-- **`[` (91) at the continuation dispatch**, to `if.then35`. -/
theorem stage2NoEventRow_loopExitBracket {calls : Calls} {K : Stage2NoEventWalkCarry}
    {mem : Mem} {s : State}
    (h : Stage2NoEventWalkInv K mem s) (hpc : s.pc = "NodeBlock15")
    (h7 : lookupName s.env "%7" = some (.int 8 (BitVec.ofNat 8 91))) :
    Stage2NoEventWalkChain calls mem K s K
      (stage2NoEventWalkAt
        (("%SwitchLeaf10", .int 1 1) ::
          ("%Pivot14", .int 1 1) :: ("%Pivot16", .int 1 0) :: s.env) s
        "if.then35" "LeafBlock9") := by
  have h7₁ : lookupName (("%Pivot16", .int 1 (0 : BitVec 1)) :: s.env) "%7"
      = some (.int 8 (BitVec.ofNat 8 91)) :=
    lookupName_cons_other _ _ _ (by decide) h7
  have h7₂ : lookupName (("%Pivot14", .int 1 (1 : BitVec 1)) ::
      ("%Pivot16", .int 1 (0 : BitVec 1)) :: s.env) "%7"
      = some (.int 8 (BitVec.ofNat 8 91)) :=
    lookupName_cons_other _ _ _ (by decide) h7₁
  let S1 := stage2NoEventWalkNext (("%Pivot16", .int 1 0) :: s.env) s "NodeBlock13"
  let S2 := stage2NoEventWalkNext
    (("%Pivot14", .int 1 1) :: ("%Pivot16", .int 1 0) :: s.env) S1 "LeafBlock9"
  have L1 : Stage2NoEventWalkLink calls K mem s K S1 :=
    link_nodeBlock15_false h hpc h7 (by decide)
  have L2 : Stage2NoEventWalkLink calls K mem S1 K S2 :=
    link_nodeBlock13_true L1.inv' (by simp only [S1, stage2NoEventWalkNext]) h7₁ (by decide)
  have L3 : Stage2NoEventWalkLink calls K mem S2 K
      (stage2NoEventWalkNext (("%SwitchLeaf10", .int 1 1) ::
        ("%Pivot14", .int 1 1) :: ("%Pivot16", .int 1 0) :: s.env) S2 "if.then35") :=
    link_leafBlock9_true L2.inv' (by simp only [S2, S1, stage2NoEventWalkNext]) h7₂
      (by decide)
  simpa only [S1, S2, stage2NoEventWalkNext, stage2NoEventWalkAt] using
    (Stage2NoEventWalkChain.tail L1 (Stage2NoEventWalkChain.tail L2
      (Stage2NoEventWalkChain.tail L3 (Stage2NoEventWalkChain.nil L3.inv'))))

/-- **`"` (34) at the continuation dispatch**, to `string_value.loopexit`. -/
theorem stage2NoEventRow_loopExitString {calls : Calls} {K : Stage2NoEventWalkCarry}
    {mem : Mem} {s : State}
    (h : Stage2NoEventWalkInv K mem s) (hpc : s.pc = "NodeBlock15")
    (h7 : lookupName s.env "%7" = some (.int 8 (BitVec.ofNat 8 34))) :
    Stage2NoEventWalkChain calls mem K s K
      (stage2NoEventWalkAt
        (("%SwitchLeaf8", .int 1 1) ::
          ("%Pivot16", .int 1 1) :: s.env) s
        "string_value.loopexit" "LeafBlock7") := by
  have h7₁ : lookupName (("%Pivot16", .int 1 (1 : BitVec 1)) :: s.env) "%7"
      = some (.int 8 (BitVec.ofNat 8 34)) :=
    lookupName_cons_other _ _ _ (by decide) h7
  let S1 := stage2NoEventWalkNext (("%Pivot16", .int 1 1) :: s.env) s "LeafBlock7"
  have L1 : Stage2NoEventWalkLink calls K mem s K S1 :=
    link_nodeBlock15_true h hpc h7 (by decide)
  have L2 : Stage2NoEventWalkLink calls K mem S1 K
      (stage2NoEventWalkNext (("%SwitchLeaf8", .int 1 1) ::
        ("%Pivot16", .int 1 1) :: s.env) S1 "string_value.loopexit") :=
    link_leafBlock7_true L1.inv' (by simp only [S1, stage2NoEventWalkNext]) h7₁ (by decide)
  simpa only [S1, stage2NoEventWalkNext, stage2NoEventWalkAt] using
    (Stage2NoEventWalkChain.tail L1 (Stage2NoEventWalkChain.tail L2
      (Stage2NoEventWalkChain.nil L2.inv')))

/-- **The value exit through `LeafBlock7`**: a byte below 91 that is not 34
reaches `scalar.loopexit`. -/
theorem stage2NoEventRow_loopScalar7 {calls : Calls} {K : Stage2NoEventWalkCarry}
    {mem : Mem} {s : State} {y : BitVec 8}
    (h : Stage2NoEventWalkInv K mem s) (hpc : s.pc = "NodeBlock15")
    (h7 : lookupName s.env "%7" = some (.int 8 y))
    (hy91 : evalICmp .slt y (BitVec.ofNat 8 91) = 1)
    (hy34 : evalICmp .eq y (BitVec.ofNat 8 34) = 0) :
    Stage2NoEventWalkChain calls mem K s K
        (stage2NoEventWalkAt
          (("%SwitchLeaf8", .int 1 0) ::
            ("%Pivot16", .int 1 1) :: s.env) s
          "scalar.loopexit" "LeafBlock7") ∧
      Stage2NoEventWalkInv K mem
        (stage2NoEventWalkAt
          (("%SwitchLeaf8", .int 1 0) ::
            ("%Pivot16", .int 1 1) :: s.env) s
          "scalar.loopexit" "LeafBlock7") := by
  have h7₁ : lookupName (("%Pivot16", .int 1 (1 : BitVec 1)) :: s.env) "%7"
      = some (.int 8 y) :=
    lookupName_cons_other _ _ _ (by decide) h7
  let S1 := stage2NoEventWalkNext (("%Pivot16", .int 1 1) :: s.env) s "LeafBlock7"
  have L1 : Stage2NoEventWalkLink calls K mem s K S1 :=
    link_nodeBlock15_true h hpc h7 hy91
  have L2 : Stage2NoEventWalkLink calls K mem S1 K
      (stage2NoEventWalkNext (("%SwitchLeaf8", .int 1 0) ::
        ("%Pivot16", .int 1 1) :: s.env) S1 "scalar.loopexit") :=
    link_leafBlock7_false L1.inv' (by simp only [S1, stage2NoEventWalkNext]) h7₁ hy34
  refine ⟨?_, ?_⟩
  · simpa only [S1, stage2NoEventWalkNext, stage2NoEventWalkAt] using
      (Stage2NoEventWalkChain.tail L1 (Stage2NoEventWalkChain.tail L2
        (Stage2NoEventWalkChain.nil L2.inv')))
  · simpa only [S1, stage2NoEventWalkNext, stage2NoEventWalkAt] using L2.inv'

/-- **The value exit through `LeafBlock9`**: a byte from 91 up to 123 signed that
is not 91 reaches `scalar.loopexit`. -/
theorem stage2NoEventRow_loopScalar9 {calls : Calls} {K : Stage2NoEventWalkCarry}
    {mem : Mem} {s : State} {y : BitVec 8}
    (h : Stage2NoEventWalkInv K mem s) (hpc : s.pc = "NodeBlock15")
    (h7 : lookupName s.env "%7" = some (.int 8 y))
    (hy91 : evalICmp .slt y (BitVec.ofNat 8 91) = 0)
    (hy123 : evalICmp .slt y (BitVec.ofNat 8 123) = 1)
    (hy91eq : evalICmp .eq y (BitVec.ofNat 8 91) = 0) :
    Stage2NoEventWalkChain calls mem K s K
        (stage2NoEventWalkAt
          (("%SwitchLeaf10", .int 1 0) ::
            ("%Pivot14", .int 1 1) :: ("%Pivot16", .int 1 0) :: s.env) s
          "scalar.loopexit" "LeafBlock9") ∧
      Stage2NoEventWalkInv K mem
        (stage2NoEventWalkAt
          (("%SwitchLeaf10", .int 1 0) ::
            ("%Pivot14", .int 1 1) :: ("%Pivot16", .int 1 0) :: s.env) s
          "scalar.loopexit" "LeafBlock9") := by
  have h7₁ : lookupName (("%Pivot16", .int 1 (0 : BitVec 1)) :: s.env) "%7"
      = some (.int 8 y) :=
    lookupName_cons_other _ _ _ (by decide) h7
  have h7₂ : lookupName (("%Pivot14", .int 1 (1 : BitVec 1)) ::
      ("%Pivot16", .int 1 (0 : BitVec 1)) :: s.env) "%7" = some (.int 8 y) :=
    lookupName_cons_other _ _ _ (by decide) h7₁
  let S1 := stage2NoEventWalkNext (("%Pivot16", .int 1 0) :: s.env) s "NodeBlock13"
  let S2 := stage2NoEventWalkNext
    (("%Pivot14", .int 1 1) :: ("%Pivot16", .int 1 0) :: s.env) S1 "LeafBlock9"
  have L1 : Stage2NoEventWalkLink calls K mem s K S1 :=
    link_nodeBlock15_false h hpc h7 hy91
  have L2 : Stage2NoEventWalkLink calls K mem S1 K S2 :=
    link_nodeBlock13_true L1.inv' (by simp only [S1, stage2NoEventWalkNext]) h7₁ hy123
  have L3 : Stage2NoEventWalkLink calls K mem S2 K
      (stage2NoEventWalkNext (("%SwitchLeaf10", .int 1 0) ::
        ("%Pivot14", .int 1 1) :: ("%Pivot16", .int 1 0) :: s.env) S2
        "scalar.loopexit") :=
    link_leafBlock9_false L2.inv' (by simp only [S2, S1, stage2NoEventWalkNext])
      h7₂ hy91eq
  refine ⟨?_, ?_⟩
  · simpa only [S1, S2, stage2NoEventWalkNext, stage2NoEventWalkAt] using
      (Stage2NoEventWalkChain.tail L1 (Stage2NoEventWalkChain.tail L2
        (Stage2NoEventWalkChain.tail L3 (Stage2NoEventWalkChain.nil L3.inv'))))
  · simpa only [S1, S2, stage2NoEventWalkNext, stage2NoEventWalkAt] using L3.inv'

/-- **The value exit through `LeafBlock11`**: a byte at or above 123 signed that
is not 123 reaches `scalar.loopexit`. -/
theorem stage2NoEventRow_loopScalar11 {calls : Calls} {K : Stage2NoEventWalkCarry}
    {mem : Mem} {s : State} {y : BitVec 8}
    (h : Stage2NoEventWalkInv K mem s) (hpc : s.pc = "NodeBlock15")
    (h7 : lookupName s.env "%7" = some (.int 8 y))
    (hy91 : evalICmp .slt y (BitVec.ofNat 8 91) = 0)
    (hy123 : evalICmp .slt y (BitVec.ofNat 8 123) = 0)
    (hy123eq : evalICmp .eq y (BitVec.ofNat 8 123) = 0) :
    Stage2NoEventWalkChain calls mem K s K
        (stage2NoEventWalkAt
          (("%SwitchLeaf12", .int 1 0) ::
            ("%Pivot14", .int 1 0) :: ("%Pivot16", .int 1 0) :: s.env) s
          "scalar.loopexit" "LeafBlock11") ∧
      Stage2NoEventWalkInv K mem
        (stage2NoEventWalkAt
          (("%SwitchLeaf12", .int 1 0) ::
            ("%Pivot14", .int 1 0) :: ("%Pivot16", .int 1 0) :: s.env) s
          "scalar.loopexit" "LeafBlock11") := by
  have h7₁ : lookupName (("%Pivot16", .int 1 (0 : BitVec 1)) :: s.env) "%7"
      = some (.int 8 y) :=
    lookupName_cons_other _ _ _ (by decide) h7
  have h7₂ : lookupName (("%Pivot14", .int 1 (0 : BitVec 1)) ::
      ("%Pivot16", .int 1 (0 : BitVec 1)) :: s.env) "%7" = some (.int 8 y) :=
    lookupName_cons_other _ _ _ (by decide) h7₁
  let S1 := stage2NoEventWalkNext (("%Pivot16", .int 1 0) :: s.env) s "NodeBlock13"
  let S2 := stage2NoEventWalkNext
    (("%Pivot14", .int 1 0) :: ("%Pivot16", .int 1 0) :: s.env) S1 "LeafBlock11"
  have L1 : Stage2NoEventWalkLink calls K mem s K S1 :=
    link_nodeBlock15_false h hpc h7 hy91
  have L2 : Stage2NoEventWalkLink calls K mem S1 K S2 :=
    link_nodeBlock13_false L1.inv' (by simp only [S1, stage2NoEventWalkNext]) h7₁ hy123
  have L3 : Stage2NoEventWalkLink calls K mem S2 K
      (stage2NoEventWalkNext (("%SwitchLeaf12", .int 1 0) ::
        ("%Pivot14", .int 1 0) :: ("%Pivot16", .int 1 0) :: s.env) S2
        "scalar.loopexit") :=
    link_leafBlock11_false L2.inv' (by simp only [S2, S1, stage2NoEventWalkNext])
      h7₂ hy123eq
  refine ⟨?_, ?_⟩
  · simpa only [S1, S2, stage2NoEventWalkNext, stage2NoEventWalkAt] using
      (Stage2NoEventWalkChain.tail L1 (Stage2NoEventWalkChain.tail L2
        (Stage2NoEventWalkChain.tail L3 (Stage2NoEventWalkChain.nil L3.inv'))))
  · simpa only [S1, S2, stage2NoEventWalkNext, stage2NoEventWalkAt] using L3.inv'

/-- **The value exit**: any byte other than `{`, `[` and `"` reaches
`scalar.loopexit`, through the leaf its pivot range selects. -/
theorem stage2NoEventRow_loopScalar {calls : Calls} {K : Stage2NoEventWalkCarry}
    {mem : Mem} {s : State} {y : BitVec 8}
    (h : Stage2NoEventWalkInv K mem s) (hpc : s.pc = "NodeBlock15")
    (h7 : lookupName s.env "%7" = some (.int 8 y))
    (hy34 : y ≠ BitVec.ofNat 8 34) (hy91 : y ≠ BitVec.ofNat 8 91)
    (hy123 : y ≠ BitVec.ofNat 8 123) :
    (Stage2NoEventWalkChain calls mem K s K
        (stage2NoEventWalkAt
          (("%SwitchLeaf8", .int 1 0) ::
            ("%Pivot16", .int 1 1) :: s.env) s
          "scalar.loopexit" "LeafBlock7") ∧
      Stage2NoEventWalkInv K mem
        (stage2NoEventWalkAt
          (("%SwitchLeaf8", .int 1 0) ::
            ("%Pivot16", .int 1 1) :: s.env) s
          "scalar.loopexit" "LeafBlock7")) ∨
      (Stage2NoEventWalkChain calls mem K s K
        (stage2NoEventWalkAt
          (("%SwitchLeaf10", .int 1 0) ::
            ("%Pivot14", .int 1 1) :: ("%Pivot16", .int 1 0) :: s.env) s
          "scalar.loopexit" "LeafBlock9") ∧
      Stage2NoEventWalkInv K mem
        (stage2NoEventWalkAt
          (("%SwitchLeaf10", .int 1 0) ::
            ("%Pivot14", .int 1 1) :: ("%Pivot16", .int 1 0) :: s.env) s
          "scalar.loopexit" "LeafBlock9")) ∨
      (Stage2NoEventWalkChain calls mem K s K
        (stage2NoEventWalkAt
          (("%SwitchLeaf12", .int 1 0) ::
            ("%Pivot14", .int 1 0) :: ("%Pivot16", .int 1 0) :: s.env) s
          "scalar.loopexit" "LeafBlock11") ∧
      Stage2NoEventWalkInv K mem
        (stage2NoEventWalkAt
          (("%SwitchLeaf12", .int 1 0) ::
            ("%Pivot14", .int 1 0) :: ("%Pivot16", .int 1 0) :: s.env) s
          "scalar.loopexit" "LeafBlock11")) := by
  rcases lt_or_ge y.toInt (BitVec.ofNat 8 91).toInt with hlt | hge
  · exact Or.inl (stage2NoEventRow_loopScalar7 h hpc h7
      (stage2NoEvent_slt_one_of_toInt_lt hlt) (stage2NoEvent_eq_zero_of_ne hy34))
  · rcases lt_or_ge y.toInt (BitVec.ofNat 8 123).toInt with hlt | hge'
    · exact Or.inr (Or.inl (stage2NoEventRow_loopScalar9 h hpc h7
        (stage2NoEvent_slt_zero_of_toInt_ge hge) (stage2NoEvent_slt_one_of_toInt_lt hlt)
        (stage2NoEvent_eq_zero_of_ne hy91)))
    · exact Or.inr (Or.inr (stage2NoEventRow_loopScalar11 h hpc h7
        (stage2NoEvent_slt_zero_of_toInt_ge hge)
        (stage2NoEvent_slt_zero_of_toInt_ge hge') (stage2NoEvent_eq_zero_of_ne hy123)))

/-- The head's own run: its nine phis and its six reads. -/
theorem loopHead_denote {calls : Calls} (env : Env) (s : State)
    {k : BitVec 64} {ep b : Nat} {bs4 bs1 : List UInt8}
    (hpre : s.pre = some "if.end.peel.preheader")
    (hk : lookupName (cells loopHeadPhiCells env) "%k.0.ph1404" = some (.int 64 k))
    (hep : lookupName (cells loopHeadPhiCells env) "%ep" = some (.ptr ep))
    (hb : lookupName (cells loopHeadPhiCells env) "%b" = some (.ptr b))
    (hklt : (k.signExtend 64).toNat < 2 ^ 63)
    (hlane : readBytes s.mem (ep + (k.signExtend 64).toNat * 4) 4 = some bs4)
    (hlanelt : bytesToNat bs4 < 2 ^ 32)
    (hbyte : readBytes s.mem (b + ((BitVec.ofNat 64 (bytesToNat bs4)).signExtend 64).toNat)
      1 = some bs1) :
    denoteCode calls loopHeadBlock.instrs (stateAt env s) =
      some (stateAt
        (("%3", .int 8 (BitVec.ofNat 8 (bytesToNat bs1))) ::
          ("%arrayidx6.peel",
            .ptr (b + ((BitVec.ofNat 64 (bytesToNat bs4)).signExtend 64).toNat)) ::
          ("%idxprom.peel", .int 64 (BitVec.ofNat 64 (bytesToNat bs4))) ::
          ("%2", .int 32 (BitVec.ofNat 32 (bytesToNat bs4))) ::
          ("%arrayidx.peel", .ptr (ep + (k.signExtend 64).toNat * 4)) ::
          ("%inc.peel", .int 64 (k + BitVec.ofNat 64 1)) ::
          cells loopHeadPhiCells env) s) := by
  rw [loopHeadBlock]
  simp only [List.append_assoc]
  rw [denoteCode_append_apply (h := baseHeadPhi_denote calls env s hpre)
    (hb := by decide)]
  exact stage2NoEventLoopHead_denote calls (cells loopHeadPhiCells env) s
    hk hep hb hklt hlane hlanelt hbyte

/-- One control step at the head: its phis, its reads, and its hand-off to the
dispatch root, as a link of the walk. -/
theorem link_loopHead {calls : Calls} {K : Stage2NoEventWalkCarry} {mem : Mem}
    {s : State} {k : BitVec 64} {ep b : Nat} {bs4 bs1 : List UInt8}
    (h : Stage2NoEventWalkInv K mem s) (hpc : s.pc = "if.end.peel")
    (hpre : s.pre = some "if.end.peel.preheader")
    (hk : lookupName (cells loopHeadPhiCells s.env) "%k.0.ph1404" = some (.int 64 k))
    (hep : lookupName (cells loopHeadPhiCells s.env) "%ep" = some (.ptr ep))
    (hb : lookupName (cells loopHeadPhiCells s.env) "%b" = some (.ptr b))
    (hklt : (k.signExtend 64).toNat < 2 ^ 63)
    (hlane : readBytes s.mem (ep + (k.signExtend 64).toNat * 4) 4 = some bs4)
    (hlanelt : bytesToNat bs4 < 2 ^ 32)
    (hbyte : readBytes s.mem (b + ((BitVec.ofNat 64 (bytesToNat bs4)).signExtend 64).toNat)
      1 = some bs1) :
    Stage2NoEventWalkLink calls K mem s K
      (stage2NoEventWalkNext
        (("%3", .int 8 (BitVec.ofNat 8 (bytesToNat bs1))) ::
          ("%arrayidx6.peel",
            .ptr (b + ((BitVec.ofNat 64 (bytesToNat bs4)).signExtend 64).toNat)) ::
          ("%idxprom.peel", .int 64 (BitVec.ofNat 64 (bytesToNat bs4))) ::
          ("%2", .int 32 (BitVec.ofNat 32 (bytesToNat bs4))) ::
          ("%arrayidx.peel", .ptr (ep + (k.signExtend 64).toNat * 4)) ::
          ("%inc.peel", .int 64 (k + BitVec.ofNat 64 1)) ::
          cells loopHeadPhiCells s.env) s "NodeBlock5") := by
  have hcode : denoteCode calls loopHeadBlock.instrs s =
      some (stateAt
        (("%3", .int 8 (BitVec.ofNat 8 (bytesToNat bs1))) ::
          ("%arrayidx6.peel",
            .ptr (b + ((BitVec.ofNat 64 (bytesToNat bs4)).signExtend 64).toNat)) ::
          ("%idxprom.peel", .int 64 (BitVec.ofNat 64 (bytesToNat bs4))) ::
          ("%2", .int 32 (BitVec.ofNat 32 (bytesToNat bs4))) ::
          ("%arrayidx.peel", .ptr (ep + (k.signExtend 64).toNat * 4)) ::
          ("%inc.peel", .int 64 (k + BitVec.ofNat 64 1)) ::
          cells loopHeadPhiCells s.env) s) := by
    have h0 := loopHead_denote (calls := calls) (k := k) s.env s hpre hk hep hb hklt hlane hlanelt hbyte
    rwa [show stateAt s.env s = s from rfl] at h0
  refine ⟨h, ?_, Stage2NoEventWalkInv.mem_congr h rfl⟩
  have hterm : loopHeadBlock.term = Term.br "NodeBlock5" := rfl
  have hstep := stage2NoEventWalk_step_at_block
    (f := stage2NoEventBody) (by rw [hpc]; exact loopHeadBlock_find)
    hcode
    (by rw [hterm])
  simpa only [stage2NoEventWalkNext, stage2NoEventJumpState, stateAt, execTerm] using hstep

/-- The head's cells after its reads, as a named environment. -/
abbrev openEnv0 (env : Env) (k : BitVec 64) (bs4 : List UInt8) (ep b : Nat)
    (bs1 : List UInt8) : Env :=
  ("%3", Value.int 8 (BitVec.ofNat 8 (bytesToNat bs1))) ::
    ("%arrayidx6.peel",
      Value.ptr (b + ((BitVec.ofNat 64 (bytesToNat bs4)).signExtend 64).toNat)) ::
    ("%idxprom.peel", Value.int 64 (BitVec.ofNat 64 (bytesToNat bs4))) ::
    ("%2", Value.int 32 (BitVec.ofNat 32 (bytesToNat bs4))) ::
    ("%arrayidx.peel", Value.ptr (ep + (k.signExtend 64).toNat * 4)) ::
    ("%inc.peel", Value.int 64 (k + BitVec.ofNat 64 1)) ::
    cells loopHeadPhiCells env

/-- The dispatch root's cell over it. -/
abbrev openEnv1 (env : Env) (k : BitVec 64) (bs4 : List UInt8) (ep b : Nat)
    (bs1 : List UInt8) : Env :=
  ("%Pivot6", Value.int 1 0) :: openEnv0 env k bs4 ep b bs1

/-- The inner dispatch's cell. -/
abbrev openEnv2 (env : Env) (k : BitVec 64) (bs4 : List UInt8) (ep b : Nat)
    (bs1 : List UInt8) : Env :=
  ("%Pivot", Value.int 1 0) :: openEnv1 env k bs4 ep b bs1

/-- The brace test's cell. -/
abbrev openEnv3 (env : Env) (k : BitVec 64) (bs4 : List UInt8) (ep b : Nat)
    (bs1 : List UInt8) : Env :=
  ("%SwitchLeaf4", Value.int 1 1) :: openEnv2 env k bs4 ep b bs1

/-- The open path's chain: the head, the dispatch tree at 123, and the brace's arm. -/
theorem chain_open123 {calls : Calls} {K : Stage2NoEventWalkCarry} {mem : Mem}
    {s : State} {k : BitVec 64} {ep b : Nat} {bs4 bs1 : List UInt8}
    (h : Stage2NoEventWalkInv K mem s) (hpc : s.pc = "if.end.peel")
    (hpre : s.pre = some "if.end.peel.preheader")
    (hk : lookupName (cells loopHeadPhiCells s.env) "%k.0.ph1404" = some (.int 64 k))
    (hep : lookupName (cells loopHeadPhiCells s.env) "%ep" = some (.ptr ep))
    (hb : lookupName (cells loopHeadPhiCells s.env) "%b" = some (.ptr b))
    (hklt : (k.signExtend 64).toNat < 2 ^ 63)
    (hlane : readBytes s.mem (ep + (k.signExtend 64).toNat * 4) 4 = some bs4)
    (hlanelt : bytesToNat bs4 < 2 ^ 32)
    (hbyte : readBytes s.mem (b + ((BitVec.ofNat 64 (bytesToNat bs4)).signExtend 64).toNat)
      1 = some bs1)
    (hy91 : evalICmp .slt (BitVec.ofNat 8 (bytesToNat bs1)) (BitVec.ofNat 8 91) = 0)
    (hy123 : evalICmp .slt (BitVec.ofNat 8 (bytesToNat bs1)) (BitVec.ofNat 8 123) = 0)
    (hy123eq : evalICmp .eq (BitVec.ofNat 8 (bytesToNat bs1)) (BitVec.ofNat 8 123) = 1) :
    Stage2NoEventWalkChain calls mem K s K
      (stage2NoEventWalkNext (openEnv3 s.env k bs4 ep b bs1)
        (stage2NoEventWalkNext (openEnv2 s.env k bs4 ep b bs1)
          (stage2NoEventWalkNext (openEnv1 s.env k bs4 ep b bs1)
            (stage2NoEventWalkNext (openEnv0 s.env k bs4 ep b bs1) s "NodeBlock5")
            "NodeBlock")
          "LeafBlock3")
        "if.then9") := by
  have h1 := link_loopHead (calls := calls) h hpc hpre hk hep hb hklt hlane hlanelt hbyte
  have h3a : lookupName (openEnv0 s.env k bs4 ep b bs1) "%3" =
      some (.int 8 (BitVec.ofNat 8 (bytesToNat bs1))) := by
    simp only [openEnv0, lookupName_cons_self]
  have h2 := link_nodeBlock5_false (calls := calls) (K := K) (mem := mem)
    (s := stage2NoEventWalkNext (openEnv0 s.env k bs4 ep b bs1) s "NodeBlock5")
    h1.inv' (by simp only [stage2NoEventWalkNext]) h3a hy91
  have h3b : lookupName (openEnv1 s.env k bs4 ep b bs1) "%3" =
      some (.int 8 (BitVec.ofNat 8 (bytesToNat bs1))) := by
    simp only [openEnv1, openEnv0]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    simp only [lookupName_cons_self]
  have h3 := link_nodeBlock_false (calls := calls) (K := K) (mem := mem)
    (s := stage2NoEventWalkNext (openEnv1 s.env k bs4 ep b bs1)
      (stage2NoEventWalkNext (openEnv0 s.env k bs4 ep b bs1) s "NodeBlock5") "NodeBlock")
    h2.inv' (by simp only [stage2NoEventWalkNext]) h3b hy123
  have h3c : lookupName (openEnv2 s.env k bs4 ep b bs1) "%3" =
      some (.int 8 (BitVec.ofNat 8 (bytesToNat bs1))) := by
    simp only [openEnv2, openEnv1, openEnv0]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    simp only [lookupName_cons_self]
  have h4 := link_leafBlock3_true (calls := calls) (K := K) (mem := mem)
    (s := stage2NoEventWalkNext (openEnv2 s.env k bs4 ep b bs1)
      (stage2NoEventWalkNext (openEnv1 s.env k bs4 ep b bs1)
        (stage2NoEventWalkNext (openEnv0 s.env k bs4 ep b bs1) s "NodeBlock5") "NodeBlock")
      "LeafBlock3")
    h3.inv' (by simp only [stage2NoEventWalkNext]) h3c hy123eq
  exact Stage2NoEventWalkChain.tail h1
    (Stage2NoEventWalkChain.tail h2
      (Stage2NoEventWalkChain.tail h3
        (Stage2NoEventWalkChain.tail h4
          (Stage2NoEventWalkChain.nil h4.inv'))))

/-- The dispatch root's cell on the false arm. -/
abbrev closeEnv1 (env : Env) (k : BitVec 64) (bs4 : List UInt8) (ep b : Nat)
    (bs1 : List UInt8) : Env :=
  ("%Pivot6", Value.int 1 0) :: openEnv0 env k bs4 ep b bs1

/-- The inner dispatch's cell on the false arm. -/
abbrev closeEnv2 (env : Env) (k : BitVec 64) (bs4 : List UInt8) (ep b : Nat)
    (bs1 : List UInt8) : Env :=
  ("%Pivot", Value.int 1 0) :: closeEnv1 env k bs4 ep b bs1

/-- The brace test's cell on the false arm. -/
abbrev closeEnv3 (env : Env) (k : BitVec 64) (bs4 : List UInt8) (ep b : Nat)
    (bs1 : List UInt8) : Env :=
  ("%SwitchLeaf4", Value.int 1 0) :: closeEnv2 env k bs4 ep b bs1

/-- The close path's chain: the head and the dispatch tree at a byte above 123,
to the scalar arm (the closers' route). -/
theorem chain_close125 {calls : Calls} {K : Stage2NoEventWalkCarry} {mem : Mem}
    {s : State} {k : BitVec 64} {ep b : Nat} {bs4 bs1 : List UInt8}
    (h : Stage2NoEventWalkInv K mem s) (hpc : s.pc = "if.end.peel")
    (hpre : s.pre = some "if.end.peel.preheader")
    (hk : lookupName (cells loopHeadPhiCells s.env) "%k.0.ph1404" = some (.int 64 k))
    (hep : lookupName (cells loopHeadPhiCells s.env) "%ep" = some (.ptr ep))
    (hb : lookupName (cells loopHeadPhiCells s.env) "%b" = some (.ptr b))
    (hklt : (k.signExtend 64).toNat < 2 ^ 63)
    (hlane : readBytes s.mem (ep + (k.signExtend 64).toNat * 4) 4 = some bs4)
    (hlanelt : bytesToNat bs4 < 2 ^ 32)
    (hbyte : readBytes s.mem (b + ((BitVec.ofNat 64 (bytesToNat bs4)).signExtend 64).toNat)
      1 = some bs1)
    (hy91 : evalICmp .slt (BitVec.ofNat 8 (bytesToNat bs1)) (BitVec.ofNat 8 91) = 0)
    (hy123 : evalICmp .slt (BitVec.ofNat 8 (bytesToNat bs1)) (BitVec.ofNat 8 123) = 0)
    (hy123ne : evalICmp .eq (BitVec.ofNat 8 (bytesToNat bs1)) (BitVec.ofNat 8 123) = 0) :
    Stage2NoEventWalkChain calls mem K s K
      (stage2NoEventWalkNext (closeEnv3 s.env k bs4 ep b bs1)
        (stage2NoEventWalkNext (closeEnv2 s.env k bs4 ep b bs1)
          (stage2NoEventWalkNext (closeEnv1 s.env k bs4 ep b bs1)
            (stage2NoEventWalkNext (openEnv0 s.env k bs4 ep b bs1) s "NodeBlock5")
            "NodeBlock")
          "LeafBlock3")
        "scalar") := by
  have h1 := link_loopHead (calls := calls) h hpc hpre hk hep hb hklt hlane hlanelt hbyte
  have h3a : lookupName (openEnv0 s.env k bs4 ep b bs1) "%3" =
      some (.int 8 (BitVec.ofNat 8 (bytesToNat bs1))) := by
    simp only [openEnv0, lookupName_cons_self]
  have h2 := link_nodeBlock5_false (calls := calls) (K := K) (mem := mem)
    (s := stage2NoEventWalkNext (openEnv0 s.env k bs4 ep b bs1) s "NodeBlock5")
    h1.inv' (by simp only [stage2NoEventWalkNext]) h3a hy91
  have h3b : lookupName (closeEnv1 s.env k bs4 ep b bs1) "%3" =
      some (.int 8 (BitVec.ofNat 8 (bytesToNat bs1))) := by
    simp only [closeEnv1, openEnv0]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    simp only [lookupName_cons_self]
  have h3 := link_nodeBlock_false (calls := calls) (K := K) (mem := mem)
    (s := stage2NoEventWalkNext (closeEnv1 s.env k bs4 ep b bs1)
      (stage2NoEventWalkNext (openEnv0 s.env k bs4 ep b bs1) s "NodeBlock5") "NodeBlock")
    h2.inv' (by simp only [stage2NoEventWalkNext]) h3b hy123
  have h3c : lookupName (closeEnv2 s.env k bs4 ep b bs1) "%3" =
      some (.int 8 (BitVec.ofNat 8 (bytesToNat bs1))) := by
    simp only [closeEnv2, closeEnv1, openEnv0]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    simp only [lookupName_cons_self]
  have h4 := link_leafBlock3_false (calls := calls) (K := K) (mem := mem)
    (s := stage2NoEventWalkNext (closeEnv2 s.env k bs4 ep b bs1)
      (stage2NoEventWalkNext (closeEnv1 s.env k bs4 ep b bs1)
        (stage2NoEventWalkNext (openEnv0 s.env k bs4 ep b bs1) s "NodeBlock5") "NodeBlock")
      "LeafBlock3")
    h3.inv' (by simp only [stage2NoEventWalkNext]) h3c hy123ne
  exact Stage2NoEventWalkChain.tail h1
    (Stage2NoEventWalkChain.tail h2
      (Stage2NoEventWalkChain.tail h3
        (Stage2NoEventWalkChain.tail h4
          (Stage2NoEventWalkChain.nil h4.inv'))))

/-- `if.then9`: the brace's payload entry, seven phis and the depth test. -/
def ifThen9Instrs : List Instr :=
  [ Instr.phi "%inc.lcssa1129" (Ty.int 64)
      [("LeafBlock3", Operand.reg "%inc.peel"), ("if.then9.loopexit", Operand.reg "%inc")],
    Instr.phi "%idxprom.lcssa1108" (Ty.int 64)
      [("LeafBlock3", Operand.reg "%idxprom.peel"),
       ("if.then9.loopexit", Operand.reg "%idxprom.le1289")],
    Instr.phi "%frame.0.lcssa1098" (Ty.int 8)
      [("LeafBlock3", Operand.reg "%frame.0.ph1402"),
       ("if.then9.loopexit", Operand.imm (.int 8 (BitVec.ofNat 8 1)))],
    Instr.phi "%sp.0.lcssa1092.wide" (Ty.int 32)
      [("LeafBlock3", Operand.reg "%sp.0.ph1403"),
       ("if.then9.loopexit", Operand.reg "%9")],
    Instr.phi "%k.0.lcssa1086" (Ty.int 64)
      [("LeafBlock3", Operand.reg "%k.0.ph1404"),
       ("if.then9.loopexit", Operand.reg "%k.0")],
    Instr.phi "%terms.0.lcssa1080" (Ty.int 64)
      [("LeafBlock3", Operand.reg "%terms.0.ph1407"),
       ("if.then9.loopexit", Operand.reg "%terms.0")],
    Instr.phi "%tokens.0.lcssa1074" (Ty.int 64)
      [("LeafBlock3", Operand.reg "%tokens.0.ph1408"),
       ("if.then9.loopexit", Operand.reg "%tokens.0")],
    Instr.icmp "%cmp10" IPred.ugt 32 (Operand.reg "%sp.0.lcssa1092.wide")
      (Operand.imm (.int 32 (BitVec.ofNat 32 519))) ]

/-- The `if.then9` cells: its seven phis and its depth test. -/
abbrev ifThen9Env (env : Env) (sp : BitVec 32) : Env :=
  ("%cmp10", Value.int 1 (evalICmp .ugt sp (BitVec.ofNat 32 519))) ::
    ("%tokens.0.lcssa1074", Value.int 64 (BitVec.ofNat 64 0)) ::
    ("%terms.0.lcssa1080", Value.int 64 (BitVec.ofNat 64 0)) ::
    ("%k.0.lcssa1086", Value.int 64 (BitVec.ofNat 64 0)) ::
    ("%sp.0.lcssa1092.wide", Value.int 32 sp) ::
    ("%frame.0.lcssa1098", Value.int 8 (BitVec.ofNat 8 0)) ::
    ("%idxprom.lcssa1108", Value.int 64 0) ::
    ("%inc.lcssa1129", Value.int 64 0) :: env

/-- The `if.then9` block's leading phi run, as specs. -/
def ifThen9PhiSpecs : List PhiSpec :=
  [ { dst := "%inc.lcssa1129", ty := Ty.int 64,
      incoming := [("LeafBlock3", Operand.reg "%inc.peel"),
        ("if.then9.loopexit", Operand.reg "%inc")] },
    { dst := "%idxprom.lcssa1108", ty := Ty.int 64,
      incoming := [("LeafBlock3", Operand.reg "%idxprom.peel"),
        ("if.then9.loopexit", Operand.reg "%idxprom.le1289")] },
    { dst := "%frame.0.lcssa1098", ty := Ty.int 8,
      incoming := [("LeafBlock3", Operand.reg "%frame.0.ph1402"),
        ("if.then9.loopexit", Operand.imm (.int 8 (BitVec.ofNat 8 1)))] },
    { dst := "%sp.0.lcssa1092.wide", ty := Ty.int 32,
      incoming := [("LeafBlock3", Operand.reg "%sp.0.ph1403"),
        ("if.then9.loopexit", Operand.reg "%9")] },
    { dst := "%k.0.lcssa1086", ty := Ty.int 64,
      incoming := [("LeafBlock3", Operand.reg "%k.0.ph1404"),
        ("if.then9.loopexit", Operand.reg "%k.0")] },
    { dst := "%terms.0.lcssa1080", ty := Ty.int 64,
      incoming := [("LeafBlock3", Operand.reg "%terms.0.ph1407"),
        ("if.then9.loopexit", Operand.reg "%terms.0")] },
    { dst := "%tokens.0.lcssa1074", ty := Ty.int 64,
      incoming := [("LeafBlock3", Operand.reg "%tokens.0.ph1408"),
        ("if.then9.loopexit", Operand.reg "%tokens.0")] } ]

theorem ifThen9Phi_eq :
    ifThen9Instrs = List.map PhiSpec.instr ifThen9PhiSpecs ++
      [Instr.icmp "%cmp10" IPred.ugt 32 (Operand.reg "%sp.0.lcssa1092.wide")
        (Operand.imm (.int 32 (BitVec.ofNat 32 519)))] := by
  decide

/-- The `if.then9` cells at the first iteration: the seven phis select the
`LeafBlock3` edge, and the depth word is the head's zero. -/
abbrev ifThen9Env1 (env : Env) (k : BitVec 64) (bs4 : List UInt8) : Env :=
  ("%cmp10", Value.int 1 0) ::
    ("%tokens.0.lcssa1074", Value.int 64 0) ::
    ("%terms.0.lcssa1080", Value.int 64 0) ::
    ("%k.0.lcssa1086", Value.int 64 k) ::
    ("%sp.0.lcssa1092.wide", Value.int 32 0) ::
    ("%frame.0.lcssa1098", Value.int 8 0) ::
    ("%idxprom.lcssa1108", Value.int 64 (BitVec.ofNat 64 (bytesToNat bs4))) ::
    ("%inc.lcssa1129", Value.int 64 (k + BitVec.ofNat 64 1)) ::
    env

/-- The `if.then9` row: its seven phis as one run, its depth test, and its arm. -/
theorem ifThen9_denote {calls : Calls} (env : Env) (s : State)
    {k : BitVec 64} {bs4 : List UInt8}
    (hpre : s.pre = some "LeafBlock3")
    (hk : lookupName env "%k.0.ph1404" = some (.int 64 k))
    (hinc : lookupName env "%inc.peel" = some (.int 64 (k + BitVec.ofNat 64 1)))
    (hidx : lookupName env "%idxprom.peel" =
      some (.int 64 (BitVec.ofNat 64 (bytesToNat bs4))))
    (hfr : lookupName env "%frame.0.ph1402" = some (.int 8 0))
    (hsp : lookupName env "%sp.0.ph1403" = some (.int 32 0))
    (htr : lookupName env "%terms.0.ph1407" = some (.int 64 0))
    (htok : lookupName env "%tokens.0.ph1408" = some (.int 64 0)) :
    denoteCode calls ifThen9Instrs (stateAt env s) =
      some (stateAt (ifThen9Env1 env k bs4) s) := by
  have hsel : PhiSelects (stateAt env s) "LeafBlock3" ifThen9PhiSpecs
      [("%inc.lcssa1129", .int 64 (k + BitVec.ofNat 64 1)),
       ("%idxprom.lcssa1108", .int 64 (BitVec.ofNat 64 (bytesToNat bs4))),
       ("%frame.0.lcssa1098", .int 8 0),
       ("%sp.0.lcssa1092.wide", .int 32 0),
       ("%k.0.lcssa1086", .int 64 k),
       ("%terms.0.lcssa1080", .int 64 0),
       ("%tokens.0.lcssa1074", .int 64 0)] := by
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
      (rest := [Instr.icmp "%cmp10" IPred.ugt 32 (Operand.reg "%sp.0.lcssa1092.wide")
        (Operand.imm (.int 32 (BitVec.ofNat 32 519)))])
      (hpre := hpre) (hsel := hsel) (hrest := rfl)]
  simp only [State.bindAll, State.bind, ifThen9Env1, cells, runCells]
  rfl

/-- **The `if.then9` link**: the seven `phi`s, the depth guard at the `phi` cells,
and the false arm to `if.end19`.  The whole block is one `denoteCode` at the phi
run's `rest` (w26), so the guard is proved at `ifThen9Env1` with no call-site
append. -/
theorem link_ifThen9 {calls : Calls} {K : Stage2NoEventWalkCarry} {mem : Mem}
    {s : State} {k : BitVec 64} {bs4 : List UInt8}
    (h : Stage2NoEventWalkInv K mem s) (hpc : s.pc = "if.then9")
    (hpre : s.pre = some "LeafBlock3")
    (hk : lookupName s.env "%k.0.ph1404" = some (.int 64 k))
    (hinc : lookupName s.env "%inc.peel" = some (.int 64 (k + BitVec.ofNat 64 1)))
    (hidx : lookupName s.env "%idxprom.peel" =
      some (.int 64 (BitVec.ofNat 64 (bytesToNat bs4))))
    (hfr : lookupName s.env "%frame.0.ph1402" = some (.int 8 0))
    (hsp : lookupName s.env "%sp.0.ph1403" = some (.int 32 0))
    (htr : lookupName s.env "%terms.0.ph1407" = some (.int 64 0))
    (htokr : lookupName s.env "%tokens.0.ph1408" = some (.int 64 0)) :
    Stage2NoEventWalkLink calls K mem s K
      (stage2NoEventWalkNext (ifThen9Env1 s.env k bs4) s "if.end19") := by
  have hblock : ifThen9Block.instrs = ifThen9Instrs := by decide
  have hcode : denoteCode calls ifThen9Block.instrs (stateAt s.env s) =
      some (stateAt (ifThen9Env1 s.env k bs4) s) := by
    rw [hblock]
    exact ifThen9_denote (calls := calls) s.env s hpre hk hinc hidx hfr hsp htr htokr
  refine stage2NoEventWalkLink_condbr_false (env' := ifThen9Env1 s.env k bs4)
    h (by rw [hpc]; exact ifThen9Block_find) hcode rfl ?_
  simp only [ifThen9Env1, lookupName_cons_self]

/-! ### The loop exits and their class heads

The continuation dispatch's four exits are the block stubs that hand the loop's
carried state to a class head: `if.then9.loopexit` (the brace), `if.then35` (the
bracket), `string_value.loopexit` (the string) and `scalar.loopexit` (the value).
Each stub computes the entry index and the depth word, and the head then runs its
`phi` run and its first test.  The rows below stop at that test's branch: the
class arm behind it is the class's own segment, not this one's.

The `phi` runs are the block's, read off `PhiSpec` lists: `ifThen9PhiSpecs` is the
brace head's (shared with the `LeafBlock3` edge) and the others are stated here.
No register the runs read is carried by `Stage2NoEventWalkInv`; every one is a
lookup at the state's environment, and each link takes the ones it reads as
hypotheses, the way the head's own link does.  The lifetime marker in
`string_value` is a call: the link is parametric in the selection and takes the
outcome's own neutrality (`out.mem = s.mem`, `out.next = s.next`), which
`stage2Calls_lifetime` supplies for `stage2Calls`'s resolution. -/

/-- A comparison of two registers, at any predicate and width. -/
theorem stage2NoEventWalk_denote_icmp_reg (calls : Calls) (env : Env) (s : State)
    (d a b : String) (p : IPred) (w : Nat) {x y : BitVec w}
    (ha : lookupName env a = some (.int w x))
    (hb : lookupName env b = some (.int w y)) (is : List Instr) :
    denoteCode calls (.icmp d p w (.reg a) (.reg b) :: is) (stateAt env s) =
      denoteCode calls is (stateAt ((d, .int 1 (evalICmp p x y)) :: env) s) := by
  have ha' : evalOperand (stateAt env s) (.reg a) = some (.int w x) := by
    simp only [stateAt, evalOperand, ha]
  have hb' : evalOperand (stateAt env s) (.reg b) = some (.int w y) := by
    simp only [stateAt, evalOperand, hb]
  have hstep : evalInstr calls (stateAt env s) (.icmp d p w (.reg a) (.reg b)) =
      some ((stateAt env s).bind d (.int 1 (evalICmp p x y))) :=
    JsonS1MasksIR.evalInstr_icmp ha' hb'
  rw [denoteCode_cons_of _ _ _ _ _ hstep]
  simp only [stateAt, State.bind]

/-! #### `if.then9.loopexit`: the brace's exit stub and the head at its edge -/

/-- `if.then9.loopexit`: `%idxprom.le1289 = zext %8`, `%9 = trunc %indvars.iv`. -/
def ifThen9LoopexitInstrs : List Instr :=
  [ Instr.zext "%idxprom.le1289" 32 64 (Operand.reg "%8"),
    Instr.trunc "%9" 64 32 (Operand.reg "%indvars.iv") ]

/-- `if.then9.loopexit`, pinned. -/
def ifThen9LoopexitBlock : Block :=
  { name := "if.then9.loopexit", instrs := ifThen9LoopexitInstrs,
    term := Term.br "if.then9" }

theorem ifThen9LoopexitBlock_find :
    stage2NoEventBody.findBlock "if.then9.loopexit" = some ifThen9LoopexitBlock := by
  decide

theorem ifThen9LoopexitEntry_denote (calls : Calls) (env : Env) (s : State)
    {w : BitVec 32} {iv : BitVec 64}
    (h8 : lookupName env "%8" = some (.int 32 w))
    (hiv : lookupName env "%indvars.iv" = some (.int 64 iv)) :
    denoteCode calls ifThen9LoopexitInstrs (stateAt env s) =
      some (stateAt
        (("%9", .int 32 (BitVec.ofNat 32 (iv.toNat % 2 ^ 32))) ::
          ("%idxprom.le1289", .int 64 (BitVec.ofNat 64 w.toNat)) :: env) s) := by
  unfold ifThen9LoopexitInstrs
  rw [denoteCode_zext (calls := calls) (env := env) (s := s) (d := "%idxprom.le1289")
    (v := "%8") (wIn := 32) (wOut := 64) (x := w) h8]
  rw [denoteCode_trunc (calls := calls)
    (env := ("%idxprom.le1289", .int 64 (BitVec.ofNat 64 w.toNat)) :: env) (s := s)
    (d := "%9") (v := "%indvars.iv") (wIn := 64) (wOut := 32) (x := iv)
    (lookupName_cons_other _ _ _ (by decide) hiv)]
  simp only [denoteCode_nil]

/-- The brace's exit stub: the index's zero extension and the depth's truncation,
to `if.then9`. -/
theorem link_ifThen9LoopexitEntry {calls : Calls} {K : Stage2NoEventWalkCarry}
    {mem : Mem} {s : State} {w : BitVec 32} {iv : BitVec 64}
    (h : Stage2NoEventWalkInv K mem s) (hpc : s.pc = "if.then9.loopexit")
    (h8 : lookupName s.env "%8" = some (.int 32 w))
    (hiv : lookupName s.env "%indvars.iv" = some (.int 64 iv)) :
    Stage2NoEventWalkLink calls K mem s K
      (stage2NoEventWalkNext
        (("%9", .int 32 (BitVec.ofNat 32 (iv.toNat % 2 ^ 32))) ::
          ("%idxprom.le1289", .int 64 (BitVec.ofNat 64 w.toNat)) :: s.env)
        s "if.then9") := by
  have hcode := ifThen9LoopexitEntry_denote (calls := calls) (env := s.env) (s := s) h8 hiv
  refine ⟨h, ?_, Stage2NoEventWalkInv.mem_congr h rfl⟩
  have hstep := stage2NoEventWalk_step_br (s := s) (f := stage2NoEventBody)
    (by rw [hpc]; exact ifThen9LoopexitBlock_find) hcode rfl
  simpa only [stage2NoEventWalkNext, stateAt] using hstep

/-- The `if.then9` cells at the brace exit's edge: its seven `phi`s and the depth
test, with `%sp` the truncated index. -/
abbrev ifThen9AtLoopexitCells (env : Env) (inc idx : BitVec 64) (sp9 : BitVec 32)
    (k terms tok : BitVec 64) : Env :=
  ("%cmp10", Value.int 1 (evalICmp .ugt sp9 (BitVec.ofNat 32 519))) ::
    ("%tokens.0.lcssa1074", Value.int 64 tok) ::
    ("%terms.0.lcssa1080", Value.int 64 terms) ::
    ("%k.0.lcssa1086", Value.int 64 k) ::
    ("%sp.0.lcssa1092.wide", Value.int 32 sp9) ::
    ("%frame.0.lcssa1098", Value.int 8 1) ::
    ("%idxprom.lcssa1108", Value.int 64 idx) ::
    ("%inc.lcssa1129", Value.int 64 inc) :: env

/-- The brace head's `phi` bindings at the brace exit's edge, in the order the
block writes them. -/
def ifThen9AtLoopexitVs (inc idx : BitVec 64) (sp9 : BitVec 32)
    (k terms tok : BitVec 64) : List (String × Value) :=
  [("%inc.lcssa1129", .int 64 inc),
   ("%idxprom.lcssa1108", .int 64 idx),
   ("%frame.0.lcssa1098", .int 8 (BitVec.ofNat 8 1)),
   ("%sp.0.lcssa1092.wide", .int 32 sp9),
   ("%k.0.lcssa1086", .int 64 k),
   ("%terms.0.lcssa1080", .int 64 terms),
   ("%tokens.0.lcssa1074", .int 64 tok)]

/-- **The brace head at the brace exit's edge**: `ifThen9PhiSpecs`' seven `phi`s
selecting `if.then9.loopexit`'s operands, then the depth test.  (`ifThen9_denote`
is the same run at the `LeafBlock3` edge; the specs and their split are reused
here.) -/
theorem ifThen9AtLoopexit_denote {calls : Calls} (env : Env) (s : State)
    {inc idx k terms tok : BitVec 64} {sp9 : BitVec 32}
    (hpre : s.pre = some "if.then9.loopexit")
    (hinc : lookupName env "%inc" = some (.int 64 inc))
    (hidx : lookupName env "%idxprom.le1289" = some (.int 64 idx))
    (h9 : lookupName env "%9" = some (.int 32 sp9))
    (hk : lookupName env "%k.0" = some (.int 64 k))
    (htr : lookupName env "%terms.0" = some (.int 64 terms))
    (htok : lookupName env "%tokens.0" = some (.int 64 tok)) :
    denoteCode calls ifThen9Instrs (stateAt env s) =
      some (stateAt (ifThen9AtLoopexitCells env inc idx sp9 k terms tok) s) := by
  have hsel : PhiSelects (stateAt env s) "if.then9.loopexit" ifThen9PhiSpecs
      (ifThen9AtLoopexitVs inc idx sp9 k terms tok) := by
    simp only [ifThen9AtLoopexitVs]
    refine PhiSelects.cons (op := .reg "%inc") (by decide) ?_
      (PhiSelects.cons (op := .reg "%idxprom.le1289") (by decide) ?_
        (PhiSelects.cons (op := .imm (.int 8 (BitVec.ofNat 8 1))) (by decide) ?_
          (PhiSelects.cons (op := .reg "%9") (by decide) ?_
            (PhiSelects.cons (op := .reg "%k.0") (by decide) ?_
              (PhiSelects.cons (op := .reg "%terms.0") (by decide) ?_
                (PhiSelects.cons (op := .reg "%tokens.0") (by decide) ?_
                  PhiSelects.nil))))))
    all_goals
      simp only [stateAt, evalOperand, Const.toValue, hinc, hidx, h9, hk, htr, htok] <;>
        rfl
  rw [ifThen9Phi_eq,
    denoteCode_phiRun (s := stateAt env s) (p := "if.then9.loopexit")
      (specs := ifThen9PhiSpecs) (vs := ifThen9AtLoopexitVs inc idx sp9 k terms tok)
      (rest := [Instr.icmp "%cmp10" IPred.ugt 32 (Operand.reg "%sp.0.lcssa1092.wide")
        (Operand.imm (.int 32 (BitVec.ofNat 32 519)))])
      (hpre := hpre) (hsel := hsel) (hrest := rfl)]
  rw [stateAt_bindAll_runCells]
  have hSp : lookupName (runCells (ifThen9AtLoopexitVs inc idx sp9 k terms tok) env)
      "%sp.0.lcssa1092.wide" = some (.int 32 sp9) := by
    simp only [ifThen9AtLoopexitVs, runCells]
    rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide)]
    simp only [lookupName_cons_self]
  rw [stage2NoEventWalk_denote_icmp_imm (calls := calls)
    (env := runCells (ifThen9AtLoopexitVs inc idx sp9 k terms tok) env) (s := s)
    (d := "%cmp10") (a := "%sp.0.lcssa1092.wide") (p := .ugt) (w := 32)
    (c := BitVec.ofNat 32 519) hSp (is := [])]
  simp only [denoteCode_nil, ifThen9AtLoopexitCells, ifThen9AtLoopexitVs, runCells]
  rfl

/-- **The brace head's depth test, taken**: the exit's edge, the `phi` run, and
`if.then9`'s `%cmp10` arm to `if.then12`. -/
theorem link_ifThen9AtLoopexit_true {calls : Calls} {K : Stage2NoEventWalkCarry}
    {mem : Mem} {s : State} {inc idx k terms tok : BitVec 64} {sp9 : BitVec 32}
    (h : Stage2NoEventWalkInv K mem s) (hpc : s.pc = "if.then9")
    (hpre : s.pre = some "if.then9.loopexit")
    (hinc : lookupName s.env "%inc" = some (.int 64 inc))
    (hidx : lookupName s.env "%idxprom.le1289" = some (.int 64 idx))
    (h9 : lookupName s.env "%9" = some (.int 32 sp9))
    (hk : lookupName s.env "%k.0" = some (.int 64 k))
    (htr : lookupName s.env "%terms.0" = some (.int 64 terms))
    (htok : lookupName s.env "%tokens.0" = some (.int 64 tok))
    (hy : evalICmp .ugt sp9 (BitVec.ofNat 32 519) = 1) :
    Stage2NoEventWalkLink calls K mem s K
      (stage2NoEventWalkNext
        (ifThen9AtLoopexitCells s.env inc idx sp9 k terms tok) s "if.then12") := by
  have hblock : ifThen9Block.instrs = ifThen9Instrs := by decide
  have hcode : denoteCode calls ifThen9Block.instrs (stateAt s.env s) =
      some (stateAt (ifThen9AtLoopexitCells s.env inc idx sp9 k terms tok) s) := by
    rw [hblock]
    exact ifThen9AtLoopexit_denote (calls := calls) s.env s hpre hinc hidx h9 hk htr htok
  exact stage2NoEventWalkLink_condbr_true
    (env' := ifThen9AtLoopexitCells s.env inc idx sp9 k terms tok)
    h (by rw [hpc]; exact ifThen9Block_find) hcode rfl
    (by simp only [ifThen9AtLoopexitCells, lookupName_cons_self, hy])

/-- **The brace head's depth test, not taken**: the same run, to `if.end19`. -/
theorem link_ifThen9AtLoopexit_false {calls : Calls} {K : Stage2NoEventWalkCarry}
    {mem : Mem} {s : State} {inc idx k terms tok : BitVec 64} {sp9 : BitVec 32}
    (h : Stage2NoEventWalkInv K mem s) (hpc : s.pc = "if.then9")
    (hpre : s.pre = some "if.then9.loopexit")
    (hinc : lookupName s.env "%inc" = some (.int 64 inc))
    (hidx : lookupName s.env "%idxprom.le1289" = some (.int 64 idx))
    (h9 : lookupName s.env "%9" = some (.int 32 sp9))
    (hk : lookupName s.env "%k.0" = some (.int 64 k))
    (htr : lookupName s.env "%terms.0" = some (.int 64 terms))
    (htok : lookupName s.env "%tokens.0" = some (.int 64 tok))
    (hy : evalICmp .ugt sp9 (BitVec.ofNat 32 519) = 0) :
    Stage2NoEventWalkLink calls K mem s K
      (stage2NoEventWalkNext
        (ifThen9AtLoopexitCells s.env inc idx sp9 k terms tok) s "if.end19") := by
  have hblock : ifThen9Block.instrs = ifThen9Instrs := by decide
  have hcode : denoteCode calls ifThen9Block.instrs (stateAt s.env s) =
      some (stateAt (ifThen9AtLoopexitCells s.env inc idx sp9 k terms tok) s) := by
    rw [hblock]
    exact ifThen9AtLoopexit_denote (calls := calls) s.env s hpre hinc hidx h9 hk htr htok
  exact stage2NoEventWalkLink_condbr_false
    (env' := ifThen9AtLoopexitCells s.env inc idx sp9 k terms tok)
    h (by rw [hpc]; exact ifThen9Block_find) hcode rfl
    (by simp only [ifThen9AtLoopexitCells, lookupName_cons_self, hy])

/-! #### `if.then35`: the bracket's exit test -/

/-- `if.then35`: the entry index against the budget's trip count. -/
def ifThen35Instrs : List Instr :=
  [ Instr.icmp "%exitcond" IPred.eq 64 (Operand.reg "%indvars.iv")
      (Operand.reg "%wide.trip.count1409") ]

/-- `if.then35`, pinned. -/
def ifThen35Block : Block :=
  { name := "if.then35", instrs := ifThen35Instrs,
    term := Term.condbr (Operand.reg "%exitcond") "if.then38.loopexit" "if.end51" }

theorem ifThen35Block_find :
    stage2NoEventBody.findBlock "if.then35" = some ifThen35Block := by
  decide

theorem ifThen35_denote (calls : Calls) (env : Env) (s : State)
    {iv cnt : BitVec 64}
    (hiv : lookupName env "%indvars.iv" = some (.int 64 iv))
    (hcnt : lookupName env "%wide.trip.count1409" = some (.int 64 cnt)) :
    denoteCode calls ifThen35Instrs (stateAt env s) =
      some (stateAt (("%exitcond", .int 1 (evalICmp .eq iv cnt)) :: env) s) := by
  rw [ifThen35Instrs, denoteCode_icmp_eq_reg (calls := calls) (env := env) (s := s)
    (d := "%exitcond") (a := "%indvars.iv") (b := "%wide.trip.count1409")
    hiv hcnt (is := [])]
  simp only [denoteCode_nil]

/-- **The bracket's exit test, taken**: the index reached the trip count, to
`if.then38.loopexit`. -/
theorem link_ifThen35_true {calls : Calls} {K : Stage2NoEventWalkCarry}
    {mem : Mem} {s : State} {iv cnt : BitVec 64}
    (h : Stage2NoEventWalkInv K mem s) (hpc : s.pc = "if.then35")
    (hiv : lookupName s.env "%indvars.iv" = some (.int 64 iv))
    (hcnt : lookupName s.env "%wide.trip.count1409" = some (.int 64 cnt))
    (hy : evalICmp .eq iv cnt = 1) :
    Stage2NoEventWalkLink calls K mem s K
      (stage2NoEventWalkNext (("%exitcond", .int 1 1) :: s.env) s
        "if.then38.loopexit") := by
  have hcode : denoteCode calls ifThen35Instrs (stateAt s.env s) =
      some (stateAt (("%exitcond", .int 1 1) :: s.env) s) := by
    have hd := ifThen35_denote (calls := calls) s.env s hiv hcnt
    rw [hy] at hd
    exact hd
  exact stage2NoEventWalkLink_condbr_true (env' := ("%exitcond", .int 1 1) :: s.env)
    h (by rw [hpc]; exact ifThen35Block_find) hcode rfl (by rw [lookupName_cons_self])

/-- **The bracket's exit test, not taken**: the index is short of the trip count,
to `if.end51`. -/
theorem link_ifThen35_false {calls : Calls} {K : Stage2NoEventWalkCarry}
    {mem : Mem} {s : State} {iv cnt : BitVec 64}
    (h : Stage2NoEventWalkInv K mem s) (hpc : s.pc = "if.then35")
    (hiv : lookupName s.env "%indvars.iv" = some (.int 64 iv))
    (hcnt : lookupName s.env "%wide.trip.count1409" = some (.int 64 cnt))
    (hy : evalICmp .eq iv cnt = 0) :
    Stage2NoEventWalkLink calls K mem s K
      (stage2NoEventWalkNext (("%exitcond", .int 1 0) :: s.env) s "if.end51") := by
  have hcode : denoteCode calls ifThen35Instrs (stateAt s.env s) =
      some (stateAt (("%exitcond", .int 1 0) :: s.env) s) := by
    have hd := ifThen35_denote (calls := calls) s.env s hiv hcnt
    rw [hy] at hd
    exact hd
  exact stage2NoEventWalkLink_condbr_false (env' := ("%exitcond", .int 1 0) :: s.env)
    h (by rw [hpc]; exact ifThen35Block_find) hcode rfl (by rw [lookupName_cons_self])

/-! #### `string_value.loopexit`: the string's exit stub and head -/

/-- `string_value.loopexit`: `%idxprom.le1287 = zext %8`, `%28 = trunc %indvars.iv`. -/
def stringValueLoopexitInstrs : List Instr :=
  [ Instr.zext "%idxprom.le1287" 32 64 (Operand.reg "%8"),
    Instr.trunc "%28" 64 32 (Operand.reg "%indvars.iv") ]

/-- `string_value.loopexit`, pinned. -/
def stringValueLoopexitBlock : Block :=
  { name := "string_value.loopexit", instrs := stringValueLoopexitInstrs,
    term := Term.br "string_value" }

theorem stringValueLoopexitBlock_find :
    stage2NoEventBody.findBlock "string_value.loopexit" = some stringValueLoopexitBlock := by
  decide

theorem stringValueLoopexit_denote (calls : Calls) (env : Env) (s : State)
    {w : BitVec 32} {iv : BitVec 64}
    (h8 : lookupName env "%8" = some (.int 32 w))
    (hiv : lookupName env "%indvars.iv" = some (.int 64 iv)) :
    denoteCode calls stringValueLoopexitInstrs (stateAt env s) =
      some (stateAt
        (("%28", .int 32 (BitVec.ofNat 32 (iv.toNat % 2 ^ 32))) ::
          ("%idxprom.le1287", .int 64 (BitVec.ofNat 64 w.toNat)) :: env) s) := by
  unfold stringValueLoopexitInstrs
  rw [denoteCode_zext (calls := calls) (env := env) (s := s) (d := "%idxprom.le1287")
    (v := "%8") (wIn := 32) (wOut := 64) (x := w) h8]
  rw [denoteCode_trunc (calls := calls)
    (env := ("%idxprom.le1287", .int 64 (BitVec.ofNat 64 w.toNat)) :: env) (s := s)
    (d := "%28") (v := "%indvars.iv") (wIn := 64) (wOut := 32) (x := iv)
    (lookupName_cons_other _ _ _ (by decide) hiv)]
  simp only [denoteCode_nil]

/-- The string's exit stub: the index's zero extension and the depth's
truncation, to `string_value`. -/
theorem link_stringValueLoopexitEntry {calls : Calls} {K : Stage2NoEventWalkCarry}
    {mem : Mem} {s : State} {w : BitVec 32} {iv : BitVec 64}
    (h : Stage2NoEventWalkInv K mem s) (hpc : s.pc = "string_value.loopexit")
    (h8 : lookupName s.env "%8" = some (.int 32 w))
    (hiv : lookupName s.env "%indvars.iv" = some (.int 64 iv)) :
    Stage2NoEventWalkLink calls K mem s K
      (stage2NoEventWalkNext
        (("%28", .int 32 (BitVec.ofNat 32 (iv.toNat % 2 ^ 32))) ::
          ("%idxprom.le1287", .int 64 (BitVec.ofNat 64 w.toNat)) :: s.env)
        s "string_value") := by
  have hcode := stringValueLoopexit_denote (calls := calls) (env := s.env) (s := s) h8 hiv
  refine ⟨h, ?_, Stage2NoEventWalkInv.mem_congr h rfl⟩
  have hstep := stage2NoEventWalk_step_br (s := s) (f := stage2NoEventBody)
    (by rw [hpc]; exact stringValueLoopexitBlock_find) hcode rfl
  simpa only [stage2NoEventWalkNext, stateAt] using hstep

/-- `string_value`: its eight `phi`s, the lifetime marker, and the end test. -/
def stringValueInstrs : List Instr :=
  [ Instr.phi "%inc.lcssa1130" (Ty.int 64)
      [("LeafBlock", Operand.reg "%inc.peel"), ("string_value.loopexit", Operand.reg "%inc")],
    Instr.phi "%.lcssa1125" (Ty.int 32)
      [("LeafBlock", Operand.reg "%2"), ("string_value.loopexit", Operand.reg "%8")],
    Instr.phi "%idxprom.lcssa1109" (Ty.int 64)
      [("LeafBlock", Operand.reg "%idxprom.peel"),
       ("string_value.loopexit", Operand.reg "%idxprom.le1287")],
    Instr.phi "%frame.0.lcssa1099" (Ty.int 8)
      [("LeafBlock", Operand.reg "%frame.0.ph1402"),
       ("string_value.loopexit", Operand.imm (.int 8 (BitVec.ofNat 8 1)))],
    Instr.phi "%sp.0.lcssa1093.wide" (Ty.int 32)
      [("LeafBlock", Operand.reg "%sp.0.ph1403"),
       ("string_value.loopexit", Operand.reg "%28")],
    Instr.phi "%k.0.lcssa1087" (Ty.int 64)
      [("LeafBlock", Operand.reg "%k.0.ph1404"),
       ("string_value.loopexit", Operand.reg "%k.0")],
    Instr.phi "%terms.0.lcssa1081" (Ty.int 64)
      [("LeafBlock", Operand.reg "%terms.0.ph1407"),
       ("string_value.loopexit", Operand.reg "%terms.0")],
    Instr.phi "%tokens.0.lcssa1075" (Ty.int 64)
      [("LeafBlock", Operand.reg "%tokens.0.ph1408"),
       ("string_value.loopexit", Operand.reg "%tokens.0")],
    Instr.callVoid "llvm.lifetime.start.p0"
      [((Ty.int 64), (Operand.imm (.int 64 (BitVec.ofNat 64 8)))),
       (Ty.ptr, (Operand.reg "%outn205"))],
    Instr.icmp "%cmp207.not" IPred.ult 64 (Operand.reg "%inc.lcssa1130")
      (Operand.reg "%nep") ]

/-- `string_value`, pinned. -/
def stringValueBlock : Block :=
  { name := "string_value", instrs := stringValueInstrs,
    term := Term.condbr (Operand.reg "%cmp207.not") "if.end216" "if.then209" }

theorem stringValueBlock_find :
    stage2NoEventBody.findBlock "string_value" = some stringValueBlock := by
  decide

/-- `string_value`'s leading `phi` run, as specs. -/
def stringValuePhiSpecs : List PhiSpec :=
  [ { dst := "%inc.lcssa1130", ty := Ty.int 64,
      incoming := [("LeafBlock", Operand.reg "%inc.peel"),
        ("string_value.loopexit", Operand.reg "%inc")] },
    { dst := "%.lcssa1125", ty := Ty.int 32,
      incoming := [("LeafBlock", Operand.reg "%2"),
        ("string_value.loopexit", Operand.reg "%8")] },
    { dst := "%idxprom.lcssa1109", ty := Ty.int 64,
      incoming := [("LeafBlock", Operand.reg "%idxprom.peel"),
        ("string_value.loopexit", Operand.reg "%idxprom.le1287")] },
    { dst := "%frame.0.lcssa1099", ty := Ty.int 8,
      incoming := [("LeafBlock", Operand.reg "%frame.0.ph1402"),
        ("string_value.loopexit", Operand.imm (.int 8 (BitVec.ofNat 8 1)))] },
    { dst := "%sp.0.lcssa1093.wide", ty := Ty.int 32,
      incoming := [("LeafBlock", Operand.reg "%sp.0.ph1403"),
        ("string_value.loopexit", Operand.reg "%28")] },
    { dst := "%k.0.lcssa1087", ty := Ty.int 64,
      incoming := [("LeafBlock", Operand.reg "%k.0.ph1404"),
        ("string_value.loopexit", Operand.reg "%k.0")] },
    { dst := "%terms.0.lcssa1081", ty := Ty.int 64,
      incoming := [("LeafBlock", Operand.reg "%terms.0.ph1407"),
        ("string_value.loopexit", Operand.reg "%terms.0")] },
    { dst := "%tokens.0.lcssa1075", ty := Ty.int 64,
      incoming := [("LeafBlock", Operand.reg "%tokens.0.ph1408"),
        ("string_value.loopexit", Operand.reg "%tokens.0")] } ]

theorem stringValuePhi_eq :
    stringValueInstrs = List.map PhiSpec.instr stringValuePhiSpecs ++
      [Instr.callVoid "llvm.lifetime.start.p0"
        [((Ty.int 64), (Operand.imm (.int 64 (BitVec.ofNat 64 8)))),
         (Ty.ptr, (Operand.reg "%outn205"))],
       Instr.icmp "%cmp207.not" IPred.ult 64 (Operand.reg "%inc.lcssa1130")
        (Operand.reg "%nep")] := by
  decide

/-- The string head's `phi` bindings at the string exit's edge. -/
def stringValueVs (inc : BitVec 64) (lc : BitVec 32) (idx : BitVec 64)
    (sp28 : BitVec 32) (k terms tok : BitVec 64) : List (String × Value) :=
  [("%inc.lcssa1130", .int 64 inc),
   ("%.lcssa1125", .int 32 lc),
   ("%idxprom.lcssa1109", .int 64 idx),
   ("%frame.0.lcssa1099", .int 8 (BitVec.ofNat 8 1)),
   ("%sp.0.lcssa1093.wide", .int 32 sp28),
   ("%k.0.lcssa1087", .int 64 k),
   ("%terms.0.lcssa1081", .int 64 terms),
   ("%tokens.0.lcssa1075", .int 64 tok)]

/-- The `string_value` cells after its run: its end test over the base `%nep`. -/
abbrev stringValueCells (env : Env) (inc : BitVec 64) (lc : BitVec 32) (idx : BitVec 64)
    (sp28 : BitVec 32) (k terms tok : BitVec 64) (nep : BitVec 64) : Env :=
  ("%cmp207.not", Value.int 1 (evalICmp .ult inc nep)) ::
    ("%tokens.0.lcssa1075", Value.int 64 tok) ::
    ("%terms.0.lcssa1081", Value.int 64 terms) ::
    ("%k.0.lcssa1087", Value.int 64 k) ::
    ("%sp.0.lcssa1093.wide", Value.int 32 sp28) ::
    ("%frame.0.lcssa1099", Value.int 8 1) ::
    ("%idxprom.lcssa1109", Value.int 64 idx) ::
    ("%.lcssa1125", Value.int 32 lc) ::
    ("%inc.lcssa1130", Value.int 64 inc) :: env

/-- A call that binds nothing, at the lifetime marker's two-argument shape. -/
theorem stage2NoEventWalk_step_callVoid2 (calls : Calls) (env : Env) (s : State)
    (callee : String) (c : BitVec 64) (o2 : Operand) {v2 : Value} {r : CallOutcome}
    (h2 : evalOperand (stateAt env s) o2 = some v2)
    (hc : calls callee [.int 64 c, v2] s.mem s.next = some r) :
    evalInstr calls (stateAt env s)
        (.callVoid callee [(Ty.int 64, .imm (.int 64 c)), (Ty.ptr, o2)]) =
      some (stateAt env { s with mem := r.mem, next := r.next }) := by
  have hargs : evalOperands (stateAt env s)
      [(Ty.int 64, .imm (.int 64 c)), (Ty.ptr, o2)] = some [.int 64 c, v2] := by
    simp only [evalOperands, evalOperand_lit_of, h2]
  have hc' : calls callee [.int 64 c, v2] (stateAt env s).mem (stateAt env s).next
      = some r := hc
  simp only [evalInstr, hargs, hc']
  rfl

/-- The lifetime marker's chain step. -/
theorem denoteCode_callVoid2 (calls : Calls) (env : Env) (s : State)
    (callee : String) (c : BitVec 64) (o2 : Operand) {v2 : Value} {r : CallOutcome}
    (h2 : evalOperand (stateAt env s) o2 = some v2)
    (hc : calls callee [.int 64 c, v2] s.mem s.next = some r) (is : List Instr) :
    denoteCode calls
        (.callVoid callee [(Ty.int 64, .imm (.int 64 c)), (Ty.ptr, o2)] :: is)
        (stateAt env s) =
      denoteCode calls is (stateAt env { s with mem := r.mem, next := r.next }) := by
  rw [denoteCode_cons_of _ _ _ _ _
    (stage2NoEventWalk_step_callVoid2 calls env s callee c o2 h2 hc)]

/-- **The string head at the string exit's edge**: the `phi` run selecting
`string_value.loopexit`'s operands, the lifetime marker, and the end test. -/
theorem stringValue_denote {calls : Calls} (env : Env) (s : State)
    {inc : BitVec 64} {lc : BitVec 32} {idx k terms tok : BitVec 64} {sp28 : BitVec 32}
    {nep : BitVec 64} {o : Nat} {r : CallOutcome}
    (hpre : s.pre = some "string_value.loopexit")
    (hinc : lookupName env "%inc" = some (.int 64 inc))
    (hlc : lookupName env "%8" = some (.int 32 lc))
    (hidx : lookupName env "%idxprom.le1287" = some (.int 64 idx))
    (hsp : lookupName env "%28" = some (.int 32 sp28))
    (hk : lookupName env "%k.0" = some (.int 64 k))
    (htr : lookupName env "%terms.0" = some (.int 64 terms))
    (htok : lookupName env "%tokens.0" = some (.int 64 tok))
    (houtn : lookupName env "%outn205" = some (.ptr o))
    (hnep : lookupName env "%nep" = some (.int 64 nep))
    (hc : calls "llvm.lifetime.start.p0"
      [.int 64 (BitVec.ofNat 64 8), .ptr o] s.mem s.next = some r) :
    denoteCode calls stringValueInstrs (stateAt env s) =
      some (stateAt (stringValueCells env inc lc idx sp28 k terms tok nep)
        { s with mem := r.mem, next := r.next }) := by
  have hsel : PhiSelects (stateAt env s) "string_value.loopexit" stringValuePhiSpecs
      (stringValueVs inc lc idx sp28 k terms tok) := by
    simp only [stringValueVs]
    refine PhiSelects.cons (op := .reg "%inc") (by decide) ?_
      (PhiSelects.cons (op := .reg "%8") (by decide) ?_
        (PhiSelects.cons (op := .reg "%idxprom.le1287") (by decide) ?_
          (PhiSelects.cons (op := .imm (.int 8 (BitVec.ofNat 8 1))) (by decide) ?_
            (PhiSelects.cons (op := .reg "%28") (by decide) ?_
              (PhiSelects.cons (op := .reg "%k.0") (by decide) ?_
                (PhiSelects.cons (op := .reg "%terms.0") (by decide) ?_
                  (PhiSelects.cons (op := .reg "%tokens.0") (by decide) ?_
                    PhiSelects.nil)))))))
    all_goals
      simp only [stateAt, evalOperand, Const.toValue, hinc, hlc, hidx, hsp, hk, htr, htok] <;>
        rfl
  rw [stringValuePhi_eq,
    denoteCode_phiRun (s := stateAt env s) (p := "string_value.loopexit")
      (specs := stringValuePhiSpecs) (vs := stringValueVs inc lc idx sp28 k terms tok)
      (rest := [Instr.callVoid "llvm.lifetime.start.p0"
          [((Ty.int 64), (Operand.imm (.int 64 (BitVec.ofNat 64 8)))),
           (Ty.ptr, (Operand.reg "%outn205"))],
        Instr.icmp "%cmp207.not" IPred.ult 64 (Operand.reg "%inc.lcssa1130")
          (Operand.reg "%nep")])
      (hpre := hpre) (hsel := hsel) (hrest := by decide)]
  rw [stateAt_bindAll_runCells]
  have hOutn : lookupName
      (runCells (stringValueVs inc lc idx sp28 k terms tok) env) "%outn205"
      = some (.ptr o) := by
    simp only [stringValueVs, runCells]
    rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide)]
    exact houtn
  have hNep : lookupName
      (runCells (stringValueVs inc lc idx sp28 k terms tok) env) "%nep"
      = some (.int 64 nep) := by
    simp only [stringValueVs, runCells]
    rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide)]
    exact hnep
  have hIncCell : lookupName
      (runCells (stringValueVs inc lc idx sp28 k terms tok) env) "%inc.lcssa1130"
      = some (.int 64 inc) := by
    simp only [stringValueVs, runCells]
    rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide)]
    simp only [lookupName_cons_self]
  rw [denoteCode_callVoid2 (calls := calls)
    (env := runCells (stringValueVs inc lc idx sp28 k terms tok) env) (s := s)
    (callee := "llvm.lifetime.start.p0") (c := BitVec.ofNat 64 8)
    (o2 := Operand.reg "%outn205") (v2 := .ptr o) (r := r)
    (by simp only [stateAt, evalOperand, hOutn]) hc]
  rw [stage2NoEventWalk_denote_icmp_reg (calls := calls)
    (env := runCells (stringValueVs inc lc idx sp28 k terms tok) env)
    (s := { s with mem := r.mem, next := r.next })
    (d := "%cmp207.not") (a := "%inc.lcssa1130") (b := "%nep") (p := .ult) (w := 64)
    (x := inc) (y := nep) hIncCell hNep (is := [])]
  simp only [denoteCode_nil, stringValueCells, stringValueVs, runCells]
  rfl

/-- **The string end test, taken**: the entry cursor is below the document, to
`if.end216`. -/
theorem link_stringValue_true {calls : Calls} {K : Stage2NoEventWalkCarry}
    {mem : Mem} {s : State} {inc : BitVec 64} {lc : BitVec 32}
    {idx k terms tok nep : BitVec 64} {sp28 : BitVec 32} {o : Nat} {r : CallOutcome}
    (h : Stage2NoEventWalkInv K mem s) (hpc : s.pc = "string_value")
    (hpre : s.pre = some "string_value.loopexit")
    (hinc : lookupName s.env "%inc" = some (.int 64 inc))
    (hlc : lookupName s.env "%8" = some (.int 32 lc))
    (hidx : lookupName s.env "%idxprom.le1287" = some (.int 64 idx))
    (hsp : lookupName s.env "%28" = some (.int 32 sp28))
    (hk : lookupName s.env "%k.0" = some (.int 64 k))
    (htr : lookupName s.env "%terms.0" = some (.int 64 terms))
    (htok : lookupName s.env "%tokens.0" = some (.int 64 tok))
    (houtn : lookupName s.env "%outn205" = some (.ptr o))
    (hnep : lookupName s.env "%nep" = some (.int 64 nep))
    (hc : calls "llvm.lifetime.start.p0"
      [.int 64 (BitVec.ofNat 64 8), .ptr o] s.mem s.next = some r)
    (hmem : r.mem = s.mem) (hnext : r.next = s.next)
    (hy : evalICmp .ult inc nep = 1) :
    Stage2NoEventWalkLink calls K mem s K
      (stage2NoEventWalkNext
        (stringValueCells s.env inc lc idx sp28 k terms tok nep) s "if.end216") := by
  have hblock : stringValueBlock.instrs = stringValueInstrs := by decide
  have hcode : denoteCode calls stringValueBlock.instrs (stateAt s.env s) =
      some (stateAt (stringValueCells s.env inc lc idx sp28 k terms tok nep)
        { s with mem := r.mem, next := r.next }) := by
    rw [hblock]
    exact stringValue_denote (calls := calls) s.env s hpre hinc hlc hidx hsp hk htr htok
      houtn hnep hc
  refine ⟨h, ?_, Stage2NoEventWalkInv.mem_congr h rfl⟩
  have hstep := stage2NoEventWalk_step_condbr_true (f := stage2NoEventBody)
    (by simp only [stateAt]; rw [hpc]; exact stringValueBlock_find) hcode rfl
    (by simp only [stateAt, stringValueCells, lookupName_cons_self, hy])
  simpa only [stage2NoEventWalkNext, stateAt, hmem, hnext] using hstep

/-- **The string end test, not taken**: the entry cursor reached the document's
end, to `if.then209`. -/
theorem link_stringValue_false {calls : Calls} {K : Stage2NoEventWalkCarry}
    {mem : Mem} {s : State} {inc : BitVec 64} {lc : BitVec 32}
    {idx k terms tok nep : BitVec 64} {sp28 : BitVec 32} {o : Nat} {r : CallOutcome}
    (h : Stage2NoEventWalkInv K mem s) (hpc : s.pc = "string_value")
    (hpre : s.pre = some "string_value.loopexit")
    (hinc : lookupName s.env "%inc" = some (.int 64 inc))
    (hlc : lookupName s.env "%8" = some (.int 32 lc))
    (hidx : lookupName s.env "%idxprom.le1287" = some (.int 64 idx))
    (hsp : lookupName s.env "%28" = some (.int 32 sp28))
    (hk : lookupName s.env "%k.0" = some (.int 64 k))
    (htr : lookupName s.env "%terms.0" = some (.int 64 terms))
    (htok : lookupName s.env "%tokens.0" = some (.int 64 tok))
    (houtn : lookupName s.env "%outn205" = some (.ptr o))
    (hnep : lookupName s.env "%nep" = some (.int 64 nep))
    (hc : calls "llvm.lifetime.start.p0"
      [.int 64 (BitVec.ofNat 64 8), .ptr o] s.mem s.next = some r)
    (hmem : r.mem = s.mem) (hnext : r.next = s.next)
    (hy : evalICmp .ult inc nep = 0) :
    Stage2NoEventWalkLink calls K mem s K
      (stage2NoEventWalkNext
        (stringValueCells s.env inc lc idx sp28 k terms tok nep) s "if.then209") := by
  have hblock : stringValueBlock.instrs = stringValueInstrs := by decide
  have hcode : denoteCode calls stringValueBlock.instrs (stateAt s.env s) =
      some (stateAt (stringValueCells s.env inc lc idx sp28 k terms tok nep)
        { s with mem := r.mem, next := r.next }) := by
    rw [hblock]
    exact stringValue_denote (calls := calls) s.env s hpre hinc hlc hidx hsp hk htr htok
      houtn hnep hc
  refine ⟨h, ?_, Stage2NoEventWalkInv.mem_congr h rfl⟩
  have hstep := stage2NoEventWalk_step_condbr_false (f := stage2NoEventBody)
    (by simp only [stateAt]; rw [hpc]; exact stringValueBlock_find) hcode rfl
    (by simp only [stateAt, stringValueCells, lookupName_cons_self, hy])
  simpa only [stage2NoEventWalkNext, stateAt, hmem, hnext] using hstep

/-! #### `scalar.loopexit`: the value's exit stub and head -/

/-- `scalar.loopexit`: `%idxprom.le1291 = zext %8`, `%55 = trunc %indvars.iv`. -/
def scalarLoopexitInstrs : List Instr :=
  [ Instr.zext "%idxprom.le1291" 32 64 (Operand.reg "%8"),
    Instr.trunc "%55" 64 32 (Operand.reg "%indvars.iv") ]

/-- `scalar.loopexit`, pinned. -/
def scalarLoopexitBlock : Block :=
  { name := "scalar.loopexit", instrs := scalarLoopexitInstrs,
    term := Term.br "scalar" }

theorem scalarLoopexitBlock_find :
    stage2NoEventBody.findBlock "scalar.loopexit" = some scalarLoopexitBlock := by
  decide

theorem scalarLoopexitEntry_denote (calls : Calls) (env : Env) (s : State)
    {w : BitVec 32} {iv : BitVec 64}
    (h8 : lookupName env "%8" = some (.int 32 w))
    (hiv : lookupName env "%indvars.iv" = some (.int 64 iv)) :
    denoteCode calls scalarLoopexitInstrs (stateAt env s) =
      some (stateAt
        (("%55", .int 32 (BitVec.ofNat 32 (iv.toNat % 2 ^ 32))) ::
          ("%idxprom.le1291", .int 64 (BitVec.ofNat 64 w.toNat)) :: env) s) := by
  unfold scalarLoopexitInstrs
  rw [denoteCode_zext (calls := calls) (env := env) (s := s) (d := "%idxprom.le1291")
    (v := "%8") (wIn := 32) (wOut := 64) (x := w) h8]
  rw [denoteCode_trunc (calls := calls)
    (env := ("%idxprom.le1291", .int 64 (BitVec.ofNat 64 w.toNat)) :: env) (s := s)
    (d := "%55") (v := "%indvars.iv") (wIn := 64) (wOut := 32) (x := iv)
    (lookupName_cons_other _ _ _ (by decide) hiv)]
  simp only [denoteCode_nil]

/-- The value's exit stub: the index's zero extension and the depth's truncation,
to `scalar`. -/
theorem link_scalarLoopexitEntry {calls : Calls} {K : Stage2NoEventWalkCarry}
    {mem : Mem} {s : State} {w : BitVec 32} {iv : BitVec 64}
    (h : Stage2NoEventWalkInv K mem s) (hpc : s.pc = "scalar.loopexit")
    (h8 : lookupName s.env "%8" = some (.int 32 w))
    (hiv : lookupName s.env "%indvars.iv" = some (.int 64 iv)) :
    Stage2NoEventWalkLink calls K mem s K
      (stage2NoEventWalkNext
        (("%55", .int 32 (BitVec.ofNat 32 (iv.toNat % 2 ^ 32))) ::
          ("%idxprom.le1291", .int 64 (BitVec.ofNat 64 w.toNat)) :: s.env)
        s "scalar") := by
  have hcode := scalarLoopexitEntry_denote (calls := calls) (env := s.env) (s := s) h8 hiv
  refine ⟨h, ?_, Stage2NoEventWalkInv.mem_congr h rfl⟩
  have hstep := stage2NoEventWalk_step_br (s := s) (f := stage2NoEventBody)
    (by rw [hpc]; exact scalarLoopexitBlock_find) hcode rfl
  simpa only [stage2NoEventWalkNext, stateAt] using hstep

/-- `scalar`: its seven `phi`s, the byte's address, and the end test. -/
def scalarInstrs : List Instr :=
  [ Instr.phi "%inc.lcssa" (Ty.int 64)
      [("scalar.loopexit", Operand.reg "%inc"), ("LeafBlock", Operand.reg "%inc.peel"),
       ("LeafBlock1", Operand.reg "%inc.peel"), ("LeafBlock3", Operand.reg "%inc.peel")],
    Instr.phi "%idxprom.lcssa" (Ty.int 64)
      [("scalar.loopexit", Operand.reg "%idxprom.le1291"),
       ("LeafBlock", Operand.reg "%idxprom.peel"),
       ("LeafBlock1", Operand.reg "%idxprom.peel"),
       ("LeafBlock3", Operand.reg "%idxprom.peel")],
    Instr.phi "%.lcssa" (Ty.int 8)
      [("scalar.loopexit", Operand.reg "%7"), ("LeafBlock", Operand.reg "%3"),
       ("LeafBlock1", Operand.reg "%3"), ("LeafBlock3", Operand.reg "%3")],
    Instr.phi "%frame.0.lcssa1097" (Ty.int 8)
      [("scalar.loopexit", Operand.imm (.int 8 (BitVec.ofNat 8 1))),
       ("LeafBlock", Operand.reg "%frame.0.ph1402"),
       ("LeafBlock1", Operand.reg "%frame.0.ph1402"),
       ("LeafBlock3", Operand.reg "%frame.0.ph1402")],
    Instr.phi "%sp.0.lcssa1091.wide" (Ty.int 32)
      [("scalar.loopexit", Operand.reg "%55"),
       ("LeafBlock", Operand.reg "%sp.0.ph1403"),
       ("LeafBlock1", Operand.reg "%sp.0.ph1403"),
       ("LeafBlock3", Operand.reg "%sp.0.ph1403")],
    Instr.phi "%terms.0.lcssa1079" (Ty.int 64)
      [("scalar.loopexit", Operand.reg "%terms.0"),
       ("LeafBlock", Operand.reg "%terms.0.ph1407"),
       ("LeafBlock1", Operand.reg "%terms.0.ph1407"),
       ("LeafBlock3", Operand.reg "%terms.0.ph1407")],
    Instr.phi "%tokens.0.lcssa1073" (Ty.int 64)
      [("scalar.loopexit", Operand.reg "%tokens.0"),
       ("LeafBlock", Operand.reg "%tokens.0.ph1408"),
       ("LeafBlock1", Operand.reg "%tokens.0.ph1408"),
       ("LeafBlock3", Operand.reg "%tokens.0.ph1408")],
    Instr.gep "%arrayidx6.le1046" (Ty.int 8) (Operand.reg "%b")
      (Operand.reg "%idxprom.lcssa"),
    Instr.icmp "%cmp436" IPred.ult 64 (Operand.reg "%inc.lcssa") (Operand.reg "%nep") ]

/-- `scalar`, pinned. -/
def scalarBlock : Block :=
  { name := "scalar", instrs := scalarInstrs,
    term := Term.condbr (Operand.reg "%cmp436") "cond.true" "cond.end" }

theorem scalarBlock_find :
    stage2NoEventBody.findBlock "scalar" = some scalarBlock := by
  decide

/-- `scalar`'s leading `phi` run, as specs. -/
def scalarPhiSpecs : List PhiSpec :=
  [ { dst := "%inc.lcssa", ty := Ty.int 64,
      incoming := [("scalar.loopexit", Operand.reg "%inc"),
        ("LeafBlock", Operand.reg "%inc.peel"),
        ("LeafBlock1", Operand.reg "%inc.peel"),
        ("LeafBlock3", Operand.reg "%inc.peel")] },
    { dst := "%idxprom.lcssa", ty := Ty.int 64,
      incoming := [("scalar.loopexit", Operand.reg "%idxprom.le1291"),
        ("LeafBlock", Operand.reg "%idxprom.peel"),
        ("LeafBlock1", Operand.reg "%idxprom.peel"),
        ("LeafBlock3", Operand.reg "%idxprom.peel")] },
    { dst := "%.lcssa", ty := Ty.int 8,
      incoming := [("scalar.loopexit", Operand.reg "%7"),
        ("LeafBlock", Operand.reg "%3"),
        ("LeafBlock1", Operand.reg "%3"),
        ("LeafBlock3", Operand.reg "%3")] },
    { dst := "%frame.0.lcssa1097", ty := Ty.int 8,
      incoming := [("scalar.loopexit", Operand.imm (.int 8 (BitVec.ofNat 8 1))),
        ("LeafBlock", Operand.reg "%frame.0.ph1402"),
        ("LeafBlock1", Operand.reg "%frame.0.ph1402"),
        ("LeafBlock3", Operand.reg "%frame.0.ph1402")] },
    { dst := "%sp.0.lcssa1091.wide", ty := Ty.int 32,
      incoming := [("scalar.loopexit", Operand.reg "%55"),
        ("LeafBlock", Operand.reg "%sp.0.ph1403"),
        ("LeafBlock1", Operand.reg "%sp.0.ph1403"),
        ("LeafBlock3", Operand.reg "%sp.0.ph1403")] },
    { dst := "%terms.0.lcssa1079", ty := Ty.int 64,
      incoming := [("scalar.loopexit", Operand.reg "%terms.0"),
        ("LeafBlock", Operand.reg "%terms.0.ph1407"),
        ("LeafBlock1", Operand.reg "%terms.0.ph1407"),
        ("LeafBlock3", Operand.reg "%terms.0.ph1407")] },
    { dst := "%tokens.0.lcssa1073", ty := Ty.int 64,
      incoming := [("scalar.loopexit", Operand.reg "%tokens.0"),
        ("LeafBlock", Operand.reg "%tokens.0.ph1408"),
        ("LeafBlock1", Operand.reg "%tokens.0.ph1408"),
        ("LeafBlock3", Operand.reg "%tokens.0.ph1408")] } ]

theorem scalarPhi_eq :
    scalarInstrs = List.map PhiSpec.instr scalarPhiSpecs ++
      [Instr.gep "%arrayidx6.le1046" (Ty.int 8) (Operand.reg "%b")
        (Operand.reg "%idxprom.lcssa"),
       Instr.icmp "%cmp436" IPred.ult 64 (Operand.reg "%inc.lcssa")
        (Operand.reg "%nep")] := by
  decide

/-- The value head's `phi` bindings at the value exit's edge. -/
def scalarVs (inc idx : BitVec 64) (bv : BitVec 8) (sp : BitVec 32)
    (terms tok : BitVec 64) : List (String × Value) :=
  [("%inc.lcssa", .int 64 inc),
   ("%idxprom.lcssa", .int 64 idx),
   ("%.lcssa", .int 8 bv),
   ("%frame.0.lcssa1097", .int 8 (BitVec.ofNat 8 1)),
   ("%sp.0.lcssa1091.wide", .int 32 sp),
   ("%terms.0.lcssa1079", .int 64 terms),
   ("%tokens.0.lcssa1073", .int 64 tok)]

/-- The `scalar` cells after its run: the byte's address and the end test. -/
abbrev scalarCells (env : Env) (inc idx : BitVec 64) (bv : BitVec 8) (sp : BitVec 32)
    (terms tok nep : BitVec 64) (a : Nat) : Env :=
  ("%cmp436", Value.int 1 (evalICmp .ult inc nep)) ::
    ("%arrayidx6.le1046", Value.ptr a) ::
    ("%tokens.0.lcssa1073", Value.int 64 tok) ::
    ("%terms.0.lcssa1079", Value.int 64 terms) ::
    ("%sp.0.lcssa1091.wide", Value.int 32 sp) ::
    ("%frame.0.lcssa1097", Value.int 8 1) ::
    ("%.lcssa", Value.int 8 bv) ::
    ("%idxprom.lcssa", Value.int 64 idx) ::
    ("%inc.lcssa", Value.int 64 inc) :: env

/-- **The value head at the value exit's edge**: the `phi` run selecting
`scalar.loopexit`'s operands, the entry byte's address, and the end test. -/
theorem scalar_denote {calls : Calls} (env : Env) (s : State)
    {inc idx : BitVec 64} {bv : BitVec 8} {sp : BitVec 32}
    {terms tok nep : BitVec 64} {b : Nat}
    (hpre : s.pre = some "scalar.loopexit")
    (hinc : lookupName env "%inc" = some (.int 64 inc))
    (hidx : lookupName env "%idxprom.le1291" = some (.int 64 idx))
    (hbv : lookupName env "%7" = some (.int 8 bv))
    (hsp : lookupName env "%55" = some (.int 32 sp))
    (htr : lookupName env "%terms.0" = some (.int 64 terms))
    (htok : lookupName env "%tokens.0" = some (.int 64 tok))
    (hb : lookupName env "%b" = some (.ptr b))
    (hnep : lookupName env "%nep" = some (.int 64 nep))
    (hpos : (idx.signExtend 64).toNat < 2 ^ 63) :
    denoteCode calls scalarInstrs (stateAt env s) =
      some (stateAt (scalarCells env inc idx bv sp terms tok nep
        (b + (idx.signExtend 64).toNat)) s) := by
  have hsel : PhiSelects (stateAt env s) "scalar.loopexit" scalarPhiSpecs
      (scalarVs inc idx bv sp terms tok) := by
    simp only [scalarVs]
    refine PhiSelects.cons (op := .reg "%inc") (by decide) ?_
      (PhiSelects.cons (op := .reg "%idxprom.le1291") (by decide) ?_
        (PhiSelects.cons (op := .reg "%7") (by decide) ?_
          (PhiSelects.cons (op := .imm (.int 8 (BitVec.ofNat 8 1))) (by decide) ?_
            (PhiSelects.cons (op := .reg "%55") (by decide) ?_
              (PhiSelects.cons (op := .reg "%terms.0") (by decide) ?_
                (PhiSelects.cons (op := .reg "%tokens.0") (by decide) ?_
                  PhiSelects.nil))))))
    all_goals
      simp only [stateAt, evalOperand, Const.toValue, hinc, hidx, hbv, hsp, htr, htok] <;>
        rfl
  rw [scalarPhi_eq,
    denoteCode_phiRun (s := stateAt env s) (p := "scalar.loopexit")
      (specs := scalarPhiSpecs) (vs := scalarVs inc idx bv sp terms tok)
      (rest := [Instr.gep "%arrayidx6.le1046" (Ty.int 8) (Operand.reg "%b")
          (Operand.reg "%idxprom.lcssa"),
        Instr.icmp "%cmp436" IPred.ult 64 (Operand.reg "%inc.lcssa")
          (Operand.reg "%nep")])
      (hpre := hpre) (hsel := hsel) (hrest := by decide)]
  rw [stateAt_bindAll_runCells]
  have hB : lookupName (runCells (scalarVs inc idx bv sp terms tok) env) "%b"
      = some (.ptr b) := by
    simp only [scalarVs, runCells]
    rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide)]
    exact hb
  have hNep : lookupName (runCells (scalarVs inc idx bv sp terms tok) env) "%nep"
      = some (.int 64 nep) := by
    simp only [scalarVs, runCells]
    rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide)]
    exact hnep
  have hIdxCell : lookupName (runCells (scalarVs inc idx bv sp terms tok) env)
      "%idxprom.lcssa" = some (.int 64 idx) := by
    simp only [scalarVs, runCells]
    rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide)]
    simp only [lookupName_cons_self]
  have hIncCell : lookupName (runCells (scalarVs inc idx bv sp terms tok) env)
      "%inc.lcssa" = some (.int 64 inc) := by
    simp only [scalarVs, runCells]
    rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide)]
    simp only [lookupName_cons_self]
  rw [denoteCode_gep8_reg (calls := calls)
    (env := runCells (scalarVs inc idx bv sp terms tok) env) (s := s)
    (d := "%arrayidx6.le1046") (base := "%b") (off := "%idxprom.lcssa")
    (a := b) (idx := idx) hB hIdxCell hpos]
  rw [stage2NoEventWalk_denote_icmp_reg (calls := calls)
    (env := ("%arrayidx6.le1046", .ptr (b + (idx.signExtend 64).toNat)) ::
      runCells (scalarVs inc idx bv sp terms tok) env) (s := s)
    (d := "%cmp436") (a := "%inc.lcssa") (b := "%nep") (p := .ult) (w := 64)
    (x := inc) (y := nep)
    (lookupName_cons_other _ _ _ (by decide) hIncCell)
    (lookupName_cons_other _ _ _ (by decide) hNep) (is := [])]
  simp only [denoteCode_nil, scalarCells, scalarVs, runCells]
  rfl

/-- **The value head's end test, taken**: the cursor is below the document, to
`cond.true`. -/
theorem link_scalar_true {calls : Calls} {K : Stage2NoEventWalkCarry}
    {mem : Mem} {s : State} {inc idx : BitVec 64} {bv : BitVec 8} {sp : BitVec 32}
    {terms tok nep : BitVec 64} {b : Nat}
    (h : Stage2NoEventWalkInv K mem s) (hpc : s.pc = "scalar")
    (hpre : s.pre = some "scalar.loopexit")
    (hinc : lookupName s.env "%inc" = some (.int 64 inc))
    (hidx : lookupName s.env "%idxprom.le1291" = some (.int 64 idx))
    (hbv : lookupName s.env "%7" = some (.int 8 bv))
    (hsp : lookupName s.env "%55" = some (.int 32 sp))
    (htr : lookupName s.env "%terms.0" = some (.int 64 terms))
    (htok : lookupName s.env "%tokens.0" = some (.int 64 tok))
    (hb : lookupName s.env "%b" = some (.ptr b))
    (hnep : lookupName s.env "%nep" = some (.int 64 nep))
    (hpos : (idx.signExtend 64).toNat < 2 ^ 63)
    (hy : evalICmp .ult inc nep = 1) :
    Stage2NoEventWalkLink calls K mem s K
      (stage2NoEventWalkNext
        (scalarCells s.env inc idx bv sp terms tok nep (b + (idx.signExtend 64).toNat))
        s "cond.true") := by
  have hblock : scalarBlock.instrs = scalarInstrs := by decide
  have hcode : denoteCode calls scalarBlock.instrs (stateAt s.env s) =
      some (stateAt
        (scalarCells s.env inc idx bv sp terms tok nep (b + (idx.signExtend 64).toNat))
        s) := by
    rw [hblock]
    exact scalar_denote (calls := calls) s.env s hpre hinc hidx hbv hsp htr htok hb hnep hpos
  exact stage2NoEventWalkLink_condbr_true
    (env' := scalarCells s.env inc idx bv sp terms tok nep (b + (idx.signExtend 64).toNat))
    h (by rw [hpc]; exact scalarBlock_find) hcode rfl
    (by simp only [scalarCells, lookupName_cons_self, hy])

/-- **The value head's end test, not taken**: the cursor reached the document's
end, to `cond.end`. -/
theorem link_scalar_false {calls : Calls} {K : Stage2NoEventWalkCarry}
    {mem : Mem} {s : State} {inc idx : BitVec 64} {bv : BitVec 8} {sp : BitVec 32}
    {terms tok nep : BitVec 64} {b : Nat}
    (h : Stage2NoEventWalkInv K mem s) (hpc : s.pc = "scalar")
    (hpre : s.pre = some "scalar.loopexit")
    (hinc : lookupName s.env "%inc" = some (.int 64 inc))
    (hidx : lookupName s.env "%idxprom.le1291" = some (.int 64 idx))
    (hbv : lookupName s.env "%7" = some (.int 8 bv))
    (hsp : lookupName s.env "%55" = some (.int 32 sp))
    (htr : lookupName s.env "%terms.0" = some (.int 64 terms))
    (htok : lookupName s.env "%tokens.0" = some (.int 64 tok))
    (hb : lookupName s.env "%b" = some (.ptr b))
    (hnep : lookupName s.env "%nep" = some (.int 64 nep))
    (hpos : (idx.signExtend 64).toNat < 2 ^ 63)
    (hy : evalICmp .ult inc nep = 0) :
    Stage2NoEventWalkLink calls K mem s K
      (stage2NoEventWalkNext
        (scalarCells s.env inc idx bv sp terms tok nep (b + (idx.signExtend 64).toNat))
        s "cond.end") := by
  have hblock : scalarBlock.instrs = scalarInstrs := by decide
  have hcode : denoteCode calls scalarBlock.instrs (stateAt s.env s) =
      some (stateAt
        (scalarCells s.env inc idx bv sp terms tok nep (b + (idx.signExtend 64).toNat))
        s) := by
    rw [hblock]
    exact scalar_denote (calls := calls) s.env s hpre hinc hidx hbv hsp htr htok hb hnep hpos
  exact stage2NoEventWalkLink_condbr_false
    (env' := scalarCells s.env inc idx bv sp terms tok nep (b + (idx.signExtend 64).toNat))
    h (by rw [hpc]; exact scalarBlock_find) hcode rfl
    (by simp only [scalarCells, lookupName_cons_self, hy])

/-- `cond.true`: the cursor's lane word, zero-extended. -/
def condTrueInstrs : List Instr :=
  [ Instr.gep "%arrayidx438" (Ty.int 32) (Operand.reg "%ep") (Operand.reg "%inc.lcssa"),
    Instr.load "%56" (Ty.int 32) (Operand.reg "%arrayidx438"),
    Instr.zext "%conv439" 32 64 (Operand.reg "%56") ]

/-- `cond.true`, pinned. -/
def condTrueBlock : Block :=
  { name := "cond.true", instrs := condTrueInstrs, term := Term.br "cond.end" }

theorem condTrueBlock_find :
    stage2NoEventBody.findBlock "cond.true" = some condTrueBlock := by
  decide

/-- The `cond.true` cells: the lane's address, its word, and its extension. -/
abbrev condTrueCells (env : Env) (a : Nat) (bs : List UInt8) : Env :=
  ("%conv439", Value.int 64
      (BitVec.ofNat 64 (BitVec.ofNat 32 (bytesToNat bs)).toNat)) ::
    ("%56", Value.int 32 (BitVec.ofNat 32 (bytesToNat bs))) ::
    ("%arrayidx438", Value.ptr a) :: env

theorem condTrue_denote (calls : Calls) (env : Env) (s : State)
    {ep : Nat} {inc : BitVec 64} {bs : List UInt8}
    (hep : lookupName env "%ep" = some (.ptr ep))
    (hinc : lookupName env "%inc.lcssa" = some (.int 64 inc))
    (hpos : (inc.signExtend 64).toNat < 2 ^ 63)
    (hload : readBytes s.mem (ep + (inc.signExtend 64).toNat * 4) 4 = some bs) :
    denoteCode calls condTrueInstrs (stateAt env s) =
      some (stateAt (condTrueCells env (ep + (inc.signExtend 64).toNat * 4) bs) s) := by
  unfold condTrueInstrs
  rw [stage2NoEventWalk_denote_gep32 (calls := calls) (env := env) (s := s)
    (d := "%arrayidx438") (base := "%ep") (off := "%inc.lcssa")
    (a := ep) (o := inc) hep hinc hpos]
  rw [stage2NoEventWalk_denote_load_int (calls := calls)
    (env := ("%arrayidx438", .ptr (ep + (inc.signExtend 64).toNat * 4)) :: env) (s := s)
    (d := "%56") (p := "%arrayidx438") (a := ep + (inc.signExtend 64).toNat * 4)
    (w := 32) (bs := bs) (hw := by decide)
    (by simp only [lookupName_cons_self]) (by simpa using hload)]
  rw [denoteCode_zext (calls := calls) (env := _) (s := s) (d := "%conv439")
    (v := "%56") (wIn := 32) (wOut := 64)
    (x := BitVec.ofNat 32 (bytesToNat bs)) (by simp only [lookupName_cons_self])]
  simp only [denoteCode_nil]

/-- One step of the taken `cond.true` arm: the lane load, to `cond.end`. -/
theorem link_condTrue {calls : Calls} {K : Stage2NoEventWalkCarry}
    {mem : Mem} {s : State} {ep : Nat} {inc : BitVec 64} {bs : List UInt8}
    (h : Stage2NoEventWalkInv K mem s) (hpc : s.pc = "cond.true")
    (hep : lookupName s.env "%ep" = some (.ptr ep))
    (hinc : lookupName s.env "%inc.lcssa" = some (.int 64 inc))
    (hpos : (inc.signExtend 64).toNat < 2 ^ 63)
    (hload : readBytes s.mem (ep + (inc.signExtend 64).toNat * 4) 4 = some bs) :
    Stage2NoEventWalkLink calls K mem s K
      (stage2NoEventWalkNext
        (condTrueCells s.env (ep + (inc.signExtend 64).toNat * 4) bs) s "cond.end") := by
  have hcode := condTrue_denote (calls := calls) (env := s.env) (s := s)
    hep hinc hpos hload
  refine ⟨h, ?_, Stage2NoEventWalkInv.mem_congr h rfl⟩
  have hstep := stage2NoEventWalk_step_br (s := s) (f := stage2NoEventBody)
    (by rw [hpc]; exact condTrueBlock_find) hcode rfl
  simpa only [stage2NoEventWalkNext, stateAt] using hstep

/-- `cond.end`: the conditional word's `phi` and the extent test. -/
def condEndInstrs : List Instr :=
  [ Instr.phi "%cond" (Ty.int 64)
      [("cond.true", Operand.reg "%conv439"), ("scalar", Operand.reg "%n")],
    Instr.icmp "%cmp443" IPred.ugt 64 (Operand.reg "%cond")
      (Operand.reg "%idxprom.lcssa") ]

/-- `cond.end`, pinned. -/
def condEndBlock : Block :=
  { name := "cond.end", instrs := condEndInstrs,
    term := Term.condbr (Operand.reg "%cmp443") "land.lhs.true" "if.end457" }

theorem condEndBlock_find :
    stage2NoEventBody.findBlock "cond.end" = some condEndBlock := by
  decide

/-- `cond.end`'s leading `phi`, as a spec. -/
def condEndPhiSpecs : List PhiSpec :=
  [ { dst := "%cond", ty := Ty.int 64,
      incoming := [("cond.true", Operand.reg "%conv439"),
        ("scalar", Operand.reg "%n")] } ]

theorem condEndPhi_eq :
    condEndInstrs = List.map PhiSpec.instr condEndPhiSpecs ++
      [Instr.icmp "%cmp443" IPred.ugt 64 (Operand.reg "%cond")
        (Operand.reg "%idxprom.lcssa")] := by
  decide

/-- The `cond.end` cells: the conditional word and the extent test. -/
abbrev condEndCells (env : Env) (c idx : BitVec 64) : Env :=
  ("%cmp443", Value.int 1 (evalICmp .ugt c idx)) ::
    ("%cond", Value.int 64 c) :: env

theorem condEnd_denote_fromScalar {calls : Calls} (env : Env) (s : State)
    {c idx : BitVec 64}
    (hpre : s.pre = some "scalar")
    (hn : lookupName env "%n" = some (.int 64 c))
    (hidx : lookupName env "%idxprom.lcssa" = some (.int 64 idx)) :
    denoteCode calls condEndInstrs (stateAt env s) =
      some (stateAt (condEndCells env c idx) s) := by
  have hsel : PhiSelects (stateAt env s) "scalar" condEndPhiSpecs
      [("%cond", .int 64 c)] := by
    refine PhiSelects.cons (op := .reg "%n") (by decide) ?_ PhiSelects.nil
    simp only [stateAt, evalOperand, hn]
  rw [condEndPhi_eq,
    denoteCode_phiRun (s := stateAt env s) (p := "scalar") (specs := condEndPhiSpecs)
      (vs := [("%cond", .int 64 c)])
      (rest := [Instr.icmp "%cmp443" IPred.ugt 64 (Operand.reg "%cond")
        (Operand.reg "%idxprom.lcssa")])
      (hpre := hpre) (hsel := hsel) (hrest := by decide)]
  rw [stateAt_bindAll_runCells]
  simp only [runCells]
  rw [stage2NoEventWalk_denote_icmp_reg (calls := calls)
    (env := ("%cond", .int 64 c) :: env) (s := s)
    (d := "%cmp443") (a := "%cond") (b := "%idxprom.lcssa") (p := .ugt) (w := 64)
    (x := c) (y := idx) (by simp only [lookupName_cons_self])
    (lookupName_cons_other _ _ _ (by decide) hidx) (is := [])]
  simp only [denoteCode_nil, condEndCells]

theorem condEnd_denote_fromCondTrue {calls : Calls} (env : Env) (s : State)
    {c idx : BitVec 64}
    (hpre : s.pre = some "cond.true")
    (hconv : lookupName env "%conv439" = some (.int 64 c))
    (hidx : lookupName env "%idxprom.lcssa" = some (.int 64 idx)) :
    denoteCode calls condEndInstrs (stateAt env s) =
      some (stateAt (condEndCells env c idx) s) := by
  have hsel : PhiSelects (stateAt env s) "cond.true" condEndPhiSpecs
      [("%cond", .int 64 c)] := by
    refine PhiSelects.cons (op := .reg "%conv439") (by decide) ?_ PhiSelects.nil
    simp only [stateAt, evalOperand, hconv]
  rw [condEndPhi_eq,
    denoteCode_phiRun (s := stateAt env s) (p := "cond.true") (specs := condEndPhiSpecs)
      (vs := [("%cond", .int 64 c)])
      (rest := [Instr.icmp "%cmp443" IPred.ugt 64 (Operand.reg "%cond")
        (Operand.reg "%idxprom.lcssa")])
      (hpre := hpre) (hsel := hsel) (hrest := by decide)]
  rw [stateAt_bindAll_runCells]
  simp only [runCells]
  rw [stage2NoEventWalk_denote_icmp_reg (calls := calls)
    (env := ("%cond", .int 64 c) :: env) (s := s)
    (d := "%cmp443") (a := "%cond") (b := "%idxprom.lcssa") (p := .ugt) (w := 64)
    (x := c) (y := idx) (by simp only [lookupName_cons_self])
    (lookupName_cons_other _ _ _ (by decide) hidx) (is := [])]
  simp only [denoteCode_nil, condEndCells]

/-- The `cond.end` extent test, taken: the word is above the entry's index, to
`land.lhs.true`. -/
theorem link_condEnd_true {calls : Calls} {K : Stage2NoEventWalkCarry}
    {mem : Mem} {s : State} {c idx : BitVec 64}
    (h : Stage2NoEventWalkInv K mem s) (hpc : s.pc = "cond.end")
    (hpre : s.pre = some "scalar") (hn : lookupName s.env "%n" = some (.int 64 c))
    (hidx : lookupName s.env "%idxprom.lcssa" = some (.int 64 idx))
    (hy : evalICmp .ugt c idx = 1) :
    Stage2NoEventWalkLink calls K mem s K
      (stage2NoEventWalkNext (condEndCells s.env c idx) s "land.lhs.true") := by
  have hcode := condEnd_denote_fromScalar (calls := calls) s.env s hpre hn hidx
  exact stage2NoEventWalkLink_condbr_true (env' := condEndCells s.env c idx)
    h (by rw [hpc]; exact condEndBlock_find) hcode rfl
    (by simp only [condEndCells, lookupName_cons_self, hy])

/-- The `cond.end` extent test, taken, from the taken `cond.true` arm. -/
theorem link_condEnd_fromCondTrue_true {calls : Calls} {K : Stage2NoEventWalkCarry}
    {mem : Mem} {s : State} {c idx : BitVec 64}
    (h : Stage2NoEventWalkInv K mem s) (hpc : s.pc = "cond.end")
    (hpre : s.pre = some "cond.true")
    (hconv : lookupName s.env "%conv439" = some (.int 64 c))
    (hidx : lookupName s.env "%idxprom.lcssa" = some (.int 64 idx))
    (hy : evalICmp .ugt c idx = 1) :
    Stage2NoEventWalkLink calls K mem s K
      (stage2NoEventWalkNext (condEndCells s.env c idx) s "land.lhs.true") := by
  have hcode := condEnd_denote_fromCondTrue (calls := calls) s.env s hpre hconv hidx
  exact stage2NoEventWalkLink_condbr_true (env' := condEndCells s.env c idx)
    h (by rw [hpc]; exact condEndBlock_find) hcode rfl
    (by simp only [condEndCells, lookupName_cons_self, hy])

/-- The `cond.end` extent test, not taken, from the untaken `scalar` arm. -/
theorem link_condEnd_false {calls : Calls} {K : Stage2NoEventWalkCarry}
    {mem : Mem} {s : State} {c idx : BitVec 64}
    (h : Stage2NoEventWalkInv K mem s) (hpc : s.pc = "cond.end")
    (hpre : s.pre = some "scalar") (hn : lookupName s.env "%n" = some (.int 64 c))
    (hidx : lookupName s.env "%idxprom.lcssa" = some (.int 64 idx))
    (hy : evalICmp .ugt c idx = 0) :
    Stage2NoEventWalkLink calls K mem s K
      (stage2NoEventWalkNext (condEndCells s.env c idx) s "if.end457") := by
  have hcode := condEnd_denote_fromScalar (calls := calls) s.env s hpre hn hidx
  exact stage2NoEventWalkLink_condbr_false (env' := condEndCells s.env c idx)
    h (by rw [hpc]; exact condEndBlock_find) hcode rfl
    (by simp only [condEndCells, lookupName_cons_self, hy])

/-- The `cond.end` extent test, not taken, from the taken `cond.true` arm. -/
theorem link_condEnd_fromCondTrue_false {calls : Calls} {K : Stage2NoEventWalkCarry}
    {mem : Mem} {s : State} {c idx : BitVec 64}
    (h : Stage2NoEventWalkInv K mem s) (hpc : s.pc = "cond.end")
    (hpre : s.pre = some "cond.true")
    (hconv : lookupName s.env "%conv439" = some (.int 64 c))
    (hidx : lookupName s.env "%idxprom.lcssa" = some (.int 64 idx))
    (hy : evalICmp .ugt c idx = 0) :
    Stage2NoEventWalkLink calls K mem s K
      (stage2NoEventWalkNext (condEndCells s.env c idx) s "if.end457") := by
  have hcode := condEnd_denote_fromCondTrue (calls := calls) s.env s hpre hconv hidx
  exact stage2NoEventWalkLink_condbr_false (env' := condEndCells s.env c idx)
    h (by rw [hpc]; exact condEndBlock_find) hcode rfl
    (by simp only [condEndCells, lookupName_cons_self, hy])

/-! ### `if.end`: the pair's counts and the dispatch handoff

`if.end` closes a completed key/value pair: its six `phi`s select the pair's
bytes, cursor, counts and entry index from whichever edge reached it, then four
adds write the next iteration's `%tokens.0`, `%terms.0`, `%indvars.iv` and
`%inc`, and it branches to `NodeBlock15`.  This is `%indvars.iv`'s producer — the
binding the exit rows at `NodeBlock15` take as a hypothesis.

The edge's operands are hypotheses, one set per predecessor: the block reads
`%47`, `%46`, `%indvars.iv`, `%inc`, `%terms.0`, `%tokens.0` from `if.end327`
and `%6`, `%5`, `%1`, `%inc.peel`, `%terms.0.ph1407`, `%tokens.0.ph1408` from
`if.end327.peel`.  `if.end327`'s own block is not modelled here, so those values
enter as named lookups at the state's environment and nothing is invented.  The
producer's conclusions are the `NodeBlock15` bindings themselves: `%7`, `%8`,
`%indvars.iv`, `%k.0`, `%terms.0`, `%tokens.0` and `%inc`, each at the value the
selected operand and the add produce. -/

/-- `if.end`'s six-`phi` run, as specs. -/
def ifEndPhiSpecs : List PhiSpec :=
  [ { dst := "%7", ty := Ty.int 8,
      incoming := [("if.end327", Operand.reg "%47"),
        ("if.end327.peel", Operand.reg "%6")] },
    { dst := "%8", ty := Ty.int 32,
      incoming := [("if.end327", Operand.reg "%46"),
        ("if.end327.peel", Operand.reg "%5")] },
    { dst := "%indvars.iv.in", ty := Ty.int 64,
      incoming := [("if.end327", Operand.reg "%indvars.iv"),
        ("if.end327.peel", Operand.reg "%1")] },
    { dst := "%k.0", ty := Ty.int 64,
      incoming := [("if.end327", Operand.reg "%inc"),
        ("if.end327.peel", Operand.reg "%inc.peel")] },
    { dst := "%terms.0.in", ty := Ty.int 64,
      incoming := [("if.end327", Operand.reg "%terms.0"),
        ("if.end327.peel", Operand.reg "%terms.0.ph1407")] },
    { dst := "%tokens.0.in", ty := Ty.int 64,
      incoming := [("if.end327", Operand.reg "%tokens.0"),
        ("if.end327.peel", Operand.reg "%tokens.0.ph1408")] } ]

/-- `if.end`'s leading `phi` run. -/
def ifEndPhiInstrs : List Instr := List.map PhiSpec.instr ifEndPhiSpecs

theorem ifEndPhi_eq : ifEndPhiInstrs = ifEndPhiSpecs.map PhiSpec.instr := rfl

/-- `if.end`'s four adds, in the order the block writes them. -/
def ifEndRest : List Instr :=
  [ Instr.binop "%tokens.0" BinOp.add 64 (Operand.reg "%tokens.0.in")
      (Operand.imm (.int 64 (BitVec.ofNat 64 1))),
    Instr.binop "%terms.0" BinOp.add 64 (Operand.reg "%terms.0.in")
      (Operand.imm (.int 64 (BitVec.ofNat 64 3))),
    Instr.binop "%indvars.iv" BinOp.add 64 (Operand.reg "%indvars.iv.in")
      (Operand.imm (.int 64 (BitVec.ofNat 64 1))),
    Instr.binop "%inc" BinOp.add 64 (Operand.reg "%k.0")
      (Operand.imm (.int 64 (BitVec.ofNat 64 1))) ]

/-- `if.end`, pinned. -/
def ifEndInstrs : List Instr := ifEndPhiInstrs ++ ifEndRest

theorem ifEnd_split : ifEndInstrs = ifEndPhiInstrs ++ ifEndRest := rfl

/-- `if.end`, pinned. -/
def ifEndBlock : Block :=
  { name := "if.end", instrs := ifEndInstrs, term := Term.br "NodeBlock15" }

theorem ifEndBlock_find :
    stage2NoEventBody.findBlock "if.end" = some ifEndBlock := by
  decide

/-- `if.end`'s `phi` cells, last written outermost. -/
def ifEndPhiCells (v7 : BitVec 8) (v8 : BitVec 32) (ivIn k0 termsIn toksIn : BitVec 64) :
    List (String × Value) :=
  [("%tokens.0.in", .int 64 toksIn), ("%terms.0.in", .int 64 termsIn),
   ("%k.0", .int 64 k0), ("%indvars.iv.in", .int 64 ivIn),
   ("%8", .int 32 v8), ("%7", .int 8 v7)]

/-- `if.end`'s add cells, last written outermost. -/
def ifEndTailCells (v7 : BitVec 8) (v8 : BitVec 32) (ivIn k0 termsIn toksIn : BitVec 64) :
    List (String × Value) :=
  [("%inc", .int 64 (k0 + BitVec.ofNat 64 1)),
   ("%indvars.iv", .int 64 (ivIn + BitVec.ofNat 64 1)),
   ("%terms.0", .int 64 (termsIn + BitVec.ofNat 64 3)),
   ("%tokens.0", .int 64 (toksIn + BitVec.ofNat 64 1))]

/-- The composed cell list `if.end`'s adds and its edge bind. -/
def ifEndAllCells (v7 : BitVec 8) (v8 : BitVec 32) (ivIn k0 termsIn toksIn : BitVec 64) :
    List (String × Value) :=
  ifEndTailCells v7 v8 ivIn k0 termsIn toksIn ++ ifEndPhiCells v7 v8 ivIn k0 termsIn toksIn

/-- `if.end`'s `phi` run at the `if.end327` edge. -/
theorem ifEndPhi_denote_fromEnd327 (calls : Calls) (env : Env) (s : State)
    {v7 : BitVec 8} {v8 : BitVec 32} {ivIn k0 termsIn toksIn : BitVec 64}
    (hpre : s.pre = some "if.end327")
    (h47 : lookupName env "%47" = some (.int 8 v7))
    (h46 : lookupName env "%46" = some (.int 32 v8))
    (hiv : lookupName env "%indvars.iv" = some (.int 64 ivIn))
    (hinc : lookupName env "%inc" = some (.int 64 k0))
    (htr : lookupName env "%terms.0" = some (.int 64 termsIn))
    (htok : lookupName env "%tokens.0" = some (.int 64 toksIn)) :
    denoteCode calls ifEndPhiInstrs (stateAt env s) =
      some (stateAt (cells (ifEndPhiCells v7 v8 ivIn k0 termsIn toksIn) env) s) := by
  have hsel : PhiSelects (stateAt env s) "if.end327" ifEndPhiSpecs
      [("%7", .int 8 v7), ("%8", .int 32 v8), ("%indvars.iv.in", .int 64 ivIn),
       ("%k.0", .int 64 k0), ("%terms.0.in", .int 64 termsIn),
       ("%tokens.0.in", .int 64 toksIn)] := by
    refine PhiSelects.cons (op := .reg "%47") (by decide) ?_
      (PhiSelects.cons (op := .reg "%46") (by decide) ?_
        (PhiSelects.cons (op := .reg "%indvars.iv") (by decide) ?_
          (PhiSelects.cons (op := .reg "%inc") (by decide) ?_
            (PhiSelects.cons (op := .reg "%terms.0") (by decide) ?_
              (PhiSelects.cons (op := .reg "%tokens.0") (by decide) ?_ PhiSelects.nil)))))
    all_goals simp only [stateAt, evalOperand, h47, h46, hiv, hinc, htr, htok]
  rw [ifEndPhi_eq, ← List.append_nil (List.map PhiSpec.instr ifEndPhiSpecs),
    denoteCode_phiRun (s := stateAt env s) (p := "if.end327")
      (specs := ifEndPhiSpecs) (rest := [])
      (hpre := hpre) (hsel := hsel) (hrest := rfl)]
  simp only [State.bindAll, State.bind, ifEndPhiCells, cells]
  rfl

/-- `if.end`'s `phi` run at the `if.end327.peel` edge. -/
theorem ifEndPhi_denote_fromEnd327Peel (calls : Calls) (env : Env) (s : State)
    {v7 : BitVec 8} {v8 : BitVec 32} {ivIn k0 termsIn toksIn : BitVec 64}
    (hpre : s.pre = some "if.end327.peel")
    (h6 : lookupName env "%6" = some (.int 8 v7))
    (h5 : lookupName env "%5" = some (.int 32 v8))
    (h1 : lookupName env "%1" = some (.int 64 ivIn))
    (hinc : lookupName env "%inc.peel" = some (.int 64 k0))
    (htr : lookupName env "%terms.0.ph1407" = some (.int 64 termsIn))
    (htok : lookupName env "%tokens.0.ph1408" = some (.int 64 toksIn)) :
    denoteCode calls ifEndPhiInstrs (stateAt env s) =
      some (stateAt (cells (ifEndPhiCells v7 v8 ivIn k0 termsIn toksIn) env) s) := by
  have hsel : PhiSelects (stateAt env s) "if.end327.peel" ifEndPhiSpecs
      [("%7", .int 8 v7), ("%8", .int 32 v8), ("%indvars.iv.in", .int 64 ivIn),
       ("%k.0", .int 64 k0), ("%terms.0.in", .int 64 termsIn),
       ("%tokens.0.in", .int 64 toksIn)] := by
    refine PhiSelects.cons (op := .reg "%6") (by decide) ?_
      (PhiSelects.cons (op := .reg "%5") (by decide) ?_
        (PhiSelects.cons (op := .reg "%1") (by decide) ?_
          (PhiSelects.cons (op := .reg "%inc.peel") (by decide) ?_
            (PhiSelects.cons (op := .reg "%terms.0.ph1407") (by decide) ?_
              (PhiSelects.cons (op := .reg "%tokens.0.ph1408") (by decide) ?_
                PhiSelects.nil)))))
    all_goals simp only [stateAt, evalOperand, h6, h5, h1, hinc, htr, htok]
  rw [ifEndPhi_eq, ← List.append_nil (List.map PhiSpec.instr ifEndPhiSpecs),
    denoteCode_phiRun (s := stateAt env s) (p := "if.end327.peel")
      (specs := ifEndPhiSpecs) (rest := [])
      (hpre := hpre) (hsel := hsel) (hrest := rfl)]
  simp only [State.bindAll, State.bind, ifEndPhiCells, cells]
  rfl

/-- `if.end`'s four adds, at the `phi` run's cells.  Edge-independent: the run
has already selected the values. -/
theorem ifEndTail_denote (calls : Calls) (env : Env) (s : State)
    {v7 : BitVec 8} {v8 : BitVec 32} {ivIn k0 termsIn toksIn : BitVec 64} :
    denoteCode calls ifEndRest
        (stateAt (cells (ifEndPhiCells v7 v8 ivIn k0 termsIn toksIn) env) s) =
      some (stateAt (cells (ifEndAllCells v7 v8 ivIn k0 termsIn toksIn) env) s) := by
  rw [ifEndRest]
  rw [stage2NoEventWalk_denote_add_imm_w (calls := calls)
    (env := cells (ifEndPhiCells v7 v8 ivIn k0 termsIn toksIn) env) (s := s)
    (d := "%tokens.0") (a := "%tokens.0.in") (w := 64) (x := toksIn)
    (c := BitVec.ofNat 64 1)
    (lookupName_cells_of_some (cs := ifEndPhiCells v7 v8 ivIn k0 termsIn toksIn)
      (n := "%tokens.0.in") (env := env) (by rw [ifEndPhiCells]; cells_lk))]
  rw [stage2NoEventWalk_denote_add_imm_w (calls := calls) (env := _) (s := s)
    (d := "%terms.0") (a := "%terms.0.in") (w := 64) (x := termsIn)
    (c := BitVec.ofNat 64 3)
    (by rw [lookupName_cons_ne _ _ (by decide),
      lookupName_cells_of_some (cs := ifEndPhiCells v7 v8 ivIn k0 termsIn toksIn)
        (n := "%terms.0.in") (env := env) (by rw [ifEndPhiCells]; cells_lk)])]
  rw [stage2NoEventWalk_denote_add_imm_w (calls := calls) (env := _) (s := s)
    (d := "%indvars.iv") (a := "%indvars.iv.in") (w := 64) (x := ivIn)
    (c := BitVec.ofNat 64 1)
    (by rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
      lookupName_cells_of_some (cs := ifEndPhiCells v7 v8 ivIn k0 termsIn toksIn)
        (n := "%indvars.iv.in") (env := env) (by rw [ifEndPhiCells]; cells_lk)])]
  rw [stage2NoEventWalk_denote_add_imm_w (calls := calls) (env := _) (s := s)
    (d := "%inc") (a := "%k.0") (w := 64) (x := k0) (c := BitVec.ofNat 64 1)
    (by rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide),
      lookupName_cells_of_some (cs := ifEndPhiCells v7 v8 ivIn k0 termsIn toksIn)
        (n := "%k.0") (env := env) (by rw [ifEndPhiCells]; cells_lk)])]
  rw [ifEndAllCells, ifEndTailCells, ifEndPhiCells, cells, denoteCode_nil]
  rfl

/-- `if.end` at the `if.end327` edge: the `phi` run and the four adds. -/
theorem ifEnd_denote_fromEnd327 (calls : Calls) (env : Env) (s : State)
    {v7 : BitVec 8} {v8 : BitVec 32} {ivIn k0 termsIn toksIn : BitVec 64}
    (hpre : s.pre = some "if.end327")
    (h47 : lookupName env "%47" = some (.int 8 v7))
    (h46 : lookupName env "%46" = some (.int 32 v8))
    (hiv : lookupName env "%indvars.iv" = some (.int 64 ivIn))
    (hinc : lookupName env "%inc" = some (.int 64 k0))
    (htr : lookupName env "%terms.0" = some (.int 64 termsIn))
    (htok : lookupName env "%tokens.0" = some (.int 64 toksIn)) :
    denoteCode calls ifEndBlock.instrs (stateAt env s) =
      some (stateAt (cells (ifEndAllCells v7 v8 ivIn k0 termsIn toksIn) env) s) := by
  have h1 := ifEndPhi_denote_fromEnd327 (calls := calls) (env := env) (s := s)
    hpre h47 h46 hiv hinc htr htok
  have h2 := ifEndTail_denote (calls := calls) (env := env) (s := s)
    (v7 := v7) (v8 := v8) (ivIn := ivIn) (k0 := k0) (termsIn := termsIn) (toksIn := toksIn)
  rw [ifEndBlock, ifEnd_split]
  rw [denoteCode_append_apply (a := ifEndPhiInstrs) (b := ifEndRest) h1 (by decide)]
  exact h2

/-- `if.end` at the `if.end327.peel` edge: the `phi` run and the four adds. -/
theorem ifEnd_denote_fromEnd327Peel (calls : Calls) (env : Env) (s : State)
    {v7 : BitVec 8} {v8 : BitVec 32} {ivIn k0 termsIn toksIn : BitVec 64}
    (hpre : s.pre = some "if.end327.peel")
    (h6 : lookupName env "%6" = some (.int 8 v7))
    (h5 : lookupName env "%5" = some (.int 32 v8))
    (h1 : lookupName env "%1" = some (.int 64 ivIn))
    (hinc : lookupName env "%inc.peel" = some (.int 64 k0))
    (htr : lookupName env "%terms.0.ph1407" = some (.int 64 termsIn))
    (htok : lookupName env "%tokens.0.ph1408" = some (.int 64 toksIn)) :
    denoteCode calls ifEndBlock.instrs (stateAt env s) =
      some (stateAt (cells (ifEndAllCells v7 v8 ivIn k0 termsIn toksIn) env) s) := by
  have hphi := ifEndPhi_denote_fromEnd327Peel (calls := calls) (env := env) (s := s)
    hpre h6 h5 h1 hinc htr htok
  have htail := ifEndTail_denote (calls := calls) (env := env) (s := s)
    (v7 := v7) (v8 := v8) (ivIn := ivIn) (k0 := k0) (termsIn := termsIn) (toksIn := toksIn)
  rw [ifEndBlock, ifEnd_split]
  rw [denoteCode_append_apply (a := ifEndPhiInstrs) (b := ifEndRest) hphi (by decide)]
  exact htail

/-- `if.end` at the `if.end327` edge, as a link to `NodeBlock15`. -/
theorem link_ifEnd_fromEnd327 {calls : Calls} {K : Stage2NoEventWalkCarry} {mem : Mem}
    {s : State} {v7 : BitVec 8} {v8 : BitVec 32} {ivIn k0 termsIn toksIn : BitVec 64}
    (h : Stage2NoEventWalkInv K mem s) (hpc : s.pc = "if.end")
    (hpre : s.pre = some "if.end327")
    (h47 : lookupName s.env "%47" = some (.int 8 v7))
    (h46 : lookupName s.env "%46" = some (.int 32 v8))
    (hiv : lookupName s.env "%indvars.iv" = some (.int 64 ivIn))
    (hinc : lookupName s.env "%inc" = some (.int 64 k0))
    (htr : lookupName s.env "%terms.0" = some (.int 64 termsIn))
    (htok : lookupName s.env "%tokens.0" = some (.int 64 toksIn)) :
    Stage2NoEventWalkLink calls K mem s K
      (stage2NoEventWalkNext (cells (ifEndAllCells v7 v8 ivIn k0 termsIn toksIn) s.env)
        s "NodeBlock15") := by
  have hcode := ifEnd_denote_fromEnd327 (calls := calls) (env := s.env) (s := s)
    hpre h47 h46 hiv hinc htr htok
  refine ⟨h, ?_, Stage2NoEventWalkInv.mem_congr h rfl⟩
  have hstep := stage2NoEventWalk_step_br (s := s) (f := stage2NoEventBody)
    (by rw [hpc]; exact ifEndBlock_find) (by simpa only [stateAt] using hcode) rfl
  simpa only [stage2NoEventWalkNext, stateAt] using hstep

/-- `if.end` at the `if.end327.peel` edge, as a link to `NodeBlock15`. -/
theorem link_ifEnd_fromEnd327Peel {calls : Calls} {K : Stage2NoEventWalkCarry} {mem : Mem}
    {s : State} {v7 : BitVec 8} {v8 : BitVec 32} {ivIn k0 termsIn toksIn : BitVec 64}
    (h : Stage2NoEventWalkInv K mem s) (hpc : s.pc = "if.end")
    (hpre : s.pre = some "if.end327.peel")
    (h6 : lookupName s.env "%6" = some (.int 8 v7))
    (h5 : lookupName s.env "%5" = some (.int 32 v8))
    (h1 : lookupName s.env "%1" = some (.int 64 ivIn))
    (hinc : lookupName s.env "%inc.peel" = some (.int 64 k0))
    (htr : lookupName s.env "%terms.0.ph1407" = some (.int 64 termsIn))
    (htok : lookupName s.env "%tokens.0.ph1408" = some (.int 64 toksIn)) :
    Stage2NoEventWalkLink calls K mem s K
      (stage2NoEventWalkNext (cells (ifEndAllCells v7 v8 ivIn k0 termsIn toksIn) s.env)
        s "NodeBlock15") := by
  have hcode := ifEnd_denote_fromEnd327Peel (calls := calls) (env := s.env) (s := s)
    hpre h6 h5 h1 hinc htr htok
  refine ⟨h, ?_, Stage2NoEventWalkInv.mem_congr h rfl⟩
  have hstep := stage2NoEventWalk_step_br (s := s) (f := stage2NoEventBody)
    (by rw [hpc]; exact ifEndBlock_find) (by simpa only [stateAt] using hcode) rfl
  simpa only [stage2NoEventWalkNext, stateAt] using hstep

/-- The seven `NodeBlock15` bindings, as the producer hands them back. -/
theorem ifEndAllCells_lookup (v7 : BitVec 8) (v8 : BitVec 32)
    (ivIn k0 termsIn toksIn : BitVec 64) (env : Env) :
    lookupName (cells (ifEndAllCells v7 v8 ivIn k0 termsIn toksIn) env) "%indvars.iv"
        = some (.int 64 (ivIn + BitVec.ofNat 64 1)) ∧
      lookupName (cells (ifEndAllCells v7 v8 ivIn k0 termsIn toksIn) env) "%tokens.0"
        = some (.int 64 (toksIn + BitVec.ofNat 64 1)) ∧
      lookupName (cells (ifEndAllCells v7 v8 ivIn k0 termsIn toksIn) env) "%terms.0"
        = some (.int 64 (termsIn + BitVec.ofNat 64 3)) ∧
      lookupName (cells (ifEndAllCells v7 v8 ivIn k0 termsIn toksIn) env) "%inc"
        = some (.int 64 (k0 + BitVec.ofNat 64 1)) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    exact lookupName_cells_of_some (cs := ifEndAllCells v7 v8 ivIn k0 termsIn toksIn)
      (n := _) (env := env)
      (by simp only [ifEndAllCells, ifEndTailCells, ifEndPhiCells, List.cons_append,
        List.nil_append]; cells_lk)

/-- **`if.end`'s producer at the `if.end327` edge**: the counts and the entry
index at `NodeBlock15`, as conclusions. -/
theorem ifEndProduce_fromEnd327 {calls : Calls} {K : Stage2NoEventWalkCarry} {mem : Mem}
    {s : State} {v7 : BitVec 8} {v8 : BitVec 32} {ivIn k0 termsIn toksIn : BitVec 64}
    (h : Stage2NoEventWalkInv K mem s) (hpc : s.pc = "if.end")
    (hpre : s.pre = some "if.end327")
    (h47 : lookupName s.env "%47" = some (.int 8 v7))
    (h46 : lookupName s.env "%46" = some (.int 32 v8))
    (hiv : lookupName s.env "%indvars.iv" = some (.int 64 ivIn))
    (hinc : lookupName s.env "%inc" = some (.int 64 k0))
    (htr : lookupName s.env "%terms.0" = some (.int 64 termsIn))
    (htok : lookupName s.env "%tokens.0" = some (.int 64 toksIn)) :
    ∃ s', Stage2NoEventWalkLink calls K mem s K s' ∧ s'.pc = "NodeBlock15" ∧
      lookupName s'.env "%7" = some (.int 8 v7) ∧
      lookupName s'.env "%8" = some (.int 32 v8) ∧
      lookupName s'.env "%indvars.iv" = some (.int 64 (ivIn + BitVec.ofNat 64 1)) ∧
      lookupName s'.env "%k.0" = some (.int 64 k0) ∧
      lookupName s'.env "%terms.0" = some (.int 64 (termsIn + BitVec.ofNat 64 3)) ∧
      lookupName s'.env "%tokens.0" = some (.int 64 (toksIn + BitVec.ofNat 64 1)) ∧
      lookupName s'.env "%inc" = some (.int 64 (k0 + BitVec.ofNat 64 1)) := by
  obtain ⟨hiv', htok', htr', hinc'⟩ :=
    ifEndAllCells_lookup v7 v8 ivIn k0 termsIn toksIn s.env
  refine ⟨stage2NoEventWalkNext
      (cells (ifEndAllCells v7 v8 ivIn k0 termsIn toksIn) s.env) s "NodeBlock15",
    link_ifEnd_fromEnd327 h hpc hpre h47 h46 hiv hinc htr htok,
    by simp only [stage2NoEventWalkNext],
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact lookupName_cells_of_some (cs := ifEndAllCells v7 v8 ivIn k0 termsIn toksIn)
      (n := "%7") (env := s.env)
      (by simp only [ifEndAllCells, ifEndTailCells, ifEndPhiCells, List.cons_append,
        List.nil_append]; cells_lk)
  · exact lookupName_cells_of_some (cs := ifEndAllCells v7 v8 ivIn k0 termsIn toksIn)
      (n := "%8") (env := s.env)
      (by simp only [ifEndAllCells, ifEndTailCells, ifEndPhiCells, List.cons_append,
        List.nil_append]; cells_lk)
  · simpa only [stage2NoEventWalkNext] using hiv'
  · exact lookupName_cells_of_some (cs := ifEndAllCells v7 v8 ivIn k0 termsIn toksIn)
      (n := "%k.0") (env := s.env)
      (by simp only [ifEndAllCells, ifEndTailCells, ifEndPhiCells, List.cons_append,
        List.nil_append]; cells_lk)
  · simpa only [stage2NoEventWalkNext] using htr'
  · simpa only [stage2NoEventWalkNext] using htok'
  · simpa only [stage2NoEventWalkNext] using hinc'

/-- **`if.end`'s producer at the `if.end327.peel` edge**: the counts and the entry
index at `NodeBlock15`, as conclusions. -/
theorem ifEndProduce_fromEnd327Peel {calls : Calls} {K : Stage2NoEventWalkCarry}
    {mem : Mem} {s : State} {v7 : BitVec 8} {v8 : BitVec 32}
    {ivIn k0 termsIn toksIn : BitVec 64}
    (h : Stage2NoEventWalkInv K mem s) (hpc : s.pc = "if.end")
    (hpre : s.pre = some "if.end327.peel")
    (h6 : lookupName s.env "%6" = some (.int 8 v7))
    (h5 : lookupName s.env "%5" = some (.int 32 v8))
    (h1 : lookupName s.env "%1" = some (.int 64 ivIn))
    (hinc : lookupName s.env "%inc.peel" = some (.int 64 k0))
    (htr : lookupName s.env "%terms.0.ph1407" = some (.int 64 termsIn))
    (htok : lookupName s.env "%tokens.0.ph1408" = some (.int 64 toksIn)) :
    ∃ s', Stage2NoEventWalkLink calls K mem s K s' ∧ s'.pc = "NodeBlock15" ∧
      lookupName s'.env "%7" = some (.int 8 v7) ∧
      lookupName s'.env "%8" = some (.int 32 v8) ∧
      lookupName s'.env "%indvars.iv" = some (.int 64 (ivIn + BitVec.ofNat 64 1)) ∧
      lookupName s'.env "%k.0" = some (.int 64 k0) ∧
      lookupName s'.env "%terms.0" = some (.int 64 (termsIn + BitVec.ofNat 64 3)) ∧
      lookupName s'.env "%tokens.0" = some (.int 64 (toksIn + BitVec.ofNat 64 1)) ∧
      lookupName s'.env "%inc" = some (.int 64 (k0 + BitVec.ofNat 64 1)) := by
  obtain ⟨hiv', htok', htr', hinc'⟩ :=
    ifEndAllCells_lookup v7 v8 ivIn k0 termsIn toksIn s.env
  refine ⟨stage2NoEventWalkNext
      (cells (ifEndAllCells v7 v8 ivIn k0 termsIn toksIn) s.env) s "NodeBlock15",
    link_ifEnd_fromEnd327Peel h hpc hpre h6 h5 h1 hinc htr htok,
    by simp only [stage2NoEventWalkNext],
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact lookupName_cells_of_some (cs := ifEndAllCells v7 v8 ivIn k0 termsIn toksIn)
      (n := "%7") (env := s.env)
      (by simp only [ifEndAllCells, ifEndTailCells, ifEndPhiCells, List.cons_append,
        List.nil_append]; cells_lk)
  · exact lookupName_cells_of_some (cs := ifEndAllCells v7 v8 ivIn k0 termsIn toksIn)
      (n := "%8") (env := s.env)
      (by simp only [ifEndAllCells, ifEndTailCells, ifEndPhiCells, List.cons_append,
        List.nil_append]; cells_lk)
  · simpa only [stage2NoEventWalkNext] using hiv'
  · exact lookupName_cells_of_some (cs := ifEndAllCells v7 v8 ivIn k0 termsIn toksIn)
      (n := "%k.0") (env := s.env)
      (by simp only [ifEndAllCells, ifEndTailCells, ifEndPhiCells, List.cons_append,
        List.nil_append]; cells_lk)
  · simpa only [stage2NoEventWalkNext] using htr'
  · simpa only [stage2NoEventWalkNext] using htok'
  · simpa only [stage2NoEventWalkNext] using hinc'

/-- **`if.end`'s producer, from either edge**: whichever predecessor reached the
block, the run hands back the seven `NodeBlock15` bindings as conclusions.  The
edge's operands are the hypotheses, supplied by the caller for the edge its state
names. -/
theorem ifEnd_produce {calls : Calls} {K : Stage2NoEventWalkCarry} {mem : Mem}
    {s : State} {v7 : BitVec 8} {v8 : BitVec 32} {ivIn k0 termsIn toksIn : BitVec 64}
    (h : Stage2NoEventWalkInv K mem s) (hpc : s.pc = "if.end")
    (hpre : s.pre = some "if.end327" ∨ s.pre = some "if.end327.peel")
    (h47 : s.pre = some "if.end327" →
      lookupName s.env "%47" = some (.int 8 v7))
    (h46 : s.pre = some "if.end327" →
      lookupName s.env "%46" = some (.int 32 v8))
    (hiv : s.pre = some "if.end327" →
      lookupName s.env "%indvars.iv" = some (.int 64 ivIn))
    (hinc : s.pre = some "if.end327" →
      lookupName s.env "%inc" = some (.int 64 k0))
    (htr : s.pre = some "if.end327" →
      lookupName s.env "%terms.0" = some (.int 64 termsIn))
    (htok : s.pre = some "if.end327" →
      lookupName s.env "%tokens.0" = some (.int 64 toksIn))
    (h6 : s.pre = some "if.end327.peel" →
      lookupName s.env "%6" = some (.int 8 v7))
    (h5 : s.pre = some "if.end327.peel" →
      lookupName s.env "%5" = some (.int 32 v8))
    (h1 : s.pre = some "if.end327.peel" →
      lookupName s.env "%1" = some (.int 64 ivIn))
    (hincp : s.pre = some "if.end327.peel" →
      lookupName s.env "%inc.peel" = some (.int 64 k0))
    (htrp : s.pre = some "if.end327.peel" →
      lookupName s.env "%terms.0.ph1407" = some (.int 64 termsIn))
    (htokp : s.pre = some "if.end327.peel" →
      lookupName s.env "%tokens.0.ph1408" = some (.int 64 toksIn)) :
    ∃ s', Stage2NoEventWalkLink calls K mem s K s' ∧ s'.pc = "NodeBlock15" ∧
      lookupName s'.env "%7" = some (.int 8 v7) ∧
      lookupName s'.env "%8" = some (.int 32 v8) ∧
      lookupName s'.env "%indvars.iv" = some (.int 64 (ivIn + BitVec.ofNat 64 1)) ∧
      lookupName s'.env "%k.0" = some (.int 64 k0) ∧
      lookupName s'.env "%terms.0" = some (.int 64 (termsIn + BitVec.ofNat 64 3)) ∧
      lookupName s'.env "%tokens.0" = some (.int 64 (toksIn + BitVec.ofNat 64 1)) ∧
      lookupName s'.env "%inc" = some (.int 64 (k0 + BitVec.ofNat 64 1)) := by
  rcases hpre with hpre | hpre
  · exact ifEndProduce_fromEnd327 h hpc hpre (h47 hpre) (h46 hpre) (hiv hpre)
      (hinc hpre) (htr hpre) (htok hpre)
  · exact ifEndProduce_fromEnd327Peel h hpc hpre (h6 hpre) (h5 hpre) (h1 hpre)
      (hincp hpre) (htrp hpre) (htokp hpre)

/-! ### The `{` count, the next-entry dispatch, and the `}` handoff

The open arm's tail after `if.end23`: `if.end74` reads the next entry's lane and
byte (its own `%add`/`%inc26` are the non-empty path's, dead on the `}` arm and
not carried), `NodeBlock21` tests the byte against 125, and `LeafBlock19` selects
the empty-object close at `if.then81`. -/

/-- `if.end74`: the `{` counts and the next-entry read. -/
def ifEnd74Instrs : List Instr :=
  [ Instr.binop "%add" BinOp.add 64 (Operand.reg "%terms.0.lcssa1080")
      (Operand.imm (.int 64 (BitVec.ofNat 64 1))),
    Instr.binop "%inc26" BinOp.add 64 (Operand.reg "%tokens.0.lcssa1074")
      (Operand.imm (.int 64 (BitVec.ofNat 64 1))),
    Instr.gep "%arrayidx75" (Ty.int 32) (Operand.reg "%ep")
      (Operand.reg "%inc.lcssa1129"),
    Instr.load "%10" (Ty.int 32) (Operand.reg "%arrayidx75"),
    Instr.zext "%idxprom76" 32 64 (Operand.reg "%10"),
    Instr.gep "%arrayidx77" (Ty.int 8) (Operand.reg "%b")
      (Operand.reg "%idxprom76"),
    Instr.load "%11" (Ty.int 8) (Operand.reg "%arrayidx77") ]

/-- `if.end74`, pinned. -/
def ifEnd74Block : Block :=
  { name := "if.end74", instrs := ifEnd74Instrs, term := Term.br "NodeBlock21" }

theorem ifEnd74Block_find :
    stage2NoEventBody.findBlock "if.end74" = some ifEnd74Block := by
  decide

/-- `NodeBlock21`: the next byte against 125. -/
def nodeBlock21Instrs : List Instr :=
  [ Instr.icmp "%Pivot22" IPred.slt 8 (Operand.reg "%11")
      (Operand.imm (.int 8 (BitVec.ofNat 8 125))) ]

/-- `NodeBlock21`, pinned. -/
def nodeBlock21Block : Block :=
  { name := "NodeBlock21", instrs := nodeBlock21Instrs,
    term := Term.condbr (Operand.reg "%Pivot22") "LeafBlock17" "LeafBlock19" }

theorem nodeBlock21Block_find :
    stage2NoEventBody.findBlock "NodeBlock21" = some nodeBlock21Block := by
  decide

/-- `LeafBlock19`: the byte against 125, selecting the empty-object close. -/
def leafBlock19Instrs : List Instr :=
  [ Instr.icmp "%SwitchLeaf20" IPred.eq 8 (Operand.reg "%11")
      (Operand.imm (.int 8 (BitVec.ofNat 8 125))) ]

/-- `LeafBlock19`, pinned. -/
def leafBlock19Block : Block :=
  { name := "LeafBlock19", instrs := leafBlock19Instrs,
    term := Term.condbr (Operand.reg "%SwitchLeaf20") "if.then81" "if.then94" }

theorem leafBlock19Block_find :
    stage2NoEventBody.findBlock "LeafBlock19" = some leafBlock19Block := by
  decide

-- The three pins are the parsed body's.
#guard decide (stage2NoEventBody.findBlock "if.end74" ≠ none)
#guard decide (stage2NoEventBody.findBlock "NodeBlock21" ≠ none)
#guard decide (stage2NoEventBody.findBlock "LeafBlock19" ≠ none)

/-- The cells `if.end74` binds: the dead `{` counts, the lane and the next byte,
newest written first. -/
def ifEnd74Cells (ep b : Nat) (terms tok inc : BitVec 64)
    (bs4n bs1n : List UInt8) : List (String × Value) :=
  [("%11", .int 8 (BitVec.ofNat 8 (bytesToNat bs1n))),
   ("%arrayidx77",
     .ptr (b + (BitVec.signExtend 64 (BitVec.ofNat 64 (bytesToNat bs4n))).toNat)),
   ("%idxprom76", .int 64 (BitVec.ofNat 64 (bytesToNat bs4n))),
   ("%10", .int 32 (BitVec.ofNat 32 (bytesToNat bs4n))),
   ("%arrayidx75", .ptr (ep + inc.toNat * 4)),
   ("%inc26", .int 64 (tok + BitVec.ofNat 64 1)),
   ("%add", .int 64 (terms + BitVec.ofNat 64 1))]

/-- `if.end74`'s environment. -/
def ifEnd74Out (env : Env) (ep b : Nat) (terms tok inc : BitVec 64)
    (bs4n bs1n : List UInt8) : Env :=
  cells (ifEnd74Cells ep b terms tok inc bs4n bs1n) env

/-- `if.end74`'s run: the two dead counts and the next-entry lane and byte. -/
theorem ifEnd74_denote (calls : Calls) (env : Env) (s : State)
    {ep b : Nat} {terms tok inc : BitVec 64} {bs4n bs1n : List UInt8}
    (hterms : lookupName env "%terms.0.lcssa1080" = some (.int 64 terms))
    (htok : lookupName env "%tokens.0.lcssa1074" = some (.int 64 tok))
    (hep : lookupName env "%ep" = some (.ptr ep))
    (hb : lookupName env "%b" = some (.ptr b))
    (hinc : lookupName env "%inc.lcssa1129" = some (.int 64 inc))
    (hincLt : inc.toNat < 2 ^ 63)
    (hlane : readBytes s.mem (ep + inc.toNat * 4) 4 = some bs4n)
    (hlanelt : bytesToNat bs4n < 2 ^ 32)
    (hbyte : readBytes s.mem
      (b + (BitVec.signExtend 64 (BitVec.ofNat 64 (bytesToNat bs4n))).toNat)
      1 = some bs1n) :
    denoteCode calls ifEnd74Instrs (stateAt env s) =
      some (stateAt (ifEnd74Out env ep b terms tok inc bs4n bs1n) s) := by
  rw [ifEnd74Instrs]
  rw [stage2NoEventWalk_denote_add_imm_w (calls := calls) (env := env) (s := s)
    (d := "%add") (a := "%terms.0.lcssa1080") (w := 64) (x := terms) hterms]
  rw [stage2NoEventWalk_denote_add_imm_w (calls := calls) (env := _) (s := s)
    (d := "%inc26") (a := "%tokens.0.lcssa1074") (w := 64) (x := tok)
    (by rw [lookupName_cons_ne _ _ (by decide)]; exact htok)]
  rw [stage2NoEventWalk_denote_gep32 (calls := calls) (env := _) (s := s)
    (d := "%arrayidx75") (base := "%ep") (off := "%inc.lcssa1129")
    (a := ep) (o := inc)
    (by rw [lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide)]; exact hep)
    (by rw [lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide)]; exact hinc)
    (by rw [stage2NoEventSignExtend_self]; exact hincLt)]
  rw [stage2NoEventSignExtend_self]
  rw [stage2NoEventWalk_denote_load_int (calls := calls) (env := _) (s := s)
    (d := "%10") (p := "%arrayidx75") (a := ep + inc.toNat * 4) (w := 32)
    (bs := bs4n) (hw := by decide) (by simp only [lookupName_cons_self])
    (by simpa using hlane)]
  rw [denoteCode_zext (calls := calls) (env := _) (s := s) (d := "%idxprom76")
    (v := "%10") (wIn := 32) (wOut := 64)
    (x := BitVec.ofNat 32 (bytesToNat bs4n)) (by simp only [lookupName_cons_self])]
  rw [stage2NoEventOfNat32_toNat hlanelt]
  rw [denoteCode_gep8_reg (calls := calls) (env := _) (s := s)
    (d := "%arrayidx77") (base := "%b") (off := "%idxprom76")
    (a := b) (idx := BitVec.ofNat 64 (bytesToNat bs4n))
    (by rw [lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide)]; exact hb)
    (by simp only [lookupName_cons_self])
    (by
      have hx : bytesToNat bs4n < 2 ^ 63 := by omega
      rw [stage2NoEventSignExtend_ofNat hx]
      exact hx)]
  rw [stage2NoEventWalk_denote_load_int (calls := calls) (env := _) (s := s)
    (d := "%11") (p := "%arrayidx77")
    (a := b + (BitVec.signExtend 64 (BitVec.ofNat 64 (bytesToNat bs4n))).toNat)
    (w := 8) (bs := bs1n) (hw := by decide)
    (by simp only [lookupName_cons_self]) (by simpa using hbyte)]
  simp only [ifEnd74Out, ifEnd74Cells, cells, denoteCode_nil]

/-- `if.end19` at the zero depth: the true arm, to `if.end23`. -/
theorem link_ifEnd19_true {calls : Calls} {K : Stage2NoEventWalkCarry} {mem : Mem}
    {s : State} {sp : BitVec 32}
    (h : Stage2NoEventWalkInv K mem s) (hpc : s.pc = "if.end19")
    (hsp : lookupName s.env "%sp.0.lcssa1092.wide" = some (.int 32 sp))
    (hzero : sp.toNat = 0) :
    Stage2NoEventWalkLink calls K mem s K
      (stage2NoEventWalkNext
        (("%tobool.not", .int 1 1) :: s.env) s "if.end23") := by
  have hsp0 : sp = BitVec.ofNat 32 0 := by
    rw [← BitVec.toNat_inj]
    simp [hzero]
  have hbit : evalICmp .eq sp (BitVec.ofNat 32 0) = (1 : BitVec 1) := by
    rw [hsp0]
    decide
  have hcode : denoteCode calls ifEnd19Block.instrs (stateAt s.env s) =
      some (stateAt (("%tobool.not", .int 1 1) :: s.env) s) := by
    rw [ifEnd19Block, stage2NoEventWalk_denote_icmp_imm (calls := calls)
      (env := s.env) (s := s) (d := "%tobool.not") (a := "%sp.0.lcssa1092.wide")
      (p := .eq) (w := 32) (c := BitVec.ofNat 32 0) hsp (is := [])]
    simp only [hbit, denoteCode_nil]
  refine stage2NoEventWalkLink_condbr_true (env' := ("%tobool.not", .int 1 1) :: s.env)
    h (by rw [hpc]; exact ifEnd19Block_find) hcode rfl ?_
  rw [lookupName_cons_self]

/-- `NodeBlock21` at a byte at or above 125: the false arm, to `LeafBlock19`. -/
theorem link_nodeBlock21_false {calls : Calls} {K : Stage2NoEventWalkCarry}
    {mem : Mem} {s : State} {y : BitVec 8}
    (h : Stage2NoEventWalkInv K mem s) (hpc : s.pc = "NodeBlock21")
    (h11 : lookupName s.env "%11" = some (.int 8 y))
    (hy : evalICmp .slt y (BitVec.ofNat 8 125) = 0) :
    Stage2NoEventWalkLink calls K mem s K
      (stage2NoEventWalkNext (("%Pivot22", .int 1 0) :: s.env) s "LeafBlock19") := by
  have hcode : denoteCode calls nodeBlock21Block.instrs (stateAt s.env s) =
      some (stateAt (("%Pivot22", .int 1 0) :: s.env) s) := by
    rw [nodeBlock21Block, nodeBlock21Instrs,
      stage2NoEventWalk_denote_icmp_imm (calls := calls) (env := s.env) (s := s)
      (d := "%Pivot22") (a := "%11") (p := .slt) (w := 8)
      (c := BitVec.ofNat 8 125) h11 (is := [])]
    simp only [hy, denoteCode_nil]
  exact stage2NoEventWalkLink_condbr_false (env' := ("%Pivot22", .int 1 0) :: s.env)
    h (by rw [hpc]; exact nodeBlock21Block_find) hcode rfl (by rw [lookupName_cons_self])

/-- `LeafBlock19` at 125: the empty-object close, to `if.then81`. -/
theorem link_leafBlock19_true {calls : Calls} {K : Stage2NoEventWalkCarry}
    {mem : Mem} {s : State} {y : BitVec 8}
    (h : Stage2NoEventWalkInv K mem s) (hpc : s.pc = "LeafBlock19")
    (h11 : lookupName s.env "%11" = some (.int 8 y))
    (hy : evalICmp .eq y (BitVec.ofNat 8 125) = 1) :
    Stage2NoEventWalkLink calls K mem s K
      (stage2NoEventWalkNext (("%SwitchLeaf20", .int 1 1) :: s.env) s "if.then81") := by
  have hcode : denoteCode calls leafBlock19Block.instrs (stateAt s.env s) =
      some (stateAt (("%SwitchLeaf20", .int 1 1) :: s.env) s) := by
    rw [leafBlock19Block, leafBlock19Instrs,
      stage2NoEventWalk_denote_icmp_imm (calls := calls) (env := s.env) (s := s)
      (d := "%SwitchLeaf20") (a := "%11") (p := .eq) (w := 8)
      (c := BitVec.ofNat 8 125) h11 (is := [])]
    simp only [hy, denoteCode_nil]
  exact stage2NoEventWalkLink_condbr_true (env' := ("%SwitchLeaf20", .int 1 1) :: s.env)
    h (by rw [hpc]; exact leafBlock19Block_find) hcode rfl (by rw [lookupName_cons_self])

/-- **`if.end74` link** (K to K): the `{` counts are the non-empty path's and
the readings do not move on this arm; the next-entry read is memory-only. -/
theorem link_ifEnd74 {calls : Calls} {K : Stage2NoEventWalkCarry} {mem : Mem}
    {s : State} {ep b : Nat} {terms tok inc : BitVec 64} {bs4n bs1n : List UInt8}
    (h : Stage2NoEventWalkInv K mem s) (hpc : s.pc = "if.end74")
    (hterms : lookupName s.env "%terms.0.lcssa1080" = some (.int 64 terms))
    (htok : lookupName s.env "%tokens.0.lcssa1074" = some (.int 64 tok))
    (hep : lookupName s.env "%ep" = some (.ptr ep))
    (hb : lookupName s.env "%b" = some (.ptr b))
    (hinc : lookupName s.env "%inc.lcssa1129" = some (.int 64 inc))
    (hincLt : inc.toNat < 2 ^ 63)
    (hlane : readBytes s.mem (ep + inc.toNat * 4) 4 = some bs4n)
    (hlanelt : bytesToNat bs4n < 2 ^ 32)
    (hbyte : readBytes s.mem
      (b + (BitVec.signExtend 64 (BitVec.ofNat 64 (bytesToNat bs4n))).toNat)
      1 = some bs1n) :
    Stage2NoEventWalkLink calls K mem s K
      (stage2NoEventWalkNext (ifEnd74Out s.env ep b terms tok inc bs4n bs1n)
        s "NodeBlock21") := by
  have hcode := ifEnd74_denote (calls := calls) s.env s hterms htok hep hb hinc
    hincLt hlane hlanelt hbyte
  refine ⟨h, ?_, Stage2NoEventWalkInv.mem_congr h rfl⟩
  have hstep := stage2NoEventWalk_step_br (s := s) (f := stage2NoEventBody)
    (by rw [hpc]; exact ifEnd74Block_find) hcode rfl
  simpa only [stage2NoEventWalkNext, stateAt] using hstep

/-- The state `if.end74` delivers. -/
def braceCountState (s : State) (ep b : Nat) (terms tok inc : BitVec 64)
    (bs4n bs1n : List UInt8) : State :=
  stage2NoEventWalkNext (ifEnd74Out s.env ep b terms tok inc bs4n bs1n)
    s "NodeBlock21"

/-- The state `NodeBlock21` delivers. -/
def braceDispatchState (s : State) (ep b : Nat) (terms tok inc : BitVec 64)
    (bs4n bs1n : List UInt8) : State :=
  stage2NoEventWalkNext
    (("%Pivot22", .int 1 0) :: ifEnd74Out s.env ep b terms tok inc bs4n bs1n)
    (braceCountState s ep b terms tok inc bs4n bs1n) "LeafBlock19"

/-- The state `LeafBlock19` delivers at the `}` arm. -/
def braceSelectState (s : State) (ep b : Nat) (terms tok inc : BitVec 64)
    (bs4n bs1n : List UInt8) : State :=
  stage2NoEventWalkNext
    (("%SwitchLeaf20", .int 1 1) :: ("%Pivot22", .int 1 0) ::
      ifEnd74Out s.env ep b terms tok inc bs4n bs1n)
    (braceDispatchState s ep b terms tok inc bs4n bs1n) "if.then81"

/-- The cells `if.then81` binds on the `{}` route. -/
def braceCountsOut (s : State) (ep b : Nat) (terms tok inc k : BitVec 64)
    (bs4n bs1n : List UInt8) : Env :=
  ifThen81Out
    (("%SwitchLeaf20", .int 1 1) :: ("%Pivot22", .int 1 0) ::
      ifEnd74Out s.env ep b terms tok inc bs4n bs1n) k tok terms

/-- The state `if.then81` delivers: the `}` count and the `close_obj` handoff. -/
def braceCloseState (s : State) (ep b : Nat) (terms tok inc k : BitVec 64)
    (bs4n bs1n : List UInt8) : State :=
  stage2NoEventWalkNext (braceCountsOut s ep b terms tok inc k bs4n bs1n)
    (braceSelectState s ep b terms tok inc bs4n bs1n) "close_obj"

/-- **The `{}` open arm's tail**: `if.end74` → `NodeBlock21` → `LeafBlock19` →
`if.then81`, the carry taking the `{`/`}` counts (`tok + 2`, `terms + 3`) from
the bound-derived guard at the close. -/
theorem stage2NoEventRow_braceCloseTail {calls : Calls} {K : Stage2NoEventWalkCarry}
    {mem : Mem} {s : State} {ep b : Nat} {terms tok inc k : BitVec 64}
    {bs4n bs1n : List UInt8}
    (h : Stage2NoEventWalkInv K mem s) (hpc : s.pc = "if.end74")
    (hterms : lookupName s.env "%terms.0.lcssa1080" = some (.int 64 terms))
    (htok : lookupName s.env "%tokens.0.lcssa1074" = some (.int 64 tok))
    (hep : lookupName s.env "%ep" = some (.ptr ep))
    (hb : lookupName s.env "%b" = some (.ptr b))
    (hinc : lookupName s.env "%inc.lcssa1129" = some (.int 64 inc))
    (hincLt : inc.toNat < 2 ^ 63)
    (hlane : readBytes s.mem (ep + inc.toNat * 4) 4 = some bs4n)
    (hlanelt : bytesToNat bs4n < 2 ^ 32)
    (hbyte : readBytes s.mem
      (b + (BitVec.signExtend 64 (BitVec.ofNat 64 (bytesToNat bs4n))).toNat)
      1 = some bs1n)
    (hnext : bytesToNat bs1n = 125)
    (hk : lookupName s.env "%k.0.lcssa1086" = some (.int 64 k))
    (hmem : K.pos ∈ K.ent) (hrel : K.tok + 2 ≤ K.pos) :
    Stage2NoEventWalkChain calls mem K s
      { K with tok := K.tok + 2, terms := K.terms + 3 }
      (braceCloseState s ep b terms tok inc k bs4n bs1n) := by
  let S1 := braceCountState s ep b terms tok inc bs4n bs1n
  let S2 := braceDispatchState s ep b terms tok inc bs4n bs1n
  let S3 := braceSelectState s ep b terms tok inc bs4n bs1n
  have L0 : Stage2NoEventWalkLink calls K mem s K S1 :=
    link_ifEnd74 h hpc hterms htok hep hb hinc hincLt hlane hlanelt hbyte
  have h11₁ : lookupName S1.env "%11"
      = some (.int 8 (BitVec.ofNat 8 (bytesToNat bs1n))) := by
    simp only [S1, braceCountState, stage2NoEventWalkNext, ifEnd74Out]
    exact lookupName_cells_of_some (cs := ifEnd74Cells ep b terms tok inc bs4n bs1n)
      (n := "%11") (env := s.env) (by rw [ifEnd74Cells]; cells_lk)
  have hlt : evalICmp .slt (BitVec.ofNat 8 (bytesToNat bs1n))
      (BitVec.ofNat 8 125) = 0 := by
    rw [hnext]; decide
  have L1 : Stage2NoEventWalkLink calls K mem S1 K S2 :=
    link_nodeBlock21_false L0.inv'
      (by simp only [S1, braceCountState, stage2NoEventWalkNext]) h11₁ hlt
  have h11₂ : lookupName S2.env "%11"
      = some (.int 8 (BitVec.ofNat 8 (bytesToNat bs1n))) := by
    simp only [S2, braceDispatchState, stage2NoEventWalkNext, ifEnd74Out]
    rw [lookupName_cons_ne _ _ (by decide)]
    exact lookupName_cells_of_some (cs := ifEnd74Cells ep b terms tok inc bs4n bs1n)
      (n := "%11") (env := s.env) (by rw [ifEnd74Cells]; cells_lk)
  have heq : evalICmp .eq (BitVec.ofNat 8 (bytesToNat bs1n))
      (BitVec.ofNat 8 125) = 1 := by
    rw [hnext]; decide
  have L2 : Stage2NoEventWalkLink calls K mem S2 K S3 :=
    link_leafBlock19_true L1.inv'
      (by simp only [S2, braceDispatchState, stage2NoEventWalkNext]) h11₂ heq
  have hk3 : lookupName S3.env "%k.0.lcssa1086" = some (.int 64 k) := by
    simp only [S3, braceSelectState, stage2NoEventWalkNext, ifEnd74Out]
    rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide)]
    rw [lookupName_cells_of_notin (cs := ifEnd74Cells ep b terms tok inc bs4n bs1n)
      (n := "%k.0.lcssa1086") (env := s.env) (by rw [ifEnd74Cells]; simp)]
    exact hk
  have htokr3 : lookupName S3.env "%tokens.0.lcssa1074" = some (.int 64 tok) := by
    simp only [S3, braceSelectState, stage2NoEventWalkNext, ifEnd74Out]
    rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide)]
    rw [lookupName_cells_of_notin (cs := ifEnd74Cells ep b terms tok inc bs4n bs1n)
      (n := "%tokens.0.lcssa1074") (env := s.env) (by rw [ifEnd74Cells]; simp)]
    exact htok
  have htr3 : lookupName S3.env "%terms.0.lcssa1080" = some (.int 64 terms) := by
    simp only [S3, braceSelectState, stage2NoEventWalkNext, ifEnd74Out]
    rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide)]
    rw [lookupName_cells_of_notin (cs := ifEnd74Cells ep b terms tok inc bs4n bs1n)
      (n := "%terms.0.lcssa1080") (env := s.env) (by rw [ifEnd74Cells]; simp)]
    exact hterms
  have L3 : Stage2NoEventWalkLink calls K mem S3
      { K with tok := K.tok + 2, terms := K.terms + 3 }
      (braceCloseState s ep b terms tok inc k bs4n bs1n) :=
    link_ifThen81_of_bound L2.inv'
      (by simp only [S3, braceSelectState, stage2NoEventWalkNext]) rfl
      hk3 htokr3 htr3 hmem hrel
  simpa only [S1, S2, S3] using
    (Stage2NoEventWalkChain.tail L0 (Stage2NoEventWalkChain.tail L1
      (Stage2NoEventWalkChain.tail L2 (Stage2NoEventWalkChain.tail L3
        (Stage2NoEventWalkChain.nil L3.inv')))))

/-- A chain's tail carries the invariant. -/
theorem Stage2NoEventWalkChain.inv {calls : Calls} {mem : Mem}
    {K K' : Stage2NoEventWalkCarry} {s s' : State}
    (h : Stage2NoEventWalkChain calls mem K s K' s') :
    Stage2NoEventWalkInv K' mem s' := by
  induction h with
  | nil hinv => exact hinv
  | tail _ _ ih => exact ih

/-- Two chains compose end to end. -/
theorem Stage2NoEventWalkChain.trans {calls : Calls} {mem : Mem}
    {K K' K'' : Stage2NoEventWalkCarry} {s s' s'' : State}
    (h1 : Stage2NoEventWalkChain calls mem K s K' s')
    (h2 : Stage2NoEventWalkChain calls mem K' s' K'' s'') :
    Stage2NoEventWalkChain calls mem K s K'' s'' := by
  induction h1 with
  | nil _ => exact h2
  | tail hl _ ih => exact Stage2NoEventWalkChain.tail hl (ih h2)

/-- The stack write's address for the `{` push, named once. -/
def bracePushAddr (K : Stage2NoEventWalkCarry) (sp : BitVec 32) : Nat :=
  K.stk + ((BitVec.ofNat 64
    ((sp + BitVec.ofNat 32 4294967295).toNat)).signExtend 64).toNat

/-- The `if.end19` true arm's `if.end23` state. -/
def openZeroEnd23 (s : State) : State :=
  stage2NoEventWalkNext (("%tobool.not", .int 1 1) :: s.env) s "if.end23"

/-- The `if.end19` true arm's `if.end74` state. -/
def openZeroEnd74 (s : State) (sp : BitVec 32) : State :=
  stage2NoEventWalkNext
    (("%cmp66.not", .int 1 1) ::
      ("%inc24", .int 32 (sp + BitVec.ofNat 32 1)) ::
      ("%tobool.not", .int 1 1) :: s.env)
    (openZeroEnd23 s) "if.end74"

/-- The `if.end19` false arm's `if.end74` state: the push row's stored state. -/
def openPushEnd74 (K : Stage2NoEventWalkCarry) (s : State) (sp : BitVec 32)
    (fr : BitVec 8) : State :=
  stage2NoEventWalkStoredAt
    (("%cmp66.not", .int 1 1) ::
      ("%inc24", .int 32 (sp + BitVec.ofNat 32 1)) ::
      ("%arrayidx22", .ptr (bracePushAddr K sp)) ::
      ("%idxprom21", .int 64 (BitVec.ofNat 64
        ((sp + BitVec.ofNat 32 4294967295).toNat))) ::
      ("%sub", .int 32 (sp + BitVec.ofNat 32 4294967295)) ::
      ("%tobool.not", .int 1 (evalICmp .eq sp (BitVec.ofNat 32 0))) :: s.env)
    s (writeBytes s.mem (bracePushAddr K sp) (natToBytes fr.toNat 1))
    "if.end74" "if.end23"

/-- **The open arm from `if.end19`**: the depth's case split.  At the zero depth
`if.end19`'s true arm skips the stack write; at a live depth the false arm runs
`stage2NoEventRow_bracePush` and writes the one stack byte.  Both rejoin at
`if.end74` and take the `{`/`}` counts to `close_obj` under the derived guard. -/
theorem stage2NoEventRow_openBrace {calls : Calls} {K : Stage2NoEventWalkCarry}
    {mem : Mem} {s : State} {sp : BitVec 32} {terms tok inc k nep : BitVec 64}
    {ep b : Nat} {fr : BitVec 8} {bs4n bs1n : List UInt8}
    (h : Stage2NoEventWalkInv K mem s) (hpc : s.pc = "if.end19")
    (hsp : lookupName s.env "%sp.0.lcssa1092.wide" = some (.int 32 sp))
    (hterms : lookupName s.env "%terms.0.lcssa1080" = some (.int 64 terms))
    (htok : lookupName s.env "%tokens.0.lcssa1074" = some (.int 64 tok))
    (hep : lookupName s.env "%ep" = some (.ptr ep))
    (hb : lookupName s.env "%b" = some (.ptr b))
    (hinc : lookupName s.env "%inc.lcssa1129" = some (.int 64 inc))
    (hnep : lookupName s.env "%nep" = some (.int 64 nep))
    (hult : BitVec.ult inc nep = true)
    (hincLt : inc.toNat < 2 ^ 63)
    (hnext : bytesToNat bs1n = 125)
    (hk : lookupName s.env "%k.0.lcssa1086" = some (.int 64 k))
    (hmem : K.pos ∈ K.ent) (hrel : K.tok + 2 ≤ K.pos)
    (hlane0 : readBytes s.mem (ep + inc.toNat * 4) 4 = some bs4n)
    (hbyte0 : readBytes s.mem
      (b + (BitVec.signExtend 64 (BitVec.ofNat 64 (bytesToNat bs4n))).toNat)
      1 = some bs1n)
    (hlanelt : bytesToNat bs4n < 2 ^ 32)
    (hfr : lookupName s.env "%frame.0.lcssa1098" = some (.int 8 fr))
    (hstk : lookupName s.env "%stk" = some (.ptr K.stk))
    (hle : sp.toNat ≤ 519)
    (hlaneW : readBytes
      (writeBytes s.mem (bracePushAddr K sp) (natToBytes fr.toNat 1))
      (ep + inc.toNat * 4) 4 = some bs4n)
    (hbyteW : readBytes
      (writeBytes s.mem (bracePushAddr K sp) (natToBytes fr.toNat 1))
      (b + (BitVec.signExtend 64 (BitVec.ofNat 64 (bytesToNat bs4n))).toNat)
      1 = some bs1n) :
    ∃ s', Stage2NoEventWalkChain calls mem K s
        { K with tok := K.tok + 2, terms := K.terms + 3 } s' ∧
      s'.pc = "close_obj" ∧
      Stage2NoEventWalkInv
        { K with tok := K.tok + 2, terms := K.terms + 3 } mem s' := by
  by_cases hzero : sp.toNat = 0
  · -- the zero depth: `if.end19` true, no stack write
    let S1 := openZeroEnd23 s
    let S2 := openZeroEnd74 s sp
    have L0 : Stage2NoEventWalkLink calls K mem s K S1 :=
      link_ifEnd19_true h hpc hsp hzero
    have hsp1 : lookupName S1.env "%sp.0.lcssa1092.wide" = some (.int 32 sp) := by
      simp only [S1, openZeroEnd23, stage2NoEventWalkNext]
      exact lookupName_cons_other _ _ _ (by decide) hsp
    have hinc1 : lookupName S1.env "%inc.lcssa1129" = some (.int 64 inc) := by
      simp only [S1, openZeroEnd23, stage2NoEventWalkNext]
      exact lookupName_cons_other _ _ _ (by decide) hinc
    have hnep1 : lookupName S1.env "%nep" = some (.int 64 nep) := by
      simp only [S1, openZeroEnd23, stage2NoEventWalkNext]
      exact lookupName_cons_other _ _ _ (by decide) hnep
    have L1 : Stage2NoEventWalkLink calls K mem S1 K S2 :=
      link_ifEnd23 L0.inv' (by simp only [S1, openZeroEnd23, stage2NoEventWalkNext])
        hsp1 hinc1 hnep1 hult
    have hterms2 : lookupName S2.env "%terms.0.lcssa1080"
        = some (.int 64 terms) := by
      simp only [S2, openZeroEnd74, stage2NoEventWalkNext]
      repeat rw [lookupName_cons_ne _ _ (by decide)]
      exact hterms
    have htok2 : lookupName S2.env "%tokens.0.lcssa1074"
        = some (.int 64 tok) := by
      simp only [S2, openZeroEnd74, stage2NoEventWalkNext]
      repeat rw [lookupName_cons_ne _ _ (by decide)]
      exact htok
    have hep2 : lookupName S2.env "%ep" = some (.ptr ep) := by
      simp only [S2, openZeroEnd74, stage2NoEventWalkNext]
      repeat rw [lookupName_cons_ne _ _ (by decide)]
      exact hep
    have hb2 : lookupName S2.env "%b" = some (.ptr b) := by
      simp only [S2, openZeroEnd74, stage2NoEventWalkNext]
      repeat rw [lookupName_cons_ne _ _ (by decide)]
      exact hb
    have hinc2 : lookupName S2.env "%inc.lcssa1129" = some (.int 64 inc) := by
      simp only [S2, openZeroEnd74, stage2NoEventWalkNext]
      repeat rw [lookupName_cons_ne _ _ (by decide)]
      exact hinc
    have hk2 : lookupName S2.env "%k.0.lcssa1086" = some (.int 64 k) := by
      simp only [S2, openZeroEnd74, stage2NoEventWalkNext]
      repeat rw [lookupName_cons_ne _ _ (by decide)]
      exact hk
    have L2 := stage2NoEventRow_braceCloseTail (calls := calls) L1.inv'
      (by simp only [S2, openZeroEnd74, stage2NoEventWalkNext])
      hterms2 htok2 hep2 hb2 hinc2 hincLt hlane0 hlanelt hbyte0 hnext hk2 hmem hrel
    have LB : Stage2NoEventWalkChain calls mem K s K S2 :=
      Stage2NoEventWalkChain.tail L0 (Stage2NoEventWalkChain.tail L1
        (Stage2NoEventWalkChain.nil L1.inv'))
    have L : Stage2NoEventWalkChain calls mem K s
        { K with tok := K.tok + 2, terms := K.terms + 3 }
        (braceCloseState S2 ep b terms tok inc k bs4n bs1n) :=
      Stage2NoEventWalkChain.trans LB L2
    exact ⟨_, by simpa only [S2] using L,
      by simp only [braceCloseState, stage2NoEventWalkNext],
      Stage2NoEventWalkChain.inv L⟩
  · -- a live depth: the push arm, one stack byte
    have hpos : 1 ≤ sp.toNat := by omega
    let SP := stage2NoEventWalkStoredAt
      (("%cmp66.not", .int 1 1) ::
        ("%inc24", .int 32 (sp + BitVec.ofNat 32 1)) ::
        ("%arrayidx22", .ptr (bracePushAddr K sp)) ::
        ("%idxprom21", .int 64 (BitVec.ofNat 64
          ((sp + BitVec.ofNat 32 4294967295).toNat))) ::
        ("%sub", .int 32 (sp + BitVec.ofNat 32 4294967295)) ::
        ("%tobool.not", .int 1 (evalICmp .eq sp (BitVec.ofNat 32 0))) :: s.env)
      s (writeBytes s.mem (bracePushAddr K sp) (natToBytes fr.toNat 1))
      "if.end74" "if.end23"
    have LP : Stage2NoEventWalkChain calls mem K s K SP :=
      stage2NoEventRow_bracePush h hpc hsp hfr hstk hpos hle hinc hnep hult
    have htermsP : lookupName SP.env "%terms.0.lcssa1080"
        = some (.int 64 terms) := by
      simp only [SP, stage2NoEventWalkStoredAt]
      repeat rw [lookupName_cons_ne _ _ (by decide)]
      exact hterms
    have htokP : lookupName SP.env "%tokens.0.lcssa1074"
        = some (.int 64 tok) := by
      simp only [SP, stage2NoEventWalkStoredAt]
      repeat rw [lookupName_cons_ne _ _ (by decide)]
      exact htok
    have hepP : lookupName SP.env "%ep" = some (.ptr ep) := by
      simp only [SP, stage2NoEventWalkStoredAt]
      repeat rw [lookupName_cons_ne _ _ (by decide)]
      exact hep
    have hbP : lookupName SP.env "%b" = some (.ptr b) := by
      simp only [SP, stage2NoEventWalkStoredAt]
      repeat rw [lookupName_cons_ne _ _ (by decide)]
      exact hb
    have hincP : lookupName SP.env "%inc.lcssa1129" = some (.int 64 inc) := by
      simp only [SP, stage2NoEventWalkStoredAt]
      repeat rw [lookupName_cons_ne _ _ (by decide)]
      exact hinc
    have hkP : lookupName SP.env "%k.0.lcssa1086" = some (.int 64 k) := by
      simp only [SP, stage2NoEventWalkStoredAt]
      repeat rw [lookupName_cons_ne _ _ (by decide)]
      exact hk
    have hmemP : SP.mem
        = writeBytes s.mem (bracePushAddr K sp) (natToBytes fr.toNat 1) := by
      simp only [SP, stage2NoEventWalkStoredAt]
    have LM : Stage2NoEventWalkChain calls mem K SP
        { K with tok := K.tok + 2, terms := K.terms + 3 }
        (braceCloseState SP ep b terms tok inc k bs4n bs1n) :=
      stage2NoEventRow_braceCloseTail (calls := calls)
        (Stage2NoEventWalkChain.inv LP)
        (by simp only [SP, stage2NoEventWalkStoredAt]) htermsP htokP hepP hbP hincP
        hincLt (by rw [hmemP]; exact hlaneW) hlanelt
        (by rw [hmemP]; exact hbyteW) hnext hkP hmem hrel
    exact ⟨_, by simpa only [SP] using Stage2NoEventWalkChain.trans LP LM,
      by simp only [braceCloseState, stage2NoEventWalkNext],
      Stage2NoEventWalkChain.inv (Stage2NoEventWalkChain.trans LP LM)⟩

/-- `if.end45.peel` at the zero depth: the true arm, to `if.end51.peel`. -/
theorem link_ifEnd45peel_true {calls : Calls} {K : Stage2NoEventWalkCarry} {mem : Mem}
    {s : State} {sp : BitVec 32}
    (h : Stage2NoEventWalkInv K mem s) (hpc : s.pc = "if.end45.peel")
    (hsp : lookupName s.env "%sp.0.ph1403" = some (.int 32 sp))
    (hzero : sp.toNat = 0) :
    Stage2NoEventWalkLink calls K mem s K
      (stage2NoEventWalkNext
        (("%tobool46.not.peel", .int 1 1) :: s.env) s "if.end51.peel") := by
  have hsp0 : sp = BitVec.ofNat 32 0 := by
    rw [← BitVec.toNat_inj]
    simp [hzero]
  have hbit : evalICmp .eq sp (BitVec.ofNat 32 0) = (1 : BitVec 1) := by
    rw [hsp0]; decide
  have hcode : denoteCode calls ifEnd45peelBlock.instrs (stateAt s.env s) =
      some (stateAt (("%tobool46.not.peel", .int 1 1) :: s.env) s) := by
    rw [ifEnd45peelBlock, stage2NoEventWalk_denote_icmp_imm (calls := calls)
      (env := s.env) (s := s) (d := "%tobool46.not.peel") (a := "%sp.0.ph1403")
      (p := .eq) (w := 32) (c := BitVec.ofNat 32 0) hsp (is := [])]
    simp only [hbit, denoteCode_nil]
  exact stage2NoEventWalkLink_condbr_true
    (env' := ("%tobool46.not.peel", .int 1 1) :: s.env)
    h (by rw [hpc]; exact ifEnd45peelBlock_find) hcode rfl
    (by rw [lookupName_cons_self])

/-- **The `[]` zero-depth arm**: `if.then35.peel` → `if.end45.peel` (true) →
`if.end51.peel` → `if.end327.peel`, with no stack write. -/
theorem stage2NoEventRow_bracketZero {calls : Calls} {K : Stage2NoEventWalkCarry}
    {mem : Mem} {s : State} {sp : BitVec 32} {inc nep : BitVec 64}
    (h : Stage2NoEventWalkInv K mem s) (hpc : s.pc = "if.then35.peel")
    (hsp : lookupName s.env "%sp.0.ph1403" = some (.int 32 sp))
    (hinc : lookupName s.env "%inc.peel" = some (.int 64 inc))
    (hnep : lookupName s.env "%nep" = some (.int 64 nep))
    (hle : sp.toNat ≤ 519) (hzero : sp.toNat = 0)
    (hult : BitVec.ult inc nep = true) :
    Stage2NoEventWalkChain calls mem K s K
      (stage2NoEventWalkNext
        (("%cmp319.not.peel", .int 1 1) ::
          ("%tobool46.not.peel", .int 1 1) ::
          ("%exitcond.peel", .int 1 0) :: s.env)
        (stage2NoEventWalkNext
          (("%tobool46.not.peel", .int 1 1) ::
            ("%exitcond.peel", .int 1 0) :: s.env)
          (stage2NoEventWalkNext (("%exitcond.peel", .int 1 0) :: s.env)
            s "if.end45.peel") "if.end51.peel")
        "if.end327.peel") := by
  let S1 := stage2NoEventWalkNext (("%exitcond.peel", .int 1 0) :: s.env)
    s "if.end45.peel"
  let S2 := stage2NoEventWalkNext (("%tobool46.not.peel", .int 1 1) :: S1.env)
    S1 "if.end51.peel"
  let S3 := stage2NoEventWalkNext (("%cmp319.not.peel", .int 1 1) :: S2.env)
    S2 "if.end327.peel"
  have L1 : Stage2NoEventWalkLink calls K mem s K S1 :=
    link_ifThen35peel h hpc hsp hle
  have hsp1 : lookupName S1.env "%sp.0.ph1403" = some (.int 32 sp) := by
    simp only [S1, stage2NoEventWalkNext]
    exact lookupName_cons_other _ _ _ (by decide) hsp
  have L2 : Stage2NoEventWalkLink calls K mem S1 K S2 :=
    link_ifEnd45peel_true L1.inv' (by simp only [S1, stage2NoEventWalkNext])
      hsp1 hzero
  have hinc2 : lookupName S2.env "%inc.peel" = some (.int 64 inc) := by
    simp only [S2, S1, stage2NoEventWalkNext]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact hinc
  have hnep2 : lookupName S2.env "%nep" = some (.int 64 nep) := by
    simp only [S2, S1, stage2NoEventWalkNext]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact hnep
  have L3 : Stage2NoEventWalkLink calls K mem S2 K S3 :=
    link_ifEnd51peel L2.inv' (by simp only [S2, S1, stage2NoEventWalkNext])
      hinc2 hnep2 hult
  simpa only [S1, S2, S3, stage2NoEventWalkNext] using
    (Stage2NoEventWalkChain.tail L1 (Stage2NoEventWalkChain.tail L2
      (Stage2NoEventWalkChain.tail L3 (Stage2NoEventWalkChain.nil L3.inv'))))

/-- The `]` row with the count guard derived, not assumed. -/
theorem row_closeBracket_of_bound {calls : Calls} {K : Stage2NoEventWalkCarry}
    {mem : Mem} {s : State} {inc : BitVec 64} {ep b : Nat} {bs4 bs1 : List UInt8}
    {sp : BitVec 32} {k terms tok : BitVec 64} {alen arena : BitVec 64}
    {stk : Nat} {a : Nat} {bs : List UInt8}
    (h : Stage2NoEventWalkInv K mem s) (hpc : s.pc = "if.end327.peel")
    (hinc : lookupName s.env "%inc.peel" = some (.int 64 inc))
    (hep : lookupName s.env "%ep" = some (.ptr ep))
    (hb : lookupName s.env "%b" = some (.ptr b))
    (hincLt : inc.toNat < 2 ^ 63)
    (hlane : readBytes s.mem (ep + inc.toNat * 4) 4 = some bs4)
    (hlanelt : bytesToNat bs4 < 2 ^ 32)
    (hbyte1 : readBytes s.mem
      (b + (BitVec.signExtend 64 (BitVec.ofNat 64 (bytesToNat bs4))).toNat) 1 = some bs1)
    (hb93 : bytesToNat bs1 = 93)
    (hsp : lookupName s.env "%sp.0.ph1403" = some (.int 32 sp))
    (hk : lookupName s.env "%k.0.ph1404" = some (.int 64 k))
    (htr : lookupName s.env "%terms.0.ph1407" = some (.int 64 terms))
    (htokr : lookupName s.env "%tokens.0.ph1408" = some (.int 64 tok))
    (halen : lookupName s.env "%alen.0.ph1405" = some (.int 64 alen))
    (harena : lookupName s.env "%arena.0.ph1406" = some (.int 64 arena))
    (hstk : lookupName s.env "%stk" = some (.ptr stk))
    (hposS : sp.toNat ≠ 0)
    (hbyte : readBytes s.mem a 1 = some bs)
    (ha : a = closeReadAddr stk (sp + BitVec.ofNat 32 4294967295).toNat)
    (hmem : K.pos ∈ K.ent) (hrel : K.tok + 2 ≤ K.pos) :
    Stage2NoEventWalkChain calls mem K s
      { K with tok := K.tok + 2, terms := K.terms + 7 }
      (bracketRead (bracketArr (bracketCounts (bracketEntry s inc ep b bs4 bs1)
        sp k tok terms) sp (k + BitVec.ofNat 64 2) alen arena
        (terms + BitVec.ofNat 64 7) (tok + BitVec.ofNat 64 2)) sp a bs) :=
  row_closeBracket h hpc hinc hep hb hincLt hlane hlanelt hbyte1 hb93
    hsp hk htr htokr (Stage2NoEventWalkInv.htok h hmem hrel)
    halen harena hstk hposS hbyte ha

/-- The bracket push's stack address, named once. -/
def bracketPushAddr (K : Stage2NoEventWalkCarry) (v1 : BitVec 64) : Nat :=
  K.stk + (BitVec.signExtend 64 (v1 + BitVec.ofNat 64 18446744073709551615)).toNat

/-- **The `[]` push arm**: `if.then35.peel` through `stage2NoEventRow_bracketPush`
to `if.end327.peel`, then the derived `]` row to the pop at `after_value`. -/
theorem stage2NoEventRow_closePush {calls : Calls} {K : Stage2NoEventWalkCarry}
    {mem : Mem} {s : State} {sp : BitVec 32} {v1 inc nep : BitVec 64}
    {fr : BitVec 8} {ep b : Nat} {bs4 bs1 : List UInt8}
    {k terms tok : BitVec 64} {alen arena : BitVec 64}
    {stk : Nat} {a : Nat} {bs : List UInt8}
    (h : Stage2NoEventWalkInv K mem s) (hpc : s.pc = "if.then35.peel")
    (hsp : lookupName s.env "%sp.0.ph1403" = some (.int 32 sp))
    (h1 : lookupName s.env "%1" = some (.int 64 v1))
    (hfr : lookupName s.env "%frame.0.ph1402" = some (.int 8 fr))
    (hstk : lookupName s.env "%stk" = some (.ptr K.stk))
    (hinc : lookupName s.env "%inc.peel" = some (.int 64 inc))
    (hnep : lookupName s.env "%nep" = some (.int 64 nep))
    (hle : sp.toNat ≤ 519) (hposS : sp.toNat ≠ 0)
    (hpos : 1 ≤ v1.toNat) (hle1 : v1.toNat ≤ 519)
    (hult : BitVec.ult inc nep = true)
    (hep : lookupName s.env "%ep" = some (.ptr ep))
    (hb : lookupName s.env "%b" = some (.ptr b))
    (hincLt : inc.toNat < 2 ^ 63)
    (hlaneW : readBytes
      (writeBytes s.mem (bracketPushAddr K v1) (natToBytes fr.toNat 1))
      (ep + inc.toNat * 4) 4 = some bs4)
    (hlanelt : bytesToNat bs4 < 2 ^ 32)
    (hbyte1W : readBytes
      (writeBytes s.mem (bracketPushAddr K v1) (natToBytes fr.toNat 1))
      (b + (BitVec.signExtend 64 (BitVec.ofNat 64 (bytesToNat bs4))).toNat) 1 = some bs1)
    (hb93 : bytesToNat bs1 = 93)
    (hk : lookupName s.env "%k.0.ph1404" = some (.int 64 k))
    (htr : lookupName s.env "%terms.0.ph1407" = some (.int 64 terms))
    (htokr : lookupName s.env "%tokens.0.ph1408" = some (.int 64 tok))
    (halen : lookupName s.env "%alen.0.ph1405" = some (.int 64 alen))
    (harena : lookupName s.env "%arena.0.ph1406" = some (.int 64 arena))
    (hbyteW : readBytes
      (writeBytes s.mem (bracketPushAddr K v1) (natToBytes fr.toNat 1))
      a 1 = some bs)
    (ha : a = closeReadAddr K.stk (sp + BitVec.ofNat 32 4294967295).toNat)
    (hmem : K.pos ∈ K.ent) (hrel : K.tok + 2 ≤ K.pos) :
    Stage2NoEventWalkChain calls mem K s
      { K with tok := K.tok + 2, terms := K.terms + 7 }
      (bracketRead (bracketArr (bracketCounts
        (bracketEntry (stage2NoEventWalkStoredAt
          (("%cmp319.not.peel", .int 1 1) ::
            ("%arrayidx50.peel", .ptr (bracketPushAddr K v1)) ::
            ("%4", .int 64 (v1 + BitVec.ofNat 64 18446744073709551615)) ::
            ("%tobool46.not.peel", .int 1 0) ::
            ("%exitcond.peel", .int 1 0) :: s.env)
          s (writeBytes s.mem (bracketPushAddr K v1) (natToBytes fr.toNat 1))
          "if.end327.peel" "if.end51.peel")
          inc ep b bs4 bs1) sp k tok terms) sp (k + BitVec.ofNat 64 2)
        alen arena (terms + BitVec.ofNat 64 7) (tok + BitVec.ofNat 64 2)) sp a bs) := by
  let SP := stage2NoEventWalkStoredAt
    (("%cmp319.not.peel", .int 1 1) ::
      ("%arrayidx50.peel", .ptr (bracketPushAddr K v1)) ::
      ("%4", .int 64 (v1 + BitVec.ofNat 64 18446744073709551615)) ::
      ("%tobool46.not.peel", .int 1 0) ::
      ("%exitcond.peel", .int 1 0) :: s.env)
    s (writeBytes s.mem (bracketPushAddr K v1) (natToBytes fr.toNat 1))
    "if.end327.peel" "if.end51.peel"
  have LP : Stage2NoEventWalkChain calls mem K s K SP :=
    stage2NoEventRow_bracketPush h hpc hsp h1 hfr hstk hinc hnep hle hposS hpos hle1 hult
  have hincP : lookupName SP.env "%inc.peel" = some (.int 64 inc) := by
    simp only [SP, stage2NoEventWalkStoredAt]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact hinc
  have hepP : lookupName SP.env "%ep" = some (.ptr ep) := by
    simp only [SP, stage2NoEventWalkStoredAt]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact hep
  have hbP : lookupName SP.env "%b" = some (.ptr b) := by
    simp only [SP, stage2NoEventWalkStoredAt]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact hb
  have hspP : lookupName SP.env "%sp.0.ph1403" = some (.int 32 sp) := by
    simp only [SP, stage2NoEventWalkStoredAt]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact hsp
  have hkP : lookupName SP.env "%k.0.ph1404" = some (.int 64 k) := by
    simp only [SP, stage2NoEventWalkStoredAt]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact hk
  have htrP : lookupName SP.env "%terms.0.ph1407" = some (.int 64 terms) := by
    simp only [SP, stage2NoEventWalkStoredAt]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact htr
  have htokrP : lookupName SP.env "%tokens.0.ph1408" = some (.int 64 tok) := by
    simp only [SP, stage2NoEventWalkStoredAt]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact htokr
  have halenP : lookupName SP.env "%alen.0.ph1405" = some (.int 64 alen) := by
    simp only [SP, stage2NoEventWalkStoredAt]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact halen
  have harenaP : lookupName SP.env "%arena.0.ph1406" = some (.int 64 arena) := by
    simp only [SP, stage2NoEventWalkStoredAt]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact harena
  have hstkP : lookupName SP.env "%stk" = some (.ptr K.stk) := by
    simp only [SP, stage2NoEventWalkStoredAt]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact hstk
  have hmemP : SP.mem
      = writeBytes s.mem (bracketPushAddr K v1) (natToBytes fr.toNat 1) := by
    simp only [SP, stage2NoEventWalkStoredAt]
  have LR : Stage2NoEventWalkChain calls mem K SP
      { K with tok := K.tok + 2, terms := K.terms + 7 }
      (bracketRead (bracketArr (bracketCounts (bracketEntry SP inc ep b bs4 bs1)
        sp k tok terms) sp (k + BitVec.ofNat 64 2) alen arena
        (terms + BitVec.ofNat 64 7) (tok + BitVec.ofNat 64 2)) sp a bs) :=
    row_closeBracket_of_bound (Stage2NoEventWalkChain.inv LP)
      (by simp only [SP, stage2NoEventWalkStoredAt])
      hincP hepP hbP hincLt
      (by rw [hmemP]; exact hlaneW) hlanelt
      (by rw [hmemP]; exact hbyte1W) hb93
      hspP hkP htrP htokrP halenP harenaP hstkP hposS
      (by rw [hmemP]; exact hbyteW) ha hmem hrel
  simpa only [SP] using Stage2NoEventWalkChain.trans LP LR

/-- The state `close_arr` delivers at the zero depth: the direct handoff to
`after_value`, with no pop. -/
def bracketArrValue (s2 : State) (sp3 : BitVec 32) (k5 alen arena terms7 toks : BitVec 64) :
    State :=
  stage2NoEventWalkNext (cells (closeArrAllCells sp3 k5 alen arena terms7 toks) s2.env)
    s2 "after_value"

/-- `close_arr` at the zero depth: the true arm, to `after_value`. -/
theorem link_closeArr_true {calls : Calls} {K : Stage2NoEventWalkCarry} {mem : Mem}
    {s : State} {sp3 : BitVec 32} {k5 alen arena terms7 toks : BitVec 64}
    (h : Stage2NoEventWalkInv K mem s) (hpc : s.pc = "close_arr")
    (hpre : s.pre = some "if.then334")
    (hsp : lookupName s.env "%sp.0.lcssa1096.wide" = some (.int 32 sp3))
    (hinc335 : lookupName s.env "%inc335" = some (.int 64 k5))
    (halen : lookupName s.env "%alen.0.ph1405" = some (.int 64 alen))
    (harena : lookupName s.env "%arena.0.ph1406" = some (.int 64 arena))
    (hadd338 : lookupName s.env "%add338" = some (.int 64 terms7))
    (hinc337 : lookupName s.env "%inc337" = some (.int 64 toks))
    (hzero : sp3.toNat = 0) :
    Stage2NoEventWalkLink calls K mem s K
      (bracketArrValue s sp3 k5 alen arena terms7 toks) := by
  have h1 := closeArr_phi_denote (calls := calls) (env := s.env) (s := s)
    (sp3 := sp3) (k5 := k5) (alen := alen) (arena := arena) (terms7 := terms7)
    (toks := toks) hpre hsp hinc335 halen harena hadd338 hinc337
  have h2 := closeArr_test_denote (calls := calls) (env := s.env) (s := s)
    (sp3 := sp3) (k5 := k5) (alen := alen) (arena := arena) (terms7 := terms7)
    (toks := toks)
  have hsp0 : sp3 = BitVec.ofNat 32 0 := by
    rw [← BitVec.toNat_inj]
    simp [hzero]
  have hbit : evalICmp .eq sp3 (BitVec.ofNat 32 0) = (1 : BitVec 1) := by
    rw [hsp0]; decide
  have hcode : denoteCode calls closeArrBlock.instrs (stateAt s.env s) =
      some (stateAt (cells (closeArrAllCells sp3 k5 alen arena terms7 toks) s.env) s) := by
    rw [closeArr_split]
    rw [denoteCode_append_apply (a := closeArrPhiInstrs) (b := closeArrRest)
      h1 (by decide)]
    exact h2
  refine stage2NoEventWalkLink_condbr_true (env' :=
    cells (closeArrAllCells sp3 k5 alen arena terms7 toks) s.env)
    h (by rw [hpc]; exact closeArrBlock_find) hcode rfl ?_
  rw [lookupName_cells_of_some (cs := closeArrAllCells sp3 k5 alen arena terms7 toks)
    (n := "%tobool349.not") (env := s.env)
    (by rw [closeArrAllCells, closeArrTail, closeArrPhiCells]; cells_lk)]
  rw [hbit]

/-- **`row_closeBracketZero`**: `if.end327.peel` → `if.then334` → `close_arr`'s
zero-depth true arm, to `after_value`, with the derived count guard. -/
theorem row_closeBracketZero {calls : Calls} {K : Stage2NoEventWalkCarry} {mem : Mem}
    {s : State} {inc : BitVec 64} {ep b : Nat} {bs4 bs1 : List UInt8}
    {sp : BitVec 32} {k terms tok : BitVec 64} {alen arena : BitVec 64}
    {stk : Nat}
    (h : Stage2NoEventWalkInv K mem s) (hpc : s.pc = "if.end327.peel")
    (hinc : lookupName s.env "%inc.peel" = some (.int 64 inc))
    (hep : lookupName s.env "%ep" = some (.ptr ep))
    (hb : lookupName s.env "%b" = some (.ptr b))
    (hincLt : inc.toNat < 2 ^ 63)
    (hlane : readBytes s.mem (ep + inc.toNat * 4) 4 = some bs4)
    (hlanelt : bytesToNat bs4 < 2 ^ 32)
    (hbyte1 : readBytes s.mem
      (b + (BitVec.signExtend 64 (BitVec.ofNat 64 (bytesToNat bs4))).toNat) 1 = some bs1)
    (hb93 : bytesToNat bs1 = 93)
    (hsp : lookupName s.env "%sp.0.ph1403" = some (.int 32 sp))
    (hk : lookupName s.env "%k.0.ph1404" = some (.int 64 k))
    (htr : lookupName s.env "%terms.0.ph1407" = some (.int 64 terms))
    (htokr : lookupName s.env "%tokens.0.ph1408" = some (.int 64 tok))
    (halen : lookupName s.env "%alen.0.ph1405" = some (.int 64 alen))
    (harena : lookupName s.env "%arena.0.ph1406" = some (.int 64 arena))
    (hstk : lookupName s.env "%stk" = some (.ptr stk))
    (hzero : sp.toNat = 0)
    (hmem : K.pos ∈ K.ent) (hrel : K.tok + 2 ≤ K.pos) :
    Stage2NoEventWalkChain calls mem K s
      { K with tok := K.tok + 2, terms := K.terms + 7 }
      (bracketArrValue (bracketCounts (bracketEntry s inc ep b bs4 bs1) sp k tok terms)
        sp (k + BitVec.ofNat 64 2) alen arena (terms + BitVec.ofNat 64 7)
        (tok + BitVec.ofNat 64 2)) := by
  let S1 := bracketEntry s inc ep b bs4 bs1
  let S2 := bracketCounts S1 sp k tok terms
  let K1 : Stage2NoEventWalkCarry := { K with tok := K.tok + 2, terms := K.terms + 7 }
  have L0 : Stage2NoEventWalkLink calls K mem s K S1 :=
    link_ifEnd327peel h hpc hinc hep hb hincLt hlane hlanelt hbyte1 hb93
  have hsp1 : lookupName S1.env "%sp.0.ph1403" = some (.int 32 sp) := by
    simp only [S1, bracketEntry, stage2NoEventWalkNext]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact hsp
  have hk1 : lookupName S1.env "%k.0.ph1404" = some (.int 64 k) := by
    simp only [S1, bracketEntry, stage2NoEventWalkNext]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact hk
  have htr1 : lookupName S1.env "%terms.0.ph1407" = some (.int 64 terms) := by
    simp only [S1, bracketEntry, stage2NoEventWalkNext]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact htr
  have htokr1 : lookupName S1.env "%tokens.0.ph1408" = some (.int 64 tok) := by
    simp only [S1, bracketEntry, stage2NoEventWalkNext]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact htokr
  have L1 : Stage2NoEventWalkLink calls K mem S1 K1 S2 :=
    link_ifThen334_of_bound (sp := sp) (k := k) (terms := terms) (tok := tok)
      L0.inv' (by simp only [S1, bracketEntry, stage2NoEventWalkNext])
      (by simp only [S1, bracketEntry, stage2NoEventWalkNext]; rw [hpc])
      hsp1 hk1 htr1 htokr1 hmem hrel
  have hsp2 : lookupName S2.env "%sp.0.lcssa1096.wide" = some (.int 32 sp) := by
    simp only [S2, bracketCounts, stage2NoEventWalkNext]
    exact lookupName_cells_of_some (cs := ifThen334AllCells sp k tok terms)
      (n := "%sp.0.lcssa1096.wide") (env := S1.env)
      (by rw [ifThen334AllCells, ifThen334Cells, ifThen334PhiCells]; cells_lk)
  have hinc335 : lookupName S2.env "%inc335"
      = some (.int 64 (k + BitVec.ofNat 64 2)) := by
    simp only [S2, bracketCounts, stage2NoEventWalkNext]
    exact lookupName_cells_of_some (cs := ifThen334AllCells sp k tok terms)
      (n := "%inc335") (env := S1.env)
      (by rw [ifThen334AllCells, ifThen334Cells, ifThen334PhiCells]; cells_lk)
  have halen2 : lookupName S2.env "%alen.0.ph1405" = some (.int 64 alen) := by
    simp only [S2, bracketCounts, stage2NoEventWalkNext]
    rw [lookupName_cells_of_notin (cs := ifThen334AllCells sp k tok terms)
      (n := "%alen.0.ph1405") (env := S1.env)
      (by rw [ifThen334AllCells, ifThen334Cells, ifThen334PhiCells]; simp)]
    simp only [S1, bracketEntry, stage2NoEventWalkNext]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact halen
  have harena2 : lookupName S2.env "%arena.0.ph1406" = some (.int 64 arena) := by
    simp only [S2, bracketCounts, stage2NoEventWalkNext]
    rw [lookupName_cells_of_notin (cs := ifThen334AllCells sp k tok terms)
      (n := "%arena.0.ph1406") (env := S1.env)
      (by rw [ifThen334AllCells, ifThen334Cells, ifThen334PhiCells]; simp)]
    simp only [S1, bracketEntry, stage2NoEventWalkNext]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact harena
  have hadd338 : lookupName S2.env "%add338"
      = some (.int 64 (terms + BitVec.ofNat 64 7)) := by
    simp only [S2, bracketCounts, stage2NoEventWalkNext]
    exact lookupName_cells_of_some (cs := ifThen334AllCells sp k tok terms)
      (n := "%add338") (env := S1.env)
      (by rw [ifThen334AllCells, ifThen334Cells, ifThen334PhiCells]; cells_lk)
  have hinc337 : lookupName S2.env "%inc337"
      = some (.int 64 (tok + BitVec.ofNat 64 2)) := by
    simp only [S2, bracketCounts, stage2NoEventWalkNext]
    exact lookupName_cells_of_some (cs := ifThen334AllCells sp k tok terms)
      (n := "%inc337") (env := S1.env)
      (by rw [ifThen334AllCells, ifThen334Cells, ifThen334PhiCells]; cells_lk)
  have L2 : Stage2NoEventWalkLink calls K1 mem S2 K1
      (bracketArrValue S2 sp (k + BitVec.ofNat 64 2) alen arena
        (terms + BitVec.ofNat 64 7) (tok + BitVec.ofNat 64 2)) :=
    link_closeArr_true (sp3 := sp) (k5 := k + BitVec.ofNat 64 2)
      (terms7 := terms + BitVec.ofNat 64 7) (toks := tok + BitVec.ofNat 64 2)
      L1.inv' (by simp only [S2, bracketCounts, stage2NoEventWalkNext])
      (by simp only [S2, bracketCounts, stage2NoEventWalkNext, S1, bracketEntry])
      hsp2 hinc335 halen2 harena2 hadd338 hinc337 hzero
  simpa only [S1, S2, K1] using
    (Stage2NoEventWalkChain.tail L0 (Stage2NoEventWalkChain.tail L1
      (Stage2NoEventWalkChain.tail L2 (Stage2NoEventWalkChain.nil L2.inv'))))

/-- **The open arm at the zero depth**: `if.end19`'s true arm, `if.end23`,
`if.end74`, the next-entry dispatch and the `{}` close, to `close_obj`. -/
theorem stage2NoEventRow_openZero {calls : Calls} {K : Stage2NoEventWalkCarry}
    {mem : Mem} {s : State} {sp : BitVec 32} {terms tok inc k nep : BitVec 64}
    {ep b : Nat} {bs4n bs1n : List UInt8}
    (h : Stage2NoEventWalkInv K mem s) (hpc : s.pc = "if.end19")
    (hsp : lookupName s.env "%sp.0.lcssa1092.wide" = some (.int 32 sp))
    (hterms : lookupName s.env "%terms.0.lcssa1080" = some (.int 64 terms))
    (htok : lookupName s.env "%tokens.0.lcssa1074" = some (.int 64 tok))
    (hep : lookupName s.env "%ep" = some (.ptr ep))
    (hb : lookupName s.env "%b" = some (.ptr b))
    (hinc : lookupName s.env "%inc.lcssa1129" = some (.int 64 inc))
    (hnep : lookupName s.env "%nep" = some (.int 64 nep))
    (hult : BitVec.ult inc nep = true)
    (hincLt : inc.toNat < 2 ^ 63)
    (hnext : bytesToNat bs1n = 125)
    (hk : lookupName s.env "%k.0.lcssa1086" = some (.int 64 k))
    (hmem : K.pos ∈ K.ent) (hrel : K.tok + 2 ≤ K.pos)
    (hlane : readBytes s.mem (ep + inc.toNat * 4) 4 = some bs4n)
    (hbyte : readBytes s.mem
      (b + (BitVec.signExtend 64 (BitVec.ofNat 64 (bytesToNat bs4n))).toNat)
      1 = some bs1n)
    (hlanelt : bytesToNat bs4n < 2 ^ 32)
    (hzero : sp.toNat = 0) :
    Stage2NoEventWalkChain calls mem K s
      { K with tok := K.tok + 2, terms := K.terms + 3 }
      (braceCloseState (openZeroEnd74 s sp) ep b terms tok inc k bs4n bs1n) := by
  let S1 := openZeroEnd23 s
  let S2 := openZeroEnd74 s sp
  have L0 : Stage2NoEventWalkLink calls K mem s K S1 :=
    link_ifEnd19_true h hpc hsp hzero
  have hsp1 : lookupName S1.env "%sp.0.lcssa1092.wide" = some (.int 32 sp) := by
    simp only [S1, openZeroEnd23, stage2NoEventWalkNext]
    exact lookupName_cons_other _ _ _ (by decide) hsp
  have hinc1 : lookupName S1.env "%inc.lcssa1129" = some (.int 64 inc) := by
    simp only [S1, openZeroEnd23, stage2NoEventWalkNext]
    exact lookupName_cons_other _ _ _ (by decide) hinc
  have hnep1 : lookupName S1.env "%nep" = some (.int 64 nep) := by
    simp only [S1, openZeroEnd23, stage2NoEventWalkNext]
    exact lookupName_cons_other _ _ _ (by decide) hnep
  have L1 : Stage2NoEventWalkLink calls K mem S1 K S2 :=
    link_ifEnd23 L0.inv' (by simp only [S1, openZeroEnd23, stage2NoEventWalkNext])
      hsp1 hinc1 hnep1 hult
  have hterms2 : lookupName S2.env "%terms.0.lcssa1080" = some (.int 64 terms) := by
    simp only [S2, openZeroEnd74, stage2NoEventWalkNext]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact hterms
  have htok2 : lookupName S2.env "%tokens.0.lcssa1074" = some (.int 64 tok) := by
    simp only [S2, openZeroEnd74, stage2NoEventWalkNext]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact htok
  have hep2 : lookupName S2.env "%ep" = some (.ptr ep) := by
    simp only [S2, openZeroEnd74, stage2NoEventWalkNext]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact hep
  have hb2 : lookupName S2.env "%b" = some (.ptr b) := by
    simp only [S2, openZeroEnd74, stage2NoEventWalkNext]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact hb
  have hinc2 : lookupName S2.env "%inc.lcssa1129" = some (.int 64 inc) := by
    simp only [S2, openZeroEnd74, stage2NoEventWalkNext]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact hinc
  have hk2 : lookupName S2.env "%k.0.lcssa1086" = some (.int 64 k) := by
    simp only [S2, openZeroEnd74, stage2NoEventWalkNext]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact hk
  have L2 := stage2NoEventRow_braceCloseTail (calls := calls) L1.inv'
    (by simp only [S2, openZeroEnd74, stage2NoEventWalkNext])
    hterms2 htok2 hep2 hb2 hinc2 hincLt hlane hlanelt hbyte hnext hk2 hmem hrel
  have LB : Stage2NoEventWalkChain calls mem K s K S2 :=
    Stage2NoEventWalkChain.tail L0 (Stage2NoEventWalkChain.tail L1
      (Stage2NoEventWalkChain.nil L1.inv'))
  simpa only [S1, S2, openZeroEnd74] using Stage2NoEventWalkChain.trans LB L2

/-- **The close arm at the zero depth**: `if.then35.peel` through the true
`if.end45.peel`, `if.end51.peel`, `if.end327.peel`, the `]` count and
`close_arr`'s zero-depth true arm, to `after_value`. -/
theorem stage2NoEventRow_closeZero {calls : Calls} {K : Stage2NoEventWalkCarry}
    {mem : Mem} {s : State} {sp : BitVec 32} {inc nep : BitVec 64}
    {ep b : Nat} {bs4 bs1 : List UInt8} {k terms tok : BitVec 64}
    {alen arena : BitVec 64} {stk : Nat}
    (h : Stage2NoEventWalkInv K mem s) (hpc : s.pc = "if.then35.peel")
    (hsp : lookupName s.env "%sp.0.ph1403" = some (.int 32 sp))
    (hinc : lookupName s.env "%inc.peel" = some (.int 64 inc))
    (hnep : lookupName s.env "%nep" = some (.int 64 nep))
    (hle : sp.toNat ≤ 519) (hult : BitVec.ult inc nep = true)
    (hep : lookupName s.env "%ep" = some (.ptr ep))
    (hb : lookupName s.env "%b" = some (.ptr b))
    (hincLt : inc.toNat < 2 ^ 63)
    (hlane : readBytes s.mem (ep + inc.toNat * 4) 4 = some bs4)
    (hlanelt : bytesToNat bs4 < 2 ^ 32)
    (hbyte1 : readBytes s.mem
      (b + (BitVec.signExtend 64 (BitVec.ofNat 64 (bytesToNat bs4))).toNat) 1 = some bs1)
    (hb93 : bytesToNat bs1 = 93)
    (hk : lookupName s.env "%k.0.ph1404" = some (.int 64 k))
    (htr : lookupName s.env "%terms.0.ph1407" = some (.int 64 terms))
    (htokr : lookupName s.env "%tokens.0.ph1408" = some (.int 64 tok))
    (halen : lookupName s.env "%alen.0.ph1405" = some (.int 64 alen))
    (harena : lookupName s.env "%arena.0.ph1406" = some (.int 64 arena))
    (hstk : lookupName s.env "%stk" = some (.ptr stk))
    (hzero : sp.toNat = 0)
    (hmem : K.pos ∈ K.ent) (hrel : K.tok + 2 ≤ K.pos) :
    Stage2NoEventWalkChain calls mem K s
      { K with tok := K.tok + 2, terms := K.terms + 7 }
      (bracketArrValue (bracketCounts
        (bracketEntry (stage2NoEventWalkNext
          (("%cmp319.not.peel", .int 1 1) ::
            ("%tobool46.not.peel", .int 1 1) ::
            ("%exitcond.peel", .int 1 0) :: s.env)
          (stage2NoEventWalkNext
            (("%tobool46.not.peel", .int 1 1) ::
              ("%exitcond.peel", .int 1 0) :: s.env)
            (stage2NoEventWalkNext (("%exitcond.peel", .int 1 0) :: s.env)
              s "if.end45.peel") "if.end51.peel") "if.end327.peel")
          inc ep b bs4 bs1) sp k tok terms) sp (k + BitVec.ofNat 64 2)
        alen arena (terms + BitVec.ofNat 64 7) (tok + BitVec.ofNat 64 2)) := by
  let S1 := stage2NoEventWalkNext (("%exitcond.peel", .int 1 0) :: s.env)
    s "if.end45.peel"
  let S2 := stage2NoEventWalkNext (("%tobool46.not.peel", .int 1 1) :: S1.env)
    S1 "if.end51.peel"
  let S3 := stage2NoEventWalkNext (("%cmp319.not.peel", .int 1 1) :: S2.env)
    S2 "if.end327.peel"
  have L1 : Stage2NoEventWalkLink calls K mem s K S1 :=
    link_ifThen35peel h hpc hsp hle
  have hsp1 : lookupName S1.env "%sp.0.ph1403" = some (.int 32 sp) := by
    simp only [S1, stage2NoEventWalkNext]
    exact lookupName_cons_other _ _ _ (by decide) hsp
  have L2 : Stage2NoEventWalkLink calls K mem S1 K S2 :=
    link_ifEnd45peel_true L1.inv' (by simp only [S1, stage2NoEventWalkNext])
      hsp1 hzero
  have hinc2 : lookupName S2.env "%inc.peel" = some (.int 64 inc) := by
    simp only [S2, S1, stage2NoEventWalkNext]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact hinc
  have hnep2 : lookupName S2.env "%nep" = some (.int 64 nep) := by
    simp only [S2, S1, stage2NoEventWalkNext]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact hnep
  have L3 : Stage2NoEventWalkLink calls K mem S2 K S3 :=
    link_ifEnd51peel L2.inv' (by simp only [S2, S1, stage2NoEventWalkNext])
      hinc2 hnep2 hult
  have hinc3 : lookupName S3.env "%inc.peel" = some (.int 64 inc) := by
    simp only [S3, S2, S1, stage2NoEventWalkNext]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact hinc
  have hep3 : lookupName S3.env "%ep" = some (.ptr ep) := by
    simp only [S3, S2, S1, stage2NoEventWalkNext]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact hep
  have hb3 : lookupName S3.env "%b" = some (.ptr b) := by
    simp only [S3, S2, S1, stage2NoEventWalkNext]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact hb
  have hsp3 : lookupName S3.env "%sp.0.ph1403" = some (.int 32 sp) := by
    simp only [S3, S2, S1, stage2NoEventWalkNext]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact hsp
  have hk3 : lookupName S3.env "%k.0.ph1404" = some (.int 64 k) := by
    simp only [S3, S2, S1, stage2NoEventWalkNext]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact hk
  have htr3 : lookupName S3.env "%terms.0.ph1407" = some (.int 64 terms) := by
    simp only [S3, S2, S1, stage2NoEventWalkNext]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact htr
  have htokr3 : lookupName S3.env "%tokens.0.ph1408" = some (.int 64 tok) := by
    simp only [S3, S2, S1, stage2NoEventWalkNext]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact htokr
  have halen3 : lookupName S3.env "%alen.0.ph1405" = some (.int 64 alen) := by
    simp only [S3, S2, S1, stage2NoEventWalkNext]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact halen
  have harena3 : lookupName S3.env "%arena.0.ph1406" = some (.int 64 arena) := by
    simp only [S3, S2, S1, stage2NoEventWalkNext]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact harena
  have hstk3 : lookupName S3.env "%stk" = some (.ptr stk) := by
    simp only [S3, S2, S1, stage2NoEventWalkNext]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact hstk
  have L4 : Stage2NoEventWalkChain calls mem K S3
      { K with tok := K.tok + 2, terms := K.terms + 7 }
      (bracketArrValue (bracketCounts (bracketEntry S3 inc ep b bs4 bs1)
        sp k tok terms) sp (k + BitVec.ofNat 64 2) alen arena
        (terms + BitVec.ofNat 64 7) (tok + BitVec.ofNat 64 2)) :=
    row_closeBracketZero L3.inv'
      (by simp only [S3, S2, S1, stage2NoEventWalkNext])
      hinc3 hep3 hb3 hincLt hlane hlanelt hbyte1 hb93 hsp3 hk3 htr3 htokr3
      halen3 harena3 hstk3 hzero hmem hrel
  have L : Stage2NoEventWalkChain calls mem K s K S3 :=
    Stage2NoEventWalkChain.tail L1 (Stage2NoEventWalkChain.tail L2
      (Stage2NoEventWalkChain.tail L3 (Stage2NoEventWalkChain.nil L3.inv')))
  simpa only [S1, S2, S3, stage2NoEventWalkNext] using
    Stage2NoEventWalkChain.trans L L4

/-- The `if.then9` state the head's `{` dispatch delivers. -/
def openHead9 (s : State) (k : BitVec 64) (bs4 : List UInt8) (ep b : Nat)
    (bs1 : List UInt8) : State :=
  stage2NoEventWalkNext (openEnv3 s.env k bs4 ep b bs1)
    (stage2NoEventWalkNext (openEnv2 s.env k bs4 ep b bs1)
      (stage2NoEventWalkNext (openEnv1 s.env k bs4 ep b bs1)
        (stage2NoEventWalkNext (openEnv0 s.env k bs4 ep b bs1) s "NodeBlock5")
        "NodeBlock") "LeafBlock3")
    "if.then9"

/-- The `if.end19` state after the `if.then9` guard. -/
def openHead19 (s : State) (k : BitVec 64) (bs4 : List UInt8) (ep b : Nat)
    (bs1 : List UInt8) : State :=
  stage2NoEventWalkNext (ifThen9Env1 (openHead9 s k bs4 ep b bs1).env k bs4)
    (openHead9 s k bs4 ep b bs1) "if.end19"

/-- The head's `NodeBlock5` state. -/
def closeHead1 (s : State) (k : BitVec 64) (bs4 : List UInt8) (ep b : Nat)
    (bs1 : List UInt8) : State :=
  stage2NoEventWalkNext (openEnv0 s.env k bs4 ep b bs1) s "NodeBlock5"

/-- The head's `if.then35.peel` state (the `[` dispatch's entry). -/
def closeHead35 (s : State) (k : BitVec 64) (bs4 : List UInt8) (ep b : Nat)
    (bs1 : List UInt8) : State :=
  stage2NoEventWalkAt
    (("%SwitchLeaf2", .int 1 1) :: ("%Pivot", .int 1 1) :: ("%Pivot6", .int 1 0) ::
      openEnv0 s.env k bs4 ep b bs1)
    (closeHead1 s k bs4 ep b bs1) "if.then35.peel" "LeafBlock1"

/-- **The class's open path**: the head, `{`'s dispatch, the `if.then9` guard,
and the zero-depth arm, to `close_obj` with `K + {tok+2, terms+3}`. -/
theorem stage2NoEventWalkOpenPath {calls : Calls} {K : Stage2NoEventWalkCarry}
    {mem : Mem} {s : State} {k : BitVec 64} {ep b : Nat} {bs4 bs1 : List UInt8}
    {sp : BitVec 32} {terms tok inc nep : BitVec 64} {bs4n bs1n : List UInt8}
    (h : Stage2NoEventWalkInv K mem s) (hpc : s.pc = "if.end.peel")
    (hpre : s.pre = some "if.end.peel.preheader")
    (hk : lookupName (cells loopHeadPhiCells s.env) "%k.0.ph1404" = some (.int 64 k))
    (hep : lookupName (cells loopHeadPhiCells s.env) "%ep" = some (.ptr ep))
    (hb : lookupName (cells loopHeadPhiCells s.env) "%b" = some (.ptr b))
    (hklt : (k.signExtend 64).toNat < 2 ^ 63)
    (hlane : readBytes s.mem (ep + (k.signExtend 64).toNat * 4) 4 = some bs4)
    (hlanelt : bytesToNat bs4 < 2 ^ 32)
    (hbyte : readBytes s.mem
      (b + ((BitVec.ofNat 64 (bytesToNat bs4)).signExtend 64).toNat) 1 = some bs1)
    (hy91 : evalICmp .slt (BitVec.ofNat 8 (bytesToNat bs1)) (BitVec.ofNat 8 91) = 0)
    (hy123 : evalICmp .slt (BitVec.ofNat 8 (bytesToNat bs1)) (BitVec.ofNat 8 123) = 0)
    (hy123eq : evalICmp .eq (BitVec.ofNat 8 (bytesToNat bs1)) (BitVec.ofNat 8 123) = 1)
    (hk9 : lookupName (openHead9 s k bs4 ep b bs1).env "%k.0.ph1404"
      = some (.int 64 k))
    (hinc9 : lookupName (openHead9 s k bs4 ep b bs1).env "%inc.peel"
      = some (.int 64 (k + BitVec.ofNat 64 1)))
    (hidx9 : lookupName (openHead9 s k bs4 ep b bs1).env "%idxprom.peel"
      = some (.int 64 (BitVec.ofNat 64 (bytesToNat bs4))))
    (hfr9 : lookupName (openHead9 s k bs4 ep b bs1).env "%frame.0.ph1402"
      = some (.int 8 0))
    (hsp9 : lookupName (openHead9 s k bs4 ep b bs1).env "%sp.0.ph1403"
      = some (.int 32 0))
    (htr9 : lookupName (openHead9 s k bs4 ep b bs1).env "%terms.0.ph1407"
      = some (.int 64 0))
    (htok9 : lookupName (openHead9 s k bs4 ep b bs1).env "%tokens.0.ph1408"
      = some (.int 64 0))
    (hsp19 : lookupName (openHead19 s k bs4 ep b bs1).env "%sp.0.lcssa1092.wide"
      = some (.int 32 sp))
    (hzero19 : sp.toNat = 0)
    (hterms19 : lookupName (openHead19 s k bs4 ep b bs1).env "%terms.0.lcssa1080"
      = some (.int 64 terms))
    (htok19 : lookupName (openHead19 s k bs4 ep b bs1).env "%tokens.0.lcssa1074"
      = some (.int 64 tok))
    (hep19 : lookupName (openHead19 s k bs4 ep b bs1).env "%ep" = some (.ptr ep))
    (hb19 : lookupName (openHead19 s k bs4 ep b bs1).env "%b" = some (.ptr b))
    (hinc19 : lookupName (openHead19 s k bs4 ep b bs1).env "%inc.lcssa1129"
      = some (.int 64 inc))
    (hnep19 : lookupName (openHead19 s k bs4 ep b bs1).env "%nep" = some (.int 64 nep))
    (hult : BitVec.ult inc nep = true)
    (hincLt : inc.toNat < 2 ^ 63)
    (hnext : bytesToNat bs1n = 125)
    (hk19 : lookupName (openHead19 s k bs4 ep b bs1).env "%k.0.lcssa1086"
      = some (.int 64 k))
    (hmem : K.pos ∈ K.ent) (hrel : K.tok + 2 ≤ K.pos)
    (hlane19 : readBytes (openHead19 s k bs4 ep b bs1).mem
      (ep + inc.toNat * 4) 4 = some bs4n)
    (hbyte19 : readBytes (openHead19 s k bs4 ep b bs1).mem
      (b + (BitVec.signExtend 64 (BitVec.ofNat 64 (bytesToNat bs4n))).toNat)
      1 = some bs1n)
    (hlanelt19 : bytesToNat bs4n < 2 ^ 32) :
    ∃ so, Stage2NoEventWalkChain calls mem K s
        { K with tok := K.tok + 2, terms := K.terms + 3 } so ∧
      so.pc = "close_obj" ∧
      Stage2NoEventWalkInv
        { K with tok := K.tok + 2, terms := K.terms + 3 } mem so := by
  have H9 : Stage2NoEventWalkChain calls mem K s K
      (openHead9 s k bs4 ep b bs1) :=
    chain_open123 h hpc hpre hk hep hb hklt hlane hlanelt hbyte hy91 hy123 hy123eq
  have L9 : Stage2NoEventWalkLink calls K mem (openHead9 s k bs4 ep b bs1) K
      (openHead19 s k bs4 ep b bs1) :=
    link_ifThen9 (calls := calls) (Stage2NoEventWalkChain.inv H9) rfl rfl hk9 hinc9 hidx9 hfr9 hsp9 htr9 htok9
  have H19 : Stage2NoEventWalkChain calls mem K s K (openHead19 s k bs4 ep b bs1) :=
    Stage2NoEventWalkChain.trans H9
      (Stage2NoEventWalkChain.tail L9 (Stage2NoEventWalkChain.nil L9.inv'))
  have L20 : Stage2NoEventWalkChain calls mem K (openHead19 s k bs4 ep b bs1)
      { K with tok := K.tok + 2, terms := K.terms + 3 }
      (braceCloseState (openZeroEnd74 (openHead19 s k bs4 ep b bs1) sp) ep b terms tok inc
        k bs4n bs1n) :=
    stage2NoEventRow_openZero (Stage2NoEventWalkChain.inv H19)
      (by simp only [openHead19, stage2NoEventWalkNext]) hsp19
      hterms19 htok19 hep19 hb19 hinc19 hnep19 hult hincLt hnext hk19 hmem hrel
      hlane19 hbyte19 hlanelt19 hzero19
  have H := Stage2NoEventWalkChain.trans H19 L20
  exact ⟨_, H, by simp only [braceCloseState, stage2NoEventWalkNext],
    Stage2NoEventWalkChain.inv H⟩

/-- **The class's close path**: the head, `[`'s dispatch, the zero-depth bracket
arm, the `]` count and the direct `after_value`, with `K + {tok+2, terms+7}`. -/
theorem stage2NoEventWalkClosePath {calls : Calls} {K : Stage2NoEventWalkCarry}
    {mem : Mem} {s : State} {k : BitVec 64} {ep b : Nat} {bs4 bs1 : List UInt8}
    {sp : BitVec 32} {inc nep alen arena64 : BitVec 64}
    (h : Stage2NoEventWalkInv K mem s) (hpc : s.pc = "if.end.peel")
    (hpre : s.pre = some "if.end.peel.preheader")
    (hk : lookupName (cells loopHeadPhiCells s.env) "%k.0.ph1404" = some (.int 64 k))
    (hep : lookupName (cells loopHeadPhiCells s.env) "%ep" = some (.ptr ep))
    (hb : lookupName (cells loopHeadPhiCells s.env) "%b" = some (.ptr b))
    (hklt : (k.signExtend 64).toNat < 2 ^ 63)
    (hlane : readBytes s.mem (ep + (k.signExtend 64).toNat * 4) 4 = some bs4)
    (hlanelt : bytesToNat bs4 < 2 ^ 32)
    (hbyte : readBytes s.mem
      (b + ((BitVec.ofNat 64 (bytesToNat bs4)).signExtend 64).toNat) 1 = some bs1)
    (h3b : bytesToNat bs1 = 91)
    (hsp35 : lookupName (closeHead35 s k bs4 ep b bs1).env "%sp.0.ph1403"
      = some (.int 32 sp))
    (hzero35 : sp.toNat = 0)
    (hinc35 : lookupName (closeHead35 s k bs4 ep b bs1).env "%inc.peel"
      = some (.int 64 inc))
    (hnep35 : lookupName (closeHead35 s k bs4 ep b bs1).env "%nep" = some (.int 64 nep))
    (hle35 : sp.toNat ≤ 519) (hult : BitVec.ult inc nep = true)
    (hep35 : lookupName (closeHead35 s k bs4 ep b bs1).env "%ep" = some (.ptr ep))
    (hb35 : lookupName (closeHead35 s k bs4 ep b bs1).env "%b" = some (.ptr b))
    (hincLt : inc.toNat < 2 ^ 63)
    (hlane35 : readBytes (closeHead35 s k bs4 ep b bs1).mem
      (ep + inc.toNat * 4) 4 = some bs4)
    (hlanelt35 : bytesToNat bs4 < 2 ^ 32)
    (hbyte35 : readBytes (closeHead35 s k bs4 ep b bs1).mem
      (b + (BitVec.signExtend 64 (BitVec.ofNat 64 (bytesToNat bs4))).toNat) 1 = some bs1)
    (hb93 : bytesToNat bs1 = 93)
    (hk35 : lookupName (closeHead35 s k bs4 ep b bs1).env "%k.0.ph1404"
      = some (.int 64 k))
    (htr35 : lookupName (closeHead35 s k bs4 ep b bs1).env "%terms.0.ph1407"
      = some (.int 64 K.terms))
    (htokr35 : lookupName (closeHead35 s k bs4 ep b bs1).env "%tokens.0.ph1408"
      = some (.int 64 K.tok))
    (halen35 : lookupName (closeHead35 s k bs4 ep b bs1).env "%alen.0.ph1405"
      = some (.int 64 alen))
    (harena35 : lookupName (closeHead35 s k bs4 ep b bs1).env "%arena.0.ph1406"
      = some (.int 64 arena64))
    (hstk35 : lookupName (closeHead35 s k bs4 ep b bs1).env "%stk" = some (.ptr K.stk))
    (hmem : K.pos ∈ K.ent) (hrel : K.tok + 2 ≤ K.pos) :
    ∃ sc, Stage2NoEventWalkChain calls mem K s
        { K with tok := K.tok + 2, terms := K.terms + 7 } sc ∧
      sc.pc = "after_value" ∧
      Stage2NoEventWalkInv
        { K with tok := K.tok + 2, terms := K.terms + 7 } mem sc := by
  have L0 : Stage2NoEventWalkLink calls K mem s K (closeHead1 s k bs4 ep b bs1) :=
    link_loopHead (calls := calls) h hpc hpre hk hep hb hklt hlane hlanelt hbyte
  have H1 : Stage2NoEventWalkChain calls mem K s K (closeHead1 s k bs4 ep b bs1) :=
    Stage2NoEventWalkChain.tail L0 (Stage2NoEventWalkChain.nil L0.inv')
  have h3' : lookupName (closeHead1 s k bs4 ep b bs1).env "%3"
      = some (.int 8 (BitVec.ofNat 8 91)) := by
    show lookupName (openEnv0 s.env k bs4 ep b bs1) "%3"
      = some (.int 8 (BitVec.ofNat 8 91))
    simp only [openEnv0, lookupName_cons_self, h3b]
  have H35 : Stage2NoEventWalkChain calls mem K s K
      (closeHead35 s k bs4 ep b bs1) :=
    Stage2NoEventWalkChain.trans H1
      (stage2NoEventRow_bracket (calls := calls) (Stage2NoEventWalkChain.inv H1)
        (by simp only [closeHead1, stage2NoEventWalkNext]) h3')
  have H := Stage2NoEventWalkChain.trans H35
    (stage2NoEventRow_closeZero (Stage2NoEventWalkChain.inv H35)
      (by simp only [closeHead35, stage2NoEventWalkAt])
      hsp35 hinc35 hnep35 hle35 hult hep35 hb35 hincLt hlane35 hlanelt35 hbyte35
      hb93 hk35 htr35 htokr35 halen35 harena35 hstk35 hzero35 hmem hrel)
  exact ⟨_, H, by simp only [bracketArrValue, stage2NoEventWalkNext],
    Stage2NoEventWalkChain.inv H⟩

/-- **The container class**: the two full paths from one head state.  The open
path runs `{`'s dispatch and the `if.then9` guard into the zero-depth arm and
reaches `close_obj` with `K + {tok+2, terms+3}`; the close path runs `[`'s
dispatch and the zero-depth bracket arm through the `]` count to `after_value`
with `K + {tok+2, terms+7}`.  Each observation is the invariant at the path's
own exit; the count guards are the bound-derived ones. -/
theorem stage2NoEventWalkContainerClass {calls : Calls} {K : Stage2NoEventWalkCarry}
    {mem : Mem} {s : State} {k : BitVec 64} {ep b : Nat} {bs4 bs1 : List UInt8}
    {sp : BitVec 32} {terms tok inc nep : BitVec 64}
    {bs4n bs1n : List UInt8} {alen arena64 : BitVec 64}
    (h : Stage2NoEventWalkInv K mem s) (hpc : s.pc = "if.end.peel")
    (hpre : s.pre = some "if.end.peel.preheader")
    (hk : lookupName (cells loopHeadPhiCells s.env) "%k.0.ph1404" = some (.int 64 k))
    (hep : lookupName (cells loopHeadPhiCells s.env) "%ep" = some (.ptr ep))
    (hb : lookupName (cells loopHeadPhiCells s.env) "%b" = some (.ptr b))
    (hklt : (k.signExtend 64).toNat < 2 ^ 63)
    (hlane : readBytes s.mem (ep + (k.signExtend 64).toNat * 4) 4 = some bs4)
    (hlanelt : bytesToNat bs4 < 2 ^ 32)
    (hbyte : readBytes s.mem
      (b + ((BitVec.ofNat 64 (bytesToNat bs4)).signExtend 64).toNat) 1 = some bs1)
    (hy91 : evalICmp .slt (BitVec.ofNat 8 (bytesToNat bs1)) (BitVec.ofNat 8 91) = 0)
    (hy123 : evalICmp .slt (BitVec.ofNat 8 (bytesToNat bs1)) (BitVec.ofNat 8 123) = 0)
    (hy123eq : evalICmp .eq (BitVec.ofNat 8 (bytesToNat bs1)) (BitVec.ofNat 8 123) = 1)
    (h3b : bytesToNat bs1 = 91)
    (hk9 : lookupName (openHead9 s k bs4 ep b bs1).env "%k.0.ph1404"
      = some (.int 64 k))
    (hinc9 : lookupName (openHead9 s k bs4 ep b bs1).env "%inc.peel"
      = some (.int 64 (k + BitVec.ofNat 64 1)))
    (hidx9 : lookupName (openHead9 s k bs4 ep b bs1).env "%idxprom.peel"
      = some (.int 64 (BitVec.ofNat 64 (bytesToNat bs4))))
    (hfr9 : lookupName (openHead9 s k bs4 ep b bs1).env "%frame.0.ph1402"
      = some (.int 8 0))
    (hsp9 : lookupName (openHead9 s k bs4 ep b bs1).env "%sp.0.ph1403"
      = some (.int 32 0))
    (htr9 : lookupName (openHead9 s k bs4 ep b bs1).env "%terms.0.ph1407"
      = some (.int 64 0))
    (htok9 : lookupName (openHead9 s k bs4 ep b bs1).env "%tokens.0.ph1408"
      = some (.int 64 0))
    (hsp19 : lookupName (openHead19 s k bs4 ep b bs1).env "%sp.0.lcssa1092.wide"
      = some (.int 32 sp))
    (hterms19 : lookupName (openHead19 s k bs4 ep b bs1).env "%terms.0.lcssa1080"
      = some (.int 64 terms))
    (htok19 : lookupName (openHead19 s k bs4 ep b bs1).env "%tokens.0.lcssa1074"
      = some (.int 64 tok))
    (hep19 : lookupName (openHead19 s k bs4 ep b bs1).env "%ep" = some (.ptr ep))
    (hb19 : lookupName (openHead19 s k bs4 ep b bs1).env "%b" = some (.ptr b))
    (hinc19 : lookupName (openHead19 s k bs4 ep b bs1).env "%inc.lcssa1129"
      = some (.int 64 inc))
    (hnep19 : lookupName (openHead19 s k bs4 ep b bs1).env "%nep" = some (.int 64 nep))
    (hnext : bytesToNat bs1n = 125)
    (hk19 : lookupName (openHead19 s k bs4 ep b bs1).env "%k.0.lcssa1086"
      = some (.int 64 k))
    (hlane19 : readBytes (openHead19 s k bs4 ep b bs1).mem
      (ep + inc.toNat * 4) 4 = some bs4n)
    (hbyte19 : readBytes (openHead19 s k bs4 ep b bs1).mem
      (b + (BitVec.signExtend 64 (BitVec.ofNat 64 (bytesToNat bs4n))).toNat)
      1 = some bs1n)
    (hlanelt19 : bytesToNat bs4n < 2 ^ 32)
    (hsp35 : lookupName (closeHead35 s k bs4 ep b bs1).env "%sp.0.ph1403"
      = some (.int 32 sp))
    (hinc35 : lookupName (closeHead35 s k bs4 ep b bs1).env "%inc.peel"
      = some (.int 64 inc))
    (hnep35 : lookupName (closeHead35 s k bs4 ep b bs1).env "%nep" = some (.int 64 nep))
    (hle35 : sp.toNat ≤ 519)
    (hep35 : lookupName (closeHead35 s k bs4 ep b bs1).env "%ep" = some (.ptr ep))
    (hb35 : lookupName (closeHead35 s k bs4 ep b bs1).env "%b" = some (.ptr b))
    (hlane35 : readBytes (closeHead35 s k bs4 ep b bs1).mem
      (ep + inc.toNat * 4) 4 = some bs4)
    (hlanelt35 : bytesToNat bs4 < 2 ^ 32)
    (hbyte35 : readBytes (closeHead35 s k bs4 ep b bs1).mem
      (b + (BitVec.signExtend 64 (BitVec.ofNat 64 (bytesToNat bs4))).toNat) 1 = some bs1)
    (hb93 : bytesToNat bs1 = 93)
    (hk35 : lookupName (closeHead35 s k bs4 ep b bs1).env "%k.0.ph1404"
      = some (.int 64 k))
    (htr35 : lookupName (closeHead35 s k bs4 ep b bs1).env "%terms.0.ph1407"
      = some (.int 64 K.terms))
    (htokr35 : lookupName (closeHead35 s k bs4 ep b bs1).env "%tokens.0.ph1408"
      = some (.int 64 K.tok))
    (halen35 : lookupName (closeHead35 s k bs4 ep b bs1).env "%alen.0.ph1405"
      = some (.int 64 alen))
    (harena35 : lookupName (closeHead35 s k bs4 ep b bs1).env "%arena.0.ph1406"
      = some (.int 64 arena64))
    (hstk35 : lookupName (closeHead35 s k bs4 ep b bs1).env "%stk" = some (.ptr K.stk))
    (hult : BitVec.ult inc nep = true)
    (hincLt : inc.toNat < 2 ^ 63)
    (hzero : sp.toNat = 0)
    (hmem : K.pos ∈ K.ent) (hrel : K.tok + 2 ≤ K.pos) :
    (∃ so, Stage2NoEventWalkChain calls mem K s
        { K with tok := K.tok + 2, terms := K.terms + 3 } so ∧
      so.pc = "close_obj" ∧
      Stage2NoEventWalkInv
        { K with tok := K.tok + 2, terms := K.terms + 3 } mem so) ∧
    (∃ sc, Stage2NoEventWalkChain calls mem K s
        { K with tok := K.tok + 2, terms := K.terms + 7 } sc ∧
      sc.pc = "after_value" ∧
      Stage2NoEventWalkInv
        { K with tok := K.tok + 2, terms := K.terms + 7 } mem sc) :=
  ⟨stage2NoEventWalkOpenPath h hpc hpre hk hep hb hklt hlane hlanelt hbyte hy91
    hy123 hy123eq hk9 hinc9 hidx9 hfr9 hsp9 htr9 htok9 hsp19 hzero hterms19 htok19
    hep19 hb19 hinc19 hnep19 hult hincLt hnext hk19 hmem hrel hlane19 hbyte19
    hlanelt19,
   stage2NoEventWalkClosePath h hpc hpre hk hep hb hklt hlane hlanelt hbyte h3b
    hsp35 hzero hinc35 hnep35 hle35 hult hep35 hb35 hincLt hlane35 hlanelt35
    hbyte35 hb93 hk35 htr35 htokr35 halen35 harena35 hstk35 hmem hrel⟩









/-- **The container class's statement.**  The open path from `if.end19` (the
depth's case split: the zero depth at `if.end19`'s true arm, a live depth through
`stage2NoEventRow_bracePush`) reaches `close_obj` with the `{`/`}` counts in the
carry (`tok + 2`, `terms + 3`); the close path from `if.then35.peel` (the `[`
push) reaches `after_value` through the `]` count and the pop (`tok + 2`,
`terms + 7`).  Each field is the invariant at the path's own last target, at the
invariant's memory and the class's written state, with the class's cells in the
exit environments; the count guards are the bound-derived ones
(`Stage2NoEventWalkInv.htok`), never restated. -/
structure Stage2NoEventWalkContainerClass (calls : Calls) (K : Stage2NoEventWalkCarry)
    (mem : Mem) (sOpen sClose : State) : Prop where
  /-- The open path: `if.end19` to `close_obj`. -/
  open_ : ∃ s', Stage2NoEventWalkChain calls mem K sOpen
      { K with tok := K.tok + 2, terms := K.terms + 3 } s' ∧
    s'.pc = "close_obj" ∧
    Stage2NoEventWalkInv { K with tok := K.tok + 2, terms := K.terms + 3 } mem s'
  /-- The close path: `if.then35.peel` to `after_value`. -/
  close_ : ∃ s', Stage2NoEventWalkChain calls mem K sClose
      { K with tok := K.tok + 2, terms := K.terms + 7 } s' ∧
    s'.pc = "after_value" ∧
    Stage2NoEventWalkInv { K with tok := K.tok + 2, terms := K.terms + 7 } mem s'






/-! ### Axiom footprints -/

#print axioms Stage2NoEventWalkInv.count
#print axioms ifThen81_denote
#print axioms closeObjRest_denote
#print axioms ifThen334_denote
#print axioms closeArrRest_denote
#print axioms ifThen334_phi_denote
#print axioms closeArr_phi_denote
#print axioms ifThen334_counts_denote
#print axioms closeArr_test_denote
#print axioms ifEnd327peelBlock_find
#print axioms link_ifEnd327peel
#print axioms link_ifThen334
#print axioms link_closeArr
#print axioms link_ifThen350
#print axioms row_closeBracket
#print axioms Stage2NoEventWalkInv.pos_lt
#print axioms Stage2NoEventWalkInv.htok
#print axioms link_ifThen81_of_bound
#print axioms link_ifThen334_of_bound
#print axioms baseHeadPhi_denote
#print axioms ifThen343_addzext_denote
#print axioms ifThen343_gep_denote
#print axioms ifThen343_load_denote
#print axioms ifThen343_denote
#print axioms ifThen350_addzext_denote
#print axioms ifThen350_gep_denote
#print axioms ifThen350_load_denote
#print axioms ifThen350_denote
#print axioms link_ifThen9
#print axioms link_ifEnd19_true
#print axioms link_ifEnd45peel_true
#print axioms ifEnd74_denote
#print axioms link_ifEnd74
#print axioms link_nodeBlock21_false
#print axioms link_leafBlock19_true
#print axioms stage2NoEventRow_braceCloseTail
#print axioms stage2NoEventRow_openBrace
#print axioms stage2NoEventRow_bracketZero
#print axioms row_closeBracket_of_bound
#print axioms stage2NoEventRow_closePush
#print axioms Stage2NoEventWalkChain.inv
#print axioms Stage2NoEventWalkChain.trans
#print axioms link_closeArr_true
#print axioms row_closeBracketZero
#print axioms stage2NoEventRow_openZero
#print axioms stage2NoEventRow_closeZero
#print axioms stage2NoEventWalkOpenPath
#print axioms stage2NoEventWalkClosePath
#print axioms stage2NoEventWalkContainerClass
#print axioms leafBlockBlock_find
#print axioms link_nodeBlock5_true
#print axioms link_leafBlock_true
#print axioms link_leafBlock_false
#print axioms stage2NoEventRow_string
#print axioms stage2NoEventRow_valueLeaf
#print axioms stage2NoEventRow_valueLeaf1
#print axioms stage2NoEventRow_valueLeaf3
#print axioms stage2NoEventRow_value
#print axioms nodeBlock15Block_find
#print axioms nodeBlock13Block_find
#print axioms leafBlock11Block_find
#print axioms leafBlock9Block_find
#print axioms leafBlock7Block_find
#print axioms link_nodeBlock15_true
#print axioms link_nodeBlock15_false
#print axioms link_nodeBlock13_true
#print axioms link_nodeBlock13_false
#print axioms link_leafBlock11_true
#print axioms link_leafBlock11_false
#print axioms link_leafBlock9_true
#print axioms link_leafBlock9_false
#print axioms link_leafBlock7_true
#print axioms link_leafBlock7_false
#print axioms stage2NoEventRow_loopExitBrace
#print axioms stage2NoEventRow_loopExitBracket
#print axioms stage2NoEventRow_loopExitString
#print axioms stage2NoEventRow_loopScalar7
#print axioms stage2NoEventRow_loopScalar9
#print axioms stage2NoEventRow_loopScalar11
#print axioms stage2NoEventRow_loopScalar
#print axioms stage2NoEventWalk_denote_icmp_reg
#print axioms stage2NoEventWalk_step_callVoid2
#print axioms denoteCode_callVoid2
#print axioms ifThen9LoopexitBlock_find
#print axioms ifThen9LoopexitEntry_denote
#print axioms link_ifThen9LoopexitEntry
#print axioms ifThen9AtLoopexit_denote
#print axioms link_ifThen9AtLoopexit_true
#print axioms link_ifThen9AtLoopexit_false
#print axioms ifThen35Block_find
#print axioms ifThen35_denote
#print axioms link_ifThen35_true
#print axioms link_ifThen35_false
#print axioms stringValueLoopexitBlock_find
#print axioms stringValueLoopexit_denote
#print axioms link_stringValueLoopexitEntry
#print axioms stringValueBlock_find
#print axioms stringValue_denote
#print axioms link_stringValue_true
#print axioms link_stringValue_false
#print axioms scalarLoopexitBlock_find
#print axioms scalarLoopexitEntry_denote
#print axioms link_scalarLoopexitEntry
#print axioms scalarBlock_find
#print axioms scalar_denote
#print axioms link_scalar_true
#print axioms link_scalar_false
#print axioms condTrueBlock_find
#print axioms condTrue_denote
#print axioms link_condTrue
#print axioms condEndBlock_find
#print axioms condEnd_denote_fromScalar
#print axioms condEnd_denote_fromCondTrue
#print axioms link_condEnd_true
#print axioms link_condEnd_false
#print axioms link_condEnd_fromCondTrue_true
#print axioms link_condEnd_fromCondTrue_false
#print axioms ifEndBlock_find
#print axioms ifEndPhi_denote_fromEnd327
#print axioms ifEndPhi_denote_fromEnd327Peel
#print axioms ifEndTail_denote
#print axioms ifEnd_denote_fromEnd327
#print axioms ifEnd_denote_fromEnd327Peel
#print axioms link_ifEnd_fromEnd327
#print axioms link_ifEnd_fromEnd327Peel
#print axioms ifEndAllCells_lookup
#print axioms ifEndProduce_fromEnd327
#print axioms ifEndProduce_fromEnd327Peel
#print axioms ifEnd_produce

end LeanLLVM.Refinement
