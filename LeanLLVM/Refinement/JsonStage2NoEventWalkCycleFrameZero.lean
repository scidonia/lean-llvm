/-
The no-event walk's frame-zero after-value arm: the shared cycle's missing arm.

`JsonStage2NoEventWalkCycleA` takes the `after_value` endpoint at a non-zero
frame word: `if.end378`'s `%cmp382 = (%frame.6 == 0)` is false there, and the
dispatch's false arm (`if.end410` → `NodeBlock41`) is the `,`/`]` route.  The
frame word is zero when the value just consumed is an object member's; the
member route carries it in, and `close_obj` writes it back
(`after_value: %frame.6 ← 0` on the `close_obj` edge).  This module owns that
arm.

The route is `if.end378`'s true arm and the byte it reads at the entry's lane:

    after_value → if.end369 → if.end378 → if.then384 → NodeBlock35
      → LeafBlock31 (byte `,`) → if.end409 → if.end111
      → LeafBlock33 (byte `}`) → do.body391 → close_obj → after_value

`NodeBlock35`'s `%Pivot36 = (%53 slt 125)` splits the byte into the two sub-arms:
`LeafBlock31`'s `%SwitchLeaf32 = (%53 eq 44)` takes the `,` to the object-member
key route's entry (`if.end111`), and `LeafBlock33`'s `%SwitchLeaf34 =
(%53 eq 125)` takes the `}` to the count store and the closer.

**The `,` sub-arm** stops at `if.end111`, the key route's entry.  That route
(`if.end111`'s quote read, `key_body`, the key's `s2_string_body` call and its
result dispatch, `for.cond.cleanup`'s byte sum, `expect_colon`, `if.end303`) is
another lane's; this module states the boundary it hands over — the state, the
index word `%inc379 = k + 1`, the comma byte, the `ult` test's cell, the base
lookups — and nothing about the key's own blocks.  The index arithmetic those
blocks carry (`key_body`'s `%k.1 = %k.1.in + 2`, `if.end136`'s
`%inc137 = %k.1.in + 3`, `if.end303`'s `%inc304 = %k.1.in + 4`, with
`%k.1.in = %k.6 = k` on the `if.end111` edge) makes the object-member pair's
delta four; this arm's own share of it is the one entry from `k` to `k + 1`.

**The `}` sub-arm** is not a head cycle: it closes the object and returns to
`after_value` at `k + 1`, with the count store's `tok + 1` / `terms + 2` and the
depth one lower.  At a top-level object (`%sp.4 = 1`) `close_obj`'s zero-depth
arm writes the frame word back to zero and the endpoint's depth is zero; at a
nested one the `if.then343` pop reads the enclosing container's tag from the
stack and the endpoint's frame is that byte.  The endpoint is a
`Stage2NoEventWalkAfterValueEntry` — the same shape the arm started from — so a
consumer hands it to `JsonStage2NoEventWalkCycleA`'s cycle at a non-zero frame
word, back to this arm at a zero one, or to the terminal dispatch at depth zero.

Prices are the routes' own block counts: three to `if.then384` (`after_value`,
`if.end369`, `if.end378`), seven to `if.end111`, and eight or nine to the
`after_value` entry (the closer at the top level, the closer and the pop at a
nested one).  The counts move by the blocks' own stores: the `,` arm adds no
event (`Trace K` unchanged; the separator's token belongs to the key route's
step), and the `}` arm appends one close-brace event and two terms
(`Stage2NoEventWalkTrace.closeBrace`), which is `do.body391`'s
`%inc392 = tok + 1` and `%add393 = terms + 2` exactly.
-/
import LeanLLVM.Refinement.JsonStage2NoEventWalkCycleA
import LeanLLVM.Refinement.JsonStage2NoEventWalkRowsBrace

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 1600000
set_option pp.maxSteps 200000

namespace LeanLLVM.Refinement

open LeanLLVM
open LeanLLVM.JSON
open LeanLLVM.Refinement.JsonStage2NoEventIR
open LeanLLVM.Refinement.JsonEntryIR (readLanes32)
open LeanLLVM.Refinement.JsonEntrySteps (readBytes_one)
open LeanLLVM.Refinement.BlockEval

/-! ### The zero test at one

`evalICmp .eq` is the words' equality, so an equal pair tests one.  The committed
cycle has the distinct pair's zero (`stage2NoEventICmp_eq_zero`); this is the
frame-zero arm's true side. -/

/-- **`icmp eq` is one at equal words.** -/
theorem stage2NoEventICmp_eq_one {w : Nat} {x c : BitVec w} (h : x = c) :
    evalICmp .eq x c = 1 := by
  subst h
  simp [evalICmp]

/-- **A literal's value** is the constructor it names. -/
theorem stage2NoEventConstToValue_int (w : Nat) (v : BitVec w) :
    (Const.int w v).toValue = Value.int w v := rfl

/-! ### `if.end378` at the frame word's zero

The committed `ifEnd378_denote` states the run's cells at the test's *zero*
(`%cmp382 = 0`, a non-zero frame word).  The arm's cells differ in that one word,
so the run is stated once at an arbitrary test and the two instances follow. -/

/-- The `if.end378` cells at a test word, newest first. -/
def ifEnd378CmpCells (cmp : BitVec 1) (ep b lane k : Nat) (byte : UInt8) :
    List (String × Value) :=
  [("%53", .int 8 (BitVec.ofNat 8 byte.toNat)),
   ("%arrayidx386", .ptr (b + lane)),
   ("%idxprom385", .int 64 (BitVec.ofNat 64 lane)),
   ("%cmp382", .int 1 cmp),
   ("%52", .int 32 (BitVec.ofNat 32 lane)),
   ("%arrayidx380", .ptr (ep + 4 * k)),
   ("%inc379", .int 64 (BitVec.ofNat 64 (k + 1)))]

/-- **`if.end378`'s run at a test word**, at the entry's lane and the document's
byte. -/
theorem ifEnd378_denote_cmp (calls : Calls) (env : Env) (s : State)
    {ep b lane k fr : Nat} {byte : UInt8} {bs4 : List UInt8} {cmp : BitVec 1}
    (hk : lookupName env "%k.6" = some (.int 64 (BitVec.ofNat 64 k)))
    (hep : lookupName env "%ep" = some (.ptr ep))
    (hb : lookupName env "%b" = some (.ptr b))
    (hframe : lookupName env "%frame.6" = some (.int 8 (BitVec.ofNat 8 fr)))
    (hkLt : k < 2 ^ 63) (hfrLt : fr < 2 ^ 8)
    (hcmp : evalICmp .eq (BitVec.ofNat 8 fr) (BitVec.ofNat 8 0) = cmp)
    (hbs : bytesToNat bs4 = lane) (hLaneLt : lane < 2 ^ 32)
    (hlane : readBytes s.mem (ep + 4 * k) 4 = some bs4)
    (hbyte : readBytes s.mem (b + lane) 1 = some [byte]) :
    denoteCode calls ifEnd378Instrs (stateAt env s) =
      some (stateAt (cells (ifEnd378CmpCells cmp ep b lane k byte) env) s) := by
  rw [ifEnd378Instrs]
  rw [stage2NoEventWalk_denote_add_imm_w (calls := calls) (env := env) (s := s)
    (d := "%inc379") (a := "%k.6") (w := 64) (x := BitVec.ofNat 64 k)
    (c := BitVec.ofNat 64 1) ?_
    (is := [Instr.gep "%arrayidx380" (Ty.int 32) (Operand.reg "%ep")
        (Operand.reg "%k.6"),
      Instr.load "%52" (Ty.int 32) (Operand.reg "%arrayidx380"),
      Instr.icmp "%cmp382" IPred.eq 8 (Operand.reg "%frame.6")
        (Operand.imm (.int 8 (BitVec.ofNat 8 0))),
      Instr.zext "%idxprom385" 32 64 (Operand.reg "%52"),
      Instr.gep "%arrayidx386" (Ty.int 8) (Operand.reg "%b")
        (Operand.reg "%idxprom385"),
      Instr.load "%53" (Ty.int 8) (Operand.reg "%arrayidx386")])]
  all_goals cycle_lk
  rw [show BitVec.ofNat 64 k + BitVec.ofNat 64 1 = BitVec.ofNat 64 (k + 1) from
    stage2NoEventOfNatSucc (by omega)]
  rw [stage2NoEventWalk_denote_gep32 (calls := calls)
    (env := ("%inc379", Value.int 64 (BitVec.ofNat 64 (k + 1))) :: env) (s := s)
    (d := "%arrayidx380") (base := "%ep") (off := "%k.6") (a := ep)
    (o := BitVec.ofNat 64 k) ?_ ?_
    (by rw [stage2NoEventSignExtend_toNat (by omega)]; omega)
    (is := [Instr.load "%52" (Ty.int 32) (Operand.reg "%arrayidx380"),
      Instr.icmp "%cmp382" IPred.eq 8 (Operand.reg "%frame.6")
        (Operand.imm (.int 8 (BitVec.ofNat 8 0))),
      Instr.zext "%idxprom385" 32 64 (Operand.reg "%52"),
      Instr.gep "%arrayidx386" (Ty.int 8) (Operand.reg "%b")
        (Operand.reg "%idxprom385"),
      Instr.load "%53" (Ty.int 8) (Operand.reg "%arrayidx386")])]
  all_goals cycle_lk
  rw [show ep + ((BitVec.ofNat 64 k).signExtend 64).toNat * 4 = ep + 4 * k from by
    rw [stage2NoEventSignExtend_toNat (by omega), Nat.mul_comm]]
  rw [stage2NoEventWalk_denote_load_int (calls := calls)
    (env := ("%arrayidx380", Value.ptr (ep + 4 * k)) ::
      ("%inc379", Value.int 64 (BitVec.ofNat 64 (k + 1))) :: env) (s := s)
    (d := "%52") (p := "%arrayidx380") (w := 32) (a := ep + 4 * k) (bs := bs4)
    (by decide) ?_ hlane
    (is := [Instr.icmp "%cmp382" IPred.eq 8 (Operand.reg "%frame.6")
        (Operand.imm (.int 8 (BitVec.ofNat 8 0))),
      Instr.zext "%idxprom385" 32 64 (Operand.reg "%52"),
      Instr.gep "%arrayidx386" (Ty.int 8) (Operand.reg "%b")
        (Operand.reg "%idxprom385"),
      Instr.load "%53" (Ty.int 8) (Operand.reg "%arrayidx386")])]
  all_goals cycle_lk
  rw [hbs]
  rw [stage2NoEventWalk_denote_icmp_imm (calls := calls)
    (env := ("%52", Value.int 32 (BitVec.ofNat 32 lane)) ::
      ("%arrayidx380", Value.ptr (ep + 4 * k)) ::
      ("%inc379", Value.int 64 (BitVec.ofNat 64 (k + 1))) :: env) (s := s)
    (d := "%cmp382") (a := "%frame.6") (p := .eq) (w := 8)
    (x := BitVec.ofNat 8 fr) (c := BitVec.ofNat 8 0) ?_
    (is := [Instr.zext "%idxprom385" 32 64 (Operand.reg "%52"),
      Instr.gep "%arrayidx386" (Ty.int 8) (Operand.reg "%b")
        (Operand.reg "%idxprom385"),
      Instr.load "%53" (Ty.int 8) (Operand.reg "%arrayidx386")])]
  all_goals cycle_lk
  rw [hcmp]
  rw [denoteCode_zext (calls := calls)
    (env := ("%cmp382", Value.int 1 cmp) ::
      ("%52", Value.int 32 (BitVec.ofNat 32 lane)) ::
      ("%arrayidx380", Value.ptr (ep + 4 * k)) ::
      ("%inc379", Value.int 64 (BitVec.ofNat 64 (k + 1))) :: env)
    (s := s) (d := "%idxprom385")
    (v := "%52") (wIn := 32) (wOut := 64) (x := BitVec.ofNat 32 lane) ?_
    (is := [Instr.gep "%arrayidx386" (Ty.int 8) (Operand.reg "%b")
        (Operand.reg "%idxprom385"),
      Instr.load "%53" (Ty.int 8) (Operand.reg "%arrayidx386")])]
  all_goals cycle_lk
  rw [stage2NoEventOfNat64_ofNat32 hLaneLt]
  rw [denoteCode_gep8_reg (calls := calls)
    (env := ("%idxprom385", Value.int 64 (BitVec.ofNat 64 lane)) ::
      ("%cmp382", Value.int 1 cmp) ::
      ("%52", Value.int 32 (BitVec.ofNat 32 lane)) ::
      ("%arrayidx380", Value.ptr (ep + 4 * k)) ::
      ("%inc379", Value.int 64 (BitVec.ofNat 64 (k + 1))) :: env)
    (s := s) (d := "%arrayidx386") (base := "%b") (off := "%idxprom385") (a := b)
    (idx := BitVec.ofNat 64 lane) ?_ ?_
    (stage2NoEventLane_signExtend_lt hLaneLt)
    (is := [Instr.load "%53" (Ty.int 8) (Operand.reg "%arrayidx386")])]
  all_goals cycle_lk
  rw [stage2NoEventSignExtend_toNat (by omega)]
  rw [stage2NoEventWalk_denote_load_int (calls := calls)
    (env := ("%arrayidx386", Value.ptr (b + lane)) ::
      ("%idxprom385", Value.int 64 (BitVec.ofNat 64 lane)) ::
      ("%cmp382", Value.int 1 cmp) ::
      ("%52", Value.int 32 (BitVec.ofNat 32 lane)) ::
      ("%arrayidx380", Value.ptr (ep + 4 * k)) ::
      ("%inc379", Value.int 64 (BitVec.ofNat 64 (k + 1))) :: env) (s := s)
    (d := "%53") (p := "%arrayidx386") (w := 8) (a := b + lane) (bs := [byte])
    (by decide) (by cycle_lk) hbyte (is := [])]
  rw [stage2NoEventBytesToNat_singleton]
  simp only [ifEnd378CmpCells, cells, denoteCode_nil]

/-- The frame-zero cells. -/
def ifEnd378FrameCells (ep b lane k : Nat) (byte : UInt8) : List (String × Value) :=
  ifEnd378CmpCells 1 ep b lane k byte

/-- **`if.end378`'s run at a zero frame word**: the true arm's cells, with
`%cmp382 = 1`. -/
theorem ifEnd378_denote_frameZero (calls : Calls) (env : Env) (s : State)
    {ep b lane k : Nat} {byte : UInt8} {bs4 : List UInt8}
    (hk : lookupName env "%k.6" = some (.int 64 (BitVec.ofNat 64 k)))
    (hep : lookupName env "%ep" = some (.ptr ep))
    (hb : lookupName env "%b" = some (.ptr b))
    (hframe : lookupName env "%frame.6" = some (.int 8 (BitVec.ofNat 8 0)))
    (hkLt : k < 2 ^ 63)
    (hbs : bytesToNat bs4 = lane) (hLaneLt : lane < 2 ^ 32)
    (hlane : readBytes s.mem (ep + 4 * k) 4 = some bs4)
    (hbyte : readBytes s.mem (b + lane) 1 = some [byte]) :
    denoteCode calls ifEnd378Instrs (stateAt env s) =
      some (stateAt (cells (ifEnd378FrameCells ep b lane k byte) env) s) := by
  refine ifEnd378_denote_cmp calls env s (fr := 0) (cmp := 1) hk hep hb hframe hkLt (by decide)
    ?_ hbs hLaneLt hlane hbyte
  exact stage2NoEventICmp_eq_one rfl

/-! ### The true arm's blocks, pinned -/

/-- `if.then384`: the split to the byte dispatch. -/
def ifThen384Block : Block :=
  { name := "if.then384", instrs := [], term := Term.br "NodeBlock35" }

theorem ifThen384Block_find :
    stage2NoEventBody.findBlock "if.then384" = some ifThen384Block := by
  decide

/-- `NodeBlock35`: the byte against 125. -/
def nodeBlock35Instrs : List Instr :=
  [ Instr.icmp "%Pivot36" IPred.slt 8 (Operand.reg "%53")
      (Operand.imm (.int 8 (BitVec.ofNat 8 125))) ]

/-- `NodeBlock35`, pinned. -/
def nodeBlock35Block : Block :=
  { name := "NodeBlock35", instrs := nodeBlock35Instrs,
    term := Term.condbr (Operand.reg "%Pivot36") "LeafBlock31" "LeafBlock33" }

theorem nodeBlock35Block_find :
    stage2NoEventBody.findBlock "NodeBlock35" = some nodeBlock35Block := by
  decide

/-- `LeafBlock31`: the byte against 44, the comma. -/
def leafBlock31Instrs : List Instr :=
  [ Instr.icmp "%SwitchLeaf32" IPred.eq 8 (Operand.reg "%53")
      (Operand.imm (.int 8 (BitVec.ofNat 8 44))) ]

/-- `LeafBlock31`, pinned. -/
def leafBlock31Block : Block :=
  { name := "LeafBlock31", instrs := leafBlock31Instrs,
    term := Term.condbr (Operand.reg "%SwitchLeaf32") "if.end409" "if.then402" }

theorem leafBlock31Block_find :
    stage2NoEventBody.findBlock "LeafBlock31" = some leafBlock31Block := by
  decide

/-- `LeafBlock33`: the byte against 125, the close brace. -/
def leafBlock33Instrs : List Instr :=
  [ Instr.icmp "%SwitchLeaf34" IPred.eq 8 (Operand.reg "%53")
      (Operand.imm (.int 8 (BitVec.ofNat 8 125))) ]

/-- `LeafBlock33`, pinned. -/
def leafBlock33Block : Block :=
  { name := "LeafBlock33", instrs := leafBlock33Instrs,
    term := Term.condbr (Operand.reg "%SwitchLeaf34") "do.body391" "if.then402" }

theorem leafBlock33Block_find :
    stage2NoEventBody.findBlock "LeafBlock33" = some leafBlock33Block := by
  decide

/-- `do.body391`'s two counts. -/
def doBody391Instrs : List Instr :=
  [ Instr.binop "%inc392" BinOp.add 64 (Operand.reg "%tokens.8")
      (Operand.imm (.int 64 (BitVec.ofNat 64 1))),
    Instr.binop "%add393" BinOp.add 64 (Operand.reg "%terms.8")
      (Operand.imm (.int 64 (BitVec.ofNat 64 2))) ]

/-- `do.body391`, pinned. -/
def doBody391Block : Block :=
  { name := "do.body391", instrs := doBody391Instrs, term := Term.br "close_obj" }

theorem doBody391Block_find :
    stage2NoEventBody.findBlock "do.body391" = some doBody391Block := by
  decide

/-- `if.end409`: the next entry against the entry count. -/
def ifEnd409Instrs : List Instr :=
  [ Instr.icmp "%cmp103.not" IPred.ult 64 (Operand.reg "%inc379")
      (Operand.reg "%nep") ]

/-- `if.end409`, pinned. -/
def ifEnd409Block : Block :=
  { name := "if.end409", instrs := ifEnd409Instrs,
    term := Term.condbr (Operand.reg "%cmp103.not") "if.end111" "if.then105" }

theorem ifEnd409Block_find :
    stage2NoEventBody.findBlock "if.end409" = some ifEnd409Block := by
  decide

/-! ### The arm's cells -/

/-- `NodeBlock35`'s cell. -/
def nodeBlock35Cells (cmp : BitVec 1) : List (String × Value) :=
  [("%Pivot36", .int 1 cmp)]

/-- `LeafBlock31`'s cell. -/
def leafBlock31Cells (cmp : BitVec 1) : List (String × Value) :=
  [("%SwitchLeaf32", .int 1 cmp)]

/-- `LeafBlock33`'s cell. -/
def leafBlock33Cells (cmp : BitVec 1) : List (String × Value) :=
  [("%SwitchLeaf34", .int 1 cmp)]

/-- `if.end409`'s cell. -/
def ifEnd409Cells (cmp : BitVec 1) : List (String × Value) :=
  [("%cmp103.not", .int 1 cmp)]

/-- `do.body391`'s cells, newest first. -/
def doBody391Cells (tok terms : BitVec 64) : List (String × Value) :=
  [("%add393", .int 64 (terms + BitVec.ofNat 64 2)),
   ("%inc392", .int 64 (tok + BitVec.ofNat 64 1))]

/-! ### The blocks' denotations -/

/-- **`NodeBlock35`'s test**, at the byte's signed comparison with 125. -/
theorem nodeBlock35_denote (calls : Calls) (env : Env) (s : State)
    {y : BitVec 8} {c : BitVec 1}
    (h53 : lookupName env "%53" = some (.int 8 y))
    (hc : evalICmp .slt y (BitVec.ofNat 8 125) = c) :
    denoteCode calls nodeBlock35Instrs (stateAt env s) =
      some (stateAt (cells (nodeBlock35Cells c) env) s) := by
  rw [nodeBlock35Instrs,
    stage2NoEventWalk_denote_icmp_imm (calls := calls) (env := env) (s := s)
      (d := "%Pivot36") (a := "%53") (p := .slt) (w := 8)
      (x := y) (c := BitVec.ofNat 8 125) h53 (is := [])]
  rw [hc]
  simp only [nodeBlock35Cells, cells, denoteCode_nil]

/-- **`LeafBlock31`'s test**, at the byte's equality with 44. -/
theorem leafBlock31_denote (calls : Calls) (env : Env) (s : State)
    {y : BitVec 8} {c : BitVec 1}
    (h53 : lookupName env "%53" = some (.int 8 y))
    (hc : evalICmp .eq y (BitVec.ofNat 8 44) = c) :
    denoteCode calls leafBlock31Instrs (stateAt env s) =
      some (stateAt (cells (leafBlock31Cells c) env) s) := by
  rw [leafBlock31Instrs,
    stage2NoEventWalk_denote_icmp_imm (calls := calls) (env := env) (s := s)
      (d := "%SwitchLeaf32") (a := "%53") (p := .eq) (w := 8)
      (x := y) (c := BitVec.ofNat 8 44) h53 (is := [])]
  rw [hc]
  simp only [leafBlock31Cells, cells, denoteCode_nil]

/-- **`LeafBlock33`'s test**, at the byte's equality with 125. -/
theorem leafBlock33_denote (calls : Calls) (env : Env) (s : State)
    {y : BitVec 8} {c : BitVec 1}
    (h53 : lookupName env "%53" = some (.int 8 y))
    (hc : evalICmp .eq y (BitVec.ofNat 8 125) = c) :
    denoteCode calls leafBlock33Instrs (stateAt env s) =
      some (stateAt (cells (leafBlock33Cells c) env) s) := by
  rw [leafBlock33Instrs,
    stage2NoEventWalk_denote_icmp_imm (calls := calls) (env := env) (s := s)
      (d := "%SwitchLeaf34") (a := "%53") (p := .eq) (w := 8)
      (x := y) (c := BitVec.ofNat 8 125) h53 (is := [])]
  rw [hc]
  simp only [leafBlock33Cells, cells, denoteCode_nil]

/-- **`do.body391`'s counts**: one token and two terms. -/
theorem doBody391_denote (calls : Calls) (env : Env) (s : State)
    {tok terms : BitVec 64}
    (htok : lookupName env "%tokens.8" = some (.int 64 tok))
    (hterms : lookupName env "%terms.8" = some (.int 64 terms)) :
    denoteCode calls doBody391Instrs (stateAt env s) =
      some (stateAt (cells (doBody391Cells tok terms) env) s) := by
  rw [doBody391Instrs]
  rw [stage2NoEventWalk_denote_add_imm_w (calls := calls) (env := env) (s := s)
    (d := "%inc392") (a := "%tokens.8") (w := 64) (x := tok)
    (c := BitVec.ofNat 64 1) htok
    (is := [Instr.binop "%add393" BinOp.add 64 (Operand.reg "%terms.8")
      (Operand.imm (.int 64 (BitVec.ofNat 64 2)))])]
  · rw [stage2NoEventWalk_denote_add_imm_w (calls := calls) (env := _) (s := s)
      (d := "%add393") (a := "%terms.8") (w := 64) (x := terms)
      (c := BitVec.ofNat 64 2) (by rw [lookupName_cons_ne _ _ (by decide)]; exact hterms)
      (is := [])]
    simp only [doBody391Cells, cells, denoteCode_nil]

/-- **`if.end409`'s test**, at the words' unsigned order. -/
theorem ifEnd409_denote (calls : Calls) (env : Env) (s : State)
    {inc nep : BitVec 64} {c : BitVec 1}
    (hinc : lookupName env "%inc379" = some (.int 64 inc))
    (hnep : lookupName env "%nep" = some (.int 64 nep))
    (hc : evalICmp .ult inc nep = c) :
    denoteCode calls ifEnd409Instrs (stateAt env s) =
      some (stateAt (cells (ifEnd409Cells c) env) s) := by
  rw [ifEnd409Instrs,
    denoteCode_icmp_ult_reg (calls := calls) (env := env) (s := s)
      (d := "%cmp103.not") (a := "%inc379") (b := "%nep")
      (x := inc) (y := nep) hinc hnep (is := [])]
  rw [hc]
  simp only [ifEnd409Cells, cells, denoteCode_nil]

/-! ### The trace's close-brace step

The `}` is one event and two terms, exactly `do.body391`'s store; the separator's
token list is the relation's, not a count, so the arm's only trace move is this
one. -/

/-- **`}` appends to the trace**, with `tok + 1` and `terms + 2`. -/
theorem Stage2NoEventWalkTrace.closeBrace {K : Stage2NoEventWalkCarry}
    (h : Stage2NoEventWalkTrace K) {start : Nat}
    (hbyte : K.bs[start]? = some (0x7D : UInt8)) :
    Stage2NoEventWalkTrace { K with tok := K.tok + 1, terms := K.terms + 2 } := by
  refine h.step (K' := { K with tok := K.tok + 1, terms := K.terms + 2 })
    (stage2NoEventWalkCloseBraceRel hbyte)
    (stage2NoEventArenaBound_markers (es := [ConsumerEvent.kind 2]) ?_) rfl rfl ?_ ?_
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl
    exact ⟨by decide, by decide⟩
  · rfl
  · have h2 : ([ConsumerEvent.kind 2].map ConsumerEvent.terms).sum = 2 := by decide
    rw [h2]

/-! ### The two endpoints

The arm starts at an `after_value` entry and the `}` sub-arm ends at one.  Both
shapes are the same fact set: the invariant, the block, a depth and a frame
word, the consumed-count bound, the dispatch `phi` run's selection at the state's
own edge, the base lookups, the report's base and the trace.  The source adds
only the frame word's zero; the arm's `,` boundary is the key route's entry. -/

/-- **An `after_value` entry**: what the dispatch needs, at the carry's values. -/
structure Stage2NoEventWalkAfterValueEntry (calls : Calls) (mem : Mem)
    (K : Stage2NoEventWalkCarry) (k : Nat) (s : State) where
  /-- The invariant at the endpoint. -/
  inv : Stage2NoEventWalkInv K mem s
  /-- The after-value block is the next one to run. -/
  pc : s.pc = "after_value"
  /-- The depth word. -/
  sp : Nat
  spLt : sp < 2 ^ 32
  /-- The frame word (the container's tag). -/
  frame : Nat
  frameLt : frame < 2 ^ 8
  /-- The consumed-count bound at the endpoint's index. -/
  count : Stage2NoEventWalkCount K k
  /-- The dispatch `phi` run, at the state's own edge and readings. -/
  phiRun : ∃ p, s.pre = some p ∧
    PhiSelects (stateAt s.env s) p afterValuePhiSpecs
      [("%frame.6", .int 8 (BitVec.ofNat 8 frame)),
       ("%sp.4", .int 32 (BitVec.ofNat 32 sp)),
       ("%k.6", .int 64 (BitVec.ofNat 64 k)),
       ("%alen.8", .int 64 (BitVec.ofNat 64 K.arena.length)),
       ("%arena.10", .int 64 (BitVec.ofNat 64 K.arenaWord)),
       ("%terms.8", .int 64 (BitVec.ofNat 64 K.terms)),
       ("%tokens.8", .int 64 (BitVec.ofNat 64 K.tok))]
  /-- The entry chain's live-ins survived the route. -/
  baseLookups : Stage2NoEventWalkBaseLookups K s
  /-- The report's base is at least one. -/
  bPos : 1 ≤ K.b
  /-- The route's output evidence. -/
  trace : Stage2NoEventWalkTrace K

/-- **The frame-zero arm's source**: an `after_value` entry at a zero frame word. -/
structure Stage2NoEventWalkFrameZeroSrc (calls : Calls) (mem : Mem)
    (K : Stage2NoEventWalkCarry) (k : Nat) (s : State) where
  /-- The invariant at the endpoint. -/
  inv : Stage2NoEventWalkInv K mem s
  /-- The after-value block is the next one to run. -/
  pc : s.pc = "after_value"
  /-- The frame word is zero. -/
  frame : Nat
  frameLt : frame < 2 ^ 8
  frameZero : frame = 0
  /-- The depth word, non-zero at a nested value. -/
  sp : Nat
  spLt : sp < 2 ^ 32
  spNe : sp ≠ 0
  /-- The index fits the address arithmetic. -/
  kAddr : k + 1 < 2 ^ 63
  /-- The entry the arm reads exists. -/
  klt : k < K.nep
  /-- The consumed-count bound at the endpoint's index. -/
  count : Stage2NoEventWalkCount K k
  /-- The dispatch `phi` run, at the class's own edge and readings. -/
  phiRun : ∃ p, s.pre = some p ∧
    PhiSelects (stateAt s.env s) p afterValuePhiSpecs
      [("%frame.6", .int 8 (BitVec.ofNat 8 frame)),
       ("%sp.4", .int 32 (BitVec.ofNat 32 sp)),
       ("%k.6", .int 64 (BitVec.ofNat 64 k)),
       ("%alen.8", .int 64 (BitVec.ofNat 64 K.arena.length)),
       ("%arena.10", .int 64 (BitVec.ofNat 64 K.arenaWord)),
       ("%terms.8", .int 64 (BitVec.ofNat 64 K.terms)),
       ("%tokens.8", .int 64 (BitVec.ofNat 64 K.tok))]
  /-- The entry chain's live-ins survived the class route. -/
  baseLookups : Stage2NoEventWalkBaseLookups K s
  /-- The report's base is at least one. -/
  bPos : 1 ≤ K.b
  /-- The class route's output evidence. -/
  trace : Stage2NoEventWalkTrace K

/-- **The `,` arm's boundary**: the object-member key route's entry, `if.end111`,
handing over everything the key's own blocks read there and nothing about them. -/
structure Stage2NoEventWalkFrameZeroCommaBoundary (calls : Calls) (mem : Mem)
    (K : Stage2NoEventWalkCarry) (k : Nat) (s : State) where
  /-- The invariant at the boundary. -/
  inv : Stage2NoEventWalkInv K mem s
  /-- The key route's entry is the next block. -/
  pc : s.pc = "if.end111"
  pre : s.pre = some "if.end409"
  /-- The next entry's index word, which `if.end111` reads the lane at. -/
  inc379 : lookupName s.env "%inc379" = some (.int 64 (BitVec.ofNat 64 (k + 1)))
  /-- The comma the arm consumed. -/
  comma : lookupName s.env "%53" = some (.int 8 (BitVec.ofNat 8 44))
  /-- The `ult` test's cell: the next entry exists. -/
  cmp103 : lookupName s.env "%cmp103.not" = some (.int 1 1)
  /-- The index the key's `phi` run reads (`%k.1.in = %k.6`). -/
  k6 : lookupName s.env "%k.6" = some (.int 64 (BitVec.ofNat 64 k))
  /-- The frame word the arm's test read. -/
  frame6 : lookupName s.env "%frame.6" = some (.int 8 (BitVec.ofNat 8 0))
  /-- The depth word. -/
  sp : Nat
  sp4 : lookupName s.env "%sp.4" = some (.int 32 (BitVec.ofNat 32 sp))
  spLt : sp < 2 ^ 32
  /-- The carry's three loop registers, as the class route left them. -/
  tokens8 : lookupName s.env "%tokens.8" = some (.int 64 (BitVec.ofNat 64 K.tok))
  terms8 : lookupName s.env "%terms.8" = some (.int 64 (BitVec.ofNat 64 K.terms))
  alen8 : lookupName s.env "%alen.8"
    = some (.int 64 (BitVec.ofNat 64 K.arena.length))
  arena10 : lookupName s.env "%arena.10" = some (.int 64 (BitVec.ofNat 64 K.arenaWord))
  /-- The entry chain's live-ins survived the arm. -/
  baseLookups : Stage2NoEventWalkBaseLookups K s
  /-- The report's base is at least one. -/
  bPos : 1 ≤ K.b
  /-- The consumed-count bound at the boundary's index. -/
  count : Stage2NoEventWalkCount K k
  /-- The output evidence. -/
  trace : Stage2NoEventWalkTrace K

/-! ### The shared prologue: `after_value` to `if.then384`

The three blocks every frame-zero byte takes, with the byte already loaded and
the test word's one. -/

/-- **The frame-zero dispatch's three blocks**, to `if.then384`'s entry, at the
entry's lane and the document's byte. -/
theorem stage2NoEventWalkFrameZeroToThen384 {calls : Calls} {mem : Mem}
    {K : Stage2NoEventWalkCarry} {k : Nat} {s : State}
    (h : Stage2NoEventWalkFrameZeroSrc calls mem K k s)
    {lane : Nat} {byte : UInt8}
    (hk : K.ent[k]? = some lane) (hbs : K.bs[lane]? = some byte) :
    ∃ s' : State,
      Stage2NoEventWalkSegment calls mem K s K s' 3 ∧
      s'.pc = "if.then384" ∧ s'.pre = some "if.end378" ∧
      lookupName s'.env "%53" = some (.int 8 (BitVec.ofNat 8 byte.toNat)) ∧
      lookupName s'.env "%inc379" = some (.int 64 (BitVec.ofNat 64 (k + 1))) ∧
      lookupName s'.env "%cmp382" = some (.int 1 1) ∧
      lookupName s'.env "%frame.6" = some (.int 8 (BitVec.ofNat 8 0)) ∧
      lookupName s'.env "%k.6" = some (.int 64 (BitVec.ofNat 64 k)) ∧
      lookupName s'.env "%sp.4" = some (.int 32 (BitVec.ofNat 32 h.sp)) ∧
      lookupName s'.env "%tokens.8" = some (.int 64 (BitVec.ofNat 64 K.tok)) ∧
      lookupName s'.env "%terms.8" = some (.int 64 (BitVec.ofNat 64 K.terms)) ∧
      lookupName s'.env "%alen.8"
        = some (.int 64 (BitVec.ofNat 64 K.arena.length)) ∧
      lookupName s'.env "%arena.10"
        = some (.int 64 (BitVec.ofNat 64 K.arenaWord)) ∧
      Stage2NoEventWalkBaseLookups K s' ∧
      Stage2NoEventWalkInv K mem s' ∧
      Stage2NoEventWalkCount K k ∧
      Stage2NoEventWalkTrace K ∧
      1 ≤ K.b ∧ s'.mem = s.mem := by
  obtain ⟨pEdge, hpre, hsel⟩ := h.phiRun
  rw [h.frameZero] at hsel
  have hnepLt : K.nep < 2 ^ 64 := h.inv.nepLt
  have hk64 : k < 2 ^ 64 := by have := h.klt; have := h.inv.nepLt; omega
  have hb : lookupName s.env "%b" = some (.ptr K.b) :=
    h.baseLookups "%b" _ (by simp [stage2NoEventWalkBaseValues, stage2NoEventWalkParamEntries])
  have hep : lookupName s.env "%ep" = some (.ptr K.ep) :=
    h.baseLookups "%ep" _ (by simp [stage2NoEventWalkBaseValues, stage2NoEventWalkParamEntries])
  have hnep : lookupName s.env "%nep" = some (.int 64 (BitVec.ofNat 64 K.nep)) :=
    h.baseLookups "%nep" _ (by simp [stage2NoEventWalkBaseValues, stage2NoEventWalkParamEntries])
  have hlanes : readLanes32 s.mem K.ep K.nep = some K.ent :=
    h.inv.readLanes_off (stage2NoEventCycleOutLane h.inv) h.inv.entries
  obtain ⟨laneAV, bsAV, hgetAV, hreadAV, hvalAV, hltAV⟩ :=
    stage2NoEventCycleEnt_lane hlanes h.klt
  have hlaneEq : laneAV = lane := by
    rw [hk] at hgetAV
    exact (Option.some.inj hgetAV).symm
  rw [hlaneEq] at hvalAV
  rw [hlaneEq] at hltAV
  have hins : lane < K.n := h.inv.inside lane (List.mem_of_getElem? hk)
  have hdoc : readBytes s.mem (K.b + lane) 1 = some [K.bs.getD lane 0] :=
    h.inv.readBytes_off (K := K) (a := K.b + lane) (N := 1)
      (bs := [K.bs.getD lane 0]) (stage2NoEventCycleOutDoc h.inv hins) (by
        rw [readBytes_one, readByte_of_readBytes h.inv.doc hins]
        rfl)
  have hgetD : K.bs.getD lane 0 = byte := by
    rw [List.getD_eq_getElem?_getD, hbs]
    rfl
  have hbyte : readBytes s.mem (K.b + lane) 1 = some [byte] := by
    rw [hgetD] at hdoc
    exact hdoc
  let e1 : Env := cells afterValueDispatchCells
    (cells (afterValuePhiCells 0 h.sp k K.arena.length K.arenaWord K.terms K.tok) s.env)
  let r1 : State := stage2NoEventWalkNext e1 s "if.end369"
  let r2 : State := stage2NoEventWalkNext e1 r1 "if.end378"
  let e3 : Env := cells (ifEnd378FrameCells K.ep K.b lane k byte) e1
  let r3 : State := stage2NoEventWalkNext e3 r2 "if.then384"
  have l1 : Stage2NoEventWalkLink calls K mem s K r1 :=
    stage2NoEventWalkLink_condbr_false h.inv (by rw [h.pc]; exact afterValueBlock_find)
      (afterValue_denote (calls := calls) (env := s.env) (s := s) (p := pEdge)
        hpre hsel hnep h.spLt h.spNe hk64 h.klt hnepLt)
      rfl (by cycle_lk)
  have l2 : Stage2NoEventWalkLink calls K mem r1 K r2 :=
    stage2NoEventWalkLink_condbr_true l1.inv'
      (by rw [show r1.pc = "if.end369" from rfl]; exact ifEnd369Block_find)
      (by rw [ifEnd369Block]; exact denoteCode_nil calls (stateAt e1 r1))
      rfl (by cycle_lk)
  have l3 : Stage2NoEventWalkLink calls K mem r2 K r3 :=
    stage2NoEventWalkLink_condbr_true l2.inv'
      (by rw [show r2.pc = "if.end378" from rfl]; exact ifEnd378Block_find)
      (ifEnd378_denote_frameZero (calls := calls) (env := e1) (s := r2)
        (ep := K.ep) (b := K.b) (lane := lane) (k := k) (byte := byte)
        (bs4 := bsAV) (by cycle_lk) (by cycle_lk) (by cycle_lk) (by cycle_lk)
        (by have := h.kAddr; omega) hvalAV hltAV hreadAV hbyte)
      rfl (by cycle_lk)
  have h53 : lookupName e3 "%53" = some (.int 8 (BitVec.ofNat 8 byte.toNat)) := by
    cycle_lk
  have hinc : lookupName e3 "%inc379" =
      some (.int 64 (BitVec.ofNat 64 (k + 1))) := by cycle_lk
  have hcmp : lookupName e3 "%cmp382" = some (.int 1 1) := by cycle_lk
  have hframe3 : lookupName e3 "%frame.6" = some (.int 8 (BitVec.ofNat 8 0)) := by
    cycle_lk
  have hk6 : lookupName e3 "%k.6" = some (.int 64 (BitVec.ofNat 64 k)) := by
    cycle_lk
  have hsp4 : lookupName e3 "%sp.4" = some (.int 32 (BitVec.ofNat 32 h.sp)) := by
    cycle_lk
  have htok : lookupName e3 "%tokens.8" =
      some (.int 64 (BitVec.ofNat 64 K.tok)) := by cycle_lk
  have hterms : lookupName e3 "%terms.8" =
      some (.int 64 (BitVec.ofNat 64 K.terms)) := by cycle_lk
  have halen : lookupName e3 "%alen.8" =
      some (.int 64 (BitVec.ofNat 64 K.arena.length)) := by cycle_lk
  have harena : lookupName e3 "%arena.10" =
      some (.int 64 (BitVec.ofNat 64 K.arenaWord)) := by cycle_lk
  have hbase1 : ∀ n v, (n, v) ∈ stage2NoEventWalkBaseValues K →
      lookupName (cells (afterValuePhiCells 0 h.sp k K.arena.length K.arenaWord
        K.terms K.tok) s.env) n = some v :=
    stage2NoEventCycleBase (K := K) (env := s.env) h.baseLookups
      (cs := afterValuePhiCells 0 h.sp k K.arena.length K.arenaWord K.terms K.tok)
      (names := ["%tokens.8", "%terms.8", "%arena.10", "%alen.8", "%k.6",
        "%sp.4", "%frame.6"]) rfl (by decide)
  have hbase2 : ∀ n v, (n, v) ∈ stage2NoEventWalkBaseValues K → lookupName e1 n = some v :=
    stage2NoEventCycleBase (K := K) hbase1
      (cs := afterValueDispatchCells) (names := ["%cmp358", "%cmp355"])
      rfl (by decide)
  have hbase3 : ∀ n v, (n, v) ∈ stage2NoEventWalkBaseValues K → lookupName e3 n = some v :=
    stage2NoEventCycleBase (K := K) hbase2
      (cs := ifEnd378FrameCells K.ep K.b lane k byte)
      (names := ["%53", "%arrayidx386", "%idxprom385", "%cmp382", "%52",
        "%arrayidx380", "%inc379"]) rfl (by decide)
  have hrun : ∀ n, runFuel calls (3 + n) stage2NoEventBody s =
      runFuel calls n stage2NoEventBody r3 := by
    intro n
    rw [show 3 + n = 1 + (1 + (1 + n)) from by omega]
    rw [stage2NoEventWalkLink_runFuel l1, stage2NoEventWalkLink_runFuel l2,
      stage2NoEventWalkLink_runFuel l3]
  exact ⟨r3, ⟨hrun, l3.inv'⟩, rfl, rfl, h53, hinc, hcmp, hframe3, hk6, hsp4, htok,
    hterms, halen, harena, hbase3, l3.inv', h.count, h.trace, h.bPos, rfl⟩

/-! ### The `,` sub-arm: to the key route's entry -/

/-- **The object-member pair's index delta.**  The `,` arm reaches the key route's
entry at `k + 1`; the key route's own blocks advance `%k.1 = %k.1.in + 2`,
`%inc137 = %k.1.in + 3`, and `if.end303`'s `%inc304 = %k.1.in + 4` is the pair's
fourth index. -/
theorem stage2NoEventWalkFrameZeroCommaDelta (k : Nat) : k + 4 = (k + 1) + 3 := by
  omega

/-- **The `,` sub-arm**: seven blocks from the frame-zero `after_value` entry to
the key route's entry, at the comma and the next entry's index.  The boundary is
`if.end111`'s entry; the key route's own blocks are another lane's. -/
theorem stage2NoEventWalkFrameZeroCommaArm {calls : Calls} {mem : Mem}
    {K : Stage2NoEventWalkCarry} {k : Nat} {s : State}
    (h : Stage2NoEventWalkFrameZeroSrc calls mem K k s)
    {lane : Nat} {byte : UInt8}
    (hk : K.ent[k]? = some lane) (hbs : K.bs[lane]? = some byte)
    (hbyte : byte.toNat = 44) (hknext : k + 1 < K.nep) :
    ∃ s' : State,
      Stage2NoEventWalkSegment calls mem K s K s' 7 ∧
      Nonempty (Stage2NoEventWalkFrameZeroCommaBoundary calls mem K k s') := by
  obtain ⟨s3, hseg3, hpc3, hpre3, h53, hinc, hcmp, hframe3, hk6, hsp4, htok, hterms,
    halen, harena, hbase3, hinv3, hcount, htrace, hbpos, hmem3⟩ :=
    stage2NoEventWalkFrameZeroToThen384 h hk hbs
  have hbyte' : BitVec.ofNat 8 byte.toNat = (BitVec.ofNat 8 44) := by rw [hbyte]
  -- `if.then384`
  let r4 : State := stage2NoEventWalkNext s3.env s3 "NodeBlock35"
  have h53r4 : lookupName r4.env "%53" = some (.int 8 (BitVec.ofNat 8 byte.toNat)) := by
    simp only [r4, stage2NoEventWalkNext]
    exact h53
  have l4 : Stage2NoEventWalkLink calls K mem s3 K r4 :=
    stage2NoEventWalkLink_br hinv3 (by rw [hpc3]; exact ifThen384Block_find)
      (by rw [ifThen384Block]; exact denoteCode_nil calls (stateAt s3.env s3)) rfl
  -- `NodeBlock35`: 44 is below 125
  let r5 : State := stage2NoEventWalkNext (cells (nodeBlock35Cells 1) r4.env) r4
    "LeafBlock31"
  have l5 : Stage2NoEventWalkLink calls K mem r4 K r5 :=
    stage2NoEventWalkLink_condbr_true l4.inv'
      (by rw [show r4.pc = "NodeBlock35" from rfl]; exact nodeBlock35Block_find)
      (nodeBlock35_denote (calls := calls) (env := r4.env) (s := r4)
        (y := BitVec.ofNat 8 byte.toNat) (c := 1) h53r4 (by rw [hbyte']; decide))
      rfl (by simp only [r5, nodeBlock35Cells, cells, lookupName_cons_self])
  have h53r5 : lookupName r5.env "%53" = some (.int 8 (BitVec.ofNat 8 byte.toNat)) := by
    simp only [r5, stage2NoEventWalkNext, cells, nodeBlock35Cells]
    rw [lookupName_cons_ne _ _ (by decide)]
    exact h53r4
  -- `LeafBlock31`: the byte is the comma
  let r6 : State := stage2NoEventWalkNext (cells (leafBlock31Cells 1) r5.env) r5
    "if.end409"
  have l6 : Stage2NoEventWalkLink calls K mem r5 K r6 :=
    stage2NoEventWalkLink_condbr_true l5.inv'
      (by rw [show r5.pc = "LeafBlock31" from rfl]; exact leafBlock31Block_find)
      (leafBlock31_denote (calls := calls) (env := r5.env) (s := r5)
        (y := BitVec.ofNat 8 byte.toNat) (c := 1) h53r5 (by rw [hbyte']; decide))
      rfl (by simp only [r6, leafBlock31Cells, cells, lookupName_cons_self])
  -- `if.end409`: the next entry exists
  let r7 : State := stage2NoEventWalkNext (cells (ifEnd409Cells 1) r6.env) r6
    "if.end111"
  have hinc7 : lookupName r6.env "%inc379" =
      some (.int 64 (BitVec.ofNat 64 (k + 1))) := by
    simp only [r6, r5, cells, leafBlock31Cells, nodeBlock35Cells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact hinc
  have hnep7 : lookupName r6.env "%nep" =
      some (.int 64 (BitVec.ofNat 64 K.nep)) := by
    have hbn : ∀ n v, (n, v) ∈ stage2NoEventWalkBaseValues K →
        lookupName r6.env n = some v := by
      have h1 := stage2NoEventCycleBase (K := K) hbase3
        (cs := nodeBlock35Cells 1) (names := ["%Pivot36"]) rfl (by decide)
      have h2 := stage2NoEventCycleBase (K := K) h1
        (cs := leafBlock31Cells 1) (names := ["%SwitchLeaf32"]) rfl (by decide)
      intro n v hv
      exact h2 n v hv
    exact hbn "%nep" _ (by simp [stage2NoEventWalkBaseValues, stage2NoEventWalkParamEntries])
  have hult : evalICmp .ult (BitVec.ofNat 64 (k + 1)) (BitVec.ofNat 64 K.nep) = 1 :=
    stage2NoEventICmp_ult_one (by have := h.klt; have := hinv3.nepLt; omega) hinv3.nepLt hknext
  have l7 : Stage2NoEventWalkLink calls K mem r6 K r7 :=
    stage2NoEventWalkLink_condbr_true l6.inv'
      (by rw [show r6.pc = "if.end409" from rfl]; exact ifEnd409Block_find)
      (ifEnd409_denote (calls := calls) (env := r6.env) (s := r6)
        (inc := BitVec.ofNat 64 (k + 1)) (nep := BitVec.ofNat 64 K.nep) (c := 1)
        hinc7 hnep7 hult)
      rfl (by simp only [r7, stage2NoEventWalkNext, ifEnd409Cells, cells, lookupName_cons_self])
  -- the run, at the seven blocks
  have hrun : ∀ n, runFuel calls (7 + n) stage2NoEventBody s =
      runFuel calls n stage2NoEventBody r7 := by
    intro n
    rw [show 7 + n = 3 + (1 + (1 + (1 + (1 + n)))) from by omega]
    rw [hseg3.run (1 + (1 + (1 + (1 + n)))),
      stage2NoEventWalkLink_runFuel l4, stage2NoEventWalkLink_runFuel l5,
      stage2NoEventWalkLink_runFuel l6, stage2NoEventWalkLink_runFuel l7]
  -- the boundary's facts
  have hb7 : lookupName r7.env "%53" = some (.int 8 (BitVec.ofNat 8 byte.toNat)) := by
    simp only [r7, stage2NoEventWalkNext, cells, ifEnd409Cells]
    rw [lookupName_cons_ne _ _ (by decide)]
    exact h53r5
  have hinc7' : lookupName r7.env "%inc379" =
      some (.int 64 (BitVec.ofNat 64 (k + 1))) := by
    simp only [r7, stage2NoEventWalkNext, cells, ifEnd409Cells]
    rw [lookupName_cons_ne _ _ (by decide)]
    exact hinc7
  have hcmp7 : lookupName r7.env "%cmp103.not" = some (.int 1 1) := by
    simp only [r7, stage2NoEventWalkNext, ifEnd409Cells, cells, lookupName_cons_self]
  have hk67 : lookupName r7.env "%k.6" = some (.int 64 (BitVec.ofNat 64 k)) := by
    simp only [r7, r6, r5, r4, stage2NoEventWalkNext, cells, ifEnd409Cells, leafBlock31Cells, nodeBlock35Cells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact hk6
  have hframe7 : lookupName r7.env "%frame.6" = some (.int 8 (BitVec.ofNat 8 0)) := by
    simp only [r7, r6, r5, r4, stage2NoEventWalkNext, cells, ifEnd409Cells, leafBlock31Cells, nodeBlock35Cells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact hframe3
  have hsp7 : lookupName r7.env "%sp.4" = some (.int 32 (BitVec.ofNat 32 h.sp)) := by
    simp only [r7, r6, r5, r4, stage2NoEventWalkNext, cells, ifEnd409Cells, leafBlock31Cells, nodeBlock35Cells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact hsp4
  have htok7 : lookupName r7.env "%tokens.8" =
      some (.int 64 (BitVec.ofNat 64 K.tok)) := by
    simp only [r7, r6, r5, r4, stage2NoEventWalkNext, cells, ifEnd409Cells, leafBlock31Cells, nodeBlock35Cells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact htok
  have hterms7 : lookupName r7.env "%terms.8" =
      some (.int 64 (BitVec.ofNat 64 K.terms)) := by
    simp only [r7, r6, r5, r4, stage2NoEventWalkNext, cells, ifEnd409Cells, leafBlock31Cells, nodeBlock35Cells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact hterms
  have halen7 : lookupName r7.env "%alen.8" =
      some (.int 64 (BitVec.ofNat 64 K.arena.length)) := by
    simp only [r7, r6, r5, r4, stage2NoEventWalkNext, cells, ifEnd409Cells, leafBlock31Cells, nodeBlock35Cells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact halen
  have harena7 : lookupName r7.env "%arena.10" =
      some (.int 64 (BitVec.ofNat 64 K.arenaWord)) := by
    simp only [r7, r6, r5, r4, stage2NoEventWalkNext, cells, ifEnd409Cells, leafBlock31Cells, nodeBlock35Cells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact harena
  have hbase7 : Stage2NoEventWalkBaseLookups K r7 := by
    have h1 := stage2NoEventCycleBase (K := K) hbase3
      (cs := nodeBlock35Cells 1) (names := ["%Pivot36"]) rfl (by decide)
    have h2 := stage2NoEventCycleBase (K := K) h1
      (cs := leafBlock31Cells 1) (names := ["%SwitchLeaf32"]) rfl (by decide)
    have h3 := stage2NoEventCycleBase (K := K) h2
      (cs := ifEnd409Cells 1) (names := ["%cmp103.not"]) rfl (by decide)
    intro n v hv
    exact h3 n v hv
  exact ⟨r7, ⟨hrun, l7.inv'⟩,
    ⟨l7.inv', rfl, rfl, hinc7', by rw [hbyte] at hb7; simpa using hb7, hcmp7, hk67,
      hframe7, h.sp, hsp7, h.spLt, htok7, hterms7, halen7, harena7, hbase7, hbpos,
      hcount, htrace⟩⟩

/-! ### The `}` sub-arm: to the next `after_value` -/

/-- The carry `do.body391`'s counts move to. -/
def stage2NoEventWalkCloseBraceCarry (K : Stage2NoEventWalkCarry) :
    Stage2NoEventWalkCarry :=
  { K with tok := K.tok + 1, terms := K.terms + 2 }

/-- **`close_obj`'s six `phi`s at the `do.body391` edge.** -/
theorem closeObjPhi_denote_doBody391 (calls : Calls) (env : Env) (s : State)
    {sp2 : BitVec 32} {k4 alen arena terms6 toks : BitVec 64}
    (hpre : s.pre = some "do.body391")
    (hsp2 : lookupName env "%sp.4" = some (.int 32 sp2))
    (hk4 : lookupName env "%inc379" = some (.int 64 k4))
    (halen : lookupName env "%alen.8" = some (.int 64 alen))
    (harena : lookupName env "%arena.10" = some (.int 64 arena))
    (hterms : lookupName env "%add393" = some (.int 64 terms6))
    (htoks : lookupName env "%inc392" = some (.int 64 toks)) :
    denoteCode calls closeObjPhiInstrs (stateAt env s) =
      some (stateAt (cells (braceCloseObjCells sp2 k4 alen arena terms6 toks) env)
        s) := by
  have hsel : PhiSelects (stateAt env s) "do.body391" closeObjPhiSpecs
      [("%sp.2", .int 32 sp2), ("%k.4", .int 64 k4), ("%alen.6", .int 64 alen),
       ("%arena.8", .int 64 arena), ("%terms.6", .int 64 terms6),
       ("%tokens.6", .int 64 toks)] := by
    refine PhiSelects.cons (op := .reg "%sp.4") (by decide) ?_
      (PhiSelects.cons (op := .reg "%inc379") (by decide) ?_
        (PhiSelects.cons (op := .reg "%alen.8") (by decide) ?_
          (PhiSelects.cons (op := .reg "%arena.10") (by decide) ?_
            (PhiSelects.cons (op := .reg "%add393") (by decide) ?_
              (PhiSelects.cons (op := .reg "%inc392") (by decide) ?_
                PhiSelects.nil)))))
    all_goals
      simp only [stateAt, evalOperand, hsp2, hk4, halen, harena, hterms, htoks]
  rw [closeObjPhi_eq, ← List.append_nil (List.map PhiSpec.instr closeObjPhiSpecs)]
  rw [denoteCode_phiRun (s := stateAt env s) (p := "do.body391")
    (specs := closeObjPhiSpecs)
    (vs := [("%sp.2", .int 32 sp2), ("%k.4", .int 64 k4), ("%alen.6", .int 64 alen),
      ("%arena.8", .int 64 arena), ("%terms.6", .int 64 terms6),
      ("%tokens.6", .int 64 toks)])
    (rest := []) (hpre := hpre) (hsel := hsel) (hrest := by decide)]
  rw [stateAt_bindAll_runCells]
  simp only [braceCloseObjCells, cells, runCells, denoteCode_nil]

/-- **`close_obj`'s live arm** at the `do.body391` edge: the six `phi`s, the
decrement and its test at a depth above one, and the false arm to `if.then343`. -/
theorem link_closeObj_doBody391_live {calls : Calls} {K : Stage2NoEventWalkCarry}
    {mem : Mem} {s : State} {sp2 : BitVec 32} {k4 alen arena terms6 toks : BitVec 64}
    (h : Stage2NoEventWalkInv K mem s) (hpc : s.pc = "close_obj")
    (hpre : s.pre = some "do.body391")
    (hsp2 : lookupName s.env "%sp.4" = some (.int 32 sp2))
    (hk4 : lookupName s.env "%inc379" = some (.int 64 k4))
    (halen : lookupName s.env "%alen.8" = some (.int 64 alen))
    (harena : lookupName s.env "%arena.10" = some (.int 64 arena))
    (hterms : lookupName s.env "%add393" = some (.int 64 terms6))
    (htoks : lookupName s.env "%inc392" = some (.int 64 toks))
    (hdec : (sp2 + BitVec.ofNat 32 4294967295).toNat ≠ 0) :
    Stage2NoEventWalkLink calls K mem s K
      (stage2NoEventWalkNext
        (cells (closeObjTail sp2 ++ braceCloseObjCells sp2 k4 alen arena terms6 toks)
          s.env) s "if.then343") := by
  have h1 := closeObjPhi_denote_doBody391 (calls := calls) (env := s.env) (s := s)
    hpre hsp2 hk4 halen harena hterms htoks
  have h2 := braceCloseObjRest_denote (calls := calls) (env := s.env) (s := s)
    (sp2 := sp2) (k4 := k4) (alen := alen) (arena := arena)
    (terms6 := terms6) (toks := toks)
  have hbit : evalICmp .eq (sp2 + BitVec.ofNat 32 4294967295) (BitVec.ofNat 32 0)
      = (0 : BitVec 1) :=
    stage2NoEventEq0_zero hdec
  refine stage2NoEventWalkLink_condbr_false
    (env' := cells (closeObjTail sp2 ++
      braceCloseObjCells sp2 k4 alen arena terms6 toks) s.env)
    h (by rw [hpc]; exact closeObjBlock_find) ?_ rfl ?_
  · rw [closeObj_split,
      denoteCode_append_apply (a := closeObjPhiInstrs) (b := closeObjRest) h1 (by decide)]
    exact h2
  · simp only [closeObjTail, braceCloseObjCells, cells, List.cons_append,
      List.nil_append, lookupName_cons_self, hbit]

/-- **`close_obj`'s zero-depth arm** at the `do.body391` edge: the six `phi`s, the
decrement and its test, and the true arm to `after_value`. -/
theorem link_closeObj_doBody391_zero {calls : Calls} {K : Stage2NoEventWalkCarry}
    {mem : Mem} {s : State} {sp2 : BitVec 32} {k4 alen arena terms6 toks : BitVec 64}
    (h : Stage2NoEventWalkInv K mem s) (hpc : s.pc = "close_obj")
    (hpre : s.pre = some "do.body391")
    (hsp2 : lookupName s.env "%sp.4" = some (.int 32 sp2))
    (hk4 : lookupName s.env "%inc379" = some (.int 64 k4))
    (halen : lookupName s.env "%alen.8" = some (.int 64 alen))
    (harena : lookupName s.env "%arena.10" = some (.int 64 arena))
    (hterms : lookupName s.env "%add393" = some (.int 64 terms6))
    (htoks : lookupName s.env "%inc392" = some (.int 64 toks))
    (hdec : (sp2 + BitVec.ofNat 32 4294967295).toNat = 0) :
    Stage2NoEventWalkLink calls K mem s K
      (stage2NoEventWalkNext
        (cells (closeObjTail sp2 ++ braceCloseObjCells sp2 k4 alen arena terms6 toks)
          s.env) s "after_value") := by
  have h1 := closeObjPhi_denote_doBody391 (calls := calls) (env := s.env) (s := s)
    hpre hsp2 hk4 halen harena hterms htoks
  have h2 := braceCloseObjRest_denote (calls := calls) (env := s.env) (s := s)
    (sp2 := sp2) (k4 := k4) (alen := alen) (arena := arena)
    (terms6 := terms6) (toks := toks)
  have hbit : evalICmp .eq (sp2 + BitVec.ofNat 32 4294967295) (BitVec.ofNat 32 0)
      = (1 : BitVec 1) :=
    stage2NoEventICmp_eq_one (by
      apply BitVec.eq_of_toNat_eq
      rw [hdec]
      rfl)
  refine stage2NoEventWalkLink_condbr_true
    (env' := cells (closeObjTail sp2 ++
      braceCloseObjCells sp2 k4 alen arena terms6 toks) s.env)
    h (by rw [hpc]; exact closeObjBlock_find) ?_ rfl ?_
  · rw [closeObj_split,
      denoteCode_append_apply (a := closeObjPhiInstrs) (b := closeObjRest) h1 (by decide)]
    exact h2
  · simp only [closeObjTail, braceCloseObjCells, cells, List.cons_append,
      List.nil_append, lookupName_cons_self, hbit]

/-- **The `}` sub-arm at the top level** (`%sp.4 = 1`): eight blocks from the
frame-zero `after_value` entry to the next one, at the close-brace carry. -/
theorem stage2NoEventWalkFrameZeroBraceTop {calls : Calls} {mem : Mem}
    {K : Stage2NoEventWalkCarry} {k : Nat} {s : State}
    (h : Stage2NoEventWalkFrameZeroSrc calls mem K k s)
    (hspOne : h.sp = 1)
    {lane : Nat} {byte : UInt8}
    (hk : K.ent[k]? = some lane) (hbs : K.bs[lane]? = some byte)
    (hbyte : byte.toNat = 125) :
    ∃ s' : State,
      Stage2NoEventWalkSegment calls mem K s (stage2NoEventWalkCloseBraceCarry K) s' 8 ∧
      Nonempty (Stage2NoEventWalkAfterValueEntry calls mem
        (stage2NoEventWalkCloseBraceCarry K) (k + 1) s') := by
  obtain ⟨s3, hseg3, hpc3, hpre3, h53, hinc, hcmp, hframe3, hk6, hsp4, htok, hterms,
    halen, harena, hbase3, hinv3, hcount, htrace, hbpos, hmem3⟩ :=
    stage2NoEventWalkFrameZeroToThen384 h hk hbs
  have hbyte' : BitVec.ofNat 8 byte.toNat = (BitVec.ofNat 8 125) := by rw [hbyte]
  -- `if.then384`
  let r4 : State := stage2NoEventWalkNext s3.env s3 "NodeBlock35"
  have h53r4 : lookupName r4.env "%53" = some (.int 8 (BitVec.ofNat 8 byte.toNat)) := by
    simp only [r4, stage2NoEventWalkNext]
    exact h53
  have l4 : Stage2NoEventWalkLink calls K mem s3 K r4 :=
    stage2NoEventWalkLink_br hinv3 (by rw [hpc3]; exact ifThen384Block_find)
      (by rw [ifThen384Block]; exact denoteCode_nil calls (stateAt s3.env s3)) rfl
  -- `NodeBlock35`: 125 is not below 125
  let r5 : State := stage2NoEventWalkNext (cells (nodeBlock35Cells 0) r4.env) r4
    "LeafBlock33"
  have l5 : Stage2NoEventWalkLink calls K mem r4 K r5 :=
    stage2NoEventWalkLink_condbr_false l4.inv'
      (by rw [show r4.pc = "NodeBlock35" from rfl]; exact nodeBlock35Block_find)
      (nodeBlock35_denote (calls := calls) (env := r4.env) (s := r4)
        (y := BitVec.ofNat 8 byte.toNat) (c := 0) h53r4 (by rw [hbyte']; decide))
      rfl (by simp only [r5, nodeBlock35Cells, cells, lookupName_cons_self])
  have h53r5 : lookupName r5.env "%53" = some (.int 8 (BitVec.ofNat 8 byte.toNat)) := by
    simp only [r5, stage2NoEventWalkNext, cells, nodeBlock35Cells]
    rw [lookupName_cons_ne _ _ (by decide)]
    exact h53r4
  -- `LeafBlock33`: the byte is the close brace
  let r6 : State := stage2NoEventWalkNext (cells (leafBlock33Cells 1) r5.env) r5
    "do.body391"
  have l6 : Stage2NoEventWalkLink calls K mem r5 K r6 :=
    stage2NoEventWalkLink_condbr_true l5.inv'
      (by rw [show r5.pc = "LeafBlock33" from rfl]; exact leafBlock33Block_find)
      (leafBlock33_denote (calls := calls) (env := r5.env) (s := r5)
        (y := BitVec.ofNat 8 byte.toNat) (c := 1) h53r5 (by rw [hbyte']; decide))
      rfl (by simp only [r6, leafBlock33Cells, cells, lookupName_cons_self])
  -- `do.body391`: the counts
  have htok6 : lookupName r6.env "%tokens.8" =
      some (.int 64 (BitVec.ofNat 64 K.tok)) := by
    simp only [r6, r5, r4, stage2NoEventWalkNext, cells, leafBlock33Cells, nodeBlock35Cells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact htok
  have hterms6 : lookupName r6.env "%terms.8" =
      some (.int 64 (BitVec.ofNat 64 K.terms)) := by
    simp only [r6, r5, r4, stage2NoEventWalkNext, cells, leafBlock33Cells, nodeBlock35Cells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact hterms
  let r7 : State := stage2NoEventWalkNext
    (cells (doBody391Cells (BitVec.ofNat 64 K.tok) (BitVec.ofNat 64 K.terms))
      r6.env) r6 "close_obj"
  have l7 : Stage2NoEventWalkLink calls K mem r6 K r7 :=
    stage2NoEventWalkLink_br l6.inv'
      (by rw [show r6.pc = "do.body391" from rfl]; exact doBody391Block_find)
      (doBody391_denote (calls := calls) (env := r6.env) (s := r6)
        (tok := BitVec.ofNat 64 K.tok) (terms := BitVec.ofNat 64 K.terms)
        htok6 hterms6)
      rfl
  -- the carry after the count store
  have hinvC : Stage2NoEventWalkInv (stage2NoEventWalkCloseBraceCarry K) mem r7 :=
    (Stage2NoEventWalkInv.count (h := l7.inv') (t := 1) (c := 2)
      (Stage2NoEventWalkInv.tok_add_le l7.inv' hcount
        (by have := h.klt; omega))).mem_congr rfl
  -- the closer's six `phi`s at the `do.body391` edge
  have hsp7 : lookupName r7.env "%sp.4" = some (.int 32 (BitVec.ofNat 32 h.sp)) := by
    simp only [r7, r6, r5, r4, stage2NoEventWalkNext, cells, doBody391Cells, leafBlock33Cells,
      nodeBlock35Cells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact hsp4
  have hinc7 : lookupName r7.env "%inc379" =
      some (.int 64 (BitVec.ofNat 64 (k + 1))) := by
    simp only [r7, r6, r5, r4, stage2NoEventWalkNext, cells, doBody391Cells, leafBlock33Cells,
      nodeBlock35Cells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact hinc
  have htok7 : lookupName r7.env "%inc392" =
      some (.int 64 (BitVec.ofNat 64 K.tok + BitVec.ofNat 64 1)) := by
    simp only [r7, stage2NoEventWalkNext, doBody391Cells, cells]
    rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_self]
  have hterms7 : lookupName r7.env "%add393" =
      some (.int 64 (BitVec.ofNat 64 K.terms + BitVec.ofNat 64 2)) := by
    simp only [r7, stage2NoEventWalkNext, doBody391Cells, cells, lookupName_cons_self]
  have halen7 : lookupName r7.env "%alen.8" =
      some (.int 64 (BitVec.ofNat 64 K.arena.length)) := by
    simp only [r7, r6, r5, r4, stage2NoEventWalkNext, cells, doBody391Cells, leafBlock33Cells,
      nodeBlock35Cells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact halen
  have harena7 : lookupName r7.env "%arena.10" =
      some (.int 64 (BitVec.ofNat 64 K.arenaWord)) := by
    simp only [r7, r6, r5, r4, stage2NoEventWalkNext, cells, doBody391Cells, leafBlock33Cells,
      nodeBlock35Cells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact harena
  have hdecA : (BitVec.ofNat 32 h.sp + BitVec.ofNat 32 4294967295).toNat = 0 := by
    rw [hspOne]
    decide
  -- the closer's zero-depth arm
  let sA : State := stage2NoEventWalkNext
    (cells (closeObjTail (BitVec.ofNat 32 h.sp) ++
      braceCloseObjCells (BitVec.ofNat 32 h.sp) (BitVec.ofNat 64 (k + 1))
        (BitVec.ofNat 64 K.arena.length) (BitVec.ofNat 64 K.arenaWord)
        (BitVec.ofNat 64 K.terms + BitVec.ofNat 64 2)
        (BitVec.ofNat 64 K.tok + BitVec.ofNat 64 1)) r7.env) r7 "after_value"
  have l8 : Stage2NoEventWalkLink calls (stage2NoEventWalkCloseBraceCarry K) mem r7
      (stage2NoEventWalkCloseBraceCarry K) sA :=
    link_closeObj_doBody391_zero hinvC rfl rfl hsp7 hinc7 halen7 harena7 hterms7 htok7
      hdecA
  -- the run, at the eight blocks
  have hrun : ∀ n, runFuel calls (8 + n) stage2NoEventBody s =
      runFuel calls n stage2NoEventBody sA := by
    intro n
    rw [show 8 + n = 3 + (1 + (1 + (1 + (1 + (1 + n))))) from by omega]
    rw [hseg3.run (1 + (1 + (1 + (1 + (1 + n))))),
      stage2NoEventWalkLink_runFuel l4, stage2NoEventWalkLink_runFuel l5,
      stage2NoEventWalkLink_runFuel l6, stage2NoEventWalkLink_runFuel l7,
      stage2NoEventWalkLink_runFuel l8]
  -- the endpoint's cells
  have hdecS : lookupName sA.env "%dec"
      = some (.int 32 (BitVec.ofNat 32 h.sp + BitVec.ofNat 32 4294967295)) := by
    simp only [sA, stage2NoEventWalkNext, cells, closeObjTail, List.cons_append, List.nil_append]
    rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_self]
  have hk4S : lookupName sA.env "%k.4"
      = some (.int 64 (BitVec.ofNat 64 (k + 1))) := by
    simp only [sA, stage2NoEventWalkNext, cells, closeObjTail, braceCloseObjCells, List.cons_append,
      List.nil_append]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    rw [lookupName_cons_self]
  have halenS : lookupName sA.env "%alen.6"
      = some (.int 64 (BitVec.ofNat 64 K.arena.length)) := by
    simp only [sA, stage2NoEventWalkNext, cells, closeObjTail, braceCloseObjCells, List.cons_append,
      List.nil_append]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    rw [lookupName_cons_self]
  have harenaS : lookupName sA.env "%arena.8"
      = some (.int 64 (BitVec.ofNat 64 K.arenaWord)) := by
    simp only [sA, stage2NoEventWalkNext, cells, closeObjTail, braceCloseObjCells, List.cons_append,
      List.nil_append]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    rw [lookupName_cons_self]
  have htermsS : lookupName sA.env "%terms.6"
      = some (.int 64 (BitVec.ofNat 64 K.terms + BitVec.ofNat 64 2)) := by
    simp only [sA, stage2NoEventWalkNext, cells, closeObjTail, braceCloseObjCells, List.cons_append,
      List.nil_append]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    rw [lookupName_cons_self]
  have htokS : lookupName sA.env "%tokens.6"
      = some (.int 64 (BitVec.ofNat 64 K.tok + BitVec.ofNat 64 1)) := by
    simp only [sA, stage2NoEventWalkNext, cells, closeObjTail, braceCloseObjCells, List.cons_append,
      List.nil_append]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    rw [lookupName_cons_self]
  -- the base lookups at the endpoint
  have hb8 : ∀ n v, (n, v) ∈ stage2NoEventWalkBaseValues K →
      lookupName sA.env n = some v := by
    have h1 := stage2NoEventCycleBase (K := K) hbase3
      (cs := nodeBlock35Cells 0) (names := ["%Pivot36"]) rfl (by decide)
    have h2 := stage2NoEventCycleBase (K := K) h1
      (cs := leafBlock33Cells 1) (names := ["%SwitchLeaf34"]) rfl (by decide)
    have h3 := stage2NoEventCycleBase (K := K) h2
      (cs := doBody391Cells (BitVec.ofNat 64 K.tok) (BitVec.ofNat 64 K.terms))
      (names := ["%add393", "%inc392"]) rfl (by decide)
    have h4 := stage2NoEventCycleBase (K := K) h3
      (cs := closeObjTail (BitVec.ofNat 32 h.sp) ++
        braceCloseObjCells (BitVec.ofNat 32 h.sp) (BitVec.ofNat 64 (k + 1))
          (BitVec.ofNat 64 K.arena.length) (BitVec.ofNat 64 K.arenaWord)
          (BitVec.ofNat 64 K.terms + BitVec.ofNat 64 2)
          (BitVec.ofNat 64 K.tok + BitVec.ofNat 64 1))
      (names := ["%tobool342.not", "%dec", "%tokens.6", "%terms.6", "%arena.8",
        "%alen.6", "%k.4", "%sp.2"]) rfl (by decide)
    intro n v hv
    exact h4 n v hv
  have hword0 : BitVec.ofNat 32 h.sp + BitVec.ofNat 32 4294967295 =
      BitVec.ofNat 32 0 := by
    rw [hspOne]
    decide
  -- the endpoint's dispatch selection at the `close_obj` edge
  have hsel : PhiSelects (stateAt sA.env sA) "close_obj" afterValuePhiSpecs
      [("%frame.6", .int 8 (BitVec.ofNat 8 0)),
       ("%sp.4", .int 32 (BitVec.ofNat 32 0)),
       ("%k.6", .int 64 (BitVec.ofNat 64 (k + 1))),
       ("%alen.8", .int 64 (BitVec.ofNat 64 K.arena.length)),
       ("%arena.10", .int 64 (BitVec.ofNat 64 K.arenaWord)),
       ("%terms.8", .int 64 (BitVec.ofNat 64
         (stage2NoEventWalkCloseBraceCarry K).terms)),
       ("%tokens.8", .int 64 (BitVec.ofNat 64
         (stage2NoEventWalkCloseBraceCarry K).tok))] := by
    refine PhiSelects.cons (op := .imm (.int 8 (BitVec.ofNat 8 0))) (by decide) ?_
      (PhiSelects.cons (op := .reg "%dec") (by decide) ?_
        (PhiSelects.cons (op := .reg "%k.4") (by decide) ?_
          (PhiSelects.cons (op := .reg "%alen.6") (by decide) ?_
            (PhiSelects.cons (op := .reg "%arena.8") (by decide) ?_
              (PhiSelects.cons (op := .reg "%terms.6") (by decide) ?_
                (PhiSelects.cons (op := .reg "%tokens.6") (by decide) ?_
                  PhiSelects.nil))))))
    all_goals
      simp only [stage2NoEventConstToValue_int,
        stage2NoEventWalkCloseBraceCarry, stateAt, evalOperand, hdecS,
        hword0, hk4S, halenS, harenaS, htermsS, htokS, stage2NoEventWalkOfNat_add,
        BitVec.ofNat_toNat, BitVec.setWidth_eq]
  -- the endpoint's trace
  have hbsClose : K.bs[lane]? = some (0x7D : UInt8) := by
    have hy : byte = (0x7D : UInt8) :=
      stage2NoEventWalk_uint8_eq_of_toNat (by rw [hbyte]; decide)
    simpa [hy] using hbs
  have htraceC : Stage2NoEventWalkTrace (stage2NoEventWalkCloseBraceCarry K) :=
    Stage2NoEventWalkTrace.closeBrace htrace hbsClose
  refine ⟨sA, ⟨hrun, l8.inv'⟩, ⟨?_⟩⟩
  refine ⟨l8.inv', rfl, 0, by decide, 0, by decide, ?_, ⟨"close_obj", rfl, hsel⟩,
    hb8, hbpos, htraceC⟩
  exact Stage2NoEventWalkCount.step (a := 1) (b := 1) hcount rfl rfl (by omega)

/-! ### The `}` sub-arm at a nested depth

The `close_obj` test is false above one, so the closer hands to `if.then343`,
which pops the enclosing container's tag from the stack.  The endpoint's frame
word is that byte and its depth is one lower. -/

/-- **The `}` sub-arm at a nested depth** (`2 ≤ %sp.4`): nine blocks from the
frame-zero `after_value` entry to the next one, at the close-brace carry. -/
theorem stage2NoEventWalkFrameZeroBraceDeep {calls : Calls} {mem : Mem}
    {K : Stage2NoEventWalkCarry} {k : Nat} {s : State}
    (h : Stage2NoEventWalkFrameZeroSrc calls mem K k s)
    (hspTwo : 2 ≤ h.sp)
    {lane : Nat} {byte : UInt8}
    (hk : K.ent[k]? = some lane) (hbs : K.bs[lane]? = some byte)
    (hbyte : byte.toNat = 125)
    {a : Nat} {bs : List UInt8}
    (hpop : readBytes s.mem a 1 = some bs)
    (hpopAddr : a = closeReadAddr K.stk
      (BitVec.ofNat 32 h.sp + BitVec.ofNat 32 4294967294).toNat)
    (hbsLen : bs.length = 1) :
    ∃ s' : State,
      Stage2NoEventWalkSegment calls mem K s (stage2NoEventWalkCloseBraceCarry K) s' 9 ∧
      Nonempty (Stage2NoEventWalkAfterValueEntry calls mem
        (stage2NoEventWalkCloseBraceCarry K) (k + 1) s') := by
  obtain ⟨s3, hseg3, hpc3, hpre3, h53, hinc, hcmp, hframe3, hk6, hsp4, htok, hterms,
    halen, harena, hbase3, hinv3, hcount, htrace, hbpos, hmem3⟩ :=
    stage2NoEventWalkFrameZeroToThen384 h hk hbs
  have hbyte' : BitVec.ofNat 8 byte.toNat = (BitVec.ofNat 8 125) := by rw [hbyte]
  let r4 : State := stage2NoEventWalkNext s3.env s3 "NodeBlock35"
  have h53r4 : lookupName r4.env "%53" = some (.int 8 (BitVec.ofNat 8 byte.toNat)) := by
    simp only [r4, stage2NoEventWalkNext]
    exact h53
  have l4 : Stage2NoEventWalkLink calls K mem s3 K r4 :=
    stage2NoEventWalkLink_br hinv3 (by rw [hpc3]; exact ifThen384Block_find)
      (by rw [ifThen384Block]; exact denoteCode_nil calls (stateAt s3.env s3)) rfl
  let r5 : State := stage2NoEventWalkNext (cells (nodeBlock35Cells 0) r4.env) r4
    "LeafBlock33"
  have l5 : Stage2NoEventWalkLink calls K mem r4 K r5 :=
    stage2NoEventWalkLink_condbr_false l4.inv'
      (by rw [show r4.pc = "NodeBlock35" from rfl]; exact nodeBlock35Block_find)
      (nodeBlock35_denote (calls := calls) (env := r4.env) (s := r4)
        (y := BitVec.ofNat 8 byte.toNat) (c := 0) h53r4 (by rw [hbyte']; decide))
      rfl (by simp only [r5, nodeBlock35Cells, cells, lookupName_cons_self])
  have h53r5 : lookupName r5.env "%53" = some (.int 8 (BitVec.ofNat 8 byte.toNat)) := by
    simp only [r5, stage2NoEventWalkNext, cells, nodeBlock35Cells]
    rw [lookupName_cons_ne _ _ (by decide)]
    exact h53r4
  let r6 : State := stage2NoEventWalkNext (cells (leafBlock33Cells 1) r5.env) r5
    "do.body391"
  have l6 : Stage2NoEventWalkLink calls K mem r5 K r6 :=
    stage2NoEventWalkLink_condbr_true l5.inv'
      (by rw [show r5.pc = "LeafBlock33" from rfl]; exact leafBlock33Block_find)
      (leafBlock33_denote (calls := calls) (env := r5.env) (s := r5)
        (y := BitVec.ofNat 8 byte.toNat) (c := 1) h53r5 (by rw [hbyte']; decide))
      rfl (by simp only [r6, leafBlock33Cells, cells, lookupName_cons_self])
  have htok6 : lookupName r6.env "%tokens.8" =
      some (.int 64 (BitVec.ofNat 64 K.tok)) := by
    simp only [r6, r5, r4, stage2NoEventWalkNext, cells, leafBlock33Cells, nodeBlock35Cells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact htok
  have hterms6 : lookupName r6.env "%terms.8" =
      some (.int 64 (BitVec.ofNat 64 K.terms)) := by
    simp only [r6, r5, r4, stage2NoEventWalkNext, cells, leafBlock33Cells, nodeBlock35Cells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact hterms
  let r7 : State := stage2NoEventWalkNext
    (cells (doBody391Cells (BitVec.ofNat 64 K.tok) (BitVec.ofNat 64 K.terms))
      r6.env) r6 "close_obj"
  have l7 : Stage2NoEventWalkLink calls K mem r6 K r7 :=
    stage2NoEventWalkLink_br l6.inv'
      (by rw [show r6.pc = "do.body391" from rfl]; exact doBody391Block_find)
      (doBody391_denote (calls := calls) (env := r6.env) (s := r6)
        (tok := BitVec.ofNat 64 K.tok) (terms := BitVec.ofNat 64 K.terms)
        htok6 hterms6)
      rfl
  have hinvC : Stage2NoEventWalkInv (stage2NoEventWalkCloseBraceCarry K) mem r7 :=
    (Stage2NoEventWalkInv.count (h := l7.inv') (t := 1) (c := 2)
      (Stage2NoEventWalkInv.tok_add_le l7.inv' hcount
        (by have := h.klt; omega))).mem_congr rfl
  have hsp7 : lookupName r7.env "%sp.4" = some (.int 32 (BitVec.ofNat 32 h.sp)) := by
    simp only [r7, r6, r5, r4, stage2NoEventWalkNext, cells, doBody391Cells, leafBlock33Cells,
      nodeBlock35Cells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact hsp4
  have hinc7 : lookupName r7.env "%inc379" =
      some (.int 64 (BitVec.ofNat 64 (k + 1))) := by
    simp only [r7, r6, r5, r4, stage2NoEventWalkNext, cells, doBody391Cells, leafBlock33Cells,
      nodeBlock35Cells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact hinc
  have htok7 : lookupName r7.env "%inc392" =
      some (.int 64 (BitVec.ofNat 64 K.tok + BitVec.ofNat 64 1)) := by
    simp only [r7, stage2NoEventWalkNext, doBody391Cells, cells]
    rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_self]
  have hterms7 : lookupName r7.env "%add393" =
      some (.int 64 (BitVec.ofNat 64 K.terms + BitVec.ofNat 64 2)) := by
    simp only [r7, stage2NoEventWalkNext, doBody391Cells, cells, lookupName_cons_self]
  have halen7 : lookupName r7.env "%alen.8" =
      some (.int 64 (BitVec.ofNat 64 K.arena.length)) := by
    simp only [r7, r6, r5, r4, stage2NoEventWalkNext, cells, doBody391Cells, leafBlock33Cells,
      nodeBlock35Cells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact halen
  have harena7 : lookupName r7.env "%arena.10" =
      some (.int 64 (BitVec.ofNat 64 K.arenaWord)) := by
    simp only [r7, r6, r5, r4, stage2NoEventWalkNext, cells, doBody391Cells, leafBlock33Cells,
      nodeBlock35Cells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact harena
  have hstk7 : lookupName r7.env "%stk" = some (.ptr K.stk) := by
    have h1 := stage2NoEventCycleBase (K := K) hbase3
      (cs := nodeBlock35Cells 0) (names := ["%Pivot36"]) rfl (by decide)
    have h2 := stage2NoEventCycleBase (K := K) h1
      (cs := leafBlock33Cells 1) (names := ["%SwitchLeaf34"]) rfl (by decide)
    have h3 := stage2NoEventCycleBase (K := K) h2
      (cs := doBody391Cells (BitVec.ofNat 64 K.tok) (BitVec.ofNat 64 K.terms))
      (names := ["%add393", "%inc392"]) rfl (by decide)
    exact h3 "%stk" _ (by simp [stage2NoEventWalkBaseValues, stage2NoEventWalkParamEntries])
  have hdecB : (BitVec.ofNat 32 h.sp + BitVec.ofNat 32 4294967295).toNat ≠ 0 := by
    rw [stage2NoEventWalkOfNat_add 32 h.sp 4294967295, BitVec.toNat_ofNat]
    have h2 : h.sp + 4294967295 = (h.sp - 1) + 1 * 2 ^ 32 := by omega
    rw [h2, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by have := h.spLt; omega)]
    omega
  -- the closer's live arm
  let s9 : State := stage2NoEventWalkNext
    (cells (closeObjTail (BitVec.ofNat 32 h.sp) ++
      braceCloseObjCells (BitVec.ofNat 32 h.sp) (BitVec.ofNat 64 (k + 1))
        (BitVec.ofNat 64 K.arena.length) (BitVec.ofNat 64 K.arenaWord)
        (BitVec.ofNat 64 K.terms + BitVec.ofNat 64 2)
        (BitVec.ofNat 64 K.tok + BitVec.ofNat 64 1)) r7.env) r7 "if.then343"
  have hsp16 : lookupName s9.env "%sp.2"
      = some (.int 32 (BitVec.ofNat 32 h.sp)) := by
    simp only [s9, stage2NoEventWalkNext, cells, closeObjTail, braceCloseObjCells, List.cons_append,
      List.nil_append]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    rw [lookupName_cons_self]
  have l8 : Stage2NoEventWalkLink calls (stage2NoEventWalkCloseBraceCarry K) mem r7
      (stage2NoEventWalkCloseBraceCarry K) s9 :=
    link_closeObj_doBody391_live hinvC rfl rfl hsp7 hinc7 halen7 harena7 hterms7 htok7
      hdecB
  -- the pop
  let sA : State := stage2NoEventWalkNext
    (cells (("%49", .int 8 (BitVec.ofNat 8 (bytesToNat bs))) ::
      closeGepCells a ++ closeIdxCells
        (BitVec.ofNat 32 h.sp + BitVec.ofNat 32 4294967294)) s9.env) s9 "after_value"
  have hstk9 : lookupName s9.env "%stk" = some (.ptr K.stk) := by
    simp only [s9, stage2NoEventWalkNext, cells, closeObjTail, braceCloseObjCells, List.cons_append,
      List.nil_append]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact hstk7
  have l9 : Stage2NoEventWalkLink calls (stage2NoEventWalkCloseBraceCarry K) mem s9
      (stage2NoEventWalkCloseBraceCarry K) sA :=
    link_ifThen343 l8.inv' rfl hsp16 hstk9
      (by simpa only [s9, r7, r6, r5, r4, stage2NoEventWalkNext, hmem3] using hpop) hpopAddr
  have hrun : ∀ n, runFuel calls (9 + n) stage2NoEventBody s =
      runFuel calls n stage2NoEventBody sA := by
    intro n
    rw [show 9 + n = 3 + (1 + (1 + (1 + (1 + (1 + (1 + n)))))) from by omega]
    rw [hseg3.run (1 + (1 + (1 + (1 + (1 + (1 + n)))))),
      stage2NoEventWalkLink_runFuel l4, stage2NoEventWalkLink_runFuel l5,
      stage2NoEventWalkLink_runFuel l6, stage2NoEventWalkLink_runFuel l7,
      stage2NoEventWalkLink_runFuel l8, stage2NoEventWalkLink_runFuel l9]
  -- the endpoint's cells
  have h49S : lookupName sA.env "%49"
      = some (.int 8 (BitVec.ofNat 8 (bytesToNat bs))) := by
    simp only [sA, stage2NoEventWalkNext, cells, closeGepCells, closeIdxCells, List.cons_append,
      List.nil_append]
    rw [lookupName_cons_self]
  have hdecS : lookupName sA.env "%dec"
      = some (.int 32 (BitVec.ofNat 32 h.sp + BitVec.ofNat 32 4294967295)) := by
    simp only [sA, s9, stage2NoEventWalkNext, cells, closeGepCells, closeIdxCells, closeObjTail,
      braceCloseObjCells, List.cons_append, List.nil_append]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    rw [lookupName_cons_self]
  have hk4S : lookupName sA.env "%k.4"
      = some (.int 64 (BitVec.ofNat 64 (k + 1))) := by
    simp only [sA, s9, stage2NoEventWalkNext, cells, closeGepCells, closeIdxCells, closeObjTail,
      braceCloseObjCells, List.cons_append, List.nil_append]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    rw [lookupName_cons_self]
  have halenS : lookupName sA.env "%alen.6"
      = some (.int 64 (BitVec.ofNat 64 K.arena.length)) := by
    simp only [sA, s9, stage2NoEventWalkNext, cells, closeGepCells, closeIdxCells, closeObjTail,
      braceCloseObjCells, List.cons_append, List.nil_append]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    rw [lookupName_cons_self]
  have harenaS : lookupName sA.env "%arena.8"
      = some (.int 64 (BitVec.ofNat 64 K.arenaWord)) := by
    simp only [sA, s9, stage2NoEventWalkNext, cells, closeGepCells, closeIdxCells, closeObjTail,
      braceCloseObjCells, List.cons_append, List.nil_append]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    rw [lookupName_cons_self]
  have htermsS : lookupName sA.env "%terms.6"
      = some (.int 64 (BitVec.ofNat 64 K.terms + BitVec.ofNat 64 2)) := by
    simp only [sA, s9, stage2NoEventWalkNext, cells, closeGepCells, closeIdxCells, closeObjTail,
      braceCloseObjCells, List.cons_append, List.nil_append]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    rw [lookupName_cons_self]
  have htokS : lookupName sA.env "%tokens.6"
      = some (.int 64 (BitVec.ofNat 64 K.tok + BitVec.ofNat 64 1)) := by
    simp only [sA, s9, stage2NoEventWalkNext, cells, closeGepCells, closeIdxCells, closeObjTail,
      braceCloseObjCells, List.cons_append, List.nil_append]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    rw [lookupName_cons_self]
  -- the base lookups at the endpoint
  have hb10 : ∀ n v, (n, v) ∈ stage2NoEventWalkBaseValues K →
      lookupName sA.env n = some v := by
    have h1 := stage2NoEventCycleBase (K := K) hbase3
      (cs := nodeBlock35Cells 0) (names := ["%Pivot36"]) rfl (by decide)
    have h2 := stage2NoEventCycleBase (K := K) h1
      (cs := leafBlock33Cells 1) (names := ["%SwitchLeaf34"]) rfl (by decide)
    have h3 := stage2NoEventCycleBase (K := K) h2
      (cs := doBody391Cells (BitVec.ofNat 64 K.tok) (BitVec.ofNat 64 K.terms))
      (names := ["%add393", "%inc392"]) rfl (by decide)
    have h4 := stage2NoEventCycleBase (K := K) h3
      (cs := closeObjTail (BitVec.ofNat 32 h.sp) ++
        braceCloseObjCells (BitVec.ofNat 32 h.sp) (BitVec.ofNat 64 (k + 1))
          (BitVec.ofNat 64 K.arena.length) (BitVec.ofNat 64 K.arenaWord)
          (BitVec.ofNat 64 K.terms + BitVec.ofNat 64 2)
          (BitVec.ofNat 64 K.tok + BitVec.ofNat 64 1))
      (names := ["%tobool342.not", "%dec", "%tokens.6", "%terms.6", "%arena.8",
        "%alen.6", "%k.4", "%sp.2"]) rfl (by decide)
    have h5 := stage2NoEventCycleBase (K := K) h4
      (cs := ("%49", .int 8 (BitVec.ofNat 8 (bytesToNat bs))) ::
        closeGepCells a ++ closeIdxCells
          (BitVec.ofNat 32 h.sp + BitVec.ofNat 32 4294967294))
      (names := ["%49", "%arrayidx346", "%idxprom345", "%sub344"]) rfl (by decide)
    intro n v hv
    exact h5 n v hv
  -- the endpoint's dispatch selection at the `if.then343` edge
  have hsel : PhiSelects (stateAt sA.env sA) "if.then343" afterValuePhiSpecs
      [("%frame.6", .int 8 (BitVec.ofNat 8 (bytesToNat bs))),
       ("%sp.4", .int 32 (BitVec.ofNat 32
         (BitVec.ofNat 32 h.sp + BitVec.ofNat 32 4294967295).toNat)),
       ("%k.6", .int 64 (BitVec.ofNat 64 (k + 1))),
       ("%alen.8", .int 64 (BitVec.ofNat 64 K.arena.length)),
       ("%arena.10", .int 64 (BitVec.ofNat 64 K.arenaWord)),
       ("%terms.8", .int 64 (BitVec.ofNat 64
         (stage2NoEventWalkCloseBraceCarry K).terms)),
       ("%tokens.8", .int 64 (BitVec.ofNat 64
         (stage2NoEventWalkCloseBraceCarry K).tok))] := by
    refine PhiSelects.cons (op := .reg "%49") (by decide) ?_
      (PhiSelects.cons (op := .reg "%dec") (by decide) ?_
        (PhiSelects.cons (op := .reg "%k.4") (by decide) ?_
          (PhiSelects.cons (op := .reg "%alen.6") (by decide) ?_
            (PhiSelects.cons (op := .reg "%arena.8") (by decide) ?_
              (PhiSelects.cons (op := .reg "%terms.6") (by decide) ?_
                (PhiSelects.cons (op := .reg "%tokens.6") (by decide) ?_
                  PhiSelects.nil))))))
    all_goals
      simp only [stage2NoEventWalkCloseBraceCarry, stateAt, evalOperand, h49S,
        hdecS, hk4S, halenS, harenaS, htermsS, htokS, stage2NoEventWalkOfNat_add,
        BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have hbsClose : K.bs[lane]? = some (0x7D : UInt8) := by
    have hy : byte = (0x7D : UInt8) :=
      stage2NoEventWalk_uint8_eq_of_toNat (by rw [hbyte]; decide)
    simpa [hy] using hbs
  have htraceC : Stage2NoEventWalkTrace (stage2NoEventWalkCloseBraceCarry K) :=
    Stage2NoEventWalkTrace.closeBrace htrace hbsClose
  refine ⟨sA, ⟨hrun, l9.inv'⟩, ⟨?_⟩⟩
  refine ⟨l9.inv', rfl, _, (BitVec.ofNat 32 h.sp + BitVec.ofNat 32 4294967295).isLt,
    bytesToNat bs, stage2NoEventWalkBytesToNat_lt hbsLen, ?_,
    ⟨"if.then343", rfl, hsel⟩, hb10, hbpos, htraceC⟩
  exact Stage2NoEventWalkCount.step (a := 1) (b := 1) hcount rfl rfl (by omega)

/-! ### The two sub-arms' statements

The `,` arm and the `}` arm as one split: the byte at the entry's lane decides
which; the price and the endpoint are the chosen route's. -/

/-- **The frame-zero arm's statement.**  From a frame-zero `after_value` entry,
the byte at the entry's lane takes exactly one of the two routes: the comma to
the key route's boundary (seven blocks, the carry unchanged) or the close brace
to the next `after_value` entry (eight at the top level, nine at a nested
depth, at the close-brace carry). -/
theorem stage2NoEventWalkFrameZeroArm {calls : Calls} {mem : Mem}
    {K : Stage2NoEventWalkCarry} {k : Nat} {s : State}
    (h : Stage2NoEventWalkFrameZeroSrc calls mem K k s)
    {lane : Nat} {byte : UInt8}
    (hk : K.ent[k]? = some lane) (hbs : K.bs[lane]? = some byte)
    (hcls : byte.toNat = 44 ∨ byte.toNat = 125) :
    (byte.toNat = 44 →
      k + 1 < K.nep →
      ∃ s' : State,
        Stage2NoEventWalkSegment calls mem K s K s' 7 ∧
        Nonempty (Stage2NoEventWalkFrameZeroCommaBoundary calls mem K k s')) ∧
    (byte.toNat = 125 →
      (h.sp = 1 →
        ∃ s' : State,
          Stage2NoEventWalkSegment calls mem K s
            (stage2NoEventWalkCloseBraceCarry K) s' 8 ∧
          Nonempty (Stage2NoEventWalkAfterValueEntry calls mem
            (stage2NoEventWalkCloseBraceCarry K) (k + 1) s')) ∧
      (2 ≤ h.sp → ∀ {a : Nat} {bs : List UInt8},
        readBytes s.mem a 1 = some bs →
        a = closeReadAddr K.stk
          (BitVec.ofNat 32 h.sp + BitVec.ofNat 32 4294967294).toNat →
        bs.length = 1 →
        ∃ s' : State,
          Stage2NoEventWalkSegment calls mem K s
            (stage2NoEventWalkCloseBraceCarry K) s' 9 ∧
          Nonempty (Stage2NoEventWalkAfterValueEntry calls mem
            (stage2NoEventWalkCloseBraceCarry K) (k + 1) s'))) := by
  constructor
  · intro h44 hknext
    exact stage2NoEventWalkFrameZeroCommaArm h hk hbs h44 hknext
  · intro h125
    constructor
    · intro hspOne
      exact stage2NoEventWalkFrameZeroBraceTop h hspOne hk hbs h125
    · intro hspTwo a bs hpop hpopAddr hbsLen
      exact stage2NoEventWalkFrameZeroBraceDeep h hspTwo hk hbs h125 hpop hpopAddr hbsLen

/-! ### Axiom footprints -/

#print axioms stage2NoEventICmp_eq_one
#print axioms ifEnd378_denote_cmp
#print axioms ifEnd378_denote_frameZero
#print axioms nodeBlock35_denote
#print axioms leafBlock31_denote
#print axioms leafBlock33_denote
#print axioms doBody391_denote
#print axioms ifEnd409_denote
#print axioms Stage2NoEventWalkTrace.closeBrace
#print axioms stage2NoEventWalkFrameZeroToThen384
#print axioms stage2NoEventWalkFrameZeroCommaDelta
#print axioms stage2NoEventWalkFrameZeroCommaArm
#print axioms closeObjPhi_denote_doBody391
#print axioms link_closeObj_doBody391_live
#print axioms link_closeObj_doBody391_zero
#print axioms stage2NoEventWalkFrameZeroBraceTop
#print axioms stage2NoEventWalkFrameZeroBraceDeep
#print axioms stage2NoEventWalkFrameZeroArm

end LeanLLVM.Refinement
