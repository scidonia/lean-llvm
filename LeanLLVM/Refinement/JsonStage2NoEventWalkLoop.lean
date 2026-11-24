/-
The no-event walk's continuing loop: the head's continuation, the container
dispatch class, and the brace's push rows.

`JsonStage2NoEventWalkInv` states the invariant at the loop head and seeds it;
`JsonStage2NoEventWalkTerminal` proves the terminal arms and the entry
bootstrap.  This module starts the loop body: the link vocabulary the body's
control steps compose in, the head's own read row, the four delimiter dispatch
rows, and the two openers' push rows through the stack write and the depth, each a
chain of named block steps ending at a named state.

**The cycle is not closed here.**  The body's only return to the head
(`if.end.peel`) is through `value.outer.backedge`, from `LeafBlock37` (a comma at
depth zero) or `if.end303` (a completed key/value pair); a delimiter row leaves
the head and lands in the next dispatch, so it is a fragment of that cycle and
not a cycle of its own.  The return to the head — and the readings' updates for
any row that contains a count store — are the count class's, the next checkpoint;
no row in this module contains a count store, so the readings are carried here
and the `htok` paragraph below is that next checkpoint's, not this one's.

**The head row's split.**  `if.end.peel` opens with a nine-`phi` run the
predecessor edge binds.  The row below is stated at the state after that run
(the state every head visit enters from), and the split is pinned
(`loopHeadBlock_find`, `loopHead_split`): the row's block list is the six read
instructions, and the `phi` run is the edge's, belonging to whoever produces the
head state.

**The register facts.**  `Params`, `Locals` and `Acc` are the three predicates
`WalkInv` keeps out of the invariant; a row transports them by reading the
registers it did not write, and no row here writes one of `Acc`'s.

**`WalkInv` is frozen and this module does not extend it.**  The one
`Inv`-preservation obligation of a stack write is a named lemma
(`Stage2NoEventWalkInv.stack_write`), and a row that writes nothing transports the
invariant through `mem_congr`.

**The `htok` guard (for the next checkpoint).**  The payload rows still to come
contain count stores (`if.end74`, `if.then81`, `if.then334`), which move the
carry's `tok`/`terms` by the block's constants; the invariant's `tokLe` is then
re-established only under `K.tok + c ≤ K.n`.  That guard is to be a named
hypothesis of those rows, not a change to the frozen invariant: the count class
must discharge it from the entry bound (`WalkInv.inside`) and the count-token
relation it establishes, and if it cannot, that is a re-approval on `WalkInv` for
the planner, not an edit here.  No row in this module contains a count store, so
none takes the guard: the readings are carried across all of them.

**The brace's push.**  The four delimiter rows end at the dispatch's handoff
(`if.then9`, `if.then35.peel`, `scalar`).  For the brace, the module goes on:
`if.then9`'s seven-`phi` run is the edge's and is pinned with the guard
(`ifThen9_split`, `ifThen9_guard`); `if.end19` at a non-zero depth hands to
`if.then20`, whose four instructions write `%frame` at `%stk + (%sp - 1)` inside
`%stk`'s region; `if.end23` raises the depth and tests the next entry.
`Stage2NoEventWalkInv.stack_write` is the preservation `link_ifThen20` consumes,
with the address `stage2NoEventStoreAddr` and the region membership from the
`%sp ≤ 519` guard.

**The bracket's push.**  The bracket's slice has no `phi`: `%1`, `%frame.0.ph1402`,
`%sp.0.ph1403`, `%inc.peel` and `%nep` are bound before the branch, so
`stage2NoEventRow_bracketPush` is a chain of real block steps —
`if.then35.peel` (the `519` guard), `if.end45.peel` (the zero test), `if.then47.peel`
(`%4 = %1 - 1`, the store at `%stk + (%1 - 1)`), `if.end51.peel` (the live-entry
guard) — ending at `if.end327.peel`'s entry, the block that reads the next entry's
byte.  Its store consumes `stack_write` with the address `stage2NoEventStoreAddr64`
and the region membership from `%1 ≤ 519`.  `link_ifEnd327peel` is that block's `]`
link (to `if.then334`), stated for the closer checkpoint.

**What this module does not do.**  It does not prove the closers
(`if.then81`/`if.then334` reaching `close_obj`/`close_arr`), any row containing a
count store (`if.end74` here, `if.then81`, `if.then334`), or the count class that
returns to the head through `value.outer.backedge`, and it does not state the base
step from `EntryState`.  `stage2NoEventRow_bracePush` ends at `if.end74` and
`stage2NoEventRow_bracketPush` at `if.end327.peel` — the count's block and the
next dispatch — each with one stack byte written and the depth raised, and the
readings carried.
-/
import LeanLLVM.Refinement.JsonStage2NoEventWalkTerminal

set_option autoImplicit false
set_option maxRecDepth 8192

namespace LeanLLVM.Refinement

open LeanLLVM
open LeanLLVM.Refinement.JsonStage2NoEventIR
open LeanLLVM.Refinement.BlockEval
open LeanLLVM.Refinement.JsonS1MasksIR
  (evalInstr_icmp evalInstr_load evalInstr_zext evalInstr_binop evalInstr_store)

/-! ### The link vocabulary

The no-event analogue of the certified walk's `WalkLink`/`WalkChain`: one control
step from an invariant-carrying state to another.  `mem` is the caller's staging
and does not move; a step changes the state's own memory. -/

/-- One control step to an invariant-carrying target. -/
structure Stage2NoEventWalkLink (calls : Calls) (K : Stage2NoEventWalkCarry)
    (mem : Mem) (s : State) (K' : Stage2NoEventWalkCarry) (s' : State) : Prop where
  /-- The invariant holds at the link's source. -/
  inv : Stage2NoEventWalkInv K mem s
  /-- The step is one control step of the body. -/
  step : step calls stage2NoEventBody s = .jump s'
  /-- The invariant holds at the link's target. -/
  inv' : Stage2NoEventWalkInv K' mem s'

/-- A trace of links: the invariant at its head and at its tail. -/
inductive Stage2NoEventWalkChain (calls : Calls) (mem : Mem) :
    Stage2NoEventWalkCarry → State → Stage2NoEventWalkCarry → State → Prop
  | nil {K : Stage2NoEventWalkCarry} {s : State} (h : Stage2NoEventWalkInv K mem s) :
      Stage2NoEventWalkChain calls mem K s K s
  | tail {K K' K'' : Stage2NoEventWalkCarry} {s s' s'' : State}
      (hl : Stage2NoEventWalkLink calls K mem s K' s')
      (ht : Stage2NoEventWalkChain calls mem K' s' K'' s'') :
      Stage2NoEventWalkChain calls mem K s K'' s''

/-- A link's step, at `runFuel`: one control step is one fuel unit. -/
theorem stage2NoEventWalkLink_runFuel {calls : Calls} {K K' : Stage2NoEventWalkCarry}
    {mem : Mem} {s s' : State} (hl : Stage2NoEventWalkLink calls K mem s K' s')
    (n : Nat) :
    runFuel calls (1 + n) stage2NoEventBody s = runFuel calls n stage2NoEventBody s' := by
  have hs : step calls stage2NoEventBody s = .jump s' := hl.step
  rw [show 1 + n = n + 1 from by omega]
  simp only [runFuel, hs]

/-- **The trace is a run.**  A chain of `k` links runs for `k` steps of fuel and
leaves exactly the fuel the tail needs. -/
theorem Stage2NoEventWalkChain.steps {calls : Calls} {mem : Mem}
    {K K' : Stage2NoEventWalkCarry} {s s' : State}
    (h : Stage2NoEventWalkChain calls mem K s K' s') :
    ∃ k, ∀ n, runFuel calls (k + n) stage2NoEventBody s =
      runFuel calls n stage2NoEventBody s' := by
  induction h with
  | nil => exact ⟨0, fun n => by simp⟩
  | tail hl _ ih =>
      obtain ⟨k, hk⟩ := ih
      exact ⟨k + 1, fun n => by
        rw [show k + 1 + n = 1 + (k + n) from by omega,
          stage2NoEventWalkLink_runFuel hl, hk]⟩

/-! ### The invariant's two memory obligations -/

/-- **The invariant at a state with the same memory.** -/
theorem Stage2NoEventWalkInv.mem_congr {K : Stage2NoEventWalkCarry} {mem : Mem}
    {s s' : State} (h : Stage2NoEventWalkInv K mem s) (hm : s'.mem = s.mem) :
    Stage2NoEventWalkInv K mem s' := by
  refine { h with walkPresent := ?_, walkFrame := ?_ }
  · intro a ha
    show ∃ b, readByte s'.mem a = some b
    rw [hm]
    exact h.walkPresent a ha
  · intro a ha
    show readByte s'.mem a = readByte mem a
    rw [hm]
    exact h.walkFrame a ha

/-- **The invariant across a write inside the run's own regions.**  Presence
grows over the written bytes; silence is `UnchangedOutside.write_inside` at the
same list.  No other field of the invariant mentions the state's memory. -/
theorem Stage2NoEventWalkInv.stack_write {K : Stage2NoEventWalkCarry} {mem : Mem}
    {s : State} (h : Stage2NoEventWalkInv K mem s) {a : Nat} {bs : List UInt8}
    (hw : ∀ k, k < bs.length → inRegions
      (stage2NoEventRunRegions K.scratch K.scratchcap K.stk K.e K.c K.d ++
        [(K.next0, K.nextEnd - K.next0)]) (a + k)) :
    Stage2NoEventWalkInv K mem { s with mem := writeBytes s.mem a bs } := by
  refine { h with walkPresent := ?_, walkFrame := ?_ }
  · intro x hx
    by_cases hin : a ≤ x ∧ x < a + bs.length
    · obtain ⟨hle, hlt⟩ := hin
      have hk : x - a < bs.length := by omega
      have hb := readByte_writeBytes_at s.mem bs a (x - a) hk
      rw [Nat.add_sub_of_le hle] at hb
      exact ⟨bs.getD (x - a) 0, hb⟩
    · have hout : x < a ∨ a + bs.length ≤ x := by omega
      obtain ⟨v, hv⟩ := h.walkPresent x hx
      refine ⟨v, ?_⟩
      rw [readByte_writeBytes_outside s.mem bs (start := a) (addr := x) hout]
      exact hv
  · exact UnchangedOutside.write_inside h.walkFrame (fun k hk => hw k hk)

/-! ### The head and dispatch blocks, pinned -/

/-- `if.end.peel`'s nine-`phi` run: the predecessor edge's. -/
def loopHeadPhiInstrs : List Instr :=
  [ Instr.phi "%wide.trip.count1409" (Ty.int 64)
      [("value.outer.backedge", (Operand.reg "%wide.trip.count")),
       ("if.end.peel.preheader", (Operand.imm (.int 64 (BitVec.ofNat 64 520))))],
    Instr.phi "%1" (Ty.int 64)
      [("value.outer.backedge", (Operand.reg "%45")),
       ("if.end.peel.preheader", (Operand.imm (.int 64 (BitVec.ofNat 64 0))))],
    Instr.phi "%tokens.0.ph1408" (Ty.int 64)
      [("value.outer.backedge", (Operand.reg "%tokens.0.ph.be")),
       ("if.end.peel.preheader", (Operand.imm (.int 64 (BitVec.ofNat 64 0))))],
    Instr.phi "%terms.0.ph1407" (Ty.int 64)
      [("value.outer.backedge", (Operand.reg "%terms.0.ph.be")),
       ("if.end.peel.preheader", (Operand.imm (.int 64 (BitVec.ofNat 64 0))))],
    Instr.phi "%arena.0.ph1406" (Ty.int 64)
      [("value.outer.backedge", (Operand.reg "%arena.0.ph.be")),
       ("if.end.peel.preheader", (Operand.imm (.int 64 (BitVec.ofNat 64 0))))],
    Instr.phi "%alen.0.ph1405" (Ty.int 64)
      [("value.outer.backedge", (Operand.reg "%alen.0.ph.be")),
       ("if.end.peel.preheader", (Operand.imm (.int 64 (BitVec.ofNat 64 0))))],
    Instr.phi "%k.0.ph1404" (Ty.int 64)
      [("value.outer.backedge", (Operand.reg "%k.0.ph.be")),
       ("if.end.peel.preheader", (Operand.imm (.int 64 (BitVec.ofNat 64 0))))],
    Instr.phi "%sp.0.ph1403" (Ty.int 32)
      [("value.outer.backedge", (Operand.reg "%sp.0.ph.be")),
       ("if.end.peel.preheader", (Operand.imm (.int 32 (BitVec.ofNat 32 0))))],
    Instr.phi "%frame.0.ph1402" (Ty.int 8)
      [("value.outer.backedge", (Operand.reg "%frame.0.ph.be")),
       ("if.end.peel.preheader", (Operand.imm (.int 8 (BitVec.ofNat 8 0))))] ]

/-- `if.end.peel`'s six instructions after its `phi` run: the entry's document
index, its byte, and the next entry's cursor. -/
def loopHeadReadInstrs : List Instr :=
  [ Instr.binop "%inc.peel" BinOp.add 64 (Operand.reg "%k.0.ph1404")
      (Operand.imm (.int 64 (BitVec.ofNat 64 1))),
    Instr.gep "%arrayidx.peel" (Ty.int 32) (Operand.reg "%ep")
      (Operand.reg "%k.0.ph1404"),
    Instr.load "%2" (Ty.int 32) (Operand.reg "%arrayidx.peel"),
    Instr.zext "%idxprom.peel" 32 64 (Operand.reg "%2"),
    Instr.gep "%arrayidx6.peel" (Ty.int 8) (Operand.reg "%b")
      (Operand.reg "%idxprom.peel"),
    Instr.load "%3" (Ty.int 8) (Operand.reg "%arrayidx6.peel") ]

/-- `if.end.peel`, pinned. -/
def loopHeadBlock : Block :=
  { name := "if.end.peel", instrs := loopHeadPhiInstrs ++ loopHeadReadInstrs,
    term := Term.br "NodeBlock5" }

theorem loopHeadBlock_find :
    stage2NoEventBody.findBlock "if.end.peel" = some loopHeadBlock := by
  decide

/-- The head block's split: the `phi` run, then the read row. -/
theorem loopHead_split :
    loopHeadBlock.instrs = loopHeadPhiInstrs ++ loopHeadReadInstrs := rfl

/-- `NodeBlock5`: the byte against 91. -/
def nodeBlock5Instrs : List Instr :=
  [ Instr.icmp "%Pivot6" IPred.slt 8 (Operand.reg "%3")
      (Operand.imm (.int 8 (BitVec.ofNat 8 91))) ]

/-- `NodeBlock5`, pinned. -/
def nodeBlock5Block : Block :=
  { name := "NodeBlock5", instrs := nodeBlock5Instrs,
    term := Term.condbr (Operand.reg "%Pivot6") "LeafBlock" "NodeBlock" }

theorem nodeBlock5Block_find :
    stage2NoEventBody.findBlock "NodeBlock5" = some nodeBlock5Block := by
  decide

/-- `NodeBlock`: the byte against 123. -/
def nodeBlockInstrs : List Instr :=
  [ Instr.icmp "%Pivot" IPred.slt 8 (Operand.reg "%3")
      (Operand.imm (.int 8 (BitVec.ofNat 8 123))) ]

/-- `NodeBlock`, pinned. -/
def nodeBlockBlock : Block :=
  { name := "NodeBlock", instrs := nodeBlockInstrs,
    term := Term.condbr (Operand.reg "%Pivot") "LeafBlock1" "LeafBlock3" }

theorem nodeBlockBlock_find :
    stage2NoEventBody.findBlock "NodeBlock" = some nodeBlockBlock := by
  decide

/-- `LeafBlock3`: the byte against 123, the brace's leaf. -/
def leafBlock3Instrs : List Instr :=
  [ Instr.icmp "%SwitchLeaf4" IPred.eq 8 (Operand.reg "%3")
      (Operand.imm (.int 8 (BitVec.ofNat 8 123))) ]

/-- `LeafBlock3`, pinned. -/
def leafBlock3Block : Block :=
  { name := "LeafBlock3", instrs := leafBlock3Instrs,
    term := Term.condbr (Operand.reg "%SwitchLeaf4") "if.then9" "scalar" }

theorem leafBlock3Block_find :
    stage2NoEventBody.findBlock "LeafBlock3" = some leafBlock3Block := by
  decide

/-- `LeafBlock1`: the byte against 91, the bracket's leaf. -/
def leafBlock1Instrs : List Instr :=
  [ Instr.icmp "%SwitchLeaf2" IPred.eq 8 (Operand.reg "%3")
      (Operand.imm (.int 8 (BitVec.ofNat 8 91))) ]

/-- `LeafBlock1`, pinned. -/
def leafBlock1Block : Block :=
  { name := "LeafBlock1", instrs := leafBlock1Instrs,
    term := Term.condbr (Operand.reg "%SwitchLeaf2") "if.then35.peel" "scalar" }

theorem leafBlock1Block_find :
    stage2NoEventBody.findBlock "LeafBlock1" = some leafBlock1Block := by
  decide

-- The blocks above are the parsed body's, not transcriptions of it.
#guard decide (stage2NoEventBody.findBlock "if.end.peel" ≠ none)
#guard decide (stage2NoEventBody.findBlock "NodeBlock5" ≠ none)
#guard decide (stage2NoEventBody.findBlock "NodeBlock" ≠ none)
#guard decide (stage2NoEventBody.findBlock "LeafBlock3" ≠ none)
#guard decide (stage2NoEventBody.findBlock "LeafBlock1" ≠ none)

/-! ### Instruction steps the rows need -/

/-- A comparison against an immediate, at any predicate and width. -/
theorem stage2NoEventWalk_denote_icmp_imm (calls : Calls) (env : Env) (s : State)
    (d a : String) (p : IPred) (w : Nat) {x c : BitVec w}
    (ha : lookupName env a = some (.int w x)) (is : List Instr) :
    denoteCode calls (.icmp d p w (.reg a) (.imm (.int w c)) :: is) (stateAt env s) =
      denoteCode calls is (stateAt ((d, .int 1 (evalICmp p x c)) :: env) s) := by
  have ha' : evalOperand (stateAt env s) (.reg a) = some (.int w x) := by
    simp only [stateAt, evalOperand, ha]
  have hb' : evalOperand (stateAt env s) (.imm (.int w c)) = some (.int w c) := by
    simp only [stateAt, evalOperand, Const.toValue]
  have hstep : evalInstr calls (stateAt env s)
      (.icmp d p w (.reg a) (.imm (.int w c))) =
      some ((stateAt env s).bind d (.int 1 (evalICmp p x c))) :=
    evalInstr_icmp ha' hb'
  rw [denoteCode_cons_of _ _ _ _ _ hstep]
  simp only [stateAt, State.bind]

/-- A load of an integer of any width, from the bytes the state's memory holds. -/
theorem stage2NoEventWalk_denote_load_int (calls : Calls) (env : Env) (s : State)
    (d p : String) (w : Nat) {a : Nat} {bs : List UInt8}
    (hw : w ≠ 0) (hp : lookupName env p = some (.ptr a))
    (hv : readBytes s.mem a ((w + 7) / 8) = some bs) (is : List Instr) :
    denoteCode calls (.load d (.int w) (.reg p) :: is) (stateAt env s) =
      denoteCode calls is
        (stateAt ((d, .int w (BitVec.ofNat w (bytesToNat bs))) :: env) s) := by
  have hv' : loadValue s.mem (.int w) a =
      some (.int w (BitVec.ofNat w (bytesToNat bs))) := by
    simp only [loadValue, hw, if_false, hv]
  have hstep : evalInstr calls (stateAt env s) (.load d (.int w) (.reg p)) =
      some ((stateAt env s).bind d (.int w (BitVec.ofNat w (bytesToNat bs)))) := by
    rw [evalInstr_load (a := a) (hp := by simp only [stateAt, evalOperand, hp])
      (hv := by simpa only [stateAt] using hv')]
  rw [denoteCode_cons_of _ _ _ _ _ hstep]
  simp only [stateAt, State.bind]

/-- A `gep i32` at a register offset. -/
theorem stage2NoEventWalk_denote_gep32 (calls : Calls) (env : Env) (s : State)
    (d base off : String) {a : Nat} {o : BitVec 64}
    (hb : lookupName env base = some (.ptr a))
    (ho : lookupName env off = some (.int 64 o))
    (hs : (o.signExtend 64).toNat < 2 ^ 63) (is : List Instr) :
    denoteCode calls (.gep d (.int 32) (.reg base) (.reg off) :: is) (stateAt env s) =
      denoteCode calls is
        (stateAt ((d, .ptr (a + (o.signExtend 64).toNat * 4)) :: env) s) := by
  have hb' : evalOperand (stateAt env s) (.reg base) = some (.ptr a) := by
    simp only [stateAt, evalOperand, hb]
  have ho' : evalOperand (stateAt env s) (.reg off) = some (.int 64 o) := by
    simp only [stateAt, evalOperand, ho]
  have hstep : evalInstr calls (stateAt env s)
      (.gep d (.int 32) (.reg base) (.reg off)) =
      some ((stateAt env s).bind d (.ptr (a + (o.signExtend 64).toNat * 4))) := by
    simp only [evalInstr, hb', ho', hs, ite_true, Ty.sizeBytes]
  rw [denoteCode_cons_of _ _ _ _ _ hstep]
  simp only [stateAt, State.bind]

/-- A zero-extended 32-bit word's `Nat`. -/
theorem stage2NoEventOfNat32_toNat {x : Nat} (h : x < 2 ^ 32) :
    (BitVec.ofNat 32 x).toNat = x := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

/-- The `gep i8` bound, at a lane below `2 ^ 32`. -/
theorem stage2NoEventLane_signExtend_lt {x : Nat} (h : x < 2 ^ 32) :
    ((BitVec.ofNat 64 x).signExtend 64).toNat < 2 ^ 63 := by
  have hx : ((BitVec.ofNat 64 x).signExtend 64).toNat = x := by
    simp only [BitVec.signExtend_eq, BitVec.setWidth_eq, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : x < 2 ^ 64)]
  omega

/-! ### One control step, from a block's denotation -/

/-- A block whose terminator branches on a computed one-bit condition: the link's
step at the true arm. -/
theorem stage2NoEventWalk_step_condbr_true {calls : Calls} {f : Function}
    {s s' : State} {b : Block} {c t el : String}
    (hfind : f.findBlock s.pc = some b)
    (hcode : denoteCode calls b.instrs s = some s')
    (hterm : b.term = Term.condbr (Operand.reg c) t el)
    (hc : lookupName s'.env c = some (.int 1 (1 : BitVec 1))) :
    step calls f s = .jump { s' with pc := t, pre := some s'.pc } := by
  have heval : evalOperand s' (Operand.reg c) = some (.int 1 (1 : BitVec 1)) := by
    simp only [evalOperand, hc]
  simp [step, hfind, hcode, hterm, execTerm, heval]

/-- The same step at the false arm. -/
theorem stage2NoEventWalk_step_condbr_false {calls : Calls} {f : Function}
    {s s' : State} {b : Block} {c t el : String}
    (hfind : f.findBlock s.pc = some b)
    (hcode : denoteCode calls b.instrs s = some s')
    (hterm : b.term = Term.condbr (Operand.reg c) t el)
    (hc : lookupName s'.env c = some (.int 1 (0 : BitVec 1))) :
    step calls f s = .jump { s' with pc := el, pre := some s'.pc } := by
  have heval : evalOperand s' (Operand.reg c) = some (.int 1 (0 : BitVec 1)) := by
    simp only [evalOperand, hc]
  simp [step, hfind, hcode, hterm, execTerm, heval]

/-- A block whose terminator is an unconditional branch. -/
theorem stage2NoEventWalk_step_br {calls : Calls} {f : Function} {s s' : State}
    {b : Block} {dest : String}
    (hfind : f.findBlock s.pc = some b)
    (hcode : denoteCode calls b.instrs s = some s')
    (hterm : b.term = Term.br dest) :
    step calls f s = .jump { s' with pc := dest, pre := some s'.pc } := by
  simp only [step, hfind, hcode, hterm, execTerm]

/-! ### The head's read row

From the state a head visit enters from (the `phi` run already bound), the six
instructions bind the entry's index and its byte, and the block branches to
`NodeBlock5`.  The two reads are the state's memory; `hlane`/`hbyte` are the bytes
it holds, and the walk's frame is what relates them to the caller's staging. -/

/-- The head's read row: the six instructions after the `phi` run. -/
theorem stage2NoEventLoopHead_denote (calls : Calls) (env : Env) (s : State)
    {k : BitVec 64} {ep b : Nat} {bs4 bs1 : List UInt8}
    (hk : lookupName env "%k.0.ph1404" = some (.int 64 k))
    (hep : lookupName env "%ep" = some (.ptr ep))
    (hb : lookupName env "%b" = some (.ptr b))
    (hklt : (k.signExtend 64).toNat < 2 ^ 63)
    (hlane : readBytes s.mem (ep + (k.signExtend 64).toNat * 4) 4 = some bs4)
    (hlanelt : bytesToNat bs4 < 2 ^ 32)
    (hbyte : readBytes s.mem (b + ((BitVec.ofNat 64 (bytesToNat bs4)).signExtend 64).toNat)
      1 = some bs1) :
    denoteCode calls loopHeadReadInstrs (stateAt env s) =
      some (stateAt
        (("%3", .int 8 (BitVec.ofNat 8 (bytesToNat bs1))) ::
          ("%arrayidx6.peel",
            .ptr (b + ((BitVec.ofNat 64 (bytesToNat bs4)).signExtend 64).toNat)) ::
          ("%idxprom.peel", .int 64 (BitVec.ofNat 64 (bytesToNat bs4))) ::
          ("%2", .int 32 (BitVec.ofNat 32 (bytesToNat bs4))) ::
          ("%arrayidx.peel", .ptr (ep + (k.signExtend 64).toNat * 4)) ::
          ("%inc.peel", .int 64 (k + BitVec.ofNat 64 1)) :: env) s) := by
  unfold loopHeadReadInstrs
  rw [denoteCode_add_imm (calls := calls) (env := env) (s := s)
    (d := "%inc.peel") (a := "%k.0.ph1404") hk]
  rw [stage2NoEventWalk_denote_gep32 (calls := calls)
    (env := ("%inc.peel", .int 64 (k + BitVec.ofNat 64 1)) :: env) (s := s)
    (d := "%arrayidx.peel") (base := "%ep") (off := "%k.0.ph1404")
    (a := ep) (o := k) hep
    (by rw [lookupName_cons_ne _ _ (by decide)]; exact hk) hklt]
  rw [stage2NoEventWalk_denote_load_int (calls := calls)
    (env := ("%arrayidx.peel", .ptr (ep + (k.signExtend 64).toNat * 4)) ::
      ("%inc.peel", .int 64 (k + BitVec.ofNat 64 1)) :: env) (s := s)
    (d := "%2") (p := "%arrayidx.peel")
    (a := ep + (k.signExtend 64).toNat * 4) (w := 32) (bs := bs4) (hw := by decide)
    (by simp only [lookupName_cons_self])
    (by simpa using hlane)]
  rw [denoteCode_zext (calls := calls) (env := _) (s := s) (d := "%idxprom.peel")
    (v := "%2") (wIn := 32) (wOut := 64)
    (x := BitVec.ofNat 32 (bytesToNat bs4))
    (by simp only [lookupName_cons_self])]
  rw [stage2NoEventOfNat32_toNat hlanelt]
  rw [denoteCode_gep8_reg (calls := calls) (env := _) (s := s)
    (d := "%arrayidx6.peel") (base := "%b") (off := "%idxprom.peel")
    (a := b) (idx := BitVec.ofNat 64 (bytesToNat bs4))
    (by rw [lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide)]; exact hb)
    (by simp only [lookupName_cons_self])
    (stage2NoEventLane_signExtend_lt hlanelt)]
  rw [stage2NoEventWalk_denote_load_int (calls := calls) (env := _) (s := s)
    (d := "%3") (p := "%arrayidx6.peel")
    (a := b + ((BitVec.ofNat 64 (bytesToNat bs4)).signExtend 64).toNat) (w := 8)
    (bs := bs1) (hw := by decide)
    (by simp only [lookupName_cons_self]) (by simpa using hbyte)]
  simp only [denoteCode_nil]


/-! ### The container dispatch class

The head branches to `NodeBlock5`, and the four delimiter bytes take three-block
paths from there:

| byte | `NodeBlock5` (slt 91) | `NodeBlock` (slt 123) | leaf | handoff |
|---|---|---|---|---|
| `{` 123 | false → `NodeBlock` | false → `LeafBlock3` | eq 123 → `if.then9` | the brace's push |
| `[` 91  | false → `NodeBlock` | true → `LeafBlock1`  | eq 91 → `if.then35.peel` | the bracket's push |
| `}` 125 | false → `NodeBlock` | false → `LeafBlock3` | eq 123 false → `scalar` | the value path |
| `]` 93  | false → `NodeBlock` | true → `LeafBlock1`  | eq 91 false → `scalar` | the value path |

`}` and `]` are **not** closers at the entry head: the body's leaf tests are 34,
91, 123 (and else the value path), so a closing delimiter at a *new* entry falls
through to `scalar`.  The closer blocks (`if.then81` → `close_obj`,
`if.then334` → `close_arr`) are dispatched from `NodeBlock21` / `if.end327.peel`
(after an opener consumed the empty container) and from `after_value`'s
`if.end378`/`NodeBlock35`/`NodeBlock41` — the next slice.  So this checkpoint's
four rows are the head's dispatch, and the payload rows they hand off to are the
stack write (`if.then20`/`if.then47.peel`) and the value path (`scalar`).

None of those instructions binds `%idxprom.lcssa`, `%tokens.8`, `%terms.8` or
`%arena.10`: the readings are carried, not re-derived, and the rows write no
memory, so the invariant is transported by `mem_congr`.
-/

/-- The state a block step delivers: the environment its run produced, the block
the edge names, and the predecessor it came from. -/
def stage2NoEventWalkNext (env : Env) (s : State) (pc : String) : State :=
  { env := env, mem := s.mem, next := s.next, pc := pc, pre := some s.pc }

/-- The same state, with the predecessor named outright: a chain's target, whose
predecessor is the last block the run left and whose memory and cursor are the
head's. -/
def stage2NoEventWalkAt (env : Env) (s : State) (pc pre : String) : State :=
  { env := env, mem := s.mem, next := s.next, pc := pc, pre := some pre }

/-- One control step at a block branch, at the false arm.  The block's run is
stated at its own `stateAt`, so the target is `env'` — the environment the run
leaves — with the head's memory and cursor. -/
theorem stage2NoEventWalkLink_condbr_false {calls : Calls} {K : Stage2NoEventWalkCarry}
    {mem : Mem} {s : State} {env' : Env} {blk : Block} {c t el : String}
    (h : Stage2NoEventWalkInv K mem s)
    (hfind : stage2NoEventBody.findBlock s.pc = some blk)
    (hcode : denoteCode calls blk.instrs (stateAt s.env s) = some (stateAt env' s))
    (hterm : blk.term = Term.condbr (Operand.reg c) t el)
    (hc : lookupName env' c = some (.int 1 (0 : BitVec 1))) :
    Stage2NoEventWalkLink calls K mem s K (stage2NoEventWalkNext env' s el) := by
  refine ⟨h, ?_, Stage2NoEventWalkInv.mem_congr h rfl⟩
  have hstep := stage2NoEventWalk_step_condbr_false (f := stage2NoEventBody) hfind
    hcode hterm hc
  simpa only [stage2NoEventWalkNext, stateAt] using hstep

/-- One control step at a block branch, at the true arm. -/
theorem stage2NoEventWalkLink_condbr_true {calls : Calls} {K : Stage2NoEventWalkCarry}
    {mem : Mem} {s : State} {env' : Env} {blk : Block} {c t el : String}
    (h : Stage2NoEventWalkInv K mem s)
    (hfind : stage2NoEventBody.findBlock s.pc = some blk)
    (hcode : denoteCode calls blk.instrs (stateAt s.env s) = some (stateAt env' s))
    (hterm : blk.term = Term.condbr (Operand.reg c) t el)
    (hc : lookupName env' c = some (.int 1 (1 : BitVec 1))) :
    Stage2NoEventWalkLink calls K mem s K (stage2NoEventWalkNext env' s t) := by
  refine ⟨h, ?_, Stage2NoEventWalkInv.mem_congr h rfl⟩
  have hstep := stage2NoEventWalk_step_condbr_true (f := stage2NoEventBody) hfind
    hcode hterm hc
  simpa only [stage2NoEventWalkNext, stateAt] using hstep

/-! ### The three blocks' denotations -/

theorem nodeBlock5_denote (calls : Calls) (env : Env) (s : State) {y : BitVec 8}
    (h3 : lookupName env "%3" = some (.int 8 y)) :
    denoteCode calls nodeBlock5Instrs (stateAt env s) =
      some (stateAt
        (("%Pivot6", .int 1 (evalICmp .slt y (BitVec.ofNat 8 91))) :: env) s) := by
  rw [nodeBlock5Instrs, stage2NoEventWalk_denote_icmp_imm (calls := calls)
    (env := env) (s := s) (d := "%Pivot6") (a := "%3") (p := .slt) (w := 8)
    (c := BitVec.ofNat 8 91) h3 (is := [])]
  simp only [denoteCode_nil]

theorem nodeBlock_denote (calls : Calls) (env : Env) (s : State) {y : BitVec 8}
    (h3 : lookupName env "%3" = some (.int 8 y)) :
    denoteCode calls nodeBlockInstrs (stateAt env s) =
      some (stateAt
        (("%Pivot", .int 1 (evalICmp .slt y (BitVec.ofNat 8 123))) :: env) s) := by
  rw [nodeBlockInstrs, stage2NoEventWalk_denote_icmp_imm (calls := calls)
    (env := env) (s := s) (d := "%Pivot") (a := "%3") (p := .slt) (w := 8)
    (c := BitVec.ofNat 8 123) h3 (is := [])]
  simp only [denoteCode_nil]

theorem leafBlock3_denote (calls : Calls) (env : Env) (s : State) {y : BitVec 8}
    (h3 : lookupName env "%3" = some (.int 8 y)) :
    denoteCode calls leafBlock3Instrs (stateAt env s) =
      some (stateAt
        (("%SwitchLeaf4", .int 1 (evalICmp .eq y (BitVec.ofNat 8 123))) :: env) s) := by
  rw [leafBlock3Instrs, stage2NoEventWalk_denote_icmp_imm (calls := calls)
    (env := env) (s := s) (d := "%SwitchLeaf4") (a := "%3") (p := .eq) (w := 8)
    (c := BitVec.ofNat 8 123) h3 (is := [])]
  simp only [denoteCode_nil]

theorem leafBlock1_denote (calls : Calls) (env : Env) (s : State) {y : BitVec 8}
    (h3 : lookupName env "%3" = some (.int 8 y)) :
    denoteCode calls leafBlock1Instrs (stateAt env s) =
      some (stateAt
        (("%SwitchLeaf2", .int 1 (evalICmp .eq y (BitVec.ofNat 8 91))) :: env) s) := by
  rw [leafBlock1Instrs, stage2NoEventWalk_denote_icmp_imm (calls := calls)
    (env := env) (s := s) (d := "%SwitchLeaf2") (a := "%3") (p := .eq) (w := 8)
    (c := BitVec.ofNat 8 91) h3 (is := [])]
  simp only [denoteCode_nil]

/-! ### The three links of a delimiter row -/

/-- `NodeBlock5` at a byte at or above 91: the false arm, to `NodeBlock`. -/
theorem link_nodeBlock5_false {calls : Calls} {K : Stage2NoEventWalkCarry}
    {mem : Mem} {s : State} {y : BitVec 8}
    (h : Stage2NoEventWalkInv K mem s) (hpc : s.pc = "NodeBlock5")
    (h3 : lookupName s.env "%3" = some (.int 8 y))
    (hy : evalICmp .slt y (BitVec.ofNat 8 91) = 0) :
    Stage2NoEventWalkLink calls K mem s K
      (stage2NoEventWalkNext (("%Pivot6", .int 1 0) :: s.env) s "NodeBlock") := by
  have hcode : denoteCode calls nodeBlock5Instrs (stateAt s.env s) =
      some (stateAt (("%Pivot6", .int 1 0) :: s.env) s) := by
    have hd := nodeBlock5_denote calls s.env s h3
    rw [hy] at hd
    exact hd
  exact stage2NoEventWalkLink_condbr_false (env' := ("%Pivot6", .int 1 0) :: s.env)
    h (by rw [hpc]; exact nodeBlock5Block_find) hcode rfl (by rw [lookupName_cons_self])

/-- `NodeBlock` at a byte below 123: the true arm, to `LeafBlock1`. -/
theorem link_nodeBlock_true {calls : Calls} {K : Stage2NoEventWalkCarry}
    {mem : Mem} {s : State} {y : BitVec 8}
    (h : Stage2NoEventWalkInv K mem s) (hpc : s.pc = "NodeBlock")
    (h3 : lookupName s.env "%3" = some (.int 8 y))
    (hy : evalICmp .slt y (BitVec.ofNat 8 123) = 1) :
    Stage2NoEventWalkLink calls K mem s K
      (stage2NoEventWalkNext (("%Pivot", .int 1 1) :: s.env) s "LeafBlock1") := by
  have hcode : denoteCode calls nodeBlockInstrs (stateAt s.env s) =
      some (stateAt (("%Pivot", .int 1 1) :: s.env) s) := by
    have hd := nodeBlock_denote calls s.env s h3
    rw [hy] at hd
    exact hd
  exact stage2NoEventWalkLink_condbr_true (env' := ("%Pivot", .int 1 1) :: s.env)
    h (by rw [hpc]; exact nodeBlockBlock_find) hcode rfl (by rw [lookupName_cons_self])

/-- `NodeBlock` at a byte at or above 123: the false arm, to `LeafBlock3`. -/
theorem link_nodeBlock_false {calls : Calls} {K : Stage2NoEventWalkCarry}
    {mem : Mem} {s : State} {y : BitVec 8}
    (h : Stage2NoEventWalkInv K mem s) (hpc : s.pc = "NodeBlock")
    (h3 : lookupName s.env "%3" = some (.int 8 y))
    (hy : evalICmp .slt y (BitVec.ofNat 8 123) = 0) :
    Stage2NoEventWalkLink calls K mem s K
      (stage2NoEventWalkNext (("%Pivot", .int 1 0) :: s.env) s "LeafBlock3") := by
  have hcode : denoteCode calls nodeBlockInstrs (stateAt s.env s) =
      some (stateAt (("%Pivot", .int 1 0) :: s.env) s) := by
    have hd := nodeBlock_denote calls s.env s h3
    rw [hy] at hd
    exact hd
  exact stage2NoEventWalkLink_condbr_false (env' := ("%Pivot", .int 1 0) :: s.env)
    h (by rw [hpc]; exact nodeBlockBlock_find) hcode rfl (by rw [lookupName_cons_self])

/-- `LeafBlock3` at 123: the brace's arm, to `if.then9`. -/
theorem link_leafBlock3_true {calls : Calls} {K : Stage2NoEventWalkCarry}
    {mem : Mem} {s : State} {y : BitVec 8}
    (h : Stage2NoEventWalkInv K mem s) (hpc : s.pc = "LeafBlock3")
    (h3 : lookupName s.env "%3" = some (.int 8 y))
    (hy : evalICmp .eq y (BitVec.ofNat 8 123) = 1) :
    Stage2NoEventWalkLink calls K mem s K
      (stage2NoEventWalkNext (("%SwitchLeaf4", .int 1 1) :: s.env) s "if.then9") := by
  have hcode : denoteCode calls leafBlock3Instrs (stateAt s.env s) =
      some (stateAt (("%SwitchLeaf4", .int 1 1) :: s.env) s) := by
    have hd := leafBlock3_denote calls s.env s h3
    rw [hy] at hd
    exact hd
  exact stage2NoEventWalkLink_condbr_true (env' := ("%SwitchLeaf4", .int 1 1) :: s.env)
    h (by rw [hpc]; exact leafBlock3Block_find) hcode rfl (by rw [lookupName_cons_self])

/-- `LeafBlock3` at a byte other than 123: the value path, `scalar`. -/
theorem link_leafBlock3_false {calls : Calls} {K : Stage2NoEventWalkCarry}
    {mem : Mem} {s : State} {y : BitVec 8}
    (h : Stage2NoEventWalkInv K mem s) (hpc : s.pc = "LeafBlock3")
    (h3 : lookupName s.env "%3" = some (.int 8 y))
    (hy : evalICmp .eq y (BitVec.ofNat 8 123) = 0) :
    Stage2NoEventWalkLink calls K mem s K
      (stage2NoEventWalkNext (("%SwitchLeaf4", .int 1 0) :: s.env) s "scalar") := by
  have hcode : denoteCode calls leafBlock3Instrs (stateAt s.env s) =
      some (stateAt (("%SwitchLeaf4", .int 1 0) :: s.env) s) := by
    have hd := leafBlock3_denote calls s.env s h3
    rw [hy] at hd
    exact hd
  exact stage2NoEventWalkLink_condbr_false (env' := ("%SwitchLeaf4", .int 1 0) :: s.env)
    h (by rw [hpc]; exact leafBlock3Block_find) hcode rfl (by rw [lookupName_cons_self])

/-- `LeafBlock1` at 91: the bracket's arm, to `if.then35.peel`. -/
theorem link_leafBlock1_true {calls : Calls} {K : Stage2NoEventWalkCarry}
    {mem : Mem} {s : State} {y : BitVec 8}
    (h : Stage2NoEventWalkInv K mem s) (hpc : s.pc = "LeafBlock1")
    (h3 : lookupName s.env "%3" = some (.int 8 y))
    (hy : evalICmp .eq y (BitVec.ofNat 8 91) = 1) :
    Stage2NoEventWalkLink calls K mem s K
      (stage2NoEventWalkNext (("%SwitchLeaf2", .int 1 1) :: s.env) s "if.then35.peel") := by
  have hcode : denoteCode calls leafBlock1Instrs (stateAt s.env s) =
      some (stateAt (("%SwitchLeaf2", .int 1 1) :: s.env) s) := by
    have hd := leafBlock1_denote calls s.env s h3
    rw [hy] at hd
    exact hd
  exact stage2NoEventWalkLink_condbr_true (env' := ("%SwitchLeaf2", .int 1 1) :: s.env)
    h (by rw [hpc]; exact leafBlock1Block_find) hcode rfl (by rw [lookupName_cons_self])

/-- `LeafBlock1` at a byte other than 91: the value path, `scalar`. -/
theorem link_leafBlock1_false {calls : Calls} {K : Stage2NoEventWalkCarry}
    {mem : Mem} {s : State} {y : BitVec 8}
    (h : Stage2NoEventWalkInv K mem s) (hpc : s.pc = "LeafBlock1")
    (h3 : lookupName s.env "%3" = some (.int 8 y))
    (hy : evalICmp .eq y (BitVec.ofNat 8 91) = 0) :
    Stage2NoEventWalkLink calls K mem s K
      (stage2NoEventWalkNext (("%SwitchLeaf2", .int 1 0) :: s.env) s "scalar") := by
  have hcode : denoteCode calls leafBlock1Instrs (stateAt s.env s) =
      some (stateAt (("%SwitchLeaf2", .int 1 0) :: s.env) s) := by
    have hd := leafBlock1_denote calls s.env s h3
    rw [hy] at hd
    exact hd
  exact stage2NoEventWalkLink_condbr_false (env' := ("%SwitchLeaf2", .int 1 0) :: s.env)
    h (by rw [hpc]; exact leafBlock1Block_find) hcode rfl (by rw [lookupName_cons_self])

/-! ### The four rows, as chains

Each row is three links from `NodeBlock5`'s dispatch to its handoff, with the
lookups at the intermediate environments read through the one binding each link
adds. -/

/-- The `%3` lookup through one binding of another name. -/
theorem lookupName_cons_other (env : Env) (d : String) (v : Value) {n : String}
    {v' : Value} (hne : d ≠ n) (h : lookupName env n = some v') :
    lookupName ((d, v) :: env) n = some v' := by
  rw [lookupName_cons_ne _ _ hne]; exact h

/-- **`{` (123)**: the brace's dispatch, to `if.then9`. -/
theorem stage2NoEventRow_brace {calls : Calls} {K : Stage2NoEventWalkCarry}
    {mem : Mem} {s : State}
    (h : Stage2NoEventWalkInv K mem s) (hpc : s.pc = "NodeBlock5")
    (h3 : lookupName s.env "%3" = some (.int 8 (BitVec.ofNat 8 123))) :
    Stage2NoEventWalkChain calls mem K s K
      (stage2NoEventWalkAt
        (("%SwitchLeaf4", .int 1 1) ::
          ("%Pivot", .int 1 0) :: ("%Pivot6", .int 1 0) :: s.env) s
        "if.then9" "LeafBlock3") := by
  have h3₁ : lookupName (("%Pivot6", .int 1 (0 : BitVec 1)) :: s.env) "%3"
      = some (.int 8 (BitVec.ofNat 8 123)) :=
    lookupName_cons_other _ _ _ (by decide) h3
  have h3₂ : lookupName (("%Pivot", .int 1 (0 : BitVec 1)) ::
      ("%Pivot6", .int 1 (0 : BitVec 1)) :: s.env) "%3"
      = some (.int 8 (BitVec.ofNat 8 123)) :=
    lookupName_cons_other _ _ _ (by decide) h3₁
  let S1 := stage2NoEventWalkNext (("%Pivot6", .int 1 0) :: s.env) s "NodeBlock"
  let S2 := stage2NoEventWalkNext (("%Pivot", .int 1 0) :: ("%Pivot6", .int 1 0) :: s.env)
    S1 "LeafBlock3"
  have L1 : Stage2NoEventWalkLink calls K mem s K S1 :=
    link_nodeBlock5_false h hpc h3 (by decide)
  have L2 : Stage2NoEventWalkLink calls K mem S1 K S2 :=
    link_nodeBlock_false L1.inv' (by simp only [S1, stage2NoEventWalkNext]) h3₁ (by decide)
  have L3 : Stage2NoEventWalkLink calls K mem S2 K
      (stage2NoEventWalkNext (("%SwitchLeaf4", .int 1 1) ::
        ("%Pivot", .int 1 0) :: ("%Pivot6", .int 1 0) :: s.env) S2 "if.then9") :=
    link_leafBlock3_true L2.inv' (by simp only [S2, stage2NoEventWalkNext]) h3₂ (by decide)
  simpa only [S1, S2, stage2NoEventWalkNext, stage2NoEventWalkAt] using
    (Stage2NoEventWalkChain.tail L1 (Stage2NoEventWalkChain.tail L2
      (Stage2NoEventWalkChain.tail L3 (Stage2NoEventWalkChain.nil L3.inv'))))

/-- **`[` (91)**: the bracket's dispatch, to `if.then35.peel`. -/
theorem stage2NoEventRow_bracket {calls : Calls} {K : Stage2NoEventWalkCarry}
    {mem : Mem} {s : State}
    (h : Stage2NoEventWalkInv K mem s) (hpc : s.pc = "NodeBlock5")
    (h3 : lookupName s.env "%3" = some (.int 8 (BitVec.ofNat 8 91))) :
    Stage2NoEventWalkChain calls mem K s K
      (stage2NoEventWalkAt
        (("%SwitchLeaf2", .int 1 1) ::
          ("%Pivot", .int 1 1) :: ("%Pivot6", .int 1 0) :: s.env) s
        "if.then35.peel" "LeafBlock1") := by
  have h3₁ : lookupName (("%Pivot6", .int 1 (0 : BitVec 1)) :: s.env) "%3"
      = some (.int 8 (BitVec.ofNat 8 91)) :=
    lookupName_cons_other _ _ _ (by decide) h3
  have h3₂ : lookupName (("%Pivot", .int 1 (1 : BitVec 1)) ::
      ("%Pivot6", .int 1 (0 : BitVec 1)) :: s.env) "%3"
      = some (.int 8 (BitVec.ofNat 8 91)) :=
    lookupName_cons_other _ _ _ (by decide) h3₁
  let S1 := stage2NoEventWalkNext (("%Pivot6", .int 1 0) :: s.env) s "NodeBlock"
  let S2 := stage2NoEventWalkNext (("%Pivot", .int 1 1) :: ("%Pivot6", .int 1 0) :: s.env)
    S1 "LeafBlock1"
  have L1 : Stage2NoEventWalkLink calls K mem s K S1 :=
    link_nodeBlock5_false h hpc h3 (by decide)
  have L2 : Stage2NoEventWalkLink calls K mem S1 K S2 :=
    link_nodeBlock_true L1.inv' (by simp only [S1, stage2NoEventWalkNext]) h3₁ (by decide)
  have L3 : Stage2NoEventWalkLink calls K mem S2 K
      (stage2NoEventWalkNext (("%SwitchLeaf2", .int 1 1) ::
        ("%Pivot", .int 1 1) :: ("%Pivot6", .int 1 0) :: s.env) S2 "if.then35.peel") :=
    link_leafBlock1_true L2.inv' (by simp only [S2, stage2NoEventWalkNext]) h3₂ (by decide)
  simpa only [S1, S2, stage2NoEventWalkNext, stage2NoEventWalkAt] using
    (Stage2NoEventWalkChain.tail L1 (Stage2NoEventWalkChain.tail L2
      (Stage2NoEventWalkChain.tail L3 (Stage2NoEventWalkChain.nil L3.inv'))))

/-- **`}` (125)**: the value path at the entry head, to `scalar`. -/
theorem stage2NoEventRow_closeBrace {calls : Calls} {K : Stage2NoEventWalkCarry}
    {mem : Mem} {s : State}
    (h : Stage2NoEventWalkInv K mem s) (hpc : s.pc = "NodeBlock5")
    (h3 : lookupName s.env "%3" = some (.int 8 (BitVec.ofNat 8 125))) :
    Stage2NoEventWalkChain calls mem K s K
      (stage2NoEventWalkAt
        (("%SwitchLeaf4", .int 1 0) ::
          ("%Pivot", .int 1 0) :: ("%Pivot6", .int 1 0) :: s.env) s
        "scalar" "LeafBlock3") := by
  have h3₁ : lookupName (("%Pivot6", .int 1 (0 : BitVec 1)) :: s.env) "%3"
      = some (.int 8 (BitVec.ofNat 8 125)) :=
    lookupName_cons_other _ _ _ (by decide) h3
  have h3₂ : lookupName (("%Pivot", .int 1 (0 : BitVec 1)) ::
      ("%Pivot6", .int 1 (0 : BitVec 1)) :: s.env) "%3"
      = some (.int 8 (BitVec.ofNat 8 125)) :=
    lookupName_cons_other _ _ _ (by decide) h3₁
  let S1 := stage2NoEventWalkNext (("%Pivot6", .int 1 0) :: s.env) s "NodeBlock"
  let S2 := stage2NoEventWalkNext (("%Pivot", .int 1 0) :: ("%Pivot6", .int 1 0) :: s.env)
    S1 "LeafBlock3"
  have L1 : Stage2NoEventWalkLink calls K mem s K S1 :=
    link_nodeBlock5_false h hpc h3 (by decide)
  have L2 : Stage2NoEventWalkLink calls K mem S1 K S2 :=
    link_nodeBlock_false L1.inv' (by simp only [S1, stage2NoEventWalkNext]) h3₁ (by decide)
  have L3 : Stage2NoEventWalkLink calls K mem S2 K
      (stage2NoEventWalkNext (("%SwitchLeaf4", .int 1 0) ::
        ("%Pivot", .int 1 0) :: ("%Pivot6", .int 1 0) :: s.env) S2 "scalar") :=
    link_leafBlock3_false L2.inv' (by simp only [S2, stage2NoEventWalkNext]) h3₂ (by decide)
  simpa only [S1, S2, stage2NoEventWalkNext, stage2NoEventWalkAt] using
    (Stage2NoEventWalkChain.tail L1 (Stage2NoEventWalkChain.tail L2
      (Stage2NoEventWalkChain.tail L3 (Stage2NoEventWalkChain.nil L3.inv'))))

/-- **`]` (93)**: the value path at the entry head, to `scalar`. -/
theorem stage2NoEventRow_closeBracket {calls : Calls} {K : Stage2NoEventWalkCarry}
    {mem : Mem} {s : State}
    (h : Stage2NoEventWalkInv K mem s) (hpc : s.pc = "NodeBlock5")
    (h3 : lookupName s.env "%3" = some (.int 8 (BitVec.ofNat 8 93))) :
    Stage2NoEventWalkChain calls mem K s K
      (stage2NoEventWalkAt
        (("%SwitchLeaf2", .int 1 0) ::
          ("%Pivot", .int 1 1) :: ("%Pivot6", .int 1 0) :: s.env) s
        "scalar" "LeafBlock1") := by
  have h3₁ : lookupName (("%Pivot6", .int 1 (0 : BitVec 1)) :: s.env) "%3"
      = some (.int 8 (BitVec.ofNat 8 93)) :=
    lookupName_cons_other _ _ _ (by decide) h3
  have h3₂ : lookupName (("%Pivot", .int 1 (1 : BitVec 1)) ::
      ("%Pivot6", .int 1 (0 : BitVec 1)) :: s.env) "%3"
      = some (.int 8 (BitVec.ofNat 8 93)) :=
    lookupName_cons_other _ _ _ (by decide) h3₁
  let S1 := stage2NoEventWalkNext (("%Pivot6", .int 1 0) :: s.env) s "NodeBlock"
  let S2 := stage2NoEventWalkNext (("%Pivot", .int 1 1) :: ("%Pivot6", .int 1 0) :: s.env)
    S1 "LeafBlock1"
  have L1 : Stage2NoEventWalkLink calls K mem s K S1 :=
    link_nodeBlock5_false h hpc h3 (by decide)
  have L2 : Stage2NoEventWalkLink calls K mem S1 K S2 :=
    link_nodeBlock_true L1.inv' (by simp only [S1, stage2NoEventWalkNext]) h3₁ (by decide)
  have L3 : Stage2NoEventWalkLink calls K mem S2 K
      (stage2NoEventWalkNext (("%SwitchLeaf2", .int 1 0) ::
        ("%Pivot", .int 1 1) :: ("%Pivot6", .int 1 0) :: s.env) S2 "scalar") :=
    link_leafBlock1_false L2.inv' (by simp only [S2, stage2NoEventWalkNext]) h3₂ (by decide)
  simpa only [S1, S2, stage2NoEventWalkNext, stage2NoEventWalkAt] using
    (Stage2NoEventWalkChain.tail L1 (Stage2NoEventWalkChain.tail L2
      (Stage2NoEventWalkChain.tail L3 (Stage2NoEventWalkChain.nil L3.inv'))))


/-! ### Axiom footprints -/

#print axioms stage2NoEventWalkLink_runFuel
#print axioms Stage2NoEventWalkChain.steps
#print axioms Stage2NoEventWalkInv.mem_congr
#print axioms Stage2NoEventWalkInv.stack_write
#print axioms stage2NoEventLoopHead_denote
#print axioms stage2NoEventRow_brace
#print axioms stage2NoEventRow_bracket
#print axioms stage2NoEventRow_closeBrace
#print axioms stage2NoEventRow_closeBracket


/-! ### The brace's payload rows: the depth guard, the stack write, the depth

The brace row above ends at `if.then9` with the leaf's `%SwitchLeaf4` binding on
the environment.  `if.then9` opens with a seven-`phi` run the edge binds, then
tests the depth's `519` guard; the guard is the edge's, and it is pinned whole
with the phis (`ifThen9_split`) while the row below is the straight-line push it
hands to.  The push branch is

| block | what it does |
|---|---|
| `if.end19` | `%tobool.not = (%sp == 0)`: false at a non-zero depth |
| `if.then20` | `%sub = %sp - 1`, `%idxprom21 = zext %sub`, `%arrayidx22 = stk[%idxprom21]`, `store i8 %frame` |
| `if.end23` | `%inc24 = %sp + 1` (the depth the push reaches), `%cmp66.not = %inc.lcssa1129 < %nep` |

The stack write is the class's memory effect and it is inside `%stk`'s region: the
address is `%stk + (%sp - 1)`, and the depth bound `%sp ≤ 519` is `if.then9`'s own
guard, so `Stage2NoEventWalkInv.stack_write` is the preservation the link consumes.
The readings do not move — `if.end74`, which counts the token, is the next block
and not in this row.

`%sp` is read at 32 bits throughout; `%nep` is the 64-bit parameter the guard
compares against, and the depth's 32-bit arithmetic (`%sub`, `%inc24`) is why the
add and the store below are stated at their own widths. -/

/-- `if.then9`'s guard: the depth against 519. -/
def ifThen9GuardInstrs : List Instr :=
  [ Instr.icmp "%cmp10" IPred.ugt 32 (Operand.reg "%sp.0.lcssa1092.wide")
      (Operand.imm (.int 32 (BitVec.ofNat 32 519))) ]

/-- `if.then9`'s seven-`phi` run, the edge's. -/
def ifThen9PhiInstrs : List Instr :=
  [ Instr.phi "%inc.lcssa1129" (Ty.int 64)
      [("LeafBlock3", (Operand.reg "%inc.peel")),
       ("if.then9.loopexit", (Operand.reg "%inc"))],
    Instr.phi "%idxprom.lcssa1108" (Ty.int 64)
      [("LeafBlock3", (Operand.reg "%idxprom.peel")),
       ("if.then9.loopexit", (Operand.reg "%idxprom.le1289"))],
    Instr.phi "%frame.0.lcssa1098" (Ty.int 8)
      [("LeafBlock3", (Operand.reg "%frame.0.ph1402")),
       ("if.then9.loopexit", (Operand.imm (.int 8 (BitVec.ofNat 8 1))))],
    Instr.phi "%sp.0.lcssa1092.wide" (Ty.int 32)
      [("LeafBlock3", (Operand.reg "%sp.0.ph1403")),
       ("if.then9.loopexit", (Operand.reg "%9"))],
    Instr.phi "%k.0.lcssa1086" (Ty.int 64)
      [("LeafBlock3", (Operand.reg "%k.0.ph1404")),
       ("if.then9.loopexit", (Operand.reg "%k.0"))],
    Instr.phi "%terms.0.lcssa1080" (Ty.int 64)
      [("LeafBlock3", (Operand.reg "%terms.0.ph1407")),
       ("if.then9.loopexit", (Operand.reg "%terms.0"))],
    Instr.phi "%tokens.0.lcssa1074" (Ty.int 64)
      [("LeafBlock3", (Operand.reg "%tokens.0.ph1408")),
       ("if.then9.loopexit", (Operand.reg "%tokens.0"))] ]

/-- `if.then9`, pinned. -/
def ifThen9Block : Block :=
  { name := "if.then9", instrs := ifThen9PhiInstrs ++ ifThen9GuardInstrs,
    term := Term.condbr (Operand.reg "%cmp10") "if.then12" "if.end19" }

theorem ifThen9Block_find :
    stage2NoEventBody.findBlock "if.then9" = some ifThen9Block := by
  decide

/-- The block's split: the edge's `phi` run, then the guard. -/
theorem ifThen9_split :
    ifThen9Block.instrs = ifThen9PhiInstrs ++ ifThen9GuardInstrs := rfl

/-- `if.end19`: the depth's zero test. -/
def ifEnd19Block : Block :=
  { name := "if.end19",
    instrs :=
      [ Instr.icmp "%tobool.not" IPred.eq 32 (Operand.reg "%sp.0.lcssa1092.wide")
          (Operand.imm (.int 32 (BitVec.ofNat 32 0))) ],
    term := Term.condbr (Operand.reg "%tobool.not") "if.end23" "if.then20" }

theorem ifEnd19Block_find :
    stage2NoEventBody.findBlock "if.end19" = some ifEnd19Block := by
  decide

/-- `if.then20`: the stack write at `%stk + (%sp - 1)`. -/
def ifThen20Block : Block :=
  { name := "if.then20",
    instrs :=
      [ Instr.binop "%sub" BinOp.add 32 (Operand.reg "%sp.0.lcssa1092.wide")
          (Operand.imm (.int 32 (BitVec.ofNat 32 4294967295))),
        Instr.zext "%idxprom21" 32 64 (Operand.reg "%sub"),
        Instr.gep "%arrayidx22" (Ty.int 8) (Operand.reg "%stk")
          (Operand.reg "%idxprom21"),
        Instr.store (Ty.int 8) (Operand.reg "%frame.0.lcssa1098")
          (Operand.reg "%arrayidx22") ],
    term := Term.br "if.end23" }

theorem ifThen20Block_find :
    stage2NoEventBody.findBlock "if.then20" = some ifThen20Block := by
  decide

/-- `if.end23`: the depth the push reaches and the next-entry guard. -/
def ifEnd23Block : Block :=
  { name := "if.end23",
    instrs :=
      [ Instr.binop "%inc24" BinOp.add 32 (Operand.reg "%sp.0.lcssa1092.wide")
          (Operand.imm (.int 32 (BitVec.ofNat 32 1))),
        Instr.icmp "%cmp66.not" IPred.ult 64 (Operand.reg "%inc.lcssa1129")
          (Operand.reg "%nep") ],
    term := Term.condbr (Operand.reg "%cmp66.not") "if.end74" "if.then68" }

theorem ifEnd23Block_find :
    stage2NoEventBody.findBlock "if.end23" = some ifEnd23Block := by
  decide

-- The four pins are the parsed body's.
#guard decide (stage2NoEventBody.findBlock "if.then9" ≠ none)
#guard decide (stage2NoEventBody.findBlock "if.end19" ≠ none)
#guard decide (stage2NoEventBody.findBlock "if.then20" ≠ none)
#guard decide (stage2NoEventBody.findBlock "if.end23" ≠ none)

/-! ### The arithmetic and the two step widths -/

/-- An integer add of an immediate at any width, as a chain step. -/
theorem stage2NoEventWalk_denote_add_imm_w (calls : Calls) (env : Env) (s : State)
    (d a : String) (w : Nat) {x c : BitVec w}
    (ha : lookupName env a = some (.int w x)) (is : List Instr) :
    denoteCode calls (.binop d .add w (.reg a) (.imm (.int w c)) :: is) (stateAt env s) =
      denoteCode calls is (stateAt ((d, .int w (x + c)) :: env) s) := by
  have hstep : evalInstr calls (stateAt env s)
      (.binop d .add w (.reg a) (.imm (.int w c))) =
      some (stateAt ((d, .int w (x + c)) :: env) s) := by
    have hr : evalBinopNat .add w x.toNat c.toNat = some ((x + c).toNat) := by
      unfold evalBinopNat
      rw [show BitVec.ofNat w x.toNat = x from by
            rw [BitVec.ofNat_toNat, BitVec.setWidth_eq],
          show BitVec.ofNat w c.toNat = c from by
            rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]]
      rfl
    rw [evalInstr_binop (r := (x + c).toNat)
      (ha := by simp only [stateAt, evalOperand, ha])
      (hb := by simp only [stateAt, evalOperand, Const.toValue]) (hr := hr)]
    simp only [stateAt, State.bind, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  rw [denoteCode_cons_of _ _ _ _ _ hstep]

/-- An integer store of a register at any width, as a chain step. -/
theorem stage2NoEventWalk_denote_store_int (calls : Calls) (env : Env) (s : State)
    (v p : String) (w : Nat) {x : BitVec w} {a : Nat}
    (hv : lookupName env v = some (.int w x))
    (hp : lookupName env p = some (.ptr a)) (is : List Instr) :
    denoteCode calls (.store (.int w) (.reg v) (.reg p) :: is) (stateAt env s) =
      denoteCode calls is
        (stateAt env (stage2NoEventStepState s
          (writeBytes s.mem a (natToBytes x.toNat ((w + 7) / 8))) s.next)) := by
  have hstep : evalInstr calls (stateAt env s) (.store (.int w) (.reg v) (.reg p)) =
      some (stateAt env (stage2NoEventStepState s
        (writeBytes s.mem a (natToBytes x.toNat ((w + 7) / 8))) s.next)) := by
    rw [evalInstr_store (vv := .int w x) (a := a)
      (s' := stateAt env (stage2NoEventStepState s
        (writeBytes s.mem a (natToBytes x.toNat ((w + 7) / 8))) s.next))
      (hv := by simp only [stateAt, evalOperand, hv])
      (hp := by simp only [stateAt, evalOperand, hp])]
    simp [storeValue, stateAt, State.bind, stage2NoEventStepState, natToBytes_length]
  rw [denoteCode_cons_of _ _ _ _ _ hstep]

/-- `%sp - 1` at 32 bits: the brace's write offset. -/
theorem stage2NoEventSub32_one {sp : BitVec 32} (h : 1 ≤ sp.toNat) :
    (sp + BitVec.ofNat 32 4294967295).toNat = sp.toNat - 1 := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat]
  have hlt : sp.toNat < 2 ^ 32 := sp.isLt
  have hmod : 4294967295 % 2 ^ 32 = 4294967295 := by decide
  rw [hmod]
  have hsum : sp.toNat + 4294967295 = (sp.toNat - 1) + 2 ^ 32 := by omega
  rw [hsum, Nat.add_mod, Nat.mod_self, Nat.add_zero, Nat.mod_mod,
    Nat.mod_eq_of_lt (by have := sp.isLt; omega)]

/-- A 64-bit word read back from its own `Nat` keeps a small value's `Nat`. -/
theorem stage2NoEventSignExtend_ofNat {x : Nat} (h : x < 2 ^ 63) :
    ((BitVec.ofNat 64 x).signExtend 64).toNat = x := by
  simp only [BitVec.signExtend_eq, BitVec.setWidth_eq, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega : x < 2 ^ 64)]

/-- The store's address is `%stk + (%sp - 1)`. -/
theorem stage2NoEventStoreAddr {sp : BitVec 32} (h : 1 ≤ sp.toNat) :
    ((BitVec.ofNat 64 ((sp + BitVec.ofNat 32 4294967295).toNat)).signExtend 64).toNat
      = sp.toNat - 1 := by
  rw [stage2NoEventSub32_one h]
  exact stage2NoEventSignExtend_ofNat (by have := sp.isLt; omega)

/-- The guard's bit is zero below `520`. -/
theorem stage2NoEventUgt519_zero {sp : BitVec 32} (h : sp.toNat ≤ 519) :
    evalICmp .ugt sp (BitVec.ofNat 32 519) = (0 : BitVec 1) := by
  unfold evalICmp
  have hoff : (BitVec.ofNat 32 519).toNat = 519 := by
    rw [BitVec.toNat_ofNat]
  have hult : BitVec.ult (BitVec.ofNat 32 519) sp = false := by
    rw [BitVec.ult]
    simp only [hoff, decide_eq_false_iff_not]
    omega
  rw [hult]
  rfl

/-- The zero test's bit is zero at a non-zero depth. -/
theorem stage2NoEventEq0_zero {sp : BitVec 32} (h : sp.toNat ≠ 0) :
    evalICmp .eq sp (BitVec.ofNat 32 0) = (0 : BitVec 1) := by
  unfold evalICmp
  have hne : ¬ (sp = BitVec.ofNat 32 0) := by
    intro he
    apply h
    rw [he, BitVec.toNat_ofNat]
  simp [hne]

/-- The guard row: the six-instruction split's second half, at the state the
edge's `phi` run delivers. -/
theorem ifThen9_guard (calls : Calls) (env : Env) (s : State) {sp : BitVec 32}
    (hsp : lookupName env "%sp.0.lcssa1092.wide" = some (.int 32 sp)) :
    denoteCode calls ifThen9GuardInstrs (stateAt env s) =
      some (stateAt
        (("%cmp10", .int 1 (evalICmp .ugt sp (BitVec.ofNat 32 519))) :: env) s) := by
  rw [ifThen9GuardInstrs, stage2NoEventWalk_denote_icmp_imm (calls := calls)
    (env := env) (s := s) (d := "%cmp10") (a := "%sp.0.lcssa1092.wide")
    (p := .ugt) (w := 32) (c := BitVec.ofNat 32 519) hsp (is := [])]
  simp only [denoteCode_nil]

/-! ### The three payload links -/

/-- The state a store step delivers: the environment and memory the block's run
produced, and the block the edge names. -/
def stage2NoEventWalkStored (env : Env) (s : State) (m : Mem) (pc : String) : State :=
  { env := env, mem := m, next := s.next, pc := pc, pre := some s.pc }

/-- `if.end19` at a non-zero depth: the false arm, to `if.then20`. -/
theorem link_ifEnd19 {calls : Calls} {K : Stage2NoEventWalkCarry} {mem : Mem}
    {s : State} {sp : BitVec 32}
    (h : Stage2NoEventWalkInv K mem s) (hpc : s.pc = "if.end19")
    (hsp : lookupName s.env "%sp.0.lcssa1092.wide" = some (.int 32 sp))
    (hpos : sp.toNat ≠ 0) :
    Stage2NoEventWalkLink calls K mem s K
      (stage2NoEventWalkNext
        (("%tobool.not", .int 1 (evalICmp .eq sp (BitVec.ofNat 32 0))) :: s.env)
        s "if.then20") := by
  have hcode : denoteCode calls ifEnd19Block.instrs (stateAt s.env s) =
      some (stateAt
        (("%tobool.not", .int 1 (evalICmp .eq sp (BitVec.ofNat 32 0))) :: s.env) s) := by
    rw [ifEnd19Block, stage2NoEventWalk_denote_icmp_imm (calls := calls)
      (env := s.env) (s := s) (d := "%tobool.not") (a := "%sp.0.lcssa1092.wide")
      (p := .eq) (w := 32) (c := BitVec.ofNat 32 0) hsp (is := [])]
    simp only [denoteCode_nil]
  refine stage2NoEventWalkLink_condbr_false (env' :=
    ("%tobool.not", .int 1 (evalICmp .eq sp (BitVec.ofNat 32 0))) :: s.env)
    h (by rw [hpc]; exact ifEnd19Block_find) hcode rfl ?_
  rw [lookupName_cons_self, stage2NoEventEq0_zero hpos]

/-- `if.then20`: the stack write, its address `%stk + (%sp - 1)` inside the
`%stk` region. -/
theorem link_ifThen20 {calls : Calls} {K : Stage2NoEventWalkCarry} {mem : Mem}
    {s : State} {sp : BitVec 32} {fr : BitVec 8}
    (h : Stage2NoEventWalkInv K mem s) (hpc : s.pc = "if.then20")
    (hsp : lookupName s.env "%sp.0.lcssa1092.wide" = some (.int 32 sp))
    (hfr : lookupName s.env "%frame.0.lcssa1098" = some (.int 8 fr))
    (hstk : lookupName s.env "%stk" = some (.ptr K.stk))
    (hpos : 1 ≤ sp.toNat) (hle : sp.toNat ≤ 519) :
    Stage2NoEventWalkLink calls K mem s K
      (stage2NoEventWalkStored
        (("%arrayidx22",
            .ptr (K.stk + ((BitVec.ofNat 64
              ((sp + BitVec.ofNat 32 4294967295).toNat)).signExtend 64).toNat)) ::
          ("%idxprom21", .int 64 (BitVec.ofNat 64
            ((sp + BitVec.ofNat 32 4294967295).toNat))) ::
          ("%sub", .int 32 (sp + BitVec.ofNat 32 4294967295)) :: s.env)
        s (writeBytes s.mem
          (K.stk + ((BitVec.ofNat 64
            ((sp + BitVec.ofNat 32 4294967295).toNat)).signExtend 64).toNat)
          (natToBytes fr.toNat 1)) "if.end23") := by
  let Z : Nat := ((sp + BitVec.ofNat 32 4294967295).toNat)
  let out : Env := ("%arrayidx22", .ptr (K.stk + ((BitVec.ofNat 64 Z).signExtend 64).toNat)) ::
    ("%idxprom21", .int 64 (BitVec.ofNat 64 Z)) ::
    ("%sub", .int 32 (sp + BitVec.ofNat 32 4294967295)) :: s.env
  have hcode : denoteCode calls ifThen20Block.instrs (stateAt s.env s) =
      some (stateAt out (stage2NoEventStepState s
        (writeBytes s.mem (K.stk + ((BitVec.ofNat 64 Z).signExtend 64).toNat)
          (natToBytes fr.toNat 1)) s.next)) := by
    rw [ifThen20Block]
    rw [stage2NoEventWalk_denote_add_imm_w (calls := calls) (env := s.env) (s := s)
      (d := "%sub") (a := "%sp.0.lcssa1092.wide") (w := 32) hsp]
    rw [denoteCode_zext (calls := calls)
      (env := ("%sub", .int 32 (sp + BitVec.ofNat 32 4294967295)) :: s.env) (s := s)
      (d := "%idxprom21") (v := "%sub") (wIn := 32) (wOut := 64)
      (x := sp + BitVec.ofNat 32 4294967295) (by simp only [lookupName_cons_self])]
    rw [denoteCode_gep8_reg (calls := calls)
      (env := ("%idxprom21", .int 64 (BitVec.ofNat 64 Z)) ::
        ("%sub", .int 32 (sp + BitVec.ofNat 32 4294967295)) :: s.env) (s := s)
      (d := "%arrayidx22") (base := "%stk") (off := "%idxprom21") (a := K.stk)
      (idx := BitVec.ofNat 64 Z)
      (by rw [lookupName_cons_ne _ _ (by decide),
        lookupName_cons_ne _ _ (by decide)]; exact hstk)
      (by simp only [lookupName_cons_self])
      (by
        have hx : Z < 2 ^ 63 := by
          have h1 := stage2NoEventSub32_one hpos
          simp only [Z]
          rw [h1]; have := sp.isLt; omega
        rw [stage2NoEventSignExtend_ofNat hx]
        exact hx)]
    rw [stage2NoEventWalk_denote_store_int (calls := calls)
      (env := ("%arrayidx22", .ptr (K.stk + ((BitVec.ofNat 64 Z).signExtend 64).toNat)) ::
        ("%idxprom21", .int 64 (BitVec.ofNat 64 Z)) ::
        ("%sub", .int 32 (sp + BitVec.ofNat 32 4294967295)) :: s.env) (s := s)
      (v := "%frame.0.lcssa1098") (p := "%arrayidx22") (w := 8) (x := fr)
      (a := K.stk + ((BitVec.ofNat 64 Z).signExtend 64).toNat)
      (by rw [lookupName_cons_ne _ _ (by decide),
        lookupName_cons_ne _ _ (by decide),
        lookupName_cons_ne _ _ (by decide)]; exact hfr)
      (by simp only [lookupName_cons_self]) (is := [])]
    simp only [Z, out, BitVec.toNat_ofNat, Nat.zero_mod, denoteCode_nil]
  refine ⟨h, ?_, ?_⟩
  · have hstep := stage2NoEventWalk_step_br (s := s) (f := stage2NoEventBody)
      (by rw [hpc]; exact ifThen20Block_find)
      (by simpa only [stateAt] using hcode) rfl
    simpa only [Z, out, stage2NoEventWalkStored, stage2NoEventStepState, stateAt]
      using hstep
  · refine Stage2NoEventWalkInv.mem_congr
      (Stage2NoEventWalkInv.stack_write h
        (a := K.stk + ((BitVec.ofNat 64 Z).signExtend 64).toNat)
        (bs := natToBytes fr.toNat 1) ?_) rfl
    intro k hk
    have hk0 : k = 0 := by simpa [natToBytes_length] using hk
    subst hk0
    have haddr : K.stk + ((BitVec.ofNat 64 Z).signExtend 64).toNat
        = K.stk + (sp.toNat - 1) := by
      rw [show ((BitVec.ofNat 64 Z).signExtend 64).toNat = Z from
        stage2NoEventSignExtend_ofNat (by
          have h1 := stage2NoEventSub32_one hpos
          simp only [Z]; rw [h1]; have := sp.isLt; omega)]
      simp only [Z]
      rw [stage2NoEventSub32_one hpos]
    rw [haddr]
    have hlt : sp.toNat - 1 < 520 := by omega
    refine ⟨(K.stk, 520), ?_, by omega, by omega⟩
    exact List.mem_append_left _
      (List.mem_cons_of_mem _ List.mem_cons_self)

/-- The same, with the predecessor named: a chain's target across a store. -/
def stage2NoEventWalkStoredAt (env : Env) (s : State) (m : Mem) (pc pre : String) : State :=
  { env := env, mem := m, next := s.next, pc := pc, pre := some pre }

/-- `if.end23` at a live entry: the true arm, to `if.end74`. -/
theorem link_ifEnd23 {calls : Calls} {K : Stage2NoEventWalkCarry} {mem : Mem}
    {s : State} {sp : BitVec 32} {inc : BitVec 64} {nep : BitVec 64}
    (h : Stage2NoEventWalkInv K mem s) (hpc : s.pc = "if.end23")
    (hsp : lookupName s.env "%sp.0.lcssa1092.wide" = some (.int 32 sp))
    (hinc : lookupName s.env "%inc.lcssa1129" = some (.int 64 inc))
    (hnep : lookupName s.env "%nep" = some (.int 64 nep))
    (hult : BitVec.ult inc nep = true) :
    Stage2NoEventWalkLink calls K mem s K
      (stage2NoEventWalkNext
        (("%cmp66.not", .int 1 1) :: ("%inc24", .int 32 (sp + BitVec.ofNat 32 1))
          :: s.env) s "if.end74") := by
  have hbit : evalICmp .ult inc nep = (1 : BitVec 1) := by
    simp only [evalICmp, hult]
    rfl
  have hcode : denoteCode calls ifEnd23Block.instrs (stateAt s.env s) =
      some (stateAt
        (("%cmp66.not", .int 1 1) ::
          ("%inc24", .int 32 (sp + BitVec.ofNat 32 1)) :: s.env) s) := by
    rw [ifEnd23Block]
    rw [stage2NoEventWalk_denote_add_imm_w (calls := calls) (env := s.env) (s := s)
      (d := "%inc24") (a := "%sp.0.lcssa1092.wide") (w := 32) hsp]
    rw [denoteCode_icmp_ult_reg (calls := calls)
      (env := ("%inc24", .int 32 (sp + BitVec.ofNat 32 1)) :: s.env) (s := s)
      (d := "%cmp66.not") (a := "%inc.lcssa1129") (b := "%nep")
      (x := inc) (y := nep)
      (by rw [lookupName_cons_ne _ _ (by decide)]; exact hinc)
      (by rw [lookupName_cons_ne _ _ (by decide)]; exact hnep) (is := [])]
    simp only [hbit, denoteCode_nil]
  refine stage2NoEventWalkLink_condbr_true (env' :=
    ("%cmp66.not", .int 1 1) :: ("%inc24", .int 32 (sp + BitVec.ofNat 32 1))
      :: s.env) h (by rw [hpc]; exact ifEnd23Block_find) hcode rfl ?_
  rw [lookupName_cons_self]

/-! ### The brace's push row

From the state the edge's `phi` run delivers at `if.end19`, the three links above
reach `if.end74` (the count's block, next checkpoint) with the stack byte written
and the depth raised. -/

/-- **The brace's push**: `if.end19` → `if.then20` → `if.end23` → `if.end74`. -/
theorem stage2NoEventRow_bracePush {calls : Calls} {K : Stage2NoEventWalkCarry}
    {mem : Mem} {s : State} {sp : BitVec 32} {fr : BitVec 8} {inc nep : BitVec 64}
    (h : Stage2NoEventWalkInv K mem s) (hpc : s.pc = "if.end19")
    (hsp : lookupName s.env "%sp.0.lcssa1092.wide" = some (.int 32 sp))
    (hfr : lookupName s.env "%frame.0.lcssa1098" = some (.int 8 fr))
    (hstk : lookupName s.env "%stk" = some (.ptr K.stk))
    (hpos : 1 ≤ sp.toNat) (hle : sp.toNat ≤ 519)
    (hinc : lookupName s.env "%inc.lcssa1129" = some (.int 64 inc))
    (hnep : lookupName s.env "%nep" = some (.int 64 nep))
    (hult : BitVec.ult inc nep = true) :
    Stage2NoEventWalkChain calls mem K s K
      (stage2NoEventWalkStoredAt
        (("%cmp66.not", .int 1 1) :: ("%inc24", .int 32 (sp + BitVec.ofNat 32 1))
          :: ("%arrayidx22",
              .ptr (K.stk + ((BitVec.ofNat 64
                ((sp + BitVec.ofNat 32 4294967295).toNat)).signExtend 64).toNat)) ::
            ("%idxprom21", .int 64 (BitVec.ofNat 64
              ((sp + BitVec.ofNat 32 4294967295).toNat))) ::
            ("%sub", .int 32 (sp + BitVec.ofNat 32 4294967295)) ::
            ("%tobool.not", .int 1 (evalICmp .eq sp (BitVec.ofNat 32 0))) :: s.env)
        s (writeBytes s.mem
          (K.stk + ((BitVec.ofNat 64
            ((sp + BitVec.ofNat 32 4294967295).toNat)).signExtend 64).toNat)
          (natToBytes fr.toNat 1)) "if.end74" "if.end23") := by
  let S1 := stage2NoEventWalkNext
    (("%tobool.not", .int 1 (evalICmp .eq sp (BitVec.ofNat 32 0))) :: s.env)
    s "if.then20"
  let S2 := stage2NoEventWalkStored
    (("%arrayidx22",
        .ptr (K.stk + ((BitVec.ofNat 64
          ((sp + BitVec.ofNat 32 4294967295).toNat)).signExtend 64).toNat)) ::
      ("%idxprom21", .int 64 (BitVec.ofNat 64
        ((sp + BitVec.ofNat 32 4294967295).toNat))) ::
      ("%sub", .int 32 (sp + BitVec.ofNat 32 4294967295)) :: S1.env)
    S1 (writeBytes S1.mem
      (K.stk + ((BitVec.ofNat 64
        ((sp + BitVec.ofNat 32 4294967295).toNat)).signExtend 64).toNat)
      (natToBytes fr.toNat 1)) "if.end23"
  have L1 : Stage2NoEventWalkLink calls K mem s K S1 :=
    link_ifEnd19 h hpc hsp (by omega)
  have hsp1 : lookupName S1.env "%sp.0.lcssa1092.wide" = some (.int 32 sp) := by
    simp only [S1, stage2NoEventWalkNext]
    exact lookupName_cons_other _ _ _ (by decide) hsp
  have hfr1 : lookupName S1.env "%frame.0.lcssa1098" = some (.int 8 fr) := by
    simp only [S1, stage2NoEventWalkNext]
    exact lookupName_cons_other _ _ _ (by decide) hfr
  have hstk1 : lookupName S1.env "%stk" = some (.ptr K.stk) := by
    simp only [S1, stage2NoEventWalkNext]
    exact lookupName_cons_other _ _ _ (by decide) hstk
  have L2 : Stage2NoEventWalkLink calls K mem S1 K S2 :=
    link_ifThen20 L1.inv' (by simp only [S1, stage2NoEventWalkNext])
      hsp1 hfr1 hstk1 hpos hle
  have hsp2 : lookupName S2.env "%sp.0.lcssa1092.wide" = some (.int 32 sp) := by
    simp only [S2, stage2NoEventWalkStored]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact hsp
  have hinc2 : lookupName S2.env "%inc.lcssa1129" = some (.int 64 inc) := by
    simp only [S2, stage2NoEventWalkStored]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact hinc
  have hnep2 : lookupName S2.env "%nep" = some (.int 64 nep) := by
    simp only [S2, stage2NoEventWalkStored]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact hnep
  have L3 : Stage2NoEventWalkLink calls K mem S2 K
      (stage2NoEventWalkNext
        (("%cmp66.not", .int 1 1) ::
          ("%inc24", .int 32 (sp + BitVec.ofNat 32 1)) :: S2.env)
        S2 "if.end74") :=
    link_ifEnd23 L2.inv' (by simp only [S2, stage2NoEventWalkStored])
      hsp2 hinc2 hnep2 hult
  simpa only [S1, S2, stage2NoEventWalkNext, stage2NoEventWalkStored,
    stage2NoEventWalkStoredAt] using
    (Stage2NoEventWalkChain.tail L1 (Stage2NoEventWalkChain.tail L2
      (Stage2NoEventWalkChain.tail L3 (Stage2NoEventWalkChain.nil L3.inv'))))




/-! ### The bracket's payload rows

The bracket's push branch is `if.then35.peel` → `if.end45.peel` → `if.then47.peel`
→ `if.end51.peel` → `if.end327.peel`.  Unlike the brace's `if.then9`, none of
these blocks has a `phi`: `%1`, `%frame.0.ph1402`, `%sp.0.ph1403`, `%inc.peel`
and `%nep` are all bound before the branch, so the whole slice is a chain of real
block steps.

| block | what it does |
|---|---|
| `if.then35.peel` | `%exitcond.peel = (%sp > 519)`; false at a depth within the stack |
| `if.end45.peel` | `%tobool46.not.peel = (%sp == 0)`; false at a non-zero depth |
| `if.then47.peel` | `%4 = %1 - 1`, `%arrayidx50.peel = stk[%4]`, `store i8 %frame` |
| `if.end51.peel` | `%cmp319.not.peel = %inc.peel < %nep` |
| `if.end327.peel` | reads the next entry's byte; `]` selects the closer `if.then334` |

The offset is 64-bit here (`%1` is the loop's 64-bit depth word), so the address is
`%stk + (%1 - 1)` and the region membership is `%1 ≤ 519`, the guard's own bound at
the 64-bit word.  The store consumes `Stage2NoEventWalkInv.stack_write` as the
brace's does; the readings are carried. -/

/-- `if.then35.peel`: the bracket's depth guard. -/
def ifThen35peelBlock : Block :=
  { name := "if.then35.peel",
    instrs :=
      [ Instr.icmp "%exitcond.peel" IPred.ugt 32 (Operand.reg "%sp.0.ph1403")
          (Operand.imm (.int 32 (BitVec.ofNat 32 519))) ],
    term := Term.condbr (Operand.reg "%exitcond.peel") "if.then38" "if.end45.peel" }

theorem ifThen35peelBlock_find :
    stage2NoEventBody.findBlock "if.then35.peel" = some ifThen35peelBlock := by
  decide

/-- `if.end45.peel`: the depth's zero test. -/
def ifEnd45peelBlock : Block :=
  { name := "if.end45.peel",
    instrs :=
      [ Instr.icmp "%tobool46.not.peel" IPred.eq 32 (Operand.reg "%sp.0.ph1403")
          (Operand.imm (.int 32 (BitVec.ofNat 32 0))) ],
    term := Term.condbr (Operand.reg "%tobool46.not.peel") "if.end51.peel" "if.then47.peel" }

theorem ifEnd45peelBlock_find :
    stage2NoEventBody.findBlock "if.end45.peel" = some ifEnd45peelBlock := by
  decide

/-- `if.then47.peel`: the bracket's stack write. -/
def ifThen47peelBlock : Block :=
  { name := "if.then47.peel",
    instrs :=
      [ Instr.binop "%4" BinOp.add 64 (Operand.reg "%1")
          (Operand.imm (.int 64 (BitVec.ofNat 64 18446744073709551615))),
        Instr.gep "%arrayidx50.peel" (Ty.int 8) (Operand.reg "%stk")
          (Operand.reg "%4"),
        Instr.store (Ty.int 8) (Operand.reg "%frame.0.ph1402")
          (Operand.reg "%arrayidx50.peel") ],
    term := Term.br "if.end51.peel" }

theorem ifThen47peelBlock_find :
    stage2NoEventBody.findBlock "if.then47.peel" = some ifThen47peelBlock := by
  decide

/-- `if.end51.peel`: the next-entry guard. -/
def ifEnd51peelBlock : Block :=
  { name := "if.end51.peel",
    instrs :=
      [ Instr.icmp "%cmp319.not.peel" IPred.ult 64 (Operand.reg "%inc.peel")
          (Operand.reg "%nep") ],
    term := Term.condbr (Operand.reg "%cmp319.not.peel") "if.end327.peel" "if.then321" }

theorem ifEnd51peelBlock_find :
    stage2NoEventBody.findBlock "if.end51.peel" = some ifEnd51peelBlock := by
  decide

-- The five pins are the parsed body's.
#guard decide (stage2NoEventBody.findBlock "if.then35.peel" ≠ none)
#guard decide (stage2NoEventBody.findBlock "if.end45.peel" ≠ none)
#guard decide (stage2NoEventBody.findBlock "if.then47.peel" ≠ none)
#guard decide (stage2NoEventBody.findBlock "if.end51.peel" ≠ none)

/-- `%1 - 1` at 64 bits: the bracket's write offset. -/
theorem stage2NoEventSub64_one {a : BitVec 64} (h : 1 ≤ a.toNat) :
    (a + BitVec.ofNat 64 18446744073709551615).toNat = a.toNat - 1 := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat]
  have hlt : a.toNat < 2 ^ 64 := a.isLt
  have hmod : 18446744073709551615 % 2 ^ 64 = 18446744073709551615 := by decide
  rw [hmod]
  have hsum : a.toNat + 18446744073709551615 = (a.toNat - 1) + 2 ^ 64 := by omega
  rw [hsum, Nat.add_mod, Nat.mod_self, Nat.add_zero, Nat.mod_mod,
    Nat.mod_eq_of_lt (by omega)]

/-- A 64-bit word's sign extension to its own width is itself. -/
theorem stage2NoEventSignExtend_self {z : BitVec 64} :
    (BitVec.signExtend 64 z).toNat = z.toNat := by
  simp only [BitVec.signExtend_eq, BitVec.setWidth_eq]

/-- The bracket store's address is `%stk + (%1 - 1)`. -/
theorem stage2NoEventStoreAddr64 {a : BitVec 64} (h : 1 ≤ a.toNat) :
    (BitVec.signExtend 64
        (a + BitVec.ofNat 64 18446744073709551615)).toNat = a.toNat - 1 := by
  rw [stage2NoEventSignExtend_self, stage2NoEventSub64_one h]

/-- `if.then35.peel` at a depth within the stack: the false arm, to `if.end45.peel`. -/
theorem link_ifThen35peel {calls : Calls} {K : Stage2NoEventWalkCarry} {mem : Mem}
    {s : State} {sp : BitVec 32}
    (h : Stage2NoEventWalkInv K mem s) (hpc : s.pc = "if.then35.peel")
    (hsp : lookupName s.env "%sp.0.ph1403" = some (.int 32 sp))
    (hle : sp.toNat ≤ 519) :
    Stage2NoEventWalkLink calls K mem s K
      (stage2NoEventWalkNext
        (("%exitcond.peel", .int 1 0) :: s.env) s "if.end45.peel") := by
  have hbit : evalICmp .ugt sp (BitVec.ofNat 32 519) = (0 : BitVec 1) :=
    stage2NoEventUgt519_zero hle
  have hcode : denoteCode calls ifThen35peelBlock.instrs (stateAt s.env s) =
      some (stateAt (("%exitcond.peel", .int 1 0) :: s.env) s) := by
    rw [ifThen35peelBlock, stage2NoEventWalk_denote_icmp_imm (calls := calls)
      (env := s.env) (s := s) (d := "%exitcond.peel") (a := "%sp.0.ph1403")
      (p := .ugt) (w := 32) (c := BitVec.ofNat 32 519) hsp (is := [])]
    simp only [hbit, denoteCode_nil]
  exact stage2NoEventWalkLink_condbr_false (env' := ("%exitcond.peel", .int 1 0) :: s.env)
    h (by rw [hpc]; exact ifThen35peelBlock_find) hcode rfl
    (by rw [lookupName_cons_self])

/-- `if.end45.peel` at a non-zero depth: the false arm, to `if.then47.peel`. -/
theorem link_ifEnd45peel {calls : Calls} {K : Stage2NoEventWalkCarry} {mem : Mem}
    {s : State} {sp : BitVec 32}
    (h : Stage2NoEventWalkInv K mem s) (hpc : s.pc = "if.end45.peel")
    (hsp : lookupName s.env "%sp.0.ph1403" = some (.int 32 sp))
    (hpos : sp.toNat ≠ 0) :
    Stage2NoEventWalkLink calls K mem s K
      (stage2NoEventWalkNext
        (("%tobool46.not.peel", .int 1 0) :: s.env) s "if.then47.peel") := by
  have hbit : evalICmp .eq sp (BitVec.ofNat 32 0) = (0 : BitVec 1) :=
    stage2NoEventEq0_zero hpos
  have hcode : denoteCode calls ifEnd45peelBlock.instrs (stateAt s.env s) =
      some (stateAt (("%tobool46.not.peel", .int 1 0) :: s.env) s) := by
    rw [ifEnd45peelBlock, stage2NoEventWalk_denote_icmp_imm (calls := calls)
      (env := s.env) (s := s) (d := "%tobool46.not.peel") (a := "%sp.0.ph1403")
      (p := .eq) (w := 32) (c := BitVec.ofNat 32 0) hsp (is := [])]
    simp only [hbit, denoteCode_nil]
  exact stage2NoEventWalkLink_condbr_false
    (env' := ("%tobool46.not.peel", .int 1 0) :: s.env)
    h (by rw [hpc]; exact ifEnd45peelBlock_find) hcode rfl
    (by rw [lookupName_cons_self])

/-- `if.then47.peel`: the bracket's stack write at `%stk + (%1 - 1)`. -/
theorem link_ifThen47peel {calls : Calls} {K : Stage2NoEventWalkCarry} {mem : Mem}
    {s : State} {v1 : BitVec 64} {fr : BitVec 8}
    (h : Stage2NoEventWalkInv K mem s) (hpc : s.pc = "if.then47.peel")
    (h1 : lookupName s.env "%1" = some (.int 64 v1))
    (hfr : lookupName s.env "%frame.0.ph1402" = some (.int 8 fr))
    (hstk : lookupName s.env "%stk" = some (.ptr K.stk))
    (hpos : 1 ≤ v1.toNat) (hle : v1.toNat ≤ 519) :
    Stage2NoEventWalkLink calls K mem s K
      (stage2NoEventWalkStored
        (("%arrayidx50.peel",
            .ptr (K.stk + (BitVec.signExtend 64
              (v1 + BitVec.ofNat 64 18446744073709551615)).toNat)) ::
          ("%4", .int 64 (v1 + BitVec.ofNat 64 18446744073709551615)) :: s.env)
        s (writeBytes s.mem
          (K.stk + (BitVec.signExtend 64
            (v1 + BitVec.ofNat 64 18446744073709551615)).toNat)
          (natToBytes fr.toNat 1)) "if.end51.peel") := by
  have hcode : denoteCode calls ifThen47peelBlock.instrs (stateAt s.env s) =
      some (stateAt
        (("%arrayidx50.peel",
            .ptr (K.stk + (BitVec.signExtend 64
              (v1 + BitVec.ofNat 64 18446744073709551615)).toNat)) ::
          ("%4", .int 64 (v1 + BitVec.ofNat 64 18446744073709551615)) :: s.env)
        (stage2NoEventStepState s
          (writeBytes s.mem
            (K.stk + (BitVec.signExtend 64
              (v1 + BitVec.ofNat 64 18446744073709551615)).toNat)
            (natToBytes fr.toNat 1)) s.next)) := by
    rw [ifThen47peelBlock]
    rw [stage2NoEventWalk_denote_add_imm_w (calls := calls) (env := s.env) (s := s)
      (d := "%4") (a := "%1") (w := 64) h1]
    rw [denoteCode_gep8_reg (calls := calls)
      (env := ("%4", .int 64 (v1 + BitVec.ofNat 64 18446744073709551615)) :: s.env)
      (s := s) (d := "%arrayidx50.peel") (base := "%stk") (off := "%4")
      (a := K.stk) (idx := v1 + BitVec.ofNat 64 18446744073709551615)
      (by rw [lookupName_cons_ne _ _ (by decide)]; exact hstk)
      (by simp only [lookupName_cons_self])
      (by
        have hx : (v1 + BitVec.ofNat 64 18446744073709551615).toNat < 2 ^ 63 := by
          rw [stage2NoEventSub64_one hpos]; have := v1.isLt; omega
        rw [stage2NoEventSignExtend_self]
        exact hx)]
    rw [stage2NoEventWalk_denote_store_int (calls := calls)
      (env := ("%arrayidx50.peel",
          .ptr (K.stk + (BitVec.signExtend 64
            (v1 + BitVec.ofNat 64 18446744073709551615)).toNat)) ::
        ("%4", .int 64 (v1 + BitVec.ofNat 64 18446744073709551615)) :: s.env) (s := s)
      (v := "%frame.0.ph1402") (p := "%arrayidx50.peel") (w := 8) (x := fr)
      (a := K.stk + (BitVec.signExtend 64
        (v1 + BitVec.ofNat 64 18446744073709551615)).toNat)
      (by rw [lookupName_cons_ne _ _ (by decide),
        lookupName_cons_ne _ _ (by decide)]; exact hfr)
      (by simp only [lookupName_cons_self]) (is := [])]
    simp only [denoteCode_nil]
  refine ⟨h, ?_, ?_⟩
  · have hstep := stage2NoEventWalk_step_br (s := s) (f := stage2NoEventBody)
      (by rw [hpc]; exact ifThen47peelBlock_find)
      (by simpa only [stateAt] using hcode) rfl
    simpa only [stage2NoEventWalkStored, stage2NoEventStepState, stateAt]
      using hstep
  · refine Stage2NoEventWalkInv.mem_congr
      (Stage2NoEventWalkInv.stack_write h
        (a := K.stk + (BitVec.signExtend 64
          (v1 + BitVec.ofNat 64 18446744073709551615)).toNat)
        (bs := natToBytes fr.toNat 1) ?_) rfl
    intro k hk
    have hk0 : k = 0 := by simpa [natToBytes_length] using hk
    subst hk0
    have haddr : K.stk + (BitVec.signExtend 64
        (v1 + BitVec.ofNat 64 18446744073709551615)).toNat
        = K.stk + (v1.toNat - 1) := by
      rw [stage2NoEventStoreAddr64 hpos]
    rw [haddr]
    have hlt : v1.toNat - 1 < 520 := by omega
    refine ⟨(K.stk, 520), ?_, by omega, by omega⟩
    exact List.mem_append_left _
      (List.mem_cons_of_mem _ List.mem_cons_self)

/-- `if.end51.peel` at a live entry: the true arm, to `if.end327.peel`. -/
theorem link_ifEnd51peel {calls : Calls} {K : Stage2NoEventWalkCarry} {mem : Mem}
    {s : State} {inc : BitVec 64} {nep : BitVec 64}
    (h : Stage2NoEventWalkInv K mem s) (hpc : s.pc = "if.end51.peel")
    (hinc : lookupName s.env "%inc.peel" = some (.int 64 inc))
    (hnep : lookupName s.env "%nep" = some (.int 64 nep))
    (hult : BitVec.ult inc nep = true) :
    Stage2NoEventWalkLink calls K mem s K
      (stage2NoEventWalkNext
        (("%cmp319.not.peel", .int 1 1) :: s.env) s "if.end327.peel") := by
  have hbit : evalICmp .ult inc nep = (1 : BitVec 1) := by
    simp only [evalICmp, hult]
    rfl
  have hcode : denoteCode calls ifEnd51peelBlock.instrs (stateAt s.env s) =
      some (stateAt (("%cmp319.not.peel", .int 1 1) :: s.env) s) := by
    rw [ifEnd51peelBlock, denoteCode_icmp_ult_reg (calls := calls)
      (env := s.env) (s := s) (d := "%cmp319.not.peel") (a := "%inc.peel")
      (b := "%nep") (x := inc) (y := nep) hinc hnep (is := [])]
    simp only [hbit, denoteCode_nil]
  exact stage2NoEventWalkLink_condbr_true (env' := ("%cmp319.not.peel", .int 1 1) :: s.env)
    h (by rw [hpc]; exact ifEnd51peelBlock_find) hcode rfl
    (by rw [lookupName_cons_self])

/-- **The bracket's push**: `if.then35.peel` → `if.end45.peel` → `if.then47.peel`
→ `if.end51.peel`, ending at `if.end327.peel`'s entry (the next dispatch block,
whose `]` link is `link_ifEnd327peel`). -/
theorem stage2NoEventRow_bracketPush {calls : Calls} {K : Stage2NoEventWalkCarry}
    {mem : Mem} {s : State} {sp : BitVec 32} {v1 inc nep : BitVec 64}
    {fr : BitVec 8}
    (h : Stage2NoEventWalkInv K mem s) (hpc : s.pc = "if.then35.peel")
    (hsp : lookupName s.env "%sp.0.ph1403" = some (.int 32 sp))
    (h1 : lookupName s.env "%1" = some (.int 64 v1))
    (hfr : lookupName s.env "%frame.0.ph1402" = some (.int 8 fr))
    (hstk : lookupName s.env "%stk" = some (.ptr K.stk))
    (hinc : lookupName s.env "%inc.peel" = some (.int 64 inc))
    (hnep : lookupName s.env "%nep" = some (.int 64 nep))
    (hle : sp.toNat ≤ 519) (hposS : sp.toNat ≠ 0)
    (hpos : 1 ≤ v1.toNat) (hle1 : v1.toNat ≤ 519)
    (hult : BitVec.ult inc nep = true) :
    Stage2NoEventWalkChain calls mem K s K
      (stage2NoEventWalkStoredAt
        (("%cmp319.not.peel", .int 1 1) ::
          ("%arrayidx50.peel",
            .ptr (K.stk + (BitVec.signExtend 64
              (v1 + BitVec.ofNat 64 18446744073709551615)).toNat)) ::
          ("%4", .int 64 (v1 + BitVec.ofNat 64 18446744073709551615)) ::
          ("%tobool46.not.peel", .int 1 0) ::
          ("%exitcond.peel", .int 1 0) :: s.env)
        s (writeBytes s.mem
          (K.stk + (BitVec.signExtend 64
            (v1 + BitVec.ofNat 64 18446744073709551615)).toNat)
          (natToBytes fr.toNat 1)) "if.end327.peel" "if.end51.peel") := by
  let S1 := stage2NoEventWalkNext (("%exitcond.peel", .int 1 0) :: s.env)
    s "if.end45.peel"
  let S2 := stage2NoEventWalkNext (("%tobool46.not.peel", .int 1 0) :: S1.env)
    S1 "if.then47.peel"
  let S3 := stage2NoEventWalkStored
    (("%arrayidx50.peel",
        .ptr (K.stk + (BitVec.signExtend 64
          (v1 + BitVec.ofNat 64 18446744073709551615)).toNat)) ::
      ("%4", .int 64 (v1 + BitVec.ofNat 64 18446744073709551615)) :: S2.env)
    S2 (writeBytes S2.mem
      (K.stk + (BitVec.signExtend 64
        (v1 + BitVec.ofNat 64 18446744073709551615)).toNat)
      (natToBytes fr.toNat 1)) "if.end51.peel"
  let S4 := stage2NoEventWalkNext (("%cmp319.not.peel", .int 1 1) :: S3.env)
    S3 "if.end327.peel"
  have L1 : Stage2NoEventWalkLink calls K mem s K S1 :=
    link_ifThen35peel h hpc hsp hle
  have hsp1 : lookupName S1.env "%sp.0.ph1403" = some (.int 32 sp) := by
    simp only [S1, stage2NoEventWalkNext]
    exact lookupName_cons_other _ _ _ (by decide) hsp
  have L2 : Stage2NoEventWalkLink calls K mem S1 K S2 :=
    link_ifEnd45peel L1.inv' (by simp only [S1, stage2NoEventWalkNext]) hsp1 hposS
  have h1₂ : lookupName S2.env "%1" = some (.int 64 v1) := by
    simp only [S2, S1, stage2NoEventWalkNext]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact h1
  have hfr₂ : lookupName S2.env "%frame.0.ph1402" = some (.int 8 fr) := by
    simp only [S2, S1, stage2NoEventWalkNext]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact hfr
  have hstk₂ : lookupName S2.env "%stk" = some (.ptr K.stk) := by
    simp only [S2, S1, stage2NoEventWalkNext]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact hstk
  have L3 : Stage2NoEventWalkLink calls K mem S2 K S3 :=
    link_ifThen47peel L2.inv' (by simp only [S2, S1, stage2NoEventWalkNext])
      h1₂ hfr₂ hstk₂ hpos hle1
  have hinc3 : lookupName S3.env "%inc.peel" = some (.int 64 inc) := by
    simp only [S3, stage2NoEventWalkStored]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact hinc
  have hnep3 : lookupName S3.env "%nep" = some (.int 64 nep) := by
    simp only [S3, stage2NoEventWalkStored]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact hnep
  have L4 : Stage2NoEventWalkLink calls K mem S3 K S4 :=
    link_ifEnd51peel L3.inv' (by simp only [S3, stage2NoEventWalkStored])
      hinc3 hnep3 hult
  simpa only [S1, S2, S3, S4, stage2NoEventWalkNext, stage2NoEventWalkStored,
    stage2NoEventWalkStoredAt] using
    (Stage2NoEventWalkChain.tail L1 (Stage2NoEventWalkChain.tail L2
      (Stage2NoEventWalkChain.tail L3 (Stage2NoEventWalkChain.tail L4
        (Stage2NoEventWalkChain.nil L4.inv')))))

/-! ### Payload footprints -/

#print axioms ifThen9_guard
#print axioms link_ifEnd19
#print axioms link_ifThen20
#print axioms link_ifEnd23
#print axioms stage2NoEventRow_bracePush
#print axioms link_ifThen35peel
#print axioms link_ifEnd45peel
#print axioms link_ifThen47peel
#print axioms link_ifEnd51peel
#print axioms stage2NoEventRow_bracketPush

end LeanLLVM.Refinement
