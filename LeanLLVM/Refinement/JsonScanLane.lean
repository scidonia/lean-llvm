/-
The JSON window scanner's lane machinery, at the LLVM level.

`LeanLLVM/Refinement/JsonScanIR.lean` holds the fixture pin and the model-side prefix
theory — `maskPref`, `firstStop`, `carriedAt` and their identifications with
`maskOfList`, `stopOf` and `carryAt`.  This module is the instruction-level half.

**The statement this feeds**, written here first so the facts below serve it and
not the other way round.  For a readable window and a well-formed carry:

    theorem scanWindowLLVM_refines (bs : List UInt8) (st : BodyState) (mem : Mem)
        (pIn pOut pState base valid : Nat) (hvalid : valid ≤ 32)
        (hlen : bs.length = valid) (hread : readBytes mem pIn valid = some bs)
        (hslot : slotAt mem pState = some st) (hst : st.WellFormed)
        (hdisj : scanSlotDisjoint pIn pOut pState valid) (hband : … base disjoint …) :
        ∃ mem', runFuel noCalls 10000 scanWindowBody
            { (initState scanWindowBody [.ptr pIn, .ptr pOut, .ptr pState,
                                        .int 32 (BitVec.ofNat 32 valid)]) with
              mem := mem, next := base } =
            some (.ret (some (.int 32 (encodeStatus (Status.ok (stopOf bs st))))) mem') ∧
          readWord mem' pOut = some (maskOfList bs) ∧
          slotAt mem' pState = some (carryAt bs st (stopLaneOrLength bs st)) ∧
          AgreesOutsideMem mem' (writeMask mem pOut (maskOfList bs))
              (fun a => Band base (base + 28) a ∨
                (pState ≤ a ∧ a < pState + 16)) ∧
          readBytes mem' pIn valid = some bs

That statement is `JsonScanIR.scanWindowStatement`, with the band hypothesis the
prose leaves as `(hband : … base disjoint …)` supplied as
`JsonScanIR.scanBandDisjoint` and the frame tied to `JsonScanIR.scanBandBytes`.
The frame also stops at the caller's state region: the body stores the rule's own
words there, so a lane that completes a UTF-8 requirement leaves the bounds it
last used where `encodeState` writes zero, and the state region's caller-visible
content is the readback clause.  `JsonScanIR.completionLeavesBounds` measures that
at a caller whose slot holds the encoding, and
`JsonScanIR.scanWindowStatementPinningSlotBytes_false` refutes the statement that
pins the slot's bytes inside the frame.  It is a proposition and not a theorem.
Three things a proof meets before it can start are settled: the band hypothesis is
load-bearing (`JsonScanIR.bandOverlap_clobbers_window`, with
`bandClear_preserves_window` as its control), the frame cannot pin the slot's bytes
(`completionLeavesBounds`), and the stop word's select chain reported `control`
where the model refuses with `badUtf8` on a byte outside a pending requirement
(`JsonScanIR.badContinuation_reason_differs`, the record of that body, with
`badLead_reason_agrees` as its control).  The body now chooses the `badUtf8` word
on `%ubad ||| %lbad`, and `JsonScanIR.probeWindows_agree` states the agreement
that produces over seven windows, the 32-byte one whose bad continuation sits at
lane 31 included.  The name above is therefore still free for the theorem to come,
and nothing here claims it.

The body is scalar: one lane per iteration, the model's predicates as straight
line IR, the structural mask accumulated into one `i32` by `shl`/`or`, the
counter, the carry and the stop word in memory.

The lane's structural bit is not a comparison chain: the body reads it out of a
two-word table (`structLo`, `structHi` in `JsonScanBody`) with a
mask/shift/test.  `structBit_correct` below is that table's bridge to the model:
`structBit` runs the body's own nine table instructions through the semantics'
`denoteCode`, and the theorem says its answer is `IsStructOrSpaceB` for every
byte.  Nothing inside the kernel had connected the table's arithmetic to the
predicate it stands for, and a check made outside the kernel cannot discharge a
hypothesis inside a theorem; the agreement is now proved, over the same finite
domain, against the chain the body runs.  `maskStep` — the mask accumulator's one
step, the emitted `or` of the lane's bit against the model's own `maskOfList`
fold — takes `structBit`'s answer as its input, so the bit it accumulates is the
table's, and the equality with `IsStructOrSpaceB` is supplied by
`structBit_correct` rather than assumed.

**The lane's opening, as a chain.**  `structBit_correct` and `maskStep` are
facts about values; a lane proof additionally needs the effect of the emitted
instruction *list* on the machine state.  The `body` block is 143 instructions
on the full-window path — `laneHead` (5), `maskedSkipBits` (18) and `ruleInstrs`
(120) — and 128 on the scalar one, where `plainSkipBits` (3) stands in for the
mask reads.  The two pieces that precede the rule are here:

* `laneHead_step` runs the opening — the counter read back, its low word, the
  lane's bit, the byte's address and the byte — into `laneHeadOut env aIn ki b`;
* `maskedSkipBits_step` runs the three mask words' own predicates into
  `maskedSkipBitsOut`, and `plainSkipBits_step` runs the scalar path's three byte
  predicates into `plainSkipBitsOut`, both from `laneHeadOut`;
* `laneHeadMaskedSkipBits_step` and `laneHeadPlainSkipBits_step` are those two
  chains composed, which is the state `ruleInstrs` starts from on each path.

Each is a `denoteCode` equation against an environment *builder* whose cells are
the lane's own data flow (`vK32`, `vOne`, `vM1`, …), so a successor step reads
its inputs off the builder instead of a hypothesis list.  `denoteCode_append_scan`
is the composition the last two use.

**The rule's chain.**  `ruleInstrs`'s 120 instructions are derived here, from the
environment the skip bits leave: eight pieces, one per group of the model's
vocabulary, each a `denoteCode` equation at the lane's own environment, composed
into `ruleInstrs_step`.  The pieces name their results as value cells — the
structural bit's table, the mask accumulator, the conditions, the skip chain, the
status word, the carry's four words and the counter — and the shapes `BlockEval`
does not carry are steps of their own: `icmp` at two registers, `xor`/`sub`/`add`
and the `or` of a literal at any width, `select` at any width on a computed
condition with each pair of operand shapes, `getelementptr` at a literal index,
and `store i32`.  `laneHeadMaskedSkipBits_rule_step` and
`laneHeadPlainSkipBits_rule_step` then compose the 23 and 8 instructions before
the rule with those 120.

**What is not here.**  The arithmetic bridge (`decodeState` of the four words the
rule leaves is `bodyStep` of the four it read, under the `act` gate; the mask
half is `maskStep`), the `laneStep` lemma the loop induction consumes, the
induction over `valid ≤ 32`, and the statement's footprint clause.
`scanWindowLLVM_refines` is still the statement `scanWindowStatement` and nothing
here claims it; the chain's own last step stores the stop word, which is the word
the model names, and the bridge is what identifies the four words the rule leaves
with the carry the model steps.
-/
import LeanLLVM.Refinement.JsonScanIR
import LeanLLVM.Refinement.BlockEval

namespace LeanLLVM.Refinement.JsonScanLane

open LeanLLVM
open LeanLLVM.JSON
open LeanLLVM.Refinement.JsonScanModel
open LeanLLVM.Refinement.JsonScanIR (maskPref maskPref_succ maskPref_eq_maskOfList)
open LeanLLVM.Refinement.JsonScanBody (scanWindowBody scanWindowBaselineBody ruleInstrs
  laneHead maskedSkipBits plainSkipBits structLo structHi)
open LeanLLVM.Refinement.BlockEval (stateAt cells)

/-! ### The structural bit table

The first nine instructions of the lane body's `ruleInstrs` decide whether the byte
is structural or whitespace, with no comparison chain: the byte picks a word
from `{structLo, structHi, 0}` by its range, and bit `b % 64` of that word is
the answer.  `structBit` is that answer read from the semantics, and
`structBit_correct` is the bridge the mask accumulator consumes. -/

/-- The nine instructions of `ruleInstrs` that decide the structural bit: the
`zext`, the two range tests, the two `select`s, the `lshr`, the `and` and the
`icmp`.  Taken from the body's own list, so the theorem below is about the
emitted table and not a transcription of it. -/
def structBitCode : List Instr := ruleInstrs.take 9

/-- The state the table is evaluated in: `%b` bound to the lane's byte as the
lane body's `load` binds it, empty memory, and no other register.  The chain
reads only the byte it is given and writes no memory, so nothing else is
needed. -/
def structBitStart (b : UInt8) : State :=
  { env := [("%b", .int 8 (BitVec.ofNat 8 b.toNat))], mem := [], next := 0, pc := "body",
    pre := none }

/-- `%stb` after the body's table instructions have run: the one-bit value the
lane body's `select` reads.  `none` would be a stuck chain, which
`structBit_correct` shows never happens. -/
def structBitReg (b : UInt8) : Option Value :=
  (denoteCode noCalls structBitCode (structBitStart b)).bind fun s => lookupName s.env "%stb"

/-- The body's structural test: the table chain leaves `%stb` holding one. -/
def structBit (b : UInt8) : Bool := structBitReg b = some (.int 1 1)

set_option maxRecDepth 20000 in
/-- **The table decides `IsStructOrSpaceB`.**  The body hands `structBit` a byte
and reads back the test bit; this says the bit is the model's predicate on that
byte, for every one of the 256 bytes.  The proof reduces the chain itself in the
kernel over the finite domain — the same instructions the lane body runs, not a
re-description of the arithmetic — so a change to `structLo`, `structHi` or the
chain's shape fails here, at the theorem the accumulator consumes. -/
theorem structBit_correct (b : UInt8) : structBit b = IsStructOrSpaceB b := by
  have hall :
      (List.range 256).all
        (fun n => decide (structBit (UInt8.ofNat n) = IsStructOrSpaceB (UInt8.ofNat n))) =
        true := by
    decide
  have hmem : b.toNat ∈ List.range 256 :=
    List.mem_range.mpr (by have := b.toNat_lt; omega)
  rw [← UInt8.ofNat_toNat (x := b)]
  exact of_decide_eq_true ((List.all_eq_true.mp hall) b.toNat hmem)

/-- **The mask accumulator's step.**  One lane's `shl`/`or` leaves the model's
own prefix fold: with the accumulator holding `maskPref bs k` and the lane's
structural bit read out of the two-word table by the body's own instructions,
the emitted `or` of the lane's bit is `maskPref bs (k + 1)`.  This is the clause
"accumulated by `shl`/`or`" made checkable: the accumulator is one `i32` `or`
chain over a predicate that is a table, which is what `maskOfList`'s fold is.

The bit is `structBit b`, the table chain's answer, so the `if` is the body's
`select` on `%stb`; `structBit_correct` — not the caller — supplies its equality
with `IsStructOrSpaceB`.

`maskPref_eq_maskOfList` at the window's end then turns the accumulator into the
word the unit stores at `%out`. -/
theorem maskStep (bs : List UInt8) (m : BitVec 32) (k : Nat) (b : UInt8)
    (hk : k < 32) (hb : bs[k]? = some b) (hm : m = maskPref bs k) :
    (if structBit b = true then m ||| ((1 : BitVec 32) <<< k) else m) =
      maskPref bs (k + 1) := by
  subst hm
  rw [maskPref_succ, structBit_correct b]
  simp only [hb]

/-! ### The lane's data flow

The registers the opening and the skip bits write, as functions of what they
read: the counter's low word, the lane's bit, the byte's address, and each mask
word's own bit with the byte's predicate or-ed in.  A step's conclusion names
them, so the next step's input is the builder's cell rather than a hypothesis.

The three groups of the skip bits are the same shape — a mask word's bit `k`,
the byte's own predicate as the disjunct that decides a short window, and their
`or` — so `vM1`, `vM2` and `vM3` are shared and only the byte predicate differs. -/

/-- The byte's value in the lane's `%b`: the load's `.int 8` reading of one byte,
`structBitStart`'s `%b` too. -/
def vByte (b : UInt8) : BitVec 8 := BitVec.ofNat 8 b.toNat

/-- `%k32`, the counter's low word: `%ki` truncated to thirty-two bits. -/
def vK32 (ki : BitVec 64) : BitVec 32 := BitVec.ofNat 32 (ki.toNat % 2 ^ 32)

/-- `%one`, the lane's bit in the mask accumulator's word. -/
def vOne (ki : BitVec 64) : BitVec 32 := (1 : BitVec 32) <<< (vK32 ki).toNat

/-- `%bp`, the byte's address: the window plus the counter. -/
def vBp (aIn : Nat) (ki : BitVec 64) : Nat := aIn + (ki.signExtend 64).toNat

/-- `%q1` (and `%s1`, `%c1`): bit `k` of a mask word, brought down to the lane. -/
def vM1 (m : BitVec 32) (ki : BitVec 64) : BitVec 32 := m >>> (vK32 ki).toNat

/-- `%q2` (and `%s2`, `%c2`): the one bit the lane's word holds, isolated. -/
def vM2 (m : BitVec 32) (ki : BitVec 64) : BitVec 32 := vM1 m ki &&& 1

/-- `%q3` (and `%s3`, `%c3`): the isolated bit as a condition. -/
def vM3 (m : BitVec 32) (ki : BitVec 64) : BitVec 1 := evalICmp .ne (vM2 m ki) 0

/-- `%q4`: the byte is a quote. -/
def vQ4 (b : UInt8) : BitVec 1 := evalICmp .eq (vByte b) 34

/-- `%qb`: the lane's quote bit — the mask word's, with the byte's own predicate
as the disjunct a short window, whose mask words are zero, is decided by. -/
def vQB (qm : BitVec 32) (ki : BitVec 64) (b : UInt8) : BitVec 1 :=
  vM3 qm ki ||| vQ4 b

/-- `%s4`: the byte is a backslash. -/
def vS4 (b : UInt8) : BitVec 1 := evalICmp .eq (vByte b) 92

/-- `%sb`: the lane's backslash bit. -/
def vSB (qs : BitVec 32) (ki : BitVec 64) (b : UInt8) : BitVec 1 :=
  vM3 qs ki ||| vS4 b

/-- `%c4`: the byte is a control byte, the `b < 0x20` predicate. -/
def vC4 (b : UInt8) : BitVec 1 := evalICmp .ult (vByte b) 32

/-- `%cb`: the lane's control bit. -/
def vCB (qc : BitVec 32) (ki : BitVec 64) (b : UInt8) : BitVec 1 :=
  vM3 qc ki ||| vC4 b

/-! ### The environments the opening and the skip bits leave

The `body` block's first two pieces, as builders: `laneHeadOut` is the state
`laneHead` leaves — the five opening cells over the caller's environment — and
the two skip paths add their own cells over it.  A builder's list is newest
first, so each cell is where the instruction that wrote it put it. -/

/-- The environment `laneHead` leaves: the counter read back, its low word, the
lane's bit, the byte's address and the byte, over the caller's environment. -/
def laneHeadOut (env : Env) (aIn : Nat) (ki : BitVec 64) (b : UInt8) : Env :=
  cells [("%b", .int 8 (vByte b)),
         ("%bp", .ptr (vBp aIn ki)),
         ("%one", .int 32 (vOne ki)),
         ("%k32", .int 32 (vK32 ki)),
         ("%ki", .int 64 ki)] env

/-- The environment the full-window path's skip bits leave: the three mask
words' bits over the byte's own predicates, over `laneHeadOut`'s cells. -/
def maskedSkipBitsOut (env : Env) (aIn : Nat) (ki : BitVec 64) (b : UInt8)
    (qm qs qc : BitVec 32) : Env :=
  cells [("%cb", .int 1 (vCB qc ki b)),
         ("%c4", .int 1 (vC4 b)),
         ("%c3", .int 1 (vM3 qc ki)),
         ("%c2", .int 32 (vM2 qc ki)),
         ("%c1", .int 32 (vM1 qc ki)),
         ("%c0", .int 32 qc),
         ("%sb", .int 1 (vSB qs ki b)),
         ("%s4", .int 1 (vS4 b)),
         ("%s3", .int 1 (vM3 qs ki)),
         ("%s2", .int 32 (vM2 qs ki)),
         ("%s1", .int 32 (vM1 qs ki)),
         ("%s0", .int 32 qs),
         ("%qb", .int 1 (vQB qm ki b)),
         ("%q4", .int 1 (vQ4 b)),
         ("%q3", .int 1 (vM3 qm ki)),
         ("%q2", .int 32 (vM2 qm ki)),
         ("%q1", .int 32 (vM1 qm ki)),
         ("%q0", .int 32 qm)] (laneHeadOut env aIn ki b)

/-- The environment the scalar path's skip bits leave: the byte's three
predicates, with no mask read at all. -/
def plainSkipBitsOut (env : Env) (aIn : Nat) (ki : BitVec 64) (b : UInt8) : Env :=
  cells [("%cb", .int 1 (vC4 b)),
         ("%sb", .int 1 (vS4 b)),
         ("%qb", .int 1 (vQ4 b))] (laneHeadOut env aIn ki b)

/-! ### The step vocabulary

One `evalInstr` fact per instruction shape the opening and the skip bits contain,
at the width the body writes; the `denoteCode` wrappers below turn each into a
chain step, through `BlockEval`'s `denoteCode_cons_of`.  `BlockEval`'s 64-bit
steps cover the `load` of the counter, the `trunc` and the `getelementptr`. -/

/-- `%d = and iW %a, %b`, at any width. -/
theorem step_and_reg_w (calls : Calls) (env : Env) (s : State) (d a b : String)
    (w : Nat) {x y : BitVec w}
    (ha : lookupName env a = some (.int w x)) (hb : lookupName env b = some (.int w y)) :
    evalInstr calls (stateAt env s) (.binop d .and w (.reg a) (.reg b)) =
      some (stateAt ((d, .int w (x &&& y)) :: env) s) := by
  simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq, stateAt, State.bind]
    using LeanLLVM.Refinement.JsonS1MasksIR.evalInstr_binop (r := (x &&& y).toNat)
      (ha := LeanLLVM.Refinement.BlockEval.evalOperand_reg_of env s a (.int w x) ha)
      (hb := LeanLLVM.Refinement.BlockEval.evalOperand_reg_of env s b (.int w y) hb)
      (hr := by simp [evalBinopNat, evalBinop, BitVec.ofNat_toNat])

/-- `%d = or iW %a, %b`, at any width. -/
theorem step_or_reg_w (calls : Calls) (env : Env) (s : State) (d a b : String)
    (w : Nat) {x y : BitVec w}
    (ha : lookupName env a = some (.int w x)) (hb : lookupName env b = some (.int w y)) :
    evalInstr calls (stateAt env s) (.binop d .or w (.reg a) (.reg b)) =
      some (stateAt ((d, .int w (x ||| y)) :: env) s) := by
  simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq, stateAt, State.bind]
    using LeanLLVM.Refinement.JsonS1MasksIR.evalInstr_binop (r := (x ||| y).toNat)
      (ha := LeanLLVM.Refinement.BlockEval.evalOperand_reg_of env s a (.int w x) ha)
      (hb := LeanLLVM.Refinement.BlockEval.evalOperand_reg_of env s b (.int w y) hb)
      (hr := by simp [evalBinopNat, evalBinop, BitVec.ofNat_toNat])

/-- `%d = and iW %a, <c>`, at any width. -/
theorem step_and_imm_w (calls : Calls) (env : Env) (s : State) (d a : String)
    (w : Nat) {x c : BitVec w}
    (ha : lookupName env a = some (.int w x)) :
    evalInstr calls (stateAt env s) (.binop d .and w (.reg a) (.imm (.int w c))) =
      some (stateAt ((d, .int w (x &&& c)) :: env) s) := by
  simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq, stateAt, State.bind]
    using LeanLLVM.Refinement.JsonS1MasksIR.evalInstr_binop (r := (x &&& c).toNat)
      (ha := LeanLLVM.Refinement.BlockEval.evalOperand_reg_of env s a (.int w x) ha)
      (hb := LeanLLVM.Refinement.BlockEval.evalOperand_lit_of _ w c)
      (hr := by simp [evalBinopNat, evalBinop, BitVec.ofNat_toNat])

/-- `%d = lshr iW %a, %b`, at any width. -/
theorem step_lshr_reg_w (calls : Calls) (env : Env) (s : State) (d a b : String)
    (w : Nat) {x y : BitVec w}
    (ha : lookupName env a = some (.int w x)) (hb : lookupName env b = some (.int w y)) :
    evalInstr calls (stateAt env s) (.binop d .lshr w (.reg a) (.reg b)) =
      some (stateAt ((d, .int w (x >>> y.toNat)) :: env) s) := by
  simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq, stateAt, State.bind]
    using LeanLLVM.Refinement.JsonS1MasksIR.evalInstr_binop (r := (x >>> y.toNat).toNat)
      (ha := LeanLLVM.Refinement.BlockEval.evalOperand_reg_of env s a (.int w x) ha)
      (hb := LeanLLVM.Refinement.BlockEval.evalOperand_reg_of env s b (.int w y) hb)
      (hr := by simp [evalBinopNat, evalBinop, BitVec.ofNat_toNat])

/-- `%d = shl iW <c>, %b`, at any width — the mask form a variable lane index
produces. -/
theorem step_shl_lit_w (calls : Calls) (env : Env) (s : State) (d b : String)
    (w : Nat) {c y : BitVec w}
    (hb : lookupName env b = some (.int w y)) :
    evalInstr calls (stateAt env s) (.binop d .shl w (.imm (.int w c)) (.reg b)) =
      some (stateAt ((d, .int w (c <<< y.toNat)) :: env) s) := by
  simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq, stateAt, State.bind]
    using LeanLLVM.Refinement.JsonS1MasksIR.evalInstr_binop (r := (c <<< y.toNat).toNat)
      (ha := LeanLLVM.Refinement.BlockEval.evalOperand_lit_of _ w c)
      (hb := LeanLLVM.Refinement.BlockEval.evalOperand_reg_of env s b (.int w y) hb)
      (hr := by simp [evalBinopNat, evalBinop, BitVec.ofNat_toNat])

/-- `%d = icmp <pred> iW %a, <c>`, at any width: the byte predicates and the
mask words' tests share this shape. -/
theorem step_icmp_imm_w (calls : Calls) (env : Env) (s : State) (d a : String)
    (pred : IPred) (w : Nat) {x c : BitVec w}
    (ha : lookupName env a = some (.int w x)) :
    evalInstr calls (stateAt env s) (.icmp d pred w (.reg a) (.imm (.int w c))) =
      some (stateAt ((d, .int 1 (evalICmp pred x c)) :: env) s) := by
  simpa only [stateAt, State.bind]
    using LeanLLVM.Refinement.JsonS1MasksIR.evalInstr_icmp
      (ha := LeanLLVM.Refinement.BlockEval.evalOperand_reg_of env s a (.int w x) ha)
      (hb := LeanLLVM.Refinement.BlockEval.evalOperand_lit_of _ w c)

/-- A one-byte read is the byte's own value. -/
theorem loadValue_i8_of_readBytes {m : Mem} {a : Nat} {bs : List UInt8}
    (hr : readBytes m a 1 = some bs) :
    loadValue m (.int 8) a = some (.int 8 (BitVec.ofNat 8 (bytesToNat bs))) := by
  simp only [loadValue, show (8 + 7) / 8 = 1 from rfl,
    show (8 = 0) = False from by decide, ite_false, hr]

/-- A four-byte read is the word it encodes. -/
theorem loadValue_i32_of_readBytes {m : Mem} {a : Nat} {bs : List UInt8}
    (hr : readBytes m a 4 = some bs) :
    loadValue m (.int 32) a = some (.int 32 (BitVec.ofNat 32 (bytesToNat bs))) := by
  simp only [loadValue, show (32 + 7) / 8 = 4 from rfl,
    show (32 = 0) = False from by decide, ite_false, hr]

/-- Four little-endian bytes encode a word below `2 ^ 32`. -/
theorem bytesToNat_natToBytes32 (v : BitVec 32) :
    bytesToNat (natToBytes v.toNat 4) = v.toNat := by
  rw [natToBytes_toNat, show (256 : Nat) ^ 4 = 2 ^ 32 from by decide,
    Nat.mod_eq_of_lt (by have := v.isLt; omega)]

/-- `%d = load i8, ptr %p`: the lane's byte, as the body reads it. -/
theorem step_load_i8 (calls : Calls) (env : Env) (s : State) (d p : String)
    {a : Nat} {b : UInt8}
    (hp : lookupName env p = some (.ptr a))
    (hv : readBytes s.mem a 1 = some [b]) :
    evalInstr calls (stateAt env s) (.load d (.int 8) (.reg p)) =
      some (stateAt ((d, .int 8 (vByte b)) :: env) s) := by
  have hv' : loadValue s.mem (.int 8) a = some (.int 8 (vByte b)) := by
    rw [loadValue_i8_of_readBytes hv]
    simp only [bytesToNat, Nat.mul_zero, Nat.add_zero, vByte]
  rw [LeanLLVM.Refinement.JsonS1MasksIR.evalInstr_load
    (hp := LeanLLVM.Refinement.BlockEval.evalOperand_reg_of env s p (.ptr a) hp)
    (hv := by simpa only [stateAt] using hv')]
  simp [stateAt, State.bind]

/-- `%d = load i32, ptr %p`: one of the three mask words. -/
theorem step_load_i32 (calls : Calls) (env : Env) (s : State) (d p : String)
    {a : Nat} {v : BitVec 32}
    (hp : lookupName env p = some (.ptr a))
    (hv : readBytes s.mem a 4 = some (natToBytes v.toNat 4)) :
    evalInstr calls (stateAt env s) (.load d (.int 32) (.reg p)) =
      some (stateAt ((d, .int 32 v) :: env) s) := by
  have hv' : loadValue s.mem (.int 32) a = some (.int 32 v) := by
    rw [loadValue_i32_of_readBytes hv, bytesToNat_natToBytes32, BitVec.ofNat_toNat,
      BitVec.setWidth_eq]
  rw [LeanLLVM.Refinement.JsonS1MasksIR.evalInstr_load
    (hp := LeanLLVM.Refinement.BlockEval.evalOperand_reg_of env s p (.ptr a) hp)
    (hv := by simpa only [stateAt] using hv')]
  simp [stateAt, State.bind]

/-! ### Composition

A straight-line run splits at a point whose second half does not begin with a
`phi`: here every lane piece is `phi`-free, so the split is available wherever
one named piece ends and the next begins. -/

/-- A straight-line run splits at a block boundary. -/
theorem denoteRun_append (calls : Calls) :
    ∀ (a b : List Instr) (pend : List (String × Value)) (s : State),
      startsWithPhi b = false →
      denoteRun calls pend (a ++ b) s =
        (denoteRun calls pend a s).bind (denoteCode calls b)
  | [], b, pend, s, hb => by
      simp only [List.nil_append, denoteRun, Option.bind_some]
      exact LeanLLVM.denoteRun_nil_pend hb
  | i :: a, b, pend, s, hb => by
      simp only [List.cons_append]
      by_cases hphi : i.isPhi = true
      · obtain ⟨d, ty, inc, rfl⟩ : ∃ d ty inc, i = .phi d ty inc := by
          cases i with
          | phi d ty inc => exact ⟨d, ty, inc, rfl⟩
          | _ => simp_all [Instr.isPhi]
        simp only [denoteRun]
        cases hsel : phiSelect s inc with
        | none => rfl
        | some v =>
            exact denoteRun_append calls a b (pend ++ [(d, v)]) s hb
      · have hi : i.isPhi = false := by
          cases i <;> simp_all [Instr.isPhi]
        simp only [LeanLLVM.denoteRun_cons_of hi]
        cases he : evalInstr calls (s.bindAll pend) i with
        | none => rfl
        | some s' => simp only []; exact denoteRun_append calls a b [] s' hb

/-- A straight-line sequence splits at a block boundary. -/
theorem denoteCode_append_scan (calls : Calls) (a b : List Instr) (s : State)
    (hb : startsWithPhi b = false) :
    denoteCode calls (a ++ b) s = (denoteCode calls a s).bind (denoteCode calls b) :=
  denoteRun_append calls a b [] s hb

/-! ### The chain steps

One `denoteCode` step per shape above, so that the chain below is one rewrite
per instruction and the instruction list is the body's own. -/

theorem denoteCode_and_reg_w (calls : Calls) (env : Env) (s : State) (d a b : String)
    {w : Nat} {x y : BitVec w}
    (ha : lookupName env a = some (.int w x)) (hb : lookupName env b = some (.int w y))
    (is : List Instr) :
    denoteCode calls (.binop d .and w (.reg a) (.reg b) :: is) (stateAt env s) =
      denoteCode calls is (stateAt ((d, .int w (x &&& y)) :: env) s) := by
  rw [LeanLLVM.Refinement.BlockEval.denoteCode_cons_of _ _ _ _ _
    (step_and_reg_w calls env s d a b w ha hb)]

theorem denoteCode_or_reg_w (calls : Calls) (env : Env) (s : State) (d a b : String)
    {w : Nat} {x y : BitVec w}
    (ha : lookupName env a = some (.int w x)) (hb : lookupName env b = some (.int w y))
    (is : List Instr) :
    denoteCode calls (.binop d .or w (.reg a) (.reg b) :: is) (stateAt env s) =
      denoteCode calls is (stateAt ((d, .int w (x ||| y)) :: env) s) := by
  rw [LeanLLVM.Refinement.BlockEval.denoteCode_cons_of _ _ _ _ _
    (step_or_reg_w calls env s d a b w ha hb)]

theorem denoteCode_and_imm_w (calls : Calls) (env : Env) (s : State) (d a : String)
    {w : Nat} {x c : BitVec w}
    (ha : lookupName env a = some (.int w x)) (is : List Instr) :
    denoteCode calls (.binop d .and w (.reg a) (.imm (.int w c)) :: is) (stateAt env s) =
      denoteCode calls is (stateAt ((d, .int w (x &&& c)) :: env) s) := by
  rw [LeanLLVM.Refinement.BlockEval.denoteCode_cons_of _ _ _ _ _
    (step_and_imm_w calls env s d a w ha)]

theorem denoteCode_lshr_reg_w (calls : Calls) (env : Env) (s : State) (d a b : String)
    {w : Nat} {x y : BitVec w}
    (ha : lookupName env a = some (.int w x)) (hb : lookupName env b = some (.int w y))
    (is : List Instr) :
    denoteCode calls (.binop d .lshr w (.reg a) (.reg b) :: is) (stateAt env s) =
      denoteCode calls is (stateAt ((d, .int w (x >>> y.toNat)) :: env) s) := by
  rw [LeanLLVM.Refinement.BlockEval.denoteCode_cons_of _ _ _ _ _
    (step_lshr_reg_w calls env s d a b w ha hb)]

theorem denoteCode_shl_lit_w (calls : Calls) (env : Env) (s : State) (d b : String)
    {w : Nat} {c y : BitVec w}
    (hb : lookupName env b = some (.int w y)) (is : List Instr) :
    denoteCode calls (.binop d .shl w (.imm (.int w c)) (.reg b) :: is) (stateAt env s) =
      denoteCode calls is (stateAt ((d, .int w (c <<< y.toNat)) :: env) s) := by
  rw [LeanLLVM.Refinement.BlockEval.denoteCode_cons_of _ _ _ _ _
    (step_shl_lit_w calls env s d b w hb)]

theorem denoteCode_icmp_imm_w (calls : Calls) (env : Env) (s : State) (d a : String)
    (pred : IPred) {w : Nat} {x c : BitVec w}
    (ha : lookupName env a = some (.int w x)) (is : List Instr) :
    denoteCode calls (.icmp d pred w (.reg a) (.imm (.int w c)) :: is) (stateAt env s) =
      denoteCode calls is (stateAt ((d, .int 1 (evalICmp pred x c)) :: env) s) := by
  rw [LeanLLVM.Refinement.BlockEval.denoteCode_cons_of _ _ _ _ _
    (step_icmp_imm_w calls env s d a pred w ha)]

theorem denoteCode_load_i8 (calls : Calls) (env : Env) (s : State) (d p : String)
    {a : Nat} {b : UInt8}
    (hp : lookupName env p = some (.ptr a))
    (hv : readBytes s.mem a 1 = some [b]) (is : List Instr) :
    denoteCode calls (.load d (.int 8) (.reg p) :: is) (stateAt env s) =
      denoteCode calls is (stateAt ((d, .int 8 (vByte b)) :: env) s) := by
  rw [LeanLLVM.Refinement.BlockEval.denoteCode_cons_of _ _ _ _ _
    (step_load_i8 calls env s d p hp hv)]

theorem denoteCode_load_i32 (calls : Calls) (env : Env) (s : State) (d p : String)
    {a : Nat} {v : BitVec 32}
    (hp : lookupName env p = some (.ptr a))
    (hv : readBytes s.mem a 4 = some (natToBytes v.toNat 4)) (is : List Instr) :
    denoteCode calls (.load d (.int 32) (.reg p) :: is) (stateAt env s) =
      denoteCode calls is (stateAt ((d, .int 32 v) :: env) s) := by
  rw [LeanLLVM.Refinement.BlockEval.denoteCode_cons_of _ _ _ _ _
    (step_load_i32 calls env s d p hp hv)]

/-! #### The shapes the byte rule adds

The lane body's rule runs at thirty-two bits and at one bit, on conditions it
computed rather than on a literal, and writes the mask, the stop and the carry
through `store i32`.  `BlockEval` carries the 64-bit arithmetic, the `select`
on a literal condition and the `getelementptr` at a register index; the steps
above carry the one-byte and one-word loads.  The shapes below are the rest:
`icmp` at two registers, `xor`/`sub`/`add` and the `or` of a literal at any
width, `select` at any width on a computed condition with each pair of operand
shapes, `getelementptr` at a literal index, and `store i32`. -/

/-- `%d = icmp <pred> iW %a, %b`, at any width. -/
theorem step_icmp_reg_w (calls : Calls) (env : Env) (s : State) (d a b : String)
    (pred : IPred) (w : Nat) {x y : BitVec w}
    (ha : lookupName env a = some (.int w x)) (hb : lookupName env b = some (.int w y)) :
    evalInstr calls (stateAt env s) (.icmp d pred w (.reg a) (.reg b)) =
      some (stateAt ((d, .int 1 (evalICmp pred x y)) :: env) s) := by
  simpa only [stateAt, State.bind]
    using LeanLLVM.Refinement.JsonS1MasksIR.evalInstr_icmp
      (ha := LeanLLVM.Refinement.BlockEval.evalOperand_reg_of env s a (.int w x) ha)
      (hb := LeanLLVM.Refinement.BlockEval.evalOperand_reg_of env s b (.int w y) hb)

/-- `%d = xor iW %a, %b`, at any width. -/
theorem step_xor_reg_w (calls : Calls) (env : Env) (s : State) (d a b : String)
    (w : Nat) {x y : BitVec w}
    (ha : lookupName env a = some (.int w x)) (hb : lookupName env b = some (.int w y)) :
    evalInstr calls (stateAt env s) (.binop d .xor w (.reg a) (.reg b)) =
      some (stateAt ((d, .int w (x ^^^ y)) :: env) s) := by
  simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq, stateAt, State.bind]
    using LeanLLVM.Refinement.JsonS1MasksIR.evalInstr_binop (r := (x ^^^ y).toNat)
      (ha := LeanLLVM.Refinement.BlockEval.evalOperand_reg_of env s a (.int w x) ha)
      (hb := LeanLLVM.Refinement.BlockEval.evalOperand_reg_of env s b (.int w y) hb)
      (hr := by simp [evalBinopNat, evalBinop, BitVec.ofNat_toNat])

/-- `%d = xor iW %a, <c>`, at any width. -/
theorem step_xor_imm_w (calls : Calls) (env : Env) (s : State) (d a : String)
    (w : Nat) {x c : BitVec w}
    (ha : lookupName env a = some (.int w x)) :
    evalInstr calls (stateAt env s) (.binop d .xor w (.reg a) (.imm (.int w c))) =
      some (stateAt ((d, .int w (x ^^^ c)) :: env) s) := by
  simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq, stateAt, State.bind]
    using LeanLLVM.Refinement.JsonS1MasksIR.evalInstr_binop (r := (x ^^^ c).toNat)
      (ha := LeanLLVM.Refinement.BlockEval.evalOperand_reg_of env s a (.int w x) ha)
      (hb := LeanLLVM.Refinement.BlockEval.evalOperand_lit_of _ w c)
      (hr := by simp [evalBinopNat, evalBinop, BitVec.ofNat_toNat])

/-- `%d = sub iW %a, <c>`, at any width. -/
theorem step_sub_imm_w (calls : Calls) (env : Env) (s : State) (d a : String)
    (w : Nat) {x c : BitVec w}
    (ha : lookupName env a = some (.int w x)) :
    evalInstr calls (stateAt env s) (.binop d .sub w (.reg a) (.imm (.int w c))) =
      some (stateAt ((d, .int w (x - c)) :: env) s) := by
  simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq, stateAt, State.bind]
    using LeanLLVM.Refinement.JsonS1MasksIR.evalInstr_binop (r := (x - c).toNat)
      (ha := LeanLLVM.Refinement.BlockEval.evalOperand_reg_of env s a (.int w x) ha)
      (hb := LeanLLVM.Refinement.BlockEval.evalOperand_lit_of _ w c)
      (hr := by simp [evalBinopNat, evalBinop, BitVec.ofNat_toNat])

/-- `%d = add iW %a, <c>`, at any width. -/
theorem step_add_imm_w (calls : Calls) (env : Env) (s : State) (d a : String)
    (w : Nat) {x c : BitVec w}
    (ha : lookupName env a = some (.int w x)) :
    evalInstr calls (stateAt env s) (.binop d .add w (.reg a) (.imm (.int w c))) =
      some (stateAt ((d, .int w (x + c)) :: env) s) := by
  simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq, stateAt, State.bind]
    using LeanLLVM.Refinement.JsonS1MasksIR.evalInstr_binop (r := (x + c).toNat)
      (ha := LeanLLVM.Refinement.BlockEval.evalOperand_reg_of env s a (.int w x) ha)
      (hb := LeanLLVM.Refinement.BlockEval.evalOperand_lit_of _ w c)
      (hr := by simp [evalBinopNat, evalBinop, BitVec.ofNat_toNat])

/-- `%d = or iW %a, <c>`, at any width. -/
theorem step_or_imm_w (calls : Calls) (env : Env) (s : State) (d a : String)
    (w : Nat) {x c : BitVec w}
    (ha : lookupName env a = some (.int w x)) :
    evalInstr calls (stateAt env s) (.binop d .or w (.reg a) (.imm (.int w c))) =
      some (stateAt ((d, .int w (x ||| c)) :: env) s) := by
  simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq, stateAt, State.bind]
    using LeanLLVM.Refinement.JsonS1MasksIR.evalInstr_binop (r := (x ||| c).toNat)
      (ha := LeanLLVM.Refinement.BlockEval.evalOperand_reg_of env s a (.int w x) ha)
      (hb := LeanLLVM.Refinement.BlockEval.evalOperand_lit_of _ w c)
      (hr := by simp [evalBinopNat, evalBinop, BitVec.ofNat_toNat])

/-- `%d = select i1 %c, %a, %b` at any width, the condition computed. -/
theorem step_select_bit_reg_w (calls : Calls) (env : Env) (s : State)
    (d c a b : String) (w : Nat) {bb : BitVec 1} {x y : BitVec w}
    (hc : lookupName env c = some (.int 1 bb))
    (ha : lookupName env a = some (.int w x))
    (hb : lookupName env b = some (.int w y)) :
    evalInstr calls (stateAt env s) (.select d (.int w) (.reg c) (.reg a) (.reg b)) =
      some (stateAt ((d, .int w (if bb = 1 then x else y)) :: env) s) := by
  rcases LeanLLVM.Refinement.BlockEval.bitVec1_eq_zero_or_one bb with h | h
  · subst h
    rw [ite_eq_right (by decide)]
    rw [LeanLLVM.Refinement.JsonS1MasksIR.evalInstr_select_false
      (hc := LeanLLVM.Refinement.BlockEval.evalOperand_reg_of env s c (.int 1 (0 : BitVec 1)) hc)
      (ha := LeanLLVM.Refinement.BlockEval.evalOperand_reg_of env s a (.int w x) ha)
      (hb := LeanLLVM.Refinement.BlockEval.evalOperand_reg_of env s b (.int w y) hb)]
    simp only [stateAt, State.bind]
  · subst h
    rw [ite_eq_left rfl]
    rw [LeanLLVM.Refinement.JsonS1MasksIR.evalInstr_select_true
      (hc := LeanLLVM.Refinement.BlockEval.evalOperand_reg_of env s c (.int 1 (1 : BitVec 1)) hc)
      (ha := LeanLLVM.Refinement.BlockEval.evalOperand_reg_of env s a (.int w x) ha)
      (hb := LeanLLVM.Refinement.BlockEval.evalOperand_reg_of env s b (.int w y) hb)]
    simp only [stateAt, State.bind]

/-- `%d = select i1 %c, %a, <b>` at any width, the condition computed. -/
theorem step_select_bit_reg_imm_w (calls : Calls) (env : Env) (s : State)
    (d c a : String) (w : Nat) {bb : BitVec 1} {x y : BitVec w}
    (hc : lookupName env c = some (.int 1 bb))
    (ha : lookupName env a = some (.int w x)) :
    evalInstr calls (stateAt env s)
        (.select d (.int w) (.reg c) (.reg a) (.imm (.int w y))) =
      some (stateAt ((d, .int w (if bb = 1 then x else y)) :: env) s) := by
  rcases LeanLLVM.Refinement.BlockEval.bitVec1_eq_zero_or_one bb with h | h
  · subst h
    rw [ite_eq_right (by decide)]
    rw [LeanLLVM.Refinement.JsonS1MasksIR.evalInstr_select_false
      (hc := LeanLLVM.Refinement.BlockEval.evalOperand_reg_of env s c (.int 1 (0 : BitVec 1)) hc)
      (ha := LeanLLVM.Refinement.BlockEval.evalOperand_reg_of env s a (.int w x) ha)
      (hb := LeanLLVM.Refinement.BlockEval.evalOperand_lit_of _ w y)]
    simp only [stateAt, State.bind]
  · subst h
    rw [ite_eq_left rfl]
    rw [LeanLLVM.Refinement.JsonS1MasksIR.evalInstr_select_true
      (hc := LeanLLVM.Refinement.BlockEval.evalOperand_reg_of env s c (.int 1 (1 : BitVec 1)) hc)
      (ha := LeanLLVM.Refinement.BlockEval.evalOperand_reg_of env s a (.int w x) ha)
      (hb := LeanLLVM.Refinement.BlockEval.evalOperand_lit_of _ w y)]
    simp only [stateAt, State.bind]

/-- `%d = select i1 %c, <a>, %b` at any width, the condition computed. -/
theorem step_select_bit_imm_reg_w (calls : Calls) (env : Env) (s : State)
    (d c b : String) (w : Nat) {bb : BitVec 1} {x y : BitVec w}
    (hc : lookupName env c = some (.int 1 bb))
    (hb : lookupName env b = some (.int w y)) :
    evalInstr calls (stateAt env s)
        (.select d (.int w) (.reg c) (.imm (.int w x)) (.reg b)) =
      some (stateAt ((d, .int w (if bb = 1 then x else y)) :: env) s) := by
  rcases LeanLLVM.Refinement.BlockEval.bitVec1_eq_zero_or_one bb with h | h
  · subst h
    rw [ite_eq_right (by decide)]
    rw [LeanLLVM.Refinement.JsonS1MasksIR.evalInstr_select_false
      (hc := LeanLLVM.Refinement.BlockEval.evalOperand_reg_of env s c (.int 1 (0 : BitVec 1)) hc)
      (ha := LeanLLVM.Refinement.BlockEval.evalOperand_lit_of _ w x)
      (hb := LeanLLVM.Refinement.BlockEval.evalOperand_reg_of env s b (.int w y) hb)]
    simp only [stateAt, State.bind]
  · subst h
    rw [ite_eq_left rfl]
    rw [LeanLLVM.Refinement.JsonS1MasksIR.evalInstr_select_true
      (hc := LeanLLVM.Refinement.BlockEval.evalOperand_reg_of env s c (.int 1 (1 : BitVec 1)) hc)
      (ha := LeanLLVM.Refinement.BlockEval.evalOperand_lit_of _ w x)
      (hb := LeanLLVM.Refinement.BlockEval.evalOperand_reg_of env s b (.int w y) hb)]
    simp only [stateAt, State.bind]

/-- `%d = select i1 %c, <a>, <b>` at any width, the condition computed. -/
theorem step_select_bit_imm_imm_w (calls : Calls) (env : Env) (s : State)
    (d c : String) (w : Nat) {bb : BitVec 1} {x y : BitVec w}
    (hc : lookupName env c = some (.int 1 bb)) :
    evalInstr calls (stateAt env s)
        (.select d (.int w) (.reg c) (.imm (.int w x)) (.imm (.int w y))) =
      some (stateAt ((d, .int w (if bb = 1 then x else y)) :: env) s) := by
  rcases LeanLLVM.Refinement.BlockEval.bitVec1_eq_zero_or_one bb with h | h
  · subst h
    rw [ite_eq_right (by decide)]
    rw [LeanLLVM.Refinement.JsonS1MasksIR.evalInstr_select_false
      (hc := LeanLLVM.Refinement.BlockEval.evalOperand_reg_of env s c (.int 1 (0 : BitVec 1)) hc)
      (ha := LeanLLVM.Refinement.BlockEval.evalOperand_lit_of _ w x)
      (hb := LeanLLVM.Refinement.BlockEval.evalOperand_lit_of _ w y)]
    simp only [stateAt, State.bind]
  · subst h
    rw [ite_eq_left rfl]
    rw [LeanLLVM.Refinement.JsonS1MasksIR.evalInstr_select_true
      (hc := LeanLLVM.Refinement.BlockEval.evalOperand_reg_of env s c (.int 1 (1 : BitVec 1)) hc)
      (ha := LeanLLVM.Refinement.BlockEval.evalOperand_lit_of _ w x)
      (hb := LeanLLVM.Refinement.BlockEval.evalOperand_lit_of _ w y)]
    simp only [stateAt, State.bind]

/-- `%d = getelementptr i8, ptr %base, <c>`, at a literal index below `2 ^ 63`. -/
theorem step_gep8_lit_w (calls : Calls) (env : Env) (s : State) (d base : String)
    {a : Nat} {w : Nat} {n : BitVec w}
    (hb : lookupName env base = some (.ptr a))
    (hpos : (n.signExtend 64).toNat < 2 ^ 63) :
    evalInstr calls (stateAt env s) (.gep d (.int 8) (.reg base) (.imm (.int w n))) =
      some (stateAt ((d, .ptr (a + (n.signExtend 64).toNat)) :: env) s) := by
  rw [evalInstr_gep_i8
    (hb := LeanLLVM.Refinement.BlockEval.evalOperand_reg_of env s base (.ptr a) hb)
    (ho := LeanLLVM.Refinement.BlockEval.evalOperand_lit_of _ w n) (hpos := hpos)]
  simp only [stateAt, State.bind]

/-- `store i32 %v, ptr %p`. -/
theorem step_store32 (calls : Calls) (env : Env) (s : State) (v p : String)
    {x : BitVec 32} {a : Nat}
    (hv : lookupName env v = some (.int 32 x))
    (hp : lookupName env p = some (.ptr a)) :
    evalInstr calls (stateAt env s) (.store (.int 32) (.reg v) (.reg p)) =
      some (stateAt env { s with mem := writeBytes s.mem a (natToBytes x.toNat 4) }) := by
  rw [LeanLLVM.Refinement.JsonS1MasksIR.evalInstr_store (vv := .int 32 x) (a := a)
    (s' := stateAt env { s with mem := writeBytes s.mem a (natToBytes x.toNat 4) })
    (hv := LeanLLVM.Refinement.BlockEval.evalOperand_reg_of env s v (.int 32 x) hv)
    (hp := LeanLLVM.Refinement.BlockEval.evalOperand_reg_of env s p (.ptr a) hp)]
  simp [storeValue, stateAt]

theorem denoteCode_icmp_reg_w (calls : Calls) (env : Env) (s : State) (d a b : String)
    (pred : IPred) (w : Nat) {x y : BitVec w}
    (ha : lookupName env a = some (.int w x)) (hb : lookupName env b = some (.int w y))
    (is : List Instr) :
    denoteCode calls (.icmp d pred w (.reg a) (.reg b) :: is) (stateAt env s) =
      denoteCode calls is (stateAt ((d, .int 1 (evalICmp pred x y)) :: env) s) := by
  rw [LeanLLVM.Refinement.BlockEval.denoteCode_cons_of _ _ _ _ _
    (step_icmp_reg_w calls env s d a b pred w ha hb)]

theorem denoteCode_xor_reg_w (calls : Calls) (env : Env) (s : State) (d a b : String)
    (w : Nat) {x y : BitVec w}
    (ha : lookupName env a = some (.int w x)) (hb : lookupName env b = some (.int w y))
    (is : List Instr) :
    denoteCode calls (.binop d .xor w (.reg a) (.reg b) :: is) (stateAt env s) =
      denoteCode calls is (stateAt ((d, .int w (x ^^^ y)) :: env) s) := by
  rw [LeanLLVM.Refinement.BlockEval.denoteCode_cons_of _ _ _ _ _
    (step_xor_reg_w calls env s d a b w ha hb)]

theorem denoteCode_xor_imm_w (calls : Calls) (env : Env) (s : State) (d a : String)
    (w : Nat) {x c : BitVec w}
    (ha : lookupName env a = some (.int w x)) (is : List Instr) :
    denoteCode calls (.binop d .xor w (.reg a) (.imm (.int w c)) :: is) (stateAt env s) =
      denoteCode calls is (stateAt ((d, .int w (x ^^^ c)) :: env) s) := by
  rw [LeanLLVM.Refinement.BlockEval.denoteCode_cons_of _ _ _ _ _
    (step_xor_imm_w calls env s d a w ha)]

theorem denoteCode_sub_imm_w (calls : Calls) (env : Env) (s : State) (d a : String)
    (w : Nat) {x c : BitVec w}
    (ha : lookupName env a = some (.int w x)) (is : List Instr) :
    denoteCode calls (.binop d .sub w (.reg a) (.imm (.int w c)) :: is) (stateAt env s) =
      denoteCode calls is (stateAt ((d, .int w (x - c)) :: env) s) := by
  rw [LeanLLVM.Refinement.BlockEval.denoteCode_cons_of _ _ _ _ _
    (step_sub_imm_w calls env s d a w ha)]

theorem denoteCode_add_imm_w (calls : Calls) (env : Env) (s : State) (d a : String)
    (w : Nat) {x c : BitVec w}
    (ha : lookupName env a = some (.int w x)) (is : List Instr) :
    denoteCode calls (.binop d .add w (.reg a) (.imm (.int w c)) :: is) (stateAt env s) =
      denoteCode calls is (stateAt ((d, .int w (x + c)) :: env) s) := by
  rw [LeanLLVM.Refinement.BlockEval.denoteCode_cons_of _ _ _ _ _
    (step_add_imm_w calls env s d a w ha)]

theorem denoteCode_or_imm_w (calls : Calls) (env : Env) (s : State) (d a : String)
    (w : Nat) {x c : BitVec w}
    (ha : lookupName env a = some (.int w x)) (is : List Instr) :
    denoteCode calls (.binop d .or w (.reg a) (.imm (.int w c)) :: is) (stateAt env s) =
      denoteCode calls is (stateAt ((d, .int w (x ||| c)) :: env) s) := by
  rw [LeanLLVM.Refinement.BlockEval.denoteCode_cons_of _ _ _ _ _
    (step_or_imm_w calls env s d a w ha)]

theorem denoteCode_select_bit_reg_w (calls : Calls) (env : Env) (s : State)
    (d c a b : String) (w : Nat) {bb : BitVec 1} {x y : BitVec w}
    (hc : lookupName env c = some (.int 1 bb))
    (ha : lookupName env a = some (.int w x))
    (hb : lookupName env b = some (.int w y)) (is : List Instr) :
    denoteCode calls (.select d (.int w) (.reg c) (.reg a) (.reg b) :: is)
        (stateAt env s) =
      denoteCode calls is (stateAt ((d, .int w (if bb = 1 then x else y)) :: env) s) := by
  rw [LeanLLVM.Refinement.BlockEval.denoteCode_cons_of _ _ _ _ _
    (step_select_bit_reg_w calls env s d c a b w hc ha hb)]

theorem denoteCode_select_bit_reg_imm_w (calls : Calls) (env : Env) (s : State)
    (d c a : String) (w : Nat) {bb : BitVec 1} {x y : BitVec w}
    (hc : lookupName env c = some (.int 1 bb))
    (ha : lookupName env a = some (.int w x)) (is : List Instr) :
    denoteCode calls
        (.select d (.int w) (.reg c) (.reg a) (.imm (.int w y)) :: is) (stateAt env s) =
      denoteCode calls is (stateAt ((d, .int w (if bb = 1 then x else y)) :: env) s) := by
  rw [LeanLLVM.Refinement.BlockEval.denoteCode_cons_of _ _ _ _ _
    (step_select_bit_reg_imm_w calls env s d c a w hc ha)]

theorem denoteCode_select_bit_imm_reg_w (calls : Calls) (env : Env) (s : State)
    (d c b : String) (w : Nat) {bb : BitVec 1} {x y : BitVec w}
    (hc : lookupName env c = some (.int 1 bb))
    (hb : lookupName env b = some (.int w y)) (is : List Instr) :
    denoteCode calls
        (.select d (.int w) (.reg c) (.imm (.int w x)) (.reg b) :: is) (stateAt env s) =
      denoteCode calls is (stateAt ((d, .int w (if bb = 1 then x else y)) :: env) s) := by
  rw [LeanLLVM.Refinement.BlockEval.denoteCode_cons_of _ _ _ _ _
    (step_select_bit_imm_reg_w calls env s d c b w hc hb)]

theorem denoteCode_select_bit_imm_imm_w (calls : Calls) (env : Env) (s : State)
    (d c : String) (w : Nat) {bb : BitVec 1} {x y : BitVec w}
    (hc : lookupName env c = some (.int 1 bb)) (is : List Instr) :
    denoteCode calls
        (.select d (.int w) (.reg c) (.imm (.int w x)) (.imm (.int w y)) :: is)
        (stateAt env s) =
      denoteCode calls is (stateAt ((d, .int w (if bb = 1 then x else y)) :: env) s) := by
  rw [LeanLLVM.Refinement.BlockEval.denoteCode_cons_of _ _ _ _ _
    (step_select_bit_imm_imm_w calls env s d c w hc)]

theorem denoteCode_gep8_lit_w (calls : Calls) (env : Env) (s : State) (d base : String)
    {a : Nat} {w : Nat} {n : BitVec w}
    (hb : lookupName env base = some (.ptr a))
    (hpos : (n.signExtend 64).toNat < 2 ^ 63) (is : List Instr) :
    denoteCode calls (.gep d (.int 8) (.reg base) (.imm (.int w n)) :: is)
        (stateAt env s) =
      denoteCode calls is (stateAt ((d, .ptr (a + (n.signExtend 64).toNat)) :: env) s) := by
  rw [LeanLLVM.Refinement.BlockEval.denoteCode_cons_of _ _ _ _ _
    (step_gep8_lit_w calls env s d base hb hpos)]

theorem denoteCode_store32 (calls : Calls) (env : Env) (s : State) (v p : String)
    {x : BitVec 32} {a : Nat}
    (hv : lookupName env v = some (.int 32 x))
    (hp : lookupName env p = some (.ptr a)) (is : List Instr) :
    denoteCode calls (.store (.int 32) (.reg v) (.reg p) :: is) (stateAt env s) =
      denoteCode calls is
        (stateAt env { s with mem := writeBytes s.mem a (natToBytes x.toNat 4) }) := by
  rw [LeanLLVM.Refinement.BlockEval.denoteCode_cons_of _ _ _ _ _
    (step_store32 calls env s v p hv hp)]


/-! ### The values the rule computes

Each instruction's result as a function of what it reads, so an environment
builder can name it.  A value a later instruction reads again is a definition
here rather than an expression copied into two cells; the structural bit's
table, the byte rule's conditions, the skip chain, the status word, the carry's
four words and the counter are all of this shape. -/

def vB64 (b : UInt8) : BitVec 64 := BitVec.ofNat 64 (vByte b).toNat
def vBt (b : UInt8) : BitVec 64 := vB64 b &&& BitVec.ofNat 64 63
def vG64 (b : UInt8) : BitVec 1 := evalICmp .ult (vByte b) (BitVec.ofNat 8 64)
def vG128 (b : UInt8) : BitVec 1 := evalICmp .ult (vByte b) (BitVec.ofNat 8 128)
def vT0 (b : UInt8) : BitVec 64 :=
  if vG128 b = 1 then BitVec.ofNat 64 structHi else 0
def vT1 (b : UInt8) : BitVec 64 :=
  if vG64 b = 1 then BitVec.ofNat 64 structLo else vT0 b
def vSh (b : UInt8) : BitVec 64 := vT1 b >>> (vBt b).toNat
def vSb1 (b : UInt8) : BitVec 64 := vSh b &&& BitVec.ofNat 64 1
def vStb (b : UInt8) : BitVec 1 := evalICmp .ne (vSb1 b) (BitVec.ofNat 64 0)

def vMaskNext (m0 : BitVec 32) (ki : BitVec 64) (b : UInt8) : BitVec 32 :=
  if vStb b = 1 then m0 ||| vOne ki else m0

def vOff (a n : Nat) : Nat := a + ((BitVec.ofNat 32 n).signExtend 64).toNat

def vLive (stp : BitVec 32) : BitVec 1 := evalICmp .eq stp (BitVec.ofNat 32 0)
def vInnb (f : BitVec 32) : BitVec 32 := f &&& BitVec.ofNat 32 1
def vInn (f : BitVec 32) : BitVec 1 := evalICmp .ne (vInnb f) (BitVec.ofNat 32 0)
def vOddb (f : BitVec 32) : BitVec 32 := f &&& BitVec.ofNat 32 2
def vOdd (f : BitVec 32) : BitVec 1 := evalICmp .ne (vOddb f) (BitVec.ofNat 32 0)
def vNinn (f : BitVec 32) : BitVec 1 := vInn f ^^^ BitVec.ofNat 1 1
def vMre (nw : BitVec 32) : BitVec 1 := evalICmp .ne nw (BitVec.ofNat 32 0)
def vNmre (nw : BitVec 32) : BitVec 1 := evalICmp .eq nw (BitVec.ofNat 32 0)
def vLov (lo : BitVec 32) : BitVec 32 := lo &&& BitVec.ofNat 32 255
def vHiv (hi : BitVec 32) : BitVec 32 := hi &&& BitVec.ofNat 32 255
def vB32 (b : UInt8) : BitVec 32 := BitVec.ofNat 32 (vByte b).toNat
def vIlo (b : UInt8) (lo : BitVec 32) : BitVec 1 := evalICmp .ule (vLov lo) (vB32 b)
def vIhi (b : UInt8) (hi : BitVec 32) : BitVec 1 := evalICmp .ule (vB32 b) (vHiv hi)
def vIrg (b : UInt8) (lo hi : BitVec 32) : BitVec 1 := vIlo b lo &&& vIhi b hi
def vNirg (b : UInt8) (lo hi : BitVec 32) : BitVec 1 := vIrg b lo hi ^^^ BitVec.ofNat 1 1
def vUok (b : UInt8) (nw lo hi : BitVec 32) : BitVec 1 := vMre nw &&& vIrg b lo hi
def vUbad (b : UInt8) (nw lo hi : BitVec 32) : BitVec 1 := vMre nw &&& vNirg b lo hi
def vNod (f : BitVec 32) (nw : BitVec 32) : BitVec 1 := vNmre nw &&& vOdd f
def vNodd (f : BitVec 32) : BitVec 1 := vOdd f ^^^ BitVec.ofNat 1 1
def vNpm (f : BitVec 32) (nw : BitVec 32) : BitVec 1 := vNmre nw &&& vNodd f
def vAq (f : BitVec 32) (nw : BitVec 32) (qb : BitVec 1) : BitVec 1 := vNpm f nw &&& qb
def vAqo (f : BitVec 32) (nw : BitVec 32) (qb : BitVec 1) : BitVec 1 := vAq f nw qb &&& vNinn f
def vAqc (f : BitVec 32) (nw : BitVec 32) (qb : BitVec 1) : BitVec 1 := vAq f nw qb &&& vInn f
def vNq (qb : BitVec 1) : BitVec 1 := qb ^^^ BitVec.ofNat 1 1
def vNpq (f : BitVec 32) (nw : BitVec 32) (qb : BitVec 1) : BitVec 1 := vNpm f nw &&& vNq qb
def vAbs (f : BitVec 32) (nw : BitVec 32) (qb sb : BitVec 1) : BitVec 1 := vNpq f nw qb &&& sb
def vAbsin (f : BitVec 32) (nw : BitVec 32) (qb sb : BitVec 1) : BitVec 1 :=
  vAbs f nw qb sb &&& vInn f
def vNbs (sb : BitVec 1) : BitVec 1 := sb ^^^ BitVec.ofNat 1 1
def vNpb (f : BitVec 32) (nw : BitVec 32) (qb sb : BitVec 1) : BitVec 1 :=
  vNpq f nw qb &&& vNbs sb
def vIb (f : BitVec 32) (nw : BitVec 32) (qb sb : BitVec 1) : BitVec 1 :=
  vNpb f nw qb sb &&& vInn f
def vNcb (cb : BitVec 1) : BitVec 1 := cb ^^^ BitVec.ofNat 1 1
def vActl (f : BitVec 32) (nw : BitVec 32) (qb sb cb : BitVec 1) : BitVec 1 :=
  vIb f nw qb sb &&& cb
def vLeadb (f : BitVec 32) (nw : BitVec 32) (qb sb cb : BitVec 1) : BitVec 1 :=
  vIb f nw qb sb &&& vNcb cb
def vAsc (b : UInt8) : BitVec 1 := evalICmp .ult (vByte b) (BitVec.ofNat 8 128)
def vNasc (b : UInt8) : BitVec 1 := vAsc b ^^^ BitVec.ofNat 1 1
def vLead (b : UInt8) (f : BitVec 32) (nw : BitVec 32) (qb sb cb : BitVec 1) : BitVec 1 :=
  vLeadb f nw qb sb cb &&& vNasc b
def vLge (b : UInt8) : BitVec 1 := evalICmp .uge (vByte b) (BitVec.ofNat 8 194)
def vLle (b : UInt8) : BitVec 1 := evalICmp .ule (vByte b) (BitVec.ofNat 8 244)
def vLok (b : UInt8) : BitVec 1 := vLge b &&& vLle b
def vNlok (b : UInt8) : BitVec 1 := vLok b ^^^ BitVec.ofNat 1 1
def vLbad (b : UInt8) (f : BitVec 32) (nw : BitVec 32) (qb sb cb : BitVec 1) : BitVec 1 :=
  vLead b f nw qb sb cb &&& vNlok b
def vLset (b : UInt8) (f : BitVec 32) (nw : BitVec 32) (qb sb cb : BitVec 1) : BitVec 1 :=
  vLead b f nw qb sb cb &&& vLok b

def vSk0 (f : BitVec 32) : BitVec 1 := vInn f &&& vNodd f
def vSk1 (f : BitVec 32) (nw : BitVec 32) : BitVec 1 := vSk0 f &&& vNmre nw
def vSk2 (f : BitVec 32) (nw : BitVec 32) (qb : BitVec 1) : BitVec 1 := vSk1 f nw &&& vNq qb
def vSk3 (f : BitVec 32) (nw : BitVec 32) (qb sb : BitVec 1) : BitVec 1 :=
  vSk2 f nw qb &&& vNbs sb
def vSk4 (f : BitVec 32) (nw : BitVec 32) (qb sb cb : BitVec 1) : BitVec 1 :=
  vSk3 f nw qb sb &&& vNcb cb
def vSkip (b : UInt8) (f : BitVec 32) (nw : BitVec 32) (qb sb cb : BitVec 1) : BitVec 1 :=
  vSk4 f nw qb sb cb &&& vAsc b
def vB3 (b : UInt8) : BitVec 1 := evalICmp .uge (vByte b) (BitVec.ofNat 8 240)
def vB2 (b : UInt8) : BitVec 1 := evalICmp .uge (vByte b) (BitVec.ofNat 8 224)
def vN3v (b : UInt8) : BitVec 32 :=
  if vB3 b = 1 then BitVec.ofNat 32 3 else BitVec.ofNat 32 2
def vNc (b : UInt8) : BitVec 32 :=
  if vB2 b = 1 then vN3v b else BitVec.ofNat 32 1
def vE0 (b : UInt8) : BitVec 1 := evalICmp .eq (vByte b) (BitVec.ofNat 8 224)
def vF0 (b : UInt8) : BitVec 1 := evalICmp .eq (vByte b) (BitVec.ofNat 8 240)
def vLc0 (b : UInt8) : BitVec 32 :=
  if vF0 b = 1 then BitVec.ofNat 32 144 else BitVec.ofNat 32 128
def vLc (b : UInt8) : BitVec 32 :=
  if vE0 b = 1 then BitVec.ofNat 32 160 else vLc0 b
def vQ1b (b : UInt8) : BitVec 1 := evalICmp .eq (vByte b) (BitVec.ofNat 8 237)
def vQ2b (b : UInt8) : BitVec 1 := evalICmp .eq (vByte b) (BitVec.ofNat 8 244)
def vHc0 (b : UInt8) : BitVec 32 :=
  if vQ2b b = 1 then BitVec.ofNat 32 143 else BitVec.ofNat 32 191
def vHc (b : UInt8) : BitVec 32 :=
  if vQ1b b = 1 then BitVec.ofNat 32 159 else vHc0 b

def vLane1 (ki : BitVec 64) : BitVec 32 := vK32 ki + BitVec.ofNat 32 1
def vWcl (ki : BitVec 64) : BitVec 32 := vLane1 ki + BitVec.ofNat 32 64
def vWct (ki : BitVec 64) : BitVec 32 := vLane1 ki + BitVec.ofNat 32 640
def vWbd (ki : BitVec 64) : BitVec 32 := vLane1 ki + BitVec.ofNat 32 896
def vBad8 (b : UInt8) (f : BitVec 32) (nw : BitVec 32) (lo hi : BitVec 32)
    (qb sb cb : BitVec 1) : BitVec 1 := vUbad b nw lo hi ||| vLbad b f nw qb sb cb
def vSw0 (ki : BitVec 64) (b : UInt8) (f : BitVec 32) (nw : BitVec 32) (lo hi : BitVec 32)
    (qb sb cb : BitVec 1) : BitVec 32 :=
  if vBad8 b f nw lo hi qb sb cb = 1 then vWbd ki else vWct ki
def vSw1 (ki : BitVec 64) (b : UInt8) (f : BitVec 32) (nw : BitVec 32) (lo hi : BitVec 32)
    (qb sb cb : BitVec 1) : BitVec 32 :=
  if vActl f nw qb sb cb = 1 then vWct ki else vSw0 ki b f nw lo hi qb sb cb
def vSw2 (ki : BitVec 64) (b : UInt8) (f : BitVec 32) (nw : BitVec 32) (lo hi : BitVec 32)
    (qb sb cb : BitVec 1) : BitVec 32 :=
  if vAqc f nw qb = 1 then vWcl ki else vSw1 ki b f nw lo hi qb sb cb
def vRas (b : UInt8) (f : BitVec 32) (nw : BitVec 32) (lo hi : BitVec 32)
    (qb sb cb : BitVec 1) : BitVec 1 := vUbad b nw lo hi ||| vActl f nw qb sb cb
def vRas2 (b : UInt8) (f : BitVec 32) (nw : BitVec 32) (lo hi : BitVec 32)
    (qb sb cb : BitVec 1) : BitVec 1 := vRas b f nw lo hi qb sb cb ||| vLbad b f nw qb sb cb
def vRaise (b : UInt8) (f : BitVec 32) (nw : BitVec 32) (lo hi : BitVec 32)
    (qb sb cb : BitVec 1) : BitVec 1 := vRas2 b f nw lo hi qb sb cb ||| vAqc f nw qb
def vStp0 (stp : BitVec 32) (b : UInt8) (f : BitVec 32) (nw : BitVec 32) (lo hi : BitVec 32)
    (qb sb cb : BitVec 1) : BitVec 1 := vLive stp &&& vRaise b f nw lo hi qb sb cb
def vStpn (stp : BitVec 32) (ki : BitVec 64) (b : UInt8) (f : BitVec 32) (nw : BitVec 32)
    (lo hi : BitVec 32) (qb sb cb : BitVec 1) : BitVec 32 :=
  if vStp0 stp b f nw lo hi qb sb cb = 1 then vSw2 ki b f nw lo hi qb sb cb else stp

def vNact (b : UInt8) (f : BitVec 32) (nw : BitVec 32) (qb sb cb : BitVec 1) : BitVec 1 :=
  vSkip b f nw qb sb cb ^^^ BitVec.ofNat 1 1
def vAct (stp : BitVec 32) (b : UInt8) (f : BitVec 32) (nw : BitVec 32)
    (qb sb cb : BitVec 1) : BitVec 1 := vLive stp &&& vNact b f nw qb sb cb
def vNw0 (nw : BitVec 32) : BitVec 32 := nw - BitVec.ofNat 32 1
def vFc0 (f : BitVec 32) : BitVec 32 := f ^^^ BitVec.ofNat 32 2
def vF1 (f : BitVec 32) (nw : BitVec 32) : BitVec 32 :=
  if vNod f nw = 1 then vFc0 f else f
def vFq1 (f : BitVec 32) (nw : BitVec 32) : BitVec 32 := vF1 f nw ||| BitVec.ofNat 32 1
def vF2 (f : BitVec 32) (nw : BitVec 32) (qb : BitVec 1) : BitVec 32 :=
  if vAqo f nw qb = 1 then vFq1 f nw else vF1 f nw
def vFb1 (f : BitVec 32) (nw : BitVec 32) (qb : BitVec 1) : BitVec 32 :=
  vF2 f nw qb ||| BitVec.ofNat 32 2
def vF3 (f : BitVec 32) (nw : BitVec 32) (qb sb : BitVec 1) : BitVec 32 :=
  if vAbsin f nw qb sb = 1 then vFb1 f nw qb else vF2 f nw qb
def vCw0 (b : UInt8) (nw : BitVec 32) (lo hi : BitVec 32) : BitVec 32 :=
  if vUok b nw lo hi = 1 then vNw0 nw else nw
def vCw1 (b : UInt8) (f : BitVec 32) (nw : BitVec 32) (lo hi : BitVec 32)
    (qb sb cb : BitVec 1) : BitVec 32 :=
  if vLset b f nw qb sb cb = 1 then vNc b else vCw0 b nw lo hi
def vLw0 (b : UInt8) (nw : BitVec 32) (lo hi : BitVec 32) : BitVec 32 :=
  if vUok b nw lo hi = 1 then BitVec.ofNat 32 128 else vLov lo
def vLw1 (b : UInt8) (f : BitVec 32) (nw : BitVec 32) (lo hi : BitVec 32)
    (qb sb cb : BitVec 1) : BitVec 32 :=
  if vLset b f nw qb sb cb = 1 then vLc b else vLw0 b nw lo hi
def vHw0 (b : UInt8) (nw : BitVec 32) (lo hi : BitVec 32) : BitVec 32 :=
  if vUok b nw lo hi = 1 then BitVec.ofNat 32 191 else vHiv hi
def vHw1 (b : UInt8) (f : BitVec 32) (nw : BitVec 32) (lo hi : BitVec 32)
    (qb sb cb : BitVec 1) : BitVec 32 :=
  if vLset b f nw qb sb cb = 1 then vHc b else vHw0 b nw lo hi
def vFout (stp : BitVec 32) (b : UInt8) (f : BitVec 32) (nw : BitVec 32) (lo hi : BitVec 32)
    (qb sb cb : BitVec 1) : BitVec 32 :=
  if vAct stp b f nw qb sb cb = 1 then vF3 f nw qb sb else f
def vCout (stp : BitVec 32) (b : UInt8) (f : BitVec 32) (nw : BitVec 32) (lo hi : BitVec 32)
    (qb sb cb : BitVec 1) : BitVec 32 :=
  if vAct stp b f nw qb sb cb = 1 then vCw1 b f nw lo hi qb sb cb else nw
def vLout (stp : BitVec 32) (b : UInt8) (f : BitVec 32) (nw : BitVec 32) (lo hi : BitVec 32)
    (qb sb cb : BitVec 1) : BitVec 32 :=
  if vAct stp b f nw qb sb cb = 1 then vLw1 b f nw lo hi qb sb cb else lo
def vHout (stp : BitVec 32) (b : UInt8) (f : BitVec 32) (nw : BitVec 32) (lo hi : BitVec 32)
    (qb sb cb : BitVec 1) : BitVec 32 :=
  if vAct stp b f nw qb sb cb = 1 then vHw1 b f nw lo hi qb sb cb else hi
def vKn (ki : BitVec 64) : BitVec 64 := ki + BitVec.ofNat 64 1

/-! ### The environments the rule leaves

`cells` builders in the order the instructions write them, newest first, so a
register read is the builder's own cell: one per instruction group, plus the four
memory shapes a store chain leaves (`ruleMaskMem`, `ruleStopMem`,
`ruleStateMem`, `ruleKMem`). -/


def ruleBitsOut (env : Env) (b : UInt8) : Env :=
  cells [("%stb", .int 1 (vStb b)),
         ("%sb1", .int 64 (vSb1 b)),
         ("%sh", .int 64 (vSh b)),
         ("%t1", .int 64 (vT1 b)),
         ("%t0", .int 64 (vT0 b)),
         ("%g128", .int 1 (vG128 b)),
         ("%g64", .int 1 (vG64 b)),
         ("%bt", .int 64 (vBt b)),
         ("%b64", .int 64 (vB64 b))] env

def ruleMaskOut (env : Env) (b : UInt8) (ki : BitVec 64) (m0 : BitVec 32) : Env :=
  cells [("%m2", .int 32 (vMaskNext m0 ki b)),
         ("%m1", .int 32 (m0 ||| vOne ki)),
         ("%m0", .int 32 m0)] env

def ruleCarryReadOut (env : Env) (aState : Nat) (f nw lo hi stp : BitVec 32) : Env :=
  cells [("%stp", .int 32 stp),
         ("%hi", .int 32 hi),
         ("%sp12", .ptr (vOff aState 12)),
         ("%lo", .int 32 lo),
         ("%sp8", .ptr (vOff aState 8)),
         ("%nw", .int 32 nw),
         ("%sp4", .ptr (vOff aState 4)),
         ("%f", .int 32 f)] env

def ruleMaskMem (mem : Mem) (aMask : Nat) (b : UInt8) (ki : BitVec 64)
    (m0 : BitVec 32) : Mem :=
  writeBytes mem aMask (natToBytes (vMaskNext m0 ki b).toNat 4)

def ruleStopMem (mem : Mem) (aStop : Nat) (stpn : BitVec 32) : Mem :=
  writeBytes mem aStop (natToBytes stpn.toNat 4)

def ruleStateMem (mem : Mem) (aState : Nat) (fout cout lout hout : BitVec 32) : Mem :=
  writeBytes (writeBytes (writeBytes
    (writeBytes mem aState (natToBytes fout.toNat 4))
      (vOff aState 4) (natToBytes cout.toNat 4))
      (vOff aState 8) (natToBytes lout.toNat 4))
      (vOff aState 12) (natToBytes hout.toNat 4)

def ruleKMem (mem : Mem) (aK : Nat) (kn : BitVec 64) : Mem :=
  writeBytes mem aK (natToBytes kn.toNat 8)

def ruleCondOut (env : Env) (b : UInt8) (f nw lo hi stp : BitVec 32)
    (qb sb cb : BitVec 1) : Env :=
  cells [("%lset", .int 1 (vLset b f nw qb sb cb)),
         ("%lbad", .int 1 (vLbad b f nw qb sb cb)),
         ("%nlok", .int 1 (vNlok b)),
         ("%lok", .int 1 (vLok b)),
         ("%lle", .int 1 (vLle b)),
         ("%lge", .int 1 (vLge b)),
         ("%lead", .int 1 (vLead b f nw qb sb cb)),
         ("%nasc", .int 1 (vNasc b)),
         ("%asc", .int 1 (vAsc b)),
         ("%leadb", .int 1 (vLeadb f nw qb sb cb)),
         ("%actl", .int 1 (vActl f nw qb sb cb)),
         ("%ncb", .int 1 (vNcb cb)),
         ("%ib", .int 1 (vIb f nw qb sb)),
         ("%npb", .int 1 (vNpb f nw qb sb)),
         ("%nbs", .int 1 (vNbs sb)),
         ("%absin", .int 1 (vAbsin f nw qb sb)),
         ("%abs", .int 1 (vAbs f nw qb sb)),
         ("%npq", .int 1 (vNpq f nw qb)),
         ("%nq", .int 1 (vNq qb)),
         ("%aqc", .int 1 (vAqc f nw qb)),
         ("%aqo", .int 1 (vAqo f nw qb)),
         ("%aq", .int 1 (vAq f nw qb)),
         ("%npm", .int 1 (vNpm f nw)),
         ("%nodd", .int 1 (vNodd f)),
         ("%nod", .int 1 (vNod f nw)),
         ("%ubad", .int 1 (vUbad b nw lo hi)),
         ("%uok", .int 1 (vUok b nw lo hi)),
         ("%nirg", .int 1 (vNirg b lo hi)),
         ("%irg", .int 1 (vIrg b lo hi)),
         ("%ihi", .int 1 (vIhi b hi)),
         ("%ilo", .int 1 (vIlo b lo)),
         ("%b32", .int 32 (vB32 b)),
         ("%hiv", .int 32 (vHiv hi)),
         ("%lov", .int 32 (vLov lo)),
         ("%nmre", .int 1 (vNmre nw)),
         ("%mre", .int 1 (vMre nw)),
         ("%ninn", .int 1 (vNinn f)),
         ("%odd", .int 1 (vOdd f)),
         ("%oddb", .int 32 (vOddb f)),
         ("%inn", .int 1 (vInn f)),
         ("%innb", .int 32 (vInnb f)),
         ("%live", .int 1 (vLive stp))] env

def ruleSkipOut (env : Env) (b : UInt8) (f nw : BitVec 32)
    (qb sb cb : BitVec 1) : Env :=
  cells [("%hc", .int 32 (vHc b)),
         ("%hc0", .int 32 (vHc0 b)),
         ("%q2b", .int 1 (vQ2b b)),
         ("%q1b", .int 1 (vQ1b b)),
         ("%lc", .int 32 (vLc b)),
         ("%lc0", .int 32 (vLc0 b)),
         ("%f0", .int 1 (vF0 b)),
         ("%e0", .int 1 (vE0 b)),
         ("%nc", .int 32 (vNc b)),
         ("%n3v", .int 32 (vN3v b)),
         ("%b2", .int 1 (vB2 b)),
         ("%b3", .int 1 (vB3 b)),
         ("%skip", .int 1 (vSkip b f nw qb sb cb)),
         ("%sk4", .int 1 (vSk4 f nw qb sb cb)),
         ("%sk3", .int 1 (vSk3 f nw qb sb)),
         ("%sk2", .int 1 (vSk2 f nw qb)),
         ("%sk1", .int 1 (vSk1 f nw)),
         ("%sk0", .int 1 (vSk0 f))] env

def ruleStatusOut (env : Env) (ki : BitVec 64) (b : UInt8) (f nw lo hi stp : BitVec 32)
    (qb sb cb : BitVec 1) : Env :=
  cells [("%stpn", .int 32 (vStpn stp ki b f nw lo hi qb sb cb)),
         ("%stp0", .int 1 (vStp0 stp b f nw lo hi qb sb cb)),
         ("%raise", .int 1 (vRaise b f nw lo hi qb sb cb)),
         ("%ras2", .int 1 (vRas2 b f nw lo hi qb sb cb)),
         ("%ras", .int 1 (vRas b f nw lo hi qb sb cb)),
         ("%sw2", .int 32 (vSw2 ki b f nw lo hi qb sb cb)),
         ("%sw1", .int 32 (vSw1 ki b f nw lo hi qb sb cb)),
         ("%sw0", .int 32 (vSw0 ki b f nw lo hi qb sb cb)),
         ("%bad8", .int 1 (vBad8 b f nw lo hi qb sb cb)),
         ("%wbd", .int 32 (vWbd ki)),
         ("%wct", .int 32 (vWct ki)),
         ("%wcl", .int 32 (vWcl ki)),
         ("%lane1", .int 32 (vLane1 ki))] env

def ruleCarryWriteOut (env : Env) (b : UInt8) (f nw lo hi stp : BitVec 32)
    (qb sb cb : BitVec 1) : Env :=
  cells [("%hout", .int 32 (vHout stp b f nw lo hi qb sb cb)),
         ("%lout", .int 32 (vLout stp b f nw lo hi qb sb cb)),
         ("%cout", .int 32 (vCout stp b f nw lo hi qb sb cb)),
         ("%fout", .int 32 (vFout stp b f nw lo hi qb sb cb)),
         ("%hw1", .int 32 (vHw1 b f nw lo hi qb sb cb)),
         ("%hw0", .int 32 (vHw0 b nw lo hi)),
         ("%lw1", .int 32 (vLw1 b f nw lo hi qb sb cb)),
         ("%lw0", .int 32 (vLw0 b nw lo hi)),
         ("%cw1", .int 32 (vCw1 b f nw lo hi qb sb cb)),
         ("%cw0", .int 32 (vCw0 b nw lo hi)),
         ("%f3", .int 32 (vF3 f nw qb sb)),
         ("%fb1", .int 32 (vFb1 f nw qb)),
         ("%f2", .int 32 (vF2 f nw qb)),
         ("%fq1", .int 32 (vFq1 f nw)),
         ("%f1", .int 32 (vF1 f nw)),
         ("%fc0", .int 32 (vFc0 f)),
         ("%nw0", .int 32 (vNw0 nw)),
         ("%act", .int 1 (vAct stp b f nw qb sb cb)),
         ("%nact", .int 1 (vNact b f nw qb sb cb))] env

def ruleCounterOut (env : Env) (ki : BitVec 64) : Env :=
  cells [("%kn", .int 64 (vKn ki))] env

/-! ### The environments the rule leaves, named

The eight builders nested in the order the rule runs them, so a chunk's input
environment and a composed statement both read as one name, and `ruleMem` for the
memory the state stores and the counter leave. -/

abbrev ruleEnvC (env : Env) (b : UInt8) (ki : BitVec 64) (m0 : BitVec 32) (aState : Nat)
    (f nw lo hi stp : BitVec 32) : Env :=
  ruleCarryReadOut (ruleMaskOut (ruleBitsOut env b) b ki m0) aState f nw lo hi stp
abbrev ruleEnvD (env : Env) (b : UInt8) (ki : BitVec 64) (m0 : BitVec 32) (aState : Nat)
    (f nw lo hi stp : BitVec 32) (qb sb cb : BitVec 1) : Env :=
  ruleCondOut (ruleEnvC env b ki m0 aState f nw lo hi stp) b f nw lo hi stp qb sb cb
abbrev ruleEnvE (env : Env) (b : UInt8) (ki : BitVec 64) (m0 : BitVec 32) (aState : Nat)
    (f nw lo hi stp : BitVec 32) (qb sb cb : BitVec 1) : Env :=
  ruleSkipOut (ruleEnvD env b ki m0 aState f nw lo hi stp qb sb cb) b f nw qb sb cb
abbrev ruleEnvF (env : Env) (b : UInt8) (ki : BitVec 64) (m0 : BitVec 32) (aState : Nat)
    (f nw lo hi stp : BitVec 32) (qb sb cb : BitVec 1) : Env :=
  ruleStatusOut (ruleEnvE env b ki m0 aState f nw lo hi stp qb sb cb) ki b f nw lo hi stp qb sb cb
abbrev ruleEnvG (env : Env) (b : UInt8) (ki : BitVec 64) (m0 : BitVec 32) (aState : Nat)
    (f nw lo hi stp : BitVec 32) (qb sb cb : BitVec 1) : Env :=
  ruleCarryWriteOut (ruleEnvF env b ki m0 aState f nw lo hi stp qb sb cb) b f nw lo hi stp qb sb cb
abbrev ruleEnvH (env : Env) (b : UInt8) (ki : BitVec 64) (m0 : BitVec 32) (aState : Nat)
    (f nw lo hi stp : BitVec 32) (qb sb cb : BitVec 1) : Env :=
  ruleCounterOut (ruleEnvG env b ki m0 aState f nw lo hi stp qb sb cb) ki

def ruleMem (mem : Mem) (aMask aStop aState aK : Nat) (b : UInt8) (ki : BitVec 64)
    (m0 f nw lo hi stp : BitVec 32) (qb sb cb : BitVec 1) : Mem :=
  ruleKMem (ruleStateMem (ruleStopMem (ruleMaskMem mem aMask b ki m0) aStop
      (vStpn stp ki b f nw lo hi qb sb cb)) aState
    (vFout stp b f nw lo hi qb sb cb) (vCout stp b f nw lo hi qb sb cb)
    (vLout stp b f nw lo hi qb sb cb) (vHout stp b f nw lo hi qb sb cb)) aK (vKn ki)

/-! ### The rule's own list, in the pieces the chain runs

`ruleInstrs` sliced at the boundaries the model's vocabulary names — the
structural bit's table, the mask accumulator, the carry and stop as they are
read, the byte rule's conditions, the fast skip and the lead byte's range, the
status word and the stop, the carry as it is written, and the counter.  The
slices are the body's own list, so a change to `ruleInstrs` fails
`ruleInstrs_split'` rather than drifting from the chain. -/

def ruleStructBits : List Instr := ruleInstrs.take 9
def ruleMaskInstrs : List Instr := (ruleInstrs.drop 9).take 4
def ruleCarryRead : List Instr := (ruleInstrs.drop 13).take 8
def ruleCond : List Instr := (ruleInstrs.drop 21).take 42
def ruleSkip : List Instr := (ruleInstrs.drop 63).take 18
def ruleStatus : List Instr := (ruleInstrs.drop 81).take 14
def ruleCarryWrite : List Instr := (ruleInstrs.drop 95).take 19
def ruleCounter : List Instr := (ruleInstrs.drop 114).take 6

/-! ### The chain

One step per instruction: the instruction's own `denoteCode` step, whose
hypotheses become goals.  A step is applied with no arguments — its operands and
values are read off the goal's own instruction and the builder cell that follows
it — so `lane_step` below rewrites the emitted list one instruction at a time. -/

open Lean Elab Tactic in
/-- Close one register-read goal against the environment builder: unfold the
builder, peel the cells written after it, and take the cell the name is.  Peeling
first is what keeps a failed `isDefEq` from assigning a value from a branch it
then rejects.

The goal's head is checked before anything is matched, because the caller's
memory facts and the register reads are the same shape once the values are open:
an `assumption` tried on a `readBytes` goal whose address is still unassigned can
bind that address from the wrong cell's fact.  Only the register reads are closed
here; the memory facts are the main equation's to fix. -/
elab "lane_lookup_close" : tactic => do
  let goal ← getMainGoal
  let some (_, lhs, _) := (← goal.getType).eq? | throwError "lane_lookup_close: not an equation"
  unless lhs.getAppFn.isConstOf ``lookupName do
    throwError "lane_lookup_close: not a register read"
  evalTactic (← `(tactic|
    (simp only [cells]
     repeat rw [lookupName_cons_ne _ _ (by decide)]
     first
      | rw [lookupName_cons_self]
      | assumption)))

macro "lane_rw" : tactic => `(tactic|
  (first
   | rw [denoteCode_and_reg_w]
   | rw [denoteCode_or_reg_w]
   | rw [denoteCode_and_imm_w]
   | rw [denoteCode_lshr_reg_w]
   | rw [denoteCode_shl_lit_w]
   | rw [denoteCode_icmp_imm_w]
   | rw [denoteCode_load_i8]
   | rw [denoteCode_load_i32]
   | rw [LeanLLVM.Refinement.BlockEval.denoteCode_store64]
   | rw [LeanLLVM.Refinement.BlockEval.denoteCode_load64]
   | rw [LeanLLVM.Refinement.BlockEval.denoteCode_trunc]
   | rw [LeanLLVM.Refinement.BlockEval.denoteCode_zext]
   | rw [LeanLLVM.Refinement.BlockEval.denoteCode_gep8_reg]
   | rw [denoteCode_icmp_reg_w]
   | rw [denoteCode_xor_reg_w]
   | rw [denoteCode_xor_imm_w]
   | rw [denoteCode_sub_imm_w]
   | rw [denoteCode_add_imm_w]
   | rw [denoteCode_or_imm_w]
   | rw [denoteCode_select_bit_reg_w]
   | rw [denoteCode_select_bit_reg_imm_w]
   | rw [denoteCode_select_bit_imm_reg_w]
   | rw [denoteCode_select_bit_imm_imm_w]
   | rw [denoteCode_gep8_lit_w]
   | rw [denoteCode_store32]))

/-- One instruction at a time: the literals the AST writes through
`JsonScanBody`'s helpers are unfolded, then the step that matches. -/
macro "lane_step" : tactic => `(tactic|
  (first
   | (simp (config := { failIfUnchanged := false }) only
       [JsonScanBody.lit1, JsonScanBody.lit8, JsonScanBody.lit32, JsonScanBody.lit64]
      lane_rw)
   | lane_rw))

/-- Close a lane chain: the builder's cells, then the side goals the steps left —
the semantic facts from the statement's hypotheses and the register reads from
the builder — and only then the statement's own environment, so the values the
lookups fix are the ones the equation names. -/
macro "lane_close" : tactic => `(tactic|
  (all_goals (try (simp (config := { failIfUnchanged := false }) only [cells]))
   all_goals (try (simp (config := { failIfUnchanged := false }) only
     [vByte, vK32, vOne, vBp, vM1, vM2, vM3, vQ4, vQB, vS4, vSB, vC4, vCB,
      vB64, vBt, vG64, vG128, vT0, vT1, vSh, vSb1, vStb, vMaskNext, vOff,
      vLive, vInnb, vInn, vOddb, vOdd, vNinn, vMre, vNmre, vLov, vHiv, vB32,
      vIlo, vIhi, vIrg, vNirg, vUok, vUbad, vNod, vNodd, vNpm, vAq, vAqo, vAqc,
      vNq, vNpq, vAbs, vAbsin, vNbs, vNpb, vIb, vNcb, vActl, vLeadb, vAsc, vNasc,
      vLead, vLge, vLle, vLok, vNlok, vLbad, vLset,
      vSk0, vSk1, vSk2, vSk3, vSk4, vSkip, vB3, vB2, vN3v, vNc, vE0, vF0, vLc0,
      vLc, vQ1b, vQ2b, vHc0, vHc,
      vLane1, vWcl, vWct, vWbd, vBad8, vSw0, vSw1, vSw2, vRas, vRas2, vRaise,
      vStp0, vStpn, vNact, vAct, vNw0, vFc0, vF1, vFq1, vF2, vFb1, vF3, vCw0,
      vCw1, vLw0, vLw1, vHw0, vHw1, vFout, vCout, vLout, vHout, vKn,
      ruleBitsOut, ruleMaskOut, ruleCarryReadOut, ruleCondOut, ruleSkipOut,
      ruleStatusOut, ruleCarryWriteOut, ruleCounterOut,
      ruleMaskMem, ruleStopMem, ruleStateMem, ruleKMem,
      laneHeadOut, maskedSkipBitsOut, plainSkipBitsOut]))
   all_goals (try lane_lookup_close)
   all_goals (try rfl)
   all_goals (try assumption)
   all_goals (try decide)
   all_goals (try rfl)))

/-- Resolve a register read against one of the lane's own builders —
`maskedSkipBitsOut`, `plainSkipBitsOut` or `laneHeadOut` — peeling to the cell
the name is, or falling back to the caller's environment when the register is a
parameter.  It is `lane_lookup_close` for a goal whose environment is still a
named builder rather than an unfolded one. -/
macro "builder_lk" : tactic => `(tactic|
  (simp only [maskedSkipBitsOut, plainSkipBitsOut, laneHeadOut, cells]
   repeat rw [lookupName_cons_ne _ _ (by decide)]
   first
    | rw [lookupName_cons_self]
    | assumption))

/-! ### The opening and the skip bits, as `denoteCode` equations -/

/-- **The lane's opening.**  `%ki` is the counter's eight bytes, `%k32` its low
word, `%one` the lane's bit, `%bp` the byte's address and `%b` the byte; nothing
is written, so the memory is the state's.  The byte's address is below `2 ^ 63`
by the `getelementptr`'s own bound, which the emitted body's caller supplies
because a wrapped index would be a different address. -/
theorem laneHead_step (calls : Calls) (s : State) (env : Env)
    (aIn aK : Nat) (ki : BitVec 64) (b : UInt8)
    (hk : lookupName env "%k" = some (.ptr aK))
    (hki : readBytes s.mem aK 8 = some (natToBytes ki.toNat 8))
    (hin : lookupName env "%in" = some (.ptr aIn))
    (hpos : (ki.signExtend 64).toNat < 2 ^ 63)
    (hb : readBytes s.mem (aIn + (ki.signExtend 64).toNat) 1 = some [b]) :
    denoteCode calls laneHead (stateAt env s) =
      some (stateAt (laneHeadOut env aIn ki b) s) := by
  simp only [laneHead]
  repeat lane_step
  lane_close

/-- **The full-window path's skip bits.**  For each of the three mask words the
body reads bit `k`, tests it, and or-s the byte's own predicate in; the three
`or`s are `%qb`, `%sb` and `%cb`, the conditions the rule's select chain reads. -/
theorem maskedSkipBits_step (calls : Calls) (s : State) (env : Env)
    (aIn : Nat) (ki : BitVec 64) (b : UInt8) (aQ aS aC : Nat) (qm qs qc : BitVec 32)
    (hQ : lookupName (laneHeadOut env aIn ki b) "%qmp" = some (.ptr aQ))
    (hS : lookupName (laneHeadOut env aIn ki b) "%smp" = some (.ptr aS))
    (hC : lookupName (laneHeadOut env aIn ki b) "%cmp" = some (.ptr aC))
    (hmQ : readBytes s.mem aQ 4 = some (natToBytes qm.toNat 4))
    (hmS : readBytes s.mem aS 4 = some (natToBytes qs.toNat 4))
    (hmC : readBytes s.mem aC 4 = some (natToBytes qc.toNat 4)) :
    denoteCode calls maskedSkipBits (stateAt (laneHeadOut env aIn ki b) s) =
      some (stateAt (maskedSkipBitsOut env aIn ki b qm qs qc) s) := by
  simp only [maskedSkipBits]
  repeat lane_step
  lane_close

/-- **The scalar path's skip bits.**  No mask word is read: a short window's
three bits are its byte's own predicates, which is what the full-window path's
disjuncts decide the same lanes by. -/
theorem plainSkipBits_step (calls : Calls) (s : State) (env : Env)
    (aIn : Nat) (ki : BitVec 64) (b : UInt8) :
    denoteCode calls plainSkipBits (stateAt (laneHeadOut env aIn ki b) s) =
      some (stateAt (plainSkipBitsOut env aIn ki b) s) := by
  simp only [plainSkipBits]
  repeat lane_step
  lane_close

/-! ### The chain `ruleInstrs` starts from, on each path -/

/-- **The full-window path's opening.**  The 23 instructions before the rule:
`laneHead`'s five and the eighteen that read the three mask words, composed. -/
theorem laneHeadMaskedSkipBits_step (calls : Calls) (s : State) (env : Env)
    (aIn aK : Nat) (ki : BitVec 64) (b : UInt8) (aQ aS aC : Nat) (qm qs qc : BitVec 32)
    (hk : lookupName env "%k" = some (.ptr aK))
    (hki : readBytes s.mem aK 8 = some (natToBytes ki.toNat 8))
    (hin : lookupName env "%in" = some (.ptr aIn))
    (hpos : (ki.signExtend 64).toNat < 2 ^ 63)
    (hb : readBytes s.mem (aIn + (ki.signExtend 64).toNat) 1 = some [b])
    (hQ : lookupName (laneHeadOut env aIn ki b) "%qmp" = some (.ptr aQ))
    (hS : lookupName (laneHeadOut env aIn ki b) "%smp" = some (.ptr aS))
    (hC : lookupName (laneHeadOut env aIn ki b) "%cmp" = some (.ptr aC))
    (hmQ : readBytes s.mem aQ 4 = some (natToBytes qm.toNat 4))
    (hmS : readBytes s.mem aS 4 = some (natToBytes qs.toNat 4))
    (hmC : readBytes s.mem aC 4 = some (natToBytes qc.toNat 4)) :
    denoteCode calls (laneHead ++ maskedSkipBits) (stateAt env s) =
      some (stateAt (maskedSkipBitsOut env aIn ki b qm qs qc) s) := by
  rw [denoteCode_append_scan calls laneHead maskedSkipBits (stateAt env s) (by decide)]
  rw [laneHead_step calls s env aIn aK ki b hk hki hin hpos hb]
  simp only [Option.bind]
  exact maskedSkipBits_step calls s env aIn ki b aQ aS aC qm qs qc hQ hS hC hmQ hmS hmC

/-- **The scalar path's opening.**  The eight instructions before the rule:
`laneHead`'s five and the byte's three predicates, composed. -/
theorem laneHeadPlainSkipBits_step (calls : Calls) (s : State) (env : Env)
    (aIn aK : Nat) (ki : BitVec 64) (b : UInt8)
    (hk : lookupName env "%k" = some (.ptr aK))
    (hki : readBytes s.mem aK 8 = some (natToBytes ki.toNat 8))
    (hin : lookupName env "%in" = some (.ptr aIn))
    (hpos : (ki.signExtend 64).toNat < 2 ^ 63)
    (hb : readBytes s.mem (aIn + (ki.signExtend 64).toNat) 1 = some [b]) :
    denoteCode calls (laneHead ++ plainSkipBits) (stateAt env s) =
      some (stateAt (plainSkipBitsOut env aIn ki b) s) := by
  rw [denoteCode_append_scan calls laneHead plainSkipBits (stateAt env s) (by decide)]
  rw [laneHead_step calls s env aIn aK ki b hk hki hin hpos hb]
  simp only [Option.bind]
  exact plainSkipBits_step calls s env aIn ki b

/-! ### The rule's chain

The rule's hundred and twenty instructions run as eight pieces, one per group the
model's own vocabulary names: the structural bit's table, the mask accumulator,
the carry's four words and the stop word as it reads them, the byte rule's
conditions, the fast skip and the lead byte's requirement, the status word and
the stop, the carry as the rule leaves it, and the counter.  Each piece is a
`denoteCode` equation from the environment the previous piece left; the eight
compose into `ruleInstrs_step`.
-/

/-- The list-reduction the chunk proofs share: a `take`/`drop` slice of the
body's own list, unfolded to the instructions it selects. -/
macro "lane_unfold_chunk" : tactic => `(tactic|
  (simp only [LeanLLVM.Refinement.JsonScanBody.ruleInstrs,
    List.take_succ_cons, List.take_zero, List.drop_succ_cons, List.drop_zero]))

/-- **The structural bit's table at the lane's own environment.**  The nine
instructions `structBitCode` names run against the environment the skip bits
leave, so `%stb` holds the table's answer as a `denoteCode` equation rather than
only as `structBit_correct`'s value.  The range tests, the selects, the shift and
the mask are the emitted instructions; nothing here re-describes them. -/
theorem ruleStructBits_step (calls : Calls) (s : State) (env : Env) (b : UInt8)
    (hb : lookupName env "%b" = some (.int 8 (vByte b))) :
    denoteCode calls ruleStructBits (stateAt env s) =
      some (stateAt (ruleBitsOut env b) s) := by
  simp only [ruleStructBits]
  lane_unfold_chunk
  repeat lane_step
  lane_close

set_option maxHeartbeats 4000000 in
/-- **The mask accumulator's four instructions.**  The word at `%maskp` is read,
or-ed with the lane's bit, selected by `%stb`, and written back: three cells and
the store, whose memory is `ruleMaskMem`. -/
theorem ruleMask_step (calls : Calls) (s : State) (env : Env) (b : UInt8)
    (ki : BitVec 64) (m0 : BitVec 32) (aMask : Nat)
    (hOne : lookupName env "%one" = some (.int 32 (vOne ki)))
    (hMask : lookupName env "%maskp" = some (.ptr aMask))
    (hM0 : readBytes s.mem aMask 4 = some (natToBytes m0.toNat 4)) :
    denoteCode calls ruleMaskInstrs (stateAt (ruleBitsOut env b) s) =
      some (stateAt (ruleMaskOut (ruleBitsOut env b) b ki m0)
        { s with mem := ruleMaskMem s.mem aMask b ki m0 }) := by
  simp only [ruleMaskInstrs]
  lane_unfold_chunk
  repeat lane_step
  lane_close

set_option maxHeartbeats 4000000 in
/-- **The carry and the stop as the rule reads them.**  `%f`, `%nw`, `%lo` and
`%hi` are the caller's four words at `%state`'s offsets, and `%stp` is the stop
word at `%stopp`.  The three `getelementptr`s are at literal indices, the shape
`BlockEval`'s register-index step does not carry. -/
theorem ruleCarryRead_step (calls : Calls) (s : State) (env : Env) (b : UInt8)
    (ki : BitVec 64) (m0 : BitVec 32) (aState aStop : Nat)
    (f nw lo hi stp : BitVec 32)
    (hState : lookupName env "%state" = some (.ptr aState))
    (hStop : lookupName env "%stopp" = some (.ptr aStop))
    (hF : readBytes s.mem aState 4 = some (natToBytes f.toNat 4))
    (hNw : readBytes s.mem (vOff aState 4) 4 = some (natToBytes nw.toNat 4))
    (hLo : readBytes s.mem (vOff aState 8) 4 = some (natToBytes lo.toNat 4))
    (hHi : readBytes s.mem (vOff aState 12) 4 = some (natToBytes hi.toNat 4))
    (hStp : readBytes s.mem aStop 4 = some (natToBytes stp.toNat 4)) :
    denoteCode calls ruleCarryRead
        (stateAt (ruleMaskOut (ruleBitsOut env b) b ki m0) s) =
      some (stateAt (ruleCarryReadOut (ruleMaskOut (ruleBitsOut env b) b ki m0)
        aState f nw lo hi stp) s) := by
  simp only [ruleCarryRead]
  lane_unfold_chunk
  repeat lane_step
  lane_close

/-- **The byte rule's conditions.**  The forty-two instructions from `%live` to
`%lset`: the flags, the byte's three skip predicates, the requirement's range
tests, the fast skip's conjunction, and the lead byte's accepted range with its
two special bounds.  Every one is a value cell; the select chain that consumes
them belongs to the status piece. -/
theorem ruleCond_step (calls : Calls) (s : State) (env : Env) (b : UInt8) (ki : BitVec 64)
    (m0 : BitVec 32) (aState : Nat) (f nw lo hi stp : BitVec 32) (qb sb cb : BitVec 1)
    (hB : lookupName env "%b" = some (.int 8 (vByte b)))
    (hQB : lookupName env "%qb" = some (.int 1 qb))
    (hSB : lookupName env "%sb" = some (.int 1 sb))
    (hCB : lookupName env "%cb" = some (.int 1 cb)) :
    denoteCode calls ruleCond
        (stateAt (ruleEnvC env b ki m0 aState f nw lo hi stp) s) =
      some (stateAt (ruleEnvD env b ki m0 aState f nw lo hi stp qb sb cb) s) := by
  simp only [ruleCond]
  lane_unfold_chunk
  repeat lane_step
  lane_close

set_option maxHeartbeats 16000000 in
/-- **The fast skip and the lead byte's requirement.**  `%sk0`…`%skip` and the
two selects that collapse the lead byte's nine classes to a count and two bounds.
The chain reads the byte, the three skip bits, and the conditions the previous
piece left. -/
theorem ruleSkip_step (calls : Calls) (s : State) (env : Env) (b : UInt8) (ki : BitVec 64)
    (m0 : BitVec 32) (aState : Nat) (f nw lo hi stp : BitVec 32) (qb sb cb : BitVec 1)
    (hB : lookupName env "%b" = some (.int 8 (vByte b))) :
    denoteCode calls ruleSkip
        (stateAt (ruleEnvD env b ki m0 aState f nw lo hi stp qb sb cb) s) =
      some (stateAt (ruleEnvE env b ki m0 aState f nw lo hi stp qb sb cb) s) := by
  simp only [ruleSkip]
  lane_unfold_chunk
  repeat lane_step
  lane_close

set_option maxHeartbeats 16000000 in
/-- **The status word and the first stop.**  The three refusal words, the select
chain that chooses one — testing both `%ubad` and `%lbad` — the raise, the freeze
and the store at `%stopp`. -/
theorem ruleStatus_step (calls : Calls) (s : State) (env : Env) (b : UInt8) (ki : BitVec 64)
    (m0 : BitVec 32) (aState aStop : Nat) (f nw lo hi stp : BitVec 32)
    (qb sb cb : BitVec 1)
    (hK32 : lookupName env "%k32" = some (.int 32 (vK32 ki)))
    (hStop : lookupName env "%stopp" = some (.ptr aStop)) :
    denoteCode calls ruleStatus
        (stateAt (ruleEnvE env b ki m0 aState f nw lo hi stp qb sb cb) s) =
      some (stateAt (ruleEnvF env b ki m0 aState f nw lo hi stp qb sb cb)
        { s with mem := ruleStopMem s.mem aStop (vStpn stp ki b f nw lo hi qb sb cb) }) := by
  simp only [ruleStatus]
  lane_unfold_chunk
  repeat lane_step
  lane_close

set_option maxHeartbeats 16000000 in
/-- **The carry as the rule leaves it.**  The flags, the requirement's count and
its two bounds, each gated by `%act`, are the four words `%fout`, `%cout`,
`%lout` and `%hout`.  This piece is their selects and nothing else; the stores
are the counter piece's. -/
theorem ruleCarryWrite_step (calls : Calls) (s : State) (env : Env) (b : UInt8)
    (ki : BitVec 64) (m0 : BitVec 32) (aState aStop : Nat) (f nw lo hi stp : BitVec 32)
    (qb sb cb : BitVec 1) :
    denoteCode calls ruleCarryWrite
        (stateAt (ruleEnvF env b ki m0 aState f nw lo hi stp qb sb cb) s) =
      some (stateAt (ruleEnvG env b ki m0 aState f nw lo hi stp qb sb cb) s) := by
  simp only [ruleCarryWrite]
  lane_unfold_chunk
  repeat lane_step
  lane_close

set_option maxHeartbeats 16000000 in
/-- **The state stores and the counter.**  The four carry words go to `%state`'s
offsets, `%kn` is the counter plus one, and it goes back to `%k`.  This is the
piece that leaves the memory `ruleMem` names. -/
theorem ruleCounter_step (calls : Calls) (s : State) (env : Env) (b : UInt8) (ki : BitVec 64)
    (m0 : BitVec 32) (aState aK : Nat) (f nw lo hi stp : BitVec 32) (qb sb cb : BitVec 1)
    (hState : lookupName env "%state" = some (.ptr aState))
    (hK : lookupName env "%k" = some (.ptr aK))
    (hKi : lookupName env "%ki" = some (.int 64 ki)) :
    denoteCode calls ruleCounter
        (stateAt (ruleEnvG env b ki m0 aState f nw lo hi stp qb sb cb) s) =
      some (stateAt (ruleEnvH env b ki m0 aState f nw lo hi stp qb sb cb)
        { s with mem := ruleKMem (ruleStateMem s.mem aState
            (vFout stp b f nw lo hi qb sb cb) (vCout stp b f nw lo hi qb sb cb)
            (vLout stp b f nw lo hi qb sb cb) (vHout stp b f nw lo hi qb sb cb)) aK (vKn ki) }) := by
  simp only [ruleCounter]
  lane_unfold_chunk
  repeat lane_step
  lane_close

def ruleRest1 : List Instr :=
  ruleMaskInstrs ++ (ruleCarryRead ++ (ruleCond ++ (ruleSkip ++
    (ruleStatus ++ (ruleCarryWrite ++ ruleCounter)))))
def ruleRest2 : List Instr :=
  ruleCarryRead ++ (ruleCond ++ (ruleSkip ++ (ruleStatus ++
    (ruleCarryWrite ++ ruleCounter))))
def ruleRest3 : List Instr :=
  ruleCond ++ (ruleSkip ++ (ruleStatus ++ (ruleCarryWrite ++ ruleCounter)))
def ruleRest4 : List Instr := ruleSkip ++ (ruleStatus ++ (ruleCarryWrite ++ ruleCounter))
def ruleRest5 : List Instr := ruleStatus ++ (ruleCarryWrite ++ ruleCounter)
def ruleRest6 : List Instr := ruleCarryWrite ++ ruleCounter

theorem ruleInstrs_split' : ruleInstrs = ruleStructBits ++ ruleRest1 := by decide
theorem ruleRest1_eq : ruleRest1 = ruleMaskInstrs ++ ruleRest2 := rfl
theorem ruleRest2_eq : ruleRest2 = ruleCarryRead ++ ruleRest3 := rfl
theorem ruleRest3_eq : ruleRest3 = ruleCond ++ ruleRest4 := rfl
theorem ruleRest4_eq : ruleRest4 = ruleSkip ++ ruleRest5 := rfl
theorem ruleRest5_eq : ruleRest5 = ruleStatus ++ ruleRest6 := rfl
theorem ruleRest6_eq : ruleRest6 = ruleCarryWrite ++ ruleCounter := rfl

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 100000 in
/-- **The rule's hundred and twenty instructions, in one equation.**  From an
environment that binds the lane's registers — the byte, the lane's bit, the
skip bits and the caller's three pointers — the eight pieces run in order and
leave `ruleEnvH`'s environment and `ruleMem`'s memory.  The hypotheses are the
reads the rule makes: the mask word at `%maskp` before its own store, and the
carry and stop words at the memory that store leaves. -/
theorem ruleInstrs_step (calls : Calls) (s : State) (env : Env) (b : UInt8) (ki : BitVec 64)
    (m0 f nw lo hi stp : BitVec 32) (qb sb cb : BitVec 1)
    (aMask aStop aState aK : Nat)
    (hB : lookupName env "%b" = some (.int 8 (vByte b)))
    (hOne : lookupName env "%one" = some (.int 32 (vOne ki)))
    (hQB : lookupName env "%qb" = some (.int 1 qb))
    (hSB : lookupName env "%sb" = some (.int 1 sb))
    (hCB : lookupName env "%cb" = some (.int 1 cb))
    (hMask : lookupName env "%maskp" = some (.ptr aMask))
    (hStop : lookupName env "%stopp" = some (.ptr aStop))
    (hState : lookupName env "%state" = some (.ptr aState))
    (hK : lookupName env "%k" = some (.ptr aK))
    (hK32 : lookupName env "%k32" = some (.int 32 (vK32 ki)))
    (hKi : lookupName env "%ki" = some (.int 64 ki))
    (hM0 : readBytes s.mem aMask 4 = some (natToBytes m0.toNat 4))
    (hF : readBytes (ruleMaskMem s.mem aMask b ki m0) aState 4 =
      some (natToBytes f.toNat 4))
    (hNw : readBytes (ruleMaskMem s.mem aMask b ki m0) (vOff aState 4) 4 =
      some (natToBytes nw.toNat 4))
    (hLo : readBytes (ruleMaskMem s.mem aMask b ki m0) (vOff aState 8) 4 =
      some (natToBytes lo.toNat 4))
    (hHi : readBytes (ruleMaskMem s.mem aMask b ki m0) (vOff aState 12) 4 =
      some (natToBytes hi.toNat 4))
    (hStp : readBytes (ruleMaskMem s.mem aMask b ki m0) aStop 4 =
      some (natToBytes stp.toNat 4)) :
    denoteCode calls ruleInstrs (stateAt env s) =
      some (stateAt (ruleEnvH env b ki m0 aState f nw lo hi stp qb sb cb)
        { s with mem := ruleMem s.mem aMask aStop aState aK b ki m0 f nw lo hi stp qb sb cb }) := by
  rw [ruleInstrs_split']
  rw [denoteCode_append_scan calls ruleStructBits ruleRest1 (stateAt env s) (by decide)]
  rw [ruleStructBits_step calls s env b hB]
  simp only [Option.bind]
  rw [ruleRest1_eq]
  rw [denoteCode_append_scan calls ruleMaskInstrs ruleRest2 (stateAt (ruleBitsOut env b) s)
    (by decide)]
  rw [ruleMask_step calls s env b ki m0 aMask hOne hMask hM0]
  simp only [Option.bind]
  rw [ruleRest2_eq]
  rw [denoteCode_append_scan calls ruleCarryRead ruleRest3 _ (by decide)]
  rw [ruleCarryRead_step calls _ env b ki m0 aState aStop f nw lo hi stp
    hState hStop hF hNw hLo hHi hStp]
  simp only [Option.bind]
  rw [ruleRest3_eq]
  rw [denoteCode_append_scan calls ruleCond ruleRest4 _ (by decide)]
  rw [ruleCond_step calls _ env b ki m0 aState f nw lo hi stp qb sb cb hB hQB hSB hCB]
  simp only [Option.bind]
  rw [ruleRest4_eq]
  rw [denoteCode_append_scan calls ruleSkip ruleRest5 _ (by decide)]
  rw [ruleSkip_step calls _ env b ki m0 aState f nw lo hi stp qb sb cb hB]
  simp only [Option.bind]
  rw [ruleRest5_eq]
  rw [denoteCode_append_scan calls ruleStatus ruleRest6 _ (by decide)]
  rw [ruleStatus_step calls _ env b ki m0 aState aStop f nw lo hi stp qb sb cb hK32 hStop]
  simp only [Option.bind]
  rw [ruleRest6_eq]
  rw [denoteCode_append_scan calls ruleCarryWrite ruleCounter _ (by decide)]
  rw [ruleCarryWrite_step calls _ env b ki m0 aState aStop f nw lo hi stp qb sb cb]
  simp only [Option.bind]
  rw [ruleCounter_step calls _ env b ki m0 aState aK f nw lo hi stp qb sb cb hState hK hKi]
  rfl


set_option maxHeartbeats 16000000 in
/-- **The full-window lane, as one `denoteCode` equation.**  The twenty-three
instructions before the rule and the rule's hundred and twenty: from the caller's
environment the lane reaches `ruleEnvH`'s environment and `ruleMem`'s memory. -/
theorem laneHeadMaskedSkipBits_rule_step (calls : Calls) (s : State) (env : Env)
    (aIn aK aQ aS aC aMask aStop aState : Nat) (ki : BitVec 64) (b : UInt8)
    (qm qs qc m0 f nw lo hi stp : BitVec 32)
    (hk : lookupName env "%k" = some (.ptr aK))
    (hki : readBytes s.mem aK 8 = some (natToBytes ki.toNat 8))
    (hin : lookupName env "%in" = some (.ptr aIn))
    (hpos : (ki.signExtend 64).toNat < 2 ^ 63)
    (hb : readBytes s.mem (aIn + (ki.signExtend 64).toNat) 1 = some [b])
    (hQ : lookupName (laneHeadOut env aIn ki b) "%qmp" = some (.ptr aQ))
    (hS : lookupName (laneHeadOut env aIn ki b) "%smp" = some (.ptr aS))
    (hC : lookupName (laneHeadOut env aIn ki b) "%cmp" = some (.ptr aC))
    (hmQ : readBytes s.mem aQ 4 = some (natToBytes qm.toNat 4))
    (hmS : readBytes s.mem aS 4 = some (natToBytes qs.toNat 4))
    (hmC : readBytes s.mem aC 4 = some (natToBytes qc.toNat 4))
    (hMask : lookupName env "%maskp" = some (.ptr aMask))
    (hStop : lookupName env "%stopp" = some (.ptr aStop))
    (hState : lookupName env "%state" = some (.ptr aState))
    (hM0 : readBytes s.mem aMask 4 = some (natToBytes m0.toNat 4))
    (hF : readBytes (ruleMaskMem s.mem aMask b ki m0) aState 4 =
      some (natToBytes f.toNat 4))
    (hNw : readBytes (ruleMaskMem s.mem aMask b ki m0) (vOff aState 4) 4 =
      some (natToBytes nw.toNat 4))
    (hLo : readBytes (ruleMaskMem s.mem aMask b ki m0) (vOff aState 8) 4 =
      some (natToBytes lo.toNat 4))
    (hHi : readBytes (ruleMaskMem s.mem aMask b ki m0) (vOff aState 12) 4 =
      some (natToBytes hi.toNat 4))
    (hStp : readBytes (ruleMaskMem s.mem aMask b ki m0) aStop 4 =
      some (natToBytes stp.toNat 4)) :
    denoteCode calls (laneHead ++ maskedSkipBits ++ ruleInstrs) (stateAt env s) =
      some (stateAt (ruleEnvH (maskedSkipBitsOut env aIn ki b qm qs qc) b ki m0 aState
          f nw lo hi stp (vQB qm ki b) (vSB qs ki b) (vCB qc ki b))
        { s with mem := (ruleMem s.mem aMask aStop aState aK b ki m0 f nw lo hi stp
            (vQB qm ki b) (vSB qs ki b) (vCB qc ki b)) }) := by
  rw [denoteCode_append_scan calls (laneHead ++ maskedSkipBits) ruleInstrs (stateAt env s)
    (by decide)]
  rw [laneHeadMaskedSkipBits_step calls s env aIn aK ki b aQ aS aC qm qs qc
    hk hki hin hpos hb hQ hS hC hmQ hmS hmC]
  simp only [Option.bind]
  exact ruleInstrs_step calls s (maskedSkipBitsOut env aIn ki b qm qs qc) b ki m0 f nw lo hi stp
    (vQB qm ki b) (vSB qs ki b) (vCB qc ki b) aMask aStop aState aK
    (by builder_lk) (by builder_lk) (by builder_lk) (by builder_lk) (by builder_lk)
    (by builder_lk) (by builder_lk) (by builder_lk) (by builder_lk)
    (by builder_lk) (by builder_lk)
    hM0 hF hNw hLo hHi hStp

set_option maxHeartbeats 16000000 in
/-- **The scalar lane, as one `denoteCode` equation.**  The eight instructions
before the rule and the rule's hundred and twenty: the same statement as the
full-window path, with the byte's own predicates in place of the three mask
words. -/
theorem laneHeadPlainSkipBits_rule_step (calls : Calls) (s : State) (env : Env)
    (aIn aK aMask aStop aState : Nat) (ki : BitVec 64) (b : UInt8)
    (m0 f nw lo hi stp : BitVec 32)
    (hk : lookupName env "%k" = some (.ptr aK))
    (hki : readBytes s.mem aK 8 = some (natToBytes ki.toNat 8))
    (hin : lookupName env "%in" = some (.ptr aIn))
    (hpos : (ki.signExtend 64).toNat < 2 ^ 63)
    (hb : readBytes s.mem (aIn + (ki.signExtend 64).toNat) 1 = some [b])
    (hMask : lookupName env "%maskp" = some (.ptr aMask))
    (hStop : lookupName env "%stopp" = some (.ptr aStop))
    (hState : lookupName env "%state" = some (.ptr aState))
    (hM0 : readBytes s.mem aMask 4 = some (natToBytes m0.toNat 4))
    (hF : readBytes (ruleMaskMem s.mem aMask b ki m0) aState 4 =
      some (natToBytes f.toNat 4))
    (hNw : readBytes (ruleMaskMem s.mem aMask b ki m0) (vOff aState 4) 4 =
      some (natToBytes nw.toNat 4))
    (hLo : readBytes (ruleMaskMem s.mem aMask b ki m0) (vOff aState 8) 4 =
      some (natToBytes lo.toNat 4))
    (hHi : readBytes (ruleMaskMem s.mem aMask b ki m0) (vOff aState 12) 4 =
      some (natToBytes hi.toNat 4))
    (hStp : readBytes (ruleMaskMem s.mem aMask b ki m0) aStop 4 =
      some (natToBytes stp.toNat 4)) :
    denoteCode calls (laneHead ++ plainSkipBits ++ ruleInstrs) (stateAt env s) =
      some (stateAt (ruleEnvH (plainSkipBitsOut env aIn ki b) b ki m0 aState
          f nw lo hi stp (vQ4 b) (vS4 b) (vC4 b))
        { s with mem := (ruleMem s.mem aMask aStop aState aK b ki m0 f nw lo hi stp
            (vQ4 b) (vS4 b) (vC4 b)) }) := by
  rw [denoteCode_append_scan calls (laneHead ++ plainSkipBits) ruleInstrs (stateAt env s)
    (by decide)]
  rw [laneHeadPlainSkipBits_step calls s env aIn aK ki b hk hki hin hpos hb]
  simp only [Option.bind]
  exact ruleInstrs_step calls s (plainSkipBitsOut env aIn ki b) b ki m0 f nw lo hi stp
    (vQ4 b) (vS4 b) (vC4 b) aMask aStop aState aK
    (by builder_lk) (by builder_lk) (by builder_lk) (by builder_lk) (by builder_lk)
    (by builder_lk) (by builder_lk) (by builder_lk) (by builder_lk)
    (by builder_lk) (by builder_lk)
    hM0 hF hNw hLo hHi hStp


end LeanLLVM.Refinement.JsonScanLane
