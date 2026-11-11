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

**Where the bridge stands.**  The identification of the four words the rule
leaves with the carry the model steps — `decodeState` of them is `bodyStep` of
the four it read, under the `act` gate, with `maskStep` as the mask half — is
proved on both arms: `ruleBridge_pending` for an outstanding requirement, the
nine leaves and `ruleBridge_no` for the no-requirement arm, and `ruleBridge` for
the two together, all against the rule's own predicates.  **Not here at all:** the
`laneStep` lemma the loop induction consumes, the induction over `valid ≤ 32`, and
the statement's footprint clause.  `scanWindowLLVM_refines` is still the statement
`scanWindowStatement` and nothing here claims it.
-/
import LeanLLVM.Refinement.JsonScanIR
import LeanLLVM.Refinement.BlockEval

namespace LeanLLVM.Refinement.JsonScanLane

open LeanLLVM
open LeanLLVM.JSON
open LeanLLVM.Refinement.JsonScanModel
open LeanLLVM.Refinement.JsonScanABI (decodeState byteOf)
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


/-! ### The arithmetic bridge

The rule leaves four words in the slot; the model steps one `BodyState`.  This
section is the identification, at the granularity the statement needs:
`decodeState` of the four words the rule leaves is the state `bodyStep` steps
the carry to, under the `act` gate.  `maskStep` above is the mask half; this is
the rule's own arithmetic.

**Shape of the proof.**  `bodyStep` is a decision tree over the decoded state
and the byte, and the rule computes each of its four words by a `select` chain
over the same conditions.  The tree is therefore split the model's way, one
leaf per arm — a pending requirement (in range and out), the run parity, the
quote (closing and opening), the backslash, the control byte, the content
lanes, and the lead byte's nine classes — and each leaf computes the four
words and then decodes them.

Two normalization facts make the words computable by rewriting rather than by a
per-instruction chain: every predicate of the rule is restated as an `if` on the
proposition it tests (`vMre_ite`, `vOdd_ite`, …), because the semantics builds
them as `BitVec.ofBool (decide p)` and a hypothesis about `p` cannot reduce
`decide p`; and the `&&&`/`^^^` of those one-bit `if`s is folded by
`bit_ite_and_ite`/`bit_ite_xor_one`, so a `select` chain collapses to the truth
of its conditions.

**What is here and what is not.**  `ruleBridge_pending` is the pending-
requirement arm, proved: while `nw ≠ 0` the byte either continues the
requirement — `nw` drops by one, the bounds become `[0x80, 0xBF]`, the flags
are unchanged — or it does not, and the words are the carry again.  It is the
arm the lane reaches with a requirement outstanding, and it is proved against
the emitted `ruleInstrs`' own predicates, not a re-description of them.

The no-requirement arm is proved too, one leaf per branch of the tree above, and
the leaves record the two facts that shape it: `bodyStep`'s control test is a
*`Bool`* conjunction (`st.inside && decide (b < 0x20)`) rather than a
propositional one, so the `if`-condition a leaf discharges is
`(a && decide p) = true` rather than `a = true ∧ p`; and `getLsbD` of a
`select`-chain word is pushed through its `if`s by `rw [getLsbD_if_prop]`,
because `simp` does not consume that lemma even when passed explicitly.
`ruleBridge_no` dispatches on the model's own order and `ruleBridge` adds the
pending arm, so the four words decode to the carry `bodyStep` leaves on every
byte and every carry.  The lane step the loop induction consumes, the induction
over `valid ≤ 32`, the footprint clause and
`scanWindowStatementOf scanWindowBody` are still outstanding, and
`scanWindowLLVM_refines` remains unclaimed. -/

set_option maxRecDepth 20000

/-! ### One-bit comparisons -/

theorem ofBool_inj {c d : Bool} : (BitVec.ofBool c = BitVec.ofBool d) ↔ c = d := by
  cases c <;> cases d <;> decide

theorem ofBool_eq_one (c : Bool) : (BitVec.ofBool c = (1 : BitVec 1)) ↔ c = true := by
  rw [show (1 : BitVec 1) = BitVec.ofBool true from rfl, ofBool_inj]

theorem ofBool_eq_zero (c : Bool) : (BitVec.ofBool c = (0 : BitVec 1)) ↔ c = false := by
  rw [show (0 : BitVec 1) = BitVec.ofBool false from rfl, ofBool_inj]

theorem bit_and_one (x y : BitVec 1) : (x &&& y) = 1 ↔ x = 1 ∧ y = 1 := by
  rcases LeanLLVM.Refinement.BlockEval.bitVec1_eq_zero_or_one x with h | h <;>
    rcases LeanLLVM.Refinement.BlockEval.bitVec1_eq_zero_or_one y with h' | h' <;>
    rw [h, h'] <;> decide

theorem bit_xor_one (x y : BitVec 1) : (x ^^^ y) = 1 ↔ x ≠ y := by
  rcases LeanLLVM.Refinement.BlockEval.bitVec1_eq_zero_or_one x with h | h <;>
    rcases LeanLLVM.Refinement.BlockEval.bitVec1_eq_zero_or_one y with h' | h' <;>
    rw [h, h'] <;> decide

theorem bit_ite_one (c : Bool) : ((if c then (1 : BitVec 1) else 0) = 1) ↔ c = true := by
  cases c <;> decide

theorem bit_ite_zero (c : Bool) : ((if c then (1 : BitVec 1) else 0) = 0) ↔ c = false := by
  cases c <;> decide

/-! ### Bits of the flags word -/

theorem and_one_eq (x : Nat) : x &&& 1 = if x.testBit 0 then 1 else 0 := by
  rw [show (1 : Nat) = 2 ^ 1 - 1 from by decide, Nat.and_two_pow_sub_one_eq_mod,
    Nat.testBit_zero]
  have := Nat.mod_two_eq_zero_or_one x
  by_cases h : x % 2 = 1
  · simp [h]
  · have h0 : x % 2 = 0 := by omega
    simp [h0]

theorem testBit_two (i : Nat) : (2 : Nat).testBit i = decide (i = 1) := by
  rw [show (2 : Nat) = 2 ^ 1 from by decide, Nat.testBit_two_pow]
  simp [eq_comm]

theorem and_two_eq (x : Nat) : x &&& 2 = if x.testBit 1 then 2 else 0 := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and, testBit_two]
  by_cases hi : i = 1
  · subst hi
    by_cases ht : x.testBit 1
    · rw [ite_eq_left ht, testBit_two]; simp [ht]
    · rw [ite_eq_right ht, Nat.zero_testBit]; simp [ht]
  · have hd : decide (i = 1) = false := by simp [hi]
    rw [hd, Bool.and_false]
    by_cases ht : x.testBit 1
    · rw [ite_eq_left ht, testBit_two]; simp [hi]
    · rw [ite_eq_right ht, Nat.zero_testBit]

theorem and_one_ne_zero (x : Nat) : x &&& 1 ≠ 0 ↔ x.testBit 0 = true := by
  rw [and_one_eq]
  by_cases h : x.testBit 0 <;> simp [h]

theorem and_two_ne_zero (x : Nat) : x &&& 2 ≠ 0 ↔ x.testBit 1 = true := by
  rw [and_two_eq]
  by_cases h : x.testBit 1 <;> simp [h]

theorem vec_and_one_toNat (f : BitVec 32) : (f &&& 1).toNat = f.toNat &&& 1 := by
  rw [BitVec.toNat_and]; simp

theorem vec_and_two_toNat (f : BitVec 32) : (f &&& 2).toNat = f.toNat &&& 2 := by
  rw [BitVec.toNat_and]; simp

theorem vec_and_one_ne_zero (f : BitVec 32) : (f &&& 1) ≠ 0 ↔ f.getLsbD 0 = true := by
  have h : ((f &&& 1) = 0) ↔ ((f &&& 1).toNat = 0) := by
    rw [BitVec.toNat_eq]
    rfl
  rw [Ne, h, vec_and_one_toNat]
  show f.toNat &&& 1 ≠ 0 ↔ f.toNat.testBit 0 = true
  exact and_one_ne_zero f.toNat

theorem vec_and_two_ne_zero (f : BitVec 32) : (f &&& 2) ≠ 0 ↔ f.getLsbD 1 = true := by
  have h : ((f &&& 2) = 0) ↔ ((f &&& 2).toNat = 0) := by
    rw [BitVec.toNat_eq]
    rfl
  rw [Ne, h, vec_and_two_toNat]
  show f.toNat &&& 2 ≠ 0 ↔ f.toNat.testBit 1 = true
  exact and_two_ne_zero f.toNat

theorem vInn_eq (f : BitVec 32) : vInn f = 1 ↔ f.getLsbD 0 = true := by
  have h : vInn f = BitVec.ofBool (decide ((f &&& 1) ≠ 0)) := rfl
  rw [h, ofBool_eq_one]
  exact Iff.trans (by simp) (vec_and_one_ne_zero f)

theorem vOdd_eq (f : BitVec 32) : vOdd f = 1 ↔ f.getLsbD 1 = true := by
  have h : vOdd f = BitVec.ofBool (decide ((f &&& 2) ≠ 0)) := rfl
  rw [h, ofBool_eq_one]
  exact Iff.trans (by simp) (vec_and_two_ne_zero f)

theorem vMre_eq (nw : BitVec 32) : vMre nw = 1 ↔ nw ≠ 0 := by
  have h : vMre nw = BitVec.ofBool (decide (nw ≠ 0)) := rfl
  rw [h, ofBool_eq_one]
  exact Iff.trans (by simp) Iff.rfl

theorem vNmre_eq (nw : BitVec 32) : vNmre nw = 1 ↔ nw = 0 := by
  have h : vNmre nw = BitVec.ofBool (decide (nw = 0)) := rfl
  rw [h, ofBool_eq_one]
  exact Iff.trans (by simp) Iff.rfl

theorem vLive_eq (stp : BitVec 32) : vLive stp = 1 ↔ stp = 0 := by
  have h : vLive stp = BitVec.ofBool (decide (stp = 0)) := rfl
  rw [h, ofBool_eq_one]
  exact Iff.trans (by simp) Iff.rfl

theorem vByte_toNat (b : UInt8) : (vByte b).toNat = b.toNat := by
  simp only [vByte, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (UInt8.toNat_lt b)]

theorem vB32_toNat (b : UInt8) : (vB32 b).toNat = b.toNat := by
  have hb : b.toNat < 2 ^ 8 := UInt8.toNat_lt b
  have h2 : b.toNat < 2 ^ 32 := by omega
  simp only [vB32, vByte, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hb, Nat.mod_eq_of_lt h2]

theorem vAsc_eq (b : UInt8) : vAsc b = 1 ↔ b < 0x80 := by
  have h : vAsc b = BitVec.ofBool (decide ((vByte b).toNat < 128)) := rfl
  rw [h, ofBool_eq_one, vByte_toNat, UInt8.lt_iff_toNat_lt]
  simp

theorem vLov_toNat (lo : BitVec 32) : (vLov lo).toNat = lo.toNat % 256 := by
  have h : (vLov lo).toNat = lo.toNat &&& 255 := by
    rw [vLov, BitVec.toNat_and]; rfl
  rw [h, show (255 : Nat) = 2 ^ 8 - 1 from by decide, Nat.and_two_pow_sub_one_eq_mod]

theorem vHiv_toNat (hi : BitVec 32) : (vHiv hi).toNat = hi.toNat % 256 := by
  have h : (vHiv hi).toNat = hi.toNat &&& 255 := by
    rw [vHiv, BitVec.toNat_and]; rfl
  rw [h, show (255 : Nat) = 2 ^ 8 - 1 from by decide, Nat.and_two_pow_sub_one_eq_mod]

/-! ### Bytes, through the finite domain -/

theorem vQ4_eq (b : UInt8) : vQ4 b = (if IsQuoteB b then 1 else 0) := by
  have hall : (List.range 256).all
      (fun n => decide (vQ4 (UInt8.ofNat n) = (if IsQuoteB (UInt8.ofNat n) then 1 else 0)))
      = true := by decide
  have hmem : b.toNat ∈ List.range 256 := List.mem_range.mpr (by have := b.toNat_lt; omega)
  rw [← UInt8.ofNat_toNat (x := b)]
  exact of_decide_eq_true ((List.all_eq_true.mp hall) b.toNat hmem)

theorem vS4_eq (b : UInt8) : vS4 b = (if IsBackslashB b then 1 else 0) := by
  have hall : (List.range 256).all
      (fun n => decide (vS4 (UInt8.ofNat n) = (if IsBackslashB (UInt8.ofNat n) then 1 else 0)))
      = true := by decide
  have hmem : b.toNat ∈ List.range 256 := List.mem_range.mpr (by have := b.toNat_lt; omega)
  rw [← UInt8.ofNat_toNat (x := b)]
  exact of_decide_eq_true ((List.all_eq_true.mp hall) b.toNat hmem)

theorem vC4_eq (b : UInt8) : vC4 b = (if decide (b < 0x20) then 1 else 0) := by
  have hall : (List.range 256).all
      (fun n => decide (vC4 (UInt8.ofNat n) = (if decide (UInt8.ofNat n < 0x20) then 1 else 0)))
      = true := by decide
  have hmem : b.toNat ∈ List.range 256 := List.mem_range.mpr (by have := b.toNat_lt; omega)
  rw [← UInt8.ofNat_toNat (x := b)]
  exact of_decide_eq_true ((List.all_eq_true.mp hall) b.toNat hmem)

/-- The nine lead classes, as the rule's count and bounds: the byte's own value
picks them, and the rule's three selects pick the same ones. -/
theorem leadClass_agrees (b : UInt8) (hlo : 194 ≤ b) (hhi : b ≤ 244) :
    Utf8Need.step .none b =
      some (.more (vNc b).toNat (byteOf (vLc b)) (byteOf (vHc b))) := by
  have hall : (List.range 256).all (fun n => decide
      (194 ≤ UInt8.ofNat n → UInt8.ofNat n ≤ 244 →
        Utf8Need.step .none (UInt8.ofNat n) =
          some (.more (vNc (UInt8.ofNat n)).toNat (byteOf (vLc (UInt8.ofNat n)))
            (byteOf (vHc (UInt8.ofNat n)))))) = true := by decide
  have hmem : b.toNat ∈ List.range 256 := List.mem_range.mpr (by have := b.toNat_lt; omega)
  rw [← UInt8.ofNat_toNat (x := b)]
  have h := (List.all_eq_true.mp hall) b.toNat hmem
  exact of_decide_eq_true h (by simpa using hlo) (by simpa using hhi)

theorem noLeadClass_agrees (b : UInt8) (hlo : 128 ≤ b) (hout : ¬ (194 ≤ b ∧ b ≤ 244)) :
    Utf8Need.step .none b = (Option.none : Option Utf8Need) := by
  have hall : (List.range 256).all (fun n => decide
      (128 ≤ UInt8.ofNat n → ¬ (194 ≤ UInt8.ofNat n ∧ UInt8.ofNat n ≤ 244) →
        Utf8Need.step .none (UInt8.ofNat n) = (Option.none : Option Utf8Need))) = true := by decide
  have hmem : b.toNat ∈ List.range 256 := List.mem_range.mpr (by have := b.toNat_lt; omega)
  rw [← UInt8.ofNat_toNat (x := b)]
  have h := (List.all_eq_true.mp hall) b.toNat hmem
  exact of_decide_eq_true h (by simpa using hlo) (by simpa using hout)

theorem step_none_ascii (b : UInt8) (h : b < 0x80) :
    Utf8Need.step .none b = some Utf8Need.none := by
  have hall : (List.range 256).all (fun n => decide
      (UInt8.ofNat n < 0x80 → Utf8Need.step .none (UInt8.ofNat n) = some Utf8Need.none))
      = true := by decide
  have hmem : b.toNat ∈ List.range 256 := List.mem_range.mpr (by have := b.toNat_lt; omega)
  rw [← UInt8.ofNat_toNat (x := b)]
  have hh := (List.all_eq_true.mp hall) b.toNat hmem
  exact of_decide_eq_true hh (by simpa using h)

/-! ### Slot words -/

theorem byteOf_and_255 (w : BitVec 32) : byteOf (w &&& BitVec.ofNat 32 255) = byteOf w := by
  show byteOf (vLov w) = byteOf w
  unfold byteOf
  rw [vLov_toNat]
  have h : UInt8.ofNat w.toNat = UInt8.ofNat (w.toNat % 256) := by
    apply UInt8.toNat_inj.mp
    unfold UInt8.ofNat
    show (BitVec.ofNat 8 w.toNat).toNat = (BitVec.ofNat 8 (w.toNat % 256)).toNat
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    exact (Nat.mod_mod w.toNat 256).symm
  rw [h]

theorem decodeState_trunc (f nw lo hi : BitVec 32) :
    decodeState ⟨f, nw, lo &&& BitVec.ofNat 32 255, hi &&& BitVec.ofNat 32 255⟩ =
      decodeState ⟨f, nw, lo, hi⟩ := by
  simp only [decodeState, byteOf_and_255]

theorem toNat_one32 : (1 : BitVec 32).toNat = 1 := by decide

theorem sub_one_toNat {nw : BitVec 32} (h : nw ≠ 0) : (nw - 1).toNat = nw.toNat - 1 := by
  have hnz : nw.toNat ≠ 0 := by
    intro hz
    exact h (BitVec.toNat_eq.mpr (by simpa using hz))
  have h1 : (1 : BitVec 32) ≤ nw := by
    rw [BitVec.le_def, toNat_one32]
    omega
  rw [BitVec.toNat_sub_of_le h1, toNat_one32]

theorem decodeState_count (f nw : BitVec 32) (hnw : nw ≠ 0) :
    decodeState ⟨f, nw - 1, BitVec.ofNat 32 128, BitVec.ofNat 32 191⟩ =
      (⟨f.getLsbD 0, f.getLsbD 1,
        (if nw.toNat ≤ 1 then Utf8Need.none
         else Utf8Need.more (nw.toNat - 1) 0x80 0xBF)⟩ : BodyState) := by
  have hn1 : 1 ≤ nw.toNat := by
    have : nw.toNat ≠ 0 := by
      intro hz
      exact hnw (BitVec.toNat_eq.mpr (by simpa using hz))
    omega
  simp only [decodeState, byteOf, BitVec.toNat_ofNat]
  rw [sub_one_toNat hnw]
  by_cases h : nw.toNat ≤ 1
  · have h1 : nw.toNat - 1 = 0 := by omega
    simp [h, h1]
  · have h1 : nw.toNat - 1 ≠ 0 := by omega
    simp [h, h1]

theorem decodeState_of_count (f count lo hi : BitVec 32) (n : Nat) (lo' hi' : UInt8)
    (hnc : count.toNat = n) (hn0 : n ≠ 0) (hlo : lo' = byteOf lo) (hhi : hi' = byteOf hi) :
    decodeState ⟨f, count, lo, hi⟩ =
      (⟨f.getLsbD 0, f.getLsbD 1, .more n lo' hi'⟩ : BodyState) := by
  simp only [decodeState, hnc, hlo, hhi, if_neg hn0]

theorem byteOf_toNat (w : BitVec 32) : (byteOf w).toNat = w.toNat % 256 := by
  unfold byteOf
  exact UInt8.toNat_ofNat

/-! ### The rule's predicates as plain `if`s

The semantics builds every comparison as `BitVec.ofBool (decide p)`, whose
`if` cannot be reduced by a hypothesis about `p`.  Each predicate below is
restated as an `if` on the proposition, so a leaf proof's hypotheses decide it. -/

theorem bit_ite_of (p : Prop) [Decidable p] :
    BitVec.ofBool (decide p) = (if p then BitVec.ofNat 1 1 else BitVec.ofNat 1 0) := by
  by_cases h : p <;> simp [h, BitVec.ofBool]

theorem bit_ite_and_ite (p q : Prop) [Decidable p] [Decidable q] :
    ((if p then BitVec.ofNat 1 1 else BitVec.ofNat 1 0) &&&
      (if q then BitVec.ofNat 1 1 else BitVec.ofNat 1 0)) =
      (if p ∧ q then BitVec.ofNat 1 1 else BitVec.ofNat 1 0) := by
  by_cases hp : p <;> by_cases hq : q <;> simp [hp, hq]

theorem bit_ite_xor_one (p : Prop) [Decidable p] :
    ((if p then BitVec.ofNat 1 1 else BitVec.ofNat 1 0) ^^^ BitVec.ofNat 1 1) =
      (if ¬p then BitVec.ofNat 1 1 else BitVec.ofNat 1 0) := by
  by_cases hp : p <;> simp [hp]

theorem ite_one_eq_one (p : Prop) [Decidable p] :
    ((if p then BitVec.ofNat 1 1 else BitVec.ofNat 1 0) = BitVec.ofNat 1 1) ↔ p := by
  by_cases h : p <;> simp [h]

theorem ite_one_eq_zero (p : Prop) [Decidable p] :
    ((if p then BitVec.ofNat 1 1 else BitVec.ofNat 1 0) = BitVec.ofNat 1 0) ↔ ¬p := by
  by_cases h : p <;> simp [h]

theorem bit_one_and (x : BitVec 1) : BitVec.ofNat 1 1 &&& x = x := by
  rcases LeanLLVM.Refinement.BlockEval.bitVec1_eq_zero_or_one x with h | h <;>
    rw [h] <;> decide

theorem bit_and_one_r (x : BitVec 1) : x &&& BitVec.ofNat 1 1 = x := by
  rcases LeanLLVM.Refinement.BlockEval.bitVec1_eq_zero_or_one x with h | h <;>
    rw [h] <;> decide

theorem bit_zero_and (x : BitVec 1) : BitVec.ofNat 1 0 &&& x = BitVec.ofNat 1 0 := by
  rcases LeanLLVM.Refinement.BlockEval.bitVec1_eq_zero_or_one x with h | h <;>
    rw [h] <;> decide

theorem bit_and_zero_r (x : BitVec 1) : x &&& BitVec.ofNat 1 0 = BitVec.ofNat 1 0 := by
  rcases LeanLLVM.Refinement.BlockEval.bitVec1_eq_zero_or_one x with h | h <;>
    rw [h] <;> decide

theorem vMre_ite (nw : BitVec 32) : vMre nw = (if nw = 0 then BitVec.ofNat 1 0 else BitVec.ofNat 1 1) := by
  rw [show vMre nw = BitVec.ofBool (decide (nw ≠ 0)) from rfl, bit_ite_of]
  by_cases h : nw = 0 <;> simp [h]

theorem vNmre_ite (nw : BitVec 32) : vNmre nw = (if nw = 0 then BitVec.ofNat 1 1 else BitVec.ofNat 1 0) :=
  (show vNmre nw = BitVec.ofBool (decide (nw = 0)) from rfl).trans (bit_ite_of _)

theorem vInn_ite (f : BitVec 32) : vInn f = (if f.getLsbD 0 = true then BitVec.ofNat 1 1 else BitVec.ofNat 1 0) := by
  rw [show vInn f = BitVec.ofBool (decide ((f &&& 1) ≠ 0)) from rfl, bit_ite_of]
  by_cases h : f.getLsbD 0 = true
  · rw [if_pos ((vec_and_one_ne_zero f).mpr h), if_pos h]
  · rw [if_neg (fun hh => h ((vec_and_one_ne_zero f).mp hh)), if_neg h]

theorem vOdd_ite (f : BitVec 32) : vOdd f = (if f.getLsbD 1 = true then BitVec.ofNat 1 1 else BitVec.ofNat 1 0) := by
  rw [show vOdd f = BitVec.ofBool (decide ((f &&& 2) ≠ 0)) from rfl, bit_ite_of]
  by_cases h : f.getLsbD 1 = true
  · rw [if_pos ((vec_and_two_ne_zero f).mpr h), if_pos h]
  · rw [if_neg (fun hh => h ((vec_and_two_ne_zero f).mp hh)), if_neg h]

theorem vLive_ite (stp : BitVec 32) : vLive stp = (if stp = 0 then BitVec.ofNat 1 1 else BitVec.ofNat 1 0) :=
  (show vLive stp = BitVec.ofBool (decide (stp = 0)) from rfl).trans (bit_ite_of _)

theorem vAsc_ite (b : UInt8) : vAsc b = (if b < 0x80 then BitVec.ofNat 1 1 else BitVec.ofNat 1 0) := by
  have h : vAsc b = BitVec.ofBool (decide ((vByte b).toNat < 128)) := rfl
  rw [h, vByte_toNat, bit_ite_of]
  by_cases hb : b < 0x80
  · rw [if_pos (show b.toNat < 128 from by rw [UInt8.lt_iff_toNat_lt] at hb; simpa using hb),
      if_pos hb]
  · rw [if_neg (show ¬ (b.toNat < 128) from by rw [UInt8.lt_iff_toNat_lt] at hb; simpa using hb),
      if_neg hb]

theorem vQ4_ite (b : UInt8) : vQ4 b = (if IsQuoteB b then BitVec.ofNat 1 1 else BitVec.ofNat 1 0) := vQ4_eq b

theorem vS4_ite (b : UInt8) : vS4 b = (if IsBackslashB b then BitVec.ofNat 1 1 else BitVec.ofNat 1 0) := vS4_eq b

theorem vC4_ite (b : UInt8) : vC4 b = (if b < 0x20 then BitVec.ofNat 1 1 else BitVec.ofNat 1 0) := by
  rw [vC4_eq]
  by_cases h : b < 0x20 <;> simp [h]

theorem vLge_ite (b : UInt8) : vLge b = (if 194 ≤ b then BitVec.ofNat 1 1 else BitVec.ofNat 1 0) := by
  have h : vLge b = BitVec.ofBool (decide (194 ≤ (vByte b).toNat)) := rfl
  rw [h, vByte_toNat, bit_ite_of]
  by_cases hb : 194 ≤ b
  · rw [if_pos (show 194 ≤ b.toNat from by rw [UInt8.le_iff_toNat_le] at hb; simpa using hb),
      if_pos hb]
  · rw [if_neg (show ¬ (194 ≤ b.toNat) from by
      rw [UInt8.le_iff_toNat_le] at hb; simpa using hb), if_neg hb]

theorem vLle_ite (b : UInt8) : vLle b = (if b ≤ 244 then BitVec.ofNat 1 1 else BitVec.ofNat 1 0) := by
  have h : vLle b = BitVec.ofBool (decide ((vByte b).toNat ≤ 244)) := rfl
  rw [h, vByte_toNat, bit_ite_of]
  by_cases hb : b ≤ 244
  · rw [if_pos (show b.toNat ≤ 244 from by rw [UInt8.le_iff_toNat_le] at hb; simpa using hb),
      if_pos hb]
  · rw [if_neg (show ¬ (b.toNat ≤ 244) from by
      rw [UInt8.le_iff_toNat_le] at hb; simpa using hb), if_neg hb]

theorem vIlo_ite (b : UInt8) (lo : BitVec 32) : vIlo b lo = (if byteOf lo ≤ b then 1 else 0) := by
  have h : vIlo b lo = BitVec.ofBool (decide ((vLov lo).toNat ≤ (vB32 b).toNat)) := rfl
  rw [h, vB32_toNat, vLov_toNat, bit_ite_of]
  by_cases hb : byteOf lo ≤ b
  · have h1 : lo.toNat % 256 ≤ b.toNat := by
      rw [UInt8.le_iff_toNat_le, byteOf_toNat] at hb
      exact hb
    rw [if_pos h1, if_pos hb]
    decide
  · have h1 : ¬ (lo.toNat % 256 ≤ b.toNat) := by
      rw [UInt8.le_iff_toNat_le, byteOf_toNat] at hb
      exact hb
    rw [if_neg h1, if_neg hb]
    decide

theorem vIhi_ite (b : UInt8) (hi : BitVec 32) : vIhi b hi = (if b ≤ byteOf hi then 1 else 0) := by
  have h : vIhi b hi = BitVec.ofBool (decide ((vB32 b).toNat ≤ (vHiv hi).toNat)) := rfl
  rw [h, vB32_toNat, vHiv_toNat, bit_ite_of]
  by_cases hb : b ≤ byteOf hi
  · have h1 : b.toNat ≤ hi.toNat % 256 := by
      rw [UInt8.le_iff_toNat_le, byteOf_toNat] at hb
      exact hb
    rw [if_pos h1, if_pos hb]
    decide
  · have h1 : ¬ (b.toNat ≤ hi.toNat % 256) := by
      rw [UInt8.le_iff_toNat_le, byteOf_toNat] at hb
      exact hb
    rw [if_neg h1, if_neg hb]
    decide


@[simp] theorem getLsbD_two_zero : (BitVec.ofNat 32 2).getLsbD 0 = false := by decide
@[simp] theorem getLsbD_two_one : (BitVec.ofNat 32 2).getLsbD 1 = true := by decide
@[simp] theorem getLsbD_one_zero : (BitVec.ofNat 32 1).getLsbD 0 = true := by decide
@[simp] theorem getLsbD_one_one : (BitVec.ofNat 32 1).getLsbD 1 = false := by decide
@[simp] theorem getLsbD_if_prop {w : Nat} (p : Prop) [Decidable p] (x y : BitVec w) (i : Nat) :
    (if p then x else y).getLsbD i = if p then x.getLsbD i else y.getLsbD i := by
  by_cases h : p <;> simp [h]

theorem IsQuoteB_eq (b : UInt8) : IsQuoteB b = true ↔ b = 0x22 := by
  unfold IsQuoteB
  by_cases h : b = 0x22 <;> simp [h]

theorem IsBackslashB_eq (b : UInt8) : IsBackslashB b = true ↔ b = 0x5C := by
  unfold IsBackslashB
  by_cases h : b = 0x5C <;> simp [h]

theorem vFout_of_act (b : UInt8) (f nw lo hi stp : BitVec 32) (qb sb cb : BitVec 1)
    (hact : vAct stp b f nw qb sb cb = 1) :
    vFout stp b f nw lo hi qb sb cb = vF3 f nw qb sb := by
  rw [vFout, if_pos hact]

theorem vCout_of_act (b : UInt8) (f nw lo hi stp : BitVec 32) (qb sb cb : BitVec 1)
    (hact : vAct stp b f nw qb sb cb = 1) :
    vCout stp b f nw lo hi qb sb cb = vCw1 b f nw lo hi qb sb cb := by
  rw [vCout, if_pos hact]

theorem vLout_of_act (b : UInt8) (f nw lo hi stp : BitVec 32) (qb sb cb : BitVec 1)
    (hact : vAct stp b f nw qb sb cb = 1) :
    vLout stp b f nw lo hi qb sb cb = vLw1 b f nw lo hi qb sb cb := by
  rw [vLout, if_pos hact]

theorem vHout_of_act (b : UInt8) (f nw lo hi stp : BitVec 32) (qb sb cb : BitVec 1)
    (hact : vAct stp b f nw qb sb cb = 1) :
    vHout stp b f nw lo hi qb sb cb = vHw1 b f nw lo hi qb sb cb := by
  rw [vHout, if_pos hact]


macro "lane_simp" hs:( Lean.Parser.Tactic.simpLemma ),* : tactic =>
  `(tactic| simp [vB64, vBt, vG64, vG128, vT0, vT1, vSh, vSb1, vStb, vMaskNext,
     vLov, vHiv, vB32, vIrg, vNirg, vUok, vUbad, vNod, vNodd, vNpm, vAq, vAqo, vAqc, vNinn,
     vNq, vNpq, vAbs, vAbsin, vNbs, vNpb, vIb, vNcb, vActl, vLeadb, vNasc, vLead,
     vLok, vNlok, vLbad, vLset, vSk0, vSk1, vSk2, vSk3, vSk4, vSkip,
     vB3, vB2, vN3v, vNc, vE0, vF0, vLc0, vLc, vQ1b, vQ2b, vHc0, vHc,
     vLane1, vWcl, vWct, vWbd, vBad8, vSw0, vSw1, vSw2, vRas, vRas2, vRaise,
     vStp0, vStpn, vNact, vNw0, vFc0, vF1, vFq1, vF2, vFb1, vF3, vCw0, vCw1,
     vLw0, vLw1, vHw0, vHw1,
     vMre_ite, vNmre_ite, vInn_ite, vOdd_ite, vLive_ite, vAsc_ite, vQ4_ite, vS4_ite,
     vC4_ite, vLge_ite, vLle_ite, vIlo_ite, vIhi_ite,
     ite_one_eq_one, ite_one_eq_zero, bit_ite_and_ite, bit_ite_xor_one,
     bit_one_and, bit_and_one_r, bit_zero_and, bit_and_zero_r,
     BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_xor, $hs,*])

set_option maxHeartbeats 8000000 in
/-- **The bridge, on the pending-requirement arm.**  While a UTF-8 requirement
is outstanding the rule's four words decode to the state `bodyStep` steps the
carry to when the byte continues the requirement, and to the carry again when it
does not.  This is the arm the lane reaches with `nw ≠ 0`; the no-requirement
arm's nine branches are not proved here. -/
theorem ruleBridge_pending (b : UInt8) (f nw lo hi stp : BitVec 32) (qb sb cb : BitVec 1)
    (hqb : qb = (if IsQuoteB b then BitVec.ofNat 1 1 else BitVec.ofNat 1 0))
    (hsb : sb = (if IsBackslashB b then BitVec.ofNat 1 1 else BitVec.ofNat 1 0))
    (hcb : cb = (if b < 0x20 then BitVec.ofNat 1 1 else BitVec.ofNat 1 0))
    (hstp : stp = 0) (hskip : vSkip b f nw qb sb cb = BitVec.ofNat 1 0)
    (hnw : nw.toNat ≠ 0) :
    decodeState ⟨vFout stp b f nw lo hi qb sb cb, vCout stp b f nw lo hi qb sb cb,
                 vLout stp b f nw lo hi qb sb cb, vHout stp b f nw lo hi qb sb cb⟩ =
      (match bodyStep (decodeState ⟨f, nw, lo, hi⟩) b with
       | .cont st' => st'
       | .closed => decodeState ⟨f, nw, lo, hi⟩
       | .refused _ => decodeState ⟨f, nw, lo, hi⟩) := by
  have hlive : vLive stp = 1 := by
    rw [vLive_ite, if_pos hstp]; decide
  have hnact : vNact b f nw qb sb cb = 1 := by
    rw [vNact, hskip]; decide
  have hact : vAct stp b f nw qb sb cb = 1 := by
    rw [vAct, hlive, hnact]; decide
  rw [vFout_of_act _ _ _ _ _ _ _ _ _ hact, vCout_of_act _ _ _ _ _ _ _ _ _ hact,
    vLout_of_act _ _ _ _ _ _ _ _ _ hact, vHout_of_act _ _ _ _ _ _ _ _ _ hact]
  have hdec : decodeState ⟨f, nw, lo, hi⟩ = ⟨f.getLsbD 0, f.getLsbD 1,
      (if nw.toNat = 0 then Utf8Need.none
       else Utf8Need.more nw.toNat (byteOf lo) (byteOf hi))⟩ := rfl
  rw [hdec, if_neg hnw]
  by_cases hin : byteOf lo ≤ b ∧ b ≤ byteOf hi
  · have hstep : bodyStep ⟨f.getLsbD 0, f.getLsbD 1,
        Utf8Need.more nw.toNat (byteOf lo) (byteOf hi)⟩ b =
        .cont ⟨f.getLsbD 0, f.getLsbD 1,
          (if nw.toNat ≤ 1 then Utf8Need.none
           else Utf8Need.more (nw.toNat - 1) 0x80 0xBF)⟩ := by
      have hne : Utf8Need.more nw.toNat (byteOf lo) (byteOf hi) ≠ Utf8Need.none := by simp
      simp only [bodyStep, Utf8Need.step, if_pos hne, if_pos hin]
    rw [hstep]
    have hnw0 : nw ≠ BitVec.ofNat 32 0 := fun h => hnw (by rw [h]; rfl)
    lane_simp hnw, hnw0, hin
    exact decodeState_count f nw hnw0
  · have hstep : bodyStep ⟨f.getLsbD 0, f.getLsbD 1,
        Utf8Need.more nw.toNat (byteOf lo) (byteOf hi)⟩ b = .refused .badUtf8 := by
      have hne : Utf8Need.more nw.toNat (byteOf lo) (byteOf hi) ≠ Utf8Need.none := by simp
      simp only [bodyStep, Utf8Need.step, if_pos hne, if_neg hin]
    rw [hstep]
    have hnw0 : nw ≠ BitVec.ofNat 32 0 := fun h => hnw (by rw [h]; rfl)
    lane_simp hnw, hnw0, hin
    rw [decodeState_trunc, hdec, if_neg hnw]
    rfl

/-! ### The no-requirement arm

`bodyStep` with no requirement outstanding is a tree of nine branches, and the
rule's four words run the same tree: the run parity, the quote on each side of a
body, the backslash, the control byte, the content lane, the lead byte's classes,
the refusal of a byte no character starts with, and the lane outside a body.
Each branch is a leaf below, proved by the same computation as
`ruleBridge_pending`: every predicate restated as an `if` on the proposition it
tests, the one-bit `&&&`/`^^^` folded to that proposition, and `getLsbD` pushed
through each `select` chain with `getLsbD_if_prop` — which `simp` does not consume
even when passed explicitly, so the leaves rewrite with it before closing.

Two facts shape the tree.  `bodyStep`'s control test is a `Bool` conjunction, so
the condition a leaf discharges is `(st.inside && decide (b < 0x20)) = true` and
not `st.inside = true ∧ b < 0x20`.  And a lane the rule skips is a content lane:
`skip_facts` reads the six facts out of the skip bit, `skip_one` puts them back,
and together they make `ruleBridge_no_content` the only arm a skipped lane
reaches.

`ruleBridge_no` dispatches on the model's own order and `ruleBridge` adds the
pending arm to it, so the rule's four words decode to the state `bodyStep` steps
the carry to on every byte and every carry.  What the lane step still needs above
this is the mask accumulator's word, the stop word and the counter, none of which
is part of the carry. -/

/-- The lead byte's count word is one, two or three, so it is never zero and
`decodeState` reads a requirement out of it rather than `.none`. -/
theorem vNc_toNat_ne_zero (b : UInt8) : (vNc b).toNat ≠ 0 := by
  unfold vNc vN3v
  repeat (first | split | decide)

/-- A one-bit value xor-ed with one is one exactly when the value is zero. -/
theorem xor_one_eq_one {x : BitVec 1} : (x ^^^ (1 : BitVec 1)) = 1 ↔ x = 0 := by
  rcases LeanLLVM.Refinement.BlockEval.bitVec1_eq_zero_or_one x with h | h <;>
    rw [h] <;> decide

/-- A `Bool` that is not true is false. -/
theorem bool_false_of_not {x : Bool} (h : ¬ x = true) : x = false := by
  cases x <;> simp_all

/-- The carry a slot holds when its count word is zero: the two flag bits and no
requirement.  `decodeState` of the four words the rule read is this, which is the
form the no-requirement arm's leaves conclude. -/
abbrev carryForm (f : BitVec 32) : BodyState := ⟨f.getLsbD 0, f.getLsbD 1, Utf8Need.none⟩

/-- The rule's gate is open on a live stop word and a lane it does not skip. -/
theorem vAct_eq_one (b : UInt8) (f nw : BitVec 32) (stp : BitVec 32) (qb sb cb : BitVec 1)
    (hstp : stp = 0) (hskip : vSkip b f nw qb sb cb = 0) :
    vAct stp b f nw qb sb cb = 1 := by
  rw [vAct, vLive_ite, if_pos hstp, vNact, hskip]
  decide

/-- A byte that is not below `0x80` is at least `0x80`. -/
theorem ge_of_not_lt {b : UInt8} (h : ¬ b < 0x80) : 0x80 ≤ b := by
  have h128 : (0x80 : UInt8).toNat = 128 := by decide
  have h' : ¬ b.toNat < 128 := by
    rw [UInt8.lt_iff_toNat_lt, h128] at h
    exact h
  rw [UInt8.le_iff_toNat_le, h128]
  omega

set_option maxHeartbeats 4000000 in
/-- **The run parity leaf.**  An odd run makes the byte escaped content: the rule
clears the run bit in the flags word and leaves the requirement's count and bounds
as it read them, which is `{ st with oddRun := false }`. -/
theorem ruleBridge_no_parity (b : UInt8) (f nw lo hi stp : BitVec 32) (qb sb cb : BitVec 1)
    (hnw : nw = 0) (hodd : f.getLsbD 1 = true)
    (hact : vAct stp b f nw qb sb cb = 1) :
    decodeState ⟨vFout stp b f nw lo hi qb sb cb, vCout stp b f nw lo hi qb sb cb,
                 vLout stp b f nw lo hi qb sb cb, vHout stp b f nw lo hi qb sb cb⟩ =
      (⟨f.getLsbD 0, false, Utf8Need.none⟩ : BodyState) := by
  rw [vFout_of_act _ _ _ _ _ _ _ _ _ hact, vCout_of_act _ _ _ _ _ _ _ _ _ hact,
    vLout_of_act _ _ _ _ _ _ _ _ _ hact, vHout_of_act _ _ _ _ _ _ _ _ _ hact]
  lane_simp hnw, hodd
  simp [decodeState]
  all_goals (try (repeat rw [getLsbD_if_prop]); simp_all; try decide)

set_option maxHeartbeats 4000000 in
/-- **The quote leaf, closing.**  Inside a body with no run and no requirement a
quote closes the string: the rule leaves the carry alone and `bodyStep` reports
`.closed`, which the statement records as the carry again. -/
theorem ruleBridge_no_quote_close (b : UInt8) (f nw lo hi stp : BitVec 32)
    (qb sb cb : BitVec 1) (hnw : nw = 0)
    (hqb : qb = (if IsQuoteB b then BitVec.ofNat 1 1 else BitVec.ofNat 1 0))
    (hq : IsQuoteB b = true) (hin : f.getLsbD 0 = true) (hnodd : f.getLsbD 1 = false)
    (hact : vAct stp b f nw qb sb cb = 1) :
    decodeState ⟨vFout stp b f nw lo hi qb sb cb, vCout stp b f nw lo hi qb sb cb,
                 vLout stp b f nw lo hi qb sb cb, vHout stp b f nw lo hi qb sb cb⟩ =
      carryForm f := by
  rw [vFout_of_act _ _ _ _ _ _ _ _ _ hact, vCout_of_act _ _ _ _ _ _ _ _ _ hact,
    vLout_of_act _ _ _ _ _ _ _ _ _ hact, vHout_of_act _ _ _ _ _ _ _ _ _ hact]
  lane_simp hnw, hqb, hq, hin, hnodd
  simp [decodeState]
  all_goals (try (repeat rw [getLsbD_if_prop]); simp_all; try decide)

set_option maxHeartbeats 4000000 in
/-- **The quote leaf, opening.**  Outside a body the same byte opens one: the rule
sets the body flag, clears the run bit and leaves the count and bounds, which is
`{ st with inside := true, oddRun := false }`. -/
theorem ruleBridge_no_quote_open (b : UInt8) (f nw lo hi stp : BitVec 32)
    (qb sb cb : BitVec 1) (hnw : nw = 0)
    (hqb : qb = (if IsQuoteB b then BitVec.ofNat 1 1 else BitVec.ofNat 1 0))
    (hq : IsQuoteB b = true) (hin : f.getLsbD 0 = false) (hnodd : f.getLsbD 1 = false)
    (hact : vAct stp b f nw qb sb cb = 1) :
    decodeState ⟨vFout stp b f nw lo hi qb sb cb, vCout stp b f nw lo hi qb sb cb,
                 vLout stp b f nw lo hi qb sb cb, vHout stp b f nw lo hi qb sb cb⟩ =
      (⟨true, false, Utf8Need.none⟩ : BodyState) := by
  rw [vFout_of_act _ _ _ _ _ _ _ _ _ hact, vCout_of_act _ _ _ _ _ _ _ _ _ hact,
    vLout_of_act _ _ _ _ _ _ _ _ _ hact, vHout_of_act _ _ _ _ _ _ _ _ _ hact]
  lane_simp hnw, hqb, hq, hin, hnodd
  simp [decodeState]
  all_goals (try (repeat rw [getLsbD_if_prop]); simp_all; try decide)

set_option maxHeartbeats 4000000 in
/-- **The backslash leaf.**  A backslash starts a run in a body and escapes nothing
outside one, so the rule sets the run bit to the body flag; the count and bounds
are the read ones. -/
theorem ruleBridge_no_backslash (b : UInt8) (f nw lo hi stp : BitVec 32)
    (qb sb cb : BitVec 1) (hnw : nw = 0)
    (hqb : qb = (if IsQuoteB b then BitVec.ofNat 1 1 else BitVec.ofNat 1 0))
    (hsb : sb = (if IsBackslashB b then BitVec.ofNat 1 1 else BitVec.ofNat 1 0))
    (hnq : IsQuoteB b = false) (hbs : IsBackslashB b = true)
    (hnodd : f.getLsbD 1 = false)
    (hact : vAct stp b f nw qb sb cb = 1) :
    decodeState ⟨vFout stp b f nw lo hi qb sb cb, vCout stp b f nw lo hi qb sb cb,
                 vLout stp b f nw lo hi qb sb cb, vHout stp b f nw lo hi qb sb cb⟩ =
      (⟨f.getLsbD 0, f.getLsbD 0, Utf8Need.none⟩ : BodyState) := by
  rw [vFout_of_act _ _ _ _ _ _ _ _ _ hact, vCout_of_act _ _ _ _ _ _ _ _ _ hact,
    vLout_of_act _ _ _ _ _ _ _ _ _ hact, vHout_of_act _ _ _ _ _ _ _ _ _ hact]
  by_cases hin : f.getLsbD 0 = true
  · lane_simp hnw, hqb, hsb, hnq, hbs, hnodd, hin
    simp [decodeState]
    all_goals (try (repeat rw [getLsbD_if_prop]); simp_all; try decide)
  · lane_simp hnw, hqb, hsb, hnq, hbs, hnodd, hin
    simp [decodeState]
    all_goals (try (repeat rw [getLsbD_if_prop]); simp_all; try decide)

set_option maxHeartbeats 4000000 in
/-- **The control leaf.**  A byte below `0x20` inside a body is refused as a control
byte: the rule leaves the carry alone and `bodyStep` reports `.refused .control`,
which the statement records as the carry again. -/
theorem ruleBridge_no_control (b : UInt8) (f nw lo hi stp : BitVec 32)
    (qb sb cb : BitVec 1) (hnw : nw = 0)
    (hqb : qb = (if IsQuoteB b then BitVec.ofNat 1 1 else BitVec.ofNat 1 0))
    (hsb : sb = (if IsBackslashB b then BitVec.ofNat 1 1 else BitVec.ofNat 1 0))
    (hcb : cb = (if b < 0x20 then BitVec.ofNat 1 1 else BitVec.ofNat 1 0))
    (hnq : IsQuoteB b = false) (hbs : IsBackslashB b = false)
    (hin : f.getLsbD 0 = true) (hnodd : f.getLsbD 1 = false) (hctrl : b < 0x20)
    (hact : vAct stp b f nw qb sb cb = 1) :
    decodeState ⟨vFout stp b f nw lo hi qb sb cb, vCout stp b f nw lo hi qb sb cb,
                 vLout stp b f nw lo hi qb sb cb, vHout stp b f nw lo hi qb sb cb⟩ =
      carryForm f := by
  rw [vFout_of_act _ _ _ _ _ _ _ _ _ hact, vCout_of_act _ _ _ _ _ _ _ _ _ hact,
    vLout_of_act _ _ _ _ _ _ _ _ _ hact, vHout_of_act _ _ _ _ _ _ _ _ _ hact]
  lane_simp hnw, hqb, hsb, hcb, hnq, hbs, hin, hnodd, hctrl
  simp [decodeState]
  all_goals (try (repeat rw [getLsbD_if_prop]); simp_all; try decide)

set_option maxHeartbeats 4000000 in
/-- **The content leaf.**  A lane the rule skips changes nothing: when `vAct` is
zero the four words are the four it read, so the slot decodes to the carry it
started from. -/
theorem ruleBridge_no_content (b : UInt8) (f nw lo hi stp : BitVec 32)
    (qb sb cb : BitVec 1) (hnact : vAct stp b f nw qb sb cb = 0) :
    decodeState ⟨vFout stp b f nw lo hi qb sb cb, vCout stp b f nw lo hi qb sb cb,
                 vLout stp b f nw lo hi qb sb cb, vHout stp b f nw lo hi qb sb cb⟩ =
      decodeState ⟨f, nw, lo, hi⟩ := by
  have h1 : ¬ (vAct stp b f nw qb sb cb = 1) := by rw [hnact]; decide
  simp only [vFout, vCout, vLout, vHout, ite_eq_right h1]

set_option maxHeartbeats 4000000 in
/-- **The lead leaf.**  A byte in `[0xC2, 0xF4]` starts a sequence: the rule's count
and bound selects are the model's own nine classes, so the slot holds the
requirement `Utf8Need.step` produces.  `leadClass_agrees` is the class bridge, and
`decodeState_of_count` reads the three words back. -/
theorem ruleBridge_no_lead (b : UInt8) (f nw lo hi stp : BitVec 32)
    (qb sb cb : BitVec 1) (hnw : nw = 0)
    (hqb : qb = (if IsQuoteB b then BitVec.ofNat 1 1 else BitVec.ofNat 1 0))
    (hsb : sb = (if IsBackslashB b then BitVec.ofNat 1 1 else BitVec.ofNat 1 0))
    (hcb : cb = (if b < 0x20 then BitVec.ofNat 1 1 else BitVec.ofNat 1 0))
    (hnq : IsQuoteB b = false) (hbs : IsBackslashB b = false)
    (hin : f.getLsbD 0 = true) (hnodd : f.getLsbD 1 = false)
    (hasc : 0x80 ≤ b) (hlo : 194 ≤ b) (hhi : b ≤ 244) (hctrl : ¬ b < 0x20)
    (hact : vAct stp b f nw qb sb cb = 1) :
    decodeState ⟨vFout stp b f nw lo hi qb sb cb, vCout stp b f nw lo hi qb sb cb,
                 vLout stp b f nw lo hi qb sb cb, vHout stp b f nw lo hi qb sb cb⟩ =
      (⟨true, false,
        Utf8Need.more (vNc b).toNat (byteOf (vLc b)) (byteOf (vHc b))⟩ : BodyState) := by
  rw [vFout_of_act _ _ _ _ _ _ _ _ _ hact, vCout_of_act _ _ _ _ _ _ _ _ _ hact,
    vLout_of_act _ _ _ _ _ _ _ _ _ hact, vHout_of_act _ _ _ _ _ _ _ _ _ hact]
  lane_simp hnw, hqb, hsb, hcb, hnq, hbs, hin, hnodd, hasc, hlo, hhi, hctrl
  simp_all
  change decodeState ⟨f, vNc b, vLc b, vHc b⟩ =
    (⟨true, false,
      Utf8Need.more (vNc b).toNat (byteOf (vLc b)) (byteOf (vHc b))⟩ : BodyState)
  have h1 : decodeState ⟨f, vNc b, vLc b, vHc b⟩ =
      (⟨f.getLsbD 0, f.getLsbD 1,
        Utf8Need.more (vNc b).toNat (byteOf (vLc b)) (byteOf (vHc b))⟩ : BodyState) :=
    decodeState_of_count f (vNc b) (vLc b) (vHc b) (vNc b).toNat
      (byteOf (vLc b)) (byteOf (vHc b)) rfl (vNc_toNat_ne_zero b) rfl rfl
  rw [h1]
  simp_all

set_option maxHeartbeats 4000000 in
/-- **The bad-lead leaf.**  A byte at or above `0x80` outside `[0xC2, 0xF4]` starts no
sequence: `Utf8Need.step` rejects it, the rule freezes the carry, and the statement
records the refusal as the carry again. -/
theorem ruleBridge_no_badlead (b : UInt8) (f nw lo hi stp : BitVec 32)
    (qb sb cb : BitVec 1) (hnw : nw = 0)
    (hqb : qb = (if IsQuoteB b then BitVec.ofNat 1 1 else BitVec.ofNat 1 0))
    (hsb : sb = (if IsBackslashB b then BitVec.ofNat 1 1 else BitVec.ofNat 1 0))
    (hcb : cb = (if b < 0x20 then BitVec.ofNat 1 1 else BitVec.ofNat 1 0))
    (hnq : IsQuoteB b = false) (hbs : IsBackslashB b = false)
    (hin : f.getLsbD 0 = true) (hnodd : f.getLsbD 1 = false)
    (hasc : 0x80 ≤ b) (hout : ¬ (194 ≤ b ∧ b ≤ 244)) (hctrl : ¬ b < 0x20)
    (hact : vAct stp b f nw qb sb cb = 1) :
    decodeState ⟨vFout stp b f nw lo hi qb sb cb, vCout stp b f nw lo hi qb sb cb,
                 vLout stp b f nw lo hi qb sb cb, vHout stp b f nw lo hi qb sb cb⟩ =
      carryForm f := by
  rw [vFout_of_act _ _ _ _ _ _ _ _ _ hact, vCout_of_act _ _ _ _ _ _ _ _ _ hact,
    vLout_of_act _ _ _ _ _ _ _ _ _ hact, vHout_of_act _ _ _ _ _ _ _ _ _ hact]
  lane_simp hnw, hqb, hsb, hcb, hnq, hbs, hin, hnodd, hasc, hout, hctrl
  simp [decodeState]
  all_goals (try (repeat rw [getLsbD_if_prop]); simp_all; try decide)

set_option maxHeartbeats 4000000 in
/-- **The outside leaf.**  With no body open and no run to clear, every gate of the
rule is closed and the four words are the ones it read, so the slot holds the
carry `bodyStep` leaves unchanged. -/
theorem ruleBridge_no_outside (b : UInt8) (f nw lo hi stp : BitVec 32)
    (qb sb cb : BitVec 1) (hnw : nw = 0)
    (hqb : qb = (if IsQuoteB b then BitVec.ofNat 1 1 else BitVec.ofNat 1 0))
    (hsb : sb = (if IsBackslashB b then BitVec.ofNat 1 1 else BitVec.ofNat 1 0))
    (hnq : IsQuoteB b = false) (hbs : IsBackslashB b = false)
    (hin : f.getLsbD 0 = false) (hnodd : f.getLsbD 1 = false)
    (hact : vAct stp b f nw qb sb cb = 1) :
    decodeState ⟨vFout stp b f nw lo hi qb sb cb, vCout stp b f nw lo hi qb sb cb,
                 vLout stp b f nw lo hi qb sb cb, vHout stp b f nw lo hi qb sb cb⟩ =
      carryForm f := by
  rw [vFout_of_act _ _ _ _ _ _ _ _ _ hact, vCout_of_act _ _ _ _ _ _ _ _ _ hact,
    vLout_of_act _ _ _ _ _ _ _ _ _ hact, vHout_of_act _ _ _ _ _ _ _ _ _ hact]
  lane_simp hnw, hqb, hsb, hnq, hbs, hin, hnodd
  simp [decodeState]
  all_goals (try (repeat rw [getLsbD_if_prop]); simp_all; try decide)

/-- **What a skipped lane implies.**  When the rule's skip bit is set the lane is a
content lane: inside, no run, no requirement, none of the three byte predicates,
and a byte below `0x80`.  Each fact is read through the predicate's own equation,
and the six-way conjunction is the `&&&` chain unrolled. -/
theorem skip_facts {b : UInt8} {f nw : BitVec 32} {qb sb cb : BitVec 1}
    (hqb : qb = (if IsQuoteB b then BitVec.ofNat 1 1 else BitVec.ofNat 1 0))
    (hsb : sb = (if IsBackslashB b then BitVec.ofNat 1 1 else BitVec.ofNat 1 0))
    (hcb : cb = (if b < 0x20 then BitVec.ofNat 1 1 else BitVec.ofNat 1 0))
    (hskip : vSkip b f nw qb sb cb = 1) :
    f.getLsbD 0 = true ∧ f.getLsbD 1 = false ∧ nw = 0 ∧
      IsQuoteB b = false ∧ IsBackslashB b = false ∧ ¬ b < 0x20 ∧ b < 0x80 := by
  have h4 : vSk4 f nw qb sb cb = 1 := ((bit_and_one _ _).mp hskip).1
  have hasc : vAsc b = 1 := ((bit_and_one _ _).mp hskip).2
  have h3 : vSk3 f nw qb sb = 1 := ((bit_and_one _ _).mp h4).1
  have hncb : vNcb cb = 1 := ((bit_and_one _ _).mp h4).2
  have h2 : vSk2 f nw qb = 1 := ((bit_and_one _ _).mp h3).1
  have hnbs : vNbs sb = 1 := ((bit_and_one _ _).mp h3).2
  have h1 : vSk1 f nw = 1 := ((bit_and_one _ _).mp h2).1
  have hnq : vNq qb = 1 := ((bit_and_one _ _).mp h2).2
  have h0 : vSk0 f = 1 := ((bit_and_one _ _).mp h1).1
  have hnmre : vNmre nw = 1 := ((bit_and_one _ _).mp h1).2
  have hinn : vInn f = 1 := ((bit_and_one _ _).mp h0).1
  have hnodd : vNodd f = 1 := ((bit_and_one _ _).mp h0).2
  have hodd0 : vOdd f = 0 := xor_one_eq_one.mp hnodd
  have hq0 : qb = 0 := xor_one_eq_one.mp hnq
  have hs0 : sb = 0 := xor_one_eq_one.mp hnbs
  have hc0 : cb = 0 := xor_one_eq_one.mp hncb
  have hinside : f.getLsbD 0 = true := (vInn_eq f).mp hinn
  have hodd : f.getLsbD 1 = false := by
    have hne : ¬ f.getLsbD 1 = true := fun h => by
      rw [← vOdd_eq f] at h
      rw [hodd0] at h
      exact absurd h (by decide)
    exact bool_false_of_not hne
  have hnw : nw = 0 := (vNmre_eq nw).mp hnmre
  have hquote : IsQuoteB b = false := by
    have h0' : (if IsQuoteB b then BitVec.ofNat 1 1 else BitVec.ofNat 1 0) = 0 := by
      rw [← hqb, hq0]
    exact (bit_ite_zero _).mp h0'
  have hback : IsBackslashB b = false := by
    have h0' : (if IsBackslashB b then BitVec.ofNat 1 1 else BitVec.ofNat 1 0) = 0 := by
      rw [← hsb, hs0]
    exact (bit_ite_zero _).mp h0'
  have hctrl : ¬ b < 0x20 := by
    have h0' : (if b < 0x20 then BitVec.ofNat 1 1 else BitVec.ofNat 1 0) = 0 := by
      rw [← hcb, hc0]
    exact (ite_one_eq_zero _).mp h0'
  have hlt : b < 0x80 := (vAsc_eq b).mp hasc
  exact ⟨hinside, hodd, hnw, hquote, hback, hctrl, hlt⟩

/-- **A content lane is skipped.**  The converse of `skip_facts`: the six facts a
content lane has set the rule's skip bit, which is what makes the content leaf the
only arm a skipped lane reaches. -/
theorem skip_one {b : UInt8} {f nw : BitVec 32} {qb sb cb : BitVec 1}
    (hqb : qb = (if IsQuoteB b then BitVec.ofNat 1 1 else BitVec.ofNat 1 0))
    (hsb : sb = (if IsBackslashB b then BitVec.ofNat 1 1 else BitVec.ofNat 1 0))
    (hcb : cb = (if b < 0x20 then BitVec.ofNat 1 1 else BitVec.ofNat 1 0))
    (hin : f.getLsbD 0 = true) (hnodd : f.getLsbD 1 = false) (hnw : nw = 0)
    (hnq : IsQuoteB b = false) (hnbs : IsBackslashB b = false) (hnc : ¬ b < 0x20)
    (hlt : b < 0x80) : vSkip b f nw qb sb cb = 1 := by
  have hinn : vInn f = 1 := (vInn_eq f).mpr hin
  have hodd0 : vOdd f = 0 := by
    rcases LeanLLVM.Refinement.BlockEval.bitVec1_eq_zero_or_one (vOdd f) with h | h
    · exact h
    · exact absurd ((vOdd_eq f).mp h) (by simpa using hnodd)
  have hnodd' : vNodd f = 1 := (xor_one_eq_one (x := vOdd f)).mpr hodd0
  have hnmre : vNmre nw = 1 := (vNmre_eq nw).mpr hnw
  have hq : vNq qb = 1 := by
    rw [vNq, hqb, hnq]
    decide
  have hbs : vNbs sb = 1 := by
    rw [vNbs, hsb, hnbs]
    decide
  have hcb1 : vNcb cb = 1 := by
    rw [vNcb, hcb]
    rw [if_neg hnc]
    decide
  have hasc : vAsc b = 1 := (vAsc_eq b).mpr hlt
  have h0 : vSk0 f = 1 := (bit_and_one _ _).mpr ⟨hinn, hnodd'⟩
  have h1 : vSk1 f nw = 1 := (bit_and_one _ _).mpr ⟨h0, hnmre⟩
  have h2 : vSk2 f nw qb = 1 := (bit_and_one _ _).mpr ⟨h1, hq⟩
  have h3 : vSk3 f nw qb sb = 1 := (bit_and_one _ _).mpr ⟨h2, hbs⟩
  have h4 : vSk4 f nw qb sb cb = 1 := (bit_and_one _ _).mpr ⟨h3, hcb1⟩
  exact (bit_and_one _ _).mpr ⟨h4, hasc⟩

set_option maxHeartbeats 8000000 in
/-- **The bridge, on the no-requirement arm.**  With the count word zero the rule's
four words decode to the state `bodyStep` steps the carry to: the run parity, the
quote's two sides, the backslash, the control byte, the content lane, the lead
byte's classes, its refusal and the outside lane.  The tree is the model's own
order, each arm is one of the nine leaves above, and a skipped lane is
`ruleBridge_no_content` with the content lane's facts supplied by `skip_facts`. -/
theorem ruleBridge_no (b : UInt8) (f nw lo hi stp : BitVec 32) (qb sb cb : BitVec 1)
    (hqb : qb = (if IsQuoteB b then BitVec.ofNat 1 1 else BitVec.ofNat 1 0))
    (hsb : sb = (if IsBackslashB b then BitVec.ofNat 1 1 else BitVec.ofNat 1 0))
    (hcb : cb = (if b < 0x20 then BitVec.ofNat 1 1 else BitVec.ofNat 1 0))
    (hstp : stp = 0) (hnw : nw = 0) :
    decodeState ⟨vFout stp b f nw lo hi qb sb cb, vCout stp b f nw lo hi qb sb cb,
                 vLout stp b f nw lo hi qb sb cb, vHout stp b f nw lo hi qb sb cb⟩ =
      (match bodyStep (decodeState ⟨f, nw, lo, hi⟩) b with
       | .cont st' => st'
       | .closed => decodeState ⟨f, nw, lo, hi⟩
       | .refused _ => decodeState ⟨f, nw, lo, hi⟩) := by
  have hdec : decodeState ⟨f, nw, lo, hi⟩ = carryForm f := by
    simp [decodeState, carryForm, hnw]
  rw [hdec]
  by_cases hskip : vSkip b f nw qb sb cb = 0
  · have hact : vAct stp b f nw qb sb cb = 1 :=
      vAct_eq_one b f nw stp qb sb cb hstp hskip
    by_cases hodd : f.getLsbD 1 = true
    · have hstep : bodyStep (carryForm f) b =
          .cont ⟨f.getLsbD 0, false, Utf8Need.none⟩ := by
        simp_all [bodyStep, carryForm]
      rw [hstep]
      exact ruleBridge_no_parity b f nw lo hi stp qb sb cb hnw hodd hact
    · have hnodd : f.getLsbD 1 = false := bool_false_of_not hodd
      by_cases hq : IsQuoteB b = true
      · by_cases hin : f.getLsbD 0 = true
        · have hstep : bodyStep (carryForm f) b = .closed := by
            simp_all [bodyStep, carryForm]
          rw [hstep]
          exact ruleBridge_no_quote_close b f nw lo hi stp qb sb cb hnw hqb hq hin hnodd
            hact
        · have hnin : f.getLsbD 0 = false := bool_false_of_not hin
          have hstep : bodyStep (carryForm f) b =
              .cont ⟨true, false, Utf8Need.none⟩ := by
            simp_all [bodyStep, carryForm]
          rw [hstep]
          exact ruleBridge_no_quote_open b f nw lo hi stp qb sb cb hnw hqb hq hnin hnodd
            hact
      · have hnq : IsQuoteB b = false := bool_false_of_not hq
        by_cases hbs : IsBackslashB b = true
        · have hstep : bodyStep (carryForm f) b =
              .cont ⟨f.getLsbD 0, f.getLsbD 0, Utf8Need.none⟩ := by
            simp_all [bodyStep, carryForm]
          rw [hstep]
          exact ruleBridge_no_backslash b f nw lo hi stp qb sb cb hnw hqb hsb hnq hbs
            hnodd hact
        · have hnbs : IsBackslashB b = false := bool_false_of_not hbs
          by_cases hin : f.getLsbD 0 = true
          · by_cases hctrl : b < 0x20
            · have hstep : bodyStep (carryForm f) b = .refused .control := by
                simp_all [bodyStep, carryForm]
              rw [hstep]
              exact ruleBridge_no_control b f nw lo hi stp qb sb cb hnw hqb hsb hcb hnq
                hnbs hin hnodd hctrl hact
            · by_cases hlt : b < 0x80
              · exfalso
                have h1 : vSkip b f nw qb sb cb = 1 :=
                  skip_one hqb hsb hcb hin hnodd hnw hnq hnbs hctrl hlt
                rw [h1] at hskip
                exact absurd hskip (by decide)
              · have hasc : 0x80 ≤ b := ge_of_not_lt hlt
                by_cases hlead : 194 ≤ b ∧ b ≤ 244
                · obtain ⟨hlo', hhi'⟩ := hlead
                  have hstep : bodyStep (carryForm f) b =
                      .cont ⟨true, false,
                        Utf8Need.more (vNc b).toNat (byteOf (vLc b)) (byteOf (vHc b))⟩ := by
                    simp_all [bodyStep, carryForm, leadClass_agrees b hlo' hhi']
                  rw [hstep]
                  exact ruleBridge_no_lead b f nw lo hi stp qb sb cb hnw hqb hsb hcb hnq
                    hnbs hin hnodd hasc hlo' hhi' hctrl hact
                · have hout : ¬ (194 ≤ b ∧ b ≤ 244) := hlead
                  have hstep : bodyStep (carryForm f) b = .refused .badUtf8 := by
                    simp_all [bodyStep, carryForm, noLeadClass_agrees b hasc hout]
                  rw [hstep]
                  exact ruleBridge_no_badlead b f nw lo hi stp qb sb cb hnw hqb hsb hcb hnq
                    hnbs hin hnodd hasc hlead hctrl hact
          · have hnin : f.getLsbD 0 = false := bool_false_of_not hin
            have hstep : bodyStep (carryForm f) b = .cont (carryForm f) := by
              simp_all [bodyStep, carryForm]
            rw [hstep]
            exact ruleBridge_no_outside b f nw lo hi stp qb sb cb hnw hqb hsb hnq hnbs
              hnin hnodd hact
  · have hskip1 : vSkip b f nw qb sb cb = 1 := by
      rcases LeanLLVM.Refinement.BlockEval.bitVec1_eq_zero_or_one
        (vSkip b f nw qb sb cb) with h | h
      · exact absurd h hskip
      · exact h
    obtain ⟨hin, hnodd, hnw', hnq, hnbs, hctrl, hlt⟩ := skip_facts hqb hsb hcb hskip1
    have hnact : vAct stp b f nw qb sb cb = 0 := by
      rw [vAct, vLive_ite, if_pos hstp, vNact, hskip1]
      decide
    have hstep : bodyStep (carryForm f) b = .cont (carryForm f) := by
      simp_all [bodyStep, carryForm, step_none_ascii b hlt]
    rw [hstep]
    exact (ruleBridge_no_content b f nw lo hi stp qb sb cb hnact).trans hdec

set_option maxHeartbeats 8000000 in
/-- **The bridge.**  The rule's four words decode to the state `bodyStep` steps the
carry to, on both arms: the pending requirement (`ruleBridge_pending`, where a
nonzero count forces the skip bit clear) and the no-requirement arm
(`ruleBridge_no`).  This is the arithmetic the lane step consumes. -/
theorem ruleBridge (b : UInt8) (f nw lo hi stp : BitVec 32) (qb sb cb : BitVec 1)
    (hqb : qb = (if IsQuoteB b then BitVec.ofNat 1 1 else BitVec.ofNat 1 0))
    (hsb : sb = (if IsBackslashB b then BitVec.ofNat 1 1 else BitVec.ofNat 1 0))
    (hcb : cb = (if b < 0x20 then BitVec.ofNat 1 1 else BitVec.ofNat 1 0))
    (hstp : stp = 0) :
    decodeState ⟨vFout stp b f nw lo hi qb sb cb, vCout stp b f nw lo hi qb sb cb,
                 vLout stp b f nw lo hi qb sb cb, vHout stp b f nw lo hi qb sb cb⟩ =
      (match bodyStep (decodeState ⟨f, nw, lo, hi⟩) b with
       | .cont st' => st'
       | .closed => decodeState ⟨f, nw, lo, hi⟩
       | .refused _ => decodeState ⟨f, nw, lo, hi⟩) := by
  by_cases hnw : nw = 0
  · exact ruleBridge_no b f nw lo hi stp qb sb cb hqb hsb hcb hstp hnw
  · have hnwt : nw.toNat ≠ 0 := by
      intro h
      exact hnw (BitVec.toNat_eq.mpr (by simpa using h))
    have hmre : vNmre nw = 0 := by
      rw [vNmre_ite, if_neg hnw]
      decide
    have hsk1 : vSk1 f nw = 0 := by simp [vSk1, hmre]
    have hsk2 : vSk2 f nw qb = 0 := by simp [vSk2, hsk1]
    have hsk3 : vSk3 f nw qb sb = 0 := by simp [vSk3, hsk2]
    have hsk4 : vSk4 f nw qb sb cb = 0 := by simp [vSk4, hsk3]
    have hskip : vSkip b f nw qb sb cb = 0 := by simp [vSkip, hsk4]
    exact ruleBridge_pending b f nw lo hi stp qb sb cb hqb hsb hcb hstp hskip hnwt

end LeanLLVM.Refinement.JsonScanLane
