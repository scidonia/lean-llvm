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

**What is not here.**  `ruleInstrs`'s 120 instructions: the table it opens with
is `structBitCode`, whose answer `structBit_correct` already identifies with
`IsStructOrSpaceB`, but the chain that runs those nine in the body's own
environment — with the mask accumulator, the carry's four words, the stop word
and the counter that follow them — is not derived here.  With it go the
arithmetic bridge (`decodeState` of the four words the rule leaves is `bodyStep`
of the four it read, under the `act` gate; the mask half is `maskStep`), the
`laneStep` lemma the loop induction consumes, the induction over `valid ≤ 32`,
and the statement's footprint clause.  `scanWindowLLVM_refines` is the statement
`scanWindowStatement`, and the chain's own last step stores the stop word, which
is the word the model names — an agreement to prove at every lane, not one to
read off the windows measured so far.
-/
import LeanLLVM.Refinement.JsonScanIR
import LeanLLVM.Refinement.BlockEval

namespace LeanLLVM.Refinement.JsonScanLane

open LeanLLVM
open LeanLLVM.JSON
open LeanLLVM.Refinement.JsonScanModel
open LeanLLVM.Refinement.JsonScanIR (maskPref maskPref_succ maskPref_eq_maskOfList)
open LeanLLVM.Refinement.JsonScanBody (scanWindowBody scanWindowBaselineBody ruleInstrs
  laneHead maskedSkipBits plainSkipBits)
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
   | rw [LeanLLVM.Refinement.BlockEval.denoteCode_load64]
   | rw [LeanLLVM.Refinement.BlockEval.denoteCode_trunc]
   | rw [LeanLLVM.Refinement.BlockEval.denoteCode_gep8_reg]))

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
      laneHeadOut, maskedSkipBitsOut, plainSkipBitsOut]))
   all_goals (try lane_lookup_close)
   all_goals (try rfl)
   all_goals (try assumption)
   all_goals (try rfl)))

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

end LeanLLVM.Refinement.JsonScanLane
