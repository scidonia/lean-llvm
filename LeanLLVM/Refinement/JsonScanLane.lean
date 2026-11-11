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
          AgreesOutsideMem mem' (writeSlot (writeMask mem pOut (maskOfList bs)) pState
              (encodeState (carryAt bs st (stopLaneOrLength bs st)))) (Band base (base + 28)) ∧
          readBytes mem' pIn valid = some bs

That statement is `JsonScanIR.scanWindowStatement`, with the band hypothesis the
prose leaves as `(hband : … base disjoint …)` supplied as
`JsonScanIR.scanBandDisjoint` and the frame tied to `JsonScanIR.scanBandBytes`.
It is a proposition and not a theorem.  Two things a proof meets before it can
start are settled: the band hypothesis is load-bearing
(`JsonScanIR.bandOverlap_clobbers_window`, with `bandClear_preserves_window` as its
control), and the stop word's select chain reported `control` where the model
refuses with `badUtf8` on a byte outside a pending requirement
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

**What is not here.**  The `body` block's instruction chain (the measured
per-lane count of the scalar skeleton, one `qN` state and one `evalInstr` lemma
per instruction), the `laneStep` lemma the loop induction consumes, and the
induction itself.  The chain is to be generated from `JsonScanBody.ruleInstrs` by
a committed `#eval` generator rather than hand-written: the `qN` states are
definitions inside a proof and carry no pins, while `laneStep`, the induction and
`scanWindowLLVM_refines` each carry a `#print axioms` pin and an `example`.  None
of them is here yet: `scanWindowLLVM_refines` is the statement
`scanWindowStatement`, and the chain's own last step stores the stop word, which is
the word the model names — an agreement to prove at every lane, not one to read off
the windows measured so far.
-/
import LeanLLVM.Refinement.JsonScanIR

namespace LeanLLVM.Refinement.JsonScanLane

open LeanLLVM
open LeanLLVM.JSON
open LeanLLVM.Refinement.JsonScanModel
open LeanLLVM.Refinement.JsonScanIR (maskPref maskPref_succ maskPref_eq_maskOfList)
open LeanLLVM.Refinement.JsonScanBody (scanWindowBody scanWindowBaselineBody ruleInstrs)

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

end LeanLLVM.Refinement.JsonScanLane
