/-
The JSON window scanner's lane machinery, at the LLVM level.

`LeanLLVM/Vellum/JsonScanIR.lean` holds the fixture pin and the model-side prefix
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

The body is scalar: one lane per iteration, the model's predicates as straight
line IR, the structural mask accumulated into one `i32` by `shl`/`or`, the
counter, the carry and the stop word in memory.  `maskStep` below is the mask
accumulator's one step — the emitted `or` of the lane's bit against the model's
own `maskOfList` fold — and it is the only theorem this module holds, so nothing
here is proved and unused.

**What is not here.**  The `body` block's instruction chain (the measured
per-lane count of the scalar skeleton, one `qN` state and one `evalInstr` lemma
per instruction), the `laneStep` lemma the loop induction consumes, and the
induction itself.  The chain is to be generated from `JsonScanBody.ruleInstrs` by
a committed `#eval` generator rather than hand-written: the `qN` states are
definitions inside a proof and carry no pins, while `laneStep`, the induction and
`scanWindowLLVM_refines` each carry a `#print axioms` pin and an `example`.
-/
import LeanLLVM.Vellum.JsonScanIR

namespace LeanLLVM.Vellum.JsonScanLane

open LeanLLVM
open LeanLLVM.JSON
open LeanLLVM.Vellum.JsonScanModel
open LeanLLVM.Vellum.JsonScanIR (maskPref maskPref_succ maskPref_eq_maskOfList)
open LeanLLVM.Vellum.JsonScanBody (scanWindowBody scanWindowBaselineBody)

/-- **The mask accumulator's step.**  One lane's `shl`/`or` leaves the model's
own prefix fold: with the accumulator holding `maskPref bs k` and the lane's
structural bit decided by the two-word table, the emitted `or` of the lane's bit
is `maskPref bs (k + 1)`.  This is the clause "accumulated by `shl`/`or`" made
checkable: the accumulator is one `i32` `or` chain over a predicate that is a
table, which is what `maskOfList`'s fold is.

`maskPref_eq_maskOfList` at the window's end then turns the accumulator into the
word the unit stores at `%out`. -/
theorem maskStep (bs : List UInt8) (m : BitVec 32) (stb : Bool) (k : Nat) (b : UInt8)
    (hk : k < 32) (hb : bs[k]? = some b) (hm : m = maskPref bs k)
    (hstb : stb = IsStructOrSpaceB b) :
    (if stb = true then m ||| ((1 : BitVec 32) <<< k) else m) = maskPref bs (k + 1) := by
  subst hm
  subst hstb
  rw [maskPref_succ]
  simp only [hb]

end LeanLLVM.Vellum.JsonScanLane
