/-
# The numeral's record, written from the scalar seam

`s2ScalarValue_appended` (`JsonStage2Helpers:1300`) proves an *existential*: the
scalar call appends some record.  This module fixes it.  At the scalar seam the
token's three words are the seam's own (`JsonEventCallerResultSeamWords`), the
log's three are `WalkInv`, and the staged window is the document's; the record the
call appends is therefore `EventRecord.number (strtodSpec evbDecimal).toBits =
EventRecord.number evbBits`, computed from the lexeme the window carries.

The seam's first staging word — `%c.i`'s base — is the environment row Main
designated: the entry stages it (`walkSeg3Stores`, `JsonStage2WalkRun:883`) and
`WalkInv` carries the record's address, its presence and silence outside it, not
the word inside it.  The row is stated where the seam's other rows are, so the
numeral's record is a consequence of the row and the seam's stores, not a premise.

There is no `sorry`, `admit` or `native_decide`.
-/
import LeanLLVM.Refinement.JsonEventCallerResultSeamWords

set_option autoImplicit false

namespace LeanLLVM.Refinement
namespace WalkScope

open LeanLLVM
open LeanLLVM.JSON
open LeanLLVM.Refinement.JsonStage2IR

/-! ### The decomposition is the reader's -/

/-- **`1` is a well-formed decomposition**: the one-digit `int` `0x31`, no fraction,
no exponent.  `strtodSpec evbDecimal` is the emitted conversion at it. -/
theorem evbDecimal_wf : evbDecimal.wellFormed := by
  refine ⟨?_, ?_, ?_⟩
  · show IntPart evbLex
    rw [show evbLex = ByteString.literal [0x31] from rfl, ByteString.literal_cons,
      show ByteString.literal ([] : List UInt8) = ByteString.empty from rfl]
    exact IntPart.lead (by decide) (by decide) (.nil)
  · intro fs h
    simp [evbDecimal] at h
  · intro s ds h
    simp [evbDecimal] at h

/-- The conversion at the slice's lexeme is the specification's. -/
theorem evb_numFastEmitted :
    numFastEmitted evbLex = strtodSpec evbDecimal :=
  numFastEmitted_strtodSpec evbDecimal evbDecimal_wf

/-! ### The append, at the callee

The scalar call's number arm is `stage2ScalarValue`'s `kind = 7` branch: it reads
the token's three words, the window, and the log's three; writes the number record
by `emitBlobs`; and advances the cursor.  With the window's lexeme fixed, the
record is the specification's. -/

/-- **The scalar call appends the numeral's record.**  Every word is an explicit
read at the call's memory; the only document fact is the window's one-byte lexeme,
`hlex`.  The conclusion is `s2ScalarValueAppend` at `EventRecord.number evbBits`'s
bytes, not an existential. -/
theorem s2ScalarValue_numberAppend {mem : Mem} {c t o next : Nat} {r : CallOutcome}
    {base e pos endp kind buf len cap : Nat} {win : List UInt8}
    (hcall : stage2Calls stage2SubCalls "od_scalar_value" [.ptr c, .ptr t, .ptr o]
      mem next = some r)
    (hbase : stage2ReadWord mem c 8 = some base)
    (he : stage2ReadWord mem (c + 1112) 8 = some e)
    (hpos : stage2ReadWord mem t 8 = some pos)
    (hend : stage2ReadWord mem (t + 8) 8 = some endp)
    (hkind : stage2ReadWord mem (t + 16) 4 = some kind)
    (hbuf : stage2ReadWord mem o 8 = some buf)
    (hlen : stage2ReadWord mem (o + 8) 8 = some len)
    (hcap : stage2ReadWord mem (o + 16) 8 = some cap)
    (hroom : len + stage2RecordBytes ≤ cap)
    (hwin : readBytes mem (base + pos) (max (endp - pos) 5) = some win)
    (hkind7 : kind = 7)
    (hlex : win.take (endp - pos) = [0x31]) :
    s2ScalarValueAppend mem r.mem o
      (EventRecord.number evbBits).encodedBytes := by
  have hlexread : readBytes mem (base + pos) (endp - pos) =
      some (win.take (endp - pos)) :=
    readBytes_take_prefix (Nat.le_max_left _ _) hwin
  rw [stage2Calls_od_scalar_value, stage2ScalarValueCall] at hcall
  simp only [stage2ScalarValue, hbase, he, hpos, hend, hkind] at hcall
  simp only [hkind7] at hcall
  simp only [hlexread, hlex] at hcall
  have hconv : numFastEmitted (ByteString.literal [0x31]) = strtodSpec evbDecimal := by
    simpa only [evbLex] using evb_numFastEmitted
  rw [hconv] at hcall
  have hscan : (numLexScan [0x31]).2 = true := by decide
  simp [hscan, hbuf, hlen, hcap, evbBits] at hcall
  have hrec : ((numberRecord ((strtodSpec evbDecimal).toBits)).flatten).length ≤
      stage2RecordBytes :=
    numberRecord_le _
  obtain ⟨p, hp⟩ := emitBlobs_complete (mem := mem) (ev := buf) (len := len)
    (cap := cap) (blobs := numberRecord ((strtodSpec evbDecimal).toBits)) (by omega)
  obtain ⟨p1, p2⟩ := p
  rw [hp] at hcall
  obtain ⟨hm', hl'⟩ := emitBlobs_spec hp
  rw [hm', hl'] at hcall
  refine ⟨buf, len, hbuf, hlen, ?_⟩
  simp only [EventRecord.encodedBytes]
  have hr : r = CallOutcome.mk (.int 32 (BitVec.ofNat 32 1))
      (writeBytes (writeBytes mem (buf + len)
        (numberRecord ((strtodSpec evbDecimal).toBits)).flatten)
        (o + 8) (wordBytes 8 (len +
          ((numberRecord ((strtodSpec evbDecimal).toBits)).flatten).length))) next := by
    simpa only [hm', hl'] using (Option.some.inj hcall).symm
  rw [hr]
  rfl

/-! ### Axiom footprints -/

#print axioms evbDecimal_wf
#print axioms evb_numFastEmitted
#print axioms s2ScalarValue_numberAppend

end WalkScope
end LeanLLVM.Refinement
