/-
The model-side selection for the scanner window, and the readback of it.

`envForScanWindow` is the reference side of the `json_scan` unit: a call
environment that reads the window and the carry from the caller's memory,
computes what `windowOf` computes, writes one 32-bit mask at `%out` and the next
carry in the 16-byte slot at `%state`, and returns the status word.  It is a
readback of the model rather than a second computation, and it consumes each of
`windowOf`'s two answers exactly where that answer holds: the mask is
`maskOfList` by `windowOf_structural`, and the carry is `carryAt` at the stop's
lane — or at `bs.length` when the window has no stop.

Three carry facts, stated separately because they hold for different objects.
`windowOf_carry` gives the fold's carry as `carryAt` at thirty-two lanes, and
`windowOf_carry_of_short` clamps that to a shorter window's own length; both are
facts about **any** window of at most thirty-two bytes.  The selection's written
carry is the fold's only on a **no-stop** window
(`carryAt_stopLaneOrLength_eq_carry`).  On a stopped window it is the **prefix**
carry at the stop's lane, a different object: the fold keeps folding past the
stop, and `stoppedWindow_carry_diverges` is the executable witness.

The unit reads at most `readExtent` bytes, so `envForScanWindow` refuses a
`valid` above that extent rather than scanning a hybrid range:
`envForScanWindow_refuses_valid` states the refusal, and every selection theorem
already carries `hvalid`.

`slotAt`/`writeSlot` are the slot's byte-level read and write, four `i32` words
at `%state`; `slotAt_writeSlot` is the readback that lets a caller seed the slot
and lets one window hand its carry to the next through memory.  `memModel` is
the whole-scan post-memory over the caller's windows: the mask each window wrote
and the prefix carry in the state slot after the last one.  `memModelGo_slot` is
its invariant — after every window the slot holds the encoded carry the fold
threaded — and the bound is over `memModelSteps`, the number of windows the fold
visits, because the output grows one mask per visited window rather than per
input byte.
-/
import LeanLLVM.Refinement.JsonScanABI

namespace LeanLLVM.Refinement.JsonScanModel

open LeanLLVM
open LeanLLVM.JSON
open LeanLLVM.Refinement.JsonScanABI

/-! ### The window's stop, and the lane the carry is read at -/

/-- The window's first stop, named for the selection below. -/
def stopOf (bs : List UInt8) (st : BodyState) : Option Stop :=
  (windowOf bs st).stop

/-- The lane a stop names.  A close stops *at* its quote and a refusal at its
byte, and both report the lane the byte rule did not continue past. -/
def stopLane : Stop → Nat
  | .close k => k
  | .refuse k _ => k

/-- The lane the next carry is read at: the stop's lane when the window stops,
and the window's length otherwise.  On a stopped window this is the **prefix**
carry, the state the caller resuming at the stop needs, not the fold's carry,
which keeps folding past the stop. -/
def stopLaneOrLength (bs : List UInt8) (st : BodyState) : Nat :=
  match stopOf bs st with
  | some s => stopLane s
  | none => bs.length

/-! ### The carry at a lane

`carryAt_succ` is private in `ScanWindow.lean`, so it is restated here additively
rather than made public.  The two facts below are what the slot invariant needs:
the carry advances one lane at a time, it keeps well-formedness, and past the
window's length the clamped fold stands still.
-/

/-- The carry on entry to lane `k + 1`: the clamped step at lane `k`. -/
theorem carryAt_succ (bs : List UInt8) (st : BodyState) (k : Nat) :
    carryAt bs st (k + 1) =
      (match bs[k]? with
       | some b =>
           (match bodyStep (carryAt bs st k) b with
            | .cont st' => st'
            | _ => carryAt bs st k)
       | none => carryAt bs st k) := by
  unfold carryAt
  rw [List.take_add_one, List.foldl_append]
  cases h : bs[k]? with
  | none => simp
  | some b => rfl

/-- Well-formedness survives the clamped fold. -/
theorem carryAt_wellFormed {bs : List UInt8} {st : BodyState} (h : st.WellFormed) (k : Nat) :
    (carryAt bs st k).WellFormed := by
  induction k with
  | zero => simpa [carryAt] using h
  | succ k ih =>
      rw [carryAt_succ]
      cases hk : bs[k]? with
      | none => simpa using ih
      | some b =>
          cases hs : bodyStep (carryAt bs st k) b with
          | cont st' => simpa only [hs] using bodyStep_wellFormed ih hs
          | closed => simpa only [hs] using ih
          | refused s => simpa only [hs] using ih

/-- Past the window's length the clamped fold stands still: `take` has already
taken every byte. -/
theorem carryAt_of_length_le {bs : List UInt8} {st : BodyState} {k : Nat}
    (h : bs.length ≤ k) : carryAt bs st k = carryAt bs st bs.length := by
  unfold carryAt
  rw [List.take_of_length_le h, List.take_length]

/-- **The short-window half of the fold's carry agreement.**  For **any** window
of fewer than thirty-two bytes, stopped or not, the fold's carry is `carryAt` at
the window's own length: `windowOf_carry` gives `carryAt` at 32, and
`carryAt_of_length_le` removes the lanes the window does not have.  This is a
statement about the fold's clamp, not about the selection's carry: identifying
the selection's written carry with the fold's additionally requires that the
window has **no stop** (`carryAt_stopLaneOrLength_eq_carry`), because a stopped
window's written carry is `carryAt` at the stop's lane instead. -/
theorem windowOf_carry_of_short {bs : List UInt8} {st : BodyState}
    (hlen : bs.length < 32) :
    (windowOf bs st).carry = carryAt bs st bs.length := by
  rw [windowOf_carry, carryAt_of_length_le (by omega)]

/-- On a no-stop window of at most thirty-two bytes, the carry the selection
writes — `carryAt` at `stopLaneOrLength`, which is the window's length — is the
fold's own carry.  The stopped case is excluded by `hstop`: there the selection's
lane is the stop's, and the fold's carry is past it. -/
theorem carryAt_stopLaneOrLength_eq_carry {bs : List UInt8} {st : BodyState}
    (hlen : bs.length ≤ 32) (hstop : stopOf bs st = none) :
    carryAt bs st (stopLaneOrLength bs st) = (windowOf bs st).carry := by
  rw [show stopLaneOrLength bs st = bs.length by simp [stopLaneOrLength, hstop]]
  by_cases hshort : bs.length < 32
  · exact (windowOf_carry_of_short hshort).symm
  · have h32 : bs.length = 32 := by omega
    rw [h32, windowOf_carry]

/-! ### The state slot in memory

The slot is four `i32` words at `%state`, so the selection reads it as four
loads and writes it as four stores.  No vector store and no list surgery: the
layout is the normative one in `JsonScanABI`.
-/

/-- One `i32` load: four little-endian bytes read back as a word. -/
def readWord (m : Mem) (addr : Nat) : Option (BitVec 32) :=
  (readBytes m addr 4).map fun bs => BitVec.ofNat 32 (bytesToNat bs)

/-- The slot's four words, as a `Slot`. -/
def readSlot (m : Mem) (p : Nat) : Option Slot :=
  (readWord m p).bind fun flags =>
    (readWord m (p + 4)).bind fun count =>
      (readWord m (p + 8)).bind fun lo =>
        (readWord m (p + 12)).map fun hi => ⟨flags, count, lo, hi⟩

/-- The carry a caller's state slot holds. -/
def slotAt (m : Mem) (p : Nat) : Option BodyState :=
  (readSlot m p).map decodeState

/-- The slot's four `i32` stores at `%state`. -/
def writeSlot (m : Mem) (p : Nat) (s : Slot) : Mem :=
  writeBytes (writeBytes (writeBytes (writeBytes m p (natToBytes s.flags.toNat 4))
      (p + 4) (natToBytes s.count.toNat 4))
      (p + 8) (natToBytes s.lo.toNat 4))
      (p + 12) (natToBytes s.hi.toNat 4)

/-- One mask's four little-endian bytes at `%out`. -/
def writeMask (m : Mem) (p : Nat) (mask : BitVec 32) : Mem :=
  writeBytes m p (natToBytes mask.toNat 4)

/-! ### The slot's readback -/

/-- A four-byte `natToBytes` read back through `bytesToNat` is the value modulo
`2 ^ 32`, and `BitVec.ofNat 32` absorbs the modulus. -/
private theorem ofNat_bytesToNat_natToBytes (x : Nat) :
    BitVec.ofNat 32 (bytesToNat (natToBytes x 4)) = BitVec.ofNat 32 x := by
  rw [natToBytes_toNat, show (256 : Nat) ^ 4 = 2 ^ 32 from by decide]
  apply BitVec.toNat_inj.mp
  simp [BitVec.toNat_ofNat]

/-- A word stored at an address reads back there. -/
private theorem readWord_ofNat (m : Mem) (p x : Nat) :
    readWord (writeBytes m p (natToBytes x 4)) p = some (BitVec.ofNat 32 x) := by
  have h := readBytes_writeBytes_same m (natToBytes x 4) (addr := p)
  rw [natToBytes_length] at h
  simp only [readWord, h, Option.map_some, ofNat_bytesToNat_natToBytes]

/-- A write sequence above a range leaves that range alone — the mirror of
`readBytes_writeBytes_below`, which the slot read needs when the mask is stored
first. -/
private theorem readBytes_writeBytes_above (m : Mem) (bs : List UInt8) (n start : Nat) :
    ∀ (addr : Nat), start + bs.length ≤ addr →
      readBytes (writeBytes m start bs) addr n = readBytes m addr n := by
  intro addr h
  induction n generalizing addr with
  | zero => rfl
  | succ n ih =>
      simp only [readBytes]
      rw [readByte_writeBytes_above m bs (by omega)]
      cases hr : readByte m addr with
      | none => rfl
      | some b => rw [ih (addr + 1) (by omega)]

/-- A word written above an address leaves the read there alone. -/
private theorem readWord_write_below {m : Mem} {p addr x : Nat} (h : addr + 4 ≤ p) :
    readWord (writeBytes m p (natToBytes x 4)) addr = readWord m addr := by
  have hb := readBytes_writeBytes_below m (natToBytes x 4) 4 addr p h
  simp only [readWord, hb]

/-- The mirror: a word read below the address written is not disturbed. -/
private theorem readWord_write_above {m : Mem} {pOut addr : Nat} {w : BitVec 32}
    (h : pOut + 4 ≤ addr) :
    readWord (writeBytes m pOut (natToBytes w.toNat 4)) addr = readWord m addr := by
  have hb := readBytes_writeBytes_above m (natToBytes w.toNat 4) 4 pOut addr
    (by rw [natToBytes_length]; exact h)
  simp only [readWord, hb]

private theorem ofNat_toNat_eq (x : BitVec 32) : BitVec.ofNat 32 x.toNat = x := by
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]

/-- The slot written with a state's encoding reads back as that state.  This is
what lets a caller seed the slot and what lets one window hand its carry to the
next through memory rather than through a register. -/
theorem slotAt_writeSlot (m : Mem) (p : Nat) {st : BodyState} (h : st.WellFormed) :
    slotAt (writeSlot m p (encodeState st)) p = some st := by
  have hdec : decodeState ⟨(encodeState st).flags, (encodeState st).count,
      (encodeState st).lo, (encodeState st).hi⟩ = st := by
    simpa only [encodeState] using decodeState_encodeState h
  simp only [slotAt, readSlot, writeSlot, Option.bind, Option.map]
  rw [readWord_write_below (p := p + 12) (addr := p) (by omega),
      readWord_write_below (p := p + 8) (addr := p) (by omega),
      readWord_write_below (p := p + 4) (addr := p) (by omega),
      readWord_ofNat]
  rw [readWord_write_below (p := p + 12) (addr := p + 4) (by omega),
      readWord_write_below (p := p + 8) (addr := p + 4) (by omega),
      readWord_ofNat]
  rw [readWord_write_below (p := p + 12) (addr := p + 8) (by omega), readWord_ofNat]
  rw [readWord_ofNat]
  simp only [ofNat_toNat_eq, hdec]

/-- A mask store at `%out` does not disturb the state slot, which the caller's
next window depends on. -/
theorem slotAt_writeMask (m : Mem) (pOut pState : Nat) (w : BitVec 32)
    (h : pOut + 4 ≤ pState) :
    slotAt (writeMask m pOut w) pState = slotAt m pState := by
  simp only [slotAt, readSlot, writeMask]
  rw [readWord_write_above (addr := pState) (by omega),
      readWord_write_above (addr := pState + 4) (by omega),
      readWord_write_above (addr := pState + 8) (by omega),
      readWord_write_above (addr := pState + 12) (by omega)]

/-! ### The reference selection -/

/-- The reference selection: the model's own window step, as a call.  It reads
the window and the slot from the caller's memory, computes `windowOf`, writes the
mask and the next carry, and returns the status word.  A call whose arguments do
not have the unit's shape, whose `valid` exceeds the unit's read extent, whose
window is unreadable, or whose slot is unreadable does not resolve.  The extent
guard is not decoration: `windowOf` folds at most thirty-two lanes, so a larger
`valid` would be answered with a thirty-two-lane mask and status beside a
longer prefix carry — an answer no window describes. -/
def envForScanWindow : Calls :=
  fun callee args mem next =>
    if callee = scanSymbol then
      match args with
      | [.ptr pIn, .ptr pOut, .ptr pState, .int 32 v] =>
          if v.toNat ≤ readExtent then
            match readBytes mem pIn v.toNat with
            | some bs =>
                match slotAt mem pState with
                | some st =>
                    let w := windowOf bs st
                    some { ret := .int 32 (encodeStatus (Status.ok w.stop)),
                           mem := writeSlot (writeMask mem pOut w.structural) pState
                                    (encodeState (carryAt bs st (stopLaneOrLength bs st))),
                           next := next }
                | none => none
            | none => none
          else none
      | _ => none
    else none

/-! ### The selection's statement

The mask is `maskOfList` and the carry is `carryAt` at the stop's lane (or the
window's length).  The stopped case is the statement rather than a case split
after it: `envForScanWindow_spec_close` and `envForScanWindow_spec_refuse` name
the lane directly, so a proof cannot reach for the fold's carry without proving
the two equal.
-/

/-- What the model's selection returns and writes, in one statement. -/
theorem envForScanWindow_spec (st : BodyState) (bs : List UInt8) (mem : Mem)
    (pIn pOut pState valid : Nat) (hvalid : valid ≤ 32)
    (hread : readBytes mem pIn valid = some bs)
    (hslot : slotAt mem pState = some st) (next : Nat) :
    envForScanWindow scanSymbol
        [.ptr pIn, .ptr pOut, .ptr pState, .int 32 (BitVec.ofNat 32 valid)] mem next =
      some { ret := .int 32 (encodeStatus (Status.ok (stopOf bs st))),
             mem := writeSlot (writeMask mem pOut (maskOfList bs)) pState
                      (encodeState (carryAt bs st (stopLaneOrLength bs st))),
             next := next } := by
  have hv : (BitVec.ofNat 32 valid).toNat = valid := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
    omega
  have hvl : valid ≤ readExtent := hvalid
  simp only [envForScanWindow, scanSymbol, hv, hvl, hread, hslot, stopOf,
    windowOf_structural, ↓reduceIte]

/-- The stopped window, closing: the slot holds the prefix carry `carryAt bs st k`
at the close's lane `k` — not the fold's carry, which keeps folding past it. -/
theorem envForScanWindow_spec_close (st : BodyState) (bs : List UInt8) (mem : Mem)
    (pIn pOut pState valid k : Nat) (hvalid : valid ≤ 32)
    (hread : readBytes mem pIn valid = some bs)
    (hslot : slotAt mem pState = some st)
    (hstop : stopOf bs st = some (.close k)) (next : Nat) :
    envForScanWindow scanSymbol
        [.ptr pIn, .ptr pOut, .ptr pState, .int 32 (BitVec.ofNat 32 valid)] mem next =
      some { ret := .int 32 (encodeStatus (Status.ok (some (.close k)))),
             mem := writeSlot (writeMask mem pOut (maskOfList bs)) pState
                      (encodeState (carryAt bs st k)),
             next := next } := by
  rw [envForScanWindow_spec st bs mem pIn pOut pState valid hvalid hread hslot next]
  simp only [stopLaneOrLength, hstop, stopLane]

/-- The stopped window, refusing: the slot holds the prefix carry at the
refusal's lane. -/
theorem envForScanWindow_spec_refuse (st : BodyState) (bs : List UInt8) (mem : Mem)
    (pIn pOut pState valid k : Nat) (reason : BodyStop) (hvalid : valid ≤ 32)
    (hread : readBytes mem pIn valid = some bs)
    (hslot : slotAt mem pState = some st)
    (hstop : stopOf bs st = some (.refuse k reason)) (next : Nat) :
    envForScanWindow scanSymbol
        [.ptr pIn, .ptr pOut, .ptr pState, .int 32 (BitVec.ofNat 32 valid)] mem next =
      some { ret := .int 32 (encodeStatus (Status.ok (some (.refuse k reason)))),
             mem := writeSlot (writeMask mem pOut (maskOfList bs)) pState
                      (encodeState (carryAt bs st k)),
             next := next } := by
  rw [envForScanWindow_spec st bs mem pIn pOut pState valid hvalid hread hslot next]
  simp only [stopLaneOrLength, hstop, stopLane]

/-- The no-stop **full-window** instance of the selection-carry identification:
the written prefix carry is the fold's own carry.  The short no-stop instance is
`carryAt_stopLaneOrLength_eq_carry` (through `windowOf_carry_of_short`); on a
stopped window neither instance applies, and the written carry is the prefix
carry at the stop's lane. -/
theorem envForScanWindow_spec_full (st : BodyState) (bs : List UInt8) (mem : Mem)
    (pIn pOut pState valid : Nat) (hvalid : valid ≤ 32)
    (hread : readBytes mem pIn valid = some bs)
    (hslot : slotAt mem pState = some st)
    (hstop : stopOf bs st = none) (hlen : bs.length = 32) (next : Nat) :
    envForScanWindow scanSymbol
        [.ptr pIn, .ptr pOut, .ptr pState, .int 32 (BitVec.ofNat 32 valid)] mem next =
      some { ret := .int 32 (encodeStatus (Status.ok none)),
             mem := writeSlot (writeMask mem pOut (maskOfList bs)) pState
                      (encodeState ((windowOf bs st).carry)),
             next := next } := by
  rw [envForScanWindow_spec st bs mem pIn pOut pState valid hvalid hread hslot next]
  simp only [stopLaneOrLength, hstop]
  rw [hlen, ← windowOf_carry bs st]

/-- A call whose `valid` exceeds the unit's read extent does not resolve: the
selection refuses it instead of folding a thirty-two-lane window and returning a
longer prefix carry.  This is the model `none` a refinement proof uses to
discharge out-of-contract arguments. -/
theorem envForScanWindow_refuses_valid (mem : Mem) (pIn pOut pState : Nat)
    (v : BitVec 32) (next : Nat) (hlarge : readExtent < v.toNat) :
    envForScanWindow scanSymbol
        [.ptr pIn, .ptr pOut, .ptr pState, .int 32 v] mem next = none := by
  have hnot : ¬ v.toNat ≤ readExtent := by omega
  simp only [envForScanWindow, scanSymbol, hnot, ↓reduceIte]

/-! ### The stopped window, as an executable check

A closing quote at lane 0 followed by a backslash: the fold stops at lane 0 and
keeps folding, so its carry is the state *after* the post-stop lane, while the
prefix carry is the state before lane 0.  The last theorem is what refuses a
`windowOf.carry` reading of the stopped case. -/

/-- A closing quote at lane 0, then a backslash. -/
def stoppedWindow : List UInt8 := [0x22, 0x5C]

/-- The model stops at lane 0. -/
theorem stoppedWindow_stop : stopOf stoppedWindow BodyState.body = some (.close 0) := by
  decide

/-- The state on entry to the stop's lane is the body's. -/
theorem stoppedWindow_prefix : carryAt stoppedWindow BodyState.body 0 = BodyState.body := by
  decide

/-- **The two carries differ on a stopped window**: the fold's is `⟨true, true,
none⟩` and the prefix is `BodyState.body`.  So `windowOf_carry` cannot stand in
for the stopped case's carry, and the selection's slot write names `carryAt`
itself. -/
theorem stoppedWindow_carry_diverges :
    (windowOf stoppedWindow BodyState.body).carry ≠
      carryAt stoppedWindow BodyState.body 0 := by
  decide

/-- The fold's own carry on the witness, named: the parity flips on the
post-stop backslash. -/
theorem stoppedWindow_fold_carry :
    (windowOf stoppedWindow BodyState.body).carry = ⟨true, true, Utf8Need.none⟩ := by
  decide

/-! ### The whole-scan post-memory

`memModel` is the memory the whole scan leaves: for each window the caller's loop
visits, the mask that window wrote at `pOut + 4k`, and the prefix carry in the
state slot, until a window stops or the bytes run out.  `memModelGo_slot` is the
invariant that makes the fold a memory fold rather than a second scan: after
every window the slot holds the encoded carry the fold threaded, with the
no-stop agreement (`carryAt_stopLaneOrLength_eq_carry`, short windows included)
supplying the step from the written prefix carry to the state the next window
reads.
-/

/-- The bytes of the window the caller's loop reads at `i`: at most thirty-two,
the rest of the input when fewer remain. -/
def windowBytes (bs : Bytes) (i : Nat) : List UInt8 :=
  ((bs.drop i).take 32).data.toList

/-- A window has at most thirty-two bytes, so the short-window carry agreement
applies to it. -/
theorem windowBytes_length_le (bs : Bytes) (i : Nat) : (windowBytes bs i).length ≤ 32 := by
  unfold windowBytes
  rw [← ByteString.toList_eq_data_toList, ByteString.toList_take, List.length_take]
  omega

/-- The post-memory fold, with its fuel explicit.  Each step writes the window's
mask at `pOut + 4k` and its next carry at `pState`, and continues on no stop.
`i` is the window's byte position, `k` its output slot, and `st` the carry the
state slot holds on entry. -/
def memModelGo (bs : Bytes) (pOut pState : Nat) :
    Nat → Nat → Nat → BodyState → Mem → Mem
  | 0, _, _, _, mem => mem
  | fuel + 1, i, k, st, mem =>
      if i < bs.size then
        let ws := windowBytes bs i
        let w := windowOf ws st
        let mem' := writeSlot (writeMask mem (pOut + 4 * k) w.structural) pState
                      (encodeState (carryAt ws st (stopLaneOrLength ws st)))
        match w.stop with
        | some _ => mem'
        | none => memModelGo bs pOut pState fuel (i + ws.length) (k + 1) w.carry mem'
      else mem

/-- The carry the fold leaves in the state slot.  It follows `memModelGo`'s
windows, but on a stopped window it names the **prefix** carry the step wrote
(`carryAt` at the stop's lane) rather than the fold's carry, which the recursion
never reaches. -/
def memModelCarry (bs : Bytes) : Nat → Nat → BodyState → BodyState
  | 0, _, st => st
  | fuel + 1, i, st =>
      if i < bs.size then
        let ws := windowBytes bs i
        let w := windowOf ws st
        match w.stop with
        | some _ => carryAt ws st (stopLaneOrLength ws st)
        | none => memModelCarry bs fuel (i + ws.length) w.carry
      else st

/-- The number of windows the fold visits: one per step, stopping at a stop or
at the end of the input.  This — not the input's length — is the unit of the
output extent: the scan writes one mask per visited window, so a caller's layout
bound is stated over this count and can be discharged from the same loop that
supplies the windows. -/
def memModelSteps (bs : Bytes) : Nat → Nat → BodyState → Nat
  | 0, _, _ => 0
  | fuel + 1, i, st =>
      if i < bs.size then
        let ws := windowBytes bs i
        let w := windowOf ws st
        match w.stop with
        | some _ => 1
        | none => 1 + memModelSteps bs fuel (i + ws.length) w.carry
      else 0

/-- **The slot invariant.**  Starting with the slot holding `st`, after `fuel`
further steps — `k` windows already written — the slot holds the encoding of the
carry the fold threaded: on a no-stop window that is the fold's own carry
(`carryAt_stopLaneOrLength_eq_carry`, short windows included), and on a stopped
window it is the prefix carry the step wrote.  The mask store at `%out` must end
before `%state`; `pOut + 4 * (k + memModelSteps) ≤ pState` is exactly the output
extent — `k` masks already written and one per window the remaining steps visit —
so the bound is per visited window, not per input byte. -/
theorem memModelGo_slot (bs : Bytes) (pOut pState : Nat) :
    ∀ (fuel i k : Nat) (st : BodyState) (mem : Mem),
      st.WellFormed →
      pOut + 4 * (k + memModelSteps bs fuel i st) ≤ pState →
      slotAt mem pState = some st →
      slotAt (memModelGo bs pOut pState fuel i k st mem) pState =
        some (memModelCarry bs fuel i st) := by
  intro fuel
  induction fuel with
  | zero =>
      intro i k st mem _ _ hs
      simpa only [memModelGo, memModelCarry] using hs
  | succ fuel ih =>
      intro i k st mem hst hb hs
      by_cases hi : i < bs.size
      · have hstep : memModelGo bs pOut pState (fuel + 1) i k st mem =
            (let ws := windowBytes bs i
             let w := windowOf ws st
             let mem' := writeSlot (writeMask mem (pOut + 4 * k) w.structural) pState
                           (encodeState (carryAt ws st (stopLaneOrLength ws st)))
             match w.stop with
             | some _ => mem'
             | none => memModelGo bs pOut pState fuel (i + ws.length) (k + 1) w.carry mem') := by
          simp only [memModelGo, hi, ↓reduceIte]
        rw [hstep]
        dsimp only
        have hstepspos : 0 < memModelSteps bs (fuel + 1) i st := by
          simp only [memModelSteps, hi, ↓reduceIte]
          split <;> omega
        have hmask : pOut + 4 * k + 4 ≤ pState := by omega
        have hwrite : slotAt
            (writeSlot (writeMask mem (pOut + 4 * k) (windowOf (windowBytes bs i) st).structural)
              pState (encodeState (carryAt (windowBytes bs i) st
                (stopLaneOrLength (windowBytes bs i) st)))) pState =
            some (carryAt (windowBytes bs i) st
              (stopLaneOrLength (windowBytes bs i) st)) :=
          slotAt_writeSlot _ _ (carryAt_wellFormed hst _)
        cases hstop : (windowOf (windowBytes bs i) st).stop with
        | some s =>
            rw [hwrite]
            simp only [memModelCarry, hi, ↓reduceIte, hstop]
        | none =>
            simp only [memModelCarry, hi, ↓reduceIte, hstop]
            have hwrite' : slotAt
                (writeSlot (writeMask mem (pOut + 4 * k)
                  (windowOf (windowBytes bs i) st).structural) pState
                  (encodeState (carryAt (windowBytes bs i) st
                    (stopLaneOrLength (windowBytes bs i) st)))) pState =
                some (windowOf (windowBytes bs i) st).carry := by
              rw [hwrite,
                carryAt_stopLaneOrLength_eq_carry (windowBytes_length_le bs i) hstop]
            have hsteps : memModelSteps bs (fuel + 1) i st =
                1 + memModelSteps bs fuel (i + (windowBytes bs i).length)
                  (windowOf (windowBytes bs i) st).carry := by
              simp only [memModelSteps, hi, ↓reduceIte, hstop]
            rw [hsteps] at hb
            exact ih (i + (windowBytes bs i).length) (k + 1)
              (windowOf (windowBytes bs i) st).carry _ (windowOf_wellFormed hst)
              (by omega) hwrite'
      · have hstep : memModelGo bs pOut pState (fuel + 1) i k st mem = mem := by
          simp only [memModelGo, hi, ↓reduceIte]
        rw [hstep]
        simpa only [memModelCarry, hi, ↓reduceIte] using hs

/-- The whole-scan post-memory: the masks each window wrote, and the prefix
carry in the state slot after the last window.  The scan starts at the first
body byte, `q + 1`, with the body's initial state; the fuel is one more than the
input, because every visited window consumes at least one byte. -/
def memModel (bs : Bytes) (q : Nat) (mem : Mem) (pOut pState : Nat) : Mem :=
  memModelGo bs pOut pState (bs.size + 1) (q + 1) 0 BodyState.body mem

/-- The whole scan's slot: seeded with the body's state and with every mask store
ending below `%state`, the slot after the fold holds the encoded carry the scan
left.  The bound is the **copy count**: `memModelSteps` masks of four bytes each,
one per visited window — the fold's own count, so P5's loop can discharge it from
the number of calls it makes rather than from the input's length. -/
theorem memModel_slot (bs : Bytes) (q : Nat) (mem : Mem) (pOut pState : Nat)
    (hbound : pOut + 4 * memModelSteps bs (bs.size + 1) (q + 1) BodyState.body ≤ pState)
    (hslot : slotAt mem pState = some BodyState.body) :
    slotAt (memModel bs q mem pOut pState) pState =
      some (memModelCarry bs (bs.size + 1) (q + 1) BodyState.body) := by
  unfold memModel
  exact memModelGo_slot bs pOut pState (bs.size + 1) (q + 1) 0 BodyState.body mem
    BodyState.body_wellFormed (by simpa using hbound) hslot

/-- The fold's definition, restated: a change to the fuel, the start, or the
initial state breaks this `rfl`. -/
theorem memModel_eq (bs : Bytes) (q : Nat) (mem : Mem) (pOut pState : Nat) :
    memModel bs q mem pOut pState =
      memModelGo bs pOut pState (bs.size + 1) (q + 1) 0 BodyState.body mem := rfl

end LeanLLVM.Refinement.JsonScanModel
