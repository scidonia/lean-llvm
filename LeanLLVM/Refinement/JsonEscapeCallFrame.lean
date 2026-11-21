/-
The escape list's per-call frame, at one block's call.

`Γ_escape_positions` read at a call site: the caller's staging is the unit's `pre`,
and what comes back is the unit's `post`, whose `EscapeReach` conjunct is the
frame.  The block's refinement does not re-prove the unit — it resolves the call
through a caller-supplied entry and needs three things at the call's own numbers:
the regions the block's `s1BlocksPost` names, the stream and count the next
iteration reads, and the capacity the next call's `pre` consumes.  Each is a
consequence of the record, and this module derives them once, at the shape a call
site holds.

**The regions are the unit's, in the block's spelling.**  The unit's frame starts
at the stream's cursor, `xp + 4 * xn0`, and reaches the counted span plus the
batch's reserve.  Its widening to the stream's base is the block's spelling,
`4 * (nxp' + batchReserve)` with `nxp'` the count read back out of its slot: the
sharp frame is restated once at the call's own numbers
(`escapeReach_callTouched`), the widening once at the block's
(`escapeReach_callRegions`), and the block's four-region list follows from it by
inclusion with no staging obligation added.

**The stream's prefix is a consequence of the frame.**  Because the frame starts
at the cursor, the bytes below it are the caller's: `escapeReach_streamPrefix`
reads the prefix below the cursor out of the record, with the caller's pre-state
read as its only premise.  A consumer no longer has to supply the post-state
prefix itself.

**The entry words are kept by the frame, not by the post.**  `s1BlocksPost`'s
entry clause is a value claim the block's own stores establish, so the call must
not disturb `ent`.  The unit's frame says every byte outside its three regions is
the caller's, and `ent` is outside them by the staging's separations, so its bytes
read back unchanged (`escapeReach_keepsEntry`).  The separations are the staging's
and not the unit's: `Γ_escape_positions.pre` has no argument for `ent`.

**What the record does not carry.**  Two facts a caller needs are wider than the
unit's own clauses:

* the count at the call is bounded below `2 ^ 63` (`pre`), but the *next* call's
  count is `xn0 + len`, and the record states nothing about that sum.  The block
  proves it from its own document bound, and it is a premise here;
* the capacity the post restates is `blockMax xn0`, this call's own extent, while
  the next call's `pre` wants `blockMax (xn0 + len)`.  `escape_call_capacity`
  carries the *staged* capacity across the call from the frame, so the caller keeps
  the whole stream it staged rather than the part this call reached.

Everything is at the unit's own record: `escape_call_at` takes the call entry as
`CallSatisfies` and derives the clauses, and `escape_call_at_unit` discharges that
entry from `escape_positions_satisfies` at the pinned body, so no caller assumes a
fact about `leanllvm_json_escape_list` that was not proved.

The one thing this module does *not* state is the positions' own values on the
block's side.  The post's positions are its witnesses' (`blockPositions blk0 lo hi
st` for the post's `lo hi st`), and the caller holds a different assignment of the
same argument list; the block's post quantifies its `ps` and needs only the
extent's readback, so the segment is handed on as `∃ ps` at the caller's length.
Recovering the *values* would take an injectivity argument on the classifier state
that nothing downstream consumes.
-/
import LeanLLVM.Refinement.JsonEscapeListContract
import LeanLLVM.Refinement.JsonEntrySteps

set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 1000000

namespace LeanLLVM.Refinement

open LeanLLVM
open LeanLLVM.JSON
open LeanLLVM.Refinement.JsonEscapeIR
open LeanLLVM.Refinement.JsonS1MasksIR
open LeanLLVM.Refinement.JsonScanSpec
open LeanLLVM.Refinement.BitLanes
open LeanLLVM.Refinement.JsonEntrySteps

/-! ### The block's write regions, in the unit's spelling -/

/-- The three regions the escape list may write, at the extent the block's post
names: the stream's *touched* extent — the counted span plus the batch's
eight-entry reserve — the count's slot, and the carry's sixteen bytes.  `nxp'` is
the count the block reads back out of the slot, so the stream's extent is stated
at the same number the block's own clauses use. -/
def escapeCallRegions (xp xn xcarry nxp' : Nat) : List (Nat × Nat) :=
  [(xp, 4 * (nxp' + batchReserve)), (xn, 8), (xcarry, 16)]

/-- The regions the block's post names: the entry words the block writes, and the
escape list's three.  A byte outside all four is the caller's, which is what the
block's post claims and what the call has to preserve. -/
def escapeCallWriteRegions (ent blocks xp xn xcarry nxp' : Nat) : List (Nat × Nat) :=
  (ent, 8 * blocks) :: escapeCallRegions xp xn xcarry nxp'

/-- The block's three regions, in the unit's spelling: the stream's extent from
its base to the counted span plus the reserve.  The unit's frame starts at the
cursor; this list is that frame's widening to the stream's base, and it is what a
consumer orders its own static regions against. -/
theorem escapeCallRegions_eq_touched (xp xn xcarry xn0 len : Nat) :
    escapeCallRegions xp xn xcarry (xn0 + len) =
      [(xp, 4 * touchedPositions xn0 len), (xn, 8), (xcarry, 16)] := rfl

/-! ### The frame, read out of the reach -/

/-- **The escape unit's frame at the call's own numbers.**  `EscapeReach`'s last
conjunct, at the cursor-based stream extent the run's stores actually reached. -/
theorem escapeReach_callTouched {blk0 : BitVec 64} {xp xn carry xn0 : Nat}
    {position : List Nat} {carryBytes : List UInt8} {mem0 M : Mem}
    (h : EscapeReach blk0 xp xn carry xn0 position carryBytes mem0 M) :
    UnchangedOutside mem0 M (touchedRegions xp xn carry xn0 position.length) :=
  h.2.2.2.2

/-- **The cursor-based frame widened to the block's spelling.**  The block's three
regions name the stream from its base; the unit's frame names it from the cursor,
and a byte outside the wide region is outside the narrow one too, so the widening
is membership alone. -/
theorem touchedRegions_to_callRegions {mem0 M : Mem} {xp xn xcarry xn0 len : Nat}
    (h : UnchangedOutside mem0 M (touchedRegions xp xn xcarry xn0 len)) :
    UnchangedOutside mem0 M (escapeCallRegions xp xn xcarry (xn0 + len)) := by
  have h' : UnchangedOutside mem0 M
      [(xp, 4 * touchedPositions xn0 len), (xn, 8), (xcarry, 16)] :=
    touchedRegions_widen_touched h
  simpa [escapeCallRegions_eq_touched] using h'

/-- **The escape unit's frame at the block's extent.**  `EscapeReach`'s last
conjunct starts at the cursor; the block's post names the stream from its base,
and the two extents are related by widening, so the frame is handed on at the
block's spelling. -/
theorem escapeReach_callRegions {blk0 : BitVec 64} {xp xn carry xn0 : Nat}
    {position : List Nat} {carryBytes : List UInt8} {mem0 M : Mem}
    (h : EscapeReach blk0 xp xn carry xn0 position carryBytes mem0 M) :
    UnchangedOutside mem0 M (escapeCallRegions xp xn carry (xn0 + position.length)) :=
  touchedRegions_to_callRegions (escapeReach_callTouched h)

/-! ### The entry words are outside the frame -/

/-- A byte of a range the staging separates from a region is outside that
region: the range lies entirely before it or entirely after it. -/
theorem outside_of_separated {start n x w a : Nat}
    (h : start + n ≤ x ∨ x + w ≤ start) (hlo : start ≤ a) (hhi : a < start + n) :
    ¬ (x ≤ a ∧ a < x + w) := by
  rintro ⟨h1, h2⟩
  rcases h with h | h <;> omega

/-- A range every byte of which is outside a region list reads back unchanged under
a frame over that list. -/
theorem readBytes_of_outside {mem0 M : Mem} {regions : List (Nat × Nat)} {a n : Nat}
    (hframe : UnchangedOutside mem0 M regions)
    (hout : ∀ k, k < n → ∀ r ∈ regions, ¬ (r.1 ≤ a + k ∧ a + k < r.1 + r.2)) :
    readBytes M a n = readBytes mem0 a n :=
  readBytes_congr_range (m := mem0) (m' := M) (fun k hk => hframe (a + k) (hout k hk))

/-- The same, for the three regions the escape list's frame names, one fact per
region: the caller reads each region's exclusion at its own separator, so no
region-pair destructuring is needed. -/
theorem readBytes_of_outside_three {mem0 M : Mem} {a n xp w1 xn w2 carry w3 : Nat}
    (hframe : UnchangedOutside mem0 M [(xp, w1), (xn, w2), (carry, w3)])
    (h1 : ∀ k, k < n → ¬ (xp ≤ a + k ∧ a + k < xp + w1))
    (h2 : ∀ k, k < n → ¬ (xn ≤ a + k ∧ a + k < xn + w2))
    (h3 : ∀ k, k < n → ¬ (carry ≤ a + k ∧ a + k < carry + w3)) :
    readBytes M a n = readBytes mem0 a n := by
  refine readBytes_of_outside hframe (fun k hk r hr => ?_)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with h | h | h
  · simpa only [h] using h1 k hk
  · simpa only [h] using h2 k hk
  · simpa only [h] using h3 k hk

/-- **The call leaves the entry words alone.**  The unit's frame is silent outside
the three regions, and the staging separates `ent`'s `8 * blocks` bytes from each
of them, so the entry array the block staged reads back byte for byte.  This is the
fact the block's own value clause needs: its stores are what put `stage1Words`
there, and this call is not allowed to disturb them.

The stream's region here is the *touched* extent of the frame rather than the
capacity the block's staging separates at, so the separations are taken at the
touched extent; `ent_separated_of_capacity` widens a staged-capacity separation to
it. -/
theorem escapeReach_keepsEntry {blk0 : BitVec 64} {xp xn carry xn0 ent blocks : Nat}
    {position : List Nat} {carryBytes : List UInt8} {mem0 M : Mem}
    (h : EscapeReach blk0 xp xn carry xn0 position carryBytes mem0 M)
    (hentXp : ent + 8 * blocks ≤ xp ∨
      xp + 4 * (xn0 + position.length + batchReserve) ≤ ent)
    (hentXn : ent + 8 * blocks ≤ xn ∨ xn + 8 ≤ ent)
    (hentCarry : ent + 8 * blocks ≤ carry ∨ carry + 16 ≤ ent) :
    readBytes M ent (8 * blocks) = readBytes mem0 ent (8 * blocks) := by
  refine readBytes_of_outside_three (escapeReach_callRegions h) ?_ ?_ ?_
  · intro k _
    exact outside_of_separated hentXp (by omega) (by omega)
  · intro k _
    exact outside_of_separated hentXn (by omega) (by omega)
  · intro k _
    exact outside_of_separated hentCarry (by omega) (by omega)

/-! ### The stream's prefix is the caller's -/

/-- **The stream's prefix below the cursor is the caller's.**  The record's frame
starts at `xp + 4 * xn0`: every byte of the prefix `[xp, xp + 4 * xn0)` lies below
that region, and the staging orders the count's slot and the carry's away from the
stream, so none of the three regions reaches the prefix.  The prefix therefore
reads back as it was handed in. -/
theorem readBytes_prefix_of_touched {mem0 M : Mem} {xp xn carry xn0 len : Nat}
    (h : UnchangedOutside mem0 M (touchedRegions xp xn carry xn0 len))
    (hkeep : xn + 8 ≤ xp ∨ xp + 4 * blockMax xn0 ≤ xn)
    (hcx : carry + 16 ≤ xp ∨ xp + 4 * blockMax xn0 ≤ carry) :
    readBytes M xp (4 * xn0) = readBytes mem0 xp (4 * xn0) := by
  have hframe : UnchangedOutside mem0 M
      [(xp + 4 * xn0, 4 * (len + batchReserve)), (xn, 8), (carry, 16)] := by
    simpa only [touchedRegions] using h
  have hread := readBytes_of_outside_three (mem0 := mem0) (M := M)
    (a := xp) (n := 4 * xn0) (xp := xp + 4 * xn0)
    (w1 := 4 * (len + batchReserve)) (xn := xn) (w2 := 8)
    (carry := carry) (w3 := 16) hframe ?_ ?_ ?_
  · exact hread
  · intro k hk
    rintro ⟨h1, h2⟩
    omega
  · intro k hk
    rintro ⟨h1, h2⟩
    unfold blockMax batchReserve at *
    rcases hkeep with h' | h' <;> omega
  · intro k hk
    rintro ⟨h1, h2⟩
    unfold blockMax batchReserve at *
    rcases hcx with h' | h' <;> omega

/-- **The record keeps the stream's prefix**, in the shape the block module calls
`StreamPrefix`: a read of the stream below the cursor at the caller's memory is
still the read at the run's memory.  The pre-state read is the caller's staging;
the post-state read is the record's, so no call site has to assume it. -/
theorem escapeReach_streamPrefix {blk0 : BitVec 64} {xp xn carry xn0 : Nat}
    {position ps0 : List Nat} {carryBytes : List UInt8} {mem0 M : Mem}
    (h : EscapeReach blk0 xp xn carry xn0 position carryBytes mem0 M)
    (hkeep : xn + 8 ≤ xp ∨ xp + 4 * blockMax xn0 ≤ xn)
    (hcx : carry + 16 ≤ xp ∨ xp + 4 * blockMax xn0 ≤ carry)
    (hprefix : readBytes mem0 xp (4 * xn0) = some (positionsBytes 4 ps0)) :
    readBytes M xp (4 * xn0) = some (positionsBytes 4 ps0) := by
  rw [readBytes_prefix_of_touched (escapeReach_callTouched h) hkeep hcx]
  exact hprefix

/-- **A staged-capacity separation is a separation at any smaller extent.**  The
block's staging separates `ent` from the *whole* stream capacity; the call's frame
names the part this call touched, which is inside it. -/
theorem ent_separated_of_capacity {ent blocks cap cap' xp : Nat}
    (h : ent + 8 * blocks ≤ xp ∨ xp + 4 * cap ≤ ent) (hle : cap' ≤ cap) :
    ent + 8 * blocks ≤ xp ∨ xp + 4 * cap' ≤ ent := by
  rcases h with h | h
  · exact Or.inl h
  · exact Or.inr (by omega)

/-! ### The count's word, and the carry's flags

The post's witnesses are its own, not the caller's assignment of the same argument
list.  Two of its numbers are pinned by memory the caller also holds — the count by
the slot's eight bytes, and the carry's flags by the slot's sixteen — and those are
what identify them with the caller's. -/

/-- Eight bytes of a bounded value decide the value.  The slot holds `wordBytes 8
v`; two representatives below `2 ^ 64` that encode to the same word are equal. -/
theorem wordBytes_eq_of_lt {x y : Nat} (hx : x < 2 ^ 64) (hy : y < 2 ^ 64)
    (h : wordBytes 8 x = wordBytes 8 y) : x = y := by
  have h1 : x % 2 ^ 64 = y % 2 ^ 64 := by
    have := congrArg bytesToNat h
    simp only [wordBytes, natToBytes_toNat,
      show (256 : Nat) ^ 8 = 2 ^ 64 from by decide] at this
    exact this
  rwa [Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy] at h1

/-- The carry slot's sixteen bytes decide its flag pair.  The one-flag form is
proved here rather than stated: a flag is one of two eight-byte words, so the two
of them are decided by `decide` at each of the four cases. -/
theorem flagPair_inj {a b a' b' : Bool}
    (h : flagBytes a ++ flagBytes b = flagBytes a' ++ flagBytes b') :
    a = a' ∧ b = b' := by
  have hinj : ∀ {x y : Bool}, flagBytes x = flagBytes y → x = y := by
    intro x y hxy
    cases x <;> cases y <;> first | rfl | exact absurd hxy (by decide)
  have hlen : (flagBytes a).length = (flagBytes a').length := by
    simp [flagBytes, natToBytes_length]
  obtain ⟨h1, h2⟩ := List.append_inj h hlen
  exact ⟨hinj h1, hinj h2⟩

/-! ### Presence carried across the frame

The post's presence clause is the call's own capacity.  The block stages the whole
stream once and each call consumes a `blockMax` at its cursor, so the capacity has
to survive the calls it is not described by: below the post's extent it is the
post, and above it the bytes are outside the frame. -/

/-- **A present range whose bytes are outside the three regions is still
present** after the call: presence is a per-byte fact, so it travels along the
frame's byte equalities. -/
theorem hasBytes_of_outside_three {mem0 M : Mem} {a n xp w1 xn w2 carry w3 : Nat}
    (hframe : UnchangedOutside mem0 M [(xp, w1), (xn, w2), (carry, w3)])
    (h1 : ∀ k, k < n → ¬ (xp ≤ a + k ∧ a + k < xp + w1))
    (h2 : ∀ k, k < n → ¬ (xn ≤ a + k ∧ a + k < xn + w2))
    (h3 : ∀ k, k < n → ¬ (carry ≤ a + k ∧ a + k < carry + w3))
    (h : HasBytes mem0 a n) : HasBytes M a n := by
  obtain ⟨vs, hvs⟩ := h
  exact ⟨vs, by rw [readBytes_of_outside_three hframe h1 h2 h3]; exact hvs⟩

/-- A present range has each of its suffixes present. -/
theorem hasBytes_drop {m : Mem} {a K n : Nat} (h : HasBytes m a K) (hn : n ≤ K) :
    HasBytes m (a + n) (K - n) := by
  obtain ⟨vs, hvs⟩ := h
  have hK : K = n + (K - n) := by omega
  rw [hK] at hvs
  exact ⟨_, (readBytes_split m a n (K - n) hvs).2⟩

/-- Two adjacent present ranges make their union present. -/
theorem hasBytes_append {m : Mem} {a n k : Nat} (h1 : HasBytes m a n)
    (h2 : HasBytes m (a + n) k) : HasBytes m a (n + k) := by
  obtain ⟨v1, hv1⟩ := h1
  obtain ⟨v2, hv2⟩ := h2
  exact ⟨v1 ++ v2, readBytes_append m n a v1 k v2 hv1 hv2⟩

/-- **The staged capacity survives the call.**  The post restates presence at
`blockMax xn0`, this call's own extent; the next call's `pre` wants the capacity at
its own count.  Below the post's extent the bytes are present by the post, and
between there and the staged capacity they are outside the frame, so they read as
the caller staged them.  The separations are the staging's, at the *whole* extent
the capacity is claimed over — that ordering is what puts the count's slot and the
carry outside the bytes this argument reads. -/
theorem escape_call_capacity {mem0 M : Mem} {xp xn carry xn0 len : Nat}
    (hframe : UnchangedOutside mem0 M (escapeCallRegions xp xn carry (xn0 + len)))
    (hpres : HasBytes M xp (4 * blockMax xn0))
    (hlen : len ≤ 64)
    (hkeep : xn + 8 ≤ xp ∨ xp + 4 * blockMax (xn0 + len) ≤ xn)
    (hcx : carry + 16 ≤ xp ∨ xp + 4 * blockMax (xn0 + len) ≤ carry)
    (hstaged : HasBytes mem0 xp (4 * blockMax (xn0 + len))) :
    HasBytes M xp (4 * blockMax (xn0 + len)) := by
  -- the post's extent is inside the one this reads
  have hn0 : 4 * blockMax xn0 ≤ 4 * blockMax (xn0 + len) := by
    unfold blockMax; omega
  -- the tail, read at the frame
  have hstream : 4 * (xn0 + len + batchReserve) ≤ 4 * blockMax xn0 := by
    unfold blockMax batchReserve
    omega
  have htail : HasBytes M (xp + 4 * blockMax xn0) (4 * blockMax (xn0 + len) -
      4 * blockMax xn0) := by
    have hsuf : HasBytes mem0 (xp + 4 * blockMax xn0)
        (4 * blockMax (xn0 + len) - 4 * blockMax xn0) := hasBytes_drop hstaged hn0
    refine hasBytes_of_outside_three hframe ?_ ?_ ?_ hsuf
    · intro k _
      rintro ⟨h1, h2⟩
      omega
    · intro k _
      rintro ⟨h1, h2⟩
      rcases hkeep with h | h <;> omega
    · intro k _
      rintro ⟨h1, h2⟩
      rcases hcx with h | h <;> omega
  -- and the head is the post's own
  have hhead : HasBytes M xp (4 * blockMax xn0) := hpres
  have hcat := hasBytes_append hhead htail
  rwa [show 4 * blockMax xn0 + (4 * blockMax (xn0 + len) - 4 * blockMax xn0) =
    4 * blockMax (xn0 + len) from by omega] at hcat

/-- The three-region frame widens to the block's four-region list by inclusion
alone: the entry array is one more region the block's post permits a change in. -/
theorem escapeReach_writeRegions_of_frame {mem0 M : Mem} {xp xn carry ent blocks nxp' : Nat}
    (h : UnchangedOutside mem0 M (escapeCallRegions xp xn carry nxp')) :
    UnchangedOutside mem0 M (escapeCallWriteRegions ent blocks xp xn carry nxp') :=
  UnchangedOutside.widen h (fun _ ha r hr => ha r (List.mem_cons_of_mem _ hr))

/-! ### The call

The block's environment leaves `leanllvm_json_escape_list` unresolved, so the
trace runs it at the caller's selection.  `CallSatisfies` is the hypothesis that
selection's record gives a call site — the record's `pre` in, its `post` out, at
the outcome the selection answers — and everything below is read out of that post.

The argument list is the unit's own, `[bs, ctl, im, blk0, xp, xn, carry]`: the
block's three mask words, the block's own index, the stream and count cursors, and
the carry slot.  `sym` is the symbol the caller's selection resolves at, and
`escapeListFunction.name` is what the emitted body calls, so
`escape_call_at_unit` below is the same theorem with the selection discharged at
the pinned body. -/

/-- **The escape list's per-call contract, at the block's own numbers.**

At the call's argument list and a staging `Γ_escape_positions.pre` admits, the
call resolves at the caller's selection and what comes back is:

* the count, at the caller's own `xn0` plus the block's position count;
* the segment this block wrote, at the caller's own cursor and count;
* the carry pair the run stores;
* the capacity the caller staged, restated;
* **the frame**: every byte outside the block's write regions is the caller's, and
  the entry words themselves read back unchanged;
* **the prefix**: the stream below this call's cursor is untouched, so it reads as
  the caller staged it — the record's frame starts at the cursor, and the prefix is
  outside it;
* the allocator's cursor, which does not shrink.

`position` is the block's own position list, taken as the lanes of the word the
list body reads (`hpos`); `hbs`/`hctl`/`him`/`hpair` are the unit's `pre` at the
block's masks, and `hentXp`/`hentXn`/`hentCarry` are the staging's separations of
the entry array from the three regions.  The count's bound `hxn0` is the unit's
`pre`; the *next* call's bound on `xn0 + position.length` is not derivable from
this record and stays the caller's. -/
theorem escape_call_at {sym : String} {esc : Calls} {base : Nat}
    (hEsc : CallSatisfies esc (Γ_escape_positions base escapePositionsBudget) sym)
    {xp xn carry ent blocks next xn0 : Nat}
    {blk0 bs ctl im : BitVec 64} {lo hi : Block32} {st : ClassState}
    {prevb prevs : Bool} {mem : Mem} {position : List Nat}
    (hblock : readBytes mem (base + blockAddr blk0) 64 = some (block64 lo hi))
    (hbs : bs = specBackslash64 lo hi st)
    (hctl : ctl = specControl64 lo hi st)
    (him : im = specInString64 lo hi st)
    (hpair : carryPair mem carry st prevb prevs)
    (hcount : readBytes mem xn 8 = some (wordBytes 8 xn0))
    (hxn0 : xn0 < 2 ^ 63)
    (hkeep : xn + 8 ≤ xp ∨ xp + 4 * blockMax xn0 ≤ xn)
    (hcarr : carry + 16 ≤ xn ∨ xn + 8 ≤ carry)
    (hcx : carry + 16 ≤ xp ∨ xp + 4 * blockMax xn0 ≤ carry)
    (hhas : HasBytes mem xp (4 * blockMax xn0))
    (hblkcap : blk0.toNat * 64 + 64 < 2 ^ 32)
    (hpos : position = setLanes (lxWord ctl im (specRunStarts bs (prevb && prevs))))
    (hentXp : ent + 8 * blocks ≤ xp ∨ xp + 4 * blockMax xn0 ≤ ent)
    (hentXn : ent + 8 * blocks ≤ xn ∨ xn + 8 ≤ ent)
    (hentCarry : ent + 8 * blocks ≤ carry ∨ carry + 16 ≤ ent) :
    ∃ r : CallOutcome,
      esc sym [.int 64 bs, .int 64 ctl, .int 64 im, .int 64 blk0, .ptr xp, .ptr xn,
          .ptr carry] mem next = some r ∧
      readBytes r.mem xn 8 = some (wordBytes 8 (xn0 + position.length)) ∧
      (∃ ps : List Nat, readBytes r.mem (xp + 4 * xn0) (4 * position.length) =
        some (positionsBytes 4 ps)) ∧
      (∃ (st' : ClassState) (prevb' prevs' : Bool),
        carryPair r.mem carry st' prevb' prevs') ∧
      HasBytes r.mem xp (4 * blockMax xn0) ∧
      UnchangedOutside mem r.mem
        (escapeCallWriteRegions ent blocks xp xn carry (xn0 + position.length)) ∧
      readBytes r.mem ent (8 * blocks) = readBytes mem ent (8 * blocks) ∧
      readBytes r.mem xp (4 * xn0) = readBytes mem xp (4 * xn0) ∧
      next ≤ r.next := by
  -- the record's pre, at the call's argument list
  have hpre : (Γ_escape_positions base escapePositionsBudget).pre
      [.int 64 bs, .int 64 ctl, .int 64 im, .int 64 blk0, .ptr xp, .ptr xn,
        .ptr carry] mem next :=
    ⟨xp, xn, carry, blk0, bs, ctl, im, lo, hi, st, prevb, prevs, xn0, rfl, hblock,
      hbs, hctl, him, hpair, hcount, hxn0, hkeep, hcarr, hcx, hhas, hblkcap⟩
  obtain ⟨r, hcall, hpost, hnext⟩ := hEsc _ mem next hpre
  have hpost' : escapePositionsPost base
      [.int 64 bs, .int 64 ctl, .int 64 im, .int 64 blk0, .ptr xp, .ptr xn,
        .ptr carry] mem r.mem := hpost
  obtain ⟨xp', xn', carry', blk0', bs', ctl', im', lo', hi', st', prevb', prevs', xn0',
    hargs, hblock', hbs', hctl', him', hpairIn, hcntIn, hxn0', hcntOut, hposOut,
    hpairOut, hhasOut, hframeOut⟩ := hpost'
  -- the post's witnesses are the call's arguments.  The pointers are ordinary
  -- equalities; the masks and the block index are `Value.int 64` fields, whose
  -- equality is heterogeneous because the width is an index (and the width is the
  -- same literal on both sides).
  simp only [List.cons.injEq, and_true, true_and, Value.ptr.injEq, Value.int.injEq]
    at hargs
  obtain ⟨hbsE, hctlE, himE, hblk0E, hxpE, hxnE, hcarryE⟩ := hargs
  have hbsEq : bs' = bs := (eq_of_heq hbsE).symm
  have hctlEq : ctl' = ctl := (eq_of_heq hctlE).symm
  have himEq : im' = im := (eq_of_heq himE).symm
  have _hblkEq : blk0' = blk0 := (eq_of_heq hblk0E).symm
  have hxpEq : xp' = xp := hxpE.symm
  have hxnEq : xn' = xn := hxnE.symm
  have hcarryEq : carry' = carry := hcarryE.symm
  -- the post's clauses, read at the call's own numbers
  have hpairIn' : carryPair mem carry st' prevb' prevs' := by
    rw [← hcarryEq]
    exact hpairIn
  have hcntIn' : readBytes mem xn 8 = some (wordBytes 8 xn0') := by
    rw [← hxnEq]
    exact hcntIn
  -- the count: both reads are the same slot, and both representatives are bounded
  have hxn0Eq : xn0' = xn0 := by
    have hw : wordBytes 8 xn0' = wordBytes 8 xn0 :=
      Option.some.inj (hcntIn'.symm.trans hcount)
    exact wordBytes_eq_of_lt hxn0' (by omega) hw
  -- the carry's flags: both pairs are the same sixteen bytes
  have hflags : prevb' = prevb ∧ prevs' = prevs := by
    have hbytes : flagBytes prevb' ++ flagBytes prevs' =
        flagBytes prevb ++ flagBytes prevs :=
      Option.some.inj (hpairIn'.1.symm.trans hpair.1)
    exact flagPair_inj hbytes
  obtain ⟨hprevb, hprevs⟩ := hflags
  have hodd : st'.oddRun = (prevb && prevs) := hpairIn'.2.trans (by rw [hprevb, hprevs])
  -- the post's mask clauses, read as the caller's masks: the arguments are the
  -- post's own, and its clause is stated at its witnesses
  have hbsP : bs = specBackslash64 lo' hi' st' := hbsEq.symm.trans hbs'
  have hctlP : ctl = specControl64 lo' hi' st' := hctlEq.symm.trans hctl'
  have himP : im = specInString64 lo' hi' st' := himEq.symm.trans him'
  -- the position list, at the post's own block and state
  have hposBlock : position = setLanes (lxWord (specControl64 lo' hi' st')
      (specInString64 lo' hi' st')
      (specRunStarts (specBackslash64 lo' hi' st') st'.oddRun)) := by
    rw [hpos, hbsP, hctlP, himP, ← hodd]
  -- the block's position count: the post's own is the word's population count
  have hctp' : ctpop (lxWord (specControl64 lo' hi' st') (specInString64 lo' hi' st')
      (specRunStarts (specBackslash64 lo' hi' st') st'.oddRun)) = position.length := by
    rw [hposBlock, ctpop_eq_setLanes_length]
  have hlen' : (escapePositionsFrom (block64 lo' hi') st').length = position.length :=
    (ctpop_lxWord_positionWord (lo := lo') (hi := hi') (st := st')).symm.trans hctp'
  have hctp : ctpop (lxWord ctl im (specRunStarts bs (prevb && prevs))) =
      position.length := by
    rw [hpos, ctpop_eq_setLanes_length]
  have hlen64 : position.length ≤ 64 := by
    rw [← hctp]
    exact ctpop_le _
  -- the frame, at the cursor-based extent the run's stores reached
  have hframeTouched : UnchangedOutside mem r.mem
      (touchedRegions xp xn carry xn0 position.length) := by
    have h := hframeOut
    rw [hxn0Eq, hlen', hxpEq, hxnEq, hcarryEq] at h
    exact h
  -- and its widening, at the block's three regions
  have hframe : UnchangedOutside mem r.mem
      (escapeCallRegions xp xn carry (xn0 + position.length)) :=
    touchedRegions_to_callRegions hframeTouched
  refine ⟨r, hcall, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hnext⟩
  · -- the count, at the caller's count and the block's position count
    rw [← hxnEq, ← hxn0Eq, ← hlen']
    exact hcntOut
  · -- the segment this block wrote, at the caller's cursor
    refine ⟨blockPositions blk0' lo' hi' st', ?_⟩
    rw [← hxpEq, ← hxn0Eq, ← hlen']
    exact hposOut
  · -- the carry pair the run stores
    refine ⟨carry64 lo' hi' st', IsBackslashB (hi' ⟨31, by decide⟩),
      (carry64 lo' hi' st').oddRun, ?_⟩
    rw [← hcarryEq]
    exact hpairOut
  · -- the capacity the caller staged, restated
    rw [← hxpEq, ← hxn0Eq]
    exact hhasOut
  · exact escapeReach_writeRegions_of_frame hframe
  · -- the entry words, outside the frame's three regions
    have hentXp' : ent + 8 * blocks ≤ xp ∨
        xp + 4 * (xn0 + position.length + batchReserve) ≤ ent :=
      ent_separated_of_capacity hentXp (by unfold blockMax batchReserve; omega)
    refine readBytes_of_outside_three hframe ?_ ?_ ?_
    · intro k _
      exact outside_of_separated hentXp' (by omega) (by omega)
    · intro k _
      exact outside_of_separated hentXn (by omega) (by omega)
    · intro k _
      exact outside_of_separated hentCarry (by omega) (by omega)
  · -- the stream's prefix, below the cursor
    exact readBytes_prefix_of_touched hframeTouched hkeep hcx

/-! ### At the pinned body -/

/-- The escape list's selection at its own pinned body: the unit's record read as a
call entry, at the symbol the emitted body calls.  A caller that wants the unit's
own guarantee rather than an arbitrary selection's uses this environment. -/
def escapeListUnitCalls (base : Nat) : Calls :=
  envForUnit escapeListFunction.name (Γ_escape_positions base escapePositionsBudget)
    (escapeListCalls Γ_xl_batch) escapeListFunction

/-- **The per-call hypothesis, discharged.**  `CallSatisfies` at the pinned body is
`escape_positions_satisfies` through the void-return bridge: the record's
`Satisfies` instance fixes the run's outcome at the record's budget, and
`ValueIrrelevant` is what lets a void return answer a `CallOutcome`.  So the
selection a block carries is the unit itself, and no fact about
`leanllvm_json_escape_list` is assumed. -/
theorem escapeListUnitCalls_callSatisfies (base : Nat) :
    CallSatisfies (escapeListUnitCalls base)
      (Γ_escape_positions base escapePositionsBudget) escapeListFunction.name :=
  satisfies_calls_void (calls := escapeListCalls Γ_xl_batch)
    (body := escapeListFunction) (Γ := Γ_escape_positions base escapePositionsBudget)
    (sym := escapeListFunction.name) (escape_positions_satisfies base)
    (escape_positions_valueIrrelevant base escapePositionsBudget)

/-- **The same contract at the unit's own body.**  `escape_call_at` with the call
entry supplied by `escapeListUnitCalls_callSatisfies`, so the premises are the
unit's `pre` and the staging's separations, and nothing about the escape list is
hypothesised. -/
theorem escape_call_at_unit {base : Nat}
    {xp xn carry ent blocks next xn0 : Nat}
    {blk0 bs ctl im : BitVec 64} {lo hi : Block32} {st : ClassState}
    {prevb prevs : Bool} {mem : Mem} {position : List Nat}
    (hblock : readBytes mem (base + blockAddr blk0) 64 = some (block64 lo hi))
    (hbs : bs = specBackslash64 lo hi st)
    (hctl : ctl = specControl64 lo hi st)
    (him : im = specInString64 lo hi st)
    (hpair : carryPair mem carry st prevb prevs)
    (hcount : readBytes mem xn 8 = some (wordBytes 8 xn0))
    (hxn0 : xn0 < 2 ^ 63)
    (hkeep : xn + 8 ≤ xp ∨ xp + 4 * blockMax xn0 ≤ xn)
    (hcarr : carry + 16 ≤ xn ∨ xn + 8 ≤ carry)
    (hcx : carry + 16 ≤ xp ∨ xp + 4 * blockMax xn0 ≤ carry)
    (hhas : HasBytes mem xp (4 * blockMax xn0))
    (hblkcap : blk0.toNat * 64 + 64 < 2 ^ 32)
    (hpos : position = setLanes (lxWord ctl im (specRunStarts bs (prevb && prevs))))
    (hentXp : ent + 8 * blocks ≤ xp ∨ xp + 4 * blockMax xn0 ≤ ent)
    (hentXn : ent + 8 * blocks ≤ xn ∨ xn + 8 ≤ ent)
    (hentCarry : ent + 8 * blocks ≤ carry ∨ carry + 16 ≤ ent) :
    ∃ r : CallOutcome,
      escapeListUnitCalls base escapeListFunction.name
        [.int 64 bs, .int 64 ctl, .int 64 im, .int 64 blk0, .ptr xp, .ptr xn,
          .ptr carry] mem next = some r ∧
      readBytes r.mem xn 8 = some (wordBytes 8 (xn0 + position.length)) ∧
      (∃ ps : List Nat, readBytes r.mem (xp + 4 * xn0) (4 * position.length) =
        some (positionsBytes 4 ps)) ∧
      (∃ (st' : ClassState) (prevb' prevs' : Bool),
        carryPair r.mem carry st' prevb' prevs') ∧
      HasBytes r.mem xp (4 * blockMax xn0) ∧
      UnchangedOutside mem r.mem
        (escapeCallWriteRegions ent blocks xp xn carry (xn0 + position.length)) ∧
      readBytes r.mem ent (8 * blocks) = readBytes mem ent (8 * blocks) ∧
      readBytes r.mem xp (4 * xn0) = readBytes mem xp (4 * xn0) ∧
      next ≤ r.next :=
  escape_call_at (escapeListUnitCalls_callSatisfies base) hblock hbs hctl him hpair
    hcount hxn0 hkeep hcarr hcx hhas hblkcap hpos hentXp hentXn hentCarry

/-- The emitted body calls the list at its pinned name. -/
example : escapeListFunction.name = "leanllvm_json_escape_list" := rfl

/-! ### Axiom footprints

The region restatements and the widening are arithmetic and definitional.  The
call's clauses read the unit's post, so they carry whatever
`escape_positions_satisfies` carries; the parametric theorem adds nothing of its
own. -/

#print axioms escapeReach_callTouched
#print axioms touchedRegions_to_callRegions
#print axioms escapeReach_callRegions
#print axioms readBytes_prefix_of_touched
#print axioms escapeReach_streamPrefix
#print axioms escapeReach_keepsEntry
#print axioms readBytes_of_outside_three
#print axioms hasBytes_of_outside_three
#print axioms escape_call_capacity
#print axioms escape_call_at
#print axioms escapeListUnitCalls_callSatisfies
#print axioms escape_call_at_unit

end LeanLLVM.Refinement
