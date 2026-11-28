/-
# `[1]`'s caller result, from the staged entry

`evb_caller_result` (`JsonEventCallerResult`) reaches the public result from five
counted segments, the carry equations and the merge's readings.  This module
produces those from the entry's own staging: the seed's memory is the entry
block's store fold (`walkEntryMem`), and everything after it — the opener, the
first header pass, the numeral's revolution, the second header pass and the
closing bracket's merge — is run here at the states that fold writes.

## What a caller supplies

1. **The call's layout** (`routePre`, the stage-2 unit's own buffers, the staged
   event cursor) — `evb_caller_result`'s first group.
2. **The staged entry**: the seed's invariant and the equation
   `s₀.mem = walkEntryMem G S`, i.e. the entry block's initialisation, cursor
   record, log and the two zeroed slots, written out.
3. **The document**: `[1]`'s bytes, its three lane positions and its entry count.

Nothing else.  In particular the two words the seam reads from inside the cursor
record — its base and its error pointer — are *derived*: the entry writes them at
`%c.i + 0` and `%c.i + 1112`, and every store the walk makes afterwards (the
opener's tag and stacks, the header's `%c.i + 32`, the scalar route's token
record, and the `if.then413.i` kind store) misses them by the staging's own
`DisjointRegions`.  The numeral's record is derived from the delivered window by
`s2ScalarValue_numberAppend`, not assumed.

## The two rows beside the staged writes

`WalkInv` carries the cursor record's address and presence, not the words inside
it, so the base and the error pointer are read off `walkEntryMem` here: the
segment-3 stores put `G.b` and `S.e` at those two addresses, and the four stores
above are peeled one at a time.  The root slot's word is the segment-4 zero.


## The refusal record's width

`HcontSeamStage.heErr` needs the cursor record's error word to be `S.e`.  The
entry's third segment stores `natToBytes S.e 8` at `%c.i + 1112`, so the word
reads back as `S.e` only when `S.e < 2 ^ 64`; without the bound it is
`S.e mod 2 ^ 64`, and the copy call's frame region `(e, stage2ErrorExtent)`
(`s2ScalarValueFoot`) can move off the object `seamCtypeByte_err_sep` reasons
about.  The width is a clause of the staging and not a hypothesis of the seam's
row:

* `stage2Pre` states `err < 2 ^ 64` in its address-word group, beside `b`, `ep`,
  `dst` and `ev`.  `pipelineStaging` carries the same clause for the slot the
  wrapper passes, `routePre` states it for the layout's `err`, and
  `layoutRefusal` checks it, so every caller the route admits has it;
* `stage2StagedPre` states `e < 2 ^ 64` for the appended refusal record — the
  object the entry writes into the error word — and that is the clause the walk
  reads;
* `WalkGeom` and `Stage2Run` carry `errLt`, supplied by `WalkGeom.nonempty`,
  `walkGeom_at_pre` and `Stage2Run.ofInv`, and `Stage2Run.pre` passes it back to
  the record's precondition;
* `WalkStage.eLt` is the staged clause at the walk's staging, supplied by
  `walkStage_at_pre` and `walkStage_at_pre_fields`;
* `natToBytes8_readWord` turns the entry's byte read into the word the scalar
  call reads; `evbStagedErrWord` is that at the entry,
  `seamKindStore_err_readWord` carries it to the seam's kind store, and
  `evbSeamErrWord` states `HcontSeamStage.heErr` at the staged entry.

The document's five-byte window at the call is likewise a row here: the document
read plus the staged read-past tail, carried across the seam's token stores.
There is no `sorry`, `admit` or `native_decide`.
-/
import LeanLLVM.Refinement.JsonEventCallerResult
import LeanLLVM.Refinement.JsonEventCallerResultPrefix
import LeanLLVM.Refinement.JsonEventCallerResultNumeral
import LeanLLVM.Refinement.JsonEventCallerResultSeamLexeme
import LeanLLVM.Refinement.JsonEventCallerResultCloserTerm
import LeanLLVM.Refinement.JsonStage2WalkDispatchScalarRows
import LeanLLVM.Refinement.JsonStage2WalkDispatchResidual
import LeanLLVM.Refinement.JsonStage2WalkPrefixCount
import LeanLLVM.Refinement.JsonStage2WalkSeedRun
import LeanLLVM.Refinement.JsonStage2WalkDispatchSeamCalls

set_option autoImplicit false

namespace LeanLLVM.Refinement
namespace WalkScope

open LeanLLVM
open LeanLLVM.JSON
open LeanLLVM.Refinement.JsonStage2IR
open LeanLLVM.Refinement.JsonEntryIR (readLanes32)
open LeanLLVM.Refinement.BlockEval

/-! ### `[1]`'s document -/

/-- `[1]`'s first entry is its first byte. -/
theorem evbPos_zero {m0 : Mem} {G : WalkGeom m0} (hent : G.ent = [0, 1, 2]) :
    entryPos G 0 = 0 := by
  simp only [entryPos, hent]
  rfl

/-- `[1]`'s second entry is its second byte. -/
theorem evbPos_one {m0 : Mem} {G : WalkGeom m0} (hent : G.ent = [0, 1, 2]) :
    entryPos G 1 = 1 := by
  simp only [entryPos, hent]
  rfl

/-- `[1]`'s third entry is its third byte. -/
theorem evbPos_two {m0 : Mem} {G : WalkGeom m0} (hent : G.ent = [0, 1, 2]) :
    entryPos G 2 = 2 := by
  simp only [entryPos, hent]
  rfl

/-- The document's first byte is `[`. -/
theorem evbByte_zero {m0 : Mem} {G : WalkGeom m0} (hbs : G.bs = evbDoc)
    (hent : G.ent = [0, 1, 2]) : entryByte G 0 = 0x5B := by
  simp only [entryByte, evbPos_zero hent, hbs, evbDoc]
  rfl

/-- The document's second byte is `1`. -/
theorem evbByte_one {m0 : Mem} {G : WalkGeom m0} (hbs : G.bs = evbDoc)
    (hent : G.ent = [0, 1, 2]) : entryByte G 1 = 0x31 := by
  simp only [entryByte, evbPos_one hent, hbs, evbDoc]
  rfl

/-- The document's third byte is `]`. -/
theorem evbByte_two {m0 : Mem} {G : WalkGeom m0} (hbs : G.bs = evbDoc)
    (hent : G.ent = [0, 1, 2]) : entryByte G 2 = 0x5D := by
  simp only [entryByte, evbPos_two hent, hbs, evbDoc]
  rfl

/-- The byte before the flag entry's end, as `contB35` names it. -/
theorem evbContB35 {m0 : Mem} {G : WalkGeom m0} (hbs : G.bs = evbDoc) :
    contB35 G (BitVec.ofNat 32 2) = 0x31 := by
  simp only [contB35, BitVec.toNat_ofNat, hbs, evbDoc]
  rfl

/-- The class of the byte before the entry's end at `1`: the high leaf. -/
def evbHb : HcontByteRoute (cont35 (0x31 : UInt8)) := by
  refine HcontByteRoute.highLeaf ?_ ?_ ?_
  · decide
  · decide
  · decide

/-! ### The entry's stores, read back

The cursor record's store list is split at the store each read names; the two
zeroed slots and the header's `%c.i + 32` store miss it by their extents. -/

/-- The base word the entry stages: `%c.i`'s first store. -/
theorem walkSeg3_read_c {m : Mem} (b n ep nep eAddr cAddr : Nat) :
    readBytes (walkSeg3PostMem b n ep nep eAddr cAddr m) cAddr 8 =
      some (natToBytes b 8) := by
  rw [walkSeg3PostMem, walkSeg3Stores]
  simp only [woff_40, woff_8, woff_16, woff_24, woff_1112]
  have hpost : ∀ st ∈ [(cAddr + 8, natToBytes n 8), (cAddr + 16, natToBytes ep 8),
      (cAddr + 24, natToBytes nep 8), (cAddr + 1112, natToBytes eAddr 8)],
      cAddr + (natToBytes b 8).length ≤ st.1 ∨ st.1 + st.2.length ≤ cAddr := by
    intro st hst
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hst
    rcases hst with rfl | rfl | rfl | rfl
    · exact Or.inl (by rw [natToBytes_length]; try (show cAddr + 8 ≤ cAddr + 8; omega))
    · exact Or.inl (by rw [natToBytes_length]; try (show cAddr + 8 ≤ cAddr + 16; omega))
    · exact Or.inl (by rw [natToBytes_length]; try (show cAddr + 8 ≤ cAddr + 24; omega))
    · exact Or.inl (by rw [natToBytes_length]; try (show cAddr + 8 ≤ cAddr + 1112; omega))
  rw [show ([(cAddr + 40, List.replicate 1152 0), (cAddr, natToBytes b 8),
      (cAddr + 8, natToBytes n 8), (cAddr + 16, natToBytes ep 8),
      (cAddr + 24, natToBytes nep 8), (cAddr + 1112, natToBytes eAddr 8)] : List (Nat × List UInt8))
      = [(cAddr + 40, List.replicate 1152 0)] ++ (cAddr, natToBytes b 8) ::
        [(cAddr + 8, natToBytes n 8), (cAddr + 16, natToBytes ep 8),
          (cAddr + 24, natToBytes nep 8), (cAddr + 1112, natToBytes eAddr 8)] from rfl]
  exact readBytes_stage2WriteStores_at m [(cAddr + 40, List.replicate 1152 0)]
    [(cAddr + 8, natToBytes n 8), (cAddr + 16, natToBytes ep 8),
      (cAddr + 24, natToBytes nep 8), (cAddr + 1112, natToBytes eAddr 8)]
    cAddr (natToBytes b 8) hpost

/-- The error pointer the entry stages: `%c.i + 1112`'s store. -/
theorem walkSeg3_read_e {m : Mem} (b n ep nep eAddr cAddr : Nat) :
    readBytes (walkSeg3PostMem b n ep nep eAddr cAddr m) (cAddr + 1112) 8 =
      some (natToBytes eAddr 8) := by
  rw [walkSeg3PostMem, walkSeg3Stores]
  simp only [woff_40, woff_8, woff_16, woff_24, woff_1112]
  have hpost : ∀ st ∈ ([] : List (Nat × List UInt8)),
      cAddr + 1112 + (natToBytes eAddr 8).length ≤ st.1 ∨ st.1 + st.2.length ≤ cAddr + 1112 := by
    intro st hst
    exact absurd hst (by simp)
  rw [show ([(cAddr + 40, List.replicate 1152 0), (cAddr, natToBytes b 8),
      (cAddr + 8, natToBytes n 8), (cAddr + 16, natToBytes ep 8),
      (cAddr + 24, natToBytes nep 8), (cAddr + 1112, natToBytes eAddr 8)] : List (Nat × List UInt8))
      = [(cAddr + 40, List.replicate 1152 0), (cAddr, natToBytes b 8),
        (cAddr + 8, natToBytes n 8), (cAddr + 16, natToBytes ep 8),
        (cAddr + 24, natToBytes nep 8)] ++
        (cAddr + 1112, natToBytes eAddr 8) :: [] from rfl]
  exact readBytes_stage2WriteStores_at m [(cAddr + 40, List.replicate 1152 0),
      (cAddr, natToBytes b 8), (cAddr + 8, natToBytes n 8), (cAddr + 16, natToBytes ep 8),
      (cAddr + 24, natToBytes nep 8)] [] (cAddr + 1112) (natToBytes eAddr 8) hpost

/-- The root slot's word the entry stages: segment 4's first store. -/
theorem walkSeg4_read_root {m : Mem} (root xj : Nat)
    (hsep : root + 4 ≤ xj ∨ xj + (natToBytes 0 8).length ≤ root) :
    readBytes (walkSeg4PostMem root xj m) root 4 = some (natToBytes 0 4) := by
  rw [walkSeg4PostMem]
  rw [walkReadBytes_writeBytes_outside (start := xj) (v := natToBytes 0 8) hsep]
  simpa only [natToBytes_length] using readBytes_writeBytes_same m (natToBytes 0 4)

/-- **The staged base word.**  The seed's memory is the entry's fold, and its
`%c.i` word is the document's base. -/
theorem evbStagedBase {m0 : Mem} {G : WalkGeom m0} {S : WalkStage G} {s₀ : State}
    (hmem : s₀.mem = walkEntryMem G S) :
    readBytes s₀.mem S.c 8 = some (natToBytes G.b 8) := by
  have hcw : S.c + 1192 ≤ G.next0 := by
    have h := S.sevenEnd (S.c, stage2CursorExtent) (by simp [stage2StagedWrites])
    simpa only [stage2CursorExtent] using h
  rw [hmem, walkEntryMem]
  rw [walkReadBytes_writeBytes_outside (start := S.c + 32) (v := wordBytes 8 1) (by
    rw [wordBytes, natToBytes_length]; omega)]
  rw [walkSeg4PostMem]
  rw [walkReadBytes_writeBytes_outside (start := G.next0 + 12) (v := natToBytes 0 8) (by
    rw [natToBytes_length]; omega)]
  rw [walkReadBytes_writeBytes_outside (start := G.next0 + 8) (v := natToBytes 0 4) (by
    rw [natToBytes_length]; omega)]
  exact walkSeg3_read_c G.b G.n G.ep G.nep S.e S.c

/-- **The staged error pointer.** -/
theorem evbStagedErr {m0 : Mem} {G : WalkGeom m0} {S : WalkStage G} {s₀ : State}
    (hmem : s₀.mem = walkEntryMem G S) :
    readBytes s₀.mem (S.c + 1112) 8 = some (natToBytes S.e 8) := by
  have hcw : S.c + 1192 ≤ G.next0 := by
    have h := S.sevenEnd (S.c, stage2CursorExtent) (by simp [stage2StagedWrites])
    simpa only [stage2CursorExtent] using h
  rw [hmem, walkEntryMem]
  rw [walkReadBytes_writeBytes_outside (start := S.c + 32) (v := wordBytes 8 1) (by
    rw [wordBytes, natToBytes_length]; omega)]
  rw [walkSeg4PostMem]
  rw [walkReadBytes_writeBytes_outside (start := G.next0 + 12) (v := natToBytes 0 8) (by
    rw [natToBytes_length]; omega)]
  rw [walkReadBytes_writeBytes_outside (start := G.next0 + 8) (v := natToBytes 0 4) (by
    rw [natToBytes_length]; omega)]
  exact walkSeg3_read_e G.b G.n G.ep G.nep S.e S.c

/-- **The staged root word.**  The two zeroed slots are the entry's, and the slot
`%root_done.i` names is the first. -/
theorem evbStagedRoot {m0 : Mem} {G : WalkGeom m0} {S : WalkStage G} {s₀ : State}
    (hmem : s₀.mem = walkEntryMem G S) :
    readBytes s₀.mem (G.next0 + 8) 4 = some (natToBytes 0 4) := by
  have hcw : S.c + 1192 ≤ G.next0 := by
    have h := S.sevenEnd (S.c, stage2CursorExtent) (by simp [stage2StagedWrites])
    simpa only [stage2CursorExtent] using h
  rw [hmem, walkEntryMem]
  rw [walkReadBytes_writeBytes_outside (start := S.c + 32) (v := wordBytes 8 1) (by
    rw [wordBytes, natToBytes_length]; omega)]
  exact walkSeg4_read_root (G.next0 + 8) (G.next0 + 12) (Or.inl (by omega))

/-! ### Separation, from the staging's own list -/

/-- A disjunction's two halves, commuted. -/
theorem evbOrComm {p q : Prop} (h : p ∨ q) : q ∨ p := h.elim Or.inr Or.inl

/-- **Eight bytes written as a word decode to their number.**  `stage2ReadWord` is
the read and `bytesToNat`; `natToBytes` of a number below `2 ^ 64` is that
number's little-endian eight bytes, and `bytesToNat` recovers it exactly at the
width.  This is the step from a byte-level read to the word-level one the
scalar call's staging states. -/
theorem natToBytes8_readWord {m : Mem} {a x : Nat}
    (h : readBytes m a 8 = some (natToBytes x 8)) (hx : x < 2 ^ 64) :
    stage2ReadWord m a 8 = some x := by
  have hb : bytesToNat (natToBytes x 8) = x := by
    rw [natToBytes_toNat, show (256 : Nat) ^ 8 = 2 ^ 64 from by decide,
      Nat.mod_eq_of_lt hx]
  show (readBytes m a 8).map bytesToNat = _
  rw [h]
  simp only [hb, Option.map]

/-- The token record and the cursor record are separate. -/
theorem evbTokCursor {m0 : Mem} {G : WalkGeom m0} (S : WalkStage G) :
    S.tok + stage2TokenExtent ≤ S.c ∨ S.c + stage2CursorExtent ≤ S.tok :=
  evbOrComm (stagedWrites_sep S.writes_separate (i := 0) (j := 3)
    (by decide) (by decide) (by decide))

/-- A container stack and the cursor record are separate. -/
theorem evbStackCursor {m0 : Mem} {G : WalkGeom m0} (S : WalkStage G) {base : Nat}
    (hb : base = S.ctype ∨ base = S.cst) :
    base + stage2StackExtent ≤ S.c ∨ S.c + stage2CursorExtent ≤ base := by
  rcases hb with rfl | rfl
  · exact evbOrComm (stagedWrites_sep S.writes_separate (i := 0) (j := 1)
      (by decide) (by decide) (by decide))
  · exact evbOrComm (stagedWrites_sep S.writes_separate (i := 0) (j := 2)
      (by decide) (by decide) (by decide))

/-- The token record and a container stack are separate. -/
theorem evbTokStackSep {m0 : Mem} {G : WalkGeom m0} (S : WalkStage G) {base : Nat}
    (hb : base = S.ctype ∨ base = S.cst) :
    S.tok + stage2TokenExtent ≤ base ∨ base + stage2StackExtent ≤ S.tok := by
  rcases hb with rfl | rfl
  · exact evbOrComm (stagedWrites_sep S.writes_separate (i := 1) (j := 3)
      (by decide) (by decide) (by decide))
  · exact evbOrComm (stagedWrites_sep S.writes_separate (i := 2) (j := 3)
      (by decide) (by decide) (by decide))

/-- The token record and the log are separate. -/
theorem evbTokLogSep {m0 : Mem} {G : WalkGeom m0} (S : WalkStage G) :
    S.tok + stage2TokenExtent ≤ S.z ∨ S.z + stage2LogExtent ≤ S.tok :=
  stagedWrites_sep S.writes_separate (i := 3) (j := 5)
    (by decide) (by decide) (by decide)

/-- The event stream and the cursor record are separate. -/
theorem evbEvCursor {m0 : Mem} {G : WalkGeom m0} (S : WalkStage G) :
    S.c + stage2CursorExtent ≤ G.ev ∨ G.ev + G.evcap ≤ S.c :=
  stage2StagedWrites_against S.separate (a := G.ev) (m := G.evcap)
    (stage2Regions_mem_ev) (r := (S.c, stage2CursorExtent)) (by simp [stage2StagedWrites])

/-- A store inside the token record misses a cursor-record word. -/
theorem evbCursorTok {m : Mem} {m0 : Mem} {G : WalkGeom m0} {S : WalkStage G} {off : Nat}
    {v : List UInt8} {addr : Nat}
    (hv : off + v.length ≤ stage2TokenExtent) (haddr : addr = S.c ∨ addr = S.c + 1112) :
    readBytes (writeBytes m (S.tok + off) v) addr 8 = readBytes m addr 8 := by
  refine walkReadBytes_writeBytes_outside (start := S.tok + off) ?_
  have h8 : 1120 ≤ stage2CursorExtent := by decide
  have htk : stage2TokenExtent = 24 := rfl
  rcases evbTokCursor (G := G) S with h | h <;> rcases haddr with rfl | rfl
  · right; omega
  · right; omega
  · left; omega
  · left; omega

/-- A store at the token record's base misses a cursor-record word. -/
theorem evbCursorTok0 {m : Mem} {m0 : Mem} {G : WalkGeom m0} {S : WalkStage G}
    {v : List UInt8} {addr : Nat} (hv : v.length ≤ stage2TokenExtent)
    (haddr : addr = S.c ∨ addr = S.c + 1112) :
    readBytes (writeBytes m S.tok v) addr 8 = readBytes m addr 8 := by
  simpa only [Nat.add_zero] using evbCursorTok (m := m) (G := G) (S := S) (off := 0)
    (v := v) (addr := addr) (by simpa only [Nat.zero_add] using hv) haddr

/-- A store inside the event stream misses a cursor-record word. -/
theorem evbCursorEv {m : Mem} {m0 : Mem} {G : WalkGeom m0} {S : WalkStage G} {k : Nat}
    {v : List UInt8} {addr : Nat} (hm : k + v.length ≤ G.evcap)
    (haddr : addr = S.c ∨ addr = S.c + 1112) :
    readBytes (writeBytes m (G.ev + k) v) addr 8 = readBytes m addr 8 := by
  refine walkReadBytes_writeBytes_outside (start := G.ev + k) ?_
  have h8 : 1120 ≤ stage2CursorExtent := by decide
  rcases evbEvCursor (G := G) S with h | h <;> rcases haddr with rfl | rfl
  · left; omega
  · left; omega
  · right; omega
  · right; omega

/-- A store inside the log misses a cursor-record word. -/
theorem evbCursorLog {m : Mem} {m0 : Mem} {G : WalkGeom m0} {S : WalkStage G} {off : Nat}
    {v : List UInt8} {addr : Nat} (hoff : off + v.length ≤ stage2LogExtent)
    (haddr : addr = S.c ∨ addr = S.c + 1112) :
    readBytes (writeBytes m (S.z + off) v) addr 8 = readBytes m addr 8 := by
  refine walkReadBytes_writeBytes_outside (start := S.z + off) ?_
  have hsep : S.z + stage2LogExtent ≤ S.c ∨ S.c + stage2CursorExtent ≤ S.z :=
    evbOrComm (stagedWrites_sep S.writes_separate (i := 0) (j := 5)
      (by decide) (by decide) (by decide))
  have h8 : 1120 ≤ stage2CursorExtent := by decide
  have hlg : stage2LogExtent = 64 := rfl
  rcases hsep with h | h <;> rcases haddr with rfl | rfl
  · right; omega
  · right; omega
  · left; omega
  · left; omega

/-- A store inside a container stack misses a cursor-record word. -/
theorem evbCursorStack {m : Mem} {m0 : Mem} {G : WalkGeom m0} {S : WalkStage G}
    {base sp : Nat} {v : List UInt8} {addr : Nat} (hb : base = S.ctype ∨ base = S.cst)
    (hm : sp + v.length ≤ stage2StackExtent)
    (haddr : addr = S.c ∨ addr = S.c + 1112) :
    readBytes (writeBytes m (base + sp) v) addr 8 = readBytes m addr 8 := by
  refine walkReadBytes_writeBytes_outside (start := base + sp) ?_
  have h8 : 1120 ≤ stage2CursorExtent := by decide
  have hstk : stage2StackExtent = 520 := rfl
  rcases evbStackCursor (G := G) S hb with h | h <;> rcases haddr with rfl | rfl
  · right; omega
  · right; omega
  · left; omega
  · left; omega

/-- The header's `%c.i + 32` store misses the two staged words. -/
theorem evbCursorHeader {m : Mem} {m0 : Mem} {G : WalkGeom m0} {S : WalkStage G} {k : Nat}
    {addr : Nat} (haddr : addr = S.c ∨ addr = S.c + 1112) :
    readBytes (writeBytes m (S.c + 32) (wordBytes 8 k)) addr 8 = readBytes m addr 8 := by
  refine walkReadBytes_writeBytes_outside (start := S.c + 32) ?_
  rw [wordBytes, natToBytes_length]
  rcases haddr with rfl | rfl
  · left; omega
  · right; omega

/-- A store inside the token record misses a stack byte at the seam. -/
theorem evbTokStackByte {m : Mem} {m0 : Mem} {G : WalkGeom m0} {S : WalkStage G}
    {off : Nat} {v : List UInt8} {base i : Nat} (hb : base = S.ctype ∨ base = S.cst)
    (hoff : off + v.length ≤ stage2TokenExtent) (hi : i < stage2StackExtent) :
    readByte (writeBytes m (S.tok + off) v) (base + i) = readByte m (base + i) := by
  refine readByte_writeBytes_outside m v ?_
  have htk : stage2TokenExtent = 24 := rfl
  have hstk : stage2StackExtent = 520 := rfl
  rcases evbTokStackSep (G := G) S hb with h | h
  · right; omega
  · left; omega

/-! ### The opener, with the call's own memory -/

/-- **The opener's nine links, and the value-position call's memory.**  The call
writes nothing, so the endpoint's memory is the seed's up to the tail's four
stores. -/
theorem evbOpenExact {m0 : Mem} {G : WalkGeom m0} {S : WalkStage G} {s₀ : State}
    (hInv₀ : WalkInv G (walkSeed G S) s₀) (hbs : G.bs = evbDoc)
    (hent : G.ent = [0, 1, 2])
    (hroot₀ : readBytes s₀.mem (G.next0 + 8) 4 =
      some (natToBytes (0 : BitVec 32).toNat 4)) :
    ∃ (r : CallOutcome) (rd : BitVec 32),
      r.mem = s₀.mem ∧ r.next = s₀.next ∧
      WalkSegment (stage2Calls stage2SubCalls) G (walkSeed G S) s₀
        (openC₉ (openHeadC (walkSeed G S)) (BitVec.ofNat 8 0x5B))
        (openS₉ (openHeadC (walkSeed G S)) (openBrS₄ s₀) r rd (BitVec.ofNat 8 0x5B)) 9 := by
  let b : BitVec 8 := BitVec.ofNat 8 0x5B
  have h8 : evalOperand s₀ (.reg "%8") = some (.int 8 b) := evbSeed_reg8 hInv₀ hbs hent
  have hbe : b = BitVec.ofNat 8 (entryByte G (walkSeed G S).k).toNat :=
    evbSeed_entryByte hbs hent
  have hsp519 : (walkSeed G S).sp ≤ 519 := by rw [evbSeed_sp]; omega
  let rd : BitVec 32 := 0
  have hrdval : rd.toNat = 0 := rfl
  have hread : readBytes s₀.mem (G.next0 + 8) 4 = some (natToBytes rd.toNat 4) := by
    rw [hrdval]
    exact hroot₀
  have hpreV := evbSeed_valuePos_pre (G := G) (S := S) (s := s₀) hInv₀ rd
  obtain ⟨r, hcall⟩ :=
    s2ValuePos_answers (args := [.int 32 (BitVec.ofNat 32 (walkSeed G S).sp), .int 32 rd,
      .ptr (walkSeed G S).stage.ctype, .ptr (walkSeed G S).stage.cst])
      (mem := s₀.mem) (next := s₀.next) hpreV
  have hret := evbSeed_valuePos_ret (G := G) (S := S) hInv₀ hrdval hcall
  obtain ⟨-, -, -, hmem, hnext⟩ := s2ValuePos_sound hpreV hcall
  exact ⟨r, rd, hmem, hnext,
    bracketOpenSeg G (walkSeed G S) s₀ hInv₀ (walkSeed_block G S) h8 (by rfl) hbe hsp519
      hread hpreV r hcall hret⟩

/-- The opener's memory, at the seed's and the tail's two stores. -/
theorem evbOpenMem {m0 : Mem} {G : WalkGeom m0} {S : WalkStage G} {s₀ : State}
    {r : CallOutcome} {rd : BitVec 32} {b : BitVec 8} (hrmem : r.mem = s₀.mem)
    (hnev0 : G.nev0 = 0) :
    (openS₉ (openHeadC (walkSeed G S)) (openBrS₄ s₀) r rd b).mem =
      writeBytes (writeBytes (writeBytes (writeBytes s₀.mem
        (S.ctype + 0) (natToBytes (ifEnd24Ty b).toNat 1)) (S.cst + 0) (natToBytes 0 1))
        (G.ev + 0) (natToBytes (ifEnd24St b).toNat 1)) (S.z + 8) (wordBytes 8 (0 + 1)) := by
  simp only [openS₉, openS₉From, openS₈, openS₈From, openS₇, openS₇From, openS₆, openS₆From,
    openS₅, openHeadC, walkSeed, hrmem, hnev0]
  rfl

/-- **The staged base word at the opener's merge.** -/
theorem evbOpenBase {m0 : Mem} {G : WalkGeom m0} {S : WalkStage G} {s₀ : State}
    (hInv₀ : WalkInv G (walkSeed G S) s₀) (hnev0 : G.nev0 = 0) (hn3 : G.n = 3)
    {r : CallOutcome} {rd : BitVec 32} {b : BitVec 8} (hrmem : r.mem = s₀.mem)
    (hbase : readBytes s₀.mem S.c 8 = some (natToBytes G.b 8)) :
    readBytes (openS₉ (openHeadC (walkSeed G S)) (openBrS₄ s₀) r rd b).mem S.c 8 =
      some (natToBytes G.b 8) := by
  rw [evbOpenMem (S := S) hrmem hnev0]
  rw [evbCursorLog (S := S) (off := 8) (v := wordBytes 8 1) (by
    rw [wordBytes, natToBytes_length]; decide) (Or.inl rfl)]
  rw [evbCursorEv (S := S) (k := 0) (v := natToBytes (ifEnd24St b).toNat 1) (by
    rw [natToBytes_length]
    have h := G.evRoom
    rw [hn3] at h
    simp only [stage2RecordBytes] at h
    omega) (Or.inl rfl)]
  rw [evbCursorStack (S := S) (base := S.cst) (sp := 0) (v := natToBytes 0 1) (Or.inr rfl)
    (by rw [natToBytes_length]; decide) (Or.inl rfl)]
  rw [evbCursorStack (S := S) (base := S.ctype) (sp := 0) (v := natToBytes (ifEnd24Ty b).toNat 1)
    (Or.inl rfl) (by rw [natToBytes_length]; decide) (Or.inl rfl)]
  exact hbase

/-- **The staged error pointer at the opener's merge.** -/
theorem evbOpenErr {m0 : Mem} {G : WalkGeom m0} {S : WalkStage G} {s₀ : State}
    (_hInv₀ : WalkInv G (walkSeed G S) s₀) (hnev0 : G.nev0 = 0) (hn3 : G.n = 3)
    {r : CallOutcome} {rd : BitVec 32} {b : BitVec 8} (hrmem : r.mem = s₀.mem)
    (herr : readBytes s₀.mem (S.c + 1112) 8 = some (natToBytes S.e 8)) :
    readBytes (openS₉ (openHeadC (walkSeed G S)) (openBrS₄ s₀) r rd b).mem (S.c + 1112) 8 =
      some (natToBytes S.e 8) := by
  rw [evbOpenMem (S := S) hrmem hnev0]
  rw [evbCursorLog (S := S) (off := 8) (v := wordBytes 8 1) (by
    rw [wordBytes, natToBytes_length]; decide) (Or.inr rfl)]
  rw [evbCursorEv (S := S) (k := 0) (v := natToBytes (ifEnd24St b).toNat 1) (by
    rw [natToBytes_length]
    have h := G.evRoom
    rw [hn3] at h
    simp only [stage2RecordBytes] at h
    omega) (Or.inr rfl)]
  rw [evbCursorStack (S := S) (base := S.cst) (sp := 0) (v := natToBytes 0 1) (Or.inr rfl)
    (by rw [natToBytes_length]; decide) (Or.inr rfl)]
  rw [evbCursorStack (S := S) (base := S.ctype) (sp := 0) (v := natToBytes (ifEnd24Ty b).toNat 1)
    (Or.inl rfl) (by rw [natToBytes_length]; decide) (Or.inr rfl)]
  exact herr

/-! ### The lane read and the entry's byte at a head -/

/-- **The next lane's word, read at a head's memory**, at the two positions `[1]`
uses. -/
theorem evbLaneRead {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {s : State}
    (hInv : WalkInv G C s) {j : Nat} (hj : j = 1 ∨ j = 2) (hent : G.ent = [0, 1, 2])
    (hnep : G.nep = 3) :
    readBytes s.mem (G.ep + 4 * j) 4 = some (natToBytes (entryPos G j) 4) := by
  have hjn : j < G.nep := by rcases hj with rfl | rfl <;> (rw [hnep]; omega)
  obtain ⟨-, hget⟩ :=
    readLanes32_nth (m := m0) (addr := G.ep) (n := G.nep) (l := G.ent) G.entries
  obtain ⟨q, bs, hq, hread0, hbs0⟩ := hget j hjn
  have hqin : q ∈ G.ent := List.mem_of_getElem? hq
  have hqn : q < G.n := G.inside q hqin
  have hqval : q = entryPos G j := by
    rw [hent] at hq
    rcases hj with rfl | rfl
    · simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hq
      first | (rw [hq, evbPos_one hent]) | (rw [← hq, evbPos_one hent])
    · simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hq
      first | (rw [hq, evbPos_two hent]) | (rw [← hq, evbPos_two hent])
  have hlen : bs.length = 4 := walkReadBytes_length hread0
  have hbsv : bs = natToBytes q 4 := by
    have h := JsonEntrySteps.natToBytes_bytesToNat bs
    rw [hlen, hbs0] at h
    exact h.symm
  have hout : readBytes s.mem (G.ep + 4 * j) 4 = readBytes m0 (G.ep + 4 * j) 4 :=
    readBytes_eq_of_UnchangedOn (mem := m0) (m := s.mem)
      (unchangedOutside_iff_inRegions.mp hInv.frame) (a := G.ep + 4 * j) (n := 4)
      (fun i hi => hInv.entry_outside (by omega) (by omega))
  rw [hout, hread0, hbsv, hqval]

/-- **The header's lane word and the document's byte**, at a head's memory. -/
theorem evbHeaderCells {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {s : State}
    (hInv : WalkInv G C s) {j : Nat} (hj : j = 1 ∨ j = 2) (hent : G.ent = [0, 1, 2])
    (hnep : G.nep = 3) :
    ∃ (bs : List UInt8) (q : Nat),
      readBytes s.mem (G.ep + 4 * j) 4 = some bs ∧ bytesToNat bs = q ∧
      readBytes s.mem (G.b + q) 1 = some [G.bs.getD q 0] ∧ q < 2 ^ 32 := by
  have hjn : j < G.nep := by rcases hj with rfl | rfl <;> (rw [hnep]; omega)
  have hlane := evbLaneRead (G := G) (C := C) (s := s) hInv hj hent hnep
  have hpos32 : entryPos G j < 2 ^ 32 := by
    have hmax := G.maxDoc
    simp only [stage2MaxDocument] at hmax
    have hlt := entryPos_lt G hjn
    omega
  refine ⟨natToBytes (entryPos G j) 4, entryPos G j, hlane, ?_, ?_, hpos32⟩
  · have h := JsonEntrySteps.natToBytes_bytesToNat (natToBytes (entryPos G j) 4)
    simpa only [natToBytes_toNat, natToBytes_length,
      show (256 : Nat) ^ 4 = 2 ^ 32 from by decide, Nat.mod_eq_of_lt hpos32] using h
  · have hdot : entryPos G j < G.n := by
      have h := G.inside (entryPos G j) (by
        rcases hj with rfl | rfl
        · rw [evbPos_one hent]; simp [hent]
        · rw [evbPos_two hent]; simp [hent])
      simpa using h
    have hdocr : readBytes m0 (G.b + entryPos G j) 1 = some [G.bs.getD (entryPos G j) 0] :=
      walkReadBytes_one_of_readByte (readByte_of_readBytes G.doc (k := entryPos G j) hdot)
    have hout : readBytes s.mem (G.b + entryPos G j) 1 =
        readBytes m0 (G.b + entryPos G j) 1 :=
      readBytes_eq_of_UnchangedOn (mem := m0) (m := s.mem)
        (unchangedOutside_iff_inRegions.mp hInv.frame) (a := G.b + entryPos G j) (n := 1)
        (fun i hi => hInv.doc_outside (by omega) (by omega))
    rw [hout, hdocr]

/-! ### The header pass, with its endpoint and memory exposed -/

/-- **The header pass at a merge state.**  The back edge's target is named
(`cleanup478Out`), the header's store is the one write (`%c.i + 32`), and the
endpoint is the header's own state, so the pass's memory is a function of the
source's. -/
theorem evbHeadPassAt {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {s : State}
    (hInv : WalkInv G C s) (hblock : C.block = "cleanup478.i")
    {prev : String} {spv k2 : Nat} {spOp kOp : Operand} {nepv : BitVec 64}
    (hpre : s.pre = some prev)
    (hsp : phiIncoming prev cleanupSpIncoming = some spOp)
    (hspv : evalOperand s spOp = some (.int 32 (BitVec.ofNat 32 spv)))
    (hk : phiIncoming prev cleanupKIncoming = some kOp)
    (hkv : evalOperand s kOp = some (.int 64 (BitVec.ofNat 64 k2)))
    (hnep : lookupName s.env "%nep" = some (.int 64 nepv))
    (hguard : k2 < nepv.toNat) (hcap : k2 < G.nep) (hadvance : C.k < k2)
    (hspcap : spv ≤ stage2StackExtent) (hspw : spv ≤ C.wlen)
    {hent : G.ent = [0, 1, 2]} (hnep3 : G.nep = 3) (hj : k2 = 1 ∨ k2 = 2) :
    ∃ (sh : State),
      WalkSegment (stage2Calls stage2SubCalls) G C s (headPassC C k2 spv) sh 2 ∧
      WalkInv G (headPassC C k2 spv) sh ∧
      sh.mem = writeBytes s.mem (C.stage.c + 32) (wordBytes 8 (k2 + 1)) := by
  obtain ⟨hstepB, hInvB, hrunB⟩ :=
    walkBack_step_at G C s hInv hblock hpre hsp hspv hk hkv hnep hguard
  obtain ⟨h3, h5, hK, -, -, -⟩ := hInvB.ptrs
  have hk2 : lookupName (cleanup478Out s spv k2).env "%k.2.i" =
      some (.int 64 (BitVec.ofNat 64 k2)) := cleanup478Out_k
  have hsp1 : lookupName (cleanup478Out s spv k2).env "%sp.i.1" =
      some (.int 32 (BitVec.ofNat 32 spv)) := cleanup478Out_sp
  obtain ⟨bs, q, hread, hbsq, hdoc, hq32⟩ :=
    evbHeaderCells (G := G) (C := { C with block := "while.body.i", inner := walkInnerCap G })
      (s := cleanup478Out s spv k2) hInvB hj hent hnep3
  have hread' : readBytes (cleanup478Out s spv k2).mem (G.ep + k2 * 4) 4 = some bs := by
    rw [Nat.mul_comm]
    exact hread
  have hk63 : k2 < 2 ^ 63 := by
    have h := G.nep_le
    have h2 := G.maxDoc
    simp only [stage2MaxDocument] at h2
    omega
  have hk64 : k2 + 1 < 2 ^ 64 := by
    have h := G.nep_le
    have h2 := G.maxDoc
    simp only [stage2MaxDocument] at h2
    omega
  have hstepW := whileBody_term (calls := stage2Calls stage2SubCalls)
    (s := cleanup478Out s spv k2) (k := k2) (sp := spv) (ep := G.ep) (b := G.b)
    (c := C.stage.c) (q := q) (bs := bs) (bt := G.bs.getD q 0)
    hInvB.pc_eq h5 h3 hK hk2 hsp1 cleanup478Out_pre hread' hbsq hdoc hq32 hk63 hk64
  obtain ⟨e, hstepE, hInvE, -, hrunE⟩ :=
    whileBody_step (calls := stage2Calls stage2SubCalls) (G := G)
      (C := { C with block := "while.body.i", inner := walkInnerCap G })
      (s := cleanup478Out s spv k2) hInvB rfl (cleanup478Out_pre) (cleanup478Out_k)
      (cleanup478Out_sp) (by simpa using hadvance) hcap hspcap (by simpa using hspw)
  let E : State :=
    { (stateAt (whileBodyOut (cleanup478Out s spv k2).env k2 spv G.b G.ep C.stage.c q
        (G.bs.getD q 0))
        { cleanup478Out s spv k2 with
          mem := writeBytes (cleanup478Out s spv k2).mem (C.stage.c + 32)
            (wordBytes 8 (k2 + 1)) }) with
      pc := "NodeBlock21", pre := some "while.body.i" }
  have heEq : e = E := (Ctrl.jump.inj (hstepW.symm.trans hstepE)).symm
  refine ⟨E, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_, rfl⟩
    · intro n
      rw [show 2 + n = 1 + (1 + n) from by omega, hrunB (1 + n), hrunE n, heEq]
    · rw [← heEq]
      exact hInvE
  · rw [← heEq]
    exact hInvE
  · show E.mem = writeBytes s.mem (C.stage.c + 32) (wordBytes 8 (k2 + 1))
    rfl

/-! ### The scalar route's seam, at the head `[1]` reaches -/

/-- **The staged base word at the numeral's call.** -/
theorem evbSeamBase {m0 : Mem} {G : WalkGeom m0} {H₁ : WalkCarry G} {sh : State}
    {x : BitVec 8} {inc nep : BitVec 64} {ep : Nat} {v : BitVec 32} {ix : BitVec 64}
    {b35 : UInt8} {hb : HcontByteRoute (cont35 b35)} {cA : BitVec 32}
    (hbase : readBytes sh.mem H₁.stage.c 8 = some (natToBytes G.b 8)) :
    readBytes (evbSeamCallsMem H₁ sh x inc nep ep v ix b35 hb cA) H₁.stage.c 8 =
      some (natToBytes G.b 8) := by
  simp only [evbSeamCallsMem]
  rw [evbCursorTok (S := H₁.stage) (off := 16) (v := natToBytes cA.toNat 4) (by
    rw [natToBytes_length]; decide) (Or.inl rfl)]
  rw [evbCursorTok (S := H₁.stage) (off := 8) (v := natToBytes (BitVec.ofNat 64 v.toNat).toNat 8)
    (by rw [natToBytes_length]; decide) (Or.inl rfl)]
  rw [evbCursorTok (S := H₁.stage) (off := 20) (v := natToBytes (BitVec.ofNat 32 1).toNat 4)
    (by rw [natToBytes_length]; decide) (Or.inl rfl)]
  rw [evbCursorTok0 (S := H₁.stage) (v := natToBytes ix.toNat 8)
    (by rw [natToBytes_length]; decide) (Or.inl rfl)]
  exact hbase

/-- **The staged error pointer at the numeral's call.** -/
theorem evbSeamErr {m0 : Mem} {G : WalkGeom m0} {H₁ : WalkCarry G} {sh : State}
    {x : BitVec 8} {inc nep : BitVec 64} {ep : Nat} {v : BitVec 32} {ix : BitVec 64}
    {b35 : UInt8} {hb : HcontByteRoute (cont35 b35)} {cA : BitVec 32}
    (herr : readBytes sh.mem (H₁.stage.c + 1112) 8 = some (natToBytes H₁.stage.e 8)) :
    readBytes (evbSeamCallsMem H₁ sh x inc nep ep v ix b35 hb cA) (H₁.stage.c + 1112) 8 =
      some (natToBytes H₁.stage.e 8) := by
  simp only [evbSeamCallsMem]
  rw [evbCursorTok (S := H₁.stage) (off := 16) (v := natToBytes cA.toNat 4) (by
    rw [natToBytes_length]; decide) (Or.inr rfl)]
  rw [evbCursorTok (S := H₁.stage) (off := 8) (v := natToBytes (BitVec.ofNat 64 v.toNat).toNat 8)
    (by rw [natToBytes_length]; decide) (Or.inr rfl)]
  rw [evbCursorTok (S := H₁.stage) (off := 20) (v := natToBytes (BitVec.ofNat 32 1).toNat 4)
    (by rw [natToBytes_length]; decide) (Or.inr rfl)]
  rw [evbCursorTok0 (S := H₁.stage) (v := natToBytes ix.toNat 8)
    (by rw [natToBytes_length]; decide) (Or.inr rfl)]
  exact herr

/-- A log word at the numeral's call, from the head state's memory. -/
theorem evbSeamLog {m0 : Mem} {G : WalkGeom m0} {H₁ : WalkCarry G} {sh : State}
    {x : BitVec 8} {inc nep : BitVec 64} {ep : Nat} {v : BitVec 32} {ix : BitVec 64}
    {b35 : UInt8} {hb : HcontByteRoute (cont35 b35)} {cA : BitVec 32}
    {off : Nat} (hoff : off + 8 ≤ stage2LogExtent) {bs : List UInt8}
    (h : readBytes sh.mem (H₁.stage.z + off) 8 = some bs) :
    readBytes (evbSeamCallsMem H₁ sh x inc nep ep v ix b35 hb cA) (H₁.stage.z + off) 8 =
      some bs := by
  simp only [evbSeamCallsMem]
  have hkeep : ∀ {m : Mem} {o : Nat} {w : List UInt8},
      o + w.length ≤ stage2TokenExtent →
      readBytes (writeBytes m (H₁.stage.tok + o) w) (H₁.stage.z + off) 8 =
        readBytes m (H₁.stage.z + off) 8 := by
    intro m o w ho
    have htk : stage2TokenExtent = 24 := rfl
    have hlg : stage2LogExtent = 64 := rfl
    refine walkReadBytes_writeBytes_outside (start := H₁.stage.tok + o) ?_
    rcases evbTokLogSep (G := G) H₁.stage with hsep | hsep
    · right; omega
    · left; omega
  rw [hkeep (o := 16) (w := natToBytes cA.toNat 4) (by rw [natToBytes_length]; decide)]
  rw [hkeep (o := 8) (w := natToBytes (BitVec.ofNat 64 v.toNat).toNat 8)
    (by rw [natToBytes_length]; decide)]
  rw [hkeep (o := 20) (w := natToBytes (BitVec.ofNat 32 1).toNat 4)
    (by rw [natToBytes_length]; decide)]
  have hkeep0 : ∀ {m : Mem}, readBytes (writeBytes m H₁.stage.tok (natToBytes ix.toNat 8))
      (H₁.stage.z + off) 8 = readBytes m (H₁.stage.z + off) 8 := by
    intro m
    simpa only [Nat.add_zero] using hkeep (m := m) (o := 0) (w := natToBytes ix.toNat 8)
      (by rw [natToBytes_length]; decide)
  rw [hkeep0]
  exact h

/-- The numeral call's answer is `1`, and its record is the document's. -/
theorem s2ScalarValue_numberRet {mem : Mem} {c t o next : Nat} {r : CallOutcome}
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
    r.ret = .int 32 (BitVec.ofNat 32 1) := by
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
  have hrr : r = CallOutcome.mk (.int 32 (BitVec.ofNat 32 1)) _ _ :=
    (Option.some.inj hcall).symm
  rw [hrr]

/-- **The cursor record's error word at the staged entry.**  The entry's third
segment stores the appended refusal record's address at `%c.i + 1112`
(`evbStagedErr`), and the word decodes to `S.e` because that address is below
`2 ^ 64` (`WalkStage.eLt`) — the width is a clause of the staging, so no caller
supplies it. -/
theorem evbStagedErrWord {m0 : Mem} {G : WalkGeom m0} {S : WalkStage G} {s₀ : State}
    (hmem : s₀.mem = walkEntryMem G S) :
    stage2ReadWord s₀.mem (S.c + 1112) 8 = some S.e :=
  natToBytes8_readWord (evbStagedErr hmem) S.eLt

/-- **`heErr` from the cursor record's byte read.**  The seam's kind store lies
inside the token record, which the staging separates from the cursor record, so
the error word is whatever the base memory held there.  Whenever that is the
entry's `natToBytes S.e 8`, the word the scalar call reads is `S.e`, and the only
side condition is the staging's own width (`WalkStage.eLt`).  A caller that
carries the byte row across the walk's stores reaches `HcontSeamStage.heErr` from
this. -/
theorem seamKindStore_err_readWord {m0 : Mem} {G : WalkGeom m0} {Cs : WalkCarry G}
    {s : State} {cA0 : BitVec 32}
    (hread : readBytes s.mem (Cs.stage.c + 1112) 8 = some (natToBytes Cs.stage.e 8)) :
    stage2ReadWord (seamKindStore Cs s cA0) (Cs.stage.c + 1112) 8 = some Cs.stage.e := by
  have hsep : (Cs.stage.c + 1112) + 8 ≤ Cs.stage.tok + 16 ∨
      Cs.stage.tok + 16 + (natToBytes cA0.toNat 4).length ≤ Cs.stage.c + 1112 := by
    have h := evbTokCursor Cs.stage
    simp only [stage2TokenExtent, stage2CursorExtent] at h
    rw [natToBytes_length]
    rcases h with h | h
    · exact Or.inr (by omega)
    · exact Or.inl (by omega)
  have hkeep : readBytes (seamKindStore Cs s cA0) (Cs.stage.c + 1112) 8 =
      some (natToBytes Cs.stage.e 8) := by
    simp only [seamKindStore]
    rw [walkReadBytes_writeBytes_outside (start := Cs.stage.tok + 16)
      (v := natToBytes cA0.toNat 4) hsep]
    exact hread
  exact natToBytes8_readWord hkeep Cs.stage.eLt

/-- **`HcontSeamStage.heErr` at the staged entry.**  The seam's kind store misses
the cursor record's error word, and the entry wrote it (`evbStagedErrWord`), so
the row the scalar call's staging names holds at the seam's own memory. -/
theorem evbSeamErrWord {m0 : Mem} {G : WalkGeom m0} {Cs : WalkCarry G} {s : State}
    {cA0 : BitVec 32} (hmem : s.mem = walkEntryMem G Cs.stage) :
    stage2ReadWord (seamKindStore Cs s cA0) (Cs.stage.c + 1112) 8 = some Cs.stage.e :=
  seamKindStore_err_readWord (evbStagedErr hmem)

end WalkScope
end LeanLLVM.Refinement
