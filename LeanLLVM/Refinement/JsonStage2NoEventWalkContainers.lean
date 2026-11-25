/-
The no-event walk's container class: the head's two openers, the pushes, the
container pair's tokens and the closers' one-step relations.

`JsonStage2NoEventWalkHead` fixes the premise a continuing row starts from: the
invariant, the index below the entry count, and the head block's exact read and
`phi` layers.  This module supplies what the container class needs from that
premise and what the class's step hands to the rest of the walk:

* **the head's container data.**  `Stage2NoEventWalkHead.baseLookup` reads a base
  cell through its table entry; `..._stk`, `..._ep`, `..._b` and `..._nep` are
  the four the container arms read.  `..._braceCell` and `..._bracketCell` turn
  the head's class into the `%3` cell the dispatch's comparison reads, at `123`
  and `91`.
* **the dispatch.**  `stage2NoEventWalkContainerOpenBrace` and
  `stage2NoEventWalkContainerOpenBracket` run the head's own three-block dispatch
  (`NodeBlock5`, `NodeBlock`, `LeafBlock3`/`LeafBlock1`) from the frozen premise
  to `if.then9`/`if.then35.peel`, carrying the invariant and the class's `%3`
  cell.  They are the head-side halves of `stage2NoEventRow_brace` and
  `stage2NoEventRow_bracket`, stated at the premise's own cells.
* **the push.**  `stage2NoEventWalkContainerPushBracket` composes the bracket's
  dispatch with its push row (`stage2NoEventRow_bracketPush`) at the head's own
  depth, frame and index cells, reaching `if.end327.peel` with the one stack byte
  written; the route supplies the live depth, the stack room and that a further
  entry exists, which are the body's own guards.  The brace's push is `stage2NoEventRow_openBrace`, whose entry is
  `if.end19` — the state `if.then9`'s `phi` run delivers — so the brace's push is
  consumed there rather than restated here.
* **the tokens.**  `stage2NoEventWalkOpenBraceRel` and its five siblings are the
  relation's one-step rows at one document byte: the two openers, the two
  closers, and the two separators, which carry no event.  The container pair is
  `stage2NoEventWalkEmptyObjectRel`/`stage2NoEventWalkEmptyArrayRel`: `{}` and
  `[]` are two events and two tokens at two document positions.  The after-value
  and pair classes' pivots are `..._AfterValueRel` and `..._PairRel`, which read
  the pivot's byte from its own class table.
* **the trace.**  `Stage2NoEventWalkTrace.step` appends a one-step relation to a
  trace, moving the carry's event count by the step's events' length and its
  terms sum by those events' `terms`; `..._emptyObject` and `..._emptyArray`
  instantiate it at the container pair with `tok + 2` and `terms + 3`/`terms +
  7`, and `..._separator` leaves the carry alone.  A continuing row's `trace'` is
  built from these and its route's own arena reading.
* **the price.**  `stage2NoEventWalkContainerPrice` is the potential's own
  difference, `32 * (k' - k) + 8 * (ent[k'] - ent[k])`; `..._Credit` proves the
  credit identity from the entry stream's monotonicity, and `..._PairCredit`
  instantiates it at one entry's advance from a head — the container pair's
  `32 + 8 * Δpos` — against the two-event carry.

Nothing here claims a run: the chains are the body's steps and the trace
transfer is the relation's, so a row composes them at its own route and states
the arena reading and the entry facts its route proves.
-/
import LeanLLVM.Refinement.JsonStage2NoEventWalkHead

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 800000

namespace LeanLLVM.Refinement

open LeanLLVM
open LeanLLVM.JSON
open LeanLLVM.Refinement.JsonStage2NoEventIR
open LeanLLVM.Refinement.JsonEntryIR (readLanes32)
open LeanLLVM.Refinement.BlockEval (cells)

/-! ### The head's base cells

The head carries the entry chain's stable live-ins as lookups over the whole
environment (`Stage2NoEventWalkBaseLookups`), so a container arm reads its
parameter or allocation through the table rather than through a list position.
-/

/-- **A base cell resolves at a head**, from the lookup predicate. -/
theorem Stage2NoEventWalkHead.baseLookup {K : Stage2NoEventWalkCarry} {mem : Mem}
    {k : Nat} {s : State} (h : Stage2NoEventWalkHead K mem k s) {n : String}
    {v : Value} (hm : (n, v) ∈ stage2NoEventWalkBaseValues K) :
    lookupName s.env n = some v :=
  h.baseLookups n v hm

/-- **The stack pointer's base cell.** -/
theorem Stage2NoEventWalkHead.stk {K : Stage2NoEventWalkCarry} {mem : Mem}
    {k : Nat} {s : State} (h : Stage2NoEventWalkHead K mem k s) :
    lookupName s.env "%stk" = some (.ptr K.stk) :=
  h.baseLookup (by
    simp only [stage2NoEventWalkBaseValues, stage2NoEventWalkParamEntries]
    exact List.mem_append_left _ (by simp))

/-- **The entry stream pointer's base cell.** -/
theorem Stage2NoEventWalkHead.epPtr {K : Stage2NoEventWalkCarry} {mem : Mem}
    {k : Nat} {s : State} (h : Stage2NoEventWalkHead K mem k s) :
    lookupName s.env "%ep" = some (.ptr K.ep) :=
  h.baseLookup (by
    simp only [stage2NoEventWalkBaseValues, stage2NoEventWalkParamEntries]
    exact List.mem_append_left _ (by simp))

/-- **The document pointer's base cell.** -/
theorem Stage2NoEventWalkHead.bPtr {K : Stage2NoEventWalkCarry} {mem : Mem}
    {k : Nat} {s : State} (h : Stage2NoEventWalkHead K mem k s) :
    lookupName s.env "%b" = some (.ptr K.b) :=
  h.baseLookup (by
    simp only [stage2NoEventWalkBaseValues, stage2NoEventWalkParamEntries]
    exact List.mem_append_left _ (by simp))

/-- **The entry count's base cell.** -/
theorem Stage2NoEventWalkHead.nepI {K : Stage2NoEventWalkCarry} {mem : Mem}
    {k : Nat} {s : State} (h : Stage2NoEventWalkHead K mem k s) :
    lookupName s.env "%nep" = some (.int 64 (BitVec.ofNat 64 K.nep)) :=
  h.baseLookup (by
    simp only [stage2NoEventWalkBaseValues, stage2NoEventWalkParamEntries]
    exact List.mem_append_left _ (by simp))

/-! ### The class's `%3` cell

The head's `%3` cell is the document's byte at the entry's lane
(`Stage2NoEventWalkHead.laneRead`).  A class guard compares the byte's `Nat`
value, so the cell the dispatch's `icmp` reads is the same value at the class's
byte.
-/

/-- A byte equal in `Nat` value is equal. -/
theorem stage2NoEventWalk_uint8_eq_of_toNat {a b : UInt8} (h : a.toNat = b.toNat) :
    a = b :=
  UInt8.toNat_inj.mp h

/-- **The head's brace cell.**  A brace byte makes the head's `%3` the `123`
the brace's dispatch tests. -/
theorem Stage2NoEventWalkHead.braceCell {K : Stage2NoEventWalkCarry} {mem : Mem}
    {k : Nat} {s : State} (h : Stage2NoEventWalkHead K mem k s) {lane : Nat}
    {byte : UInt8} (hk : K.ent[k]? = some lane) (hbs : K.bs[lane]? = some byte)
    (hb : byte.toNat = 123) :
    lookupName s.env "%3" = some (.int 8 (BitVec.ofNat 8 123)) := by
  obtain ⟨lane', byte', hent, -, hbs', -, -, -, -, -, -, h3⟩ := h.laneRead
  have hll : lane' = lane := Option.some.inj (hent.symm.trans hk)
  cases hll
  have hb' : byte' = byte := Option.some.inj (hbs'.symm.trans hbs)
  cases hb'
  rw [h3, hb]

/-- **The head's bracket cell.**  A bracket byte makes the head's `%3` the
`91` the bracket's dispatch tests. -/
theorem Stage2NoEventWalkHead.bracketCell {K : Stage2NoEventWalkCarry} {mem : Mem}
    {k : Nat} {s : State} (h : Stage2NoEventWalkHead K mem k s) {lane : Nat}
    {byte : UInt8} (hk : K.ent[k]? = some lane) (hbs : K.bs[lane]? = some byte)
    (hb : byte.toNat = 91) :
    lookupName s.env "%3" = some (.int 8 (BitVec.ofNat 8 91)) := by
  obtain ⟨lane', byte', hent, -, hbs', -, -, -, -, -, -, h3⟩ := h.laneRead
  have hll : lane' = lane := Option.some.inj (hent.symm.trans hk)
  cases hll
  have hb' : byte' = byte := Option.some.inj (hbs'.symm.trans hbs)
  cases hb'
  rw [h3, hb]

/-! ### The head's container dispatch

The head's three-block dispatch is `NodeBlock5`'s `%3 < 91` test, `NodeBlock`'s
`%3 < 123` test and the leaf's equality.  At a brace or a bracket the chain is the
body's, and its target is the arm's entry, where the push rows take over.
-/

/-- **The brace's dispatch from the head's dispatch root.** -/
theorem stage2NoEventWalkContainerOpenBrace {calls : Calls}
    {K : Stage2NoEventWalkCarry} {mem : Mem} {k : Nat} {s : State}
    (h : Stage2NoEventWalkHead K mem k s) {lane : Nat} {byte : UInt8}
    (hk : K.ent[k]? = some lane) (hbs : K.bs[lane]? = some byte)
    (hb : byte.toNat = 123) :
    ∃ s', Stage2NoEventWalkChain calls mem K s K s' ∧
      s'.pc = "if.then9" ∧ s'.pre = some "LeafBlock3" ∧
      Stage2NoEventWalkInv K mem s' ∧
      lookupName s'.env "%3" = some (.int 8 (BitVec.ofNat 8 123)) := by
  have h3 := h.braceCell hk hbs hb
  let S := stage2NoEventWalkAt
    (("%SwitchLeaf4", .int 1 1) :: ("%Pivot", .int 1 0) ::
      ("%Pivot6", .int 1 0) :: s.env) s "if.then9" "LeafBlock3"
  have H : Stage2NoEventWalkChain calls mem K s K S :=
    stage2NoEventRow_brace h.inv h.pc h3
  have h3S : lookupName S.env "%3" = some (.int 8 (BitVec.ofNat 8 123)) := by
    show lookupName (cells [("%SwitchLeaf4", .int 1 1), ("%Pivot", .int 1 0),
      ("%Pivot6", .int 1 0)] s.env) "%3" = _
    rw [cells_lookup_of_notin _ _ (by decide)]
    exact h3
  exact ⟨S, H, rfl, rfl, Stage2NoEventWalkChain.inv H, h3S⟩

/-- **The bracket's dispatch from the head's dispatch root.** -/
theorem stage2NoEventWalkContainerOpenBracket {calls : Calls}
    {K : Stage2NoEventWalkCarry} {mem : Mem} {k : Nat} {s : State}
    (h : Stage2NoEventWalkHead K mem k s) {lane : Nat} {byte : UInt8}
    (hk : K.ent[k]? = some lane) (hbs : K.bs[lane]? = some byte)
    (hb : byte.toNat = 91) :
    ∃ s', Stage2NoEventWalkChain calls mem K s K s' ∧
      s'.pc = "if.then35.peel" ∧ s'.pre = some "LeafBlock1" ∧
      Stage2NoEventWalkInv K mem s' ∧
      lookupName s'.env "%3" = some (.int 8 (BitVec.ofNat 8 91)) := by
  have h3 := h.bracketCell hk hbs hb
  let S := stage2NoEventWalkAt
    (("%SwitchLeaf2", .int 1 1) :: ("%Pivot", .int 1 1) ::
      ("%Pivot6", .int 1 0) :: s.env) s "if.then35.peel" "LeafBlock1"
  have H : Stage2NoEventWalkChain calls mem K s K S :=
    stage2NoEventRow_bracket h.inv h.pc h3
  have h3S : lookupName S.env "%3" = some (.int 8 (BitVec.ofNat 8 91)) := by
    show lookupName (cells [("%SwitchLeaf2", .int 1 1), ("%Pivot", .int 1 1),
      ("%Pivot6", .int 1 0)] s.env) "%3" = _
    rw [cells_lookup_of_notin _ _ (by decide)]
    exact h3
  exact ⟨S, H, rfl, rfl, Stage2NoEventWalkChain.inv H, h3S⟩

/-! ### The bracket's push from the head

The dispatch's target is `if.then35.peel`, whose push row
(`stage2NoEventRow_bracketPush`) reads the depth, the frame, the stack pointer,
the index and the entry count.  At the head those are the `phi` layer's stack
cells, the read layer's `%inc.peel` and the base cells; the push is taken at a
live depth with room in the stack, which is the route's own guard and not a fact
the head binds.
-/

/-- **A head cell read through the bracket dispatch's three bindings.**  The
dispatch binds `%SwitchLeaf2`, `%Pivot` and `%Pivot6`; a differently named cell
reads through to the head. -/
theorem stage2NoEventWalkBracketDispEnv_lookup {s : State} {n : String} {v : Value}
    (h1 : "%SwitchLeaf2" ≠ n) (h2 : "%Pivot" ≠ n) (h3 : "%Pivot6" ≠ n)
    (h : lookupName s.env n = some v) :
    lookupName (("%SwitchLeaf2", .int 1 1) :: ("%Pivot", .int 1 1) ::
      ("%Pivot6", .int 1 0) :: s.env) n = some v :=
  lookupName_cons_other _ _ _ h1
    (lookupName_cons_other _ _ _ h2 (lookupName_cons_other _ _ _ h3 h))

/-- **The bracket's push at the head**: the dispatch to `if.then35.peel`, then
the push row to `if.end327.peel` with the one stack byte written.  The head
supplies the depth, the frame, the zero extension and the stack pointer; the
route supplies the live depth, the stack room and that the next entry exists. -/
theorem stage2NoEventWalkContainerPushBracket {calls : Calls}
    {K : Stage2NoEventWalkCarry} {mem : Mem} {k : Nat} {s : State}
    (h : Stage2NoEventWalkHead K mem k s) {lane : Nat} {byte : UInt8}
    (hk : K.ent[k]? = some lane) (hbs : K.bs[lane]? = some byte)
    (hb : byte.toNat = 91) (hk'lt : k + 1 < K.nep)
    (hroom : ∃ sp fr one : Nat,
      lookupName s.env "%sp.0.ph1403" = some (.int 32 (BitVec.ofNat 32 sp)) ∧
      lookupName s.env "%frame.0.ph1402" = some (.int 8 (BitVec.ofNat 8 fr)) ∧
      lookupName s.env "%1" = some (.int 64 (BitVec.ofNat 64 one)) ∧
      one = sp ∧ sp < 2 ^ 32 ∧ 1 ≤ sp ∧ sp ≤ 519) :
    ∃ s', Stage2NoEventWalkChain calls mem K s K s' ∧
      s'.pc = "if.end327.peel" ∧ s'.pre = some "if.end51.peel" := by
  have h3 := h.bracketCell hk hbs hb
  let S := stage2NoEventWalkAt
    (("%SwitchLeaf2", .int 1 1) :: ("%Pivot", .int 1 1) ::
      ("%Pivot6", .int 1 0) :: s.env) s "if.then35.peel" "LeafBlock1"
  have HD : Stage2NoEventWalkChain calls mem K s K S :=
    stage2NoEventRow_bracket h.inv h.pc h3
  obtain ⟨sp, fr, one, hsp, hfr, hone, honeq, hspLt, hposN, hleN⟩ := hroom
  have hspS : lookupName S.env "%sp.0.ph1403" =
      some (.int 32 (BitVec.ofNat 32 sp)) := by
    show lookupName (("%SwitchLeaf2", .int 1 1) :: ("%Pivot", .int 1 1) ::
      ("%Pivot6", .int 1 0) :: s.env) "%sp.0.ph1403" = _
    exact stage2NoEventWalkBracketDispEnv_lookup (by decide) (by decide) (by decide) hsp
  have hfrS : lookupName S.env "%frame.0.ph1402" =
      some (.int 8 (BitVec.ofNat 8 fr)) := by
    show lookupName (("%SwitchLeaf2", .int 1 1) :: ("%Pivot", .int 1 1) ::
      ("%Pivot6", .int 1 0) :: s.env) "%frame.0.ph1402" = _
    exact stage2NoEventWalkBracketDispEnv_lookup (by decide) (by decide) (by decide) hfr
  have h1S : lookupName S.env "%1" =
      some (.int 64 (BitVec.ofNat 64 one)) := by
    show lookupName (("%SwitchLeaf2", .int 1 1) :: ("%Pivot", .int 1 1) ::
      ("%Pivot6", .int 1 0) :: s.env) "%1" = _
    exact stage2NoEventWalkBracketDispEnv_lookup (by decide) (by decide) (by decide) hone
  have hstkS : lookupName S.env "%stk" = some (.ptr K.stk) := by
    show lookupName (("%SwitchLeaf2", .int 1 1) :: ("%Pivot", .int 1 1) ::
      ("%Pivot6", .int 1 0) :: s.env) "%stk" = _
    exact stage2NoEventWalkBracketDispEnv_lookup (by decide) (by decide) (by decide) h.stk
  have hnepS : lookupName S.env "%nep" =
      some (.int 64 (BitVec.ofNat 64 K.nep)) := by
    show lookupName (("%SwitchLeaf2", .int 1 1) :: ("%Pivot", .int 1 1) ::
      ("%Pivot6", .int 1 0) :: s.env) "%nep" = _
    exact stage2NoEventWalkBracketDispEnv_lookup (by decide) (by decide) (by decide) h.nepI
  have hinc0 : lookupName s.env "%inc.peel" =
      some (.int 64 (BitVec.ofNat 64 (k + 1))) := by
    obtain ⟨-, -, -, -, -, -, -, -, hinc, -, -⟩ := h.laneRead
    exact hinc
  have hincS : lookupName S.env "%inc.peel" =
      some (.int 64 (BitVec.ofNat 64 (k + 1))) := by
    show lookupName (("%SwitchLeaf2", .int 1 1) :: ("%Pivot", .int 1 1) ::
      ("%Pivot6", .int 1 0) :: s.env) "%inc.peel" = _
    exact stage2NoEventWalkBracketDispEnv_lookup (by decide) (by decide) (by decide) hinc0
  -- the routed readings at the row's `BitVec` values
  have h32 : (BitVec.ofNat 32 sp).toNat = sp := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hspLt]
  have h64 : (BitVec.ofNat 64 sp).toNat = sp := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_trans hspLt (by decide))]
  have hpos : 1 ≤ (BitVec.ofNat 64 sp).toNat := by omega
  have hle1 : (BitVec.ofNat 64 sp).toNat ≤ 519 := by omega
  have hposS : (BitVec.ofNat 32 sp).toNat ≠ 0 := by omega
  have hle : (BitVec.ofNat 32 sp).toNat ≤ 519 := by omega
  have hk64 : k + 1 < 2 ^ 64 := Nat.lt_trans hk'lt h.inv.nepLt
  have hult : BitVec.ult (BitVec.ofNat 64 (k + 1)) (BitVec.ofNat 64 K.nep) = true :=
    BitVec.ult_iff_toNat_lt.2 (by
      rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt hk64, Nat.mod_eq_of_lt h.inv.nepLt]
      exact hk'lt)
  have h1S' : lookupName S.env "%1" =
      some (.int 64 (BitVec.ofNat 64 sp)) := by
    rw [honeq] at h1S
    exact h1S
  let S2 := stage2NoEventWalkStoredAt
    (("%cmp319.not.peel", .int 1 1) ::
      ("%arrayidx50.peel",
        .ptr (K.stk + (BitVec.signExtend 64
          (BitVec.ofNat 64 sp + BitVec.ofNat 64 18446744073709551615)).toNat)) ::
      ("%4", .int 64 (BitVec.ofNat 64 sp + BitVec.ofNat 64 18446744073709551615)) ::
      ("%tobool46.not.peel", .int 1 0) ::
      ("%exitcond.peel", .int 1 0) :: S.env)
    S (writeBytes S.mem
      (K.stk + (BitVec.signExtend 64
        (BitVec.ofNat 64 sp + BitVec.ofNat 64 18446744073709551615)).toNat)
      (natToBytes (BitVec.ofNat 8 fr).toNat 1)) "if.end327.peel" "if.end51.peel"
  have H2 : Stage2NoEventWalkChain calls mem K S K S2 :=
    stage2NoEventRow_bracketPush (Stage2NoEventWalkChain.inv HD) rfl hspS h1S' hfrS
      hstkS hincS hnepS
      hle hposS hpos hle1 hult
  refine ⟨S2, Stage2NoEventWalkChain.trans HD H2, rfl, rfl⟩

/-! ### The one-step relations at one document byte

Each is the relation's constructor at the byte, one event and one token for a
container marker, no event and one token for a separator.  They are stated at
the document and the arena rather than at a state: a row supplies the byte from
its own read.
-/

/-- `{` (`T_OBJ`). -/
theorem stage2NoEventWalkOpenBraceRel {bs arena : List UInt8} {start : Nat}
    (hbyte : bs[start]? = some (0x7B : UInt8)) :
    Stage2NoEvent bs arena [ConsumerEvent.kind 1]
      [Token.punct Punct.openBrace ⟨start, start + 1⟩] :=
  Stage2NoEvent.openBrace hbyte rfl Stage2NoEvent.nil

/-- `}` (`T_OBJ_END`). -/
theorem stage2NoEventWalkCloseBraceRel {bs arena : List UInt8} {start : Nat}
    (hbyte : bs[start]? = some (0x7D : UInt8)) :
    Stage2NoEvent bs arena [ConsumerEvent.kind 2]
      [Token.punct Punct.closeBrace ⟨start, start + 1⟩] :=
  Stage2NoEvent.closeBrace hbyte rfl Stage2NoEvent.nil

/-- `[` (`T_ARR`). -/
theorem stage2NoEventWalkOpenBracketRel {bs arena : List UInt8} {start : Nat}
    (hbyte : bs[start]? = some (0x5B : UInt8)) :
    Stage2NoEvent bs arena [ConsumerEvent.kind 3]
      [Token.punct Punct.openBracket ⟨start, start + 1⟩] :=
  Stage2NoEvent.openBracket hbyte rfl Stage2NoEvent.nil

/-- `]` (`T_ARR_END`). -/
theorem stage2NoEventWalkCloseBracketRel {bs arena : List UInt8} {start : Nat}
    (hbyte : bs[start]? = some (0x5D : UInt8)) :
    Stage2NoEvent bs arena [ConsumerEvent.kind 4]
      [Token.punct Punct.closeBracket ⟨start, start + 1⟩] :=
  Stage2NoEvent.closeBracket hbyte rfl Stage2NoEvent.nil

/-- `,` — a separator, no event. -/
theorem stage2NoEventWalkCommaRel {bs arena : List UInt8} {start : Nat} :
    Stage2NoEvent bs arena [] [Token.punct Punct.comma ⟨start, start + 1⟩] :=
  Stage2NoEvent.comma Stage2NoEvent.nil

/-- `:` — a separator, no event. -/
theorem stage2NoEventWalkColonRel {bs arena : List UInt8} {start : Nat} :
    Stage2NoEvent bs arena [] [Token.punct Punct.colon ⟨start, start + 1⟩] :=
  Stage2NoEvent.colon Stage2NoEvent.nil

/-! ### The container pair

An empty object or array is the opener's constructor over the closer's at the next
document position.  The pair is the class the count stores move as one step:
`if.then81` adds two events and `3` terms, `if.then334` two events and `7` terms.
-/

/-- `{}`. -/
theorem stage2NoEventWalkEmptyObjectRel {bs arena : List UInt8} {start₁ start₂ : Nat}
    (h₁ : bs[start₁]? = some (0x7B : UInt8))
    (h₂ : bs[start₂]? = some (0x7D : UInt8)) :
    Stage2NoEvent bs arena [ConsumerEvent.kind 1, ConsumerEvent.kind 2]
      [Token.punct Punct.openBrace ⟨start₁, start₁ + 1⟩,
       Token.punct Punct.closeBrace ⟨start₂, start₂ + 1⟩] :=
  Stage2NoEvent.openBrace h₁ rfl (Stage2NoEvent.closeBrace h₂ rfl Stage2NoEvent.nil)

/-- `[]`. -/
theorem stage2NoEventWalkEmptyArrayRel {bs arena : List UInt8} {start₁ start₂ : Nat}
    (h₁ : bs[start₁]? = some (0x5B : UInt8))
    (h₂ : bs[start₂]? = some (0x5D : UInt8)) :
    Stage2NoEvent bs arena [ConsumerEvent.kind 3, ConsumerEvent.kind 4]
      [Token.punct Punct.openBracket ⟨start₁, start₁ + 1⟩,
       Token.punct Punct.closeBracket ⟨start₂, start₂ + 1⟩] :=
  Stage2NoEvent.openBracket h₁ rfl
    (Stage2NoEvent.closeBracket h₂ rfl Stage2NoEvent.nil)

/-- **The container pair at a head**: the empty object's relation from the head's
own lane and the next entry's lane. -/
theorem Stage2NoEventWalkHead.emptyObjectRel {K : Stage2NoEventWalkCarry} {mem : Mem}
    {k : Nat} {s : State} (_h : Stage2NoEventWalkHead K mem k s) {lane next : Nat}
    {byte nextByte : UInt8} (hbs : K.bs[lane]? = some byte) (hb : byte.toNat = 123)
    (hbs' : K.bs[next]? = some nextByte) (hb' : nextByte.toNat = 125) :
    Stage2NoEvent K.bs K.arena [ConsumerEvent.kind 1, ConsumerEvent.kind 2]
      [Token.punct Punct.openBrace ⟨lane, lane + 1⟩,
       Token.punct Punct.closeBrace ⟨next, next + 1⟩] := by
  have h1 : K.bs[lane]? = some (0x7B : UInt8) := by
    have : byte = (0x7B : UInt8) := stage2NoEventWalk_uint8_eq_of_toNat (by rw [hb]; decide)
    simpa [this] using hbs
  have h2 : K.bs[next]? = some (0x7D : UInt8) := by
    have : nextByte = (0x7D : UInt8) :=
      stage2NoEventWalk_uint8_eq_of_toNat (by rw [hb']; decide)
    simpa [this] using hbs'
  exact stage2NoEventWalkEmptyObjectRel h1 h2

/-- **The container pair at a head**: the empty array's relation from the head's
own lane and the next entry's lane. -/
theorem Stage2NoEventWalkHead.emptyArrayRel {K : Stage2NoEventWalkCarry} {mem : Mem}
    {k : Nat} {s : State} (_h : Stage2NoEventWalkHead K mem k s) {lane next : Nat}
    {byte nextByte : UInt8} (hbs : K.bs[lane]? = some byte) (hb : byte.toNat = 91)
    (hbs' : K.bs[next]? = some nextByte) (hb' : nextByte.toNat = 93) :
    Stage2NoEvent K.bs K.arena [ConsumerEvent.kind 3, ConsumerEvent.kind 4]
      [Token.punct Punct.openBracket ⟨lane, lane + 1⟩,
       Token.punct Punct.closeBracket ⟨next, next + 1⟩] := by
  have h1 : K.bs[lane]? = some (0x5B : UInt8) := by
    have : byte = (0x5B : UInt8) := stage2NoEventWalk_uint8_eq_of_toNat (by rw [hb]; decide)
    simpa [this] using hbs
  have h2 : K.bs[next]? = some (0x5D : UInt8) := by
    have : nextByte = (0x5D : UInt8) :=
      stage2NoEventWalk_uint8_eq_of_toNat (by rw [hb']; decide)
    simpa [this] using hbs'
  exact stage2NoEventWalkEmptyArrayRel h1 h2

/-! ### The after-value and pair classes' pivots

The after-value dispatch reads the frame's zero test and the next entry's byte;
the pair dispatch reads the byte after the key.  Each class names its byte, so the
class's relation is the byte's.
-/

/-- **The after-value class's relation**: a closer or a comma at the pivot's byte. -/
theorem stage2NoEventWalkAfterValueRel {bs arena : List UInt8} {start frame : Nat}
    {byte : UInt8} (hbs : bs[start]? = some byte)
    (hcls : Stage2NoEventAfterValueClass frame byte.toNat) :
    (match hcls with
      | .closeBrace _ _ => Stage2NoEvent bs arena [ConsumerEvent.kind 2]
          [Token.punct Punct.closeBrace ⟨start, start + 1⟩]
      | .closeBracket _ _ => Stage2NoEvent bs arena [ConsumerEvent.kind 4]
          [Token.punct Punct.closeBracket ⟨start, start + 1⟩]
      | .commaZero _ _ => Stage2NoEvent bs arena []
          [Token.punct Punct.comma ⟨start, start + 1⟩]
      | .commaDeep _ _ => Stage2NoEvent bs arena []
          [Token.punct Punct.comma ⟨start, start + 1⟩]
      | .other _ => True) := by
  cases hcls with
  | closeBrace _ hx =>
      exact stage2NoEventWalkCloseBraceRel (by
        have : byte = (0x7D : UInt8) :=
          stage2NoEventWalk_uint8_eq_of_toNat (by rw [hx]; decide)
        simpa [this] using hbs)
  | commaZero _ hx =>
      exact stage2NoEventWalkCommaRel (bs := bs) (arena := arena) (start := start)
  | closeBracket _ hx =>
      exact stage2NoEventWalkCloseBracketRel (by
        have : byte = (0x5D : UInt8) :=
          stage2NoEventWalk_uint8_eq_of_toNat (by rw [hx]; decide)
        simpa [this] using hbs)
  | commaDeep _ hx =>
      exact stage2NoEventWalkCommaRel (bs := bs) (arena := arena) (start := start)
  | other _ => trivial

/-- **The pair class's relation**: the colon at the pivot's byte. -/
theorem stage2NoEventWalkPairRel {bs arena : List UInt8} {start : Nat} {byte : UInt8}
    (_hbs : bs[start]? = some byte) (hcls : Stage2NoEventPairClass byte.toNat) :
    (match hcls with
      | .colon _ => Stage2NoEvent bs arena []
          [Token.punct Punct.colon ⟨start, start + 1⟩]
      | .other _ => True) := by
  cases hcls with
  | colon hx =>
      exact stage2NoEventWalkColonRel (bs := bs) (arena := arena) (start := start)
  | other _ => trivial

/-! ### The markers' arena bound

The pair and the separators are not string records, so the trace's arena-extent
bound is vacuous at them.
-/

/-- **A marker list's bound.** -/
theorem stage2NoEventArenaBound_markers {arena : List UInt8} {es : List ConsumerEvent}
    (h : ∀ e ∈ es, e.tag ≠ EventRecord.tagKey ∧ e.tag ≠ EventRecord.tagStr) :
    Stage2NoEventArenaBound arena es := by
  intro e he htag _
  rcases htag with h1 | h2
  · exact absurd h1 (h e he).1
  · exact absurd h2 (h e he).2

/-- **The container pair's bound.** -/
theorem stage2NoEventArenaBound_emptyObject (arena : List UInt8) :
    Stage2NoEventArenaBound arena
      [ConsumerEvent.kind 1, ConsumerEvent.kind 2] :=
  stage2NoEventArenaBound_markers (by
    intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl <;>
      exact ⟨by decide, by decide⟩)

/-- **The empty array's bound.** -/
theorem stage2NoEventArenaBound_emptyArray (arena : List UInt8) :
    Stage2NoEventArenaBound arena
      [ConsumerEvent.kind 3, ConsumerEvent.kind 4] :=
  stage2NoEventArenaBound_markers (by
    intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl <;>
      exact ⟨by decide, by decide⟩)

/-- **The bound of a step's event list**, when the source's and the step's are
separate: the step's own bound is the route's, and the concatenation's is the two. -/
theorem Stage2NoEventArenaBound.append {arena : List UInt8}
    {es₁ es₂ : List ConsumerEvent} (h₁ : Stage2NoEventArenaBound arena es₁)
    (h₂ : Stage2NoEventArenaBound arena es₂) :
    Stage2NoEventArenaBound arena (es₁ ++ es₂) := by
  intro e he
  rcases List.mem_append.mp he with h | h
  · exact h₁ e h
  · exact h₂ e h

/-! ### The trace's one-step extension

A trace is the events consumed so far at the carry's counts, their tokens, the
terms sum and the arena bound; it carries no arena read, the arena being the
carry's logical list extended by the route's deltas.
-/

/-- **A one-step relation appends to a trace**, at a carry whose readings the
step's events move and whose arena and byte stream are the source's.  The step's
own arena bound is the route's: the source trace's bound does not constrain events
the source has not seen. -/
theorem Stage2NoEventWalkTrace.step {K : Stage2NoEventWalkCarry}
    (h : Stage2NoEventWalkTrace K) {evs : List ConsumerEvent} {toks : List Token}
    (hstep : Stage2NoEvent K.bs K.arena evs toks)
    (hstepBound : Stage2NoEventArenaBound K.arena evs)
    (K' : Stage2NoEventWalkCarry)
    (hbs : K'.bs = K.bs) (harena : K'.arena = K.arena)
    (htok : K'.tok = K.tok + evs.length)
    (hterms : K'.terms = K.terms + (evs.map ConsumerEvent.terms).sum) :
    Stage2NoEventWalkTrace K' := by
  cases h with
  | intro obs toks₀ rel obsLen termsEq arenaBound =>
      have hrel : Stage2NoEvent K'.bs K'.arena (obs ++ evs) (toks₀ ++ toks) := by
        rw [hbs, harena]
        exact Stage2NoEvent.append rel hstep
      have hlen : (obs ++ evs).length = K'.tok := by
        rw [List.length_append, obsLen, htok]
      have hsum : K'.terms = ((obs ++ evs).map ConsumerEvent.terms).sum := by
        rw [hterms, List.map_append, List.sum_append, ← termsEq]
      have hbound : Stage2NoEventArenaBound K'.arena (obs ++ evs) := by
        rw [harena]
        exact Stage2NoEventArenaBound.append arenaBound hstepBound
      exact ⟨obs ++ evs, toks₀ ++ toks, hrel, hlen, hsum, hbound⟩

/-! ### The container pair's trace step

The pair's events move the carry by the count stores' own deltas: two events and
`3` terms for `{}`, two events and `7` for `[]`.  The arena and the byte stream do
not move.
-/

/-- **`{}` appends to the trace**, with `tok + 2` and `terms + 3`. -/
theorem Stage2NoEventWalkTrace.emptyObject {K : Stage2NoEventWalkCarry}
    (h : Stage2NoEventWalkTrace K) {start₁ start₂ : Nat}
    (h₁ : K.bs[start₁]? = some (0x7B : UInt8))
    (h₂ : K.bs[start₂]? = some (0x7D : UInt8)) :
    Stage2NoEventWalkTrace { K with tok := K.tok + 2, terms := K.terms + 3 } := by
  refine h.step (K' := { K with tok := K.tok + 2, terms := K.terms + 3 })
    (stage2NoEventWalkEmptyObjectRel h₁ h₂)
    (stage2NoEventArenaBound_emptyObject K.arena) rfl rfl ?_ ?_
  · rfl
  · have h3 : ([ConsumerEvent.kind 1, ConsumerEvent.kind 2].map
        ConsumerEvent.terms).sum = 3 := by decide
    rw [h3]

/-- **`[]` appends to the trace**, with `tok + 2` and `terms + 7`. -/
theorem Stage2NoEventWalkTrace.emptyArray {K : Stage2NoEventWalkCarry}
    (h : Stage2NoEventWalkTrace K) {start₁ start₂ : Nat}
    (h₁ : K.bs[start₁]? = some (0x5B : UInt8))
    (h₂ : K.bs[start₂]? = some (0x5D : UInt8)) :
    Stage2NoEventWalkTrace { K with tok := K.tok + 2, terms := K.terms + 7 } := by
  refine h.step (K' := { K with tok := K.tok + 2, terms := K.terms + 7 })
    (stage2NoEventWalkEmptyArrayRel h₁ h₂)
    (stage2NoEventArenaBound_emptyArray K.arena) rfl rfl ?_ ?_
  · rfl
  · have h7 : ([ConsumerEvent.kind 3, ConsumerEvent.kind 4].map
        ConsumerEvent.terms).sum = 7 := by decide
    rw [h7]

/-- **A separator appends to the trace** without moving a count. -/
theorem Stage2NoEventWalkTrace.separator {K : Stage2NoEventWalkCarry}
    (h : Stage2NoEventWalkTrace K) {toks : List Token}
    (hstep : Stage2NoEvent K.bs K.arena [] toks) :
    Stage2NoEventWalkTrace K := by
  refine h.step (K' := K) hstep ?_ rfl rfl rfl rfl
  intro e he
  cases he

/-! ### The container pair's price

The potential is `32 * (nep - k) + 8 * (n - ent[k])`; advancing one entry and one
position costs the difference, `32 + 8 * Δpos`.
-/

/-- **The container step's price**, the potential's own difference between two
indices of one entry stream. -/
def stage2NoEventWalkContainerPrice (K : Stage2NoEventWalkCarry) (k k' : Nat) : Nat :=
  32 * (k' - k) + 8 * (K.ent.getD k' 0 - K.ent.getD k 0)

/-- **The price closes the credit**: from an entry stream in increasing order, the
price of advancing `k` to `k'` plus the target's potential is inside the source's.
The carry's two counted terms and its arena do not occur, so the target is any
carry with the same `nep`, `n` and entry stream. -/
theorem stage2NoEventWalkContainerCredit {K K' : Stage2NoEventWalkCarry} {k k' : Nat}
    (horder : K.ent.Pairwise (· < ·)) (hk : k ≤ k') (hk' : k' ≤ K.nep)
    (hk'len : k' < K.ent.length)
    (hnep : K'.nep = K.nep) (hn : K'.n = K.n) (hent : K'.ent = K.ent)
    (hinside : K.ent.getD k' 0 ≤ K.n) :
    stage2NoEventWalkContainerPrice K k k' +
        stage2NoEventWalkPotential K' k' ≤ stage2NoEventWalkPotential K k := by
  have hsub : K.ent.getD k 0 ≤ K.ent.getD k' 0 :=
    stage2NoEventEnt_getD_le horder hk hk'len
  unfold stage2NoEventWalkContainerPrice stage2NoEventWalkPotential
  rw [hnep, hn, hent]
  omega

/-- **The container pair's price at a head**: one entry's advance, `32 + 8 * Δpos`,
against the pair's carry, whose `nep`, `n` and entry stream are the head's. -/
theorem stage2NoEventWalkContainerPairCredit {K : Stage2NoEventWalkCarry} {mem : Mem}
    {s : State} {k : Nat} (h : Stage2NoEventWalkInv K mem s)
    (hk'lt : k + 1 < K.nep) :
    stage2NoEventWalkContainerPrice K k (k + 1) +
        stage2NoEventWalkPotential
          { K with tok := K.tok + 2, terms := K.terms + 3 } (k + 1) ≤
      stage2NoEventWalkPotential K k := by
  have hentLen : K.ent.length = K.nep :=
    readLanes32_length mem K.ep K.nep K.ent h.entries
  have hk'len : k + 1 < K.ent.length := by rw [hentLen]; exact hk'lt
  have hmem : K.ent.getD (k + 1) 0 ∈ K.ent := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk'len]
    exact List.getElem_mem hk'len
  exact stage2NoEventWalkContainerCredit h.order (Nat.le_succ k) (Nat.le_of_lt hk'lt)
    hk'len rfl rfl rfl (le_of_lt (h.inside _ hmem))

/-- **The pair's price is the position delta**: at one entry's advance the price
is `32 + 8 * (ent[k+1] - ent[k])`. -/
theorem stage2NoEventWalkContainerPrice_pair (K : Stage2NoEventWalkCarry) (k : Nat) :
    stage2NoEventWalkContainerPrice K k (k + 1) =
      32 + 8 * (K.ent.getD (k + 1) 0 - K.ent.getD k 0) := by
  unfold stage2NoEventWalkContainerPrice
  omega

/-! ### The container arms' head-live-in census

Each arm reads a set of registers from the head; the guard below checks that every
name in the set is a head register (`stage2NoEventWalkHeadRegs`), so a register
the arm needs and the head does not bind is a build failure here rather than an
unprovable row.  The route-bound names (`%cond`, `%idxprom.lcssa`, `%ee.1`) stay
with their arms and are not in this table.
-/

/-- The container arms' head-live-in names. -/
def stage2NoEventWalkContainerLiveIns : List (String × List String) :=
  [("head-brace-dispatch", ["%3", "%ep", "%b"]),
   ("head-bracket-dispatch", ["%3", "%ep", "%b"]),
   ("head-bracket-push", ["%3", "%ep", "%b", "%1", "%frame.0.ph1402",
     "%sp.0.ph1403", "%inc.peel", "%nep", "%stk"]),
   ("after-value-close", ["%3", "%ep", "%b"]),
   ("pair-colon", ["%3", "%ep", "%b"])]

/-- The census flattened to its names. -/
def stage2NoEventWalkContainerLiveInFlat : List String :=
  stage2NoEventWalkContainerLiveIns.flatMap (·.2)

/-- **Every container arm's head-live-in is a head register.** -/
theorem stage2NoEventWalkContainerLiveIn_census :
    (stage2NoEventWalkContainerLiveInFlat.all
      fun n => decide (n ∈ stage2NoEventWalkHeadRegs)) = true := by
  decide

#guard stage2NoEventWalkContainerLiveIns.length = 5
#guard stage2NoEventWalkContainerLiveInFlat.all
  (fun n => decide (n ∈ stage2NoEventWalkHeadRegs))

/-- **The census's membership**, from the guard. -/
theorem stage2NoEventWalkContainerLiveIn_headRegs {arm : String × List String}
    (ha : arm ∈ stage2NoEventWalkContainerLiveIns) {n : String} (hn : n ∈ arm.2) :
    n ∈ stage2NoEventWalkHeadRegs := by
  have hmem : n ∈ stage2NoEventWalkContainerLiveInFlat :=
    List.mem_flatMap.mpr ⟨arm, ha, hn⟩
  exact of_decide_eq_true
    ((List.all_eq_true.mp stage2NoEventWalkContainerLiveIn_census) n hmem)

/-- **The container arms' live-ins resolve at a head**, from the head's closure. -/
theorem stage2NoEventWalkContainerLiveIns_resolve {K : Stage2NoEventWalkCarry}
    {mem : Mem} {k : Nat} {s : State} (h : Stage2NoEventWalkHead K mem k s) :
    ∀ arm ∈ stage2NoEventWalkContainerLiveIns, ∀ n ∈ arm.2,
      ∃ v, lookupName s.env n = some v :=
  fun _ ha n hn =>
    stage2NoEventWalkHead_closure h n
      (stage2NoEventWalkContainerLiveIn_headRegs ha hn)

/-! ### Axiom footprints -/

#print axioms Stage2NoEventWalkHead.stk
#print axioms Stage2NoEventWalkHead.nepI
#print axioms Stage2NoEventWalkHead.braceCell
#print axioms Stage2NoEventWalkHead.bracketCell
#print axioms stage2NoEventWalkContainerOpenBrace
#print axioms stage2NoEventWalkContainerOpenBracket
#print axioms stage2NoEventWalkBracketDispEnv_lookup
#print axioms stage2NoEventWalkContainerPushBracket
#print axioms stage2NoEventWalkOpenBraceRel
#print axioms stage2NoEventWalkEmptyObjectRel
#print axioms stage2NoEventWalkEmptyArrayRel
#print axioms Stage2NoEventWalkHead.emptyObjectRel
#print axioms Stage2NoEventWalkHead.emptyArrayRel
#print axioms stage2NoEventWalkAfterValueRel
#print axioms stage2NoEventWalkPairRel
#print axioms Stage2NoEventWalkTrace.step
#print axioms Stage2NoEventWalkTrace.emptyObject
#print axioms Stage2NoEventWalkTrace.emptyArray
#print axioms Stage2NoEventWalkTrace.separator
#print axioms stage2NoEventWalkContainerCredit
#print axioms stage2NoEventWalkContainerPairCredit
#print axioms stage2NoEventWalkContainerPrice_pair
#print axioms stage2NoEventWalkContainerLiveIns_resolve

end LeanLLVM.Refinement
