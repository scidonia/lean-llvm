/-
The fused loop's iteration and induction.

`for.body54` is the stage-1 block unit's fused loop.  A page loads the row's two
`<4 x i64>` words at `%b + 64 * i`, runs the byte class on them, stores the
emitted word at `%ent + 8 * i`, and takes one of two arms: `if.then90` runs the
classifier's DFA step on the block's neighbourhood and merges its accumulator at
`if.end93`, while the loop's own decision goes straight to `if.end93` with the
accumulator unchanged.  `if.end93` then reads the arm's escape bit: it skips to
`if.end98`, or runs the escape record at `if.then96` first.  `if.end98` increments
the index and either exits at the bound (`for.end101`) or takes the back edge.

The page's carried tuple is `FusedCarry` — the index, the shift register, the
ASCII word, the DFA's accumulator, the predecessor's probe, the three DFA state
words, the two arena pointers and the loop's bound — and `FusedInv` is its
reading at `for.body54`: every cell the body and the latch look up, in the state's
own environment, with the index inside the bound.  `FusedLatch` is the same
reading at the latch, where the successor's seven words are the cells the
`for.end101` phis name; `fusedNext` is that successor.

A page is `fusedInv_page`: the body's run and step, the DFA or merge arm, the
escape record or its skip, reaching the latch's invariant in at most four control
steps with the successor's carry and the page's memory.  The latch's two arms are
`fused_latch_exit` — the exit at `for.end101`, with `FusedExit`'s seven words
readable at the block's own environment — and `fused_latch_loop`, the back edge
at the successor's `FusedInv`.  So `fusedInv_step` is one iteration in at most
five control steps, and `fusedInv_runFuel` inducts on the measure
`%shr - (i + 1)`.  The document's blocks are the premise the induction carries; a
page that takes the escape record hands the next page the call's own memory, so
the escape unit enters through the caller's two facts: it answers the loop's call
(`hcall`) and its answer keeps the document and the three staged prefix bytes
(`hkeep`).  Those are the record's, from the staging's separations.

What is not here: the hand-off's seed at the loop head (the preheader's first page
is `for_body54_lr_ph_page`, and the row it lands on is the first one the DFA arm
reads), the `for.end101` phis' own run on this loop's arm — its `if.end98` arm,
tying the seven carried words to the staging's entry array — the staging's
separations that discharge `hcall` and `hkeep`, and the record's instance of the
loop's charge: five control steps per row plus five, which with the ASCII phase's
three per row and four is the contract's eight per block.
-/
import LeanLLVM.Refinement.JsonS1BlocksRefine
import LeanLLVM.Refinement.JsonUtf8Fused
import LeanLLVM.Refinement.JsonS1BlocksCompose

namespace LeanLLVM.Refinement.JsonS1BlocksLoop

open LeanLLVM
open LeanLLVM.Refinement
open LeanLLVM.Refinement.BlockEval
open LeanLLVM.Refinement.BlockEvalVector
open LeanLLVM.Refinement.JsonS1BlocksIR
open LeanLLVM.Refinement.JsonS1BlocksSteps
open LeanLLVM.Refinement.JsonS1BlocksRefine
open LeanLLVM.Refinement.JsonS1MasksIR
open LeanLLVM.Refinement.JsonUtf8IR (reg)

set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

/-! ### The carried tuple

The loop's registers are seven words and two pointers: the shift register
`%prevS`, the index `%i`, the ASCII accumulator `%ascii`, the DFA's accumulator
`%u8k`, the predecessor's non-ASCII probe `%prev_ascii`, the DFA's three state
words, the row base `%b` and the emit base `%ent`, plus the bound `%shr` the
latch compares against and the memory the page reads and writes. -/

/-- The fused loop's carried tuple. -/
structure FusedCarry where
  /-- The index the page processes: the block the body loads. -/
  i : BitVec 64
  /-- The shift register the previous page left. -/
  prevS : BitVec 64
  /-- The ASCII accumulator: the pages' joined words. -/
  ascii : List (BitVec 64)
  /-- The DFA's accumulator, as the merge left it. -/
  u8k : List (BitVec 64)
  /-- The predecessor block's non-ASCII probe. -/
  prevAscii : BitVec 32
  /-- The DFA's first state word. -/
  st0 : BitVec 64
  /-- The DFA's second state word. -/
  st9 : BitVec 64
  /-- The DFA's third state word. -/
  st15 : BitVec 64
  /-- The row base the page loads at `%b + 64 * i`. -/
  b : Nat
  /-- The emit base the page stores at `%ent + 8 * i`. -/
  ent : Nat
  /-- The escape stream's base, the escape record's fifth argument. -/
  xp : Nat
  /-- The stream count's slot, the escape record's sixth argument. -/
  nxp : Nat
  /-- The carry's slot, the escape record's seventh argument. -/
  xcarry : Nat
  /-- The loop bound the latch's exit test compares the successor with. -/
  shr : BitVec 64
  /-- The memory the page reads and writes. -/
  mem : Mem

/-! ### The invariant at the loop head

The back edge enters `for.body54` from `if.end98`, so the eight phi operands are
the cells that edge leaves readable: the body's own `%shr85`, `%or.i282`, `%75`,
`%shr.i.i325`, `%conv13.i.i324` and `%shr.i348`, the merge's `%u8k.2`, and the
latch's `%inc100`.  The invariant binds exactly those, the parameters the page
reads beneath them, the two arm bits, and the index's place in the bound. -/

/-- **The loop's invariant at `for.body54`.**  The state is at the head, entered
from the latch, with the eight phi operands bound to the carry's fields, the
row's arena pointers and the bound, the two arm selections, and the index inside
the bound. -/
structure FusedInv (env : Env) (s : State) (c : FusedCarry)
    (gate esc : BitVec 1) : Prop where
  /-- The state is at the loop head. -/
  pc : s.pc = "for.body54"
  /-- The back edge is the predecessor. -/
  pre : s.pre = some "if.end98"
  /-- The state's memory is the one the page reads. -/
  mem : s.mem = c.mem
  /-- The successor index the latch left. -/
  index : lookupName env "%inc100" = some (.int 64 c.i)
  /-- The shift register the previous page left. -/
  prevS : lookupName env "%shr85" = some (.int 64 c.prevS)
  /-- The ASCII accumulator. -/
  ascii : lookupName env "%or.i282" = some (.vec 4 64 c.ascii)
  /-- The DFA's accumulator. -/
  u8k : lookupName env "%u8k.2" = some (.vec 4 64 c.u8k)
  /-- The predecessor's probe. -/
  prevAscii : lookupName env "%75" = some (.int 32 c.prevAscii)
  /-- The DFA's first state word. -/
  st0 : lookupName env "%shr.i.i325" = some (.int 64 c.st0)
  /-- The DFA's second state word. -/
  st9 : lookupName env "%conv13.i.i324" = some (.int 64 c.st9)
  /-- The DFA's third state word. -/
  st15 : lookupName env "%shr.i348" = some (.int 64 c.st15)
  /-- The row base. -/
  base : lookupName env "%b" = some (.ptr c.b)
  /-- The emit base. -/
  emit : lookupName env "%ent" = some (.ptr c.ent)
  /-- The loop bound. -/
  bound : lookupName env "%shr" = some (.int 64 c.shr)
  /-- The escape stream's base. -/
  stream : lookupName env "%xp" = some (.ptr c.xp)
  /-- The stream count's slot. -/
  count : lookupName env "%nxp" = some (.ptr c.nxp)
  /-- The carry's slot. -/
  carry : lookupName env "%xcarry" = some (.ptr c.xcarry)
  /-- The DFA gate `%tobool87`. -/
  gate : lookupName env "%tobool87" = some (.int 1 gate)
  /-- The escape record's bit `%tobool95.not`. -/
  escape : lookupName env "%tobool95.not" = some (.int 1 esc)
  /-- The index is inside the bound. -/
  index_lt : c.i.toNat < c.shr.toNat
  /-- The ASCII accumulator has four lanes. -/
  ascii_len : c.ascii.length = 4
  /-- The DFA's accumulator has four lanes. -/
  u8k_len : c.u8k.length = 4

/-- **The ladder's invariant at `if.end98`.**  The latch's own index is `i`, and
its seven carried cells are the successor's words: the words the merge, the DFA
arm and the body left for the next page and for `for.end101`'s phis. -/
structure FusedLatch (env : Env) (s : State) (i : BitVec 64) (c : FusedCarry)
    (gate esc : BitVec 1) : Prop where
  /-- The state is at the latch. -/
  pc : s.pc = "if.end98"
  /-- The state's memory is the page's, after the body's store and any call. -/
  mem : s.mem = c.mem
  /-- The latch's own index, which the increment reads. -/
  index : lookupName env "%i.2523" = some (.int 64 i)
  /-- The successor's shift register. -/
  prevS : lookupName env "%shr85" = some (.int 64 c.prevS)
  /-- The successor's ASCII word. -/
  ascii : lookupName env "%or.i282" = some (.vec 4 64 c.ascii)
  /-- The successor's DFA accumulator, as the merge left it. -/
  u8k : lookupName env "%u8k.2" = some (.vec 4 64 c.u8k)
  /-- The successor's predecessor probe. -/
  prevAscii : lookupName env "%75" = some (.int 32 c.prevAscii)
  /-- The successor's first DFA state word. -/
  st0 : lookupName env "%shr.i.i325" = some (.int 64 c.st0)
  /-- The successor's second DFA state word. -/
  st9 : lookupName env "%conv13.i.i324" = some (.int 64 c.st9)
  /-- The successor's third DFA state word. -/
  st15 : lookupName env "%shr.i348" = some (.int 64 c.st15)
  /-- The row base. -/
  base : lookupName env "%b" = some (.ptr c.b)
  /-- The emit base. -/
  emit : lookupName env "%ent" = some (.ptr c.ent)
  /-- The loop bound. -/
  bound : lookupName env "%shr" = some (.int 64 c.shr)
  /-- The escape stream's base. -/
  stream : lookupName env "%xp" = some (.ptr c.xp)
  /-- The stream count's slot. -/
  count : lookupName env "%nxp" = some (.ptr c.nxp)
  /-- The carry's slot. -/
  carry : lookupName env "%xcarry" = some (.ptr c.xcarry)
  /-- The DFA gate. -/
  gate : lookupName env "%tobool87" = some (.int 1 gate)
  /-- The escape record's bit. -/
  escape : lookupName env "%tobool95.not" = some (.int 1 esc)
  /-- The latch's index is the successor's predecessor. -/
  succ : c.i = i + 1
  /-- The latch's index is inside the bound. -/
  index_lt : i.toNat < c.shr.toNat
  /-- The ASCII accumulator has four lanes. -/
  ascii_len : c.ascii.length = 4
  /-- The DFA's accumulator has four lanes. -/
  u8k_len : c.u8k.length = 4

/-- **The exit's facts at `for.end101`.**  The bound has been reached: the seven
carried words the block's phis name are the successor's, the state is at the
block with the latch as its predecessor, and the index is the bound. -/
structure FusedExit (env : Env) (s : State) (c : FusedCarry) : Prop where
  /-- The state is at `for.end101`. -/
  pc : s.pc = "for.end101"
  /-- The latch is the predecessor. -/
  pre : s.pre = some "if.end98"
  /-- The state's memory is the page's. -/
  mem : s.mem = c.mem
  /-- The bound is reached. -/
  bound_reached : c.i = c.shr
  /-- `%prevS.2.lcssa`'s operand. -/
  prevS : lookupName env "%shr85" = some (.int 64 c.prevS)
  /-- `%ascii.1.lcssa`'s operand. -/
  ascii : lookupName env "%or.i282" = some (.vec 4 64 c.ascii)
  /-- `%u8k.1.lcssa`'s operand. -/
  u8k : lookupName env "%u8k.2" = some (.vec 4 64 c.u8k)
  /-- `%prev_ascii.1.lcssa`'s operand. -/
  prevAscii : lookupName env "%75" = some (.int 32 c.prevAscii)
  /-- `%st.sroa.0.2.lcssa`'s operand. -/
  st0 : lookupName env "%shr.i.i325" = some (.int 64 c.st0)
  /-- `%st.sroa.9.2.lcssa`'s operand. -/
  st9 : lookupName env "%conv13.i.i324" = some (.int 64 c.st9)
  /-- `%st.sroa.15.2.lcssa`'s operand. -/
  st15 : lookupName env "%shr.i348" = some (.int 64 c.st15)
  /-- The row base. -/
  base : lookupName env "%b" = some (.ptr c.b)
  /-- The emit base. -/
  emit : lookupName env "%ent" = some (.ptr c.ent)
  /-- The loop bound. -/
  bound : lookupName env "%shr" = some (.int 64 c.shr)

/-! ### The page's computation and its successor

The body's values at the carry's index, the successor's seven words, and the
carry the next page (or `for.end101`'s phis) reads. -/

/-- The values one page binds: the body's own computation at the carry's index
and its two loaded words. -/
def fusedValues (c : FusedCarry) (bs73 bs74 : List UInt8) : ForBody54Values :=
  forBody54Values c.prevS c.i c.ascii c.u8k c.prevAscii c.st0 c.st9 c.st15
    bs73 bs74 c.b c.ent

/-- The successor's ASCII word: the two loaded words' join, joined again with
the incoming accumulator. -/
def fusedAscii (c : FusedCarry) (bs73 bs74 : List UInt8) : List (BitVec 64) :=
  fb54Or (fb54Or (fusedValues c bs73 bs74).w74 (fusedValues c bs73 bs74).w73)
    (fusedValues c bs73 bs74).ascii

/-- The successor's predecessor probe: the block's non-ASCII test. -/
def fusedPrevAscii (c : FusedCarry) (bs73 bs74 : List UInt8) : BitVec 32 :=
  fb54Probe (fb54Or (fusedValues c bs73 bs74).w74 (fusedValues c bs73 bs74).w73)

/-- The carry one page hands on.  The index is the latch's increment, the seven
words are the body's and the merge's, and the memory is the page's — the body's
store, or the escape call's own outcome. -/
def fusedNext (c : FusedCarry) (bs73 bs74 : List UInt8) (u8k : List (BitVec 64))
    (mem : Mem) : FusedCarry :=
  let v := fusedValues c bs73 bs74
  { i := c.i + 1
    prevS := v.shr85
    ascii := fb54Or (fb54Or v.w74 v.w73) v.ascii
    u8k := u8k
    prevAscii := fb54Probe (fb54Or v.w74 v.w73)
    st0 := v.shrII
    st9 := v.conv13II
    st15 := v.shrI
    b := c.b
    ent := c.ent
    xp := c.xp
    nxp := c.nxp
    xcarry := c.xcarry
    shr := c.shr
    mem := mem }

/-! ### Reading the page's environments

The body's nine segment environments, the DFA arm's six, the escape record's
four and the two merges are builders of literal cells, so a read is decided by
peeling the cons chain: the name is a literal and the value is the cell's.  The
two macros below are that peel at the body's chain and at the latch's chain (the
latch's cells, the merge's, the DFA arm's, the escape record's and the body's,
in the order a state can nest them). -/

/-- A read through the body's nine segment environments. -/
macro "fused_body_lk" : tactic => `(tactic|
  (first
   | assumption
   | (simp only [fb54Env9, fb54Env8, fb54Env7, fb54Env6, fb54Env5, fb54Env4,
        fb54Env3, fb54Env2, fb54Env1, cells]
      block_lk_cons)))

/-! ### The body's cells -/

/-- The shift register, as the body leaves it. -/
theorem lookupName_fb54Env9_shr85 (env : Env) (v : ForBody54Values) (gate : BitVec 1) :
    lookupName (fb54Env9 env v gate) "%shr85" = some (.int 64 v.shr85) := by
  fused_body_lk

/-- The ASCII word, as the body leaves it. -/
theorem lookupName_fb54Env9_or282 (env : Env) (v : ForBody54Values) (gate : BitVec 1) :
    lookupName (fb54Env9 env v gate) "%or.i282"
      = some (.vec 4 64 (fb54Or (fb54Or v.w74 v.w73) v.ascii)) := by
  fused_body_lk

/-- The predecessor's probe, as the body leaves it. -/
theorem lookupName_fb54Env9_p75 (env : Env) (v : ForBody54Values) (gate : BitVec 1) :
    lookupName (fb54Env9 env v gate) "%75"
      = some (.int 32 (fb54Probe (fb54Or v.w74 v.w73))) := by
  fused_body_lk

/-- The DFA's first successor word, as the body leaves it. -/
theorem lookupName_fb54Env9_shrII (env : Env) (v : ForBody54Values) (gate : BitVec 1) :
    lookupName (fb54Env9 env v gate) "%shr.i.i325" = some (.int 64 v.shrII) := by
  fused_body_lk

/-- The DFA's second successor word, as the body leaves it. -/
theorem lookupName_fb54Env9_conv13 (env : Env) (v : ForBody54Values) (gate : BitVec 1) :
    lookupName (fb54Env9 env v gate) "%conv13.i.i324" = some (.int 64 v.conv13II) := by
  fused_body_lk

/-- The DFA's third successor word, as the body leaves it. -/
theorem lookupName_fb54Env9_shrI (env : Env) (v : ForBody54Values) (gate : BitVec 1) :
    lookupName (fb54Env9 env v gate) "%shr.i348" = some (.int 64 v.shrI) := by
  fused_body_lk

/-- The page's index, as the body's phi run bound it. -/
theorem lookupName_fb54Env9_i (env : Env) (v : ForBody54Values) (gate : BitVec 1) :
    lookupName (fb54Env9 env v gate) "%i.2523" = some (.int 64 v.i) := by
  fused_body_lk

/-- The DFA's accumulator, as the body's phi run bound it. -/
theorem lookupName_fb54Env9_u8k (env : Env) (v : ForBody54Values) (gate : BitVec 1) :
    lookupName (fb54Env9 env v gate) "%u8k.1521" = some (.vec 4 64 v.u8k) := by
  fused_body_lk

/-- The DFA arm's first low-nibble control, as the body left it. -/
theorem lookupName_fb54Env9_p88 (env : Env) (v : ForBody54Values) (gate : BitVec 1) :
    lookupName (fb54Env9 env v gate) "%88" = some (.vec 32 8 v.low88) := by
  fused_body_lk

/-- The DFA arm's second low-nibble control, as the body left it. -/
theorem lookupName_fb54Env9_p97 (env : Env) (v : ForBody54Values) (gate : BitVec 1) :
    lookupName (fb54Env9 env v gate) "%97" = some (.vec 32 8 v.low97) := by
  fused_body_lk

/-- The row pointer, as the body left it. -/
theorem lookupName_fb54Env9_addPtr57 (env : Env) (v : ForBody54Values) (gate : BitVec 1) :
    lookupName (fb54Env9 env v gate) "%add.ptr57" = some (.ptr v.addPtr57) := by
  fused_body_lk

/-- The two loaded words, as the body left them. -/
theorem lookupName_fb54Env9_w73 (env : Env) (v : ForBody54Values) (gate : BitVec 1) :
    lookupName (fb54Env9 env v gate) "%73" = some (.vec 4 64 v.w73) := by
  fused_body_lk

theorem lookupName_fb54Env9_w74 (env : Env) (v : ForBody54Values) (gate : BitVec 1) :
    lookupName (fb54Env9 env v gate) "%74" = some (.vec 4 64 v.w74) := by
  fused_body_lk

/-- The escape record's first argument, as the body left it. -/
theorem lookupName_fb54Env9_or14 (env : Env) (v : ForBody54Values) (gate : BitVec 1) :
    lookupName (fb54Env9 env v gate) "%or14.i303" = some (.int 64 v.or14) := by
  fused_body_lk

/-- The escape record's third argument, as the body left it. -/
theorem lookupName_fb54Env9_xorI (env : Env) (v : ForBody54Values) (gate : BitVec 1) :
    lookupName (fb54Env9 env v gate) "%xor.i347" = some (.int 64 v.xorI) := by
  fused_body_lk

/-- The page's memory before any escape call: the body's store at the row's
slot, `%ent + 8 * i`. -/
def fusedStore (c : FusedCarry) (bs73 bs74 : List UInt8) : Mem :=
  let v := fusedValues c bs73 bs74
  writeBytes c.mem v.arrayidx (natToBytes v.or84.toNat 8)

/-! ### The page's addresses and lane counts

The row's pointer is the 64-byte stride, the store's slot is `%ent + 8 * i`, and
the two words' lane counts are the load's own arity. -/

/-- The row's pointer, at the 64-byte stride. -/
theorem fusedValues_addPtr57 (c : FusedCarry) (bs73 bs74 : List UInt8)
    (hj : c.i.toNat < 2 ^ 57) :
    (fusedValues c bs73 bs74).addPtr57 = c.b + 64 * c.i.toNat := by
  show c.b + ((BitVec.signExtend 64 (c.i <<< (0x0000000000000006#64).toNat)).toNat)
      = c.b + 64 * c.i.toNat
  rw [for_body_offset_toNat _ hj]

/-- The second word's pointer: the row's first thirty-two bytes on. -/
theorem fusedValues_addPtr61 (c : FusedCarry) (bs73 bs74 : List UInt8)
    (hj : c.i.toNat < 2 ^ 57) :
    (fusedValues c bs73 bs74).addPtr61 = c.b + 64 * c.i.toNat + 32 := by
  show (c.b + ((BitVec.signExtend 64 (c.i <<< (0x0000000000000006#64).toNat)).toNat))
      + ((0x0000000000000020#64).signExtend 64).toNat = c.b + 64 * c.i.toNat + 32
  rw [for_body_offset_toNat _ hj,
    show ((0x0000000000000020#64).signExtend 64).toNat = 32 from by decide]

/-- The store's slot: the entry array's word for the page's index. -/
theorem fusedValues_arrayidx (c : FusedCarry) (bs73 bs74 : List UInt8) :
    (fusedValues c bs73 bs74).arrayidx = c.ent + 8 * c.i.toNat := by
  show c.ent + (c.i.signExtend 64).toNat * (Ty.int 64).sizeBytes = c.ent + 8 * c.i.toNat
  rw [show (Ty.int 64).sizeBytes = 8 from by decide,
    show (c.i.signExtend 64).toNat = c.i.toNat from by simp [BitVec.signExtend]]
  omega

/-- The first loaded word has four lanes. -/
theorem fusedValues_w73_length (c : FusedCarry) (bs73 bs74 : List UInt8) :
    (fusedValues c bs73 bs74).w73.length = 4 := by
  show (unpackLanes 64 4 (bytesToNat bs73)).length = 4
  simp [unpackLanes_length]

/-- The second loaded word has four lanes. -/
theorem fusedValues_w74_length (c : FusedCarry) (bs73 bs74 : List UInt8) :
    (fusedValues c bs73 bs74).w74.length = 4 := by
  show (unpackLanes 64 4 (bytesToNat bs74)).length = 4
  simp [unpackLanes_length]

/-- The first low-nibble control has thirty-two lanes. -/
theorem fusedValues_low88_length (c : FusedCarry) (bs73 bs74 : List UInt8) :
    (fusedValues c bs73 bs74).low88.length = 32 := by
  simp [fusedValues, forBody54Values, bitcastVecLanes, unpackLanes_length,
    List.length_map]

/-- The second low-nibble control has thirty-two lanes. -/
theorem fusedValues_low97_length (c : FusedCarry) (bs73 bs74 : List UInt8) :
    (fusedValues c bs73 bs74).low97.length = 32 := by
  simp [fusedValues, forBody54Values, bitcastVecLanes, unpackLanes_length,
    List.length_map]

/-- A lane-wise disjunction of two four-lane words has four lanes. -/
theorem fusedOr_length (a b : List (BitVec 64))
    (ha : a.length = 4) (hb : b.length = 4) : (fb54Or a b).length = 4 := by
  simp [fb54Or, List.length_zipWith, ha, hb]

/-- The successor's ASCII word has four lanes. -/
theorem fusedNext_ascii_length (c : FusedCarry) (bs73 bs74 : List UInt8)
    (u8k : List (BitVec 64)) (mem : Mem) (ha : c.ascii.length = 4) :
    (fusedNext c bs73 bs74 u8k mem).ascii.length = 4 := by
  have h1 : (fb54Or (fusedValues c bs73 bs74).w74 (fusedValues c bs73 bs74).w73).length
      = 4 :=
    fusedOr_length _ _ (fusedValues_w74_length c bs73 bs74)
      (fusedValues_w73_length c bs73 bs74)
  have h2 : (fusedValues c bs73 bs74).ascii.length = 4 := ha
  show (fb54Or (fb54Or (fusedValues c bs73 bs74).w74 (fusedValues c bs73 bs74).w73)
    (fusedValues c bs73 bs74).ascii).length = 4
  exact fusedOr_length _ _ h1 h2

/-- The merged accumulator's four lanes: the DFA arm's join of two four-lane
words against the incoming accumulator. -/
theorem ifThen90Values_or281_length (a : Nat) (low88 low97 : List (BitVec 8))
    (u8k : List (BitVec 64)) (bs41 bs42 bs43 bs57 bs58 bs59 : List UInt8)
    (huk : u8k.length = 4) :
    (ifThen90Values a low88 low97 u8k bs41 bs42 bs43 bs57 bs58 bs59).or281.length
      = 4 := by
  have h132 := ifThen90Values_or132_length a low88 low97 u8k bs41 bs42 bs43 bs57 bs58 bs59
  have h : (ifThen90Values a low88 low97 u8k bs41 bs42 bs43 bs57 bs58 bs59).or281
      = List.zipWith (fun x y => x ||| y)
          (ifThen90Values a low88 low97 u8k bs41 bs42 bs43 bs57 bs58 bs59).or132 u8k :=
    rfl
  rw [h, List.length_zipWith, h132, huk]
  rfl

/-! ### The body's run

The body's nine segments at the carry's values, the phi run's operands from the
latch's cells, and the two word loads at the 64-byte stride.  The statement
carries no register reads as hypotheses: every one is the invariant's or the
builder's. -/

/-- **The page's body run.**  The body reads the carry's eight phi operands off
the back edge, loads the row's two words at `%b + 64 * i`, and leaves its own
environment with the store at `%ent + 8 * i` in the memory. -/
theorem fused_body_run (env : Env) (s : State) (c : FusedCarry) (gate esc : BitVec 1)
    (bs73 bs74 : List UInt8)
    (hinv : FusedInv env s c gate esc)
    (hshr57 : c.shr.toNat < 2 ^ 57)
    (hread73 : readBytes c.mem (c.b + 64 * c.i.toNat) 32 = some bs73)
    (hread74 : readBytes c.mem (c.b + 64 * c.i.toNat + 32) 32 = some bs74) :
    let v := fusedValues c bs73 bs74
    denoteCode s1BlocksCalls for_body54Instrs (stateAt env s) =
      some (stateAt (fb54Env9 env v gate)
        { s with mem := writeBytes s.mem v.arrayidx (natToBytes v.or84.toNat 8) }) := by
  intro v
  have hi : c.i.toNat < c.shr.toNat := hinv.index_lt
  have hj57 : c.i.toNat < 2 ^ 57 := by omega
  have hshl63 : ((c.i <<< (0x0000000000000006#64).toNat).signExtend 64).toNat < 2 ^ 63 := by
    rw [for_body_offset_toNat _ hj57]; omega
  have hread73' : readBytes s.mem
      (c.b + ((c.i <<< (0x0000000000000006#64).toNat).signExtend 64).toNat) 32
      = some bs73 := by
    rw [hinv.mem, for_body_offset_toNat _ hj57]
    exact hread73
  have hread74' : readBytes s.mem
      ((c.b + ((c.i <<< (0x0000000000000006#64).toNat).signExtend 64).toNat)
        + ((0x0000000000000020#64).signExtend 64).toNat) 32 = some bs74 := by
    rw [hinv.mem, for_body_offset_toNat _ hj57,
      show ((0x0000000000000020#64).signExtend 64).toNat = 32 from by decide]
    exact hread74
  have h73len : (unpackLanes 64 4 (bytesToNat bs73)).length = 4 := by
    simp [unpackLanes_length]
  have h74len : (unpackLanes 64 4 (bytesToNat bs74)).length = 4 := by
    simp [unpackLanes_length]
  have hi63 : (c.i.signExtend 64).toNat < 2 ^ 63 := by
    rw [show (c.i.signExtend 64).toNat = c.i.toNat from by simp [BitVec.signExtend]]
    omega
  have hbody := for_body54_denote env s "if.end98"
    (.reg "%shr85") (.reg "%inc100") (.reg "%or.i282") (.reg "%u8k.2")
    (.reg "%75") (.reg "%shr.i.i325") (.reg "%conv13.i.i324") (.reg "%shr.i348")
    c.prevS c.i c.ascii c.u8k c.prevAscii c.st0 c.st9 c.st15 bs73 bs74 c.b c.ent gate
    hinv.pre
    (by simp [phiIncoming]) (BlockEval.evalOperand_reg_of _ _ _ _ hinv.prevS)
    (by simp [phiIncoming]) (BlockEval.evalOperand_reg_of _ _ _ _ hinv.index)
    (by simp [phiIncoming]) (BlockEval.evalOperand_reg_of _ _ _ _ hinv.ascii)
    (by simp [phiIncoming]) (BlockEval.evalOperand_reg_of _ _ _ _ hinv.u8k)
    (by simp [phiIncoming]) (BlockEval.evalOperand_reg_of _ _ _ _ hinv.prevAscii)
    (by simp [phiIncoming]) (BlockEval.evalOperand_reg_of _ _ _ _ hinv.st0)
    (by simp [phiIncoming]) (BlockEval.evalOperand_reg_of _ _ _ _ hinv.st9)
    (by simp [phiIncoming]) (BlockEval.evalOperand_reg_of _ _ _ _ hinv.st15)
    hinv.base hshl63 hread73' hread74' h73len h74len hinv.ascii_len
  exact hbody (lookupName_fb54Env8_ent env v hinv.emit) hi63
    (lookupName_fb54Env8_tobool87 env v hinv.gate)

/-- The emit base, as the body's environment leaves it. -/
theorem lookupName_fb54Env9_ent (env : Env) (v : ForBody54Values)
    (gate : BitVec 1) {ent : Nat}
    (h : lookupName env "%ent" = some (.ptr ent)) :
    lookupName (fb54Env9 env v gate) "%ent" = some (.ptr ent) := by
  fused_body_lk

/-- The loop bound, as the body's environment leaves it. -/
theorem lookupName_fb54Env9_shr (env : Env) (v : ForBody54Values)
    (gate : BitVec 1) {shr : BitVec 64}
    (h : lookupName env "%shr" = some (.int 64 shr)) :
    lookupName (fb54Env9 env v gate) "%shr" = some (.int 64 shr) := by
  fused_body_lk

/-- The DFA gate, as the body's environment leaves it. -/
theorem lookupName_fb54Env9_tobool87 (env : Env) (v : ForBody54Values)
    (gate : BitVec 1) {g : BitVec 1}
    (h : lookupName env "%tobool87" = some (.int 1 g)) :
    lookupName (fb54Env9 env v gate) "%tobool87" = some (.int 1 g) := by
  fused_body_lk

/-- The escape bit's zero test, as the body's environment leaves it. -/
theorem lookupName_fb54Env9_tobool95 (env : Env) (v : ForBody54Values)
    (gate : BitVec 1) {esc : BitVec 1}
    (h : lookupName env "%tobool95.not" = some (.int 1 esc)) :
    lookupName (fb54Env9 env v gate) "%tobool95.not" = some (.int 1 esc) := by
  fused_body_lk

/-- The row base, as the body's environment leaves it. -/
theorem lookupName_fb54Env9_b (env : Env) (v : ForBody54Values)
    (gate : BitVec 1) {b : Nat}
    (h : lookupName env "%b" = some (.ptr b)) :
    lookupName (fb54Env9 env v gate) "%b" = some (.ptr b) := by
  fused_body_lk

/-- The escape stream's base, as the body's environment leaves it. -/
theorem lookupName_fb54Env9_xp (env : Env) (v : ForBody54Values)
    (gate : BitVec 1) {xp : Nat}
    (h : lookupName env "%xp" = some (.ptr xp)) :
    lookupName (fb54Env9 env v gate) "%xp" = some (.ptr xp) := by
  fused_body_lk

/-- The count slot, as the body's environment leaves it. -/
theorem lookupName_fb54Env9_nxp (env : Env) (v : ForBody54Values)
    (gate : BitVec 1) {nxp : Nat}
    (h : lookupName env "%nxp" = some (.ptr nxp)) :
    lookupName (fb54Env9 env v gate) "%nxp" = some (.ptr nxp) := by
  fused_body_lk

/-- The carry's slot, as the body's environment leaves it. -/
theorem lookupName_fb54Env9_xcarry (env : Env) (v : ForBody54Values)
    (gate : BitVec 1) {xcarry : Nat}
    (h : lookupName env "%xcarry" = some (.ptr xcarry)) :
    lookupName (fb54Env9 env v gate) "%xcarry" = some (.ptr xcarry) := by
  fused_body_lk

/-! ### The page's environments and states

The body's output environment, the merge's, the escape record's, and the states
the three edges reach.  Naming them keeps the page statements readable and lets
each lookup be decided at the builder the block itself wrote. -/

/-- The body's output environment: its nine segments' cells over the carry's. -/
def fusedE3 (env : Env) (c : FusedCarry) (gate : BitVec 1) (bs73 bs74 : List UInt8) : Env :=
  fb54Env9 env (fusedValues c bs73 bs74) gate

/-- The merge's environment: `%u8k.2` over the body's cells. -/
def fusedE9 (env : Env) (c : FusedCarry) (gate : BitVec 1) (bs73 bs74 : List UInt8) : Env :=
  ifEnd93Env (fusedE3 env c gate bs73 bs74) c.u8k

/-- The escape record's environment: its four cells over the merge's. -/
def fusedE96 (env : Env) (c : FusedCarry) (gate : BitVec 1) (bs73 bs74 : List UInt8) : Env :=
  ifThen96Out (fusedE9 env c gate bs73 bs74)
    (fusedValues c bs73 bs74).w73 (fusedValues c bs73 bs74).w74

/-- The latch's core state on the silent arm: the block, the predecessor and the
body's store, with the environment supplied by the state above it. -/
def fusedLatchCore (s : State) (c : FusedCarry) (bs73 bs74 : List UInt8) : State :=
  { s with pc := "if.end98", pre := some "if.end93", mem := fusedStore c bs73 bs74 }

/-- The latch's core state on the escape arm: the record's memory and cursor. -/
def fusedEscapedLatchCore (s : State) (c : FusedCarry) (bs73 bs74 : List UInt8)
    (r : CallOutcome) : State :=
  { s with pc := "if.end98", pre := some "if.then96", mem := r.mem, next := r.next }

/-- The latch's core state on the DFA arm's skip branch. -/
def fusedDfaLatchCore (s : State) (c : FusedCarry) (bs73 bs74 : List UInt8) : State :=
  { s with pc := "if.end98", pre := some "if.end93", mem := fusedStore c bs73 bs74 }

/-- The latch's core state on the DFA arm's escape branch. -/
def fusedDfaEscapedLatchCore (s : State) (c : FusedCarry) (bs73 bs74 : List UInt8)
    (r : CallOutcome) : State :=
  { s with pc := "if.end98", pre := some "if.then96", mem := r.mem, next := r.next }

/-- The state the body's edge reaches: the merge, with the page's store. -/
def fusedBodyState (env : Env) (s : State) (c : FusedCarry) (gate : BitVec 1)
    (bs73 bs74 : List UInt8) : State :=
  stateAt (fusedE3 env c gate bs73 bs74)
    { s with pc := "if.end93", pre := some "for.body54", mem := fusedStore c bs73 bs74 }

/-- The latch's entry on the silent arm: the merge's environment, no call. -/
def fusedLatchState (env : Env) (s : State) (c : FusedCarry) (gate : BitVec 1)
    (bs73 bs74 : List UInt8) : State :=
  stateAt (fusedE9 env c gate bs73 bs74) (fusedLatchCore s c bs73 bs74)

/-- The escape record's entry: the merge's environment at the arm's edge. -/
def fusedEscapeState (env : Env) (s : State) (c : FusedCarry) (gate : BitVec 1)
    (bs73 bs74 : List UInt8) : State :=
  stateAt (fusedE9 env c gate bs73 bs74)
    { s with pc := "if.then96", pre := some "if.end93", mem := fusedStore c bs73 bs74 }

/-- The latch's entry on the escape arm: the record's environment and the call's
own memory and cursor. -/
def fusedEscapedLatchState (env : Env) (s : State) (c : FusedCarry) (gate : BitVec 1)
    (bs73 bs74 : List UInt8) (r : CallOutcome) : State :=
  stateAt (fusedE96 env c gate bs73 bs74) (fusedEscapedLatchCore s c bs73 bs74 r)

/-- A read through the merge's two cells to the body's environment. -/
macro "fused_e9_lk" : tactic => `(tactic|
  (first
   | assumption
   | (simp only [fusedE9, ifEnd93Env, fusedE3, fb54Env9, fb54Env8, fb54Env7,
        fb54Env6, fb54Env5, fb54Env4, fb54Env3, fb54Env2, fb54Env1, cells]
      block_lk_cons)))

/-- A read through the escape record's four cells, the merge's and the body's. -/
macro "fused_e96_lk" : tactic => `(tactic|
  (first
   | assumption
   | (simp only [fusedE96, ifThen96Out, fusedE9, ifEnd93Env, fusedE3, fb54Env9,
        fb54Env8, fb54Env7, fb54Env6, fb54Env5, fb54Env4, fb54Env3, fb54Env2,
        fb54Env1, cells]
      block_lk_cons)))

/-- A read through the latch's increment and exit-test cells. -/
macro "fused_end98_lk" : tactic => `(tactic|
  (first
   | assumption
   | (simp only [ifEnd98Env, cells]
      block_lk_cons)))

/-! ### Reading the merge's and the record's environments

Each layer of the latch's environment is a `cells` builder whose keys the block
itself wrote, so a read that misses the layer's keys reaches the one beneath.
The two peel lemmas below are that step; the per-name lemmas are the reads the
latch's invariant and the exit's fields need. -/

/-- A read that misses the merge's single cell reaches the body's environment. -/
theorem lookupName_fusedE9_of (env : Env) (c : FusedCarry) (gate : BitVec 1)
    (bs73 bs74 : List UInt8) {n : String} {v : Value}
    (hn : "%u8k.2" ≠ n)
    (h : lookupName (fusedE3 env c gate bs73 bs74) n = some v) :
    lookupName (fusedE9 env c gate bs73 bs74) n = some v := by
  show lookupName (("%u8k.2", Value.vec 4 64 c.u8k) :: fusedE3 env c gate bs73 bs74) n
    = some v
  rw [lookupName_cons_ne _ _ hn]
  exact h

/-- A read that misses the escape record's four cells reaches the merge. -/
theorem lookupName_fusedE96_of (env : Env) (c : FusedCarry) (gate : BitVec 1)
    (bs73 bs74 : List UInt8) {n : String} {v : Value}
    (h1 : "%or.i379" ≠ n) (h2 : "%135" ≠ n) (h3 : "%134" ≠ n) (h4 : "%133" ≠ n)
    (h : lookupName (fusedE9 env c gate bs73 bs74) n = some v) :
    lookupName (fusedE96 env c gate bs73 bs74) n = some v := by
  show lookupName (("%or.i379", Value.int 64 (ifThen96Mask
        (fusedValues c bs73 bs74).w73 (fusedValues c bs73 bs74).w74)) ::
      ("%135", Value.vec 64 1 (icmpLanes .ult
        (bitcastVecLanes 8 64 ((fusedValues c bs73 bs74).w73 ++ (fusedValues c bs73 bs74).w74))
        (List.replicate 64 0x20#8))) ::
      ("%134", Value.vec 64 8 (bitcastVecLanes 8 64 ((fusedValues c bs73 bs74).w73 ++ (fusedValues c bs73 bs74).w74))) ::
      ("%133", Value.vec 8 64 ((fusedValues c bs73 bs74).w73 ++ (fusedValues c bs73 bs74).w74)) ::
      fusedE9 env c gate bs73 bs74) n = some v
  rw [lookupName_cons_ne _ _ h1, lookupName_cons_ne _ _ h2,
    lookupName_cons_ne _ _ h3, lookupName_cons_ne _ _ h4]
  exact h

/-- The shift register through the merge's cell. -/
theorem lookupName_fusedE9_shr85 (env : Env) (c : FusedCarry) (gate : BitVec 1)
    (bs73 bs74 : List UInt8) :
    lookupName (fusedE9 env c gate bs73 bs74) "%shr85"
      = some (.int 64 (fusedValues c bs73 bs74).shr85) :=
  lookupName_fusedE9_of env c gate bs73 bs74 (by decide)
    (lookupName_fb54Env9_shr85 env (fusedValues c bs73 bs74) gate)

/-- The ASCII word through the merge's cell. -/
theorem lookupName_fusedE9_or282 (env : Env) (c : FusedCarry) (gate : BitVec 1)
    (bs73 bs74 : List UInt8) :
    lookupName (fusedE9 env c gate bs73 bs74) "%or.i282"
      = some (.vec 4 64 (fusedAscii c bs73 bs74)) :=
  lookupName_fusedE9_of env c gate bs73 bs74 (by decide)
    (lookupName_fb54Env9_or282 env (fusedValues c bs73 bs74) gate)

/-- The predecessor's probe through the merge's cell. -/
theorem lookupName_fusedE9_p75 (env : Env) (c : FusedCarry) (gate : BitVec 1)
    (bs73 bs74 : List UInt8) :
    lookupName (fusedE9 env c gate bs73 bs74) "%75"
      = some (.int 32 (fusedPrevAscii c bs73 bs74)) :=
  lookupName_fusedE9_of env c gate bs73 bs74 (by decide)
    (lookupName_fb54Env9_p75 env (fusedValues c bs73 bs74) gate)

/-- The DFA's first successor word through the merge's cell. -/
theorem lookupName_fusedE9_shrII (env : Env) (c : FusedCarry) (gate : BitVec 1)
    (bs73 bs74 : List UInt8) :
    lookupName (fusedE9 env c gate bs73 bs74) "%shr.i.i325"
      = some (.int 64 (fusedValues c bs73 bs74).shrII) :=
  lookupName_fusedE9_of env c gate bs73 bs74 (by decide)
    (lookupName_fb54Env9_shrII env (fusedValues c bs73 bs74) gate)

/-- The DFA's second successor word through the merge's cell. -/
theorem lookupName_fusedE9_conv13 (env : Env) (c : FusedCarry) (gate : BitVec 1)
    (bs73 bs74 : List UInt8) :
    lookupName (fusedE9 env c gate bs73 bs74) "%conv13.i.i324"
      = some (.int 64 (fusedValues c bs73 bs74).conv13II) :=
  lookupName_fusedE9_of env c gate bs73 bs74 (by decide)
    (lookupName_fb54Env9_conv13 env (fusedValues c bs73 bs74) gate)

/-- The DFA's third successor word through the merge's cell. -/
theorem lookupName_fusedE9_shrI (env : Env) (c : FusedCarry) (gate : BitVec 1)
    (bs73 bs74 : List UInt8) :
    lookupName (fusedE9 env c gate bs73 bs74) "%shr.i348"
      = some (.int 64 (fusedValues c bs73 bs74).shrI) :=
  lookupName_fusedE9_of env c gate bs73 bs74 (by decide)
    (lookupName_fb54Env9_shrI env (fusedValues c bs73 bs74) gate)

/-- The page's index through the merge's cell. -/
theorem lookupName_fusedE9_i (env : Env) (c : FusedCarry) (gate : BitVec 1)
    (bs73 bs74 : List UInt8) :
    lookupName (fusedE9 env c gate bs73 bs74) "%i.2523" = some (.int 64 c.i) :=
  lookupName_fusedE9_of env c gate bs73 bs74 (by decide)
    (lookupName_fb54Env9_i env (fusedValues c bs73 bs74) gate)

/-- The DFA's incoming accumulator through the merge's own cell. -/
theorem lookupName_fusedE9_u8k (env : Env) (c : FusedCarry) (gate : BitVec 1)
    (bs73 bs74 : List UInt8) (u8k : List (BitVec 64))
    (hu : c.u8k = u8k) :
    lookupName (fusedE9 env c gate bs73 bs74) "%u8k.2" = some (.vec 4 64 u8k) := by
  show lookupName (("%u8k.2", Value.vec 4 64 c.u8k) :: fusedE3 env c gate bs73 bs74)
    "%u8k.2" = some (.vec 4 64 u8k)
  rw [lookupName_cons_self]
  rw [hu]

/-- The row base through the merge's cell and the body's. -/
theorem lookupName_fusedE9_b (env : Env) (c : FusedCarry) (gate : BitVec 1)
    (bs73 bs74 : List UInt8) {b : Nat}
    (h : lookupName env "%b" = some (.ptr b)) :
    lookupName (fusedE9 env c gate bs73 bs74) "%b" = some (.ptr b) :=
  lookupName_fusedE9_of env c gate bs73 bs74 (by decide)
    (lookupName_fb54Env9_b env (fusedValues c bs73 bs74) gate h)

/-- The emit base through the merge's cell and the body's. -/
theorem lookupName_fusedE9_ent (env : Env) (c : FusedCarry) (gate : BitVec 1)
    (bs73 bs74 : List UInt8) {ent : Nat}
    (h : lookupName env "%ent" = some (.ptr ent)) :
    lookupName (fusedE9 env c gate bs73 bs74) "%ent" = some (.ptr ent) :=
  lookupName_fusedE9_of env c gate bs73 bs74 (by decide)
    (lookupName_fb54Env9_ent env (fusedValues c bs73 bs74) gate h)

/-- The bound through the merge's cell and the body's. -/
theorem lookupName_fusedE9_shr (env : Env) (c : FusedCarry) (gate : BitVec 1)
    (bs73 bs74 : List UInt8) {shr : BitVec 64}
    (h : lookupName env "%shr" = some (.int 64 shr)) :
    lookupName (fusedE9 env c gate bs73 bs74) "%shr" = some (.int 64 shr) :=
  lookupName_fusedE9_of env c gate bs73 bs74 (by decide)
    (lookupName_fb54Env9_shr env (fusedValues c bs73 bs74) gate h)

/-- The escape stream's base through the merge's cell and the body's. -/
theorem lookupName_fusedE9_xp (env : Env) (c : FusedCarry) (gate : BitVec 1)
    (bs73 bs74 : List UInt8) {xp : Nat}
    (h : lookupName env "%xp" = some (.ptr xp)) :
    lookupName (fusedE9 env c gate bs73 bs74) "%xp" = some (.ptr xp) :=
  lookupName_fusedE9_of env c gate bs73 bs74 (by decide)
    (lookupName_fb54Env9_xp env (fusedValues c bs73 bs74) gate h)

/-- The count slot through the merge's cell and the body's. -/
theorem lookupName_fusedE9_nxp (env : Env) (c : FusedCarry) (gate : BitVec 1)
    (bs73 bs74 : List UInt8) {nxp : Nat}
    (h : lookupName env "%nxp" = some (.ptr nxp)) :
    lookupName (fusedE9 env c gate bs73 bs74) "%nxp" = some (.ptr nxp) :=
  lookupName_fusedE9_of env c gate bs73 bs74 (by decide)
    (lookupName_fb54Env9_nxp env (fusedValues c bs73 bs74) gate h)

/-- The carry's slot through the merge's cell and the body's. -/
theorem lookupName_fusedE9_xcarry (env : Env) (c : FusedCarry) (gate : BitVec 1)
    (bs73 bs74 : List UInt8) {xcarry : Nat}
    (h : lookupName env "%xcarry" = some (.ptr xcarry)) :
    lookupName (fusedE9 env c gate bs73 bs74) "%xcarry" = some (.ptr xcarry) :=
  lookupName_fusedE9_of env c gate bs73 bs74 (by decide)
    (lookupName_fb54Env9_xcarry env (fusedValues c bs73 bs74) gate h)

/-- The DFA gate through the merge's cell and the body's. -/
theorem lookupName_fusedE9_tobool87 (env : Env) (c : FusedCarry) (gate : BitVec 1)
    (bs73 bs74 : List UInt8) {g : BitVec 1}
    (h : lookupName env "%tobool87" = some (.int 1 g)) :
    lookupName (fusedE9 env c gate bs73 bs74) "%tobool87" = some (.int 1 g) :=
  lookupName_fusedE9_of env c gate bs73 bs74 (by decide)
    (lookupName_fb54Env9_tobool87 env (fusedValues c bs73 bs74) gate h)

/-- The escape bit through the merge's cell and the body's. -/
theorem lookupName_fusedE9_tobool95 (env : Env) (c : FusedCarry) (gate : BitVec 1)
    (bs73 bs74 : List UInt8) {e : BitVec 1}
    (h : lookupName env "%tobool95.not" = some (.int 1 e)) :
    lookupName (fusedE9 env c gate bs73 bs74) "%tobool95.not" = some (.int 1 e) :=
  lookupName_fusedE9_of env c gate bs73 bs74 (by decide)
    (lookupName_fb54Env9_tobool95 env (fusedValues c bs73 bs74) gate h)

/-! ### `if.end93`'s two arms

The body's decision set: the merge reads the body's own `%u8k.1521` and branches
on the escape bit.  The two lemmas below are one page each to the latch. -/

/-- **One page on the merge's skip arm.**  The body's run and step, the merge at
`%u8k.1521`, and the escape bit's set form: the latch's invariant at the merge's
environment, with the successor's seven words and the body's store. -/
theorem fused_merge_skip_page (sel : Calls) (env : Env) (s : State) (c : FusedCarry)
    (gate : BitVec 1) (bs73 bs74 : List UInt8)
    (hinv : FusedInv env s c gate 1)
    (hshr57 : c.shr.toNat < 2 ^ 57)
    (hread73 : readBytes c.mem (c.b + 64 * c.i.toNat) 32 = some bs73)
    (hread74 : readBytes c.mem (c.b + 64 * c.i.toNat + 32) 32 = some bs74)
    (hdec : fb54Select gate (fusedValues c bs73 bs74).v107 = 1) :
    step (s1BlocksCallsEsc sel) s1BlocksFunction (stateAt env s) =
      .jump (fusedBodyState env s c gate bs73 bs74) ∧
    step (s1BlocksCallsEsc sel) s1BlocksFunction (fusedBodyState env s c gate bs73 bs74) =
      .jump (fusedLatchState env s c gate bs73 bs74) ∧
    FusedLatch (fusedE9 env c gate bs73 bs74) (fusedLatchCore s c bs73 bs74)
      c.i (fusedNext c bs73 bs74 c.u8k (fusedStore c bs73 bs74)) gate 1 := by
  have hbody := fused_body_run env s c gate 1 bs73 bs74 hinv hshr57 hread73 hread74
  have hbit : lookupName (fusedE3 env c gate bs73 bs74) "%or.cond189"
      = some (.int 1 1) := by
    rw [show fusedE3 env c gate bs73 bs74
        = fb54Env9 env (fusedValues c bs73 bs74) gate from rfl,
      lookupName_fb54Env9_cond189]
    show some (Value.int 1 (fb54Select gate (fusedValues c bs73 bs74).v107))
      = some (Value.int 1 1)
    rw [hdec]
  have h01 : step (s1BlocksCallsEsc sel) s1BlocksFunction (stateAt env s) =
      .jump (fusedBodyState env s c gate bs73 bs74) := by
    rw [step_esc_of_free sel s1BlocksFunction (stateAt env s) for_body54Block
      (by rw [show (stateAt env s).pc = s.pc from rfl, hinv.pc]
          exact findBlock_for_body54) (by decide)]
    rw [show fusedBodyState env s c gate bs73 bs74
        = stateAt (fb54Env9 env (fusedValues c bs73 bs74) gate)
            { s with
              pc := "if.end93",
              pre := some "for.body54",
              mem := writeBytes c.mem (fusedValues c bs73 bs74).arrayidx
                (natToBytes (fusedValues c bs73 bs74).or84.toNat 8) } from rfl,
      ← hinv.mem]
    exact for_body54_step_end env s (fusedValues c bs73 bs74) gate hinv.pc hbit hbody
  have hesc : lookupName (fusedE3 env c gate bs73 bs74) "%tobool95.not"
      = some (.int 1 1) := by
    rw [show fusedE3 env c gate bs73 bs74
        = fb54Env9 env (fusedValues c bs73 bs74) gate from rfl]
    exact lookupName_fb54Env9_tobool95 env _ gate hinv.escape
  have h12 : step (s1BlocksCallsEsc sel) s1BlocksFunction
      (fusedBodyState env s c gate bs73 bs74) =
      .jump (fusedLatchState env s c gate bs73 bs74) := by
    rw [step_esc_of_free sel s1BlocksFunction _ if_end93Block
      (by rw [show (fusedBodyState env s c gate bs73 bs74).pc = "if.end93" from rfl]
          exact findBlock_if_end93) (by decide)]
    rw [show fusedLatchState env s c gate bs73 bs74
        = stateAt (ifEnd93Env (fusedE3 env c gate bs73 bs74) c.u8k)
            { fusedBodyState env s c gate bs73 bs74 with
              pc := "if.end98",
              pre := some "if.end93" } from rfl]
    exact if_end93_step_skip (fusedE3 env c gate bs73 bs74)
      (fusedBodyState env s c gate bs73 bs74) "for.body54" (.reg "%u8k.1521")
      c.u8k 1 rfl rfl (by simp [phiIncoming])
      (BlockEval.evalOperand_reg_of _ _ _ _
        (lookupName_fb54Env9_u8k env (fusedValues c bs73 bs74) gate))
      hesc rfl
  refine ⟨h01, h12, ?_⟩
  refine
    { pc := rfl
      mem := rfl
      index := lookupName_fusedE9_i env c gate bs73 bs74
      prevS := lookupName_fusedE9_shr85 env c gate bs73 bs74
      ascii := lookupName_fusedE9_or282 env c gate bs73 bs74
      u8k := lookupName_fusedE9_u8k env c gate bs73 bs74 c.u8k rfl
      prevAscii := lookupName_fusedE9_p75 env c gate bs73 bs74
      st0 := lookupName_fusedE9_shrII env c gate bs73 bs74
      st9 := lookupName_fusedE9_conv13 env c gate bs73 bs74
      st15 := lookupName_fusedE9_shrI env c gate bs73 bs74
      base := lookupName_fusedE9_b env c gate bs73 bs74 hinv.base
      emit := lookupName_fusedE9_ent env c gate bs73 bs74 hinv.emit
      bound := lookupName_fusedE9_shr env c gate bs73 bs74 hinv.bound
      stream := lookupName_fusedE9_xp env c gate bs73 bs74 hinv.stream
      count := lookupName_fusedE9_nxp env c gate bs73 bs74 hinv.count
      carry := lookupName_fusedE9_xcarry env c gate bs73 bs74 hinv.carry
      gate := lookupName_fusedE9_tobool87 env c gate bs73 bs74 hinv.gate
      escape := lookupName_fusedE9_tobool95 env c gate bs73 bs74 hinv.escape
      succ := rfl
      index_lt := hinv.index_lt
      ascii_len := fusedNext_ascii_length c bs73 bs74 c.u8k (fusedStore c bs73 bs74)
        hinv.ascii_len
      u8k_len := hinv.u8k_len }

/-- The first loaded word through the merge's cell. -/
theorem lookupName_fusedE9_w73 (env : Env) (c : FusedCarry) (gate : BitVec 1)
    (bs73 bs74 : List UInt8) :
    lookupName (fusedE9 env c gate bs73 bs74) "%73"
      = some (.vec 4 64 (fusedValues c bs73 bs74).w73) :=
  lookupName_fusedE9_of env c gate bs73 bs74 (by decide)
    (lookupName_fb54Env9_w73 env (fusedValues c bs73 bs74) gate)

/-- The second loaded word through the merge's cell. -/
theorem lookupName_fusedE9_w74 (env : Env) (c : FusedCarry) (gate : BitVec 1)
    (bs73 bs74 : List UInt8) :
    lookupName (fusedE9 env c gate bs73 bs74) "%74"
      = some (.vec 4 64 (fusedValues c bs73 bs74).w74) :=
  lookupName_fusedE9_of env c gate bs73 bs74 (by decide)
    (lookupName_fb54Env9_w74 env (fusedValues c bs73 bs74) gate)

/-- The escape record's first argument through the merge's cell. -/
theorem lookupName_fusedE9_or14 (env : Env) (c : FusedCarry) (gate : BitVec 1)
    (bs73 bs74 : List UInt8) :
    lookupName (fusedE9 env c gate bs73 bs74) "%or14.i303"
      = some (.int 64 (fusedValues c bs73 bs74).or14) :=
  lookupName_fusedE9_of env c gate bs73 bs74 (by decide)
    (lookupName_fb54Env9_or14 env (fusedValues c bs73 bs74) gate)

/-- The escape record's third argument through the merge's cell. -/
theorem lookupName_fusedE9_xorI (env : Env) (c : FusedCarry) (gate : BitVec 1)
    (bs73 bs74 : List UInt8) :
    lookupName (fusedE9 env c gate bs73 bs74) "%xor.i347"
      = some (.int 64 (fusedValues c bs73 bs74).xorI) :=
  lookupName_fusedE9_of env c gate bs73 bs74 (by decide)
    (lookupName_fb54Env9_xorI env (fusedValues c bs73 bs74) gate)

/-- The escape record's environment, read at a cell the record does not bind:
each of the latch's seven words and every parameter rides through. -/
theorem lookupName_fusedE96_shr85 (env : Env) (c : FusedCarry) (gate : BitVec 1)
    (bs73 bs74 : List UInt8) :
    lookupName (fusedE96 env c gate bs73 bs74) "%shr85"
      = some (.int 64 (fusedValues c bs73 bs74).shr85) :=
  lookupName_fusedE96_of env c gate bs73 bs74 (by decide) (by decide) (by decide)
    (by decide) (lookupName_fusedE9_shr85 env c gate bs73 bs74)

theorem lookupName_fusedE96_or282 (env : Env) (c : FusedCarry) (gate : BitVec 1)
    (bs73 bs74 : List UInt8) :
    lookupName (fusedE96 env c gate bs73 bs74) "%or.i282"
      = some (.vec 4 64 (fusedAscii c bs73 bs74)) :=
  lookupName_fusedE96_of env c gate bs73 bs74 (by decide) (by decide) (by decide)
    (by decide) (lookupName_fusedE9_or282 env c gate bs73 bs74)

theorem lookupName_fusedE96_p75 (env : Env) (c : FusedCarry) (gate : BitVec 1)
    (bs73 bs74 : List UInt8) :
    lookupName (fusedE96 env c gate bs73 bs74) "%75"
      = some (.int 32 (fusedPrevAscii c bs73 bs74)) :=
  lookupName_fusedE96_of env c gate bs73 bs74 (by decide) (by decide) (by decide)
    (by decide) (lookupName_fusedE9_p75 env c gate bs73 bs74)

theorem lookupName_fusedE96_shrII (env : Env) (c : FusedCarry) (gate : BitVec 1)
    (bs73 bs74 : List UInt8) :
    lookupName (fusedE96 env c gate bs73 bs74) "%shr.i.i325"
      = some (.int 64 (fusedValues c bs73 bs74).shrII) :=
  lookupName_fusedE96_of env c gate bs73 bs74 (by decide) (by decide) (by decide)
    (by decide) (lookupName_fusedE9_shrII env c gate bs73 bs74)

theorem lookupName_fusedE96_conv13 (env : Env) (c : FusedCarry) (gate : BitVec 1)
    (bs73 bs74 : List UInt8) :
    lookupName (fusedE96 env c gate bs73 bs74) "%conv13.i.i324"
      = some (.int 64 (fusedValues c bs73 bs74).conv13II) :=
  lookupName_fusedE96_of env c gate bs73 bs74 (by decide) (by decide) (by decide)
    (by decide) (lookupName_fusedE9_conv13 env c gate bs73 bs74)

theorem lookupName_fusedE96_shrI (env : Env) (c : FusedCarry) (gate : BitVec 1)
    (bs73 bs74 : List UInt8) :
    lookupName (fusedE96 env c gate bs73 bs74) "%shr.i348"
      = some (.int 64 (fusedValues c bs73 bs74).shrI) :=
  lookupName_fusedE96_of env c gate bs73 bs74 (by decide) (by decide) (by decide)
    (by decide) (lookupName_fusedE9_shrI env c gate bs73 bs74)

theorem lookupName_fusedE96_i (env : Env) (c : FusedCarry) (gate : BitVec 1)
    (bs73 bs74 : List UInt8) :
    lookupName (fusedE96 env c gate bs73 bs74) "%i.2523" = some (.int 64 c.i) :=
  lookupName_fusedE96_of env c gate bs73 bs74 (by decide) (by decide) (by decide)
    (by decide) (lookupName_fusedE9_i env c gate bs73 bs74)

theorem lookupName_fusedE96_u8k (env : Env) (c : FusedCarry) (gate : BitVec 1)
    (bs73 bs74 : List UInt8) (u8k : List (BitVec 64)) (hu : c.u8k = u8k) :
    lookupName (fusedE96 env c gate bs73 bs74) "%u8k.2" = some (.vec 4 64 u8k) :=
  lookupName_fusedE96_of env c gate bs73 bs74 (by decide) (by decide) (by decide)
    (by decide) (lookupName_fusedE9_u8k env c gate bs73 bs74 u8k hu)

theorem lookupName_fusedE96_b (env : Env) (c : FusedCarry) (gate : BitVec 1)
    (bs73 bs74 : List UInt8) {b : Nat}
    (h : lookupName env "%b" = some (.ptr b)) :
    lookupName (fusedE96 env c gate bs73 bs74) "%b" = some (.ptr b) :=
  lookupName_fusedE96_of env c gate bs73 bs74 (by decide) (by decide) (by decide)
    (by decide) (lookupName_fusedE9_b env c gate bs73 bs74 h)

theorem lookupName_fusedE96_ent (env : Env) (c : FusedCarry) (gate : BitVec 1)
    (bs73 bs74 : List UInt8) {ent : Nat}
    (h : lookupName env "%ent" = some (.ptr ent)) :
    lookupName (fusedE96 env c gate bs73 bs74) "%ent" = some (.ptr ent) :=
  lookupName_fusedE96_of env c gate bs73 bs74 (by decide) (by decide) (by decide)
    (by decide) (lookupName_fusedE9_ent env c gate bs73 bs74 h)

theorem lookupName_fusedE96_shr (env : Env) (c : FusedCarry) (gate : BitVec 1)
    (bs73 bs74 : List UInt8) {shr : BitVec 64}
    (h : lookupName env "%shr" = some (.int 64 shr)) :
    lookupName (fusedE96 env c gate bs73 bs74) "%shr" = some (.int 64 shr) :=
  lookupName_fusedE96_of env c gate bs73 bs74 (by decide) (by decide) (by decide)
    (by decide) (lookupName_fusedE9_shr env c gate bs73 bs74 h)

theorem lookupName_fusedE96_xp (env : Env) (c : FusedCarry) (gate : BitVec 1)
    (bs73 bs74 : List UInt8) {xp : Nat}
    (h : lookupName env "%xp" = some (.ptr xp)) :
    lookupName (fusedE96 env c gate bs73 bs74) "%xp" = some (.ptr xp) :=
  lookupName_fusedE96_of env c gate bs73 bs74 (by decide) (by decide) (by decide)
    (by decide) (lookupName_fusedE9_xp env c gate bs73 bs74 h)

theorem lookupName_fusedE96_nxp (env : Env) (c : FusedCarry) (gate : BitVec 1)
    (bs73 bs74 : List UInt8) {nxp : Nat}
    (h : lookupName env "%nxp" = some (.ptr nxp)) :
    lookupName (fusedE96 env c gate bs73 bs74) "%nxp" = some (.ptr nxp) :=
  lookupName_fusedE96_of env c gate bs73 bs74 (by decide) (by decide) (by decide)
    (by decide) (lookupName_fusedE9_nxp env c gate bs73 bs74 h)

theorem lookupName_fusedE96_xcarry (env : Env) (c : FusedCarry) (gate : BitVec 1)
    (bs73 bs74 : List UInt8) {xcarry : Nat}
    (h : lookupName env "%xcarry" = some (.ptr xcarry)) :
    lookupName (fusedE96 env c gate bs73 bs74) "%xcarry" = some (.ptr xcarry) :=
  lookupName_fusedE96_of env c gate bs73 bs74 (by decide) (by decide) (by decide)
    (by decide) (lookupName_fusedE9_xcarry env c gate bs73 bs74 h)

theorem lookupName_fusedE96_tobool87 (env : Env) (c : FusedCarry) (gate : BitVec 1)
    (bs73 bs74 : List UInt8) {g : BitVec 1}
    (h : lookupName env "%tobool87" = some (.int 1 g)) :
    lookupName (fusedE96 env c gate bs73 bs74) "%tobool87" = some (.int 1 g) :=
  lookupName_fusedE96_of env c gate bs73 bs74 (by decide) (by decide) (by decide)
    (by decide) (lookupName_fusedE9_tobool87 env c gate bs73 bs74 h)

theorem lookupName_fusedE96_tobool95 (env : Env) (c : FusedCarry) (gate : BitVec 1)
    (bs73 bs74 : List UInt8) {e : BitVec 1}
    (h : lookupName env "%tobool95.not" = some (.int 1 e)) :
    lookupName (fusedE96 env c gate bs73 bs74) "%tobool95.not" = some (.int 1 e) :=
  lookupName_fusedE96_of env c gate bs73 bs74 (by decide) (by decide) (by decide)
    (by decide) (lookupName_fusedE9_tobool95 env c gate bs73 bs74 h)

/-- **One page on the merge's escape arm.**  The body's run and step, the merge
at `%u8k.1521` with the escape bit clear, the record's call at the caller's
selection, and the latch's invariant at the record's environment with the call's
own memory and cursor. -/
theorem fused_merge_escape_page (sel : Calls) (env : Env) (s : State) (c : FusedCarry)
    (gate : BitVec 1) (bs73 bs74 : List UInt8)
    (hinv : FusedInv env s c gate 0)
    (hshr57 : c.shr.toNat < 2 ^ 57)
    (hread73 : readBytes c.mem (c.b + 64 * c.i.toNat) 32 = some bs73)
    (hread74 : readBytes c.mem (c.b + 64 * c.i.toNat + 32) 32 = some bs74)
    (hdec : fb54Select gate (fusedValues c bs73 bs74).v107 = 1)
    (r : CallOutcome)
    (hc : sel escapeListCallee
      [.int 64 (fusedValues c bs73 bs74).or14,
       .int 64 (ifThen96Mask (fusedValues c bs73 bs74).w73
         (fusedValues c bs73 bs74).w74),
       .int 64 (fusedValues c bs73 bs74).xorI, .int 64 c.i,
       .ptr c.xp, .ptr c.nxp, .ptr c.xcarry]
      (fusedStore c bs73 bs74) s.next = some r) :
    step (s1BlocksCallsEsc sel) s1BlocksFunction (stateAt env s) =
      .jump (fusedBodyState env s c gate bs73 bs74) ∧
    step (s1BlocksCallsEsc sel) s1BlocksFunction (fusedBodyState env s c gate bs73 bs74) =
      .jump (fusedEscapeState env s c gate bs73 bs74) ∧
    step (s1BlocksCallsEsc sel) s1BlocksFunction (fusedEscapeState env s c gate bs73 bs74) =
      .jump (fusedEscapedLatchState env s c gate bs73 bs74 r) ∧
    FusedLatch (fusedE96 env c gate bs73 bs74)
      (fusedEscapedLatchCore s c bs73 bs74 r)
      c.i (fusedNext c bs73 bs74 c.u8k r.mem) gate 0 := by
  have hbody := fused_body_run env s c gate 0 bs73 bs74 hinv hshr57 hread73 hread74
  have hbit : lookupName (fusedE3 env c gate bs73 bs74) "%or.cond189"
      = some (.int 1 1) := by
    rw [show fusedE3 env c gate bs73 bs74
        = fb54Env9 env (fusedValues c bs73 bs74) gate from rfl,
      lookupName_fb54Env9_cond189]
    show some (Value.int 1 (fb54Select gate (fusedValues c bs73 bs74).v107))
      = some (Value.int 1 1)
    rw [hdec]
  have h01 : step (s1BlocksCallsEsc sel) s1BlocksFunction (stateAt env s) =
      .jump (fusedBodyState env s c gate bs73 bs74) := by
    rw [step_esc_of_free sel s1BlocksFunction (stateAt env s) for_body54Block
      (by rw [show (stateAt env s).pc = s.pc from rfl, hinv.pc]
          exact findBlock_for_body54) (by decide)]
    rw [show fusedBodyState env s c gate bs73 bs74
        = stateAt (fb54Env9 env (fusedValues c bs73 bs74) gate)
            { s with
              pc := "if.end93",
              pre := some "for.body54",
              mem := writeBytes c.mem (fusedValues c bs73 bs74).arrayidx
                (natToBytes (fusedValues c bs73 bs74).or84.toNat 8) } from rfl,
      ← hinv.mem]
    exact for_body54_step_end env s (fusedValues c bs73 bs74) gate hinv.pc hbit hbody
  have hesc : lookupName (fusedE3 env c gate bs73 bs74) "%tobool95.not"
      = some (.int 1 0) := by
    rw [show fusedE3 env c gate bs73 bs74
        = fb54Env9 env (fusedValues c bs73 bs74) gate from rfl]
    exact lookupName_fb54Env9_tobool95 env _ gate hinv.escape
  have h12 : step (s1BlocksCallsEsc sel) s1BlocksFunction
      (fusedBodyState env s c gate bs73 bs74) =
      .jump (fusedEscapeState env s c gate bs73 bs74) := by
    rw [step_esc_of_free sel s1BlocksFunction _ if_end93Block
      (by rw [show (fusedBodyState env s c gate bs73 bs74).pc = "if.end93" from rfl]
          exact findBlock_if_end93) (by decide)]
    exact if_end93_step_escape (fusedE3 env c gate bs73 bs74)
      (fusedBodyState env s c gate bs73 bs74) "for.body54" (.reg "%u8k.1521")
      c.u8k 0 rfl rfl (by simp [phiIncoming])
      (BlockEval.evalOperand_reg_of _ _ _ _
        (lookupName_fb54Env9_u8k env (fusedValues c bs73 bs74) gate))
      hesc rfl
  have h23 : step (s1BlocksCallsEsc sel) s1BlocksFunction
      (fusedEscapeState env s c gate bs73 bs74) =
      .jump (fusedEscapedLatchState env s c gate bs73 bs74 r) :=
    if_then96_step sel (fusedE9 env c gate bs73 bs74)
      (fusedEscapeState env s c gate bs73 bs74)
      (fusedValues c bs73 bs74).w73 (fusedValues c bs73 bs74).w74
      (fusedValues_w73_length c bs73 bs74) (fusedValues_w74_length c bs73 bs74)
      (fusedValues c bs73 bs74).or14 (fusedValues c bs73 bs74).xorI c.i
      c.xp c.nxp c.xcarry r rfl
      (lookupName_fusedE9_w73 env c gate bs73 bs74)
      (lookupName_fusedE9_w74 env c gate bs73 bs74)
      (lookupName_fusedE9_or14 env c gate bs73 bs74)
      (lookupName_fusedE9_xorI env c gate bs73 bs74)
      (lookupName_fusedE9_i env c gate bs73 bs74)
      (lookupName_fusedE9_xp env c gate bs73 bs74 hinv.stream)
      (lookupName_fusedE9_nxp env c gate bs73 bs74 hinv.count)
      (lookupName_fusedE9_xcarry env c gate bs73 bs74 hinv.carry)
      hc
  refine ⟨h01, h12, h23, ?_⟩
  refine
    { pc := rfl
      mem := rfl
      index := lookupName_fusedE96_i env c gate bs73 bs74
      prevS := lookupName_fusedE96_shr85 env c gate bs73 bs74
      ascii := lookupName_fusedE96_or282 env c gate bs73 bs74
      u8k := lookupName_fusedE96_u8k env c gate bs73 bs74 c.u8k rfl
      prevAscii := lookupName_fusedE96_p75 env c gate bs73 bs74
      st0 := lookupName_fusedE96_shrII env c gate bs73 bs74
      st9 := lookupName_fusedE96_conv13 env c gate bs73 bs74
      st15 := lookupName_fusedE96_shrI env c gate bs73 bs74
      base := lookupName_fusedE96_b env c gate bs73 bs74 hinv.base
      emit := lookupName_fusedE96_ent env c gate bs73 bs74 hinv.emit
      bound := lookupName_fusedE96_shr env c gate bs73 bs74 hinv.bound
      stream := lookupName_fusedE96_xp env c gate bs73 bs74 hinv.stream
      count := lookupName_fusedE96_nxp env c gate bs73 bs74 hinv.count
      carry := lookupName_fusedE96_xcarry env c gate bs73 bs74 hinv.carry
      gate := lookupName_fusedE96_tobool87 env c gate bs73 bs74 hinv.gate
      escape := lookupName_fusedE96_tobool95 env c gate bs73 bs74 hinv.escape
      succ := rfl
      index_lt := hinv.index_lt
      ascii_len := fusedNext_ascii_length c bs73 bs74 c.u8k r.mem hinv.ascii_len
      u8k_len := hinv.u8k_len }

/-! ### The stacks above the body's environment

A latch's environment is the body's, then the merge's `%u8k.2`, then — on the
DFA arm — the arm's fifty cells, then the record's four.  Each layer's keys are
the block's own, so a read that misses them reaches the layer beneath.  The peel
lemmas below are that step, once per layer, and the arm's key list is its six
environments' keys: a name the latch reads is in none of them. -/

/-- A read that misses the merge's cell reaches the environment beneath. -/
theorem lookupName_ifEnd93Env_of (env : Env) (u8k : List (BitVec 64))
    {n : String} {val : Value} (hne : "%u8k.2" ≠ n)
    (h : lookupName env n = some val) :
    lookupName (ifEnd93Env env u8k) n = some val := by
  show lookupName (("%u8k.2", Value.vec 4 64 u8k) :: env) n = some val
  rw [lookupName_cons_ne _ _ hne]
  exact h

/-- A read that misses the escape record's four cells reaches the environment
beneath. -/
theorem lookupName_ifThen96Out_of (env : Env) (a2 a3 : List (BitVec 64))
    {n : String} {val : Value}
    (h1 : "%or.i379" ≠ n) (h2 : "%135" ≠ n) (h3 : "%134" ≠ n) (h4 : "%133" ≠ n)
    (h : lookupName env n = some val) :
    lookupName (ifThen96Out env a2 a3) n = some val := by
  show lookupName (("%or.i379", Value.int 64 (ifThen96Mask a2 a3)) ::
      ("%135", Value.vec 64 1 (icmpLanes .ult
        (bitcastVecLanes 8 64 (a2 ++ a3)) (List.replicate 64 0x20#8))) ::
      ("%134", Value.vec 64 8 (bitcastVecLanes 8 64 (a2 ++ a3))) ::
      ("%133", Value.vec 8 64 (a2 ++ a3)) :: env) n = some val
  rw [lookupName_cons_ne _ _ h1, lookupName_cons_ne _ _ h2,
    lookupName_cons_ne _ _ h3, lookupName_cons_ne _ _ h4]
  exact h

/-- A read that misses the latch's two cells reaches the environment beneath. -/
theorem lookupName_ifEnd98Env_of (env : Env) (i shr : BitVec 64)
    {n : String} {val : Value}
    (h1 : "%exitcond537.not" ≠ n) (h2 : "%inc100" ≠ n)
    (h : lookupName env n = some val) :
    lookupName (ifEnd98Env env i shr) n = some val := by
  show lookupName (("%exitcond537.not", Value.int 1 (evalICmp .eq (i + 1) shr)) ::
      ("%inc100", Value.int 64 (i + 1)) :: env) n = some val
  rw [lookupName_cons_ne _ _ h1, lookupName_cons_ne _ _ h2]
  exact h

/-- The latch's increment cell, as its own environment leaves it. -/
theorem lookupName_ifEnd98Env_inc100 (env : Env) (i shr : BitVec 64) :
    lookupName (ifEnd98Env env i shr) "%inc100" = some (.int 64 (i + 1)) := by
  show lookupName (("%exitcond537.not", Value.int 1 (evalICmp .eq (i + 1) shr)) ::
      ("%inc100", Value.int 64 (i + 1)) :: env) "%inc100" = some (.int 64 (i + 1))
  rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_self]

/-- The keys the DFA arm binds: its six environments' cells, outermost last. -/
def ift90Keys : List String :=
  ["%110", "%add.ptr5.i.i351", "%109", "%add.ptr3.i.i350", "%108", "%add.ptr.i.i349",
   "%and.i3741.i.i352", "%118", "%117", "%116", "%115", "%114", "%113", "%112",
   "%111", "%xor.i.i.i360", "%and.i.i.i359", "%or.i.i.i358", "%or.i43.i.i357",
   "%elt.sat.i.i.i356", "%elt.sat.i40.i.i355", "%and.i35.i.i354",
   "%and.i3542.i.i353", "%119", "%122", "%add.ptr5.i6.i363", "%121",
   "%add.ptr3.i5.i362", "%120", "%add.ptr.i4.i361", "%and.i3741.i7.i364", "%130",
   "%129", "%128", "%127", "%126", "%125", "%124", "%123", "%or.i281", "%132",
   "%xor.i.i15.i372", "%and.i.i14.i371", "%or.i.i13.i370", "%or.i43.i12.i369",
   "%elt.sat.i.i11.i368", "%elt.sat.i40.i10.i367", "%and.i35.i9.i366",
   "%and.i3542.i8.i365", "%131"]

/-- A read that misses the DFA arm's fifty cells reaches the environment beneath.
The side condition is the arm's key list: for a name the latch reads it is a
`decide`d membership. -/
theorem lookupName_ifThen90Out_of (env : Env) (v : IfThen90Values)
    {n : String} {val : Value} (hne : ∀ k ∈ ift90Keys, k ≠ n)
    (h : lookupName env n = some val) :
    lookupName (ifThen90Out env v) n = some val := by
  simp only [ifThen90Out, ift90Env6, ift90Env5, ift90Env4, ift90Env3, ift90Env2,
    ift90Env1, cells]
  repeat rw [lookupName_cons_ne _ _ (fun he => hne _ (by decide) he)]
  exact h

/-- The arm's accumulator, as its own environment binds it. -/
theorem lookupName_ifThen90Out_or281 (env : Env) (v : IfThen90Values) :
    lookupName (ifThen90Out env v) "%or.i281" = some (.vec 4 64 v.or281) := by
  show lookupName ((("%or.i281", Value.vec 4 64 v.or281)) :: ift90Env5 env v)
    "%or.i281" = some (.vec 4 64 v.or281)
  rw [lookupName_cons_self]

/-! ### The DFA arm's environment

`if.then90` reads the row's neighbourhood — the three windows below its pointer,
the two low-nibble controls the body left, and the three windows above it — and
merges its accumulator at `if.end93`.  The arm's values and the three states its
edge reaches are named below. -/

/-- The values `if.then90` binds at the page's row: its pointer, the body's two
controls and accumulator, and the six windows it loads. -/
def fusedDfa90 (c : FusedCarry) (bs73 bs74 : List UInt8)
    (bs41 bs42 bs43 bs57 bs58 bs59 : List UInt8) : IfThen90Values :=
  let v := fusedValues c bs73 bs74
  ifThen90Values v.addPtr57 v.low88 v.low97 c.u8k bs41 bs42 bs43 bs57 bs58 bs59

/-- The arm's environment: its fifty cells over the body's. -/
def fusedDfaEnv (env : Env) (c : FusedCarry) (gate : BitVec 1)
    (bs73 bs74 : List UInt8) (bs41 bs42 bs43 bs57 bs58 bs59 : List UInt8) : Env :=
  ifThen90Out (fusedE3 env c gate bs73 bs74)
    (fusedDfa90 c bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59)

/-- The state the body's cleared decision reaches: the DFA arm, with the page's
store. -/
def fusedDfaState (env : Env) (s : State) (c : FusedCarry) (gate : BitVec 1)
    (bs73 bs74 : List UInt8) : State :=
  stateAt (fusedE3 env c gate bs73 bs74)
    { s with pc := "if.then90", pre := some "for.body54", mem := fusedStore c bs73 bs74 }

/-- The merge's entry on the DFA arm. -/
def fusedDfaMergeState (env : Env) (s : State) (c : FusedCarry) (gate : BitVec 1)
    (bs73 bs74 : List UInt8) (bs41 bs42 bs43 bs57 bs58 bs59 : List UInt8) : State :=
  stateAt (fusedDfaEnv env c gate bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59)
    { s with pc := "if.end93", pre := some "if.then90", mem := fusedStore c bs73 bs74 }

/-- The latch's entry on the DFA arm's skip branch. -/
def fusedDfaLatchState (env : Env) (s : State) (c : FusedCarry) (gate : BitVec 1)
    (bs73 bs74 : List UInt8) (bs41 bs42 bs43 bs57 bs58 bs59 : List UInt8) : State :=
  stateAt
    (ifEnd93Env (fusedDfaEnv env c gate bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59)
      (fusedDfa90 c bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59).or281)
    (fusedDfaLatchCore s c bs73 bs74)

/-- The latch's entry on the DFA arm's escape branch. -/
def fusedDfaEscapedLatchState (env : Env) (s : State) (c : FusedCarry) (gate : BitVec 1)
    (bs73 bs74 : List UInt8) (bs41 bs42 bs43 bs57 bs58 bs59 : List UInt8)
    (r : CallOutcome) : State :=
  stateAt
    (ifThen96Out
      (ifEnd93Env (fusedDfaEnv env c gate bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59)
        (fusedDfa90 c bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59).or281)
      (fusedValues c bs73 bs74).w73 (fusedValues c bs73 bs74).w74)
    (fusedDfaEscapedLatchCore s c bs73 bs74 r)


/-- The DFA arm's latch environment: the merged accumulator over the arm's. -/
def fusedDfaLatchEnv (env : Env) (c : FusedCarry) (gate : BitVec 1)
    (bs73 bs74 : List UInt8) (bs41 bs42 bs43 bs57 bs58 bs59 : List UInt8) : Env :=
  ifEnd93Env (fusedDfaEnv env c gate bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59)
    (fusedDfa90 c bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59).or281

/-- The DFA arm's escaped latch environment: the record's four cells over it. -/
def fusedDfaEscapedLatchEnv (env : Env) (c : FusedCarry) (gate : BitVec 1)
    (bs73 bs74 : List UInt8) (bs41 bs42 bs43 bs57 bs58 bs59 : List UInt8) : Env :=
  ifThen96Out (fusedDfaLatchEnv env c gate bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59)
    (fusedValues c bs73 bs74).w73 (fusedValues c bs73 bs74).w74

/-- The six windows the arm reads are below the body's store, so the page's
memory reads them unchanged. -/
theorem fused_dfa_window_below (c : FusedCarry) (bs73 bs74 : List UInt8)
    {a n : Nat} (h : a + n ≤ c.ent) :
    readBytes (fusedStore c bs73 bs74) a n = readBytes c.mem a n := by
  show readBytes (writeBytes c.mem (fusedValues c bs73 bs74).arrayidx
    (natToBytes (fusedValues c bs73 bs74).or84.toNat 8)) a n = readBytes c.mem a n
  rw [fusedValues_arrayidx]
  exact readBytes_writeBytes_below c.mem _ n a (c.ent + 8 * c.i.toNat) (by omega)

/-! ### Reading the DFA arm's latch environment

The arm's fifty cells shadow none of the latch's names, so each of the latch's
readings is one peel of the arm and one of the merge. -/


theorem lookupName_fusedDfaLatch_shr85 (env : Env) (c : FusedCarry) (gate : BitVec 1)
    (bs73 bs74 : List UInt8) (bs41 bs42 bs43 bs57 bs58 bs59 : List UInt8) :
    lookupName (fusedDfaLatchEnv env c gate bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59) "%shr85" = some (.int 64 (fusedValues c bs73 bs74).shr85) :=
  lookupName_ifEnd93Env_of (fusedDfaEnv env c gate bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59) _ (by decide)
    (lookupName_ifThen90Out_of (fusedE3 env c gate bs73 bs74)
      (fusedDfa90 c bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59) (by decide)
      (lookupName_fb54Env9_shr85 env (fusedValues c bs73 bs74) gate))

theorem lookupName_fusedDfaLatch_or282 (env : Env) (c : FusedCarry) (gate : BitVec 1)
    (bs73 bs74 : List UInt8) (bs41 bs42 bs43 bs57 bs58 bs59 : List UInt8) :
    lookupName (fusedDfaLatchEnv env c gate bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59) "%or.i282" = some (.vec 4 64 (fusedAscii c bs73 bs74)) :=
  lookupName_ifEnd93Env_of (fusedDfaEnv env c gate bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59) _ (by decide)
    (lookupName_ifThen90Out_of (fusedE3 env c gate bs73 bs74)
      (fusedDfa90 c bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59) (by decide)
      (lookupName_fb54Env9_or282 env (fusedValues c bs73 bs74) gate))

theorem lookupName_fusedDfaLatch_p75 (env : Env) (c : FusedCarry) (gate : BitVec 1)
    (bs73 bs74 : List UInt8) (bs41 bs42 bs43 bs57 bs58 bs59 : List UInt8) :
    lookupName (fusedDfaLatchEnv env c gate bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59) "%75" = some (.int 32 (fusedPrevAscii c bs73 bs74)) :=
  lookupName_ifEnd93Env_of (fusedDfaEnv env c gate bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59) _ (by decide)
    (lookupName_ifThen90Out_of (fusedE3 env c gate bs73 bs74)
      (fusedDfa90 c bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59) (by decide)
      (lookupName_fb54Env9_p75 env (fusedValues c bs73 bs74) gate))

theorem lookupName_fusedDfaLatch_shrII (env : Env) (c : FusedCarry) (gate : BitVec 1)
    (bs73 bs74 : List UInt8) (bs41 bs42 bs43 bs57 bs58 bs59 : List UInt8) :
    lookupName (fusedDfaLatchEnv env c gate bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59) "%shr.i.i325" = some (.int 64 (fusedValues c bs73 bs74).shrII) :=
  lookupName_ifEnd93Env_of (fusedDfaEnv env c gate bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59) _ (by decide)
    (lookupName_ifThen90Out_of (fusedE3 env c gate bs73 bs74)
      (fusedDfa90 c bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59) (by decide)
      (lookupName_fb54Env9_shrII env (fusedValues c bs73 bs74) gate))

theorem lookupName_fusedDfaLatch_conv13 (env : Env) (c : FusedCarry) (gate : BitVec 1)
    (bs73 bs74 : List UInt8) (bs41 bs42 bs43 bs57 bs58 bs59 : List UInt8) :
    lookupName (fusedDfaLatchEnv env c gate bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59) "%conv13.i.i324" = some (.int 64 (fusedValues c bs73 bs74).conv13II) :=
  lookupName_ifEnd93Env_of (fusedDfaEnv env c gate bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59) _ (by decide)
    (lookupName_ifThen90Out_of (fusedE3 env c gate bs73 bs74)
      (fusedDfa90 c bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59) (by decide)
      (lookupName_fb54Env9_conv13 env (fusedValues c bs73 bs74) gate))

theorem lookupName_fusedDfaLatch_shrI (env : Env) (c : FusedCarry) (gate : BitVec 1)
    (bs73 bs74 : List UInt8) (bs41 bs42 bs43 bs57 bs58 bs59 : List UInt8) :
    lookupName (fusedDfaLatchEnv env c gate bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59) "%shr.i348" = some (.int 64 (fusedValues c bs73 bs74).shrI) :=
  lookupName_ifEnd93Env_of (fusedDfaEnv env c gate bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59) _ (by decide)
    (lookupName_ifThen90Out_of (fusedE3 env c gate bs73 bs74)
      (fusedDfa90 c bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59) (by decide)
      (lookupName_fb54Env9_shrI env (fusedValues c bs73 bs74) gate))

theorem lookupName_fusedDfaLatch_i (env : Env) (c : FusedCarry) (gate : BitVec 1)
    (bs73 bs74 : List UInt8) (bs41 bs42 bs43 bs57 bs58 bs59 : List UInt8) :
    lookupName (fusedDfaLatchEnv env c gate bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59) "%i.2523" = some (.int 64 c.i) :=
  lookupName_ifEnd93Env_of (fusedDfaEnv env c gate bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59) _ (by decide)
    (lookupName_ifThen90Out_of (fusedE3 env c gate bs73 bs74)
      (fusedDfa90 c bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59) (by decide)
      (lookupName_fb54Env9_i env (fusedValues c bs73 bs74) gate))

theorem lookupName_fusedDfaLatch_u8k (env : Env) (c : FusedCarry) (gate : BitVec 1)
    (bs73 bs74 : List UInt8) (bs41 bs42 bs43 bs57 bs58 bs59 : List UInt8) :
    lookupName (fusedDfaLatchEnv env c gate bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59) "%u8k.2"
      = some (.vec 4 64 (fusedDfa90 c bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59).or281) := by
  show lookupName (("%u8k.2", Value.vec 4 64
      (fusedDfa90 c bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59).or281) ::
      fusedDfaEnv env c gate bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59) "%u8k.2"
    = some (.vec 4 64 (fusedDfa90 c bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59).or281)
  rw [lookupName_cons_self]

theorem lookupName_fusedDfaLatch_b (env : Env) (c : FusedCarry) (gate : BitVec 1)
    (bs73 bs74 : List UInt8) (bs41 bs42 bs43 bs57 bs58 bs59 : List UInt8) {b : Nat} (h : lookupName env "%b" = some (.ptr b)) :
    lookupName (fusedDfaLatchEnv env c gate bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59) "%b" = some (.ptr b) :=
  lookupName_ifEnd93Env_of (fusedDfaEnv env c gate bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59) _ (by decide)
    (lookupName_ifThen90Out_of (fusedE3 env c gate bs73 bs74)
      (fusedDfa90 c bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59) (by decide)
      (lookupName_fb54Env9_b env (fusedValues c bs73 bs74) gate h))

theorem lookupName_fusedDfaLatch_ent (env : Env) (c : FusedCarry) (gate : BitVec 1)
    (bs73 bs74 : List UInt8) (bs41 bs42 bs43 bs57 bs58 bs59 : List UInt8) {ent : Nat} (h : lookupName env "%ent" = some (.ptr ent)) :
    lookupName (fusedDfaLatchEnv env c gate bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59) "%ent" = some (.ptr ent) :=
  lookupName_ifEnd93Env_of (fusedDfaEnv env c gate bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59) _ (by decide)
    (lookupName_ifThen90Out_of (fusedE3 env c gate bs73 bs74)
      (fusedDfa90 c bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59) (by decide)
      (lookupName_fb54Env9_ent env (fusedValues c bs73 bs74) gate h))

theorem lookupName_fusedDfaLatch_shr (env : Env) (c : FusedCarry) (gate : BitVec 1)
    (bs73 bs74 : List UInt8) (bs41 bs42 bs43 bs57 bs58 bs59 : List UInt8) {shr : BitVec 64} (h : lookupName env "%shr" = some (.int 64 shr)) :
    lookupName (fusedDfaLatchEnv env c gate bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59) "%shr" = some (.int 64 shr) :=
  lookupName_ifEnd93Env_of (fusedDfaEnv env c gate bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59) _ (by decide)
    (lookupName_ifThen90Out_of (fusedE3 env c gate bs73 bs74)
      (fusedDfa90 c bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59) (by decide)
      (lookupName_fb54Env9_shr env (fusedValues c bs73 bs74) gate h))

theorem lookupName_fusedDfaLatch_xp (env : Env) (c : FusedCarry) (gate : BitVec 1)
    (bs73 bs74 : List UInt8) (bs41 bs42 bs43 bs57 bs58 bs59 : List UInt8) {xp : Nat} (h : lookupName env "%xp" = some (.ptr xp)) :
    lookupName (fusedDfaLatchEnv env c gate bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59) "%xp" = some (.ptr xp) :=
  lookupName_ifEnd93Env_of (fusedDfaEnv env c gate bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59) _ (by decide)
    (lookupName_ifThen90Out_of (fusedE3 env c gate bs73 bs74)
      (fusedDfa90 c bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59) (by decide)
      (lookupName_fb54Env9_xp env (fusedValues c bs73 bs74) gate h))

theorem lookupName_fusedDfaLatch_nxp (env : Env) (c : FusedCarry) (gate : BitVec 1)
    (bs73 bs74 : List UInt8) (bs41 bs42 bs43 bs57 bs58 bs59 : List UInt8) {nxp : Nat} (h : lookupName env "%nxp" = some (.ptr nxp)) :
    lookupName (fusedDfaLatchEnv env c gate bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59) "%nxp" = some (.ptr nxp) :=
  lookupName_ifEnd93Env_of (fusedDfaEnv env c gate bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59) _ (by decide)
    (lookupName_ifThen90Out_of (fusedE3 env c gate bs73 bs74)
      (fusedDfa90 c bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59) (by decide)
      (lookupName_fb54Env9_nxp env (fusedValues c bs73 bs74) gate h))

theorem lookupName_fusedDfaLatch_xcarry (env : Env) (c : FusedCarry) (gate : BitVec 1)
    (bs73 bs74 : List UInt8) (bs41 bs42 bs43 bs57 bs58 bs59 : List UInt8) {xcarry : Nat} (h : lookupName env "%xcarry" = some (.ptr xcarry)) :
    lookupName (fusedDfaLatchEnv env c gate bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59) "%xcarry" = some (.ptr xcarry) :=
  lookupName_ifEnd93Env_of (fusedDfaEnv env c gate bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59) _ (by decide)
    (lookupName_ifThen90Out_of (fusedE3 env c gate bs73 bs74)
      (fusedDfa90 c bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59) (by decide)
      (lookupName_fb54Env9_xcarry env (fusedValues c bs73 bs74) gate h))

theorem lookupName_fusedDfaLatch_tobool87 (env : Env) (c : FusedCarry) (gate : BitVec 1)
    (bs73 bs74 : List UInt8) (bs41 bs42 bs43 bs57 bs58 bs59 : List UInt8) {g : BitVec 1} (h : lookupName env "%tobool87" = some (.int 1 g)) :
    lookupName (fusedDfaLatchEnv env c gate bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59) "%tobool87" = some (.int 1 g) :=
  lookupName_ifEnd93Env_of (fusedDfaEnv env c gate bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59) _ (by decide)
    (lookupName_ifThen90Out_of (fusedE3 env c gate bs73 bs74)
      (fusedDfa90 c bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59) (by decide)
      (lookupName_fb54Env9_tobool87 env (fusedValues c bs73 bs74) gate h))

theorem lookupName_fusedDfaLatch_tobool95 (env : Env) (c : FusedCarry) (gate : BitVec 1)
    (bs73 bs74 : List UInt8) (bs41 bs42 bs43 bs57 bs58 bs59 : List UInt8) {e : BitVec 1} (h : lookupName env "%tobool95.not" = some (.int 1 e)) :
    lookupName (fusedDfaLatchEnv env c gate bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59) "%tobool95.not" = some (.int 1 e) :=
  lookupName_ifEnd93Env_of (fusedDfaEnv env c gate bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59) _ (by decide)
    (lookupName_ifThen90Out_of (fusedE3 env c gate bs73 bs74)
      (fusedDfa90 c bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59) (by decide)
      (lookupName_fb54Env9_tobool95 env (fusedValues c bs73 bs74) gate h))

/-- The escape bit through the arm's cells. -/
theorem lookupName_fusedDfaEnv_tobool95 (env : Env) (c : FusedCarry) (gate : BitVec 1)
    (bs73 bs74 : List UInt8) (bs41 bs42 bs43 bs57 bs58 bs59 : List UInt8)
    {e : BitVec 1} (h : lookupName env "%tobool95.not" = some (.int 1 e)) :
    lookupName (fusedDfaEnv env c gate bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59) "%tobool95.not" = some (.int 1 e) :=
  lookupName_ifThen90Out_of (fusedE3 env c gate bs73 bs74)
    (fusedDfa90 c bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59) (by decide)
    (lookupName_fb54Env9_tobool95 env (fusedValues c bs73 bs74) gate h)

/-- The arm's accumulator, as the merge reads it. -/
theorem lookupName_fusedDfaEnv_or281 (env : Env) (c : FusedCarry) (gate : BitVec 1)
    (bs73 bs74 : List UInt8) (bs41 bs42 bs43 bs57 bs58 bs59 : List UInt8) :
    lookupName (fusedDfaEnv env c gate bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59) "%or.i281"
      = some (.vec 4 64 (fusedDfa90 c bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59).or281) :=
  lookupName_ifThen90Out_or281 (fusedE3 env c gate bs73 bs74)
    (fusedDfa90 c bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59)

/-! ### The DFA arm's two pages

The body's cleared decision runs the classifier's DFA step on the row's
neighbourhood and merges its accumulator; the merge then takes the same two
branches the silent arm takes.  The six window reads are stated at the carry's
memory and moved to the page's, the body's store being above them. -/

/-- **One page on the DFA arm's skip branch.** -/
theorem fused_dfa_skip_page (sel : Calls) (env : Env) (s : State) (c : FusedCarry)
    (gate : BitVec 1) (bs73 bs74 : List UInt8)
    (bs41 bs42 bs43 bs57 bs58 bs59 : List UInt8)
    (hinv : FusedInv env s c gate 1)
    (hshr57 : c.shr.toNat < 2 ^ 57)
    (hb3 : 3 ≤ c.b)
    (hgap : c.b + 64 * c.shr.toNat ≤ c.ent)
    (hread73 : readBytes c.mem (c.b + 64 * c.i.toNat) 32 = some bs73)
    (hread74 : readBytes c.mem (c.b + 64 * c.i.toNat + 32) 32 = some bs74)
    (hdec : fb54Select gate (fusedValues c bs73 bs74).v107 = 0)
    (h41 : readBytes c.mem (c.b + 64 * c.i.toNat - 1) 32 = some bs41)
    (h42 : readBytes c.mem (c.b + 64 * c.i.toNat - 2) 32 = some bs42)
    (h43 : readBytes c.mem (c.b + 64 * c.i.toNat - 3) 32 = some bs43)
    (h57 : readBytes c.mem (c.b + 64 * c.i.toNat + 31) 32 = some bs57)
    (h58 : readBytes c.mem (c.b + 64 * c.i.toNat + 30) 32 = some bs58)
    (h59 : readBytes c.mem (c.b + 64 * c.i.toNat + 29) 32 = some bs59) :
    step (s1BlocksCallsEsc sel) s1BlocksFunction (stateAt env s) =
      .jump (fusedDfaState env s c gate bs73 bs74) ∧
    step (s1BlocksCallsEsc sel) s1BlocksFunction (fusedDfaState env s c gate bs73 bs74) =
      .jump (fusedDfaMergeState env s c gate bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59) ∧
    step (s1BlocksCallsEsc sel) s1BlocksFunction (fusedDfaMergeState env s c gate bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59) =
      .jump (fusedDfaLatchState env s c gate bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59) ∧
    FusedLatch (fusedDfaLatchEnv env c gate bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59)
      (fusedDfaLatchCore s c bs73 bs74) c.i
      (fusedNext c bs73 bs74 (fusedDfa90 c bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59).or281
        (fusedStore c bs73 bs74)) gate 1 := by
  have hi : c.i.toNat < c.shr.toNat := hinv.index_lt
  have hj57 : c.i.toNat < 2 ^ 57 := by omega
  have ha : (fusedValues c bs73 bs74).addPtr57 = c.b + 64 * c.i.toNat :=
    fusedValues_addPtr57 c bs73 bs74 hj57
  have h1 : 1 ≤ (fusedValues c bs73 bs74).addPtr57 := by rw [ha]; omega
  have h2 : 2 ≤ (fusedValues c bs73 bs74).addPtr57 := by rw [ha]; omega
  have h3 : 3 ≤ (fusedValues c bs73 bs74).addPtr57 := by rw [ha]; omega
  have hbit : lookupName (fusedE3 env c gate bs73 bs74) "%or.cond189"
      = some (.int 1 0) := by
    rw [show fusedE3 env c gate bs73 bs74
        = fb54Env9 env (fusedValues c bs73 bs74) gate from rfl, lookupName_fb54Env9_cond189]
    show some (Value.int 1 (fb54Select gate (fusedValues c bs73 bs74).v107)) = some (Value.int 1 0)
    rw [hdec]
  have hbody := fused_body_run env s c gate 1 bs73 bs74 hinv hshr57 hread73 hread74
  have h01 : step (s1BlocksCallsEsc sel) s1BlocksFunction (stateAt env s) =
      .jump (fusedDfaState env s c gate bs73 bs74) := by
    rw [step_esc_of_free sel s1BlocksFunction (stateAt env s) for_body54Block
      (by rw [show (stateAt env s).pc = s.pc from rfl, hinv.pc]
          exact findBlock_for_body54) (by decide)]
    rw [show fusedDfaState env s c gate bs73 bs74
        = stateAt (fb54Env9 env (fusedValues c bs73 bs74) gate)
            { s with
              pc := "if.then90",
              pre := some "for.body54",
              mem := writeBytes c.mem (fusedValues c bs73 bs74).arrayidx
                (natToBytes (fusedValues c bs73 bs74).or84.toNat 8) } from rfl,
      ← hinv.mem]
    exact for_body54_step_escape env s (fusedValues c bs73 bs74) gate hinv.pc hbit hbody
  have h41' : readBytes (fusedDfaState env s c gate bs73 bs74).mem ((fusedValues c bs73 bs74).addPtr57 - 1) 32 = some bs41 := by
    show readBytes (fusedStore c bs73 bs74) ((fusedValues c bs73 bs74).addPtr57 - 1) 32 = some bs41
    rw [fusedValues_addPtr57 c bs73 bs74 hj57]
    rw [fused_dfa_window_below c bs73 bs74 (a := c.b + 64 * c.i.toNat - 1)
      (n := 32) (by omega)]
    exact h41
  have h42' : readBytes (fusedDfaState env s c gate bs73 bs74).mem ((fusedValues c bs73 bs74).addPtr57 - 2) 32 = some bs42 := by
    show readBytes (fusedStore c bs73 bs74) ((fusedValues c bs73 bs74).addPtr57 - 2) 32 = some bs42
    rw [fusedValues_addPtr57 c bs73 bs74 hj57]
    rw [fused_dfa_window_below c bs73 bs74 (a := c.b + 64 * c.i.toNat - 2)
      (n := 32) (by omega)]
    exact h42
  have h43' : readBytes (fusedDfaState env s c gate bs73 bs74).mem ((fusedValues c bs73 bs74).addPtr57 - 3) 32 = some bs43 := by
    show readBytes (fusedStore c bs73 bs74) ((fusedValues c bs73 bs74).addPtr57 - 3) 32 = some bs43
    rw [fusedValues_addPtr57 c bs73 bs74 hj57]
    rw [fused_dfa_window_below c bs73 bs74 (a := c.b + 64 * c.i.toNat - 3)
      (n := 32) (by omega)]
    exact h43
  have h57' : readBytes (fusedDfaState env s c gate bs73 bs74).mem
      ((fusedValues c bs73 bs74).addPtr57 + ((0x000000000000001f#64).signExtend 64).toNat) 32 = some bs57 := by
    show readBytes (fusedStore c bs73 bs74)
      ((fusedValues c bs73 bs74).addPtr57 + ((0x000000000000001f#64).signExtend 64).toNat) 32 = some bs57
    rw [fusedValues_addPtr57 c bs73 bs74 hj57,
      show ((0x000000000000001f#64).signExtend 64).toNat = 31 from by decide]
    rw [fused_dfa_window_below c bs73 bs74 (a := c.b + 64 * c.i.toNat + 31)
      (n := 32) (by omega)]
    exact h57
  have h58' : readBytes (fusedDfaState env s c gate bs73 bs74).mem
      ((fusedValues c bs73 bs74).addPtr57 + ((0x000000000000001e#64).signExtend 64).toNat) 32 = some bs58 := by
    show readBytes (fusedStore c bs73 bs74)
      ((fusedValues c bs73 bs74).addPtr57 + ((0x000000000000001e#64).signExtend 64).toNat) 32 = some bs58
    rw [fusedValues_addPtr57 c bs73 bs74 hj57,
      show ((0x000000000000001e#64).signExtend 64).toNat = 30 from by decide]
    rw [fused_dfa_window_below c bs73 bs74 (a := c.b + 64 * c.i.toNat + 30)
      (n := 32) (by omega)]
    exact h58
  have h59' : readBytes (fusedDfaState env s c gate bs73 bs74).mem
      ((fusedValues c bs73 bs74).addPtr57 + ((0x000000000000001d#64).signExtend 64).toNat) 32 = some bs59 := by
    show readBytes (fusedStore c bs73 bs74)
      ((fusedValues c bs73 bs74).addPtr57 + ((0x000000000000001d#64).signExtend 64).toNat) 32 = some bs59
    rw [fusedValues_addPtr57 c bs73 bs74 hj57,
      show ((0x000000000000001d#64).signExtend 64).toNat = 29 from by decide]
    rw [fused_dfa_window_below c bs73 bs74 (a := c.b + 64 * c.i.toNat + 29)
      (n := 32) (by omega)]
    exact h59
  have h12 : step (s1BlocksCallsEsc sel) s1BlocksFunction (fusedDfaState env s c gate bs73 bs74) =
      .jump (fusedDfaMergeState env s c gate bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59) := by
    rw [step_esc_of_free sel s1BlocksFunction _ if_then90Block
      (by rw [show (fusedDfaState env s c gate bs73 bs74).pc = "if.then90" from rfl]
          exact findBlock_if_then90) (by decide)]
    exact if_then90_step (fusedE3 env c gate bs73 bs74) (fusedDfaState env s c gate bs73 bs74) (fusedDfa90 c bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59) rfl
      (if_then90_denote (fusedE3 env c gate bs73 bs74) (fusedDfaState env s c gate bs73 bs74) (fusedValues c bs73 bs74).addPtr57
        (fusedValues c bs73 bs74).low88 (fusedValues c bs73 bs74).low97 c.u8k bs41 bs42 bs43 bs57 bs58 bs59
        (lookupName_fb54Env9_addPtr57 env (fusedValues c bs73 bs74) gate) h1 h41' h2 h42' h3 h43'
        (lookupName_fb54Env9_p88 env (fusedValues c bs73 bs74) gate) (fusedValues_low88_length c bs73 bs74)
        (lookupName_fb54Env9_p97 env (fusedValues c bs73 bs74) gate) (fusedValues_low97_length c bs73 bs74)
        (lookupName_fb54Env9_u8k env (fusedValues c bs73 bs74) gate) hinv.u8k_len h57' h58' h59')
  have hesc : lookupName (fusedDfaEnv env c gate bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59) "%tobool95.not" = some (.int 1 1) :=
    lookupName_fusedDfaEnv_tobool95 env c gate bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59 hinv.escape
  have h23 : step (s1BlocksCallsEsc sel) s1BlocksFunction (fusedDfaMergeState env s c gate bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59) =
      .jump (fusedDfaLatchState env s c gate bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59) := by
    rw [step_esc_of_free sel s1BlocksFunction _ if_end93Block
      (by rw [show (fusedDfaMergeState env s c gate bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59).pc = "if.end93" from rfl]
          exact findBlock_if_end93) (by decide)]
    exact if_end93_step_skip (fusedDfaEnv env c gate bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59) (fusedDfaMergeState env s c gate bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59) "if.then90"
      (.reg "%or.i281") (fusedDfa90 c bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59).or281 1 rfl rfl (by simp [phiIncoming])
      (BlockEval.evalOperand_reg_of _ _ _ _ (lookupName_fusedDfaEnv_or281 env c gate bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59))
      hesc rfl
  refine ⟨h01, h12, h23, ?_⟩
  refine
    { pc := rfl
      mem := rfl
      index := lookupName_fusedDfaLatch_i env c gate bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59
      prevS := lookupName_fusedDfaLatch_shr85 env c gate bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59
      ascii := lookupName_fusedDfaLatch_or282 env c gate bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59
      u8k := lookupName_fusedDfaLatch_u8k env c gate bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59
      prevAscii := lookupName_fusedDfaLatch_p75 env c gate bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59
      st0 := lookupName_fusedDfaLatch_shrII env c gate bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59
      st9 := lookupName_fusedDfaLatch_conv13 env c gate bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59
      st15 := lookupName_fusedDfaLatch_shrI env c gate bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59
      base := lookupName_fusedDfaLatch_b env c gate bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59 hinv.base
      emit := lookupName_fusedDfaLatch_ent env c gate bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59 hinv.emit
      bound := lookupName_fusedDfaLatch_shr env c gate bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59 hinv.bound
      stream := lookupName_fusedDfaLatch_xp env c gate bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59 hinv.stream
      count := lookupName_fusedDfaLatch_nxp env c gate bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59 hinv.count
      carry := lookupName_fusedDfaLatch_xcarry env c gate bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59 hinv.carry
      gate := lookupName_fusedDfaLatch_tobool87 env c gate bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59 hinv.gate
      escape := lookupName_fusedDfaLatch_tobool95 env c gate bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59 hinv.escape
      succ := rfl
      index_lt := hinv.index_lt
      ascii_len := fusedNext_ascii_length c bs73 bs74 (fusedDfa90 c bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59).or281
        (fusedStore c bs73 bs74) hinv.ascii_len
      u8k_len := ifThen90Values_or281_length (fusedValues c bs73 bs74).addPtr57 (fusedValues c bs73 bs74).low88 (fusedValues c bs73 bs74).low97
        c.u8k bs41 bs42 bs43 bs57 bs58 bs59 hinv.u8k_len }

/-- The first loaded word through the arm and the merge. -/
theorem lookupName_fusedDfaLatch_w73 (env : Env) (c : FusedCarry) (gate : BitVec 1)
    (bs73 bs74 : List UInt8) (bs41 bs42 bs43 bs57 bs58 bs59 : List UInt8) :
    lookupName (fusedDfaLatchEnv env c gate bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59) "%73"
      = some (.vec 4 64 (fusedValues c bs73 bs74).w73) :=
  lookupName_ifEnd93Env_of (fusedDfaEnv env c gate bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59) _ (by decide)
    (lookupName_ifThen90Out_of (fusedE3 env c gate bs73 bs74) (fusedDfa90 c bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59) (by decide)
      (lookupName_fb54Env9_w73 env (fusedValues c bs73 bs74) gate))

/-- The second loaded word through the arm and the merge. -/
theorem lookupName_fusedDfaLatch_w74 (env : Env) (c : FusedCarry) (gate : BitVec 1)
    (bs73 bs74 : List UInt8) (bs41 bs42 bs43 bs57 bs58 bs59 : List UInt8) :
    lookupName (fusedDfaLatchEnv env c gate bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59) "%74"
      = some (.vec 4 64 (fusedValues c bs73 bs74).w74) :=
  lookupName_ifEnd93Env_of (fusedDfaEnv env c gate bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59) _ (by decide)
    (lookupName_ifThen90Out_of (fusedE3 env c gate bs73 bs74) (fusedDfa90 c bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59) (by decide)
      (lookupName_fb54Env9_w74 env (fusedValues c bs73 bs74) gate))

/-- The escape record's first argument through the arm and the merge. -/
theorem lookupName_fusedDfaLatch_or14 (env : Env) (c : FusedCarry) (gate : BitVec 1)
    (bs73 bs74 : List UInt8) (bs41 bs42 bs43 bs57 bs58 bs59 : List UInt8) :
    lookupName (fusedDfaLatchEnv env c gate bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59) "%or14.i303"
      = some (.int 64 (fusedValues c bs73 bs74).or14) :=
  lookupName_ifEnd93Env_of (fusedDfaEnv env c gate bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59) _ (by decide)
    (lookupName_ifThen90Out_of (fusedE3 env c gate bs73 bs74) (fusedDfa90 c bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59) (by decide)
      (lookupName_fb54Env9_or14 env (fusedValues c bs73 bs74) gate))

/-- The escape record's third argument through the arm and the merge. -/
theorem lookupName_fusedDfaLatch_xorI (env : Env) (c : FusedCarry) (gate : BitVec 1)
    (bs73 bs74 : List UInt8) (bs41 bs42 bs43 bs57 bs58 bs59 : List UInt8) :
    lookupName (fusedDfaLatchEnv env c gate bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59) "%xor.i347"
      = some (.int 64 (fusedValues c bs73 bs74).xorI) :=
  lookupName_ifEnd93Env_of (fusedDfaEnv env c gate bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59) _ (by decide)
    (lookupName_ifThen90Out_of (fusedE3 env c gate bs73 bs74) (fusedDfa90 c bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59) (by decide)
      (lookupName_fb54Env9_xorI env (fusedValues c bs73 bs74) gate))

/-! ### The DFA arm's escape page -/

/-- The escape record's entry on the DFA arm. -/
def fusedDfaEscapeState (env : Env) (s : State) (c : FusedCarry) (gate : BitVec 1)
    (bs73 bs74 : List UInt8) (bs41 bs42 bs43 bs57 bs58 bs59 : List UInt8) : State :=
  stateAt (fusedDfaLatchEnv env c gate bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59)
    { s with pc := "if.then96", pre := some "if.end93", mem := fusedStore c bs73 bs74 }

/-- **One page on the DFA arm's escape branch.** -/
theorem fused_dfa_escape_page (sel : Calls) (env : Env) (s : State) (c : FusedCarry)
    (gate : BitVec 1) (bs73 bs74 : List UInt8)
    (bs41 bs42 bs43 bs57 bs58 bs59 : List UInt8)
    (hinv : FusedInv env s c gate 0)
    (hshr57 : c.shr.toNat < 2 ^ 57)
    (hb3 : 3 ≤ c.b)
    (hgap : c.b + 64 * c.shr.toNat ≤ c.ent)
    (hread73 : readBytes c.mem (c.b + 64 * c.i.toNat) 32 = some bs73)
    (hread74 : readBytes c.mem (c.b + 64 * c.i.toNat + 32) 32 = some bs74)
    (hdec : fb54Select gate (fusedValues c bs73 bs74).v107 = 0)
    (h41 : readBytes c.mem (c.b + 64 * c.i.toNat - 1) 32 = some bs41)
    (h42 : readBytes c.mem (c.b + 64 * c.i.toNat - 2) 32 = some bs42)
    (h43 : readBytes c.mem (c.b + 64 * c.i.toNat - 3) 32 = some bs43)
    (h57 : readBytes c.mem (c.b + 64 * c.i.toNat + 31) 32 = some bs57)
    (h58 : readBytes c.mem (c.b + 64 * c.i.toNat + 30) 32 = some bs58)
    (h59 : readBytes c.mem (c.b + 64 * c.i.toNat + 29) 32 = some bs59)
    (r : CallOutcome)
    (hc : sel escapeListCallee
      [.int 64 (fusedValues c bs73 bs74).or14,
       .int 64 (ifThen96Mask (fusedValues c bs73 bs74).w73 (fusedValues c bs73 bs74).w74),
       .int 64 (fusedValues c bs73 bs74).xorI, .int 64 c.i, .ptr c.xp, .ptr c.nxp, .ptr c.xcarry]
      (fusedStore c bs73 bs74) s.next = some r) :
    step (s1BlocksCallsEsc sel) s1BlocksFunction (stateAt env s) =
      .jump (fusedDfaState env s c gate bs73 bs74) ∧
    step (s1BlocksCallsEsc sel) s1BlocksFunction (fusedDfaState env s c gate bs73 bs74) =
      .jump (fusedDfaMergeState env s c gate bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59) ∧
    step (s1BlocksCallsEsc sel) s1BlocksFunction (fusedDfaMergeState env s c gate bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59) =
      .jump (fusedDfaEscapeState env s c gate bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59) ∧
    step (s1BlocksCallsEsc sel) s1BlocksFunction (fusedDfaEscapeState env s c gate bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59) =
      .jump (fusedDfaEscapedLatchState env s c gate bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59 r) ∧
    FusedLatch (fusedDfaEscapedLatchEnv env c gate bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59)
      (fusedDfaEscapedLatchCore s c bs73 bs74 r) c.i
      (fusedNext c bs73 bs74 (fusedDfa90 c bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59).or281 r.mem)
      gate 0 := by
  have hi : c.i.toNat < c.shr.toNat := hinv.index_lt
  have hj57 : c.i.toNat < 2 ^ 57 := by omega
  have ha : (fusedValues c bs73 bs74).addPtr57 = c.b + 64 * c.i.toNat :=
    fusedValues_addPtr57 c bs73 bs74 hj57
  have h1 : 1 ≤ (fusedValues c bs73 bs74).addPtr57 := by rw [ha]; omega
  have h2 : 2 ≤ (fusedValues c bs73 bs74).addPtr57 := by rw [ha]; omega
  have h3 : 3 ≤ (fusedValues c bs73 bs74).addPtr57 := by rw [ha]; omega
  have hbit : lookupName (fusedE3 env c gate bs73 bs74) "%or.cond189"
      = some (.int 1 0) := by
    rw [show fusedE3 env c gate bs73 bs74
        = fb54Env9 env (fusedValues c bs73 bs74) gate from rfl, lookupName_fb54Env9_cond189]
    show some (Value.int 1 (fb54Select gate (fusedValues c bs73 bs74).v107)) = some (Value.int 1 0)
    rw [hdec]
  have hbody := fused_body_run env s c gate 0 bs73 bs74 hinv hshr57 hread73 hread74
  have h01 : step (s1BlocksCallsEsc sel) s1BlocksFunction (stateAt env s) =
      .jump (fusedDfaState env s c gate bs73 bs74) := by
    rw [step_esc_of_free sel s1BlocksFunction (stateAt env s) for_body54Block
      (by rw [show (stateAt env s).pc = s.pc from rfl, hinv.pc]
          exact findBlock_for_body54) (by decide)]
    rw [show fusedDfaState env s c gate bs73 bs74
        = stateAt (fb54Env9 env (fusedValues c bs73 bs74) gate)
            { s with
              pc := "if.then90",
              pre := some "for.body54",
              mem := writeBytes c.mem (fusedValues c bs73 bs74).arrayidx (natToBytes (fusedValues c bs73 bs74).or84.toNat 8) } from rfl,
      ← hinv.mem]
    exact for_body54_step_escape env s (fusedValues c bs73 bs74) gate hinv.pc hbit hbody
  have h41' : readBytes (fusedDfaState env s c gate bs73 bs74).mem ((fusedValues c bs73 bs74).addPtr57 - 1) 32 = some bs41 := by
    show readBytes (fusedStore c bs73 bs74) ((fusedValues c bs73 bs74).addPtr57 - 1) 32 = some bs41
    rw [fusedValues_addPtr57 c bs73 bs74 hj57]
    rw [fused_dfa_window_below c bs73 bs74 (a := c.b + 64 * c.i.toNat - 1)
      (n := 32) (by omega)]
    exact h41
  have h42' : readBytes (fusedDfaState env s c gate bs73 bs74).mem ((fusedValues c bs73 bs74).addPtr57 - 2) 32 = some bs42 := by
    show readBytes (fusedStore c bs73 bs74) ((fusedValues c bs73 bs74).addPtr57 - 2) 32 = some bs42
    rw [fusedValues_addPtr57 c bs73 bs74 hj57]
    rw [fused_dfa_window_below c bs73 bs74 (a := c.b + 64 * c.i.toNat - 2)
      (n := 32) (by omega)]
    exact h42
  have h43' : readBytes (fusedDfaState env s c gate bs73 bs74).mem ((fusedValues c bs73 bs74).addPtr57 - 3) 32 = some bs43 := by
    show readBytes (fusedStore c bs73 bs74) ((fusedValues c bs73 bs74).addPtr57 - 3) 32 = some bs43
    rw [fusedValues_addPtr57 c bs73 bs74 hj57]
    rw [fused_dfa_window_below c bs73 bs74 (a := c.b + 64 * c.i.toNat - 3)
      (n := 32) (by omega)]
    exact h43
  have h57' : readBytes (fusedDfaState env s c gate bs73 bs74).mem
      ((fusedValues c bs73 bs74).addPtr57 + ((0x000000000000001f#64).signExtend 64).toNat) 32 = some bs57 := by
    show readBytes (fusedStore c bs73 bs74)
      ((fusedValues c bs73 bs74).addPtr57 + ((0x000000000000001f#64).signExtend 64).toNat) 32 = some bs57
    rw [fusedValues_addPtr57 c bs73 bs74 hj57,
      show ((0x000000000000001f#64).signExtend 64).toNat = 31 from by decide]
    rw [fused_dfa_window_below c bs73 bs74 (a := c.b + 64 * c.i.toNat + 31)
      (n := 32) (by omega)]
    exact h57
  have h58' : readBytes (fusedDfaState env s c gate bs73 bs74).mem
      ((fusedValues c bs73 bs74).addPtr57 + ((0x000000000000001e#64).signExtend 64).toNat) 32 = some bs58 := by
    show readBytes (fusedStore c bs73 bs74)
      ((fusedValues c bs73 bs74).addPtr57 + ((0x000000000000001e#64).signExtend 64).toNat) 32 = some bs58
    rw [fusedValues_addPtr57 c bs73 bs74 hj57,
      show ((0x000000000000001e#64).signExtend 64).toNat = 30 from by decide]
    rw [fused_dfa_window_below c bs73 bs74 (a := c.b + 64 * c.i.toNat + 30)
      (n := 32) (by omega)]
    exact h58
  have h59' : readBytes (fusedDfaState env s c gate bs73 bs74).mem
      ((fusedValues c bs73 bs74).addPtr57 + ((0x000000000000001d#64).signExtend 64).toNat) 32 = some bs59 := by
    show readBytes (fusedStore c bs73 bs74)
      ((fusedValues c bs73 bs74).addPtr57 + ((0x000000000000001d#64).signExtend 64).toNat) 32 = some bs59
    rw [fusedValues_addPtr57 c bs73 bs74 hj57,
      show ((0x000000000000001d#64).signExtend 64).toNat = 29 from by decide]
    rw [fused_dfa_window_below c bs73 bs74 (a := c.b + 64 * c.i.toNat + 29)
      (n := 32) (by omega)]
    exact h59
  have h12 : step (s1BlocksCallsEsc sel) s1BlocksFunction (fusedDfaState env s c gate bs73 bs74) =
      .jump (fusedDfaMergeState env s c gate bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59) := by
    rw [step_esc_of_free sel s1BlocksFunction _ if_then90Block
      (by rw [show (fusedDfaState env s c gate bs73 bs74).pc = "if.then90" from rfl]
          exact findBlock_if_then90) (by decide)]
    exact if_then90_step (fusedE3 env c gate bs73 bs74) (fusedDfaState env s c gate bs73 bs74) (fusedDfa90 c bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59) rfl
      (if_then90_denote (fusedE3 env c gate bs73 bs74) (fusedDfaState env s c gate bs73 bs74) (fusedValues c bs73 bs74).addPtr57
        (fusedValues c bs73 bs74).low88 (fusedValues c bs73 bs74).low97 c.u8k bs41 bs42 bs43 bs57 bs58 bs59
        (lookupName_fb54Env9_addPtr57 env (fusedValues c bs73 bs74) gate) h1 h41' h2 h42' h3 h43'
        (lookupName_fb54Env9_p88 env (fusedValues c bs73 bs74) gate) (fusedValues_low88_length c bs73 bs74)
        (lookupName_fb54Env9_p97 env (fusedValues c bs73 bs74) gate) (fusedValues_low97_length c bs73 bs74)
        (lookupName_fb54Env9_u8k env (fusedValues c bs73 bs74) gate) hinv.u8k_len h57' h58' h59')
  have hesc : lookupName (fusedDfaEnv env c gate bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59) "%tobool95.not" = some (.int 1 0) :=
    lookupName_fusedDfaEnv_tobool95 env c gate bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59 hinv.escape
  have h23 : step (s1BlocksCallsEsc sel) s1BlocksFunction (fusedDfaMergeState env s c gate bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59) =
      .jump (fusedDfaEscapeState env s c gate bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59) := by
    rw [step_esc_of_free sel s1BlocksFunction _ if_end93Block
      (by rw [show (fusedDfaMergeState env s c gate bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59).pc = "if.end93" from rfl]
          exact findBlock_if_end93) (by decide)]
    exact if_end93_step_escape (fusedDfaEnv env c gate bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59) (fusedDfaMergeState env s c gate bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59) "if.then90"
      (.reg "%or.i281") (fusedDfa90 c bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59).or281 0 rfl rfl (by simp [phiIncoming])
      (BlockEval.evalOperand_reg_of _ _ _ _ (lookupName_fusedDfaEnv_or281 env c gate bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59))
      hesc rfl
  have h34 : step (s1BlocksCallsEsc sel) s1BlocksFunction (fusedDfaEscapeState env s c gate bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59) =
      .jump (fusedDfaEscapedLatchState env s c gate bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59 r) :=
    if_then96_step sel (fusedDfaLatchEnv env c gate bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59) (fusedDfaEscapeState env s c gate bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59)
      (fusedValues c bs73 bs74).w73 (fusedValues c bs73 bs74).w74 (fusedValues_w73_length c bs73 bs74)
      (fusedValues_w74_length c bs73 bs74)
      (fusedValues c bs73 bs74).or14 (fusedValues c bs73 bs74).xorI c.i c.xp c.nxp c.xcarry r rfl
      (lookupName_fusedDfaLatch_w73 env c gate bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59)
      (lookupName_fusedDfaLatch_w74 env c gate bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59)
      (lookupName_fusedDfaLatch_or14 env c gate bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59)
      (lookupName_fusedDfaLatch_xorI env c gate bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59)
      (lookupName_fusedDfaLatch_i env c gate bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59)
      (lookupName_fusedDfaLatch_xp env c gate bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59 hinv.stream)
      (lookupName_fusedDfaLatch_nxp env c gate bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59 hinv.count)
      (lookupName_fusedDfaLatch_xcarry env c gate bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59 hinv.carry)
      hc
  refine ⟨h01, h12, h23, h34, ?_⟩
  refine
    { pc := rfl
      mem := rfl
      index := lookupName_ifThen96Out_of (fusedDfaLatchEnv env c gate bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59) _ _ (by decide)
        (by decide) (by decide) (by decide) (lookupName_fusedDfaLatch_i env c gate bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59)
      prevS := lookupName_ifThen96Out_of (fusedDfaLatchEnv env c gate bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59) _ _ (by decide)
        (by decide) (by decide) (by decide) (lookupName_fusedDfaLatch_shr85 env c gate bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59)
      ascii := lookupName_ifThen96Out_of (fusedDfaLatchEnv env c gate bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59) _ _ (by decide)
        (by decide) (by decide) (by decide) (lookupName_fusedDfaLatch_or282 env c gate bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59)
      u8k := lookupName_ifThen96Out_of (fusedDfaLatchEnv env c gate bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59) _ _ (by decide)
        (by decide) (by decide) (by decide) (lookupName_fusedDfaLatch_u8k env c gate bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59)
      prevAscii := lookupName_ifThen96Out_of (fusedDfaLatchEnv env c gate bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59) _ _ (by decide)
        (by decide) (by decide) (by decide) (lookupName_fusedDfaLatch_p75 env c gate bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59)
      st0 := lookupName_ifThen96Out_of (fusedDfaLatchEnv env c gate bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59) _ _ (by decide)
        (by decide) (by decide) (by decide) (lookupName_fusedDfaLatch_shrII env c gate bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59)
      st9 := lookupName_ifThen96Out_of (fusedDfaLatchEnv env c gate bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59) _ _ (by decide)
        (by decide) (by decide) (by decide) (lookupName_fusedDfaLatch_conv13 env c gate bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59)
      st15 := lookupName_ifThen96Out_of (fusedDfaLatchEnv env c gate bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59) _ _ (by decide)
        (by decide) (by decide) (by decide) (lookupName_fusedDfaLatch_shrI env c gate bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59)
      base := lookupName_ifThen96Out_of (fusedDfaLatchEnv env c gate bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59) _ _ (by decide)
        (by decide) (by decide) (by decide) (lookupName_fusedDfaLatch_b env c gate bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59 hinv.base)
      emit := lookupName_ifThen96Out_of (fusedDfaLatchEnv env c gate bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59) _ _ (by decide)
        (by decide) (by decide) (by decide) (lookupName_fusedDfaLatch_ent env c gate bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59 hinv.emit)
      bound := lookupName_ifThen96Out_of (fusedDfaLatchEnv env c gate bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59) _ _ (by decide)
        (by decide) (by decide) (by decide) (lookupName_fusedDfaLatch_shr env c gate bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59 hinv.bound)
      stream := lookupName_ifThen96Out_of (fusedDfaLatchEnv env c gate bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59) _ _ (by decide)
        (by decide) (by decide) (by decide) (lookupName_fusedDfaLatch_xp env c gate bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59 hinv.stream)
      count := lookupName_ifThen96Out_of (fusedDfaLatchEnv env c gate bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59) _ _ (by decide)
        (by decide) (by decide) (by decide) (lookupName_fusedDfaLatch_nxp env c gate bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59 hinv.count)
      carry := lookupName_ifThen96Out_of (fusedDfaLatchEnv env c gate bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59) _ _ (by decide)
        (by decide) (by decide) (by decide) (lookupName_fusedDfaLatch_xcarry env c gate bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59 hinv.carry)
      gate := lookupName_ifThen96Out_of (fusedDfaLatchEnv env c gate bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59) _ _ (by decide)
        (by decide) (by decide) (by decide) (lookupName_fusedDfaLatch_tobool87 env c gate bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59 hinv.gate)
      escape := lookupName_ifThen96Out_of (fusedDfaLatchEnv env c gate bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59) _ _ (by decide)
        (by decide) (by decide) (by decide) (lookupName_fusedDfaLatch_tobool95 env c gate bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59 hinv.escape)
      succ := rfl
      index_lt := hinv.index_lt
      ascii_len := fusedNext_ascii_length c bs73 bs74 (fusedDfa90 c bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59).or281 r.mem hinv.ascii_len
      u8k_len := ifThen90Values_or281_length (fusedValues c bs73 bs74).addPtr57 (fusedValues c bs73 bs74).low88 (fusedValues c bs73 bs74).low97
        c.u8k bs41 bs42 bs43 bs57 bs58 bs59 hinv.u8k_len }

/-! ### The DFA arm's windows, from the document

`if.then90` reads three windows below its pointer and three above it.  Below, a
window is the previous block's tail and the row's head — or, at the document's
first row, the three zero bytes the caller stages before it.  Above, each is an
interior window of the row.  The document's blocks give all six. -/

/-- The six windows the DFA arm loads at one row. -/
structure FusedWindows (mem : Mem) (b shr : Nat) (i : BitVec 64)
    (doc : Nat → List UInt8) where
  /-- The window one byte below the row. -/
  bs41 : List UInt8
  /-- The window two bytes below the row. -/
  bs42 : List UInt8
  /-- The window three bytes below the row. -/
  bs43 : List UInt8
  /-- The interior window thirty-one bytes into the row. -/
  bs57 : List UInt8
  /-- The interior window thirty bytes into the row. -/
  bs58 : List UInt8
  /-- The interior window twenty-nine bytes into the row. -/
  bs59 : List UInt8
  w41 : readBytes mem (b + 64 * i.toNat - 1) 32 = some bs41
  w42 : readBytes mem (b + 64 * i.toNat - 2) 32 = some bs42
  w43 : readBytes mem (b + 64 * i.toNat - 3) 32 = some bs43
  w57 : readBytes mem (b + 64 * i.toNat + 31) 32 = some bs57
  w58 : readBytes mem (b + 64 * i.toNat + 30) 32 = some bs58
  w59 : readBytes mem (b + 64 * i.toNat + 29) 32 = some bs59

/-- **The DFA arm's six windows at one row.**  At a row past the first, each
below-window is the previous block's tail joined with the row's head; at the
first row it is the staged zeroes joined with the row's head.  The three above
are interior windows of the row. -/
def fused_windows (mem : Mem) (b shr : Nat) (i : BitVec 64)
    (doc : Nat → List UInt8) (h3b : 3 ≤ b) (hi : i.toNat < shr)
    (hzero : readBytes mem (b - 3) 3 = some [0, 0, 0])
    (hdoc : ∀ j, j < shr → readBytes mem (b + 64 * j) 64 = some (doc j)) :
    FusedWindows mem b shr i doc := by
  by_cases hi0 : i.toNat = 0
  · have hshr0 : 0 < shr := by omega
    have hblk : readBytes mem b 64 = some (doc 0) := by
      have h := hdoc 0 hshr0
      simpa using h
    have h1 : readBytes mem (b - 1) 1 = some [0] := by
      have h := (readBytes_split mem (b - 3) 2 1 (by
        rw [show 2 + 1 = 3 from by omega]; exact hzero)).2
      rw [show b - 3 + 2 = b - 1 from by omega] at h
      simpa using h
    have h2 : readBytes mem (b - 2) 2 = some [0, 0] := by
      have h := (readBytes_split mem (b - 3) 1 2 (by
        rw [show 1 + 2 = 3 from by omega]; exact hzero)).2
      rw [show b - 3 + 1 = b - 2 from by omega] at h
      simpa using h
    have hb1 : readBytes mem b 31 = some ((doc 0).take 31) := by
      have h := readBytes_docBlock_inside (addr := b) hblk (k := 0) (n := 31) (by omega)
      simpa using h
    have hb2 : readBytes mem b 30 = some ((doc 0).take 30) := by
      have h := readBytes_docBlock_inside (addr := b) hblk (k := 0) (n := 30) (by omega)
      simpa using h
    have hb3 : readBytes mem b 29 = some ((doc 0).take 29) := by
      have h := readBytes_docBlock_inside (addr := b) hblk (k := 0) (n := 29) (by omega)
      simpa using h
    refine
      { bs41 := [0] ++ (doc 0).take 31
        bs42 := [0, 0] ++ (doc 0).take 30
        bs43 := [0, 0, 0] ++ (doc 0).take 29
        bs57 := ((doc 0).drop 31).take 32
        bs58 := ((doc 0).drop 30).take 32
        bs59 := ((doc 0).drop 29).take 32
        w41 := ?_
        w42 := ?_
        w43 := ?_
        w57 := ?_
        w58 := ?_
        w59 := ?_ }
    · rw [hi0]; simp only [Nat.mul_zero, Nat.add_zero]
      have hb1' : readBytes mem ((b - 1) + 1) 31 = some ((doc 0).take 31) := by
        rw [show b - 1 + 1 = b from by omega]; exact hb1
      exact LeanLLVM.Refinement.JsonEntrySteps.readBytes_append mem 1 (b - 1) [0] 31
        ((doc 0).take 31) h1 hb1'
    · rw [hi0]; simp only [Nat.mul_zero, Nat.add_zero]
      have hb2' : readBytes mem ((b - 2) + 2) 30 = some ((doc 0).take 30) := by
        rw [show b - 2 + 2 = b from by omega]; exact hb2
      exact LeanLLVM.Refinement.JsonEntrySteps.readBytes_append mem 2 (b - 2) [0, 0] 30
        ((doc 0).take 30) h2 hb2'
    · rw [hi0]; simp only [Nat.mul_zero, Nat.add_zero]
      have hb3' : readBytes mem ((b - 3) + 3) 29 = some ((doc 0).take 29) := by
        rw [show b - 3 + 3 = b from by omega]; exact hb3
      exact LeanLLVM.Refinement.JsonEntrySteps.readBytes_append mem 3 (b - 3) [0, 0, 0] 29
        ((doc 0).take 29) hzero hb3'
    · rw [hi0]; simp only [Nat.mul_zero, Nat.add_zero]
      have h := readBytes_docBlock_inside (addr := b) hblk (k := 31) (n := 32) (by omega)
      simpa using h
    · rw [hi0]; simp only [Nat.mul_zero, Nat.add_zero]
      have h := readBytes_docBlock_inside (addr := b) hblk (k := 30) (n := 32) (by omega)
      simpa using h
    · rw [hi0]; simp only [Nat.mul_zero, Nat.add_zero]
      have h := readBytes_docBlock_inside (addr := b) hblk (k := 29) (n := 32) (by omega)
      simpa using h
  · have hi1 : 1 ≤ i.toNat := by omega
    have haddr : 64 ≤ b + 64 * i.toNat := by omega
    have hblk : readBytes mem (b + 64 * i.toNat) 64 = some (doc i.toNat) :=
      hdoc i.toNat hi
    have hprev : readBytes mem (b + 64 * (i.toNat - 1)) 64 = some (doc (i.toNat - 1)) :=
      hdoc _ (by omega)
    have hprevAddr : (b + 64 * i.toNat) - 64 = b + 64 * (i.toNat - 1) := by omega
    refine
      { bs41 := (doc (i.toNat - 1)).drop 63 ++ (doc i.toNat).take 31
        bs42 := (doc (i.toNat - 1)).drop 62 ++ (doc i.toNat).take 30
        bs43 := (doc (i.toNat - 1)).drop 61 ++ (doc i.toNat).take 29
        bs57 := ((doc i.toNat).drop 31).take 32
        bs58 := ((doc i.toNat).drop 30).take 32
        bs59 := ((doc i.toNat).drop 29).take 32
        w41 := ?_
        w42 := ?_
        w43 := ?_
        w57 := ?_
        w58 := ?_
        w59 := ?_ }
    · exact readBytes_docBlock_carry (m := mem) (addr := b + 64 * i.toNat)
        (prev := doc (i.toNat - 1)) (blk := doc i.toNat) (d := 1)
        (by omega) (by rw [hprevAddr]; exact hprev) hblk (by omega) (by omega)
    · exact readBytes_docBlock_carry (m := mem) (addr := b + 64 * i.toNat)
        (prev := doc (i.toNat - 1)) (blk := doc i.toNat) (d := 2)
        (by omega) (by rw [hprevAddr]; exact hprev) hblk (by omega) (by omega)
    · exact readBytes_docBlock_carry (m := mem) (addr := b + 64 * i.toNat)
        (prev := doc (i.toNat - 1)) (blk := doc i.toNat) (d := 3)
        (by omega) (by rw [hprevAddr]; exact hprev) hblk (by omega) (by omega)
    · exact readBytes_docBlock_inside hblk (k := 31) (n := 32) (by omega)
    · exact readBytes_docBlock_inside hblk (k := 30) (n := 32) (by omega)
    · exact readBytes_docBlock_inside hblk (k := 29) (n := 32) (by omega)

/-- Four admitted jumps are a `runFuel` prefix of four control steps. -/
theorem runFuel_jump4 {calls : Calls} {f : Function} {s0 s1 s2 s3 s4 : State}
    (h01 : step calls f s0 = .jump s1) (h12 : step calls f s1 = .jump s2)
    (h23 : step calls f s2 = .jump s3) (h34 : step calls f s3 = .jump s4) (k : Nat) :
    runFuel calls (4 + k) f s0 = runFuel calls k f s4 := by
  rw [show 4 + k = 1 + (1 + (1 + (1 + k))) from by omega,
    runFuel_jump_prefix h01 (1 + (1 + (1 + k))),
    runFuel_jump_prefix h12 (1 + (1 + k)),
    runFuel_jump_prefix h23 (1 + k),
    runFuel_jump_prefix h34 k]

/-- Five admitted jumps are a `runFuel` prefix of five control steps. -/
theorem runFuel_jump5 {calls : Calls} {f : Function} {s0 s1 s2 s3 s4 s5 : State}
    (h01 : step calls f s0 = .jump s1) (h12 : step calls f s1 = .jump s2)
    (h23 : step calls f s2 = .jump s3) (h34 : step calls f s3 = .jump s4)
    (h45 : step calls f s4 = .jump s5) (k : Nat) :
    runFuel calls (5 + k) f s0 = runFuel calls k f s5 := by
  rw [show 5 + k = 1 + (1 + (1 + (1 + (1 + k)))) from by omega,
    runFuel_jump_prefix h01 (1 + (1 + (1 + (1 + k)))),
    runFuel_jump_prefix h12 (1 + (1 + (1 + k))),
    runFuel_jump_prefix h23 (1 + (1 + k)),
    runFuel_jump_prefix h34 (1 + k),
    runFuel_jump_prefix h45 k]

/-! ### The latch's two arms

The latch increments the index and tests it against the bound.  At the bound it
leaves `for.end101` with the seven carried words readable at its own
environment; inside it, the back edge re-enters `for.body54` at the successor's
carry. -/

/-- **The latch's exit.**  The bound's test taken true leaves `for.end101`, and
the exit's seven words are the successor's, readable at the latch's own
environment with the latch's increment on top. -/
theorem fused_latch_exit (sel : Calls) (env : Env) (s : State) (i : BitVec 64)
    (c : FusedCarry) (gate escBit : BitVec 1)
    (hl : FusedLatch env s i c gate escBit)
    (hbit : evalICmp .eq (i + 1) c.shr = 1) :
    step (s1BlocksCallsEsc sel) s1BlocksFunction (stateAt env s) =
      .jump (stateAt (ifEnd98Env env i c.shr)
        { s with pc := "for.end101", pre := some "if.end98" }) ∧
    FusedExit (ifEnd98Env env i c.shr)
      (stateAt (ifEnd98Env env i c.shr)
        { s with pc := "for.end101", pre := some "if.end98" }) c := by
  have hstep : step s1BlocksCalls s1BlocksFunction (stateAt env s) =
      .jump (stateAt (ifEnd98Env env i c.shr)
        { s with pc := "for.end101", pre := some "if.end98" }) :=
    if_end98_step_exit env s i c.shr hl.pc hl.index hl.bound hbit
  refine ⟨?_, ?_⟩
  · rw [step_esc_of_free sel s1BlocksFunction (stateAt env s) if_end98Block
      (by rw [show (stateAt env s).pc = s.pc from rfl, hl.pc]
          exact findBlock_if_end98) (by decide)]
    exact hstep
  · refine
      { pc := rfl
        pre := rfl
        mem := hl.mem
        bound_reached := hl.succ.trans ((for_inc_exitcond_iff i c.shr).1.mp hbit)
        prevS := lookupName_ifEnd98Env_of env i c.shr (by decide) (by decide) hl.prevS
        ascii := lookupName_ifEnd98Env_of env i c.shr (by decide) (by decide) hl.ascii
        u8k := lookupName_ifEnd98Env_of env i c.shr (by decide) (by decide) hl.u8k
        prevAscii := lookupName_ifEnd98Env_of env i c.shr (by decide) (by decide)
          hl.prevAscii
        st0 := lookupName_ifEnd98Env_of env i c.shr (by decide) (by decide) hl.st0
        st9 := lookupName_ifEnd98Env_of env i c.shr (by decide) (by decide) hl.st9
        st15 := lookupName_ifEnd98Env_of env i c.shr (by decide) (by decide) hl.st15
        base := lookupName_ifEnd98Env_of env i c.shr (by decide) (by decide) hl.base
        emit := lookupName_ifEnd98Env_of env i c.shr (by decide) (by decide) hl.emit
        bound := lookupName_ifEnd98Env_of env i c.shr (by decide) (by decide) hl.bound }

/-- **The latch's back edge.**  The bound's test taken false leaves
`for.body54` at the successor's carry, with the index advanced inside the
bound. -/
theorem fused_latch_loop (sel : Calls) (env : Env) (s : State) (i : BitVec 64)
    (c : FusedCarry) (gate escBit : BitVec 1)
    (hl : FusedLatch env s i c gate escBit)
    (hbit : evalICmp .eq (i + 1) c.shr = 0)
    (hshr57 : c.shr.toNat < 2 ^ 57) :
    step (s1BlocksCallsEsc sel) s1BlocksFunction (stateAt env s) =
      .jump (stateAt (ifEnd98Env env i c.shr)
        { s with pc := "for.body54", pre := some "if.end98" }) ∧
    FusedInv (ifEnd98Env env i c.shr)
      (stateAt (ifEnd98Env env i c.shr)
        { s with pc := "for.body54", pre := some "if.end98" }) c gate escBit := by
  have hsucc : (i + 1).toNat = i.toNat + 1 := by
    rw [BitVec.toNat_add, show (1 : BitVec 64).toNat = 1 from by decide]
    have := hl.index_lt; omega
  have hstep : step s1BlocksCalls s1BlocksFunction (stateAt env s) =
      .jump (stateAt (ifEnd98Env env i c.shr)
        { s with pc := "for.body54", pre := some "if.end98" }) :=
    if_end98_step_loop env s i c.shr hl.pc hl.index hl.bound hbit
  refine ⟨?_, ?_⟩
  · rw [step_esc_of_free sel s1BlocksFunction (stateAt env s) if_end98Block
      (by rw [show (stateAt env s).pc = s.pc from rfl, hl.pc]
          exact findBlock_if_end98) (by decide)]
    exact hstep
  · have hlt : i.toNat < c.shr.toNat := hl.index_lt
    have hne : i + 1 ≠ c.shr := (for_inc_exitcond_iff i c.shr).2.mp hbit
    have hneNat : i.toNat + 1 ≠ c.shr.toNat := fun h =>
      hne (BitVec.eq_of_toNat_eq (by rw [hsucc]; exact h))
    refine
      { pc := rfl
        pre := rfl
        mem := hl.mem
        index := by rw [hl.succ]; exact lookupName_ifEnd98Env_inc100 env i c.shr
        prevS := lookupName_ifEnd98Env_of env i c.shr (by decide) (by decide) hl.prevS
        ascii := lookupName_ifEnd98Env_of env i c.shr (by decide) (by decide) hl.ascii
        u8k := lookupName_ifEnd98Env_of env i c.shr (by decide) (by decide) hl.u8k
        prevAscii := lookupName_ifEnd98Env_of env i c.shr (by decide) (by decide)
          hl.prevAscii
        st0 := lookupName_ifEnd98Env_of env i c.shr (by decide) (by decide) hl.st0
        st9 := lookupName_ifEnd98Env_of env i c.shr (by decide) (by decide) hl.st9
        st15 := lookupName_ifEnd98Env_of env i c.shr (by decide) (by decide) hl.st15
        base := lookupName_ifEnd98Env_of env i c.shr (by decide) (by decide) hl.base
        emit := lookupName_ifEnd98Env_of env i c.shr (by decide) (by decide) hl.emit
        bound := lookupName_ifEnd98Env_of env i c.shr (by decide) (by decide) hl.bound
        stream := lookupName_ifEnd98Env_of env i c.shr (by decide) (by decide) hl.stream
        count := lookupName_ifEnd98Env_of env i c.shr (by decide) (by decide) hl.count
        carry := lookupName_ifEnd98Env_of env i c.shr (by decide) (by decide) hl.carry
        gate := lookupName_ifEnd98Env_of env i c.shr (by decide) (by decide) hl.gate
        escape := lookupName_ifEnd98Env_of env i c.shr (by decide) (by decide) hl.escape
        index_lt := by
          rw [hl.succ, hsucc]
          omega
        ascii_len := hl.ascii_len
        u8k_len := hl.u8k_len }

/-! ### The page, uniformly

One page reaches the latch with the successor's carry and the page's memory, in
at most four control steps: the body, the DFA arm when the decision is clear, the
merge, and the escape record when its bit is clear.  The latch's own step is the
next block, `fused_latch_exit` or `fused_latch_loop`, which is why the page's
charge is four and an iteration's is five. -/

/-- Two admitted jumps are a `runFuel` prefix of two control steps. -/
theorem runFuel_jump2 {calls : Calls} {f : Function} {s0 s1 s2 : State}
    (h01 : step calls f s0 = .jump s1) (h12 : step calls f s1 = .jump s2) (k : Nat) :
    runFuel calls (2 + k) f s0 = runFuel calls k f s2 := by
  rw [show 2 + k = 1 + (1 + k) from by omega,
    runFuel_jump_prefix h01 (1 + k), runFuel_jump_prefix h12 k]

/-- The document survives the page's store: the store is at or above `%ent`,
above every block the loop reads. -/
theorem readBytes_fusedStore_doc (c : FusedCarry) (bs73 bs74 : List UInt8)
    (doc : Nat → List UInt8) (hgap : c.b + 64 * c.shr.toNat ≤ c.ent)
    (hdoc : ∀ j, j < c.shr.toNat → readBytes c.mem (c.b + 64 * j) 64 = some (doc j)) :
    ∀ j, j < c.shr.toNat →
      readBytes (fusedStore c bs73 bs74) (c.b + 64 * j) 64 = some (doc j) := by
  intro j hj
  show readBytes (writeBytes c.mem (fusedValues c bs73 bs74).arrayidx
    (natToBytes (fusedValues c bs73 bs74).or84.toNat 8)) (c.b + 64 * j) 64 = some (doc j)
  rw [fusedValues_arrayidx]
  exact readBytes_writeBytes_doc c.mem _ (c.ent + 8 * c.i.toNat) c.b c.shr.toNat doc
    hdoc (by omega) j hj

/-- The three staged zeroes survive the page's store. -/
theorem readBytes_fusedStore_zero (c : FusedCarry) (bs73 bs74 : List UInt8)
    (hb3 : 3 ≤ c.b) (hgap : c.b + 64 * c.shr.toNat ≤ c.ent) :
    readBytes (fusedStore c bs73 bs74) (c.b - 3) 3 = readBytes c.mem (c.b - 3) 3 := by
  show readBytes (writeBytes c.mem (fusedValues c bs73 bs74).arrayidx
    (natToBytes (fusedValues c bs73 bs74).or84.toNat 8)) (c.b - 3) 3
    = readBytes c.mem (c.b - 3) 3
  rw [fusedValues_arrayidx]
  exact readBytes_writeBytes_below c.mem _ 3 (c.b - 3) (c.ent + 8 * c.i.toNat)
    (by omega)

/-- **One page, uniformly.**  From the invariant at the loop head, one page
reaches the latch's invariant in at most four control steps: the body, the DFA
arm or the merge, the escape record or its skip.  The successor's carry and the
page's memory are returned together with the document's survival, so the next
page (or `for.end101`'s phis) reads what this one read. -/
theorem fusedInv_page (sel : Calls) (env : Env) (s : State) (c : FusedCarry)
    (gate escBit : BitVec 1) (bs73 bs74 : List UInt8) (doc : Nat → List UInt8)
    (hinv : FusedInv env s c gate escBit)
    (hshr57 : c.shr.toNat < 2 ^ 57)
    (hb3 : 3 ≤ c.b)
    (hgap : c.b + 64 * c.shr.toNat ≤ c.ent)
    (hdoc : ∀ j, j < c.shr.toNat → readBytes c.mem (c.b + 64 * j) 64 = some (doc j))
    (hzero : readBytes c.mem (c.b - 3) 3 = some [0, 0, 0])
    (hread73 : readBytes c.mem (c.b + 64 * c.i.toNat) 32 = some bs73)
    (hread74 : readBytes c.mem (c.b + 64 * c.i.toNat + 32) 32 = some bs74)
    (r : CallOutcome)
    (hc : sel escapeListCallee
      [.int 64 (fusedValues c bs73 bs74).or14,
       .int 64 (ifThen96Mask (fusedValues c bs73 bs74).w73
         (fusedValues c bs73 bs74).w74),
       .int 64 (fusedValues c bs73 bs74).xorI, .int 64 c.i,
       .ptr c.xp, .ptr c.nxp, .ptr c.xcarry]
      (fusedStore c bs73 bs74) s.next = some r)
    (hkeepDoc : ∀ j, j < c.shr.toNat → readBytes r.mem (c.b + 64 * j) 64 = some (doc j))
    (hkeepZero : readBytes r.mem (c.b - 3) 3 = some [0, 0, 0]) :
    ∃ (env' : Env) (core : State) (c' : FusedCarry) (k : Nat),
      k ≤ 4 ∧
      (∀ j, runFuel (s1BlocksCallsEsc sel) (k + j) s1BlocksFunction (stateAt env s)
        = runFuel (s1BlocksCallsEsc sel) j s1BlocksFunction (stateAt env' core)) ∧
      FusedLatch env' core c.i c' gate escBit ∧
      c'.b = c.b ∧ c'.ent = c.ent ∧ c'.xp = c.xp ∧ c'.nxp = c.nxp ∧
      c'.xcarry = c.xcarry ∧ c'.shr = c.shr ∧
      (∀ j, j < c.shr.toNat → readBytes c'.mem (c.b + 64 * j) 64 = some (doc j)) ∧
      readBytes c'.mem (c.b - 3) 3 = some [0, 0, 0] := by
  have hi : c.i.toNat < c.shr.toNat := hinv.index_lt
  have hwin : FusedWindows c.mem c.b c.shr.toNat c.i doc :=
    fused_windows c.mem c.b c.shr.toNat c.i doc hb3 hi hzero hdoc
  rcases BlockEval.bitVec1_eq_zero_or_one (fb54Select gate (fusedValues c bs73 bs74).v107)
    with hdec | hdec
  · -- the DFA arm
    rcases BlockEval.bitVec1_eq_zero_or_one escBit with he | he
    · subst he
      obtain ⟨h01, h12, h23, h34, hl⟩ := fused_dfa_escape_page sel env s c gate bs73 bs74
        hwin.bs41 hwin.bs42 hwin.bs43 hwin.bs57 hwin.bs58 hwin.bs59
        hinv hshr57 hb3 hgap hread73 hread74 hdec
        hwin.w41 hwin.w42 hwin.w43 hwin.w57 hwin.w58 hwin.w59 r hc
      exact ⟨_, _, _, 4, by omega, fun j => runFuel_jump4 h01 h12 h23 h34 j, hl,
        rfl, rfl, rfl, rfl, rfl, rfl, hkeepDoc, hkeepZero⟩
    · subst he
      obtain ⟨h01, h12, h23, hl⟩ := fused_dfa_skip_page sel env s c gate bs73 bs74
        hwin.bs41 hwin.bs42 hwin.bs43 hwin.bs57 hwin.bs58 hwin.bs59
        hinv hshr57 hb3 hgap hread73 hread74 hdec
        hwin.w41 hwin.w42 hwin.w43 hwin.w57 hwin.w58 hwin.w59
      have hdoc' := readBytes_fusedStore_doc c bs73 bs74 doc hgap hdoc
      have hzero' : readBytes (fusedStore c bs73 bs74) (c.b - 3) 3 = some [0, 0, 0] := by
        rw [readBytes_fusedStore_zero c bs73 bs74 hb3 hgap]
        exact hzero
      exact ⟨_, _, _, 3, by omega, fun j => runFuel_jump3 h01 h12 h23 j, hl,
        rfl, rfl, rfl, rfl, rfl, rfl, hdoc', hzero'⟩
  · -- the merge
    rcases BlockEval.bitVec1_eq_zero_or_one escBit with he | he
    · subst he
      obtain ⟨h01, h12, h23, hl⟩ := fused_merge_escape_page sel env s c gate bs73 bs74
        hinv hshr57 hread73 hread74 hdec r hc
      exact ⟨_, _, _, 3, by omega, fun j => runFuel_jump3 h01 h12 h23 j, hl,
        rfl, rfl, rfl, rfl, rfl, rfl, hkeepDoc, hkeepZero⟩
    · subst he
      obtain ⟨h01, h12, hl⟩ := fused_merge_skip_page sel env s c gate bs73 bs74
        hinv hshr57 hread73 hread74 hdec
      have hdoc' := readBytes_fusedStore_doc c bs73 bs74 doc hgap hdoc
      have hzero' : readBytes (fusedStore c bs73 bs74) (c.b - 3) 3 = some [0, 0, 0] := by
        rw [readBytes_fusedStore_zero c bs73 bs74 hb3 hgap]
        exact hzero
      exact ⟨_, _, _, 2, by omega, fun j => runFuel_jump2 h01 h12 j, hl,
        rfl, rfl, rfl, rfl, rfl, rfl, hdoc', hzero'⟩

/-! ### The loop's terminals and one iteration

`FusedTerm` is the loop's end: the bound's exit at `for.end101` with the seven
carried words readable at the block's own environment.  `FusedEnd` adds the other
terminal one iteration has — the back edge at the successor's carry — which is
what `fusedInv_step` states. -/

/-- The loop's end: the bound's exit at `for.end101`. -/
inductive FusedTerm : State → Prop where
  | exit (env : Env) (s : State) (c : FusedCarry) :
      FusedExit env s c → FusedTerm (stateAt env s)

/-- One iteration's two terminals. -/
inductive FusedEnd : State → Prop where
  | exit (env : Env) (s : State) (c : FusedCarry) :
      FusedExit env s c → FusedEnd (stateAt env s)
  | loop (env : Env) (s : State) (c : FusedCarry) (gate esc : BitVec 1) :
      FusedInv env s c gate esc → FusedEnd (stateAt env s)

/-- **One iteration.**  From the invariant, one page and the latch reach either
`for.end101` with the exit's seven words, or the back edge at the successor's
carry — in at most five control steps: the page's four and the latch's one.  The
escape call is the caller's selection; `hcall` says it answers the loop's call and
`hkeep` that the answer keeps the document. -/
theorem fusedInv_step (sel : Calls) (env : Env) (s : State) (c : FusedCarry)
    (gate escBit : BitVec 1) (bs73 bs74 : List UInt8) (doc : Nat → List UInt8)
    (hinv : FusedInv env s c gate escBit)
    (hshr57 : c.shr.toNat < 2 ^ 57)
    (hb3 : 3 ≤ c.b)
    (hgap : c.b + 64 * c.shr.toNat ≤ c.ent)
    (hdoc : ∀ j, j < c.shr.toNat → readBytes c.mem (c.b + 64 * j) 64 = some (doc j))
    (hzero : readBytes c.mem (c.b - 3) 3 = some [0, 0, 0])
    (hread73 : readBytes c.mem (c.b + 64 * c.i.toNat) 32 = some bs73)
    (hread74 : readBytes c.mem (c.b + 64 * c.i.toNat + 32) 32 = some bs74)
    (hcall : ∀ (args : List Value) (mem : Mem) (next : Nat),
      ∃ r : CallOutcome, sel escapeListCallee args mem next = some r)
    (hkeep : ∀ (or14 mask xs i : BitVec 64) (mem : Mem) (next : Nat) (r : CallOutcome),
      sel escapeListCallee
        [.int 64 or14, .int 64 mask, .int 64 xs, .int 64 i,
         .ptr c.xp, .ptr c.nxp, .ptr c.xcarry] mem next = some r →
      (∀ j, j < c.shr.toNat → readBytes r.mem (c.b + 64 * j) 64 = some (doc j)) ∧
      readBytes r.mem (c.b - 3) 3 = some [0, 0, 0]) :
    ∃ (e : State) (k : Nat), k ≤ 5 ∧ FusedEnd e ∧
      ∀ j, runFuel (s1BlocksCallsEsc sel) (k + j) s1BlocksFunction (stateAt env s)
        = runFuel (s1BlocksCallsEsc sel) j s1BlocksFunction e := by
  obtain ⟨r, hc⟩ := hcall
    [.int 64 (fusedValues c bs73 bs74).or14,
     .int 64 (ifThen96Mask (fusedValues c bs73 bs74).w73
       (fusedValues c bs73 bs74).w74),
     .int 64 (fusedValues c bs73 bs74).xorI, .int 64 c.i,
     .ptr c.xp, .ptr c.nxp, .ptr c.xcarry]
    (fusedStore c bs73 bs74) s.next
  obtain ⟨hkeepDoc, hkeepZero⟩ := hkeep _ _ _ _ _ _ r hc
  obtain ⟨env', core, c', k, hk, hrun, hl, -, -, -, -, -, hshr', -, -⟩ :=
    fusedInv_page sel env s c gate escBit bs73 bs74 doc hinv hshr57 hb3 hgap hdoc
      hzero hread73 hread74 r hc hkeepDoc hkeepZero
  rcases BlockEval.bitVec1_eq_zero_or_one (evalICmp .eq (c.i + 1) c'.shr) with hbit | hbit
  · -- the back edge
    obtain ⟨hstep, hinv'⟩ :=
      fused_latch_loop sel env' core c.i c' gate escBit hl hbit
        (by rw [hshr']; exact hshr57)
    refine ⟨stateAt (ifEnd98Env env' c.i c'.shr)
        { core with pc := "for.body54", pre := some "if.end98" }, k + 1, by omega,
      FusedEnd.loop (ifEnd98Env env' c.i c'.shr)
        (stateAt (ifEnd98Env env' c.i c'.shr)
          { core with pc := "for.body54", pre := some "if.end98" }) c' gate escBit hinv',
      fun j => ?_⟩
    rw [show k + 1 + j = k + (1 + j) from by omega, hrun (1 + j),
      runFuel_jump_prefix hstep j]
  · -- the bound's exit
    obtain ⟨hstep, hexit⟩ :=
      fused_latch_exit sel env' core c.i c' gate escBit hl hbit
    refine ⟨stateAt (ifEnd98Env env' c.i c'.shr)
        { core with pc := "for.end101", pre := some "if.end98" }, k + 1, by omega,
      FusedEnd.exit (ifEnd98Env env' c.i c'.shr)
        (stateAt (ifEnd98Env env' c.i c'.shr)
          { core with pc := "for.end101", pre := some "if.end98" }) c' hexit,
      fun j => ?_⟩
    rw [show k + 1 + j = k + (1 + j) from by omega, hrun (1 + j),
      runFuel_jump_prefix hstep j]

/-! ### The induction

The measure is the distance to the bound, `%shr - (i + 1)`, one page per step.
At zero the latch's test is true and the run exits at `for.end101`; above zero it
is false, the back edge re-enters the head at the successor's carry, and the
document the next page reads is the page's own.  A page that takes the escape
record hands on the call's memory, so the escape unit enters the induction
through two caller facts: it answers the loop's call (`hcall`), and its answer
keeps the document and the staged zeroes (`hkeep`).  Both are the record's, from
the staging's separations. -/

/-- **The loop's run.**  From the invariant at the head of a row inside the bound
— with the document's blocks and the three staged zeroes readable, the emit area
above them, and the bound below `2 ^ 57` — the run reaches the bound's exit at
`for.end101` in at most five control steps per remaining row plus five: each page
is four and the latch one.  The terminal carries the exit's seven words and the
last page's memory, so `for.end101`'s phis read what that page left. -/
theorem fusedInv_runFuel_aux (sel : Calls) :
    ∀ (r : Nat) (env : Env) (s : State) (c : FusedCarry) (gate escBit : BitVec 1)
      (doc : Nat → List UInt8),
      c.shr.toNat - (c.i.toNat + 1) = r →
      c.shr.toNat < 2 ^ 57 →
      FusedInv env s c gate escBit →
      3 ≤ c.b →
      c.b + 64 * c.shr.toNat ≤ c.ent →
      (∀ j, j < c.shr.toNat → readBytes c.mem (c.b + 64 * j) 64 = some (doc j)) →
      readBytes c.mem (c.b - 3) 3 = some [0, 0, 0] →
      (∀ (args : List Value) (mem : Mem) (next : Nat),
        ∃ r : CallOutcome, sel escapeListCallee args mem next = some r) →
      (∀ (or14 mask xs i : BitVec 64) (mem : Mem) (next : Nat) (r : CallOutcome),
        sel escapeListCallee
          [.int 64 or14, .int 64 mask, .int 64 xs, .int 64 i,
           .ptr c.xp, .ptr c.nxp, .ptr c.xcarry] mem next = some r →
        (∀ j, j < c.shr.toNat → readBytes r.mem (c.b + 64 * j) 64 = some (doc j)) ∧
        readBytes r.mem (c.b - 3) 3 = some [0, 0, 0]) →
      ∃ (e : State) (j : Nat), j ≤ 5 * r + 5 ∧ FusedTerm e ∧
        ∀ k, runFuel (s1BlocksCallsEsc sel) (j + k) s1BlocksFunction (stateAt env s)
          = runFuel (s1BlocksCallsEsc sel) k s1BlocksFunction e
  | 0, env, s, c, gate, escBit, doc, hmeasure, hshr57, hinv, hb3, hgap, hdoc, hzero,
    hcall, hkeep => by
      have hi : c.i.toNat < c.shr.toNat := hinv.index_lt
      have hsucc : (c.i + 1).toNat = c.i.toNat + 1 := by
        rw [BitVec.toNat_add, show (1 : BitVec 64).toNat = 1 from by decide]
        omega
      have hbound : c.i + 1 = c.shr := by
        apply BitVec.eq_of_toNat_eq
        rw [hsucc]
        omega
      have hblk : readBytes c.mem (c.b + 64 * c.i.toNat) 64 = some (doc c.i.toNat) :=
        hdoc c.i.toNat hi
      obtain ⟨hread73, hread74⟩ := readBytes_split c.mem (c.b + 64 * c.i.toNat) 32 32 (by
        rw [show 32 + 32 = 64 from rfl]; exact hblk)
      obtain ⟨rc, hc⟩ := hcall _ _ _
      obtain ⟨hkeepDoc, hkeepZero⟩ := hkeep _ _ _ _ _ _ rc hc
      obtain ⟨env', core, c', k, hk, hrun, hl, -, -, -, -, -, hshr', hdoc', hzero'⟩ :=
        fusedInv_page sel env s c gate escBit ((doc c.i.toNat).take 32)
          ((doc c.i.toNat).drop 32) doc hinv hshr57 hb3 hgap hdoc hzero
          hread73 hread74 rc hc hkeepDoc hkeepZero
      have hbit : evalICmp .eq (c.i + 1) c'.shr = 1 := by
        rw [hshr']
        exact (for_inc_exitcond_iff c.i c.shr).1.mpr hbound
      obtain ⟨hstep, hexit⟩ := fused_latch_exit sel env' core c.i c' gate escBit hl hbit
      refine ⟨stateAt (ifEnd98Env env' c.i c'.shr)
          { core with pc := "for.end101", pre := some "if.end98" }, k + 1, by omega,
        FusedTerm.exit (ifEnd98Env env' c.i c'.shr)
          (stateAt (ifEnd98Env env' c.i c'.shr)
            { core with pc := "for.end101", pre := some "if.end98" }) c' hexit,
        fun j => ?_⟩
      rw [show k + 1 + j = k + (1 + j) from by omega, hrun (1 + j),
        runFuel_jump_prefix hstep j]
  | r + 1, env, s, c, gate, escBit, doc, hmeasure, hshr57, hinv, hb3, hgap, hdoc, hzero,
    hcall, hkeep => by
      have hi : c.i.toNat < c.shr.toNat := hinv.index_lt
      have hsucc : (c.i + 1).toNat = c.i.toNat + 1 := by
        rw [BitVec.toNat_add, show (1 : BitVec 64).toNat = 1 from by decide]
        omega
      have hne : c.i + 1 ≠ c.shr := by
        intro heq
        have hcongr := congrArg BitVec.toNat heq
        rw [hsucc] at hcongr
        omega
      have hblk : readBytes c.mem (c.b + 64 * c.i.toNat) 64 = some (doc c.i.toNat) :=
        hdoc c.i.toNat hi
      obtain ⟨hread73, hread74⟩ := readBytes_split c.mem (c.b + 64 * c.i.toNat) 32 32 (by
        rw [show 32 + 32 = 64 from rfl]; exact hblk)
      obtain ⟨rc, hc⟩ := hcall _ _ _
      obtain ⟨hkeepDoc, hkeepZero⟩ := hkeep _ _ _ _ _ _ rc hc
      obtain ⟨env', core, c', k, hk, hrun, hl, hb', he', hxp', hnxp', hxc', hshr',
        hdoc', hzero'⟩ :=
        fusedInv_page sel env s c gate escBit ((doc c.i.toNat).take 32)
          ((doc c.i.toNat).drop 32) doc hinv hshr57 hb3 hgap hdoc hzero
          hread73 hread74 rc hc hkeepDoc hkeepZero
      have hbit : evalICmp .eq (c.i + 1) c'.shr = 0 := by
        rw [hshr']
        exact (for_inc_exitcond_iff c.i c.shr).2.mpr hne
      obtain ⟨hstep, hinv'⟩ :=
        fused_latch_loop sel env' core c.i c' gate escBit hl hbit
          (by rw [hshr']; exact hshr57)
      have hmeasure' : c'.shr.toNat - (c'.i.toNat + 1) = r := by
        rw [hshr', hl.succ, hsucc]
        omega
      have hgap' : c'.b + 64 * c'.shr.toNat ≤ c'.ent := by
        rw [hb', he', hshr']; exact hgap
      have hb3' : 3 ≤ c'.b := by rw [hb']; exact hb3
      have hkeepUpd : ∀ (or14 mask xs i : BitVec 64) (mem : Mem) (next : Nat)
          (r' : CallOutcome),
          sel escapeListCallee
            [.int 64 or14, .int 64 mask, .int 64 xs, .int 64 i,
             .ptr c'.xp, .ptr c'.nxp, .ptr c'.xcarry] mem next = some r' →
          (∀ j, j < c'.shr.toNat →
              readBytes r'.mem (c'.b + 64 * j) 64 = some (doc j)) ∧
          readBytes r'.mem (c'.b - 3) 3 = some [0, 0, 0] := by
        intro or14 mask xs i mem next r' hc'
        have h := hkeep or14 mask xs i mem next r' (by
          simpa only [hb', he', hxp', hnxp', hxc', hshr'] using hc')
        simpa only [hb', he', hxp', hnxp', hxc', hshr'] using h
      obtain ⟨e', j, hjle, hterm, hrun'⟩ :=
        fusedInv_runFuel_aux sel r (ifEnd98Env env' c.i c'.shr)
          (stateAt (ifEnd98Env env' c.i c'.shr)
            { core with pc := "for.body54", pre := some "if.end98" })
          c' gate escBit doc hmeasure'
          (by rw [hshr']; exact hshr57) hinv' hb3' hgap'
          (by simpa only [hb', hshr'] using hdoc')
          (by simpa only [hb'] using hzero') hcall hkeepUpd
      refine ⟨e', (k + 1) + j, by omega, hterm, fun k' => ?_⟩
      rw [show (k + 1) + j + k' = k + (1 + (j + k')) from by omega,
        hrun (1 + (j + k')), runFuel_jump_prefix hstep (j + k')]
      exact hrun' k'

/-- **The loop's run from the head.**  The auxiliary form at the head's own
measure, `%shr - (i + 1)` pages to go. -/
theorem fusedInv_runFuel (sel : Calls) (env : Env) (s : State) (c : FusedCarry)
    (gate escBit : BitVec 1) (doc : Nat → List UInt8)
    (hshr57 : c.shr.toNat < 2 ^ 57) (hinv : FusedInv env s c gate escBit)
    (hb3 : 3 ≤ c.b) (hgap : c.b + 64 * c.shr.toNat ≤ c.ent)
    (hdoc : ∀ j, j < c.shr.toNat → readBytes c.mem (c.b + 64 * j) 64 = some (doc j))
    (hzero : readBytes c.mem (c.b - 3) 3 = some [0, 0, 0])
    (hcall : ∀ (args : List Value) (mem : Mem) (next : Nat),
      ∃ r : CallOutcome, sel escapeListCallee args mem next = some r)
    (hkeep : ∀ (or14 mask xs i : BitVec 64) (mem : Mem) (next : Nat) (r : CallOutcome),
      sel escapeListCallee
        [.int 64 or14, .int 64 mask, .int 64 xs, .int 64 i,
         .ptr c.xp, .ptr c.nxp, .ptr c.xcarry] mem next = some r →
      (∀ j, j < c.shr.toNat → readBytes r.mem (c.b + 64 * j) 64 = some (doc j)) ∧
      readBytes r.mem (c.b - 3) 3 = some [0, 0, 0]) :
    ∃ (e : State) (j : Nat), j ≤ 5 * (c.shr.toNat - (c.i.toNat + 1)) + 5 ∧
      FusedTerm e ∧
        ∀ k, runFuel (s1BlocksCallsEsc sel) (j + k) s1BlocksFunction (stateAt env s)
          = runFuel (s1BlocksCallsEsc sel) k s1BlocksFunction e :=
  fusedInv_runFuel_aux sel (c.shr.toNat - (c.i.toNat + 1)) env s c gate escBit doc
    rfl hshr57 hinv hb3 hgap hdoc hzero hcall hkeep

/-! ### Axiom footprints

The page's runs are the blocks' own `denoteCode` equations, the induction is on
the measure, and the arithmetic is omega's.  The escape call enters through the
caller's two facts, so nothing here assumes anything about the escape unit that
the record does not supply. -/

#print axioms fused_body_run
#print axioms fused_merge_skip_page
#print axioms fused_merge_escape_page
#print axioms fused_dfa_skip_page
#print axioms fused_dfa_escape_page
#print axioms fused_windows
#print axioms fused_latch_exit
#print axioms fused_latch_loop
#print axioms fusedInv_page
#print axioms fusedInv_step
#print axioms fusedInv_runFuel_aux
#print axioms fusedInv_runFuel
