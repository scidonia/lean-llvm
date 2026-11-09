/-
The walking decoder's staging facts, and its two sixty-four-byte copies.

`DecodeInv` (`JsonEscapeExpandContract`) states the walk as the specification's own
recursion and the decoded prefix in the store, and `DecodeLatch`
(`JsonEscapeDecodeRun`) adds the register cells the iteration's blocks read.  What
neither carries is the **staging** the iteration consumes: the caller's position
list in memory, the count of its entries, the guarantee that every entry lies in
the body's window, and the body's end offset as `%add` holds it.  Those four facts
are in the record's `pre` and were in no invariant, which is why the two copies
could not be stated: a copy's source is a byte range the caller's list and body
size provide, and its destination's distance from that range is the record's
aliasing clause, not a property of the block.

`DecodeStaging` states the four facts; `StagedDecodeInv` and `StagedLatchInv` are
`DecodeInv`'s and `DecodeLatch`'s old shapes with the staging conjoined, and their
projections are the implications that leave every existing consumer untouched.

The two copies are then `BoundLoop` instances in their own right.  Each head
(`while.body.i91`, `while.body.i`) moves sixty-four bytes per visit and tests the
residual count against sixty-four, so the bound is the residual's block count and
one visit is one control step.  The measure is the iteration count: the head's own
counter advances by sixty-four bytes, which is one unit of the budget.  `step_loop`
and `step_exit` are the block's two arms at the trace's own step facts
(`udCopyBody_step`/`udCopyBodyN_step`), and the memory the invariant carries is
the copy's own statement: the source range reads back as it was and the
destination's written prefix is the source range's prefix.

**The copy's invariant needs the caller's aliasing clause, not a property of the
block.**  The second load of a visit reads at `src + k + 32` from the memory the
first store left at `dst + k`, so the two ranges must not meet; the record's
`pre` supplies exactly that (`dst + n + 64 ≤ b ∨ b + n + 32 ≤ dst`), and
`copyDisjoint` is where the copies state it.  Every frame step below is that
clause, weakened to the visit's two thirty-two-byte stores.

**The emitter's table guard, read off the record.**  The escape reader loads the
table's image of the byte after a backslash and branches on a signed compare.
`tableByte` turns the record's `readBytes mem tab 256 = some unescapeTable` into
the one-byte read the block makes, and `emitterTest_of_table` identifies the
block's branch with the specification's `simpleEscape b ≠ none` through
`unescapeTable_test`.  Those are `if.end.i`'s `ht` and branch value, supplied by
the staging instead of assumed.

**What this module does not contain.**  The two copies are the walk's per-position
and final moves, but the run that *crosses* them is not stated here.  The walk's
iteration arm (`LatchStepLoopTwo`, `JsonEscapeDecodeRun`) is
`while.body6 → if.end → this copy → its tail → us_run.exit → the escape emitter →
while.end35 → the second copy → its tail → cleanup32`.  Its copies now contribute
their proved fuel at `while.body.i91` and `while.body.i` — `copyBodyLoop_run_at`
and `copyBodyNLoop_run_at`, with `copyLoopFuel_le_decodeIterCost` placing that fuel
inside `decodeIterCost` — and its emitter's table guard is read off the record
above; the hex and surrogate halves of the emitter are the trace's `hex4_pmadd`
and the record's `DecodeInv.step_six`/`step_pair`, still to be composed into the
emitter's own run.  So the arm's two largest halves are compositions rather than
inductions, but the arm itself, and therefore `ExpandFacts.loop`, is still owed.
-/
import LeanLLVM.Vellum.JsonEscapeDecodeRun

set_option autoImplicit false
set_option maxRecDepth 16000

namespace LeanLLVM.Vellum

open LeanLLVM
open LeanLLVM.Vellum.JsonEscapeIR
open LeanLLVM.Vellum.JsonEscapeIntrinsics
open LeanLLVM.Vellum.JsonScanSpec

/-- A cell the block's own environment builder wrote, read out of the chain. -/
macro "ud_lk" : tactic => `(tactic|
  ((repeat rw [lookupName_cons_ne _ _ (by decide)]) <;>
   (first | rw [lookupName_cons_self] | rfl)))

/-! ### The staging the walk's invariant does not carry

Four facts, all of them the caller's: the position list as `*xp` holds it, its
length, each entry's place in the body's window, and the body's end offset as the
body's own `%add` carries it.  The list is read through the memory the walk holds,
because the record promises the list is outside the destination extent and the
walk writes only there.
-/
def DecodeStaging (M : Mem) (nps xp pos0 n : Nat) (ps : List Nat)
    (addv : BitVec 64) : Prop :=
  readBytes M xp (4 * nps) = some (positionsBytes 4 ps) ∧
  ps.length = nps ∧
  (∀ (j q : Nat), ps[j]? = some q → pos0 ≤ q ∧ q < pos0 + n) ∧
  addv.toNat = pos0 + n

/-- The staging's entry condition at an index inside the list.  This is the form
the block that reads a position consumes: `%arrayidx`'s load is defined when the
entry below the count is inside the body's window. -/
theorem DecodeStaging.entry {M : Mem} {nps xp pos0 n : Nat} {ps : List Nat}
    {addv : BitVec 64} (h : DecodeStaging M nps xp pos0 n ps addv)
    {j : Nat} (hj : j < nps) :
    ∃ q, ps[j]? = some q ∧ pos0 ≤ q ∧ q < pos0 + n := by
  cases hq : ps[j]? with
  | none =>
      have hle : ps.length ≤ j := List.getElem?_eq_none_iff.1 hq
      have hn : ps.length = nps := h.2.1
      omega
  | some q => exact ⟨q, rfl, h.2.2.1 j q hq⟩

/-- The walk's invariant with the staging conjoined: the old shape, unchanged, and
the four facts beside it. -/
structure StagedDecodeInv (body : List UInt8) (st : ClassState) (M : Mem) (dst nps : Nat)
    (i k : Nat) (out : List UInt8) (goal : EscapeOutcome)
    (xp pos0 n : Nat) (ps : List Nat) (addv : BitVec 64) : Prop where
  /-- The walk, exactly as `DecodeInv` states it. -/
  walk : DecodeInv body st M dst nps i k out goal
  /-- The caller's staging, beside it. -/
  staging : DecodeStaging M nps xp pos0 n ps addv

/-- **The extension implies the old invariant.**  Every consumer of `DecodeInv`
reads a `StagedDecodeInv` through this projection, so the extension adds a
hypothesis and changes no statement. -/
theorem StagedDecodeInv.toDecodeInv {body : List UInt8} {st : ClassState} {M : Mem}
    {dst nps i k : Nat} {out : List UInt8} {goal : EscapeOutcome}
    {xp pos0 n : Nat} {ps : List Nat} {addv : BitVec 64}
    (h : StagedDecodeInv body st M dst nps i k out goal xp pos0 n ps addv) :
    DecodeInv body st M dst nps i k out goal :=
  h.walk

/-- The staging beside the walk, projected on its own. -/
theorem StagedDecodeInv.staging_of {body : List UInt8} {st : ClassState} {M : Mem}
    {dst nps i k : Nat} {out : List UInt8} {goal : EscapeOutcome}
    {xp pos0 n : Nat} {ps : List Nat} {addv : BitVec 64}
    (h : StagedDecodeInv body st M dst nps i k out goal xp pos0 n ps addv) :
    DecodeStaging M nps xp pos0 n ps addv :=
  h.staging

/-- The walk's own invariant, from its instance. -/
theorem latchInv_walk {body : List UInt8} {st : ClassState} {dst nps : Nat}
    {goal : EscapeOutcome} {r : Nat} {s : State} {c : Nat}
    (h : LatchInv body st dst nps goal r s c) :
    ∃ (i : Nat) (out : List UInt8), DecodeInv body st s.mem dst nps i c out goal := by
  obtain ⟨i, out, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hwalk, _, _, _, _, _,
    _, _, _, _, _, _, _, _, _, _, _, _, _, _⟩ := h.1
  exact ⟨i, out, hwalk⟩

/-- The latch invariant with the staging conjoined.  The `%add` cell the staging
names is the one the state carries, so the two halves speak about one state. -/
def StagedLatchInv (body : List UInt8) (st : ClassState) (dst nps : Nat)
    (goal : EscapeOutcome) (xp pos0 n : Nat) (ps : List Nat)
    (r c : Nat) (s : State) : Prop :=
  LatchInv body st dst nps goal r s c ∧
  ∃ addv : BitVec 64,
    DecodeStaging s.mem nps xp pos0 n ps addv ∧
    lookupName s.env "%add" = some (.int 64 addv)

/-- **The latch's extension implies the latch's old invariant.** -/
theorem stagedLatchInv_latch {body : List UInt8} {st : ClassState} {dst nps : Nat}
    {goal : EscapeOutcome} {xp pos0 n : Nat} {ps : List Nat} {r c : Nat} {s : State}
    (h : StagedLatchInv body st dst nps goal xp pos0 n ps r c s) :
    LatchInv body st dst nps goal r s c :=
  h.1

/-- **The latch's extension implies the walk's old invariant**, which is the
statement the loop instance consumes. -/
theorem stagedLatchInv_decodeInv {body : List UInt8} {st : ClassState} {dst nps : Nat}
    {goal : EscapeOutcome} {xp pos0 n : Nat} {ps : List Nat} {r c : Nat} {s : State}
    (h : StagedLatchInv body st dst nps goal xp pos0 n ps r c s) :
    ∃ (i : Nat) (out : List UInt8), DecodeInv body st s.mem dst nps i c out goal :=
  latchInv_walk h.1

/-- The staging at the latch, on its own. -/
theorem stagedLatchInv_staging {body : List UInt8} {st : ClassState} {dst nps : Nat}
    {goal : EscapeOutcome} {xp pos0 n : Nat} {ps : List Nat} {r c : Nat} {s : State}
    (h : StagedLatchInv body st dst nps goal xp pos0 n ps r c s) :
    ∃ addv : BitVec 64,
      DecodeStaging s.mem nps xp pos0 n ps addv ∧
      lookupName s.env "%add" = some (.int 64 addv) :=
  h.2

/-- The staged latch's budget pair, from the old invariant. -/
theorem stagedLatchInv_budget {body : List UInt8} {st : ClassState} {dst nps : Nat}
    {goal : EscapeOutcome} {xp pos0 n : Nat} {ps : List Nat} {r c : Nat} {s : State}
    (h : StagedLatchInv body st dst nps goal xp pos0 n ps r c s) :
    c ≤ nps ∧ nps ≤ c + r :=
  latchInv_budget h.1

/-- The walk's entry with the staging beside it: `DecodeInv`'s own seed, and the
caller's four facts.  This is the form the assembly's entry stage produces and the
staging the copies below read. -/
theorem stagedDecodeInv_seed {body : List UInt8} {st : ClassState} {dst nps k0 : Nat}
    {xp pos0 n : Nat} {ps : List Nat} {addv : BitVec 64} {M : Mem}
    (hlist : (escAt body st 0).length = nps) (hstage : DecodeStaging M nps xp pos0 n ps addv) :
    StagedDecodeInv body st M dst nps 0 k0 []
      (escapeDecodeGo body 0 k0 ((escAt body st 0).drop k0) []) xp pos0 n ps addv :=
  ⟨decodeInv_seed hlist, hstage⟩


/-! ### The residual's block count

A copy's head tests `%sub13 - (%k + 64) > 64`: it goes round again while the
residual has a block's worth past the next one.  The trip count is therefore the
number of sixty-four-byte blocks in `sub - 128`, rounded up, and that number is a
term of the caller's arguments — the residual count, which is `n - i` at the
walk's cursor.  `copyIterBound` is that number, and the three lemmas below are
what the two arms consume: an advance stays inside the residual, the exit at the
bound leaves a residual of at most one block, and the counter never passes the
residual.
-/
def copyIterBound (sub : Nat) : Nat := (sub - 128 + 63) / 64

/-- The ceiling: `x ≤ 64 * ⌈x / 64⌉`, which is what makes the bound the trip
count rather than an estimate. -/
theorem le_mul_div_ceil (x : Nat) : x ≤ 64 * ((x + 63) / 64) := by
  have h := Nat.div_add_mod (x + 63) 64
  have hr := Nat.mod_lt (x + 63) (by decide : 0 < 64)
  rw [Nat.mul_comm]
  omega

/-- The bound is inside the residual: sixty-four bytes per unit of it. -/
theorem copyIterBound_mul_le (sub : Nat) : 64 * copyIterBound sub ≤ sub := by
  have h2 : 64 * copyIterBound sub ≤ sub - 128 + 63 := by
    rw [copyIterBound, Nat.mul_comm]
    exact Nat.div_mul_le_self _ _
  by_cases h : 63 ≤ sub
  · omega
  · have hz : sub - 128 = 0 := by omega
    have hN : copyIterBound sub = 0 := by
      rw [copyIterBound, hz]
    omega

/-- A counter below the bound leaves a residual longer than the next block plus
the test's own sixty-four bytes, so the head's `ugt` is one. -/
theorem copyIterBound_advance {sub c : Nat} (h : c < copyIterBound sub) :
    64 * c + 128 < sub := by
  have h2 : 64 * copyIterBound sub ≤ sub - 128 + 63 := by
    rw [copyIterBound, Nat.mul_comm]
    exact Nat.div_mul_le_self _ _
  have h3 : 64 * c + 64 ≤ 64 * copyIterBound sub := by
    have hc : c + 1 ≤ copyIterBound sub := h
    have hm := Nat.mul_le_mul_left 64 hc
    omega
  by_cases hs : 128 ≤ sub
  · omega
  · have hz : sub - 128 = 0 := by omega
    have hN : copyIterBound sub = 0 := by
      rw [copyIterBound, hz]
    omega

/-- At the bound the head's test is zero: the next block plus the test's own
sixty-four bytes reach the residual's end. -/
theorem copyIterBound_exit {sub c : Nat} (hlo : c ≤ copyIterBound sub)
    (hhi : copyIterBound sub ≤ c) (hgate : 64 < sub) :
    sub - (64 * c + 64) ≤ 64 := by
  have hc : c = copyIterBound sub := by omega
  rw [hc]
  have hceil : sub - 128 ≤ 64 * copyIterBound sub := by
    simpa [copyIterBound] using le_mul_div_ceil (sub - 128)
  by_cases hs : 128 ≤ sub
  · omega
  · have hz : sub - 128 = 0 := by omega
    have hN : copyIterBound sub = 0 := by
      rw [copyIterBound, hz]
    omega

/-- At the bound the residual still holds the visit's sixty-four bytes. -/
theorem copyIterBound_step_le {sub c : Nat} (hlo : c ≤ copyIterBound sub)
    (hhi : copyIterBound sub ≤ c) (hgate : 64 < sub) :
    64 * c + 64 ≤ sub := by
  have hc : c = copyIterBound sub := by omega
  rw [hc]
  have h2 : 64 * copyIterBound sub ≤ sub - 128 + 63 := by
    rw [copyIterBound, Nat.mul_comm]
    exact Nat.div_mul_le_self _ _
  by_cases hs : 128 ≤ sub
  · omega
  · have hz : sub - 128 = 0 := by omega
    have hN : copyIterBound sub = 0 := by
      rw [copyIterBound, hz]
    omega

/-! ### The two copies' names -/

/-- The register names and the phi table one of the two `<4 x i64>` copies uses.
The blocks are the same shape (`udCopyBody_instrs`, `udCopyBodyN_instrs`), so one
invariant and one induction serve both; the names are what tell them apart. -/
structure CopyNames where
  /-- The head: the block that copies and tests. -/
  head : String
  /-- The block the head leaves for when its test is zero. -/
  tail : String
  /-- The head's counter `phi`. -/
  kreg : String
  /-- The head's own `%add.i…`: the counter the back edge carries. -/
  knext : String
  /-- The head's own `%sub.i…`: the residual the back edge carries. -/
  snext : String
  /-- The source base. -/
  srcreg : String
  /-- The destination base. -/
  dstreg : String
  /-- The residual count. -/
  subreg : String
  /-- The counter `phi`'s incoming table. -/
  incoming : List (String × Operand)

/-! ### The copy's invariant -/

/-- The head's exit test, at the carried iteration count: the copy leaves exactly
when the count reaches the residual's block count. -/
def copyAtBound (sub : Nat) : State → Nat → Bool := fun _ c => decide (copyIterBound sub ≤ c)

/-- The two ranges a visit's stores reach never meet the source range.  The first
disjunct is the record's `dst + n + 64 ≤ b`, the second its `b + n + 32 ≤ dst`; the
residual narrows both. -/
def copyDisjoint (src dst sub : Nat) : Prop :=
  dst + sub + 64 ≤ src ∨ src + sub + 32 ≤ dst

/-- **A copy's invariant at its head.**  The state is at the head carrying the
iteration count `c` and the byte counter `%k = 64 c`; the source range
`[src, src + sub + 32)` reads back as the caller's bytes `B`; the destination holds
`B`'s first `64 c` bytes; and the three staging facts the record supplies are the
disjointness of the ranges, the residual below the sign-extension bound, and the
residual above one block (the head is only entered when its test is one).

The counter and the predecessor are existentially bound rather than stored: the
invariant is a `Prop`, so the block's data is read out of it at each arm. -/
def CopyInv (nm : CopyNames) (src dst sub : Nat) (B : List UInt8)
    (r c : Nat) (s : State) : Prop :=
  ∃ (prev : String) (op : Operand) (k : BitVec 64),
    s.pc = nm.head ∧
    s.pre = some prev ∧
    phiIncoming prev nm.incoming = some op ∧
    evalOperand s op = some (.int 64 k) ∧
    k = BitVec.ofNat 64 (64 * c) ∧
    lookupName s.env nm.srcreg = some (.ptr src) ∧
    lookupName s.env nm.dstreg = some (.ptr dst) ∧
    lookupName s.env nm.subreg = some (.int 64 (BitVec.ofNat 64 sub)) ∧
    readBytes s.mem src (sub + 32) = some B ∧
    B.length = sub + 32 ∧
    readBytes s.mem dst (64 * c) = some (B.take (64 * c)) ∧
    copyDisjoint src dst sub ∧
    sub < 2 ^ 63 ∧
    64 < sub ∧
    c ≤ copyIterBound sub ∧
    copyIterBound sub ≤ c + r

/-- The source range's first thirty-two bytes at a visit's counter. -/
theorem copySrc_read {M : Mem} {src sub k : Nat} {B : List UInt8}
    (hB : readBytes M src (sub + 32) = some B) (hk : k ≤ sub) :
    readBytes M (src + k) 32 = some ((B.drop k).take 32) := by
  have hB' : readBytes M src (k + (sub + 32 - k)) = some B := by
    rw [show k + (sub + 32 - k) = sub + 32 from by omega]
    exact hB
  obtain ⟨_, h2⟩ := readBytes_split M src k (sub + 32 - k) hB'
  have h1 : sub + 32 - k = 32 + (sub - k) := by omega
  rw [h1] at h2
  exact (readBytes_split M (src + k) 32 (sub - k) h2).1

/-- The source range's second thirty-two bytes at a visit's counter. -/
theorem copySrc_read_mid {M : Mem} {src sub k : Nat} {B : List UInt8}
    (hB : readBytes M src (sub + 32) = some B) (hk : k + 32 ≤ sub) :
    readBytes M (src + k + 32) 32 = some ((B.drop (k + 32)).take 32) := by
  have hB' : readBytes M src ((k + 32) + (sub + 32 - (k + 32))) = some B := by
    rw [show (k + 32) + (sub + 32 - (k + 32)) = sub + 32 from by omega]
    exact hB
  obtain ⟨_, h2⟩ := readBytes_split M src (k + 32) (sub + 32 - (k + 32)) hB'
  have h1 : sub + 32 - (k + 32) = 32 + (sub - (k + 32)) := by omega
  rw [h1] at h2
  have h3 : readBytes M (src + k + 32) (32 + (sub - (k + 32)))
      = some (B.drop (k + 32)) := by
    rw [show src + k + 32 = src + (k + 32) from by omega]
    exact h2
  exact (readBytes_split M (src + k + 32) 32 (sub - (k + 32)) h3).1

/-- The chunk a visit stores is thirty-two bytes long. -/
theorem copyChunk_length {B : List UInt8} {k : Nat} (hk : k + 32 ≤ B.length) :
    ((B.drop k).take 32).length = 32 := by
  rw [List.length_take, List.length_drop]
  exact Nat.min_eq_left (by omega)

/-- A thirty-two-byte block's place in the destination prefix. -/
theorem take_split_sixtyFour (B : List UInt8) (k : Nat) :
    B.take k ++ (B.drop k).take 32 ++ (B.drop (k + 32)).take 32 = B.take (k + 64) := by
  have h1 : B.take (k + 64) = B.take k ++ (B.drop k).take 64 := List.take_add
  have h2 : (B.drop k).take 64 = (B.drop k).take 32 ++ (B.drop (k + 32)).take 32 := by
    rw [show (64 : Nat) = 32 + 32 from by decide, List.take_add]
    rw [List.drop_drop]
  rw [h1, h2, List.append_assoc]

/-- The copy's two stores leave the destination prefix one block longer. -/
theorem readBytes_copy2Mem_dst (mem : Mem) (dst k : Nat) (B bs1 bs2 : List UInt8)
    (hpre : readBytes mem dst k = some (B.take k))
    (h1 : bs1 = (B.drop k).take 32) (h2 : bs2 = (B.drop (k + 32)).take 32)
    (hk : k + 64 ≤ B.length) :
    readBytes (udCopy2Mem mem (dst + k) bs1 bs2) dst (k + 64) = some (B.take (k + 64)) := by
  have hl1 : bs1.length = 32 := by rw [h1]; exact copyChunk_length (by omega)
  have hl2 : bs2.length = 32 := by rw [h2]; exact copyChunk_length (by omega)
  have hmem : udCopy2Mem mem (dst + k) bs1 bs2
      = writeBytes (writeBytes mem (dst + k) bs1) (dst + (k + 32)) bs2 := by
    simp only [udCopy2Mem]
    rw [show (dst + k) + 32 = dst + (k + 32) from by omega]
  rw [hmem]
  have hb : readBytes (writeBytes mem (dst + k) bs1) dst k = some (B.take k) := by
    rw [readBytes_writeBytes_below mem bs1 k dst (dst + k) (by omega)]
    exact hpre
  have hm : readBytes (writeBytes mem (dst + k) bs1) (dst + k) 32 = some bs1 := by
    have h := readBytes_writeBytes_same mem bs1 (addr := dst + k)
    rwa [hl1] at h
  have hmid : readBytes (writeBytes mem (dst + k) bs1) dst (k + 32)
      = some (B.take k ++ bs1) := by
    have h := JsonEntrySteps.readBytes_append (writeBytes mem (dst + k) bs1) k dst
      (B.take k) 32 bs1 hb hm
    simpa using h
  have hb2 : readBytes (writeBytes (writeBytes mem (dst + k) bs1) (dst + (k + 32)) bs2)
      dst (k + 32) = some (B.take k ++ bs1) := by
    rw [readBytes_writeBytes_below (writeBytes mem (dst + k) bs1) bs2 (k + 32) dst
      (dst + (k + 32)) (by omega)]
    exact hmid
  have hm2 : readBytes (writeBytes (writeBytes mem (dst + k) bs1) (dst + (k + 32)) bs2)
      (dst + (k + 32)) 32 = some bs2 := by
    have h := readBytes_writeBytes_same
      (writeBytes mem (dst + k) bs1) bs2 (addr := dst + (k + 32))
    rwa [hl2] at h
  have hfin := JsonEntrySteps.readBytes_append
    (writeBytes (writeBytes mem (dst + k) bs1) (dst + (k + 32)) bs2) (k + 32) dst
    (B.take k ++ bs1) 32 bs2 hb2 hm2
  have hlist : (B.take k ++ bs1) ++ bs2 = B.take (k + 64) := by
    rw [h1, h2, take_split_sixtyFour B k]
  rw [show (k + 32) + 32 = k + 64 from by omega] at hfin
  rw [hlist] at hfin
  exact hfin

/-- The copy's stores leave the source range as it was.  Each of them is outside
it, and which side is the `copyDisjoint` staging's. -/
theorem readBytes_copy2Mem_src {mem : Mem} {src dst sub k : Nat} {B bs1 bs2 : List UInt8}
    (hB : readBytes mem src (sub + 32) = some B)
    (hdisj : copyDisjoint src dst sub)
    (hlen1 : bs1.length = 32) (hlen2 : bs2.length = 32)
    (hk : k + 64 ≤ sub + 64) :
    readBytes (udCopy2Mem mem (dst + k) bs1 bs2) src (sub + 32) = some B := by
  have hmem : udCopy2Mem mem (dst + k) bs1 bs2
      = writeBytes (writeBytes mem (dst + k) bs1) (dst + (k + 32)) bs2 := by
    simp only [udCopy2Mem]
    rw [show (dst + k) + 32 = dst + (k + 32) from by omega]
  rw [hmem]
  have hw2 : readBytes (writeBytes (writeBytes mem (dst + k) bs1) (dst + (k + 32)) bs2)
      src (sub + 32) = readBytes (writeBytes mem (dst + k) bs1) src (sub + 32) := by
    refine JsonEntrySteps.readBytes_writeBytes_frame _ bs2 (dst + (k + 32)) src (sub + 32) ?_
    rcases hdisj with hd | hd
    · right; rw [hlen2]; omega
    · left; omega
  have hw1 : readBytes (writeBytes mem (dst + k) bs1) src (sub + 32)
      = readBytes mem src (sub + 32) := by
    refine JsonEntrySteps.readBytes_writeBytes_frame _ bs1 (dst + k) src (sub + 32) ?_
    rcases hdisj with hd | hd
    · right; rw [hlen1]; omega
    · left; omega
  rw [hw2, hw1]
  exact hB

/-- `ugt` at zero is the non-strict order on the operands' `Nat` readings. -/
theorem evalICmp_ugt_zero_iff {w : Nat} (x y : BitVec w) :
    evalICmp .ugt x y = (0 : BitVec 1) ↔ ¬ y.toNat < x.toNat := by
  unfold evalICmp
  cases hb : BitVec.ult y x
  · have h : ¬ y.toNat < x.toNat := by
      intro hlt
      have htrue : BitVec.ult y x = true := (BitVec.ult_iff_toNat_lt).2 hlt
      rw [htrue] at hb
      exact Bool.noConfusion hb
    simp [h]
  · have h : y.toNat < x.toNat := by
      rw [← BitVec.ult_iff_toNat_lt]
      exact hb
    simp [h]

/-- The head's test reads at a counter: `%cmp = ugt (sub - (k + 64)) 64`. -/
def copyTest (sub : Nat) (k : BitVec 64) : BitVec 1 :=
  evalICmp .ugt (BitVec.ofNat 64 sub - (k + BitVec.ofInt 64 64)) (BitVec.ofInt 64 64)

/-- The counter as a sum, which is what `mkEnv`'s back edge binds. -/
theorem copyK_sum {k : BitVec 64} {c : Nat}
    (hk : k = BitVec.ofNat 64 (64 * c)) :
    k + BitVec.ofInt 64 64 = BitVec.ofNat 64 (64 * c + 64) := by
  rw [hk, BitVec.ofInt_ofNat, BitVec.ofNat_add_ofNat]

/-- The test's `Nat` reading at a counter below the residual. -/
theorem copyTest_toNat {sub : Nat} {k : BitVec 64} {c : Nat}
    (hk : k = BitVec.ofNat 64 (64 * c)) (h64 : sub < 2 ^ 63)
    (hle : 64 * c + 64 ≤ sub) :
    (BitVec.ofNat 64 sub - (k + BitVec.ofInt 64 64)).toNat = sub - (64 * c + 64) := by
  have hsum : k + BitVec.ofInt 64 64 = BitVec.ofNat 64 (64 * c + 64) := copyK_sum hk
  have hs : (BitVec.ofNat 64 sub).toNat = sub := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hk64 : (BitVec.ofNat 64 (64 * c + 64)).toNat = 64 * c + 64 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have horder : BitVec.ofNat 64 (64 * c + 64) ≤ BitVec.ofNat 64 sub := by
    rw [BitVec.le_def, hk64, hs]
    omega
  rw [hsum, BitVec.toNat_sub_of_le horder, hs, hk64]

/-- The counter at a successor visit. -/
theorem copyNext_counter {k : BitVec 64} {c : Nat}
    (hk : k = BitVec.ofNat 64 (64 * c)) :
    k + BitVec.ofInt 64 64 = BitVec.ofNat 64 (64 * (c + 1)) := by
  rw [hk, BitVec.ofInt_ofNat, BitVec.ofNat_add_ofNat]
  rw [show 64 * (c + 1) = 64 * c + 64 from by omega]


/-- The state one visit of a copy's head leaves before its control step: its two
thirty-two-byte chunks written at `dst + k`, the environment its own builder makes,
and the block it takes.  The trace's step facts conclude at exactly this state. -/
def CopyStepState (nm : CopyNames)
    (mkEnv : Env → Nat → Nat → BitVec 64 → List UInt8 → List UInt8 → BitVec 64 → Env)
    (s : State) (src dst sub : Nat) (k : BitVec 64) (bs1 bs2 : List UInt8)
    (target : String) : State :=
  let s1 : State := { s with mem := udCopy2Mem s.mem (dst + k.toNat) bs1 bs2 }
  let s2 : State := { s1 with pc := target, pre := some nm.head }
  withEnv (mkEnv s.env src dst k bs1 bs2 (BitVec.ofNat 64 sub)) s2

/-- The step state's block. -/
theorem CopyStepState_pc (nm : CopyNames)
    (mkEnv : Env → Nat → Nat → BitVec 64 → List UInt8 → List UInt8 → BitVec 64 → Env)
    (s : State) (src dst sub : Nat) (k : BitVec 64) (bs1 bs2 : List UInt8) (target : String) :
    (CopyStepState nm mkEnv s src dst sub k bs1 bs2 target).pc = target := rfl

/-- The step state's predecessor. -/
theorem CopyStepState_pre (nm : CopyNames)
    (mkEnv : Env → Nat → Nat → BitVec 64 → List UInt8 → List UInt8 → BitVec 64 → Env)
    (s : State) (src dst sub : Nat) (k : BitVec 64) (bs1 bs2 : List UInt8) (target : String) :
    (CopyStepState nm mkEnv s src dst sub k bs1 bs2 target).pre = some nm.head := rfl

/-- The step state's environment. -/
theorem CopyStepState_env (nm : CopyNames)
    (mkEnv : Env → Nat → Nat → BitVec 64 → List UInt8 → List UInt8 → BitVec 64 → Env)
    (s : State) (src dst sub : Nat) (k : BitVec 64) (bs1 bs2 : List UInt8) (target : String) :
    (CopyStepState nm mkEnv s src dst sub k bs1 bs2 target).env
      = mkEnv s.env src dst k bs1 bs2 (BitVec.ofNat 64 sub) := rfl

/-- The step state's memory. -/
theorem CopyStepState_mem (nm : CopyNames)
    (mkEnv : Env → Nat → Nat → BitVec 64 → List UInt8 → List UInt8 → BitVec 64 → Env)
    (s : State) (src dst sub : Nat) (k : BitVec 64) (bs1 bs2 : List UInt8) (target : String) :
    (CopyStepState nm mkEnv s src dst sub k bs1 bs2 target).mem
      = udCopy2Mem s.mem (dst + k.toNat) bs1 bs2 := rfl

/-- What the copy leaves at its tail: the cells its tail block reads, the source
range, and the destination prefix one block longer. -/
def CopyExitWord (nm : CopyNames) (src dst sub : Nat) (B : List UInt8) (e : State) : Prop :=
  e.pc = nm.tail ∧
  e.pre = some nm.head ∧
  lookupName e.env nm.knext =
    some (.int 64 (BitVec.ofNat 64 (64 * copyIterBound sub + 64))) ∧
  lookupName e.env nm.snext =
    some (.int 64 (BitVec.ofNat 64 (sub - (64 * copyIterBound sub + 64)))) ∧
  lookupName e.env nm.srcreg = some (.ptr src) ∧
  lookupName e.env nm.dstreg = some (.ptr dst) ∧
  lookupName e.env nm.subreg = some (.int 64 (BitVec.ofNat 64 sub)) ∧
  readBytes e.mem dst (64 * copyIterBound sub + 64) =
    some (B.take (64 * copyIterBound sub + 64)) ∧
  readBytes e.mem src (sub + 32) = some B

/-! ### The two heads' phi tables -/

def copyBodyNames : CopyNames where
  head := "while.body.i91"
  tail := "us_run_long.exit99"
  kreg := "%k.0.i86290"
  knext := "%add.i98"
  snext := "%sub.i87"
  srcreg := "%add.ptr"
  dstreg := "%add.ptr12"
  subreg := "%sub13"
  incoming := udCopyBodyIncoming

def copyBodyNNames : CopyNames where
  head := "while.body.i"
  tail := "us_run_long.exit"
  kreg := "%k.0.i304"
  knext := "%add.i"
  snext := "%sub.i"
  srcreg := "%add.ptr36"
  dstreg := "%add.ptr37"
  subreg := "%sub38"
  incoming := udCopyBodyNIncoming

theorem copyBodyNames_head_phi :
    phiIncoming copyBodyNames.head copyBodyNames.incoming
      = some (.reg copyBodyNames.knext) := by
  simp only [copyBodyNames]
  decide

theorem copyBodyNNames_head_phi :
    phiIncoming copyBodyNNames.head copyBodyNNames.incoming
      = some (.reg copyBodyNNames.knext) := by
  simp only [copyBodyNNames]
  decide

/-! ### The instance

One induction serves both copies: the head's block is the same shape in each, so
the arms take the block's own step fact as their hypothesis and everything else —
the test's arithmetic, the two ranges, the destination prefix — is proved once.
-/

def copyBoundLoop
    (nm : CopyNames)
    (mkEnv : Env → Nat → Nat → BitVec 64 → List UInt8 → List UInt8 → BitVec 64 → Env)
    (src dst sub : Nat) (B : List UInt8)
    (phiHead : phiIncoming nm.head nm.incoming = some (.reg nm.knext))
    (envKnext : ∀ (env : Env) (src' dst' : Nat) (k' : BitVec 64) (bs1 bs2 : List UInt8)
      (subv : BitVec 64),
      lookupName (mkEnv env src' dst' k' bs1 bs2 subv) nm.knext
        = some (.int 64 (k' + BitVec.ofInt 64 64)))
    (envSnext : ∀ (env : Env) (src' dst' : Nat) (k' : BitVec 64) (bs1 bs2 : List UInt8)
      (subv : BitVec 64),
      lookupName (mkEnv env src' dst' k' bs1 bs2 subv) nm.snext
        = some (.int 64 (subv - (k' + BitVec.ofInt 64 64))))
    (envSrc : ∀ (env : Env) (src' dst' : Nat) (k' : BitVec 64) (bs1 bs2 : List UInt8)
      (subv : BitVec 64),
      lookupName (mkEnv env src' dst' k' bs1 bs2 subv) nm.srcreg = lookupName env nm.srcreg)
    (envDst : ∀ (env : Env) (src' dst' : Nat) (k' : BitVec 64) (bs1 bs2 : List UInt8)
      (subv : BitVec 64),
      lookupName (mkEnv env src' dst' k' bs1 bs2 subv) nm.dstreg = lookupName env nm.dstreg)
    (envSub : ∀ (env : Env) (src' dst' : Nat) (k' : BitVec 64) (bs1 bs2 : List UInt8)
      (subv : BitVec 64),
      lookupName (mkEnv env src' dst' k' bs1 bs2 subv) nm.subreg = lookupName env nm.subreg)
    (stepBack : ∀ (s : State) (prev : String) (op : Operand) (e : State)
        (k : BitVec 64) (bs1 bs2 : List UInt8),
      s.pc = nm.head → s.pre = some prev → phiIncoming prev nm.incoming = some op →
      evalOperand (withEnv s.env s) op = some (.int 64 k) →
      lookupName s.env nm.srcreg = some (.ptr src) →
      lookupName s.env nm.dstreg = some (.ptr dst) →
      lookupName s.env nm.subreg = some (.int 64 (BitVec.ofNat 64 sub)) →
      k.toNat < 2 ^ 63 → (BitVec.signExtend 64 k).toNat = k.toNat →
      readBytes s.mem (src + k.toNat) 32 = some bs1 →
      readBytes (writeBytes s.mem (dst + k.toNat) bs1) (src + k.toNat + 32) 32 = some bs2 →
      bs1.length = 32 → bs2.length = 32 → copyTest sub k = (1 : BitVec 1) →
      e = CopyStepState nm mkEnv s src dst sub k bs1 bs2 nm.head →
      step escapeCalls usDecFunction s = .jump e)
    (stepExit : ∀ (s : State) (prev : String) (op : Operand) (e : State)
        (k : BitVec 64) (bs1 bs2 : List UInt8),
      s.pc = nm.head → s.pre = some prev → phiIncoming prev nm.incoming = some op →
      evalOperand (withEnv s.env s) op = some (.int 64 k) →
      lookupName s.env nm.srcreg = some (.ptr src) →
      lookupName s.env nm.dstreg = some (.ptr dst) →
      lookupName s.env nm.subreg = some (.int 64 (BitVec.ofNat 64 sub)) →
      k.toNat < 2 ^ 63 → (BitVec.signExtend 64 k).toNat = k.toNat →
      readBytes s.mem (src + k.toNat) 32 = some bs1 →
      readBytes (writeBytes s.mem (dst + k.toNat) bs1) (src + k.toNat + 32) 32 = some bs2 →
      bs1.length = 32 → bs2.length = 32 → copyTest sub k = (0 : BitVec 1) →
      e = CopyStepState nm mkEnv s src dst sub k bs1 bs2 nm.tail →
      step escapeCalls usDecFunction s = .jump e) :
    BoundLoop escapeCalls usDecFunction where
  head := nm.head
  exitBlock := nm.tail
  N := copyIterBound sub
  cost := 1
  Inv := fun r s c => CopyInv nm src dst sub B r c s
  atBound := copyAtBound sub
  Exit := fun e => e.pc = nm.tail
  ExitWord := fun e => CopyExitWord nm src dst sub B e
  step_exit := by
    intro r s c h hat
    obtain ⟨prev, op, k, hpc, hpre, hinc, hop, hkval, hsrc, hdst, hsubc, hwhole,
      hBlen, hprefix, hdisj, hsub63, hgate, hlo, hhi⟩ := h
    have hat' : copyIterBound sub ≤ c := by
      have := hat
      simp only [copyAtBound] at this
      exact of_decide_eq_true this
    have hc : c = copyIterBound sub := by omega
    have hbnd := copyIterBound_mul_le sub
    have hkN : k.toNat = 64 * c := by
      rw [hkval, BitVec.toNat_ofNat]
      omega
    have hkNlt : k.toNat < 2 ^ 63 := by omega
    have hspan : 64 * c + 64 ≤ sub := copyIterBound_step_le hlo hat' hgate
    have hgap : sub - (64 * c + 64) ≤ 64 := copyIterBound_exit hlo hat' hgate
    have hle : k.toNat ≤ sub := by omega
    have hmid : k.toNat + 32 ≤ sub := by omega
    have h64v : (BitVec.ofInt 64 64).toNat = 64 := by decide
    have hr1 : readBytes s.mem (src + k.toNat) 32 = some ((B.drop k.toNat).take 32) :=
      copySrc_read hwhole hle
    have hm : readBytes s.mem (src + k.toNat + 32) 32
        = some ((B.drop (k.toNat + 32)).take 32) := copySrc_read_mid hwhole hmid
    have hl1 : ((B.drop k.toNat).take 32).length = 32 := by
      refine copyChunk_length ?_
      rw [hBlen]; omega
    have hl2 : ((B.drop (k.toNat + 32)).take 32).length = 32 := by
      refine copyChunk_length ?_
      rw [hBlen]; omega
    have hfr := JsonEntrySteps.readBytes_writeBytes_frame s.mem ((B.drop k.toNat).take 32)
      (dst + k.toNat) (src + k.toNat + 32) 32 (by
        rcases hdisj with hd | hd
        · right; omega
        · left; omega)
    have hr2 : readBytes (writeBytes s.mem (dst + k.toNat) ((B.drop k.toNat).take 32))
        (src + k.toNat + 32) 32 = some ((B.drop (k.toNat + 32)).take 32) := by
      rw [hfr]
      exact hm
    have htest : copyTest sub k = (0 : BitVec 1) := by
      refine (evalICmp_ugt_zero_iff _ _).2 ?_
      rw [h64v, copyTest_toNat hkval hsub63 hspan]
      omega
    let e : State := CopyStepState nm mkEnv s src dst sub k
      ((B.drop k.toNat).take 32) ((B.drop (k.toNat + 32)).take 32) nm.tail
    have he : e = CopyStepState nm mkEnv s src dst sub k
        ((B.drop k.toNat).take 32) ((B.drop (k.toNat + 32)).take 32) nm.tail := rfl
    have hstep : step escapeCalls usDecFunction s = .jump e := by
      rw [he]
      exact stepExit s prev op _ k _ _ hpc hpre hinc hop hsrc hdst hsubc hkNlt
        (by rw [BitVec.signExtend_eq]) hr1 hr2 hl1 hl2 htest rfl
    refine ⟨e, 1, by omega, ?_, ?_, fun k' => runFuel_jump_prefix hstep k'⟩
    · rw [he, CopyStepState_pc]
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [he, CopyStepState_pc]
      · rw [he, CopyStepState_pre]
      · rw [he, CopyStepState_env, envKnext s.env src dst k _ _ (BitVec.ofNat 64 sub),
          copyK_sum hkval, ← hc]
      · rw [he, CopyStepState_env, envSnext s.env src dst k _ _ (BitVec.ofNat 64 sub)]
        have hv : BitVec.ofNat 64 sub - (k + BitVec.ofInt 64 64)
            = BitVec.ofNat 64 (sub - (64 * copyIterBound sub + 64)) := by
          refine BitVec.toNat_inj.1 ?_
          rw [copyTest_toNat hkval hsub63 hspan, BitVec.toNat_ofNat, ← hc,
            Nat.mod_eq_of_lt (by omega)]
        rw [hv]
      · rw [he, CopyStepState_env, envSrc s.env src dst k _ _ (BitVec.ofNat 64 sub)]
        exact hsrc
      · rw [he, CopyStepState_env, envDst s.env src dst k _ _ (BitVec.ofNat 64 sub)]
        exact hdst
      · rw [he, CopyStepState_env, envSub s.env src dst k _ _ (BitVec.ofNat 64 sub)]
        exact hsubc
      · rw [he, CopyStepState_mem, hkN]
        have hp : readBytes s.mem dst (64 * c) = some (B.take (64 * c)) := hprefix
        have hh := readBytes_copy2Mem_dst s.mem dst (64 * c) B _ _ hp rfl rfl
          (by rw [hBlen]; omega)
        rw [← hc]
        exact hh
      · rw [he, CopyStepState_mem]
        exact readBytes_copy2Mem_src hwhole hdisj hl1 hl2 (by omega)
  step_loop := by
    intro r s c h hat
    obtain ⟨prev, op, k, hpc, hpre, hinc, hop, hkval, hsrc, hdst, hsubc, hwhole,
      hBlen, hprefix, hdisj, hsub63, hgate, hlo, hhi⟩ := h
    have hat' : ¬ copyIterBound sub ≤ c := by
      have := hat
      simp only [copyAtBound] at this
      exact of_decide_eq_false this
    have hcN : c < copyIterBound sub := by omega
    have hbnd := copyIterBound_mul_le sub
    have hkN : k.toNat = 64 * c := by
      rw [hkval, BitVec.toNat_ofNat]
      omega
    have hkNlt : k.toNat < 2 ^ 63 := by omega
    have hspan : 64 * c + 128 < sub := copyIterBound_advance hcN
    have hspan' : 64 * c + 64 ≤ sub := by omega
    have hle : k.toNat ≤ sub := by omega
    have hmid : k.toNat + 32 ≤ sub := by omega
    have h64v : (BitVec.ofInt 64 64).toNat = 64 := by decide
    have hr1 : readBytes s.mem (src + k.toNat) 32 = some ((B.drop k.toNat).take 32) :=
      copySrc_read hwhole hle
    have hm : readBytes s.mem (src + k.toNat + 32) 32
        = some ((B.drop (k.toNat + 32)).take 32) := copySrc_read_mid hwhole hmid
    have hl1 : ((B.drop k.toNat).take 32).length = 32 := by
      refine copyChunk_length ?_
      rw [hBlen]; omega
    have hl2 : ((B.drop (k.toNat + 32)).take 32).length = 32 := by
      refine copyChunk_length ?_
      rw [hBlen]; omega
    have hfr := JsonEntrySteps.readBytes_writeBytes_frame s.mem ((B.drop k.toNat).take 32)
      (dst + k.toNat) (src + k.toNat + 32) 32 (by
        rcases hdisj with hd | hd
        · right; omega
        · left; omega)
    have hr2 : readBytes (writeBytes s.mem (dst + k.toNat) ((B.drop k.toNat).take 32))
        (src + k.toNat + 32) 32 = some ((B.drop (k.toNat + 32)).take 32) := by
      rw [hfr]
      exact hm
    have htest : copyTest sub k = (1 : BitVec 1) := by
      refine (evalICmp_ugt_one_iff_toNat _ _).2 ?_
      rw [h64v, copyTest_toNat hkval hsub63 hspan']
      omega
    let e : State := CopyStepState nm mkEnv s src dst sub k
      ((B.drop k.toNat).take 32) ((B.drop (k.toNat + 32)).take 32) nm.head
    have he : e = CopyStepState nm mkEnv s src dst sub k
        ((B.drop k.toNat).take 32) ((B.drop (k.toNat + 32)).take 32) nm.head := rfl
    have hstep : step escapeCalls usDecFunction s = .jump e := by
      rw [he]
      exact stepBack s prev op _ k _ _ hpc hpre hinc hop hsrc hdst hsubc hkNlt
        (by rw [BitVec.signExtend_eq]) hr1 hr2 hl1 hl2 htest rfl
    refine ⟨e, c + 1, 1, by omega, ?_, by omega, ?_,
      fun k' => runFuel_jump_prefix hstep k'⟩
    · rw [he, CopyStepState_pc]
    · refine ⟨nm.head, .reg nm.knext, k + BitVec.ofInt 64 64, rfl, rfl, phiHead,
        ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [he]
        simp only [evalOperand, CopyStepState_env]
        exact envKnext s.env src dst k _ _ (BitVec.ofNat 64 sub)
      · exact copyNext_counter hkval
      · rw [he, CopyStepState_env, envSrc s.env src dst k _ _ (BitVec.ofNat 64 sub)]
        exact hsrc
      · rw [he, CopyStepState_env, envDst s.env src dst k _ _ (BitVec.ofNat 64 sub)]
        exact hdst
      · rw [he, CopyStepState_env, envSub s.env src dst k _ _ (BitVec.ofNat 64 sub)]
        exact hsubc
      · rw [he, CopyStepState_mem]
        exact readBytes_copy2Mem_src hwhole hdisj hl1 hl2 (by omega)
      · exact hBlen
      · rw [he, CopyStepState_mem, hkN]
        have hp : readBytes s.mem dst (64 * c) = some (B.take (64 * c)) := hprefix
        have hh := readBytes_copy2Mem_dst s.mem dst (64 * c) B _ _ hp rfl rfl
          (by rw [hBlen]; omega)
        rw [show 64 * c + 64 = 64 * (c + 1) from by omega] at hh
        exact hh
      · exact hdisj
      · exact hsub63
      · exact hgate
      · omega
      · omega
  exit_at_zero := by
    intro s c h
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hhi⟩ := h
    show decide (copyIterBound sub ≤ c) = true
    exact decide_eq_true (by omega)
  budget := by
    intro r s c h
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hlo, hhi⟩ := h
    exact ⟨hlo, hhi⟩

/-! ### The two instances -/

/-- **The copy after a position** (`while.body.i91`) is a `BoundLoop`.**  Its
budget is the residual's block count, which is a term of the caller's arguments:
the residual is `n - i` and the block count is at most `(n - i) / 64 + 1`, inside
`decodeIterCost`'s `n / 64 + 2`. -/
def copyBodyLoop (src dst sub : Nat) (B : List UInt8) : BoundLoop escapeCalls usDecFunction :=
  copyBoundLoop copyBodyNames udCopyBodyEnv src dst sub B copyBodyNames_head_phi
    (by intro env src' dst' k' bs1 bs2 subv; simp only [copyBodyNames, udCopyBodyEnv]; ud_lk)
    (by intro env src' dst' k' bs1 bs2 subv; simp only [copyBodyNames, udCopyBodyEnv]; ud_lk)
    (by intro env src' dst' k' bs1 bs2 subv; simp only [copyBodyNames, udCopyBodyEnv]; ud_lk)
    (by intro env src' dst' k' bs1 bs2 subv; simp only [copyBodyNames, udCopyBodyEnv]; ud_lk)
    (by intro env src' dst' k' bs1 bs2 subv; simp only [copyBodyNames, udCopyBodyEnv]; ud_lk)
    (by
      intro s prev op e k bs1 bs2 hpc hpre hinc hop hsrc hdst hsub hk63 hkw hr1 hr2
        hl1 hl2 htest he
      subst he
      exact udCopyBody_step s.env s prev op src dst k bs1 bs2 (BitVec.ofNat 64 sub)
        hpc hpre hinc hop hsrc hdst hsub hk63 hkw hr1 hr2 hl1 hl2
        (by simpa [copyTest] using htest))
    (by
      intro s prev op e k bs1 bs2 hpc hpre hinc hop hsrc hdst hsub hk63 hkw hr1 hr2
        hl1 hl2 htest he
      subst he
      exact udCopyBody_step_zero s.env s prev op src dst k bs1 bs2 (BitVec.ofNat 64 sub)
        hpc hpre hinc hop hsrc hdst hsub hk63 hkw hr1 hr2 hl1 hl2
        (by simpa [copyTest] using htest))

/-- **The copy after the walk** (`while.body.i`) is the same instance at its own
block.**  Its residual is `%sub38` and its bases are `%add.ptr36`/`%add.ptr37`;
the test's arithmetic, the two ranges and the destination prefix are the first
copy's, reused unchanged. -/
def copyBodyNLoop (src dst sub : Nat) (B : List UInt8) : BoundLoop escapeCalls usDecFunction :=
  copyBoundLoop copyBodyNNames udCopyBodyNEnv src dst sub B copyBodyNNames_head_phi
    (by intro env src' dst' k' bs1 bs2 subv; simp only [copyBodyNNames, udCopyBodyNEnv]; ud_lk)
    (by intro env src' dst' k' bs1 bs2 subv; simp only [copyBodyNNames, udCopyBodyNEnv]; ud_lk)
    (by intro env src' dst' k' bs1 bs2 subv; simp only [copyBodyNNames, udCopyBodyNEnv]; ud_lk)
    (by intro env src' dst' k' bs1 bs2 subv; simp only [copyBodyNNames, udCopyBodyNEnv]; ud_lk)
    (by intro env src' dst' k' bs1 bs2 subv; simp only [copyBodyNNames, udCopyBodyNEnv]; ud_lk)
    (by
      intro s prev op e k bs1 bs2 hpc hpre hinc hop hsrc hdst hsub hk63 hkw hr1 hr2
        hl1 hl2 htest he
      subst he
      exact udCopyBodyN_step s.env s prev op src dst k bs1 bs2 (BitVec.ofNat 64 sub)
        hpc hpre hinc hop hsrc hdst hsub hk63 hkw hr1 hr2 hl1 hl2
        (by simpa [copyTest] using htest))
    (by
      intro s prev op e k bs1 bs2 hpc hpre hinc hop hsrc hdst hsub hk63 hkw hr1 hr2
        hl1 hl2 htest he
      subst he
      exact udCopyBodyN_step_zero s.env s prev op src dst k bs1 bs2 (BitVec.ofNat 64 sub)
        hpc hpre hinc hop hsrc hdst hsub hk63 hkw hr1 hr2 hl1 hl2
        (by simpa [copyTest] using htest))


/-! ### The emitter's guard, read off the record's table clause

The escape reader (`if.end.i`) loads the byte after a backslash and then the
table's image of it, and its branch is a signed compare against `-1`.  The trace
already states that block's step (`udIfEndI_step`/`udIfEndI_step_zero`), but takes
the table read as a hypothesis of the post-store memory, because nothing carried
it.  The record's `pre` does: `readBytes mem tab 256 = some unescapeTable`, the
rule's own table.  The two facts below turn that clause into the read the block
makes and the branch the specification decides, so the iteration arm takes them
from the staging instead of assuming them.
-/

/-- The rule's table is two hundred and fifty-six entries, one per byte. -/
theorem unescapeTable_length : unescapeTable.length = 256 := by
  simp [unescapeTable, List.length_map]

/-- **The table read at one byte.**  A whole-table read gives the entry at a byte's
index, and the body loads that entry as one byte. -/
theorem tableByte {M : Mem} {tab : Nat} {b : UInt8}
    (htab : readBytes M tab 256 = some unescapeTable)
    (hb2 : b.toNat < unescapeTable.length) :
    readBytes M (tab + b.toNat) 1 =
      some (natToBytes (unescapeTable[b.toNat]'hb2).toNat 1) := by
  have hbyte : readByte M (tab + b.toNat) = some (unescapeTable[b.toNat]'hb2) := by
    have h := readByte_of_readBytes htab (k := b.toNat) hb2
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hb2, Option.getD_some] at h
    exact h
  have hone : natToBytes (unescapeTable[b.toNat]'hb2).toNat 1
      = [unescapeTable[b.toNat]'hb2] := by
    show UInt8.ofNat ((unescapeTable[b.toNat]'hb2).toNat % 256) ::
      natToBytes ((unescapeTable[b.toNat]'hb2).toNat / 256) 0 = [_]
    rw [Nat.mod_eq_of_lt (UInt8.toNat_lt _), UInt8.ofNat_toNat]
    rfl
  rw [hone]
  simp only [readBytes, hbyte]

/-- **The emitter's guard, from the record's table clause.**  The byte the body
loads out of `%tab` is the table's entry at `b`, and the body's signed compare
decides exactly the specification's "`b` begins a two-character escape".  These are
the two facts `if.end.i`'s step needs — its table read and its branch value — and
both come from the record's `pre` rather than from the caller's memory shape. -/
theorem emitterTest_of_table {M : Mem} {tab : Nat} (b : UInt8)
    (htab : readBytes M tab 256 = some unescapeTable) :
    ∃ t : BitVec 8, unescapeTable[b.toNat]? = some (UInt8.ofNat t.toNat) ∧
      readBytes M (tab + b.toNat) 1 = some (natToBytes t.toNat 1) ∧
      (evalICmp .sgt t (BitVec.ofInt 8 (-1)) = (1 : BitVec 1) ↔ simpleEscape b ≠ none) := by
  have hb2 : b.toNat < unescapeTable.length := by
    rw [unescapeTable_length]
    exact UInt8.toNat_lt b
  have htval : UInt8.ofNat
      (BitVec.ofNat 8 (unescapeTable[b.toNat]'hb2).toNat).toNat
      = unescapeTable[b.toNat]'hb2 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (UInt8.toNat_lt _), UInt8.ofNat_toNat]
  have htn : (BitVec.ofNat 8 (unescapeTable[b.toNat]'hb2).toNat).toNat
      = (unescapeTable[b.toNat]'hb2).toNat := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (UInt8.toNat_lt _)]
  refine ⟨BitVec.ofNat 8 (unescapeTable[b.toNat]'hb2).toNat, ?_, ?_, ?_⟩
  · rw [htval, List.getElem?_eq_getElem hb2]
  · rw [htn]
    exact tableByte htab hb2
  · exact unescapeTable_test b _ (List.getElem?_eq_getElem hb2)

/-! ### What the two loops contribute to the walk's fuel

The iteration arm adds the copies' fuel to `decodeIterCost (n)`, so the number it
adds must be inside that function of the arguments.  A copy's whole fuel is its
block count plus its exit iteration, and the block count is bounded by the
residual's sixty-fourth part however far the walk has advanced — the residual is
`n - i ≤ n`.
-/

/-- The residual's block count is inside the residual's sixty-fourth part. -/
theorem copyIterBound_le_div {sub n : Nat} (hn : sub ≤ n) :
    (sub - 128 + 63) / 64 ≤ n / 64 + 1 := by
  have hle : sub - 128 + 63 ≤ n + 63 := by omega
  have h1 : (sub - 128 + 63) / 64 ≤ (n + 63) / 64 := Nat.div_le_div_right hle
  have hq := Nat.div_add_mod n 64
  have hr := Nat.mod_lt n (by decide : 0 < 64)
  have hlt : n + 63 < (n / 64 + 2) * 64 := by omega
  have h2 : (n + 63) / 64 < n / 64 + 2 :=
    (Nat.div_lt_iff_lt_mul (by decide : 0 < 64)).2 hlt
  omega

/-- **A copy's fuel is a term of the caller's arguments, and it is inside
`decodeIterCost n`.**  The loop's whole fuel is `copyIterBound sub + 1` control
steps, and the residual is at most the body's length, so the number is a summand
of the iteration's cost — which is what lets the iteration arm add it to the walk's
budget without reading the run. -/
theorem copyLoopFuel_le_decodeIterCost {sub n : Nat} (hn : sub ≤ n) :
    copyIterBound sub + 1 ≤ decodeIterCost n := by
  have hsub := copyIterBound_le_div hn
  unfold decodeIterCost copyIterBound
  omega

/-- **The copy after a position, from its head.**  At the whole bound the head
reaches `us_run_long.exit99` within `copyIterBound sub + 1` control steps, leaving
the exit word, and a continuation that reads that word lifts to the head.  This is
`BoundLoop.run_at` at the instance — the shape the walk's iteration arm consumes
when it composes the copy's contribution. -/
theorem copyBodyLoop_run_at (src dst sub : Nat) (B : List UInt8) (s : State) (c : Nat)
    (hinv : CopyInv copyBodyNames src dst sub B (copyIterBound sub) c s) (k : Nat)
    {o : Outcome}
    (hcont : ∀ (e : State), e.pc = copyBodyNames.tail →
      CopyExitWord copyBodyNames src dst sub B e →
      runFuel escapeCalls k usDecFunction e = some o) :
    runFuel escapeCalls (copyIterBound sub + 1 + k) usDecFunction s = some o := by
  have h := (copyBodyLoop src dst sub B).run_at s c hinv k hcont
  simpa [copyBodyLoop, copyBoundLoop, Nat.mul_one] using h

/-- **The copy after the walk, from its head.**  The same statement at
`while.body.i`, whose exit is `us_run_long.exit`. -/
theorem copyBodyNLoop_run_at (src dst sub : Nat) (B : List UInt8) (s : State) (c : Nat)
    (hinv : CopyInv copyBodyNNames src dst sub B (copyIterBound sub) c s) (k : Nat)
    {o : Outcome}
    (hcont : ∀ (e : State), e.pc = copyBodyNNames.tail →
      CopyExitWord copyBodyNNames src dst sub B e →
      runFuel escapeCalls k usDecFunction e = some o) :
    runFuel escapeCalls (copyIterBound sub + 1 + k) usDecFunction s = some o := by
  have h := (copyBodyNLoop src dst sub B).run_at s c hinv k hcont
  simpa [copyBodyNLoop, copyBoundLoop, Nat.mul_one] using h

/-! ### Axiom footprints

Every theorem here is pinned where it is proved.  The two instances carry
`Classical.choice`, and it is one carrier: `BitVec.signExtend_eq`, the
sign-extension width equality the trace's block steps take as a hypothesis, which
is the same carrier `JsonEscapeDecodeRun`'s instance names.  Nothing else leaves
the development's ceiling.
-/
/-- info: 'LeanLLVM.Vellum.DecodeStaging' depends on axioms: [propext] -/
#guard_msgs in
#print axioms DecodeStaging
/-- info: 'LeanLLVM.Vellum.StagedDecodeInv.toDecodeInv' depends on axioms: [propext] -/
#guard_msgs in
#print axioms StagedDecodeInv.toDecodeInv
/-- info: 'LeanLLVM.Vellum.stagedLatchInv_latch' depends on axioms: [propext] -/
#guard_msgs in
#print axioms stagedLatchInv_latch
/-- info: 'LeanLLVM.Vellum.stagedLatchInv_decodeInv' depends on axioms: [propext] -/
#guard_msgs in
#print axioms stagedLatchInv_decodeInv
/-- info: 'LeanLLVM.Vellum.stagedDecodeInv_seed' depends on axioms: [propext] -/
#guard_msgs in
#print axioms stagedDecodeInv_seed
/-- info: 'LeanLLVM.Vellum.copyIterBound_mul_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms copyIterBound_mul_le
/-- info: 'LeanLLVM.Vellum.copyIterBound_advance' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms copyIterBound_advance
/-- info: 'LeanLLVM.Vellum.copyIterBound_exit' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms copyIterBound_exit
/-- info: 'LeanLLVM.Vellum.copyIterBound_step_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms copyIterBound_step_le
/-- info: 'LeanLLVM.Vellum.copySrc_read' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms copySrc_read
/-- info: 'LeanLLVM.Vellum.copySrc_read_mid' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms copySrc_read_mid
/-- info: 'LeanLLVM.Vellum.copyChunk_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms copyChunk_length
/-- info: 'LeanLLVM.Vellum.take_split_sixtyFour' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms take_split_sixtyFour
/-- info: 'LeanLLVM.Vellum.readBytes_copy2Mem_dst' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms readBytes_copy2Mem_dst
/-- info: 'LeanLLVM.Vellum.readBytes_copy2Mem_src' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms readBytes_copy2Mem_src
/-- info: 'LeanLLVM.Vellum.evalICmp_ugt_zero_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms evalICmp_ugt_zero_iff
/-- info: 'LeanLLVM.Vellum.copyTest_toNat' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms copyTest_toNat
/-- info: 'LeanLLVM.Vellum.copyNext_counter' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms copyNext_counter
/-- info: 'LeanLLVM.Vellum.copyK_sum' depends on axioms: [propext] -/
#guard_msgs in
#print axioms copyK_sum
/-- info: 'LeanLLVM.Vellum.copyBodyNames_head_phi' depends on axioms: [propext] -/
#guard_msgs in
#print axioms copyBodyNames_head_phi
/-- info: 'LeanLLVM.Vellum.copyBodyNNames_head_phi' depends on axioms: [propext] -/
#guard_msgs in
#print axioms copyBodyNNames_head_phi
/-- info: 'LeanLLVM.Vellum.copyBodyLoop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms copyBodyLoop
/-- info: 'LeanLLVM.Vellum.copyBodyNLoop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms copyBodyNLoop
/-- info: 'LeanLLVM.Vellum.copyIterBound_le_div' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms copyIterBound_le_div

/-- info: 'LeanLLVM.Vellum.copyLoopFuel_le_decodeIterCost' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms copyLoopFuel_le_decodeIterCost

/-- info: 'LeanLLVM.Vellum.copyBodyLoop_run_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms copyBodyLoop_run_at

/-- info: 'LeanLLVM.Vellum.copyBodyNLoop_run_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms copyBodyNLoop_run_at

/-- info: 'LeanLLVM.Vellum.unescapeTable_length' depends on axioms: [propext] -/
#guard_msgs in
#print axioms unescapeTable_length

/-- info: 'LeanLLVM.Vellum.tableByte' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms tableByte

/-- info: 'LeanLLVM.Vellum.emitterTest_of_table' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms emitterTest_of_table

/-- info: 'LeanLLVM.Vellum.CopyInv' does not depend on any axioms -/
#guard_msgs in
#print axioms CopyInv

/-- info: 'LeanLLVM.Vellum.CopyExitWord' does not depend on any axioms -/
#guard_msgs in
#print axioms CopyExitWord

/-- info: 'LeanLLVM.Vellum.CopyStepState' does not depend on any axioms -/
#guard_msgs in
#print axioms CopyStepState

end LeanLLVM.Vellum
