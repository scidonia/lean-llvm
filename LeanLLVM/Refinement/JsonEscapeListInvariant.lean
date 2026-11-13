/-
The escape position list's loop invariant, and the call site that resolves its
batch.

`escapeListFunction` is the pinned mask-driven list body: ten blocks and 149
instruction lines, with two backward edges — the `xl_lanes` set-bit loop
(`do.body.i`, five instruction lines) and the `xl_emit` batch loop
(`while.body.i.i`, twenty-five, inside the sixty-three-line `if.end.i4`).  The
record's claim is about a word the body builds (three classifier masks and a
two-word carry) and a stream it writes eight entries at a time, so the proof has
to carry a state through both loops.  That state is `ListLoopInv` below, and it
carries the three facts the loops must preserve:

* **the residual set-bit word** — after `used` positions have been emitted, the
  word's set lanes are exactly the positions not yet emitted;
* **the batch's eight-entry store at `xp + 4 * xn0`** — the `used` entries the
  run claims stand at the record's base, and the eight-entry reserve the batch
  touches past them is not part of the claim;
* **the running count** — `*xn` holds the caller's count plus `used`, which is
  the count the next batch reads back and adds to.

The batch's own claim is not re-derived here.  `@xl_batch` is resolved by
`escapeListCalls` through `envForUnit` at `Γ_xl_batch`, and the per-call
`xl_batch_satisfies` (in `JsonEscapeBatch`) is the hypothesis the loop
discharges: `xl_batch_callsatisfies` below turns it into the call-site claim,
and `xl_batch_call_eq` reads the exact count and memory the selection returns.
So a loop step needs no new semantics for the call, only the arithmetic of
adding the returned count and advancing by it.

**Where the proof stands.**  The two supporting folds are proved here: the
carry fold composes over a concatenation (`classCarryAt_append`), and the run
parity is a fold over the bytes (`classCarryAt_oddRun`, `parityAt_append`).
They are the two facts a bridge from the body's three mask words to the
specification's lane rule needs.  The doubling map's own account is proved in
`JsonEscapeListFixpoint`: `stepWord_specRunStarts` states that
`specRunStarts` is a fixed point of the map, and
`stepN_escapeSeed_specRunStarts` states that 32 iterations from the body's
boundary seed reach it.  What remains is the body-side trace, the 64-lane lane
rule and the batch loop's arithmetic, listed at the end of this file.  No
declaration here takes any of those as a hypothesis, so nothing in this module
claims the record's post of the body.
-/
import LeanLLVM.Refinement.JsonEscapeSpec
import LeanLLVM.Refinement.JsonEscapeBatch
import LeanLLVM.Refinement.JsonEscapeIntrinsics
import LeanLLVM.Refinement.BitLanes

namespace LeanLLVM.Refinement

open LeanLLVM
open LeanLLVM.JSON
open LeanLLVM.Refinement.JsonEscapeIR
open LeanLLVM.Refinement.JsonS1MasksIR
open LeanLLVM.Refinement.JsonScanSpec
open LeanLLVM.Refinement.JsonEscapeIntrinsics
open LeanLLVM.Refinement.BitLanes

/-! ### The carry fold composes

The classifier folds its two-field carry over a half-block; the kernel's
sixty-four-lane masks are the two halves' masks joined, the high half entered
with the carry the low half left.  That composition is what makes a lane above
the halfway point readable at the low half's fold, so it is stated once here. -/

/-- Taking `length l1 + j` lanes of a concatenation is the first list and `j`
lanes of the second. -/
theorem take_append_len (l1 l2 : List UInt8) (j : Nat) :
    (l1 ++ l2).take (l1.length + j) = l1 ++ l2.take j := by
  rw [List.take_append, List.take_of_length_le (by omega), Nat.add_sub_cancel_left]

/-- The carry fold at a lane of the second list, entered with the carry the
first list's fold left. -/
theorem classCarryAt_append (l1 l2 : List UInt8) (st : ClassState) (j : Nat) :
    classCarryAt (l1 ++ l2) st (l1.length + j) =
      classCarryAt l2 (classCarryAt l1 st l1.length) j := by
  unfold classCarryAt
  rw [take_append_len, List.foldl_append, List.take_length]

/-- At the boundary the fold is the first list's own fold. -/
theorem classCarryAt_append_len (l1 l2 : List UInt8) (st : ClassState) :
    classCarryAt (l1 ++ l2) st l1.length = classCarryAt l1 st l1.length := by
  unfold classCarryAt
  rw [List.take_left, List.take_length]

/-! ### The run parity is a fold over the bytes

`IsEscapeLane` reads the carry's `oddRun` at each lane, so a bridge from the
mask words to the position rule has to know that field as a function of the
bytes.  `parityAt` is that function: it toggles on a backslash and resets on
any other byte, which is `classStep`'s own rule for the field. -/

/-- The run parity on entry to lane `k`, from the incoming parity at lane zero. -/
def parityAt (bs : List UInt8) (odd0 : Bool) : Nat → Bool
  | 0 => odd0
  | k + 1 => (match bs[k]? with
      | some b => if IsBackslashB b then !parityAt bs odd0 k else false
      | none => parityAt bs odd0 k)

/-- The carry's run parity is `parityAt`. -/
theorem classCarryAt_oddRun (bs : List UInt8) (st : ClassState) (k : Nat) :
    (classCarryAt bs st k).oddRun = parityAt bs st.oddRun k := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [classCarryAt_succ]
      cases hb : bs[k]? with
      | none => simp [parityAt, hb, ih]
      | some b =>
          simp only [hb, parityAt]
          by_cases hbk : IsBackslashB b = true
          · simp [classStep, hbk, ih]
          · have hbf : IsBackslashB b = false := by cases h : IsBackslashB b <;> simp_all
            simp [classStep, hbf]

/-- The parity fold ignores bytes past the lane it reads. -/
theorem parityAt_append_of_le (l1 l2 : List UInt8) (odd0 : Bool) {k : Nat}
    (h : k ≤ l1.length) :
    parityAt (l1 ++ l2) odd0 k = parityAt l1 odd0 k := by
  induction k with
  | zero => rfl
  | succ k ih =>
      have hk : k < l1.length := by omega
      rw [parityAt, parityAt, List.getElem?_append_left hk, ih (by omega)]

/-- The parity fold composes over a concatenation. -/
theorem parityAt_append (l1 l2 : List UInt8) (odd0 : Bool) (j : Nat) :
    parityAt (l1 ++ l2) odd0 (l1.length + j) =
      parityAt l2 (parityAt l1 odd0 l1.length) j := by
  induction j with
  | zero =>
      rw [Nat.add_zero, parityAt_append_of_le l1 l2 odd0 (Nat.le_refl _)]
      rfl
  | succ j ih =>
      rw [show l1.length + (j + 1) = (l1.length + j) + 1 from by omega, parityAt, ih,
        parityAt, List.getElem?_append_right (by omega), Nat.add_sub_cancel_left]

/-! ### The specification's position word

The body's escape word is `(runstarts | ctl) & im`, where `runstarts` is the
set of backslashes entered with even run parity.  `specPositionWord` states that
word from the three mask words and the incoming parity alone, which is the form
the entry blocks build; a later bridge has to show it is the lane rule of
`escapePositionsFrom`.  This definition is not the bridge: it is only the word
the invariant's first conjunct mentions. -/

/-- The run parity over a word's lanes, from the incoming parity at lane zero. -/
def parityBit (bs : BitVec 64) (odd0 : Bool) : Nat → Bool
  | 0 => odd0
  | k + 1 => if bs.getLsbD k then !parityBit bs odd0 k else false

/-- The lanes entered with even run parity, from the backslash mask and the
incoming parity at lane zero. -/
def specRunStarts (bs : BitVec 64) (odd0 : Bool) : BitVec 64 :=
  ofLanes fun k => bs.getLsbD k.val && !(parityBit bs odd0 k.val)

/-- The escape word the emission's arithmetic forms, over the three masks. -/
def specPositionWord (bs ctl im : BitVec 64) (odd0 : Bool) : BitVec 64 :=
  (specRunStarts bs odd0 ||| ctl) &&& im

/-! ### The loop invariant

Stated at the head of the batch loop, after `used` positions have been emitted.
`position` is the block's position list (`escapePositionsFrom`'s value at the
body's block), so the block-relative positions are ordered and the store's
values are their document offsets. -/

/-- The batch loop's state: the residual set-bit word, the store the run has
made at the record's base, and the running count.

The three conjuncts are the three facts the two backward edges must preserve.
`used ≤ position.length` and `position.length ≤ 64` bound the count the batch
reads; the store clause covers exactly the `used` entries the run claims and
says nothing about the eight-entry reserve past them, which is the record's
extent exclusion rather than a frame. -/
def ListLoopInv (blk0 : BitVec 64) (xp xn : Nat) (xn0 used : Nat)
    (w : BitVec 64) (position : List Nat) (mem : Mem) : Prop :=
  -- (1) the residual set-bit word: its set lanes are the positions not yet emitted
  (∀ k, k < 64 → w.getLsbD k = decide (k ∈ position.drop used)) ∧
  -- (2) the batch's eight-entry store at `xp + 4 * xn0`: the claimed prefix, in order
  readBytes mem (xp + 4 * xn0) (4 * used) =
    some (positionsBytes 4 ((position.take used).map fun k => blockAddr blk0 + k)) ∧
  -- (3) the running count
  readBytes mem xn 8 = some (wordBytes 8 (xn0 + used)) ∧
  -- the count is a count
  used ≤ position.length ∧ position.length ≤ 64

/-! ### The batch call site

`escapeListCalls` resolves `@xl_batch` through `envForUnit` at `Γ_xl_batch`.
`xl_batch_satisfies` is the per-call hypothesis; the two lemmas below are its
call-site form, so a loop step reads the count and memory rather than a
`satisfies` statement. -/

/-- `@xl_batch` satisfies its record at the list's call site. -/
theorem xl_batch_callsatisfies :
    CallSatisfies (escapeListCalls Γ_xl_batch) Γ_xl_batch "xl_batch" := by
  have hbridge : CallSatisfies
      (envForUnit "xl_batch" Γ_xl_batch escapeCalls xlBatchFunction)
      Γ_xl_batch "xl_batch" :=
    satisfies_calls (sym := "xl_batch") xl_batch_satisfies
      (by decide : retsValued xlBatchFunction = true)
  intro args mem next hpre
  obtain ⟨r, hr, hpost, hnext⟩ := hbridge args mem next hpre
  exact ⟨r, by rw [escapeListCalls_xlBatch]; exact hr, hpost, hnext⟩

/-- The shape `Γ_xl_batch.post` admits: a value return at `i32`, with the
population count against eight and the batch's memory. -/
theorem xl_batch_post_unpack {args mem next out} (h : Γ_xl_batch.post args mem next out) :
    ∃ (esc : BitVec 64) (base : BitVec 32) (o : Nat) (c : BitVec 32) (m : Mem),
      args = [.int 64 esc, .int 32 base, .ptr o] ∧
      out = .ret (some (.int 32 c)) m ∧
      c = umin (BitVec.ofNat 32 (ctpop esc)) (BitVec.ofNat 32 8) ∧
      m = batchMem base esc o mem := by
  unfold Γ_xl_batch at h
  cases out with
  | ub => exact absurd h (by simp)
  | ret v m =>
      cases v with
      | none => simp at h
      | some v =>
          cases v with
          | float b =>
            simp at h
          | int w c =>
              by_cases hw : w = 32
              · subst hw
                simp only at h
                obtain ⟨esc, base, o, hargs, hc, hm⟩ := h
                exact ⟨esc, base, o, c, m, hargs, rfl, hc, hm⟩
              · simp [hw] at h
          | ptr a => simp at h
          | vec n w l => simp at h

/-- The count and the memory `@xl_batch` leaves, at an argument list its record
admits: the population count against eight, and the eight-entry batch written at
`o`. -/
theorem xl_batch_call_eq (esc : BitVec 64) (base : BitVec 32) (o : Nat)
    (mem : Mem) (next : Nat) :
    ∃ r, escapeListCalls Γ_xl_batch "xl_batch"
        [.int 64 esc, .int 32 base, .ptr o] mem next = some r ∧
      r.ret = .int 32 (umin (BitVec.ofNat 32 (ctpop esc)) (BitVec.ofNat 32 8)) ∧
      r.mem = batchMem base esc o mem := by
  obtain ⟨r, hcall, hpost, _⟩ := xl_batch_callsatisfies
    [.int 64 esc, .int 32 base, .ptr o] mem next ⟨esc, base, o, rfl⟩
  obtain ⟨esc', base', o', c, m, hargs, hout, hc, hm⟩ := xl_batch_post_unpack hpost
  simp only [List.cons.injEq, and_true] at hargs
  obtain ⟨h1, h2⟩ := hargs
  have hesc : esc = esc' := by injection h1
  have hbase : base = base' := by injection h2.1
  have ho : o = o' := by injection h2.2
  subst hesc; subst hbase; subst ho
  rw [Outcome.ret.injEq, Option.some.injEq] at hout
  obtain ⟨hret, hmem⟩ := hout
  refine ⟨r, hcall, ?_, ?_⟩
  · rw [hret, hc]
  · rw [hmem, hm]

/-! ### Axiom footprints -/

/-- info: 'LeanLLVM.Refinement.classCarryAt_append' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms classCarryAt_append

/-- info: 'LeanLLVM.Refinement.classCarryAt_append_len' depends on axioms: [propext] -/
#guard_msgs in
#print axioms classCarryAt_append_len

/-- info: 'LeanLLVM.Refinement.classCarryAt_oddRun' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms classCarryAt_oddRun

/-- info: 'LeanLLVM.Refinement.parityAt_append_of_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms parityAt_append_of_le

/-- info: 'LeanLLVM.Refinement.parityAt_append' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms parityAt_append

/-- info: 'LeanLLVM.Refinement.ListLoopInv' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ListLoopInv

/-- info: 'LeanLLVM.Refinement.xl_batch_callsatisfies' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms xl_batch_callsatisfies

/-- info: 'LeanLLVM.Refinement.xl_batch_post_unpack' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms xl_batch_post_unpack

/-- info: 'LeanLLVM.Refinement.xl_batch_call_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms xl_batch_call_eq

/-- info: 'LeanLLVM.Refinement.parityBit' depends on axioms: [propext] -/
#guard_msgs in
#print axioms parityBit

/-- info: 'LeanLLVM.Refinement.specRunStarts' depends on axioms: [propext] -/
#guard_msgs in
#print axioms specRunStarts

/-- info: 'LeanLLVM.Refinement.specPositionWord' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms specPositionWord


/-! ### The remaining bridge

The doubling map's two halves are proved in `JsonEscapeListFixpoint`; what is
still owed is the body-side work that consumes them, and none of it is assumed
here:

* The entry blocks and `do.body.i` build `%and31 = (e.2 | %ctl) & %im`, where
  `e.2` is 32 iterations of `stepWord` from the boundary seed.  The trace that
  reads `runFuel` through `entry`, `if.then.i`, `if.end.i`, `do.body.i` and
  `xl_lanes.exit` and lands on `escapeSeed = specRunStarts bs (opened && prevs)`
  is not in this module.
* The lane rule: `setLanes (specPositionWord bs ctl im odd0)` is
  `escapePositionsFrom (block64 lo hi) st` when the three mask words are the
  block's, which needs `classCarryAt_append`, `classCarryAt_oddRun` and
  `parityAt_append` per half plus `isEscapeLane_eq_escapeWord`.  The folds are
  here; the per-half assembly is not.
* The batch store: the first `min (ctpop esc) 8` entries the batch writes are
  `base + (setLanes esc)[i]`, and `clearStep^8` drops exactly those lanes, so a
  loop step may replace the residual word by the cleared one and advance the
  count by the returned minimum.
* `ListLoopInv` preservation through the two backward edges, and the post
  assembly from the invariant at the exit.

Nothing in this module assumes any of these.  `ListLoopInv`, the two folds and
the call-site lemmas are independent of them, and they are what a proof of
`escape_positions_satisfies` consumes next. -/

end LeanLLVM.Refinement
