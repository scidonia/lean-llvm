/-
The B3 kernel's step corpus.

`JsonEntryIR` pins the three emitted bodies in one text; `JsonEntrySteps` holds
POS8's execution and `JsonB8Steps` B8's.  This module holds B3's, and the
statement `entry_b3_refines` the block layer asks for.

## What is B8's and what is B3's

B3's block loop, the eight-lane slot machinery of `b8Lanes`, the `cttz`/`ctpop`
lemmas, the state and frame vocabulary (`B8Ctx`, `B8Frame`), and the stream
identities (`b8Stream`, `pos8Cursor`) are B8's and are used here unchanged:
none of them mentions a function's text.  What B3 adds is three fixed slots and
a second group of four above three lanes: its block has two early-exit tests
into the join -- a word of at most three lanes returns after the first group,
one of at most seven after the second -- where B8 has one, and its scalar tail
is a counted loop rather than the measured build's partial unroll.

The written lanes of a block are therefore `b3Len w` -- seven for a non-zero
word of at most seven set lanes, the population count above that -- and the
tail starts at lane seven.

The tail's proof is an induction over the remaining count, not over unrolled
groups: the loop's exit test compares its running cursor with `%10`, which is
`ctpop (clearLow w 7) + 7` -- the block's population count on the entered path
-- so one iteration writes one lane and the trip count is the remaining count.
-/
import LeanLLVM.Refinement.JsonB8Steps

namespace LeanLLVM.Refinement.JsonB3Steps

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

/-- Resolve a lookup: reduce a concrete environment, or take the caller's
hypothesis.  `ent_auto`'s peeling rewrite is exponential on the long environment
a second group builds, so the concrete case is left to `simp`. -/
macro "b3_lk" : tactic =>
  `(tactic| first | assumption | rfl | (simp [lookupName]; done))

open LeanLLVM
open LeanLLVM.Refinement.JsonEntryIR
open LeanLLVM.Refinement.JsonScanSpec
open LeanLLVM.Refinement.BitLanes
open LeanLLVM.Refinement.JsonEntrySteps
open LeanLLVM.Refinement.JsonB8Steps

/-! ### The written lanes of one block -/

/-- The lanes a B3 block writes: none for a zero word, three for a word of at
most three set lanes, seven up to seven, and the population count above that. -/
def b3Len (w : BitVec 64) : Nat :=
  if ctpop w = 0 then 0 else if ctpop w ≤ 3 then 3 else if ctpop w ≤ 7 then 7 else ctpop w

theorem b3Len_zero : b3Len 0 = 0 := by
  unfold b3Len
  rw [ctpop_zero64]
  rfl

theorem b3Len_pos {w : BitVec 64} (hw : w ≠ 0) : 1 ≤ b3Len w := by
  have hp := ctpop_pos_of_ne hw
  by_cases h0 : ctpop w = 0
  · exfalso; omega
  · by_cases h3 : ctpop w ≤ 3
    · simp [b3Len, h0, h3]
    · by_cases h7 : ctpop w ≤ 7
      · simp [b3Len, h0, h3, h7]
      · simp [b3Len, h0, h3, h7] <;> omega

/-- A non-zero block writes at most three lanes past its count. -/
theorem b3Len_le {w : BitVec 64} (hw : w ≠ 0) : b3Len w ≤ ctpop w + 3 := by
  by_cases h0 : ctpop w = 0
  · simp [b3Len, h0]
  · by_cases h3 : ctpop w ≤ 3
    · simp [b3Len, h0, h3] <;> omega
    · by_cases h7 : ctpop w ≤ 7
      · simp [b3Len, h0, h3, h7] <;> omega
      · simp [b3Len, h0, h3, h7]

/-- Every set lane of the word is inside the block's written lanes. -/
theorem ctpop_le_b3Len (w : BitVec 64) : ctpop w ≤ b3Len w := by
  by_cases h0 : ctpop w = 0
  · simp [b3Len, h0]
  · by_cases h3 : ctpop w ≤ 3
    · simp [b3Len, h0, h3]
    · by_cases h7 : ctpop w ≤ 7
      · simp [b3Len, h0, h3, h7] <;> omega
      · simp [b3Len, h0, h3, h7]

/-- One block's stores over the stream: nothing for a zero word, otherwise the
seven fixed slots and, above seven lanes, the tail's own. -/
def b3BlockStore (o : Nat) (w : BitVec 64) (base k : Nat) (mem : Mem) : Mem :=
  if w = 0 then mem else b8Lanes o w base k 0 (b3Len w) mem

theorem b3BlockStore_zero (o : Nat) (base k : Nat) (mem : Mem) :
    b3BlockStore o 0 base k mem = mem := by
  unfold b3BlockStore
  simp

theorem b3BlockStore_of_ne (o : Nat) (w : BitVec 64) (base k : Nat) (mem : Mem) (h : w ≠ 0) :
    b3BlockStore o w base k mem = b8Lanes o w base k 0 (b3Len w) mem := by
  unfold b3BlockStore
  split
  · exact absurd ‹w = 0› h
  · rfl

/-- The stream's blocks, each written at its own base and cursor. -/
def b3MemFold (o : Nat) : Nat → Nat → List (BitVec 64) → Mem → Mem
  | _, _, [], mem => mem
  | base, k, w :: ws, mem =>
      b3MemFold o (base + 64) (k + ctpop w) ws (b3BlockStore o w base k mem)

theorem b3MemFold_append (o base k : Nat) (a b : List (BitVec 64)) (mem : Mem) :
    b3MemFold o base k (a ++ b) mem =
      b3MemFold o (base + 64 * a.length) (pos8Cursor a k) b (b3MemFold o base k a mem) := by
  induction a generalizing base k mem with
  | nil =>
      show b3MemFold o base k b mem =
        b3MemFold o (base + 64 * ([] : List (BitVec 64)).length) (pos8Cursor [] k) b mem
      rw [pos8Cursor]
      rfl
  | cons w ws ih =>
      show b3MemFold o (base + 64) (k + ctpop w) (ws ++ b) (b3BlockStore o w base k mem) =
        b3MemFold o (base + 64 * (ws.length + 1)) (pos8Cursor ws (k + ctpop w)) b
          (b3MemFold o (base + 64) (k + ctpop w) ws (b3BlockStore o w base k mem))
      rw [ih (base + 64) (k + ctpop w) (b3BlockStore o w base k mem)]
      rw [show base + 64 * (ws.length + 1) = (base + 64) + 64 * ws.length from by omega]

/-- One block's store leaves every read outside its own lanes alone. -/
theorem b3BlockStore_frame (o : Nat) (w : BitVec 64) (base k : Nat) (mem : Mem) (p n : Nat)
    (hdisj : p + n ≤ o + 4 * k ∨ o + 4 * (k + b3Len w) ≤ p) :
    readBytes (b3BlockStore o w base k mem) p n = readBytes mem p n := by
  unfold b3BlockStore
  split
  · rfl
  · exact b8Lanes_frame o w base k 0 mem (b3Len w) p n (by
      rcases hdisj with h | h
      · left; omega
      · right; omega)

/-- The fold of a block stream leaves every read outside its span alone. -/
theorem b3MemFold_frame (o base k : Nat) (ent : List (BitVec 64)) (mem : Mem) (p n : Nat)
    (hdisj : p + n ≤ o + 4 * k ∨ o + 4 * (pos8Cursor ent k + 3) ≤ p) :
    readBytes (b3MemFold o base k ent mem) p n = readBytes mem p n := by
  induction ent generalizing base k mem with
  | nil => rfl
  | cons w ws ih =>
      by_cases hw : w = 0
      · subst hw
        rw [show b3MemFold o base k ((0 : BitVec 64) :: ws) mem
            = b3MemFold o (base + 64) k ws mem from by
          show b3MemFold o (base + 64) (k + ctpop 0) ws (b3BlockStore o 0 base k mem)
            = b3MemFold o (base + 64) k ws mem
          rw [b3BlockStore_zero, ctpop_zero64]
          rfl]
        refine ih (base + 64) k mem ?_
        have hcur : pos8Cursor ((0 : BitVec 64) :: ws) k = pos8Cursor ws k := by
          show pos8Cursor ws (k + ctpop 0) = pos8Cursor ws k
          rw [ctpop_zero64]
          rfl
        rw [hcur] at hdisj
        exact hdisj
      · rw [show b3MemFold o base k (w :: ws) mem
            = b3MemFold o (base + 64) (k + ctpop w) ws (b3BlockStore o w base k mem) from rfl]
        have h1 : readBytes (b3MemFold o (base + 64) (k + ctpop w) ws
            (b3BlockStore o w base k mem)) p n = readBytes (b3BlockStore o w base k mem) p n := by
          refine ih (base + 64) (k + ctpop w) (b3BlockStore o w base k mem) ?_
          rcases hdisj with h | h
          · left; omega
          · exact Or.inr h
        rw [h1]
        refine b3BlockStore_frame o w base k mem p n ?_
        rcases hdisj with h | h
        · exact Or.inl h
        · refine Or.inr ?_
          have h2 : k + b3Len w ≤ pos8Cursor ws (k + ctpop w) + 3 := by
            have hsc : b3Len w ≤ ctpop w + 3 := b3Len_le hw
            have hcur : k + ctpop w ≤ pos8Cursor ws (k + ctpop w) := pos8Cursor_self_le ws _
            omega
          calc o + 4 * (k + b3Len w)
              ≤ o + 4 * (pos8Cursor ws (k + ctpop w) + 3) := by
                have hm := Nat.mul_le_mul_left 4 h2
                omega
            _ ≤ p := h

/-! ### Reading a block's first lanes back -/

/-- The first `n` lanes of a lane fold, for `n` inside the fold's length. -/
theorem b8Lanes_read_first (o : Nat) (w : BitVec 64) (base k : Nat) (mem : Mem) :
    ∀ (len n : Nat), n ≤ len →
      readLanes32 (b8Lanes o w base k 0 len mem) (o + 4 * k) n
        = some ((List.range n).map (fun t => (slotVal base w t).toNat)) := by
  intro len n
  induction n with
  | zero => intro _; rfl
  | succ m ih =>
      intro hmn
      have hm : m ≤ len := by omega
      have h1 : readLanes32 (b8Lanes o w base k 0 len mem) (o + 4 * k) m
          = some ((List.range m).map (fun t => (slotVal base w t).toNat)) := ih hm
      have h2 : readLanes32 (b8Lanes o w base k 0 len mem) (o + 4 * k + 4 * m) 1
          = some [(slotVal base w m).toNat] := by
        simp only [readLanes32]
        rw [b8Lanes_lane0 o w base k mem len m (by omega)]
        simp only [Option.bind_some, Option.map_some]
        rw [bytesToNat_slot _ (slotVal base w m).isLt]
      rw [readLanes32_add (b8Lanes o w base k 0 len mem) m (o + 4 * k)
        ((List.range m).map (fun t => (slotVal base w t).toNat)) 1
        [(slotVal base w m).toNat] h1 h2]
      rw [List.range_succ, List.map_append, List.map_cons, List.map_nil]

/-- A non-zero block's first `ctpop` lanes are the model's positions for it. -/
theorem b3Lanes_read_ctpop (o : Nat) (w : BitVec 64) (base k : Nat) (mem : Mem)
    (hb : base % 64 = 0) (hcap : base + 64 < 2 ^ 32) :
    readLanes32 (b8Lanes o w base k 0 (b3Len w) mem) (o + 4 * k) (ctpop w)
      = some (positionsOf w base) := by
  rw [b8Lanes_read_first o w base k mem (b3Len w) (ctpop w) (ctpop_le_b3Len w)]
  exact congrArg some (b8WordPositions w base hb hcap)

/-- The fold's own lanes, read from the start cursor, are the model's stream. -/
theorem b3MemFold_read (o base k : Nat) (ent : List (BitVec 64)) (mem : Mem)
    (hb : base % 64 = 0) (hcap : base + 64 * ent.length < 2 ^ 32) :
    readLanes32 (b3MemFold o base k ent mem) (o + 4 * k) ((ent.map ctpop).sum)
      = some (b8Stream ent base) := by
  induction ent generalizing base k mem with
  | nil => rfl
  | cons w ws ih =>
      by_cases hw : w = 0
      · subst hw
        rw [show b3MemFold o base k ((0 : BitVec 64) :: ws) mem
            = b3MemFold o (base + 64) k ws mem from by
          show b3MemFold o (base + 64) (k + ctpop 0) ws (b3BlockStore o 0 base k mem)
            = b3MemFold o (base + 64) k ws mem
          rw [b3BlockStore_zero, ctpop_zero64]
          rfl]
        rw [show (((0 : BitVec 64) :: ws).map ctpop).sum = (ws.map ctpop).sum from by
          rw [List.map_cons, ctpop_zero64, List.sum_cons, Nat.zero_add]]
        rw [show b8Stream ((0 : BitVec 64) :: ws) base = b8Stream ws (base + 64) from by
          show positionsOf 0 base ++ b8Stream ws (base + 64) = _
          rw [show positionsOf (0 : BitVec 64) base = [] from by
            show (setLanes (0 : BitVec 64)).map (fun k => base + k) = []
            rw [setLanes_zero]; rfl]
          rfl]
        refine ih (base + 64) k mem ?_ ?_
        · rw [Nat.add_mod, show (64 : Nat) % 64 = 0 from by decide, hb, Nat.zero_add,
            Nat.zero_mod]
        · rw [List.length_cons, Nat.mul_add, Nat.mul_one] at hcap; omega
      · have hcd : ((w :: ws).map ctpop).sum = ctpop w + (ws.map ctpop).sum := by
          rw [List.map_cons, List.sum_cons]
        rw [hcd]
        have hfold : b3MemFold o base k (w :: ws) mem
            = b3MemFold o (base + 64) (k + ctpop w) ws (b8Lanes o w base k 0 (b3Len w) mem) := by
          show b3MemFold o (base + 64) (k + ctpop w) ws (b3BlockStore o w base k mem) = _
          rw [b3BlockStore_of_ne o w base k mem hw]
        rw [hfold]
        have hbelow : readLanes32 (b3MemFold o (base + 64) (k + ctpop w) ws
              (b8Lanes o w base k 0 (b3Len w) mem)) (o + 4 * k) (ctpop w)
            = some (positionsOf w base) := by
          have hcongr := readLanes32_congr
            (b8Lanes o w base k 0 (b3Len w) mem)
            (b3MemFold o (base + 64) (k + ctpop w) ws (b8Lanes o w base k 0 (b3Len w) mem))
            (o + 4 * k) (ctpop w) (fun j hj => by
              exact b3MemFold_frame o (base + 64) (k + ctpop w) ws
                (b8Lanes o w base k 0 (b3Len w) mem) (o + 4 * k + 4 * j) 4
                (Or.inl (by omega)))
          rw [hcongr]
          exact b3Lanes_read_ctpop o w base k mem hb (by rw [List.length_cons] at hcap; omega)
        have habove : readLanes32 (b3MemFold o (base + 64) (k + ctpop w) ws
              (b8Lanes o w base k 0 (b3Len w) mem)) (o + 4 * k + 4 * ctpop w)
              ((ws.map ctpop).sum)
            = some (b8Stream ws (base + 64)) := by
          rw [show o + 4 * k + 4 * ctpop w = o + 4 * (k + ctpop w) from by omega]
          refine ih (base + 64) (k + ctpop w) (b8Lanes o w base k 0 (b3Len w) mem) ?_ ?_
          · rw [Nat.add_mod, show (64 : Nat) % 64 = 0 from by decide, hb, Nat.zero_add,
              Nat.zero_mod]
          · rw [List.length_cons, Nat.mul_add, Nat.mul_one] at hcap; omega
        have hadd := readLanes32_add
          (b3MemFold o (base + 64) (k + ctpop w) ws (b8Lanes o w base k 0 (b3Len w) mem))
          (ctpop w) (o + 4 * k) (positionsOf w base) ((ws.map ctpop).sum)
          (b8Stream ws (base + 64)) hbelow habove
        rw [hadd]
        rfl

/-! ### The body's blocks, by name -/

theorem findBlock_b3Kernel :
    entryB3Function.findBlock "if.end" = some b3Kernel := by
  simp [entryB3Function, b3Entry, b3LoopExit, b3Body, b3Kernel, b3Kernel2,
    b3TailGuard, b3TailPreheader, b3TailLoop, b3Join, b3Advance,
    Function.findBlock, findBlockList]

theorem findBlock_b3Kernel2 :
    entryB3Function.findBlock "if.end14.i" = some b3Kernel2 := by
  simp [entryB3Function, b3Entry, b3LoopExit, b3Body, b3Kernel, b3Kernel2,
    b3TailGuard, b3TailPreheader, b3TailLoop, b3Join, b3Advance,
    Function.findBlock, findBlockList]

theorem findBlock_b3TailGuard :
    entryB3Function.findBlock "if.end38.i" = some b3TailGuard := by
  simp [entryB3Function, b3Entry, b3LoopExit, b3Body, b3Kernel, b3Kernel2,
    b3TailGuard, b3TailPreheader, b3TailLoop, b3Join, b3Advance,
    Function.findBlock, findBlockList]

theorem findBlock_b3TailPreheader :
    entryB3Function.findBlock "while.body.preheader.i" = some b3TailPreheader := by
  simp [entryB3Function, b3Entry, b3LoopExit, b3Body, b3Kernel, b3Kernel2,
    b3TailGuard, b3TailPreheader, b3TailLoop, b3Join, b3Advance,
    Function.findBlock, findBlockList]

theorem findBlock_b3TailLoop :
    entryB3Function.findBlock "while.body.i" = some b3TailLoop := by
  simp [entryB3Function, b3Entry, b3LoopExit, b3Body, b3Kernel, b3Kernel2,
    b3TailGuard, b3TailPreheader, b3TailLoop, b3Join, b3Advance,
    Function.findBlock, findBlockList]

theorem findBlock_b3Join :
    entryB3Function.findBlock "s1f_ke_b3.exit" = some b3Join := by
  simp [entryB3Function, b3Entry, b3LoopExit, b3Body, b3Kernel, b3Kernel2,
    b3TailGuard, b3TailPreheader, b3TailLoop, b3Join, b3Advance,
    Function.findBlock, findBlockList]

theorem findBlock_b3Body :
    entryB3Function.findBlock "for.body" = some b3Body := by
  simp [entryB3Function, b3Entry, b3LoopExit, b3Body, b3Kernel, b3Kernel2,
    b3TailGuard, b3TailPreheader, b3TailLoop, b3Join, b3Advance,
    Function.findBlock, findBlockList]

theorem findBlock_b3Advance :
    entryB3Function.findBlock "cleanup" = some b3Advance := by
  simp [entryB3Function, b3Entry, b3LoopExit, b3Body, b3Kernel, b3Kernel2,
    b3TailGuard, b3TailPreheader, b3TailLoop, b3Join, b3Advance,
    Function.findBlock, findBlockList]

theorem findBlock_b3Entry :
    entryB3Function.findBlock "entry" = some b3Entry := by
  simp [entryB3Function, b3Entry, b3LoopExit, b3Body, b3Kernel, b3Kernel2,
    b3TailGuard, b3TailPreheader, b3TailLoop, b3Join, b3Advance,
    Function.findBlock, findBlockList]

theorem findBlock_b3Exit :
    entryB3Function.findBlock "for.cond.cleanup" = some b3LoopExit := by
  simp [entryB3Function, b3Entry, b3LoopExit, b3Body, b3Kernel, b3Kernel2,
    b3TailGuard, b3TailPreheader, b3TailLoop, b3Join, b3Advance,
    Function.findBlock, findBlockList]

theorem b3_step_of (s : State) (name : String) (b : Block) (s' : State)
    (hpc : s.pc = name) (hfind : entryB3Function.findBlock name = some b)
    (hbody : denoteCode entryCalls b.instrs s = some s') :
    step entryCalls entryB3Function s = execTerm s' b.term := by
  simp [step, hpc, hfind, hbody]

/-! ### The `if.end` block: three slots and the first branch -/

theorem b3Kernel_run (env : Env) (s : State) (w : BitVec 64) (i blk0 k o : Nat)
    (hi : lookupName env "%i.010" = some (.int 64 (BitVec.ofNat 64 i)))
    (hbk : lookupName env "%blk0" = some (.int 64 (BitVec.ofNat 64 blk0)))
    (hout : lookupName env "%out" = some (.ptr o))
    (hk : lookupName env "%k.addr.011" = some (.int 64 (BitVec.ofNat 64 k)))
    (h0 : lookupName env "%0" = some (.int 64 w))
    (hk63 : k + 64 ≤ 2 ^ 63)
    (hblk : posBase blk0 i + 64 ≤ 2 ^ 32)
    (hconv : BitVec.ofNat 32 ((BitVec.ofNat 64 i + BitVec.ofNat 64 blk0).toNat % 2 ^ 32) <<< 6
              = BitVec.ofNat 32 (posBase blk0 i)) :
    ∃ env', denoteCode entryCalls b3Kernel.instrs (withEnv env s)
        = some (withEnv env' { s with mem := b8Lanes o w (posBase blk0 i) k 0 3 s.mem }) ∧
      lookupName env' "%1" = some (.int 64 (BitVec.ofNat 64 (ctpop w))) ∧
      lookupName env' "%and6.i" = some (.int 64 (clearLow w 2)) ∧
      lookupName env' "%conv" = some (.int 32 (BitVec.ofNat 32 (posBase blk0 i))) ∧
      lookupName env' "%add.ptr" = some (.ptr (o + 4 * k)) ∧
      lookupName env' "%cmp.i"
        = some (.int 1 (BitVec.ofBool (BitVec.ult (BitVec.ofNat 64 (ctpop w)) (BitVec.ofInt 64 4)))) := by
  refine ⟨?env', ?hrun, ?h1', ?hand', ?hconv', ?hptr', ?hcmp⟩
  case hrun =>
    simp only [b3Kernel, reg, lit]
    ent_step (step_add_reg _ _ "%add" "%i.010" "%blk0" 64 (BitVec.ofNat 64 i) (BitVec.ofNat 64 blk0) (by ent_auto) (by ent_auto))
    ent_step (step_trunc _ _ "%add.tr" "%add" 64 32 (BitVec.ofNat 64 i + BitVec.ofNat 64 blk0) (by ent_auto))
    ent_step (step_shl_imm _ _ "%conv" "%add.tr" 32 (BitVec.ofNat 32 ((BitVec.ofNat 64 i + BitVec.ofNat 64 blk0).toNat % 2 ^ 32)) (BitVec.ofInt 32 6) (by ent_auto))
    rw [show (BitVec.ofInt 32 6).toNat = 6 from by decide, hconv]
    ent_step (step_gep64 _ _ "%add.ptr" "%out" "%k.addr.011" (.int 32) o (BitVec.ofNat 64 k) (by ent_auto) (by ent_auto) (by rw [toNat_ofNat64 k (by omega)]; omega))
    rw [show o + (BitVec.ofNat 64 k).toNat * (Ty.int 32).sizeBytes = o + 4 * k from by
      rw [toNat_ofNat64 k (by omega), show (Ty.int 32).sizeBytes = 4 from rfl]; omega]
    ent_step (step_call_ctpop64 _ _ "%1" "%0" w (by ent_auto))
    -- slot 0
    ent_step (b8_step_call_cttz _ _ "%2" "%0" w (BitVec.ofInt 1 (-1)) (by ent_auto))
    ent_step (step_trunc _ _ "%cast1.i" "%2" 64 32 (BitVec.ofNat 64 (cttz w)) (by ent_auto))
    rw [trunc_cttz w]
    ent_step (b8_step_or_reg _ _ "%add.i" "%conv" "%cast1.i" 32 (BitVec.ofNat 32 (posBase blk0 i)) (BitVec.ofNat 32 (cttz w)) (by ent_auto) (by ent_auto))
    ent_step (b8_step_store32 _ _ "%add.i" "%add.ptr" (slotVal (posBase blk0 i) w 0) (o + 4 * k + 4 * 0) (by ent_auto) (by ent_auto))
    -- slot 1
    ent_step (step_add_imm _ _ "%sub.i" "%0" 64 (w) (BitVec.ofInt 64 (-1)) (by ent_auto))
    ent_step (b8_step_and_reg _ _ "%and.i" "%sub.i" "%0" 64 (w + (-1)) (w) (by ent_auto) (by ent_auto))
    rw [show (w + (-1)) &&& (w) = clearLow w 1 from rfl]
    ent_step (b8_step_call_cttz _ _ "%3" "%and.i" (clearLow w 1) (BitVec.ofInt 1 (-1)) (by ent_auto))
    ent_step (step_trunc _ _ "%cast2.i" "%3" 64 32 (BitVec.ofNat 64 (cttz (clearLow w 1))) (by ent_auto))
    rw [trunc_cttz _]
    ent_step (b8_step_or_reg _ _ "%add3.i" "%conv" "%cast2.i" 32 (BitVec.ofNat 32 (posBase blk0 i)) (BitVec.ofNat 32 (cttz (clearLow w 1))) (by ent_auto) (by ent_auto))
    ent_step (b8_step_gep_imm _ _ "%arrayidx4.i" "%add.ptr" (.int 8) (o + 4 * k) (BitVec.ofInt 64 4) (by ent_auto) (by decide))
    rw [show (o + 4 * k) + (BitVec.ofInt 64 4).toNat * (Ty.int 8).sizeBytes = o + 4 * k + 4 * (0 + 1) from by
      simp [show (BitVec.ofInt 64 4).toNat = 4 from by decide,
        show (Ty.int 8).sizeBytes = 1 from rfl]]
    ent_step (b8_step_store32 _ _ "%add3.i" "%arrayidx4.i" (slotVal (posBase blk0 i) w 1) (o + 4 * k + 4 * (0 + 1)) (by ent_auto) (by ent_auto))
    -- slot 2
    ent_step (step_add_imm _ _ "%sub5.i" "%and.i" 64 (clearLow w 1) (BitVec.ofInt 64 (-1)) (by ent_auto))
    ent_step (b8_step_and_reg _ _ "%and6.i" "%sub5.i" "%and.i" 64 (clearLow w 1 + (-1)) (clearLow w 1) (by ent_auto) (by ent_auto))
    rw [show (clearLow w 1 + (-1)) &&& (clearLow w 1) = clearLow w 2 from rfl]
    ent_step (b8_step_call_cttz _ _ "%4" "%and6.i" (clearLow w 2) (BitVec.ofInt 1 (-1)) (by ent_auto))
    ent_step (step_trunc _ _ "%cast7.i" "%4" 64 32 (BitVec.ofNat 64 (cttz (clearLow w 2))) (by ent_auto))
    rw [trunc_cttz _]
    ent_step (b8_step_or_reg _ _ "%add8.i" "%conv" "%cast7.i" 32 (BitVec.ofNat 32 (posBase blk0 i)) (BitVec.ofNat 32 (cttz (clearLow w 2))) (by ent_auto) (by ent_auto))
    ent_step (b8_step_gep_imm _ _ "%arrayidx9.i" "%add.ptr" (.int 8) (o + 4 * k) (BitVec.ofInt 64 8) (by ent_auto) (by decide))
    rw [show (o + 4 * k) + (BitVec.ofInt 64 8).toNat * (Ty.int 8).sizeBytes = o + 4 * k + 4 * (0 + 2) from by
      simp [show (BitVec.ofInt 64 8).toNat = 8 from by decide,
        show (Ty.int 8).sizeBytes = 1 from rfl]]
    ent_step (b8_step_store32 _ _ "%add8.i" "%arrayidx9.i" (slotVal (posBase blk0 i) w 2) (o + 4 * k + 4 * (0 + 2)) (by ent_auto) (by ent_auto))
    -- the test the block branches on
    ent_step (b8_step_icmp_ult_imm _ _ "%cmp.i" "%1" 64 (BitVec.ofNat 64 (ctpop w)) (BitVec.ofInt 64 4) (by ent_auto))
    simp only [denoteCode, denoteRun, State.bindAll, Option.bind]
    rfl
  case h1' => simp [lookupName]
  case hand' => simp [lookupName]
  case hconv' => simp [lookupName]
  case hptr' => simp [lookupName]
  case hcmp => simp [lookupName]

/-! ### The second group of four slots -/

theorem b3Kernel2_run (env : Env) (s : State) (w : BitVec 64) (i blk0 k o : Nat)
    (hconv : lookupName env "%conv" = some (.int 32 (BitVec.ofNat 32 (posBase blk0 i))))
    (hptr : lookupName env "%add.ptr" = some (.ptr (o + 4 * k)))
    (h1 : lookupName env "%1" = some (.int 64 (BitVec.ofNat 64 (ctpop w))))
    (hand6 : lookupName env "%and6.i" = some (.int 64 (clearLow w 2)))
    (hmem : s.mem = b8Lanes o w (posBase blk0 i) k 0 3 (b8Lanes o w (posBase blk0 i) k 0 3 s.mem) ∨
            True) :
    ∃ env', denoteCode entryCalls b3Kernel2.instrs (withEnv env s)
        = some (withEnv env' { s with mem := b8Lanes o w (posBase blk0 i) k 3 4 s.mem }) ∧
      lookupName env' "%and29.i" = some (.int 64 (clearLow w 6)) ∧
      lookupName env' "%cmp35.i"
        = some (.int 1 (BitVec.ofBool (BitVec.ult (BitVec.ofNat 64 (ctpop w)) (BitVec.ofInt 64 8)))) := by
  refine ⟨?env', ?hrun, ?hand', ?hcmp⟩
  case hrun =>
    simp only [b3Kernel2, reg, lit]
    -- slot 3
    ent_step (step_add_imm _ _ "%sub10.i" "%and6.i" 64 (clearLow w 2) (BitVec.ofInt 64 (-1)) (by b3_lk))
    ent_step (b8_step_and_reg _ _ "%and11.i" "%sub10.i" "%and6.i" 64 (clearLow w 2 + (-1)) (clearLow w 2) (by b3_lk) (by b3_lk))
    rw [show (clearLow w 2 + (-1)) &&& (clearLow w 2) = clearLow w 3 from rfl]
    ent_step (b8_step_call_cttz _ _ "%5" "%and11.i" (clearLow w 3) (BitVec.ofInt 1 (-1)) (by b3_lk))
    ent_step (step_trunc _ _ "%cast15.i" "%5" 64 32 (BitVec.ofNat 64 (cttz (clearLow w 3))) (by b3_lk))
    rw [trunc_cttz _]
    ent_step (b8_step_or_reg _ _ "%add16.i" "%conv" "%cast15.i" 32 (BitVec.ofNat 32 (posBase blk0 i)) (BitVec.ofNat 32 (cttz (clearLow w 3))) (by b3_lk) (by b3_lk))
    ent_step (b8_step_gep_imm _ _ "%arrayidx17.i" "%add.ptr" (.int 8) (o + 4 * k) (BitVec.ofInt 64 12) (by b3_lk) (by decide))
    rw [show (o + 4 * k) + (BitVec.ofInt 64 12).toNat * (Ty.int 8).sizeBytes = o + 4 * k + 4 * (3 + 0) from by
      simp [show (BitVec.ofInt 64 12).toNat = 12 from by decide,
        show (Ty.int 8).sizeBytes = 1 from rfl]]
    ent_step (b8_step_store32 _ _ "%add16.i" "%arrayidx17.i" (slotVal (posBase blk0 i) w 3) (o + 4 * k + 4 * (3 + 0)) (by b3_lk) (by b3_lk))
    -- slot 4
    ent_step (step_add_imm _ _ "%sub18.i" "%and11.i" 64 (clearLow w 3) (BitVec.ofInt 64 (-1)) (by b3_lk))
    ent_step (b8_step_and_reg _ _ "%and19.i" "%sub18.i" "%and11.i" 64 (clearLow w 3 + (-1)) (clearLow w 3) (by b3_lk) (by b3_lk))
    rw [show (clearLow w 3 + (-1)) &&& (clearLow w 3) = clearLow w 4 from rfl]
    ent_step (b8_step_call_cttz _ _ "%6" "%and19.i" (clearLow w 4) (BitVec.ofInt 1 (-1)) (by b3_lk))
    ent_step (step_trunc _ _ "%cast20.i" "%6" 64 32 (BitVec.ofNat 64 (cttz (clearLow w 4))) (by b3_lk))
    rw [trunc_cttz _]
    ent_step (b8_step_or_reg _ _ "%add21.i" "%conv" "%cast20.i" 32 (BitVec.ofNat 32 (posBase blk0 i)) (BitVec.ofNat 32 (cttz (clearLow w 4))) (by b3_lk) (by b3_lk))
    ent_step (b8_step_gep_imm _ _ "%arrayidx22.i" "%add.ptr" (.int 8) (o + 4 * k) (BitVec.ofInt 64 16) (by b3_lk) (by decide))
    rw [show (o + 4 * k) + (BitVec.ofInt 64 16).toNat * (Ty.int 8).sizeBytes = o + 4 * k + 4 * (3 + 1) from by
      simp [show (BitVec.ofInt 64 16).toNat = 16 from by decide,
        show (Ty.int 8).sizeBytes = 1 from rfl]]
    ent_step (b8_step_store32 _ _ "%add21.i" "%arrayidx22.i" (slotVal (posBase blk0 i) w 4) (o + 4 * k + 4 * (3 + 1)) (by b3_lk) (by b3_lk))
    -- slot 5
    ent_step (step_add_imm _ _ "%sub23.i" "%and19.i" 64 (clearLow w 4) (BitVec.ofInt 64 (-1)) (by b3_lk))
    ent_step (b8_step_and_reg _ _ "%and24.i" "%sub23.i" "%and19.i" 64 (clearLow w 4 + (-1)) (clearLow w 4) (by b3_lk) (by b3_lk))
    rw [show (clearLow w 4 + (-1)) &&& (clearLow w 4) = clearLow w 5 from rfl]
    ent_step (b8_step_call_cttz _ _ "%7" "%and24.i" (clearLow w 5) (BitVec.ofInt 1 (-1)) (by b3_lk))
    ent_step (step_trunc _ _ "%cast25.i" "%7" 64 32 (BitVec.ofNat 64 (cttz (clearLow w 5))) (by b3_lk))
    rw [trunc_cttz _]
    ent_step (b8_step_or_reg _ _ "%add26.i" "%conv" "%cast25.i" 32 (BitVec.ofNat 32 (posBase blk0 i)) (BitVec.ofNat 32 (cttz (clearLow w 5))) (by b3_lk) (by b3_lk))
    ent_step (b8_step_gep_imm _ _ "%arrayidx27.i" "%add.ptr" (.int 8) (o + 4 * k) (BitVec.ofInt 64 20) (by b3_lk) (by decide))
    rw [show (o + 4 * k) + (BitVec.ofInt 64 20).toNat * (Ty.int 8).sizeBytes = o + 4 * k + 4 * (3 + 2) from by
      simp [show (BitVec.ofInt 64 20).toNat = 20 from by decide,
        show (Ty.int 8).sizeBytes = 1 from rfl]]
    ent_step (b8_step_store32 _ _ "%add26.i" "%arrayidx27.i" (slotVal (posBase blk0 i) w 5) (o + 4 * k + 4 * (3 + 2)) (by b3_lk) (by b3_lk))
    -- slot 6
    ent_step (step_add_imm _ _ "%sub28.i" "%and24.i" 64 (clearLow w 5) (BitVec.ofInt 64 (-1)) (by b3_lk))
    ent_step (b8_step_and_reg _ _ "%and29.i" "%sub28.i" "%and24.i" 64 (clearLow w 5 + (-1)) (clearLow w 5) (by b3_lk) (by b3_lk))
    rw [show (clearLow w 5 + (-1)) &&& (clearLow w 5) = clearLow w 6 from rfl]
    ent_step (b8_step_call_cttz _ _ "%8" "%and29.i" (clearLow w 6) (BitVec.ofInt 1 (-1)) (by b3_lk))
    ent_step (step_trunc _ _ "%cast30.i" "%8" 64 32 (BitVec.ofNat 64 (cttz (clearLow w 6))) (by b3_lk))
    rw [trunc_cttz _]
    ent_step (b8_step_or_reg _ _ "%add31.i" "%conv" "%cast30.i" 32 (BitVec.ofNat 32 (posBase blk0 i)) (BitVec.ofNat 32 (cttz (clearLow w 6))) (by b3_lk) (by b3_lk))
    ent_step (b8_step_gep_imm _ _ "%arrayidx32.i" "%add.ptr" (.int 8) (o + 4 * k) (BitVec.ofInt 64 24) (by b3_lk) (by decide))
    rw [show (o + 4 * k) + (BitVec.ofInt 64 24).toNat * (Ty.int 8).sizeBytes = o + 4 * k + 4 * (3 + 3) from by
      simp [show (BitVec.ofInt 64 24).toNat = 24 from by decide,
        show (Ty.int 8).sizeBytes = 1 from rfl]]
    ent_step (b8_step_store32 _ _ "%add31.i" "%arrayidx32.i" (slotVal (posBase blk0 i) w 6) (o + 4 * k + 4 * (3 + 3)) (by b3_lk) (by b3_lk))
    ent_step (b8_step_icmp_ult_imm _ _ "%cmp35.i" "%1" 64 (BitVec.ofNat 64 (ctpop w)) (BitVec.ofInt 64 8) (by b3_lk))
    simp only [denoteCode, denoteRun, State.bindAll, Option.bind]
    rfl
  case hand' => simp [lookupName]
  case hcmp => simp [lookupName]

/-! ### The scalar tail's guard, preheader and loop -/

/-- The loop's phi incoming lists, in the order the fixture names them. -/
def b3IncomingK : List (String × Operand) :=
  [("while.body.i", reg "%inc.i"), ("while.body.preheader.i", lit 64 7)]

def b3IncomingC : List (String × Operand) :=
  [("while.body.i", reg "%and43.i"), ("while.body.preheader.i", reg "%and34.i")]

def b3IncomingO : List (String × Operand) :=
  [("while.body.i", reg "%incdec.ptr.i"), ("while.body.preheader.i", reg "%add.ptr.i")]

/-- The join's count phi: `%1` from the two early exits, seven from the guard's
empty-tail edge, and the running cursor from the loop. -/
def b3IncomingR : List (String × Operand) :=
  [("if.end", reg "%1"), ("if.end14.i", reg "%1"), ("if.end38.i", lit 64 7),
   ("while.body.i", reg "%10")]

/-- The guard before the loop: clear the seventh lane, count the rest, and enter
the loop only when a lane remains. -/
theorem b3TailGuard_run (env : Env) (s : State) (w : BitVec 64) (i blk0 k o : Nat)
    (hand : lookupName env "%and29.i" = some (.int 64 (clearLow w 6))) :
    ∃ env', denoteCode entryCalls b3TailGuard.instrs (withEnv env s) = some (withEnv env' s) ∧
      lookupName env' "%9" = some (.int 64 (BitVec.ofNat 64 (ctpop (clearLow w 7)))) ∧
      lookupName env' "%10"
        = some (.int 64 (BitVec.ofNat 64 (ctpop (clearLow w 7)) + BitVec.ofNat 64 7)) ∧
      lookupName env' "%and34.i" = some (.int 64 (clearLow w 7)) ∧
      lookupName env' "%11" = some (.int 1 (BitVec.ofBool (clearLow w 7 = 0))) := by
  refine ⟨?env', ?hrun, ?h9, ?h10, ?hand34, ?h11⟩
  case hrun =>
    simp only [b3TailGuard, reg, lit]
    ent_step (step_add_imm _ _ "%sub33.i" "%and29.i" 64 (clearLow w 6) (BitVec.ofInt 64 (-1)) (by b3_lk))
    ent_step (b8_step_and_reg _ _ "%and34.i" "%sub33.i" "%and29.i" 64 (clearLow w 6 + (-1)) (clearLow w 6) (by b3_lk) (by b3_lk))
    rw [show (clearLow w 6 + (-1)) &&& (clearLow w 6) = clearLow w 7 from rfl]
    ent_step (step_call_ctpop64 _ _ "%9" "%and34.i" (clearLow w 7) (by b3_lk))
    ent_step (step_add_imm _ _ "%10" "%9" 64 (BitVec.ofNat 64 (ctpop (clearLow w 7))) (BitVec.ofInt 64 7) (by b3_lk))
    rw [show BitVec.ofInt 64 7 = BitVec.ofNat 64 7 from by decide]
    ent_step (step_icmp_eq_imm _ _ "%11" "%and34.i" 64 (clearLow w 7) (BitVec.ofInt 64 0) (by b3_lk))
    simp only [denoteCode, denoteRun, State.bindAll, Option.bind]
    rfl
  case h9 => simp [lookupName]
  case h10 => simp [lookupName]
  case hand34 => simp [lookupName]
  case h11 => simp [lookupName]

theorem b3TailPreheader_run (env : Env) (s : State) (w : BitVec 64) (i blk0 k o : Nat)
    (hptr : lookupName env "%add.ptr" = some (.ptr (o + 4 * k))) :
    ∃ env', denoteCode entryCalls b3TailPreheader.instrs (withEnv env s) = some (withEnv env' s) ∧
      lookupName env' "%add.ptr.i" = some (.ptr (o + 4 * k + 4 * 7)) := by
  refine ⟨?env', ?hrun, ?hptr'⟩
  case hrun =>
    simp only [b3TailPreheader, reg, lit]
    ent_step (b8_step_gep_imm _ _ "%add.ptr.i" "%add.ptr" (.int 8) (o + 4 * k) (BitVec.ofInt 64 28) (by b3_lk) (by decide))
    rw [show (o + 4 * k) + (BitVec.ofInt 64 28).toNat * (Ty.int 8).sizeBytes = o + 4 * k + 4 * 7 from by
      simp [show (BitVec.ofInt 64 28).toNat = 28 from by decide,
        show (Ty.int 8).sizeBytes = 1 from rfl] <;> omega]
    simp only [denoteCode, denoteRun, State.bindAll, Option.bind]
    rfl
  case hptr' => simp [lookupName]

/-- One loop iteration, from the loop state at lane `7 + j`.  It writes one
position and hands the next state either the loop or the join. -/
theorem b3TailLoop_step (env : Env) (s : State) (w : BitVec 64) (i blk0 k o j n : Nat)
    (p : String) (opk opc opo : Operand) (mem0 : Mem)
    (hpc : s.pc = "while.body.i")
    (hpre : s.pre = some p)
    (hopk : phiIncoming p b3IncomingK = some opk)
    (hopc : phiIncoming p b3IncomingC = some opc)
    (hopo : phiIncoming p b3IncomingO = some opo)
    (hvk : evalOperand (withEnv env s) opk = some (.int 64 (BitVec.ofNat 64 (7 + j))))
    (hvc : evalOperand (withEnv (("%k.093.i", .int 64 (BitVec.ofNat 64 (7 + j))) :: env) s) opc
            = some (.int 64 (clearLow w (7 + j))))
    (hvo : evalOperand (withEnv (("%c.092.i", .int 64 (clearLow w (7 + j))) ::
            ("%k.093.i", .int 64 (BitVec.ofNat 64 (7 + j))) :: env) s) opo
            = some (.ptr (o + 4 * k + 4 * (7 + j))))
    (hconv : lookupName env "%conv" = some (.int 32 (BitVec.ofNat 32 (posBase blk0 i))))
    (h10 : lookupName env "%10" = some (.int 64 (BitVec.ofNat 64 n)))
    (hn64 : n < 2 ^ 64)
    (hlt : 7 + j < n)
    (hmem : s.mem = b8Lanes o w (posBase blk0 i) k 0 (7 + j) mem0) :
    ∃ env', denoteCode entryCalls b3TailLoop.instrs (withEnv env s)
        = some (withEnv env' { s with mem := b8Lanes o w (posBase blk0 i) k 0 (7 + j + 1) mem0 }) ∧
      lookupName env' "%inc.i" = some (.int 64 (BitVec.ofNat 64 (7 + j + 1))) ∧
      lookupName env' "%and43.i" = some (.int 64 (clearLow w (7 + j + 1))) ∧
      lookupName env' "%incdec.ptr.i" = some (.ptr (o + 4 * k + 4 * (7 + j + 1))) ∧
      lookupName env' "%exitcond.i"
        = some (.int 1 (BitVec.ofBool (BitVec.ofNat 64 (7 + j + 1) = BitVec.ofNat 64 n))) := by
  refine ⟨?env', ?hrun, ?hinc, ?hand, ?hptr', ?hx⟩
  case hrun =>
    simp only [b3TailLoop, reg, lit, b3IncomingK, b3IncomingC, b3IncomingO]
    have hmemC : ("%k.093.i" : String) ∉ Operand.regs opc := by
      have hm := phiIncoming_mem hopc
      simp only [b3IncomingC, List.map_cons, List.map_nil, List.mem_cons,
        List.not_mem_nil, or_false] at hm
      rcases hm with rfl | rfl <;> decide
    have hmemOk : ("%k.093.i" : String) ∉ Operand.regs opo := by
      have hm := phiIncoming_mem hopo
      simp only [b3IncomingO, List.map_cons, List.map_nil, List.mem_cons,
        List.not_mem_nil, or_false] at hm
      rcases hm with rfl | rfl <;> decide
    have hmemOc : ("%c.092.i" : String) ∉ Operand.regs opo := by
      have hm := phiIncoming_mem hopo
      simp only [b3IncomingO, List.map_cons, List.map_nil, List.mem_cons,
        List.not_mem_nil, or_false] at hm
      rcases hm with rfl | rfl <;> decide
    have hvc' : evalOperand (withEnv env s) opc
        = some (.int 64 (clearLow w (7 + j))) :=
      ((evalOperand_withEnv_cons_of_ne (env := env) (s := s)
        (n := "%k.093.i") (v := .int 64 (BitVec.ofNat 64 (7 + j))) (op := opc) hmemC).symm).trans hvc
    have hvo1 : evalOperand (withEnv (("%c.092.i", .int 64 (clearLow w (7 + j))) ::
        ("%k.093.i", .int 64 (BitVec.ofNat 64 (7 + j))) :: env) s) opo
        = some (.ptr (o + 4 * k + 4 * (7 + j))) := hvo
    have hstepC := evalOperand_withEnv_cons_of_ne
      (env := ("%k.093.i", .int 64 (BitVec.ofNat 64 (7 + j))) :: env) (s := s)
      (n := "%c.092.i") (v := .int 64 (clearLow w (7 + j))) (op := opo) hmemOc
    have hstepK := evalOperand_withEnv_cons_of_ne (env := env) (s := s)
      (n := "%k.093.i") (v := .int 64 (BitVec.ofNat 64 (7 + j))) (op := opo) hmemOk
    have hvo' : evalOperand (withEnv env s) opo
        = some (.ptr (o + 4 * k + 4 * (7 + j))) :=
      hstepK.symm.trans (hstepC.symm.trans hvo1)
    rw [denoteCode_phi3 _ _ _ _ _ _ _ _ _ _ _ _ _ hpre (by assumption) hvk
      (by assumption) hvc' (by assumption) hvo']
    all_goals (first | rfl | decide | skip)
    ent_step (b8_step_call_cttz _ _ "%12" "%c.092.i" (clearLow w (7 + j))
      (BitVec.ofInt 1 (-1)) (by b3_lk))
    ent_step (step_trunc _ _ "%cast40.i" "%12" 64 32
      (BitVec.ofNat 64 (cttz (clearLow w (7 + j)))) (by b3_lk))
    rw [trunc_cttz _]
    ent_step (b8_step_or_reg _ _ "%add41.i" "%conv" "%cast40.i" 32
      (BitVec.ofNat 32 (posBase blk0 i)) (BitVec.ofNat 32 (cttz (clearLow w (7 + j)))) (by b3_lk) (by b3_lk))
    ent_step (b8_step_gep_imm _ _ "%incdec.ptr.i" "%o.addr.091.i" (.int 8)
      (o + 4 * k + 4 * (7 + j)) (BitVec.ofInt 64 4) (by b3_lk) (by decide))
    rw [show (o + 4 * k + 4 * (7 + j)) + (BitVec.ofInt 64 4).toNat * (Ty.int 8).sizeBytes
        = o + 4 * k + 4 * (7 + j + 1) from by
      simp [show (BitVec.ofInt 64 4).toNat = 4 from by decide,
        show (Ty.int 8).sizeBytes = 1 from rfl]; omega]
    ent_step (b8_step_store32 _ _ "%add41.i" "%o.addr.091.i"
      (slotVal (posBase blk0 i) w (7 + j)) (o + 4 * k + 4 * (7 + j)) (by b3_lk) (by b3_lk))
    ent_step (step_add_imm _ _ "%inc.i" "%k.093.i" 64 (BitVec.ofNat 64 (7 + j))
      (BitVec.ofInt 64 1) (by b3_lk))
    rw [ofInt64_one, ofNat64_add_one (7 + j) (by omega)]
    ent_step (step_add_imm _ _ "%sub42.i" "%c.092.i" 64 (clearLow w (7 + j))
      (BitVec.ofInt 64 (-1)) (by b3_lk))
    ent_step (b8_step_and_reg _ _ "%and43.i" "%sub42.i" "%c.092.i" 64
      (clearLow w (7 + j) + (-1)) (clearLow w (7 + j)) (by b3_lk) (by b3_lk))
    rw [show (clearLow w (7 + j) + (-1)) &&& (clearLow w (7 + j)) = clearLow w (7 + j + 1) from rfl]
    ent_step (step_icmp_eq_reg _ _ "%exitcond.i" "%inc.i" "%10" 64
      (BitVec.ofNat 64 (7 + j + 1)) (BitVec.ofNat 64 n) (by b3_lk) (by b3_lk))
    rw [hmem]
    rw [show (7 + j + 1) = (7 + j) + 1 from by omega]
    rw [b8Lanes_succ]
    simp only [Nat.zero_add]
    simp only [denoteCode, denoteRun, State.bindAll, Option.bind]
    rfl
  case hinc => simp [lookupName]
  case hand => simp [lookupName]
  case hptr' => simp [lookupName]
  case hx => simp [lookupName]

/-- The join: the count phi and the cursor addition. -/
theorem b3Join_run (env : Env) (s : State) (rv k : Nat) (p : String) (opr : Operand)
    (hpre : s.pre = some p)
    (hopr : phiIncoming p b3IncomingR = some opr)
    (hrv : evalOperand (withEnv env s) opr = some (.int 64 (BitVec.ofNat 64 rv)))
    (hk : lookupName env "%k.addr.011" = some (.int 64 (BitVec.ofNat 64 k)))
    (hsum : rv + k < 2 ^ 64) :
    ∃ e, denoteCode entryCalls b3Join.instrs (withEnv env s) = some (withEnv e s) ∧
      lookupName e "%add1" = some (.int 64 (BitVec.ofNat 64 (rv + k))) := by
  refine ⟨?e, ?hrun, ?hadd⟩
  case hrun =>
    simp only [b3Join, reg, lit, b3IncomingR]
    rw [denoteCode_phi1 _ _ _ _ _ _ _ hpre (by assumption) hrv]
    all_goals (first | rfl | decide | skip)
    ent_step (step_add_reg _ _ "%add1" "%retval.0.i" "%k.addr.011" 64
      (BitVec.ofNat 64 rv) (BitVec.ofNat 64 k) (by b3_lk) (by b3_lk))
    rw [ofNat64_add_ofNat rv k hsum]
    simp only [denoteCode, denoteRun, State.bindAll, Option.bind]
    rfl
  case hadd => simp [lookupName]

/-- The state the loop's exit hands the join. -/
def b3JoinState (s : State) (M : Mem) : State :=
  { s with mem := M, pc := "s1f_ke_b3.exit", pre := some "while.body.i" }

/-- A long word's tail count is its population count, seven lanes on. -/
theorem b3_tail_count (w : BitVec 64) (hpop : 8 ≤ ctpop w) :
    BitVec.ofNat 64 (ctpop (clearLow w 7)) + BitVec.ofNat 64 7 = BitVec.ofNat 64 (ctpop w) := by
  have hsum : ctpop (clearLow w 7) + 7 = ctpop w := by
    have h := ctpop_clearLow w 7
    omega
  have hb : ctpop (clearLow w 7) + 7 < 2 ^ 64 := by
    have := ctpop_le w
    omega
  rw [ofNat64_add_ofNat _ _ hb, hsum]

theorem b3_tail_ne (w : BitVec 64) (hpop : 8 ≤ ctpop w) : clearLow w 7 ≠ 0 := by
  intro h
  have hc := ctpop_clearLow w 7
  rw [h] at hc
  rw [ctpop_zero64] at hc
  omega

/-- **The scalar tail's loop.**  From `while.body.i` at lane `7 + j`, with `r`
lanes left, it runs to the join and the memory gains those `r` lanes. -/
theorem b3TailLoop_run (w : BitVec 64) (e nblk i blk0 k o : Nat) (mem0 : Mem) (n : Nat) :
    ∀ (r j : Nat) (env : Env) (s : State) (p : String) (opk opc opo : Operand)
      (hctx : B8Ctx env e o blk0 nblk i k),
      1 ≤ r → 7 + j + r = n → n = ctpop w → n < 2 ^ 64 →
      s.pc = "while.body.i" → s.pre = some p →
      phiIncoming p b3IncomingK = some opk → phiIncoming p b3IncomingC = some opc →
      phiIncoming p b3IncomingO = some opo →
      evalOperand (withEnv env s) opk = some (.int 64 (BitVec.ofNat 64 (7 + j))) →
      evalOperand (withEnv (("%k.093.i", .int 64 (BitVec.ofNat 64 (7 + j))) :: env) s) opc
        = some (.int 64 (clearLow w (7 + j))) →
      evalOperand (withEnv (("%c.092.i", .int 64 (clearLow w (7 + j))) ::
        ("%k.093.i", .int 64 (BitVec.ofNat 64 (7 + j))) :: env) s) opo
        = some (.ptr (o + 4 * k + 4 * (7 + j))) →
      lookupName env "%conv" = some (.int 32 (BitVec.ofNat 32 (posBase blk0 i))) →
      lookupName env "%10" = some (.int 64 (BitVec.ofNat 64 n)) →
      lookupName env "%k.addr.011" = some (.int 64 (BitVec.ofNat 64 k)) →
      lookupName env "%i.010" = some (.int 64 (BitVec.ofNat 64 i)) →
      k + 64 ≤ 2 ^ 63 →
      s.mem = b8Lanes o w (posBase blk0 i) k 0 (7 + j) mem0 →
      ∃ (env' : Env),
        Jumps entryB3Function r (withEnv env s)
          (withEnv env' (b3JoinState s (b8Lanes o w (posBase blk0 i) k 0 n mem0))) ∧
        lookupName env' "%10" = some (.int 64 (BitVec.ofNat 64 n)) ∧
        lookupName env' "%conv" = some (.int 32 (BitVec.ofNat 32 (posBase blk0 i))) ∧
        lookupName env' "%k.addr.011" = some (.int 64 (BitVec.ofNat 64 k)) ∧
        lookupName env' "%i.010" = some (.int 64 (BitVec.ofNat 64 i)) ∧
        B8Ctx env' e o blk0 nblk i k := by
  intro r
  induction r with
  | zero => intro j env s p opk opc opo hctx h1; omega
  | succ r' ih =>
    intro j env s p opk opc opo hctx hr hjn hn hn64 hpc hpre hopk hopc hopo hvk hvc hvo
      hconv h10 hkadd hi hk63 hmem
    let S : State := { s with mem := b8Lanes o w (posBase blk0 i) k 0 (7 + j + 1) mem0 }
    have hlt : 7 + j < n := by omega
    obtain ⟨e1, hrun1, hinc1, hand1, hptr1, hx1⟩ :=
      b3TailLoop_step env s w i blk0 k o j n p opk opc opo mem0 hpc hpre hopk hopc hopo
        hvk hvc hvo hconv h10 hn64 hlt hmem
    have hctx1 : B8Ctx e1 e o blk0 nblk i k :=
      hctx.transfer (b8_keep b3TailLoop.instrs (by decide) _ _ hrun1)
    have hconv1 : lookupName e1 "%conv" = some (.int 32 (BitVec.ofNat 32 (posBase blk0 i))) :=
      (denoteCode_lookupName entryCalls b3TailLoop.instrs "%conv" (by decide)
        (withEnv env s) (withEnv e1 S) hrun1).trans hconv
    have h10_1 : lookupName e1 "%10" = some (.int 64 (BitVec.ofNat 64 n)) :=
      (denoteCode_lookupName entryCalls b3TailLoop.instrs "%10" (by decide)
        (withEnv env s) (withEnv e1 S) hrun1).trans h10
    have hkadd1 : lookupName e1 "%k.addr.011" = some (.int 64 (BitVec.ofNat 64 k)) :=
      (denoteCode_lookupName entryCalls b3TailLoop.instrs "%k.addr.011" (by decide)
        (withEnv env s) (withEnv e1 S) hrun1).trans hkadd
    have hi1 : lookupName e1 "%i.010" = some (.int 64 (BitVec.ofNat 64 i)) :=
      (denoteCode_lookupName entryCalls b3TailLoop.instrs "%i.010" (by decide)
        (withEnv env s) (withEnv e1 S) hrun1).trans hi
    rcases Nat.eq_zero_or_pos r' with hr0 | hrpos
    · -- the last iteration: the loop exits to the join
      subst hr0
      have hidx : 7 + j + 1 = n := by omega
      have hbit : BitVec.ofBool (BitVec.ofNat 64 (7 + j + 1) = BitVec.ofNat 64 n) = (1 : BitVec 1) := by
        rw [hidx]
        simp
      have hstep : step entryCalls entryB3Function (withEnv env s) =
          .jump (withEnv e1 (b3JoinState s (b8Lanes o w (posBase blk0 i) k 0 n mem0))) := by
        rw [b3_step_of (withEnv env s) "while.body.i" b3TailLoop (withEnv e1 S)
          hpc findBlock_b3TailLoop hrun1]
        show execTerm _ (.condbr (.reg "%exitcond.i") "s1f_ke_b3.exit" "while.body.i") = _
        rw [execTerm_condbr_true (c := .reg "%exitcond.i") (t := "s1f_ke_b3.exit")
          (f := "while.body.i")
          (JsonB8Steps.evalOperand_reg_of (env := e1) (s := S) (n := "%exitcond.i")
            (v := .int 1 (BitVec.ofBool (BitVec.ofNat 64 (7 + j + 1) = BitVec.ofNat 64 n)))
            (h := hx1)) hbit]
        rw [show (withEnv e1 S).pc = "while.body.i" from hpc]
        rw [withEnv_jump]
        rw [show (withEnv e1 ({ S with pc := "s1f_ke_b3.exit", pre := some "while.body.i" } : State))
            = withEnv e1 (b3JoinState s (b8Lanes o w (posBase blk0 i) k 0 n mem0)) from by
          simp only [S, b3JoinState, hidx]]
      exact ⟨e1, Jumps.one hstep, h10_1, hconv1, hkadd1, hi1, hctx1⟩
    · -- another lane remains: the loop's back edge
      have hne : BitVec.ofNat 64 (7 + j + 1) ≠ BitVec.ofNat 64 n := by
        intro hcon
        have := ofNat64_inj (a := 7 + j + 1) (b := n) (by omega) (by omega) hcon
        omega
      have hbit : BitVec.ofBool (BitVec.ofNat 64 (7 + j + 1) = BitVec.ofNat 64 n) = (0 : BitVec 1) := by
        rw [show decide (BitVec.ofNat 64 (7 + j + 1) = BitVec.ofNat 64 n) = false from
          decide_eq_false hne]
        rfl
      have hstep : step entryCalls entryB3Function (withEnv env s) =
          .jump (withEnv e1 (b8LoopState s (b8Lanes o w (posBase blk0 i) k 0 (7 + j + 1) mem0))) := by
        rw [b3_step_of (withEnv env s) "while.body.i" b3TailLoop (withEnv e1 S)
          hpc findBlock_b3TailLoop hrun1]
        show execTerm _ (.condbr (.reg "%exitcond.i") "s1f_ke_b3.exit" "while.body.i") = _
        rw [execTerm_condbr_false (c := .reg "%exitcond.i") (t := "s1f_ke_b3.exit")
          (f := "while.body.i")
          (JsonB8Steps.evalOperand_reg_of (env := e1) (s := S) (n := "%exitcond.i")
            (v := .int 1 (BitVec.ofBool (BitVec.ofNat 64 (7 + j + 1) = BitVec.ofNat 64 n)))
            (h := hx1)) hbit]
        rw [show (withEnv e1 S).pc = "while.body.i" from hpc]
        rw [withEnv_jump]
        rw [show (withEnv e1 ({ S with pc := "while.body.i", pre := some "while.body.i" } : State))
            = withEnv e1 (b8LoopState s (b8Lanes o w (posBase blk0 i) k 0 (7 + j + 1) mem0)) from rfl]
      obtain ⟨e2, hrec, h10_2, hconv2, hkadd2, hi2, hctx2⟩ :=
        ih (j + 1) e1 (b8LoopState s (b8Lanes o w (posBase blk0 i) k 0 (7 + j + 1) mem0))
          "while.body.i" (reg "%inc.i") (reg "%and43.i") (reg "%incdec.ptr.i") hctx1
          (by omega) (by omega) hn hn64 rfl rfl
          (by simp [b3IncomingK, phiIncoming]) (by simp [b3IncomingC, phiIncoming])
          (by simp [b3IncomingO, phiIncoming])
          (JsonB8Steps.evalOperand_reg_of (env := e1)
            (s := b8LoopState s (b8Lanes o w (posBase blk0 i) k 0 (7 + j + 1) mem0))
            (n := "%inc.i") (v := .int 64 (BitVec.ofNat 64 (7 + j + 1))) (h := hinc1))
          (JsonB8Steps.evalOperand_reg_of (env := ("%k.093.i", .int 64 (BitVec.ofNat 64 (7 + j + 1))) :: e1)
            (s := b8LoopState s (b8Lanes o w (posBase blk0 i) k 0 (7 + j + 1) mem0))
            (n := "%and43.i") (v := .int 64 (clearLow w (7 + j + 1)))
            (h := by simpa [lookupName] using hand1))
          (JsonB8Steps.evalOperand_reg_of (env := ("%c.092.i", .int 64 (clearLow w (7 + j + 1))) ::
              ("%k.093.i", .int 64 (BitVec.ofNat 64 (7 + j + 1))) :: e1)
            (s := b8LoopState s (b8Lanes o w (posBase blk0 i) k 0 (7 + j + 1) mem0))
            (n := "%incdec.ptr.i") (v := .ptr (o + 4 * k + 4 * (7 + j + 1)))
            (h := by simpa [lookupName] using hptr1))
          hconv1 h10_1 hkadd1 hi1 hk63 (by rfl)
      refine ⟨e2, ?_, h10_2, hconv2, hkadd2, hi2, hctx2⟩
      simpa only [b3JoinState, b8LoopState, Nat.add_comm] using Jumps.comp (Jumps.one hstep) hrec

/-- The preheader's entry state, named so the run's literals stay readable. -/
def b3PreState (s : State) : State :=
  { s with pc := "while.body.preheader.i", pre := some "if.end38.i" }

/-- The loop's entry state. -/
def b3TailEntry (s : State) : State :=
  { s with pc := "while.body.i", pre := some "while.body.preheader.i" }

/-- The join's entry state, at a given memory. -/
def b3JoinStart (s : State) (M : Mem) : State :=
  { s with mem := M, pc := "s1f_ke_b3.exit", pre := some "while.body.i" }

/-- **The whole scalar tail.**  From the guard at `if.end38.i`, a long word runs
through the preheader, the counted loop and the join to `cleanup`; the memory
gains the lanes past the seventh and the cursor gains the word's count.  The
resulting memory is a variable: composing the tail with the join never asks the
elaborator to reduce a lane fold. -/
theorem b3Tail_run (w : BitVec 64) (e i blk0 k o : Nat) (env : Env) (s : State)
    (mem0 : Mem) (nblk : Nat) (p : String)
    (hpc : s.pc = "if.end38.i")
    (hand : lookupName env "%and29.i" = some (.int 64 (clearLow w 6)))
    (hptr : lookupName env "%add.ptr" = some (.ptr (o + 4 * k)))
    (hconv : lookupName env "%conv" = some (.int 32 (BitVec.ofNat 32 (posBase blk0 i))))
    (hi : lookupName env "%i.010" = some (.int 64 (BitVec.ofNat 64 i)))
    (hk : lookupName env "%k.addr.011" = some (.int 64 (BitVec.ofNat 64 k)))
    (hnb : lookupName env "%nblk" = some (.int 64 (BitVec.ofNat 64 nblk)))
    (hctx : B8Ctx env e o blk0 nblk i k)
    (hpop : 8 ≤ ctpop w)
    (hk63 : k + 64 ≤ 2 ^ 63)
    (hmem : s.mem = b8Lanes o w (posBase blk0 i) k 0 7 mem0) :
    ∃ (env' : Env),
      Jumps entryB3Function (3 + (ctpop w - 7)) (withEnv env s)
        (withEnv env' (b8AdvanceAt s
          (b8Lanes o w (posBase blk0 i) k 0 (ctpop w) mem0) "s1f_ke_b3.exit")) ∧
      lookupName env' "%add1" = some (.int 64 (BitVec.ofNat 64 (ctpop w + k))) ∧
      lookupName env' "%i.010" = some (.int 64 (BitVec.ofNat 64 i)) ∧
      B8Ctx env' e o blk0 nblk i k := by
  obtain ⟨e1, hguard, h9, h10, hand34, h11⟩ := b3TailGuard_run env s w i blk0 k o hand
  have hctx1 : B8Ctx e1 e o blk0 nblk i k :=
    hctx.transfer (b8_keep b3TailGuard.instrs (by decide) _ _ hguard)
  have hne : clearLow w 7 ≠ 0 := b3_tail_ne w hpop
  have hbit0 : BitVec.ofBool (clearLow w 7 = 0) = (0 : BitVec 1) := by
    rw [show decide (clearLow w 7 = 0) = false from decide_eq_false hne]
    rfl
  have hstep1 : step entryCalls entryB3Function (withEnv env s) =
      .jump (withEnv e1 (b3PreState s)) := by
    rw [b3_step_of (withEnv env s) "if.end38.i" b3TailGuard (withEnv e1 s) hpc
      findBlock_b3TailGuard hguard]
    show execTerm _ (.condbr (.reg "%11") "s1f_ke_b3.exit" "while.body.preheader.i") = _
    rw [execTerm_condbr_false (c := .reg "%11") (t := "s1f_ke_b3.exit")
      (f := "while.body.preheader.i")
      (JsonB8Steps.evalOperand_reg_of (env := e1) (s := s) (n := "%11")
        (v := .int 1 (BitVec.ofBool (clearLow w 7 = 0))) (h := h11)) hbit0]
    rw [show (withEnv e1 s).pc = "if.end38.i" from hpc]
    rw [withEnv_jump]
    simp only [withEnv, b3PreState]
  -- the preheader
  have hptr1 : lookupName e1 "%add.ptr" = some (.ptr (o + 4 * k)) :=
    (denoteCode_lookupName entryCalls b3TailGuard.instrs "%add.ptr" (by decide)
      (withEnv env s) (withEnv e1 s) hguard).trans hptr
  have hconv1 : lookupName e1 "%conv" = some (.int 32 (BitVec.ofNat 32 (posBase blk0 i))) :=
    (denoteCode_lookupName entryCalls b3TailGuard.instrs "%conv" (by decide)
      (withEnv env s) (withEnv e1 s) hguard).trans hconv
  have hi1 : lookupName e1 "%i.010" = some (.int 64 (BitVec.ofNat 64 i)) :=
    (denoteCode_lookupName entryCalls b3TailGuard.instrs "%i.010" (by decide)
      (withEnv env s) (withEnv e1 s) hguard).trans hi
  have hk1 : lookupName e1 "%k.addr.011" = some (.int 64 (BitVec.ofNat 64 k)) :=
    (denoteCode_lookupName entryCalls b3TailGuard.instrs "%k.addr.011" (by decide)
      (withEnv env s) (withEnv e1 s) hguard).trans hk
  have hnb1 : lookupName e1 "%nblk" = some (.int 64 (BitVec.ofNat 64 nblk)) :=
    (denoteCode_lookupName entryCalls b3TailGuard.instrs "%nblk" (by decide)
      (withEnv env s) (withEnv e1 s) hguard).trans hnb
  obtain ⟨e2, hpre, hptr2⟩ := b3TailPreheader_run e1 (b3PreState s) w i blk0 k o hptr1
  have hctx2 : B8Ctx e2 e o blk0 nblk i k :=
    hctx1.transfer (b8_keep b3TailPreheader.instrs (by decide) _ _ hpre)
  have hstep2 : step entryCalls entryB3Function
      (withEnv e1 (b3PreState s)) =
      .jump (withEnv e2 (b3TailEntry s)) := by
    rw [b3_step_of (withEnv e1 (b3PreState s)) "while.body.preheader.i" b3TailPreheader
      (withEnv e2 (b3PreState s)) rfl findBlock_b3TailPreheader hpre]
    show execTerm _ (.br "while.body.i") = _
    rw [execTerm_br]
    rw [withEnv_jump]
    simp only [withEnv, b3PreState, b3TailEntry]
  have h10n : lookupName e2 "%10" = some (.int 64 (BitVec.ofNat 64 (ctpop w))) := by
    have hkeep : lookupName e2 "%10" = lookupName e1 "%10" :=
      denoteCode_lookupName entryCalls b3TailPreheader.instrs "%10" (by decide)
        (withEnv e1 (b3PreState s)) (withEnv e2 (b3PreState s)) hpre
    rw [hkeep, h10]
    exact congrArg (fun v => some (Value.int 64 v)) (b3_tail_count w hpop)
  have hconv2 : lookupName e2 "%conv" = some (.int 32 (BitVec.ofNat 32 (posBase blk0 i))) :=
    (denoteCode_lookupName entryCalls b3TailPreheader.instrs "%conv" (by decide)
      (withEnv e1 (b3PreState s)) (withEnv e2 (b3PreState s)) hpre).trans hconv1
  have hi2 : lookupName e2 "%i.010" = some (.int 64 (BitVec.ofNat 64 i)) :=
    (denoteCode_lookupName entryCalls b3TailPreheader.instrs "%i.010" (by decide)
      (withEnv e1 (b3PreState s)) (withEnv e2 (b3PreState s)) hpre).trans hi1
  have hk2 : lookupName e2 "%k.addr.011" = some (.int 64 (BitVec.ofNat 64 k)) :=
    (denoteCode_lookupName entryCalls b3TailPreheader.instrs "%k.addr.011" (by decide)
      (withEnv e1 (b3PreState s)) (withEnv e2 (b3PreState s)) hpre).trans hk1
  have hnb2 : lookupName e2 "%nblk" = some (.int 64 (BitVec.ofNat 64 nblk)) :=
    (denoteCode_lookupName entryCalls b3TailPreheader.instrs "%nblk" (by decide)
      (withEnv e1 (b3PreState s)) (withEnv e2 (b3PreState s)) hpre).trans hnb1
  -- the counted loop
  obtain ⟨e3, hloop, h10_3, hconv3, hkadd3, hi3, hctx3⟩ :=
    b3TailLoop_run w e nblk i blk0 k o mem0 (ctpop w) (ctpop w - 7) 0 e2
      (b3TailEntry s)
      "while.body.preheader.i" (lit 64 7) (reg "%and34.i") (reg "%add.ptr.i") hctx2
      (by omega) (by omega) rfl (by have := ctpop_le w; omega) rfl rfl
      (by simp [b3IncomingK, phiIncoming]) (by simp [b3IncomingC, phiIncoming])
      (by simp [b3IncomingO, phiIncoming])
      (by
        show evalOperand (withEnv e2 (b3TailEntry s)) (.imm (.int 64 (BitVec.ofInt 64 7)))
          = some (.int 64 (BitVec.ofNat 64 (7 + 0)))
        rw [show (BitVec.ofInt 64 7 : BitVec 64) = BitVec.ofNat 64 7 from by decide,
          Nat.add_zero]
        exact evalOperand_lit_of _ 64 _)
      (JsonB8Steps.evalOperand_reg_of (env := e2) (s := b3TailEntry s) (n := "%and34.i")
        (v := .int 64 (clearLow w (7 + 0))) (h := by
          rw [Nat.add_zero]
          exact (denoteCode_lookupName entryCalls b3TailPreheader.instrs "%and34.i" (by decide)
            (withEnv e1 (b3PreState s)) (withEnv e2 (b3PreState s)) hpre).trans hand34))
      (JsonB8Steps.evalOperand_reg_of
        (env := ("%c.092.i", .int 64 (clearLow w (7 + 0))) ::
          ("%k.093.i", .int 64 (BitVec.ofNat 64 (7 + 0))) :: e2)
        (s := b3TailEntry s) (n := "%add.ptr.i") (v := .ptr (o + 4 * k + 4 * (7 + 0)))
        (h := by simpa [lookupName, Nat.add_zero] using hptr2))
      hconv2 h10n hk2 hi2 hk63 (by rw [Nat.add_zero]; exact hmem)
  -- the join
  have hjoinTarget : b3JoinState (b3TailEntry s)
        (b8Lanes o w (posBase blk0 i) k 0 (ctpop w) mem0)
      = b3JoinStart s (b8Lanes o w (posBase blk0 i) k 0 (ctpop w) mem0) := by
    simp only [b3JoinState, b3TailEntry, b3JoinStart]
  rw [hjoinTarget] at hloop
  obtain ⟨e4, hjoin, hadd1⟩ :=
    b3Join_run e3 (b3JoinStart s (b8Lanes o w (posBase blk0 i) k 0 (ctpop w) mem0))
      (ctpop w) k "while.body.i" (reg "%10") rfl (by simp [b3IncomingR, phiIncoming])
      (JsonB8Steps.evalOperand_reg_of (env := e3)
        (s := b3JoinStart s (b8Lanes o w (posBase blk0 i) k 0 (ctpop w) mem0))
        (n := "%10") (v := .int 64 (BitVec.ofNat 64 (ctpop w))) (h := h10_3))
      hkadd3
      (by have := ctpop_le w; omega)
  have hctx4 : B8Ctx e4 e o blk0 nblk i k :=
    hctx3.transfer (b8_keep b3Join.instrs (by decide) _ _ hjoin)
  have hstep3 : step entryCalls entryB3Function
      (withEnv e3 (b3JoinStart s (b8Lanes o w (posBase blk0 i) k 0 (ctpop w) mem0))) =
      .jump (withEnv e4 (b8AdvanceAt s
        (b8Lanes o w (posBase blk0 i) k 0 (ctpop w) mem0) "s1f_ke_b3.exit")) := by
    rw [b3_step_of (withEnv e3 _) "s1f_ke_b3.exit" b3Join (withEnv e4 _) rfl
      findBlock_b3Join hjoin]
    show execTerm _ (.br "cleanup") = _
    rw [execTerm_br]
    rw [withEnv_jump]
    simp only [withEnv, b3JoinStart, b8AdvanceAt]
  have hi4 : lookupName e4 "%i.010" = some (.int 64 (BitVec.ofNat 64 i)) := by
    have h := denoteCode_lookupName entryCalls b3Join.instrs "%i.010" (by decide)
      (withEnv e3 (b3JoinStart s (b8Lanes o w (posBase blk0 i) k 0 (ctpop w) mem0)))
      (withEnv e4 (b3JoinStart s (b8Lanes o w (posBase blk0 i) k 0 (ctpop w) mem0))) hjoin
    simpa only [withEnv] using h.trans hi3
  refine ⟨e4, ?_, hadd1, hi4, hctx4⟩
  have h1 := Jumps.comp (Jumps.one hstep1) (Jumps.one hstep2)
  have h2 := Jumps.comp h1 hloop
  have h3 := Jumps.comp h2 (Jumps.one hstep3)
  rw [show 3 + (ctpop w - 7) = (1 + 1) + (ctpop w - 7) + 1 from by omega]
  exact h3

/-! ### The written-lane counts of the three exits -/

/-- A word of at most three set lanes writes three slots. -/
theorem b3Len_of_le3 {w : BitVec 64} (hw : w ≠ 0) (h : ctpop w ≤ 3) : b3Len w = 3 := by
  have h0 : ctpop w ≠ 0 := by
    intro hz
    refine hw (eq_zero_of_setLanes_nil ?_)
    have hlen := ctpop_eq_setLanes_length w
    rw [hz] at hlen
    exact List.length_eq_zero_iff.mp hlen.symm
  unfold b3Len
  rw [if_neg h0, if_pos h]

/-- A word of four to seven set lanes writes seven slots. -/
theorem b3Len_of_le7 {w : BitVec 64} (h3 : ¬ ctpop w ≤ 3) (h7 : ctpop w ≤ 7) :
    b3Len w = 7 := by
  have h0 : ctpop w ≠ 0 := by omega
  unfold b3Len
  rw [if_neg h0, if_neg h3, if_pos h7]

/-- Above seven lanes the tail writes one slot per set lane. -/
theorem b3Len_of_ge8 {w : BitVec 64} (h : 8 ≤ ctpop w) : b3Len w = ctpop w := by
  have h0 : ctpop w ≠ 0 := by omega
  have h3 : ¬ ctpop w ≤ 3 := by omega
  have h7 : ¬ ctpop w ≤ 7 := by omega
  unfold b3Len
  rw [if_neg h0, if_neg h3, if_neg h7]

/-! ### `for.body`, `cleanup` and `for.cond.cleanup`

B3's three outer blocks are the same instructions as POS8's, so their bodies are
the same terms; only the function the step is taken in differs. -/

theorem b3Body_body (env : Env) (s : State) (w : BitVec 64) (i k e : Nat) (p : String)
    (opk opi : Operand)
    (hpre : s.pre = some p)
    (hopk : phiIncoming p pos8IncomingK = some opk)
    (hopi : phiIncoming p pos8IncomingI = some opi)
    (hvk : evalOperand (withEnv env s) opk = some (.int 64 (BitVec.ofNat 64 k)))
    (hvi : evalOperand (withEnv (("%k.addr.011", .int 64 (BitVec.ofNat 64 k)) :: env) s) opi
            = some (.int 64 (BitVec.ofNat 64 i)))
    (hent : lookupName env "%ent" = some (.ptr e))
    (hread : readBytes s.mem (e + 8 * i) 8 = some (natToBytes w.toNat 8))
    (hi63 : i < 2 ^ 63) :
    ∃ env', denoteCode entryCalls b3Body.instrs (withEnv env s) = some (withEnv env' s) ∧
      lookupName env' "%i.010" = some (.int 64 (BitVec.ofNat 64 i)) ∧
      lookupName env' "%k.addr.011" = some (.int 64 (BitVec.ofNat 64 k)) ∧
      lookupName env' "%0" = some (.int 64 w) ∧
      lookupName env' "%tobool.not" = some (.int 1 (BitVec.ofBool (w = 0))) :=
  pos8Body_body env s w i k e p opk opi hpre hopk hopi hvk hvi hent hread hi63

theorem b3Body_step_zero (env : Env) (s : State) (w : BitVec 64) (i k e : Nat) (p : String)
    (opk opi : Operand)
    (hpc : s.pc = "for.body")
    (hpre : s.pre = some p)
    (hopk : phiIncoming p pos8IncomingK = some opk)
    (hopi : phiIncoming p pos8IncomingI = some opi)
    (hvk : evalOperand (withEnv env s) opk = some (.int 64 (BitVec.ofNat 64 k)))
    (hvi : evalOperand (withEnv (("%k.addr.011", .int 64 (BitVec.ofNat 64 k)) :: env) s) opi
            = some (.int 64 (BitVec.ofNat 64 i)))
    (hent : lookupName env "%ent" = some (.ptr e))
    (hread : readBytes s.mem (e + 8 * i) 8 = some (natToBytes w.toNat 8))
    (hi63 : i < 2 ^ 63)
    (hw : w = 0) :
    ∃ env', denoteCode entryCalls b3Body.instrs (withEnv env s) = some (withEnv env' s) ∧
      step entryCalls entryB3Function (withEnv env s)
        = .jump (withEnv env' { s with pc := "cleanup", pre := some "for.body" }) ∧
      lookupName env' "%i.010" = some (.int 64 (BitVec.ofNat 64 i)) ∧
      lookupName env' "%k.addr.011" = some (.int 64 (BitVec.ofNat 64 k)) ∧
      lookupName env' "%0" = some (.int 64 w) ∧
      lookupName env' "%tobool.not" = some (.int 1 1) := by
  obtain ⟨env', hbody, h1, h2, h3, h4⟩ :=
    b3Body_body env s w i k e p opk opi hpre hopk hopi hvk hvi hent hread hi63
  have hb : BitVec.ofBool (w = 0) = (1 : BitVec 1) := by
    rw [show decide (w = 0) = true from decide_eq_true hw]; rfl
  refine ⟨env', hbody, ?_, h1, h2, h3, ?_⟩
  · rw [b3_step_of (withEnv env s) "for.body" b3Body (withEnv env' s) hpc
      findBlock_b3Body hbody]
    show execTerm (withEnv env' s) (.condbr (.reg "%tobool.not") "cleanup" "if.end")
      = .jump (withEnv env' { s with pc := "cleanup", pre := some "for.body" })
    rw [execTerm_condbr_true (c := .reg "%tobool.not") (t := "cleanup") (f := "if.end")
      (JsonB8Steps.evalOperand_reg_of env' s "%tobool.not" (.int 1 (BitVec.ofBool (w = 0))) h4) hb]
    rw [show (withEnv env' s).pc = "for.body" from hpc]
    rfl
  · rwa [hb] at h4

theorem b3Body_step_pos (env : Env) (s : State) (w : BitVec 64) (i k e : Nat) (p : String)
    (opk opi : Operand)
    (hpc : s.pc = "for.body")
    (hpre : s.pre = some p)
    (hopk : phiIncoming p pos8IncomingK = some opk)
    (hopi : phiIncoming p pos8IncomingI = some opi)
    (hvk : evalOperand (withEnv env s) opk = some (.int 64 (BitVec.ofNat 64 k)))
    (hvi : evalOperand (withEnv (("%k.addr.011", .int 64 (BitVec.ofNat 64 k)) :: env) s) opi
            = some (.int 64 (BitVec.ofNat 64 i)))
    (hent : lookupName env "%ent" = some (.ptr e))
    (hread : readBytes s.mem (e + 8 * i) 8 = some (natToBytes w.toNat 8))
    (hi63 : i < 2 ^ 63)
    (hw : w ≠ 0) :
    ∃ env', denoteCode entryCalls b3Body.instrs (withEnv env s) = some (withEnv env' s) ∧
      step entryCalls entryB3Function (withEnv env s)
        = .jump (withEnv env' { s with pc := "if.end", pre := some "for.body" }) ∧
      lookupName env' "%i.010" = some (.int 64 (BitVec.ofNat 64 i)) ∧
      lookupName env' "%k.addr.011" = some (.int 64 (BitVec.ofNat 64 k)) ∧
      lookupName env' "%0" = some (.int 64 w) ∧
      lookupName env' "%tobool.not" = some (.int 1 0) := by
  obtain ⟨env', hbody, h1, h2, h3, h4⟩ :=
    b3Body_body env s w i k e p opk opi hpre hopk hopi hvk hvi hent hread hi63
  have hb : BitVec.ofBool (w = 0) = (0 : BitVec 1) := by
    rw [show decide (w = 0) = false from decide_eq_false hw]; rfl
  refine ⟨env', hbody, ?_, h1, h2, h3, ?_⟩
  · rw [b3_step_of (withEnv env s) "for.body" b3Body (withEnv env' s) hpc
      findBlock_b3Body hbody]
    show execTerm (withEnv env' s) (.condbr (.reg "%tobool.not") "cleanup" "if.end")
      = .jump (withEnv env' { s with pc := "if.end", pre := some "for.body" })
    rw [execTerm_condbr_false (c := .reg "%tobool.not") (t := "cleanup") (f := "if.end")
      (JsonB8Steps.evalOperand_reg_of env' s "%tobool.not" (.int 1 (BitVec.ofBool (w = 0))) h4) hb]
    rw [show (withEnv env' s).pc = "for.body" from hpc]
    rfl
  · rwa [hb] at h4

/-- `cleanup`'s phi, whose first edge comes from B3's join. -/
def b3IncomingCl : List (String × Operand) :=
  [("s1f_ke_b3.exit", reg "%add1"), ("for.body", reg "%k.addr.011")]

/-- `cleanup`: the cursor phi, the block counter, and the exit test. -/
theorem b3Advance_body (env : Env) (s : State) (i k nblk : Nat) (p : String) (opk : Operand)
    (hpre : s.pre = some p)
    (hopk : phiIncoming p b3IncomingCl = some opk)
    (hvk : evalOperand (withEnv env s) opk = some (.int 64 (BitVec.ofNat 64 k)))
    (hi : lookupName env "%i.010" = some (.int 64 (BitVec.ofNat 64 i)))
    (hnb : lookupName env "%nblk" = some (.int 64 (BitVec.ofNat 64 nblk)))
    (hi64 : i + 1 < 2 ^ 64) :
    ∃ env', denoteCode entryCalls b3Advance.instrs (withEnv env s) = some (withEnv env' s) ∧
      lookupName env' "%k.addr.1" = some (.int 64 (BitVec.ofNat 64 k)) ∧
      lookupName env' "%inc" = some (.int 64 (BitVec.ofNat 64 (i + 1))) ∧
      lookupName env' "%exitcond.not"
        = some (.int 1 (BitVec.ofBool (BitVec.ofNat 64 (i + 1) = BitVec.ofNat 64 nblk))) := by
  refine ⟨?env', ?hrun, ?hk, ?hinc, ?hx⟩
  case hrun =>
    simp only [b3Advance, reg, lit, b3IncomingCl]
    rw [denoteCode_phi1 _ _ _ _ _ _ _ hpre (by assumption) hvk]
    all_goals (first | rfl | decide | skip)
    ent_step (step_add_imm _ _ "%inc" "%i.010" 64 (BitVec.ofNat 64 i) (BitVec.ofInt 64 1)
      (by ent_auto))
    rw [ofInt64_one, ofNat64_add_one i hi64]
    ent_step (step_icmp_eq_reg _ _ "%exitcond.not" "%inc" "%nblk" 64
      (BitVec.ofNat 64 (i + 1)) (BitVec.ofNat 64 nblk) (by ent_auto) (by ent_auto))
    simp only [denoteCode, denoteRun, State.bindAll, Option.bind]
    rfl
  case hk => ent_auto
  case hinc => ent_auto
  case hx => ent_auto

theorem b3Advance_step_more (env : Env) (s : State) (i k nblk : Nat) (p : String)
    (opk : Operand)
    (hpc : s.pc = "cleanup")
    (hpre : s.pre = some p)
    (hopk : phiIncoming p b3IncomingCl = some opk)
    (hvk : evalOperand (withEnv env s) opk = some (.int 64 (BitVec.ofNat 64 k)))
    (hi : lookupName env "%i.010" = some (.int 64 (BitVec.ofNat 64 i)))
    (hnb : lookupName env "%nblk" = some (.int 64 (BitVec.ofNat 64 nblk)))
    (hi64 : i + 1 < 2 ^ 64)
    (hx : ¬ BitVec.ofNat 64 (i + 1) = BitVec.ofNat 64 nblk) :
    ∃ env', denoteCode entryCalls b3Advance.instrs (withEnv env s) = some (withEnv env' s) ∧
      step entryCalls entryB3Function (withEnv env s)
        = .jump (withEnv env' { s with pc := "for.body", pre := some "cleanup" }) ∧
      lookupName env' "%k.addr.1" = some (.int 64 (BitVec.ofNat 64 k)) ∧
      lookupName env' "%inc" = some (.int 64 (BitVec.ofNat 64 (i + 1))) ∧
      lookupName env' "%exitcond.not" = some (.int 1 0) := by
  obtain ⟨env', hbody, hk, hinc, hxx⟩ :=
    b3Advance_body env s i k nblk p opk hpre hopk hvk hi hnb hi64
  have hx' : BitVec.ofBool (BitVec.ofNat 64 (i + 1) = BitVec.ofNat 64 nblk) = (0 : BitVec 1) := by
    rw [show decide (BitVec.ofNat 64 (i + 1) = BitVec.ofNat 64 nblk) = false from
      decide_eq_false hx]
    rfl
  refine ⟨env', hbody, ?_, hk, hinc, ?_⟩
  · rw [b3_step_of (withEnv env s) "cleanup" b3Advance (withEnv env' s) hpc
      findBlock_b3Advance hbody]
    show execTerm (withEnv env' s) (.condbr (.reg "%exitcond.not") "for.cond.cleanup" "for.body")
      = .jump (withEnv env' { s with pc := "for.body", pre := some "cleanup" })
    rw [execTerm_condbr_false (c := .reg "%exitcond.not") (t := "for.cond.cleanup")
      (f := "for.body")
      (JsonB8Steps.evalOperand_reg_of env' s "%exitcond.not"
        (.int 1 (BitVec.ofBool (BitVec.ofNat 64 (i + 1) = BitVec.ofNat 64 nblk))) hxx) hx']
    rw [show (withEnv env' s).pc = "cleanup" from hpc]
    rfl
  · rwa [hx'] at hxx

theorem b3Advance_step_last (env : Env) (s : State) (i k nblk : Nat) (p : String)
    (opk : Operand)
    (hpc : s.pc = "cleanup")
    (hpre : s.pre = some p)
    (hopk : phiIncoming p b3IncomingCl = some opk)
    (hvk : evalOperand (withEnv env s) opk = some (.int 64 (BitVec.ofNat 64 k)))
    (hi : lookupName env "%i.010" = some (.int 64 (BitVec.ofNat 64 i)))
    (hnb : lookupName env "%nblk" = some (.int 64 (BitVec.ofNat 64 nblk)))
    (hi64 : i + 1 < 2 ^ 64)
    (hx : BitVec.ofNat 64 (i + 1) = BitVec.ofNat 64 nblk) :
    ∃ env', denoteCode entryCalls b3Advance.instrs (withEnv env s) = some (withEnv env' s) ∧
      step entryCalls entryB3Function (withEnv env s)
        = .jump (withEnv env' { s with pc := "for.cond.cleanup", pre := some "cleanup" }) ∧
      lookupName env' "%k.addr.1" = some (.int 64 (BitVec.ofNat 64 k)) ∧
      lookupName env' "%inc" = some (.int 64 (BitVec.ofNat 64 (i + 1))) ∧
      lookupName env' "%exitcond.not" = some (.int 1 1) := by
  obtain ⟨env', hbody, hk, hinc, hxx⟩ :=
    b3Advance_body env s i k nblk p opk hpre hopk hvk hi hnb hi64
  have hx' : BitVec.ofBool (BitVec.ofNat 64 (i + 1) = BitVec.ofNat 64 nblk) = (1 : BitVec 1) := by
    rw [show decide (BitVec.ofNat 64 (i + 1) = BitVec.ofNat 64 nblk) = true from
      decide_eq_true hx]
    rfl
  refine ⟨env', hbody, ?_, hk, hinc, ?_⟩
  · rw [b3_step_of (withEnv env s) "cleanup" b3Advance (withEnv env' s) hpc
      findBlock_b3Advance hbody]
    show execTerm (withEnv env' s) (.condbr (.reg "%exitcond.not") "for.cond.cleanup" "for.body")
      = .jump (withEnv env' { s with pc := "for.cond.cleanup", pre := some "cleanup" })
    rw [execTerm_condbr_true (c := .reg "%exitcond.not") (t := "for.cond.cleanup")
      (f := "for.body")
      (JsonB8Steps.evalOperand_reg_of env' s "%exitcond.not"
        (.int 1 (BitVec.ofBool (BitVec.ofNat 64 (i + 1) = BitVec.ofNat 64 nblk))) hxx) hx']
    rw [show (withEnv env' s).pc = "cleanup" from hpc]
    rfl
  · rwa [hx'] at hxx

/-- `for.cond.cleanup`: the cursor phi and the return. -/
theorem b3Exit_run (env : Env) (s : State) (k : Nat) (p : String) (opk : Operand)
    (hpre : s.pre = some p)
    (hopk : phiIncoming p pos8IncomingE = some opk)
    (hvk : evalOperand (withEnv env s) opk = some (.int 64 (BitVec.ofNat 64 k))) :
    ∃ env', denoteCode entryCalls b3LoopExit.instrs (withEnv env s) = some (withEnv env' s) ∧
      lookupName env' "%k.addr.0.lcssa" = some (.int 64 (BitVec.ofNat 64 k)) :=
  pos8Exit_body env s k p opk hpre hopk hvk

theorem b3Exit_step (env : Env) (s : State) (k : Nat) (p : String) (opk : Operand)
    (hpc : s.pc = "for.cond.cleanup")
    (hpre : s.pre = some p)
    (hopk : phiIncoming p pos8IncomingE = some opk)
    (hvk : evalOperand (withEnv env s) opk = some (.int 64 (BitVec.ofNat 64 k))) :
    ∃ env', denoteCode entryCalls b3LoopExit.instrs (withEnv env s) = some (withEnv env' s) ∧
      step entryCalls entryB3Function (withEnv env s)
        = .ret (some (.int 64 (BitVec.ofNat 64 k))) (withEnv env' s) ∧
      lookupName env' "%k.addr.0.lcssa" = some (.int 64 (BitVec.ofNat 64 k)) := by
  obtain ⟨env', hbody, hk⟩ := b3Exit_run env s k p opk hpre hopk hvk
  refine ⟨env', hbody, ?_, hk⟩
  rw [b3_step_of (withEnv env s) "for.cond.cleanup" b3LoopExit (withEnv env' s) hpc
    findBlock_b3Exit hbody]
  show execTerm (withEnv env' s) (.ret (.int 64) (some (.reg "%k.addr.0.lcssa")))
    = .ret (some (.int 64 (BitVec.ofNat 64 k))) (withEnv env' s)
  rw [execTerm_ret_reg (s := withEnv env' s) (d := "%k.addr.0.lcssa")
    (v := .int 64 (BitVec.ofNat 64 k)) (JsonB8Steps.evalOperand_reg_of env' s "%k.addr.0.lcssa"
      (.int 64 (BitVec.ofNat 64 k)) hk)]

/-! ### One block -/

/-- A zero word: `for.body` takes the `continue` edge to `cleanup`, and the
memory is unchanged. -/
theorem b3Block_zero_run (env : Env) (s : State) (i k nblk e o blk0 : Nat) (p : String)
    (opk opi : Operand)
    (hpc : s.pc = "for.body")
    (hpre : s.pre = some p)
    (hopk : phiIncoming p pos8IncomingK = some opk)
    (hopi : phiIncoming p pos8IncomingI = some opi)
    (hvk : evalOperand (withEnv env s) opk = some (.int 64 (BitVec.ofNat 64 k)))
    (hvi : evalOperand (withEnv (("%k.addr.011", .int 64 (BitVec.ofNat 64 k)) :: env) s) opi
            = some (.int 64 (BitVec.ofNat 64 i)))
    (hframe : B8Frame env e o blk0 nblk)
    (hread : readBytes s.mem (e + 8 * i) 8 = some (natToBytes (0 : BitVec 64).toNat 8))
    (hi63 : i < 2 ^ 63) :
    ∃ (env' : Env),
      Jumps entryB3Function 1 (withEnv env s) (withEnv env' (b8AdvanceAt s s.mem "for.body")) ∧
      B8Frame env' e o blk0 nblk ∧
      lookupName env' "%i.010" = some (.int 64 (BitVec.ofNat 64 i)) ∧
      lookupName env' "%k.addr.011" = some (.int 64 (BitVec.ofNat 64 k)) := by
  obtain ⟨e1, hbody1, hjump1, hi1, hk1, h0, hb1⟩ :=
    b3Body_step_zero env s 0 i k e p opk opi hpc hpre hopk hopi hvk hvi hframe.ent hread hi63 rfl
  have hpr := b8_preserved b3Body.instrs ["%ent", "%blk0", "%nblk", "%out"] (by decide)
    (withEnv env s) (withEnv e1 s) hbody1
  have hE : lookupName e1 "%ent" = lookupName env "%ent" := by
    have h := hpr "%ent" (by decide); simpa only [withEnv] using h
  have hB : lookupName e1 "%blk0" = lookupName env "%blk0" := by
    have h := hpr "%blk0" (by decide); simpa only [withEnv] using h
  have hN : lookupName e1 "%nblk" = lookupName env "%nblk" := by
    have h := hpr "%nblk" (by decide); simpa only [withEnv] using h
  have hO : lookupName e1 "%out" = lookupName env "%out" := by
    have h := hpr "%out" (by decide); simpa only [withEnv] using h
  exact ⟨e1, Jumps.one hjump1, hframe.of_preserved hE hB hN hO, hi1, hk1⟩

/-- The steps a block takes: the body, one or two slot groups, the tail when the
word is long, and the join's branch to `cleanup`. -/
def b3BlockSteps (w : BitVec 64) : Nat :=
  if ctpop w = 0 then 3
  else if ctpop w ≤ 3 then 3
  else if ctpop w ≤ 7 then 4
  else 6 + (ctpop w - 7)

theorem b3BlockSteps_of_le3 (w : BitVec 64) (h : ctpop w ≤ 3) : b3BlockSteps w = 3 := by
  rw [b3BlockSteps]
  by_cases h0 : ctpop w = 0
  · rw [ite_eq_left h0]
  · rw [ite_eq_right h0, ite_eq_left h]

theorem b3BlockSteps_of_le7 (w : BitVec 64) (h3 : ¬ ctpop w ≤ 3) (h7 : ctpop w ≤ 7) :
    b3BlockSteps w = 4 := by
  rw [b3BlockSteps]
  have h0 : ¬ ctpop w = 0 := by omega
  rw [ite_eq_right h0, ite_eq_right h3, ite_eq_left h7]

theorem b3BlockSteps_of_gt7 (w : BitVec 64) (h7 : ¬ ctpop w ≤ 7) :
    b3BlockSteps w = 6 + (ctpop w - 7) := by
  rw [b3BlockSteps]
  have h0 : ¬ ctpop w = 0 := by omega
  have h3 : ¬ ctpop w ≤ 3 := by omega
  rw [ite_eq_right h0, ite_eq_right h3, ite_eq_right h7]

theorem b3BlockSteps_le (w : BitVec 64) : b3BlockSteps w ≤ 63 := by
  by_cases h0 : ctpop w = 0
  · rw [b3BlockSteps, ite_eq_left h0]; omega
  · by_cases h3 : ctpop w ≤ 3
    · rw [b3BlockSteps_of_le3 w h3]; omega
    · by_cases h7 : ctpop w ≤ 7
      · rw [b3BlockSteps_of_le7 w h3 h7]; omega
      · rw [b3BlockSteps_of_gt7 w h7]
        have := ctpop_le w; omega

theorem b3BlockSteps_zero : b3BlockSteps (0 : BitVec 64) = 3 := by
  rw [b3BlockSteps]
  rw [ite_eq_left (by decide)]

/-- A non-zero word's block, up to `cleanup`: three or seven fixed slots, the
tail when the word is long, and the join's cursor addition.  The memory gains
exactly `b3Len` lanes from the cursor. -/
theorem b3Block_pos_run (env : Env) (s : State) (w : BitVec 64) (i blk0 k o : Nat)
    (nblk : Nat) (p : String) (opk opi : Operand)
    (hpc : s.pc = "for.body")
    (hpre : s.pre = some p)
    (hopk : phiIncoming p pos8IncomingK = some opk)
    (hopi : phiIncoming p pos8IncomingI = some opi)
    (hvk : evalOperand (withEnv env s) opk = some (.int 64 (BitVec.ofNat 64 k)))
    (hvi : evalOperand (withEnv (("%k.addr.011", .int 64 (BitVec.ofNat 64 k)) :: env) s) opi
            = some (.int 64 (BitVec.ofNat 64 i)))
    (hent : lookupName env "%ent" = some (.ptr e))
    (hread : readBytes s.mem (e + 8 * i) 8 = some (natToBytes w.toNat 8))
    (hw : w ≠ 0)
    (hi63 : i < 2 ^ 63)
    (hk63 : k + 64 ≤ 2 ^ 63)
    (hblk : posBase blk0 i + 64 ≤ 2 ^ 32)
    (hconv : BitVec.ofNat 32 ((BitVec.ofNat 64 i + BitVec.ofNat 64 blk0).toNat % 2 ^ 32) <<< 6
              = BitVec.ofNat 32 (posBase blk0 i))
    (hsum : ctpop w + k < 2 ^ 64)
    (hframe : B8Frame env e o blk0 nblk) :
    ∃ (env' : Env) (M' : Mem),
      Jumps entryB3Function (b3BlockSteps w) (withEnv env s)
        (withEnv env' (b8AdvanceAt s M' "s1f_ke_b3.exit")) ∧
      b3BlockSteps w ≤ 63 ∧
      B8Frame env' e o blk0 nblk ∧
      lookupName env' "%add1" = some (.int 64 (BitVec.ofNat 64 (ctpop w + k))) ∧
      lookupName env' "%i.010" = some (.int 64 (BitVec.ofNat 64 i)) ∧
      M' = b8Lanes o w (posBase blk0 i) k 0 (b3Len w) s.mem := by
  obtain ⟨e1, hbody1, hjump1, hi1, hk1, h0, hb1⟩ :=
    b3Body_step_pos env s w i k e p opk opi hpc hpre hopk hopi hvk hvi hent hread hi63 hw
  have hpr := b8_preserved b3Body.instrs ["%ent", "%blk0", "%nblk", "%out"] (by decide)
    (withEnv env s) (withEnv e1 s) hbody1
  have hE : lookupName e1 "%ent" = lookupName env "%ent" := by
    have h := hpr "%ent" (by decide); simpa only [withEnv] using h
  have hB : lookupName e1 "%blk0" = lookupName env "%blk0" := by
    have h := hpr "%blk0" (by decide); simpa only [withEnv] using h
  have hN : lookupName e1 "%nblk" = lookupName env "%nblk" := by
    have h := hpr "%nblk" (by decide); simpa only [withEnv] using h
  have hO : lookupName e1 "%out" = lookupName env "%out" := by
    have h := hpr "%out" (by decide); simpa only [withEnv] using h
  have hBk1 : lookupName e1 "%blk0" = some (.int 64 (BitVec.ofNat 64 blk0)) := hB.trans hframe.blk0
  have hOu1 : lookupName e1 "%out" = some (.ptr o) := hO.trans hframe.out
  have hctx1 : B8Ctx e1 e o blk0 nblk i k := hframe.ctx hE hB hN hO hi1 hk1
  obtain ⟨sK, hsK⟩ : ∃ t : State, t = { s with pc := "if.end", pre := some "for.body" } := ⟨_, rfl⟩
  have hpcK : sK.pc = "if.end" := by rw [hsK]
  obtain ⟨e2, hbody2, h1, hand, hconv2, hptr, hcmp⟩ :=
    b3Kernel_run e1 sK w i blk0 k o hi1 hBk1 hOu1 hk1 h0 hk63 hblk hconv
  have hctx2 : B8Ctx e2 e o blk0 nblk i k :=
    hctx1.transfer (b8_keep b3Kernel.instrs (by decide) _ _ hbody2)
  obtain ⟨sK', hsK'⟩ :
      ∃ t : State, t = { sK with mem := b8Lanes o w (posBase blk0 i) k 0 3 sK.mem } := ⟨_, rfl⟩
  have hbody2' : denoteCode entryCalls b3Kernel.instrs (withEnv e1 sK) = some (withEnv e2 sK') := by
    rw [hsK']; exact hbody2
  have hsk : sK.mem = s.mem := by rw [hsK]
  have hnextK : sK.next = s.next := by rw [hsK]
  have henvK : sK.env = s.env := by rw [hsK]
  have hpreK : (withEnv e2 sK').pc = "if.end" := by rw [hsK']; exact hpcK
  rw [← hsK] at hjump1
  by_cases h3 : ctpop w ≤ 3
  · -- at most three set lanes: the first group is the whole block
    have hlt : BitVec.ult (BitVec.ofNat 64 (ctpop w)) (BitVec.ofInt 64 4) = true := by
      rw [show (BitVec.ofInt 64 4 : BitVec 64) = BitVec.ofNat 64 4 from by decide]
      rw [BitVec.ult, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by have := ctpop_le w; omega), Nat.mod_eq_of_lt (by decide)]
      exact decide_eq_true (show ctpop w < 4 by omega)
    have hbit : BitVec.ofBool
        (BitVec.ult (BitVec.ofNat 64 (ctpop w)) (BitVec.ofInt 64 4)) = (1 : BitVec 1) := by
      rw [hlt]; rfl
    obtain ⟨sJ, hsJ⟩ :
        ∃ t : State, t = { sK with mem := b8Lanes o w (posBase blk0 i) k 0 3 sK.mem, pc := "s1f_ke_b3.exit", pre := some "if.end" } := ⟨_, rfl⟩
    have hSJ : ({ sK' with pc := "s1f_ke_b3.exit", pre := some "if.end" } : State) = sJ := by
      rw [hsK', hsJ, hsk]
    have hjump2 : step entryCalls entryB3Function (withEnv e1 sK) = .jump (withEnv e2 sJ) := by
      rw [b3_step_of (withEnv e1 sK) "if.end" b3Kernel (withEnv e2 sK') hpcK
        findBlock_b3Kernel hbody2']
      show execTerm (withEnv e2 sK')
        (.condbr (.reg "%cmp.i") "s1f_ke_b3.exit" "if.end14.i") = _
      rw [execTerm_condbr_true (c := .reg "%cmp.i") (t := "s1f_ke_b3.exit") (f := "if.end14.i")
        (JsonB8Steps.evalOperand_reg_of e2 sK' "%cmp.i" (.int 1 _) hcmp) hbit]
      rw [hpreK, withEnv_jump, hSJ]
    obtain ⟨e3, hjoin3, hadd1⟩ := b3Join_run e2 sJ (ctpop w) k "if.end" (reg "%1")
      (by rw [hsJ])
      (by simp [b3IncomingR, phiIncoming])
      (JsonB8Steps.evalOperand_reg_of e2 sJ "%1" (.int 64 (BitVec.ofNat 64 (ctpop w))) h1)
      (by show lookupName e2 "%k.addr.011" = some (.int 64 (BitVec.ofNat 64 k))
          exact hctx2.k011)
      hsum
    have hctx3 : B8Ctx e3 e o blk0 nblk i k :=
      hctx2.transfer (b8_keep b3Join.instrs (by decide) _ _ hjoin3)
    have hii3 : lookupName e3 "%i.010" = some (.int 64 (BitVec.ofNat 64 i)) :=
      (denoteCode_lookupName entryCalls b3Join.instrs "%i.010" (by decide) _ _ hjoin3).trans hctx2.i010
    obtain ⟨sA, hsA⟩ :
        ∃ t : State, t = b8AdvanceAt s (b8Lanes o w (posBase blk0 i) k 0 3 sK.mem)
          "s1f_ke_b3.exit" := ⟨_, rfl⟩
    have hSA : ({ sJ with pc := "cleanup", pre := some "s1f_ke_b3.exit" } : State) = sA := by
      rw [hsJ, hsA, hnextK, henvK, hsk]
      simp only [b8AdvanceAt]
    have hjump3 : step entryCalls entryB3Function (withEnv e2 sJ) = .jump (withEnv e3 sA) := by
      rw [b3_step_of (withEnv e2 sJ) "s1f_ke_b3.exit" b3Join (withEnv e3 sJ)
        (by rw [hsJ]; rfl) findBlock_b3Join hjoin3]
      show execTerm (withEnv e3 sJ) (.br "cleanup") = _
      rw [execTerm_br]
      rw [show (withEnv e3 sJ).pc = "s1f_ke_b3.exit" from by rw [hsJ]; rfl]
      rw [withEnv_jump, hSA]
    refine ⟨e3, b8Lanes o w (posBase blk0 i) k 0 (b3Len w) s.mem, ?_, ?_, hctx3.frame,
      hadd1, hii3, rfl⟩
    · rw [show b3BlockSteps w = 3 from b3BlockSteps_of_le3 w h3]
      have hJ := Jumps.comp (Jumps.one hjump1) (Jumps.one hjump2)
      have hJ2 := Jumps.comp hJ (Jumps.one hjump3)
      have hsl : b8Lanes o w (posBase blk0 i) k 0 3 sK.mem
          = b8Lanes o w (posBase blk0 i) k 0 (b3Len w) s.mem := by
        rw [hsk, b3Len_of_le3 hw h3]
      rw [hsA] at hJ2
      rw [hsl] at hJ2
      exact hJ2
    · rw [show b3BlockSteps w = 3 from b3BlockSteps_of_le3 w h3]; omega
  · by_cases h7 : ctpop w ≤ 7
    · -- four to seven lanes: the second group reaches the join
      have hlt4 : BitVec.ult (BitVec.ofNat 64 (ctpop w)) (BitVec.ofInt 64 4) = false := by
        rw [show (BitVec.ofInt 64 4 : BitVec 64) = BitVec.ofNat 64 4 from by decide]
        rw [BitVec.ult, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt (by have := ctpop_le w; omega), Nat.mod_eq_of_lt (by decide)]
        exact decide_eq_false (show ¬ ctpop w < 4 by omega)
      have hbit : BitVec.ofBool
          (BitVec.ult (BitVec.ofNat 64 (ctpop w)) (BitVec.ofInt 64 4)) = (0 : BitVec 1) := by
        rw [hlt4]; rfl
      obtain ⟨sK2, hsK2⟩ :
          ∃ t : State, t = { sK' with pc := "if.end14.i", pre := some "if.end" } := ⟨_, rfl⟩
      have hS2 : ({ sK' with pc := "if.end14.i", pre := some "if.end" } : State) = sK2 := by
        rw [hsK2]
      have hjump2 : step entryCalls entryB3Function (withEnv e1 sK) = .jump (withEnv e2 sK2) := by
        rw [b3_step_of (withEnv e1 sK) "if.end" b3Kernel (withEnv e2 sK') hpcK
          findBlock_b3Kernel hbody2']
        show execTerm (withEnv e2 sK')
          (.condbr (.reg "%cmp.i") "s1f_ke_b3.exit" "if.end14.i") = _
        rw [execTerm_condbr_false (c := .reg "%cmp.i") (t := "s1f_ke_b3.exit")
          (f := "if.end14.i")
          (JsonB8Steps.evalOperand_reg_of e2 sK' "%cmp.i" (.int 1 _) hcmp) hbit]
        rw [hpreK, withEnv_jump, hS2]
      have hpcK2 : sK2.pc = "if.end14.i" := by rw [hsK2]
      obtain ⟨e3, hbody3, hand29, hcmp35⟩ :=
        b3Kernel2_run e2 sK2 w i blk0 k o hconv2 hptr h1 hand (Or.inr trivial)
      have hctx3 : B8Ctx e3 e o blk0 nblk i k :=
        hctx2.transfer (b8_keep b3Kernel2.instrs (by decide) _ _ hbody3)
      obtain ⟨sK2', hsK2'⟩ :
          ∃ t : State, t = { sK2 with mem := b8Lanes o w (posBase blk0 i) k 3 4 sK2.mem } :=
        ⟨_, rfl⟩
      have hbody3' : denoteCode entryCalls b3Kernel2.instrs (withEnv e2 sK2)
          = some (withEnv e3 sK2') := by
        rw [hsK2']; exact hbody3
      have hpreK2 : (withEnv e3 sK2').pc = "if.end14.i" := by rw [hsK2']; exact hpcK2
      have hs2mem : sK2.mem = b8Lanes o w (posBase blk0 i) k 0 3 s.mem := by
        rw [hsK2, hsK', hsk]
      have hlt8 : BitVec.ult (BitVec.ofNat 64 (ctpop w)) (BitVec.ofInt 64 8) = true := by
        rw [show (BitVec.ofInt 64 8 : BitVec 64) = BitVec.ofNat 64 8 from by decide]
        rw [BitVec.ult, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt (by have := ctpop_le w; omega), Nat.mod_eq_of_lt (by decide)]
        exact decide_eq_true (show ctpop w < 8 by omega)
      have hbit35 : BitVec.ofBool
          (BitVec.ult (BitVec.ofNat 64 (ctpop w)) (BitVec.ofInt 64 8)) = (1 : BitVec 1) := by
        rw [hlt8]; rfl
      obtain ⟨sJ, hsJ⟩ :
          ∃ t : State, t = { sK2 with mem := b8Lanes o w (posBase blk0 i) k 3 4 sK2.mem, pc := "s1f_ke_b3.exit", pre := some "if.end14.i" } := ⟨_, rfl⟩
      have hSJ : ({ sK2' with pc := "s1f_ke_b3.exit", pre := some "if.end14.i" } : State)
          = sJ := by
        rw [hsK2', hsJ]
      have hjump3 : step entryCalls entryB3Function (withEnv e2 sK2) = .jump (withEnv e3 sJ) := by
        rw [b3_step_of (withEnv e2 sK2) "if.end14.i" b3Kernel2 (withEnv e3 sK2') hpcK2
          findBlock_b3Kernel2 hbody3']
        show execTerm (withEnv e3 sK2')
          (.condbr (.reg "%cmp35.i") "s1f_ke_b3.exit" "if.end38.i") = _
        rw [execTerm_condbr_true (c := .reg "%cmp35.i") (t := "s1f_ke_b3.exit")
          (f := "if.end38.i")
          (JsonB8Steps.evalOperand_reg_of e3 sK2' "%cmp35.i" (.int 1 _) hcmp35) hbit35]
        rw [hpreK2, withEnv_jump, hSJ]
      obtain ⟨e4, hjoin4, hadd1⟩ := b3Join_run e3 sJ (ctpop w) k "if.end14.i" (reg "%1")
        (by rw [hsJ])
        (by simp [b3IncomingR, phiIncoming])
        (JsonB8Steps.evalOperand_reg_of e3 sJ "%1" (.int 64 (BitVec.ofNat 64 (ctpop w)))
          ((denoteCode_lookupName entryCalls b3Kernel2.instrs "%1" (by decide)
            (withEnv e2 sK2) (withEnv e3 sK2') hbody3').trans h1))
        (by show lookupName e3 "%k.addr.011" = some (.int 64 (BitVec.ofNat 64 k))
            exact hctx3.k011)
        hsum
      have hctx4 : B8Ctx e4 e o blk0 nblk i k :=
        hctx3.transfer (b8_keep b3Join.instrs (by decide) _ _ hjoin4)
      have hii4 : lookupName e4 "%i.010" = some (.int 64 (BitVec.ofNat 64 i)) :=
        (denoteCode_lookupName entryCalls b3Join.instrs "%i.010" (by decide) _ _ hjoin4).trans hctx3.i010
      obtain ⟨sA, hsA⟩ :
          ∃ t : State, t = b8AdvanceAt s
            (b8Lanes o w (posBase blk0 i) k 3 4 sK2.mem) "s1f_ke_b3.exit" := ⟨_, rfl⟩
      have hSA : ({ sJ with pc := "cleanup", pre := some "s1f_ke_b3.exit" } : State) = sA := by
        rw [hsJ, hsA]
        simp only [hsK2, hsK', hsK, b8AdvanceAt]
      have hjump4 : step entryCalls entryB3Function (withEnv e3 sJ) = .jump (withEnv e4 sA) := by
        rw [b3_step_of (withEnv e3 sJ) "s1f_ke_b3.exit" b3Join (withEnv e4 sJ)
          (by rw [hsJ]; rfl) findBlock_b3Join hjoin4]
        show execTerm (withEnv e4 sJ) (.br "cleanup") = _
        rw [execTerm_br]
        rw [show (withEnv e4 sJ).pc = "s1f_ke_b3.exit" from by rw [hsJ]; rfl]
        rw [withEnv_jump, hSA]
      have hsl : b8Lanes o w (posBase blk0 i) k 3 4 sK2.mem
          = b8Lanes o w (posBase blk0 i) k 0 (b3Len w) s.mem := by
        rw [hs2mem, b3Len_of_le7 h3 h7]
        exact (b8Lanes_split o w (posBase blk0 i) k 0 3 4 s.mem).symm
      refine ⟨e4, b8Lanes o w (posBase blk0 i) k 3 4 sK2.mem, ?_, ?_, hctx4.frame,
        hadd1, hii4, hsl⟩
      · rw [show b3BlockSteps w = 4 from b3BlockSteps_of_le7 w h3 h7]
        have hJ := Jumps.comp (Jumps.one hjump1) (Jumps.one hjump2)
        have hJ2 := Jumps.comp hJ (Jumps.one hjump3)
        have hJ3 := Jumps.comp hJ2 (Jumps.one hjump4)
        rw [hsA] at hJ3
        exact hJ3
      · rw [show b3BlockSteps w = 4 from b3BlockSteps_of_le7 w h3 h7]; omega
    · -- eight lanes and above: the second test reaches the tail
      have hlt4 : BitVec.ult (BitVec.ofNat 64 (ctpop w)) (BitVec.ofInt 64 4) = false := by
        rw [show (BitVec.ofInt 64 4 : BitVec 64) = BitVec.ofNat 64 4 from by decide]
        rw [BitVec.ult, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt (by have := ctpop_le w; omega), Nat.mod_eq_of_lt (by decide)]
        exact decide_eq_false (show ¬ ctpop w < 4 by omega)
      have hbit : BitVec.ofBool
          (BitVec.ult (BitVec.ofNat 64 (ctpop w)) (BitVec.ofInt 64 4)) = (0 : BitVec 1) := by
        rw [hlt4]; rfl
      obtain ⟨sK2, hsK2⟩ :
          ∃ t : State, t = { sK' with pc := "if.end14.i", pre := some "if.end" } := ⟨_, rfl⟩
      have hS2 : ({ sK' with pc := "if.end14.i", pre := some "if.end" } : State) = sK2 := by
        rw [hsK2]
      have hjump2 : step entryCalls entryB3Function (withEnv e1 sK) = .jump (withEnv e2 sK2) := by
        rw [b3_step_of (withEnv e1 sK) "if.end" b3Kernel (withEnv e2 sK') hpcK
          findBlock_b3Kernel hbody2']
        show execTerm (withEnv e2 sK')
          (.condbr (.reg "%cmp.i") "s1f_ke_b3.exit" "if.end14.i") = _
        rw [execTerm_condbr_false (c := .reg "%cmp.i") (t := "s1f_ke_b3.exit")
          (f := "if.end14.i")
          (JsonB8Steps.evalOperand_reg_of e2 sK' "%cmp.i" (.int 1 _) hcmp) hbit]
        rw [hpreK, withEnv_jump, hS2]
      have hpcK2 : sK2.pc = "if.end14.i" := by rw [hsK2]
      obtain ⟨e3, hbody3, hand29, hcmp35⟩ :=
        b3Kernel2_run e2 sK2 w i blk0 k o hconv2 hptr h1 hand (Or.inr trivial)
      have hctx3 : B8Ctx e3 e o blk0 nblk i k :=
        hctx2.transfer (b8_keep b3Kernel2.instrs (by decide) _ _ hbody3)
      obtain ⟨sK2', hsK2'⟩ :
          ∃ t : State, t = { sK2 with mem := b8Lanes o w (posBase blk0 i) k 3 4 sK2.mem } :=
        ⟨_, rfl⟩
      have hbody3' : denoteCode entryCalls b3Kernel2.instrs (withEnv e2 sK2)
          = some (withEnv e3 sK2') := by
        rw [hsK2']; exact hbody3
      have hpreK2 : (withEnv e3 sK2').pc = "if.end14.i" := by rw [hsK2']; exact hpcK2
      have hs2mem : sK2.mem = b8Lanes o w (posBase blk0 i) k 0 3 s.mem := by
        rw [hsK2, hsK', hsk]
      have hlt8 : BitVec.ult (BitVec.ofNat 64 (ctpop w)) (BitVec.ofInt 64 8) = false := by
        rw [show (BitVec.ofInt 64 8 : BitVec 64) = BitVec.ofNat 64 8 from by decide]
        rw [BitVec.ult, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt (by have := ctpop_le w; omega), Nat.mod_eq_of_lt (by decide)]
        exact decide_eq_false (show ¬ ctpop w < 8 by omega)
      have hbit35 : BitVec.ofBool
          (BitVec.ult (BitVec.ofNat 64 (ctpop w)) (BitVec.ofInt 64 8)) = (0 : BitVec 1) := by
        rw [hlt8]; rfl
      obtain ⟨sG, hsG⟩ :
          ∃ t : State, t = { sK2 with mem := b8Lanes o w (posBase blk0 i) k 3 4 sK2.mem, pc := "if.end38.i", pre := some "if.end14.i" } := ⟨_, rfl⟩
      have hSG : ({ sK2' with pc := "if.end38.i", pre := some "if.end14.i" } : State)
          = sG := by
        rw [hsK2', hsG]
      have hjump3 : step entryCalls entryB3Function (withEnv e2 sK2) = .jump (withEnv e3 sG) := by
        rw [b3_step_of (withEnv e2 sK2) "if.end14.i" b3Kernel2 (withEnv e3 sK2') hpcK2
          findBlock_b3Kernel2 hbody3']
        show execTerm (withEnv e3 sK2')
          (.condbr (.reg "%cmp35.i") "s1f_ke_b3.exit" "if.end38.i") = _
        rw [execTerm_condbr_false (c := .reg "%cmp35.i") (t := "s1f_ke_b3.exit")
          (f := "if.end38.i")
          (JsonB8Steps.evalOperand_reg_of e3 sK2' "%cmp35.i" (.int 1 _) hcmp35) hbit35]
        rw [hpreK2, withEnv_jump, hSG]
      have hpcG : sG.pc = "if.end38.i" := by rw [hsG]
      have hgm : sG.mem = b8Lanes o w (posBase blk0 i) k 0 7 s.mem := by
        rw [hsG]
        show b8Lanes o w (posBase blk0 i) k 3 4 sK2.mem
          = b8Lanes o w (posBase blk0 i) k 0 7 s.mem
        rw [hs2mem]
        exact (b8Lanes_split o w (posBase blk0 i) k 0 3 4 s.mem).symm
      have hpop : 8 ≤ ctpop w := by omega
      have hptr3 : lookupName e3 "%add.ptr" = some (.ptr (o + 4 * k)) :=
        (denoteCode_lookupName entryCalls b3Kernel2.instrs "%add.ptr" (by decide)
          (withEnv e2 sK2) (withEnv e3 sK2') hbody3').trans hptr
      have hconv3 : lookupName e3 "%conv"
          = some (.int 32 (BitVec.ofNat 32 (posBase blk0 i))) :=
        (denoteCode_lookupName entryCalls b3Kernel2.instrs "%conv" (by decide)
          (withEnv e2 sK2) (withEnv e3 sK2') hbody3').trans hconv2
      have hi3t : lookupName e3 "%i.010" = some (.int 64 (BitVec.ofNat 64 i)) :=
        (denoteCode_lookupName entryCalls b3Kernel2.instrs "%i.010" (by decide)
          (withEnv e2 sK2) (withEnv e3 sK2') hbody3').trans hctx2.i010
      obtain ⟨e4, hJumps4, hadd1, hi4, hctx4⟩ :=
        b3Tail_run w e i blk0 k o e3 sG s.mem
          nblk "if.end14.i"
          hpcG hand29 hptr3 hconv3 hi3t hctx3.k011 hctx3.nblk hctx3 hpop hk63 hgm
      obtain ⟨sT, hsT⟩ :
          ∃ t : State, t = b8AdvanceAt s
            (b8Lanes o w (posBase blk0 i) k 0 (ctpop w) s.mem) "s1f_ke_b3.exit" := ⟨_, rfl⟩
      have hst : b8AdvanceAt sG
          (b8Lanes o w (posBase blk0 i) k 0 (ctpop w) s.mem) "s1f_ke_b3.exit" = sT := by
        rw [hsG, hsT]
        simp only [hsK2, hsK', hsK, b8AdvanceAt]
      rw [hst] at hJumps4
      have hsl : b8Lanes o w (posBase blk0 i) k 0 (ctpop w) s.mem
          = b8Lanes o w (posBase blk0 i) k 0 (b3Len w) s.mem := by
        rw [b3Len_of_ge8 hpop]
      refine ⟨e4, b8Lanes o w (posBase blk0 i) k 0 (ctpop w) s.mem, ?_, ?_, hctx4.frame,
        hadd1, hi4, hsl⟩
      · rw [show b3BlockSteps w = ((1 + 1) + 1) + (3 + (ctpop w - 7)) from by
          rw [b3BlockSteps_of_gt7 w h7]; omega]
        have hJ := Jumps.comp (Jumps.one hjump1) (Jumps.one hjump2)
        have hJ2 := Jumps.comp hJ (Jumps.one hjump3)
        have hJ3 := Jumps.comp hJ2 hJumps4
        rw [hsT] at hJ3
        exact hJ3
      · rw [show b3BlockSteps w = 6 + (ctpop w - 7) from b3BlockSteps_of_gt7 w h7]
        have := ctpop_le w; omega

/-! ### The block loop

Each block's own run is bounded by `b3BlockSteps`; the loop adds one `cleanup`
step per block and one exit, so its fuel is the stream's step count plus the
block count plus one. -/

/-- The B3 function's own jump and return steps. -/
theorem b3_runFuel_jump {s s' : State} {n : Nat}
    (h : step entryCalls entryB3Function s = .jump s') :
    runFuel entryCalls (n + 1) entryB3Function s = runFuel entryCalls n entryB3Function s' := by
  simp [runFuel, h]

theorem b3_runFuel_ret {s s' : State} {v : Option Value} {n : Nat}
    (h : step entryCalls entryB3Function s = .ret v s') :
    runFuel entryCalls (n + 1) entryB3Function s = some (.ret v s'.mem) := by
  simp [runFuel, h]

/-- The stream's fold, one element further. -/
theorem b3MemFold_succ (ent : List (BitVec 64)) (blk0 k0 o i : Nat) (mem0 : Mem)
    (hi : i < ent.length) :
    b3MemFold o (64 * blk0) k0 (ent.take (i + 1)) mem0
      = b3BlockStore o (ent.get ⟨i, hi⟩) (posBase blk0 i) (pos8Cursor (ent.take i) k0)
          (b3MemFold o (64 * blk0) k0 (ent.take i) mem0) := by
  rw [pos8_take_succ ent i hi, b3MemFold_append]
  rw [pos8_take_length ent i (by omega)]
  rw [show 64 * blk0 + 64 * i = posBase blk0 i from by rw [posBase]; omega]
  rfl

/-- The mask word a block's iteration reads, out of the stream's fold. -/
theorem b3_read_word (ent : List (BitVec 64)) (blk0 k0 o e i : Nat) (mem0 : Mem)
    (hwords : readBytes mem0 e (8 * ent.length) = some (wordsOf ent))
    (hdisj : e + 8 * ent.length ≤ o ∨ o + 4 * (k0 + 64 * ent.length + 8) ≤ e)
    (hi : i < ent.length) :
    readBytes (b3MemFold o (64 * blk0) k0 (ent.take i) mem0) (e + 8 * i) 8
      = some (natToBytes (ent.get ⟨i, hi⟩).toNat 8) := by
  have h0 := readBytes_wordsOf mem0 e ent hwords i hi
  have hfr := b3MemFold_frame o (64 * blk0) k0 (ent.take i) mem0 (e + 8 * i) 8 (by
    rcases hdisj with h | h
    · left; omega
    · right
      have hc : pos8Cursor (ent.take i) k0 ≤ k0 + 64 * i := by
        have h1 := pos8Cursor_le (ent.take i) k0
        rwa [pos8_take_length ent i (by omega)] at h1
      omega)
  rw [hfr]; exact h0

/-- The steps the remaining blocks take, block after block. -/
def b3RunSteps : List (BitVec 64) → Nat
  | [] => 0
  | w :: ws => b3BlockSteps w + b3RunSteps ws

theorem b3RunSteps_drop_succ (ent : List (BitVec 64)) (i : Nat) (hi : i < ent.length) :
    b3RunSteps (ent.drop i) = b3BlockSteps (ent.get ⟨i, hi⟩) + b3RunSteps (ent.drop (i + 1)) := by
  rw [List.drop_eq_getElem_cons hi]
  rfl

/-- **The block loop.**  From `for.body` with `r` blocks left, the loop runs to
the exit and returns the stream's cursor, with the fold of every block's stores
as its memory.  Each block's own run is bounded by `b3BlockSteps`, and its
`cleanup` step is the one that follows. -/
theorem b3_loop_run (ent : List (BitVec 64)) (blk0 nblk k0 o e : Nat) (mem0 : Mem)
    (hwords : readBytes mem0 e (8 * ent.length) = some (wordsOf ent))
    (hblk : 64 * (blk0 + nblk) + 63 < 2 ^ 32)
    (hk63 : k0 + 64 * ent.length + 9 < 2 ^ 63)
    (hdisj : e + 8 * ent.length ≤ o ∨ o + 4 * (k0 + 64 * ent.length + 8) ≤ e)
    (hnblk : nblk = ent.length) :
    ∀ (r i k : Nat) (env : Env) (s : State) (p : String) (opk opi : Operand),
      1 ≤ r → i + r = nblk → s.pc = "for.body" → s.pre = some p →
      phiIncoming p pos8IncomingK = some opk → phiIncoming p pos8IncomingI = some opi →
      evalOperand (withEnv env s) opk = some (.int 64 (BitVec.ofNat 64 k)) →
      evalOperand (withEnv (("%k.addr.011", .int 64 (BitVec.ofNat 64 k)) :: env) s) opi
        = some (.int 64 (BitVec.ofNat 64 i)) →
      B8Frame env e o blk0 nblk →
      k = pos8Cursor (ent.take i) k0 →
      s.mem = b3MemFold o (64 * blk0) k0 (ent.take i) mem0 →
      ∃ (env' : Env) (mem' : Mem),
        runFuel entryCalls (b3RunSteps (ent.drop i) + r + 1) entryB3Function (withEnv env s)
          = some (.ret (some (.int 64 (BitVec.ofNat 64 (pos8Cursor (ent.drop i) k)))) mem') ∧
        mem' = b3MemFold o (64 * blk0) k0 ent mem0 := by
  intro r
  induction r with
  | zero => intro i k env s p opk opi hr _; exact absurd hr (by simp)
  | succ r' ih =>
    intro i k env s p opk opi hr hi hpc hpre hopk hopi hvk hvi hframe hk hmem
    have hilen : i < ent.length := by omega
    have hnblkpos : 1 ≤ nblk := by omega
    have hkle : k ≤ k0 + 64 * i := by
      rw [hk]
      have hc := pos8Cursor_le (ent.take i) k0
      rwa [pos8_take_length ent i (by omega)] at hc
    have hi63 : i < 2 ^ 63 := by omega
    have hi64 : i + 1 < 2 ^ 64 := by omega
    have hword : readBytes s.mem (e + 8 * i) 8 = some (natToBytes (ent.get ⟨i, hilen⟩).toNat 8) := by
      rw [hmem]; exact b3_read_word ent blk0 k0 o e i mem0 hwords hdisj hilen
    have hxeq : BitVec.ofNat 64 (i + 1) = BitVec.ofNat 64 nblk ↔ i + 1 = nblk :=
      ⟨fun h => ofNat64_inj (by omega) (by omega) h, fun h => by rw [h]⟩
    have hent_eq : ∀ _ : i + 1 = nblk, ent = ent.take (i + 1) := fun hlast => by
      have h1 : ent.take (i + 1) = ent.take nblk := by rw [hlast]
      rw [h1, hnblk, List.take_length]
    have hkNext : k + ctpop (ent.get ⟨i, hilen⟩) = pos8Cursor (ent.take (i + 1)) k0 := by
      rw [hk]; exact (pos8Cursor_take_succ ent k0 i hilen).symm
    by_cases hw : ent.get ⟨i, hilen⟩ = 0
    · -- the word is zero: the body takes the `continue` edge, and nothing is stored
      obtain ⟨e1, hjump1, hframe1, hi1, hk1⟩ :=
        b3Block_zero_run env s i k nblk e o blk0 p opk opi hpc hpre hopk hopi hvk hvi hframe
          (by rw [hword, hw]) hi63
      have hmem1 : s.mem = b3MemFold o (64 * blk0) k0 (ent.take (i + 1)) mem0 := by
        rw [hmem, b3MemFold_succ ent blk0 k0 o i mem0 hilen, hw, b3BlockStore_zero]
      obtain ⟨sC, hsC⟩ : ∃ t : State, t = b8AdvanceAt s s.mem "for.body" := ⟨_, rfl⟩
      rw [← hsC] at hjump1
      by_cases hlast : i + 1 = nblk
      · -- the last block: `cleanup` branches to the exit, which returns the cursor
        have hr0 : r' = 0 := by omega
        obtain ⟨e2, hbody2, hjump2, hk2, hinc2, hx2⟩ :=
          b3Advance_step_last e1 sC i k nblk "for.body" (reg "%k.addr.011") (by rw [hsC]; rfl) (by rw [hsC]; rfl) rfl
            (JsonB8Steps.evalOperand_reg_of e1 _ _ _ hk1) hi1 hframe1.nblk hi64 (hxeq.mpr hlast)
        obtain ⟨sX, hsX⟩ : ∃ t : State, t = { sC with pc := "for.cond.cleanup", pre := some "cleanup" } := ⟨_, rfl⟩
        obtain ⟨e3, hbody3, hjump3, hk3⟩ :=
          b3Exit_step e2 sX k "cleanup" (reg "%k.addr.1") (by rw [hsX]) (by rw [hsX]) rfl
            (JsonB8Steps.evalOperand_reg_of e2 _ _ _ hk2)
        rw [← hsX] at hjump2
        have hJ : Jumps entryB3Function 2 (withEnv env s) (withEnv e2 sX) :=
          Jumps.comp hjump1 (Jumps.one hjump2)
        have hdrop : ent.drop (i + 1) = [] := by rw [hlast, hnblk, List.drop_length]
        have hnil : b3RunSteps ([] : List (BitVec 64)) = 0 := rfl
        have hmemE : s.mem = b3MemFold o (64 * blk0) k0 ent mem0 :=
          hmem1.trans (congrArg (fun l => b3MemFold o (64 * blk0) k0 l mem0) (hent_eq hlast)).symm
        have hmemX : (withEnv e3 sX).mem = s.mem := by
          show sX.mem = s.mem
          rw [hsX]
          show sC.mem = s.mem
          rw [hsC]
          rfl
        refine ⟨e3, (withEnv e3 sX).mem, ?_, ?_⟩
        · refine runFuel_mono_le (n := 3) ?_ ?_
          · rw [b3RunSteps_drop_succ ent i hilen, hw, b3BlockSteps_zero, hr0, hdrop, hnil]; omega
          · rw [pos8Cursor_drop_succ ent k i hilen]
            show runFuel entryCalls 3 entryB3Function (withEnv env s)
              = some (.ret (some (.int 64 (BitVec.ofNat 64 (pos8Cursor (ent.drop (i + 1)) (k + ctpop (ent.get ⟨i, hilen⟩)))))) (withEnv e3 sX).mem)
            rw [hdrop, hw, ctpop_zero64, Nat.add_zero]
            rw [show pos8Cursor ([] : List (BitVec 64)) k = k from rfl]
            rw [show (3 : Nat) = 2 + 1 from rfl]
            rw [runFuel_of_Jumps hJ]
            exact b3_runFuel_ret (n := 0) hjump3
        · rw [hmemX]
          exact hmemE
      · -- the loop continues: `cleanup` branches back to `for.body`
        obtain ⟨e2, hbody2, hjump2, hk2, hinc2, hx2⟩ :=
          b3Advance_step_more e1 sC i k nblk "for.body" (reg "%k.addr.011") (by rw [hsC]; rfl) (by rw [hsC]; rfl) rfl
            (JsonB8Steps.evalOperand_reg_of e1 _ _ _ hk1) hi1 hframe1.nblk hi64
            (fun hcon => hlast (hxeq.mp hcon))
        have hprA := b8_preserved b3Advance.instrs ["%ent", "%blk0", "%nblk", "%out"] (by decide)
          (withEnv e1 sC) (withEnv e2 sC) hbody2
        have hE2 : lookupName e2 "%ent" = lookupName e1 "%ent" := by
          have h := hprA "%ent" (by decide); simpa only [withEnv] using h
        have hB2 : lookupName e2 "%blk0" = lookupName e1 "%blk0" := by
          have h := hprA "%blk0" (by decide); simpa only [withEnv] using h
        have hN2 : lookupName e2 "%nblk" = lookupName e1 "%nblk" := by
          have h := hprA "%nblk" (by decide); simpa only [withEnv] using h
        have hO2 : lookupName e2 "%out" = lookupName e1 "%out" := by
          have h := hprA "%out" (by decide); simpa only [withEnv] using h
        have hframe2 : B8Frame e2 e o blk0 nblk := hframe1.of_preserved hE2 hB2 hN2 hO2
        have hvk2 : evalOperand (withEnv e2 sC) (reg "%k.addr.1")
            = some (.int 64 (BitVec.ofNat 64 (k + ctpop (ent.get ⟨i, hilen⟩)))) := by
          simp only [reg]
          rw [JsonB8Steps.evalOperand_reg_of e2 sC "%k.addr.1" (.int 64 (BitVec.ofNat 64 k)) hk2]
          rw [hw, ctpop_zero64, Nat.add_zero]
        have hvi2 : evalOperand (withEnv (("%k.addr.011", .int 64 (BitVec.ofNat 64 (k + ctpop (ent.get ⟨i, hilen⟩)))) :: e2) sC) (reg "%inc")
            = some (.int 64 (BitVec.ofNat 64 (i + 1))) :=
          JsonB8Steps.evalOperand_reg_of (("%k.addr.011", .int 64 (BitVec.ofNat 64 (k + ctpop (ent.get ⟨i, hilen⟩)))) :: e2)
            sC "%inc" (.int 64 (BitVec.ofNat 64 (i + 1)))
            ((lookupName_cons_ne _ _ (by decide)).trans hinc2)
        have hmem2 : ({ sC with pc := "for.body", pre := some "cleanup" } : State).mem
            = b3MemFold o (64 * blk0) k0 (ent.take (i + 1)) mem0 := by
          show sC.mem = b3MemFold o (64 * blk0) k0 (ent.take (i + 1)) mem0
          rw [hsC]
          exact hmem1
        obtain ⟨e3, mem3, hrun3, hmem3⟩ :=
          ih (i + 1) (k + ctpop (ent.get ⟨i, hilen⟩)) e2
            { sC with pc := "for.body", pre := some "cleanup" }
            "cleanup" (reg "%k.addr.1") (reg "%inc")
            (by omega) (by omega) rfl rfl rfl rfl hvk2 hvi2 hframe2 hkNext hmem2
        refine ⟨e3, mem3, ?_, hmem3⟩
        rw [pos8Cursor_drop_succ ent k i hilen]
        refine runFuel_mono_le (n := 2 + (b3RunSteps (ent.drop (i + 1)) + r' + 1)) ?_ ?_
        · rw [b3RunSteps_drop_succ ent i hilen, hw, b3BlockSteps_zero]; omega
        · rw [runFuel_of_Jumps (Jumps.comp hjump1 (Jumps.one hjump2))]
          exact hrun3
    · -- a non-zero word: the fixed slots and, for a long word, the tail
      have hwne : ent.get ⟨i, hilen⟩ ≠ 0 := hw
      have hk63' : k + 64 ≤ 2 ^ 63 := by omega
      have hblk' : posBase blk0 i + 64 ≤ 2 ^ 32 := by
        have h1 : 64 * (blk0 + i) + 64 ≤ 64 * (blk0 + nblk) := by
          have h2 : blk0 + i + 1 ≤ blk0 + nblk := by omega
          calc 64 * (blk0 + i) + 64 = 64 * (blk0 + i + 1) := by omega
            _ ≤ 64 * (blk0 + nblk) := by omega
        rw [posBase_eq]
        omega
      have hconv : BitVec.ofNat 32 ((BitVec.ofNat 64 i + BitVec.ofNat 64 blk0).toNat % 2 ^ 32) <<< 6
          = BitVec.ofNat 32 (posBase blk0 i) := pos8_conv i blk0 (by omega)
      have hsum : ctpop (ent.get ⟨i, hilen⟩) + k < 2 ^ 64 := by
        have h1 := ctpop_le (ent.get ⟨i, hilen⟩)
        omega
      obtain ⟨e1, Mk, hjumps1, hsteps1le, hframe1, hadd1, hi1', hMk⟩ :=
        b3Block_pos_run env s (ent.get ⟨i, hilen⟩) i blk0 k o nblk p opk opi hpc hpre hopk hopi hvk hvi
          hframe.ent hword hwne hi63 hk63' hblk' hconv hsum hframe
      have hcomm : ctpop (ent.get ⟨i, hilen⟩) + k = k + ctpop (ent.get ⟨i, hilen⟩) := Nat.add_comm _ _
      have hadd1' : lookupName e1 "%add1"
          = some (.int 64 (BitVec.ofNat 64 (k + ctpop (ent.get ⟨i, hilen⟩)))) := by
        rw [hadd1, hcomm]
      have hmem1 : Mk = b3MemFold o (64 * blk0) k0 (ent.take (i + 1)) mem0 := by
        rw [hMk, hmem, b3MemFold_succ ent blk0 k0 o i mem0 hilen, hk,
          b3BlockStore_of_ne o (ent.get ⟨i, hilen⟩) (posBase blk0 i) (pos8Cursor (ent.take i) k0) _ hwne]
      obtain ⟨sC, hsC⟩ : ∃ t : State, t = b8AdvanceAt s Mk "s1f_ke_b3.exit" := ⟨_, rfl⟩
      rw [← hsC] at hjumps1
      by_cases hlast : i + 1 = nblk
      · have hr0 : r' = 0 := by omega
        obtain ⟨e2, hbody2, hjump2, hk2, hinc2, hx2⟩ :=
          b3Advance_step_last e1 sC i (k + ctpop (ent.get ⟨i, hilen⟩)) nblk "s1f_ke_b3.exit" (reg "%add1")
            (by rw [hsC]; rfl) (by rw [hsC]; rfl) rfl
            (JsonB8Steps.evalOperand_reg_of e1 _ _ _ hadd1') hi1' hframe1.nblk hi64 (hxeq.mpr hlast)
        obtain ⟨sX, hsX⟩ : ∃ t : State, t = { sC with pc := "for.cond.cleanup", pre := some "cleanup" } := ⟨_, rfl⟩
        obtain ⟨e3, hbody3, hjump3, hk3⟩ :=
          b3Exit_step e2 sX (k + ctpop (ent.get ⟨i, hilen⟩)) "cleanup" (reg "%k.addr.1") (by rw [hsX]) (by rw [hsX]) rfl
            (JsonB8Steps.evalOperand_reg_of e2 _ _ _ hk2)
        rw [← hsX] at hjump2
        have hJ : Jumps entryB3Function (b3BlockSteps (ent.get ⟨i, hilen⟩) + 1) (withEnv env s) (withEnv e2 sX) :=
          Jumps.comp hjumps1 (Jumps.one hjump2)
        have hdrop : ent.drop (i + 1) = [] := by rw [hlast, hnblk, List.drop_length]
        have hnil : b3RunSteps ([] : List (BitVec 64)) = 0 := rfl
        have hmemE : Mk = b3MemFold o (64 * blk0) k0 ent mem0 :=
          hmem1.trans (congrArg (fun l => b3MemFold o (64 * blk0) k0 l mem0) (hent_eq hlast)).symm
        have hmemX : (withEnv e3 sX).mem = Mk := by
          show sX.mem = Mk
          rw [hsX]
          show sC.mem = Mk
          rw [hsC]
          rfl
        refine ⟨e3, (withEnv e3 sX).mem, ?_, ?_⟩
        · refine runFuel_mono_le (n := (b3BlockSteps (ent.get ⟨i, hilen⟩) + 1) + 1) ?_ ?_
          · rw [b3RunSteps_drop_succ ent i hilen, hr0, hdrop, hnil]; omega
          · rw [pos8Cursor_drop_succ ent k i hilen]
            show runFuel entryCalls ((b3BlockSteps (ent.get ⟨i, hilen⟩) + 1) + 1) entryB3Function (withEnv env s)
              = some (.ret (some (.int 64 (BitVec.ofNat 64 (pos8Cursor (ent.drop (i + 1)) (k + ctpop (ent.get ⟨i, hilen⟩)))))) (withEnv e3 sX).mem)
            rw [hdrop]
            rw [show pos8Cursor ([] : List (BitVec 64)) (k + ctpop (ent.get ⟨i, hilen⟩)) = (k + ctpop (ent.get ⟨i, hilen⟩)) from rfl]
            rw [runFuel_of_Jumps hJ]
            exact b3_runFuel_ret (n := 0) hjump3
        · rw [hmemX]
          exact hmemE
      · obtain ⟨e2, hbody2, hjump2, hk2, hinc2, hx2⟩ :=
          b3Advance_step_more e1 sC i (k + ctpop (ent.get ⟨i, hilen⟩)) nblk "s1f_ke_b3.exit" (reg "%add1")
            (by rw [hsC]; rfl) (by rw [hsC]; rfl) rfl
            (JsonB8Steps.evalOperand_reg_of e1 _ _ _ hadd1') hi1' hframe1.nblk hi64
            (fun hcon => hlast (hxeq.mp hcon))
        have hprA := b8_preserved b3Advance.instrs ["%ent", "%blk0", "%nblk", "%out"] (by decide)
          (withEnv e1 sC) (withEnv e2 sC) hbody2
        have hE2 : lookupName e2 "%ent" = lookupName e1 "%ent" := by
          have h := hprA "%ent" (by decide); simpa only [withEnv] using h
        have hB2 : lookupName e2 "%blk0" = lookupName e1 "%blk0" := by
          have h := hprA "%blk0" (by decide); simpa only [withEnv] using h
        have hN2 : lookupName e2 "%nblk" = lookupName e1 "%nblk" := by
          have h := hprA "%nblk" (by decide); simpa only [withEnv] using h
        have hO2 : lookupName e2 "%out" = lookupName e1 "%out" := by
          have h := hprA "%out" (by decide); simpa only [withEnv] using h
        have hframe2 : B8Frame e2 e o blk0 nblk := hframe1.of_preserved hE2 hB2 hN2 hO2
        have hvk2 : evalOperand (withEnv e2 sC) (reg "%k.addr.1")
            = some (.int 64 (BitVec.ofNat 64 (k + ctpop (ent.get ⟨i, hilen⟩)))) :=
          JsonB8Steps.evalOperand_reg_of e2 sC "%k.addr.1" (.int 64 (BitVec.ofNat 64 (k + ctpop (ent.get ⟨i, hilen⟩)))) hk2
        have hvi2 : evalOperand (withEnv (("%k.addr.011", .int 64 (BitVec.ofNat 64 (k + ctpop (ent.get ⟨i, hilen⟩)))) :: e2) sC) (reg "%inc")
            = some (.int 64 (BitVec.ofNat 64 (i + 1))) :=
          JsonB8Steps.evalOperand_reg_of (("%k.addr.011", .int 64 (BitVec.ofNat 64 (k + ctpop (ent.get ⟨i, hilen⟩)))) :: e2)
            sC "%inc" (.int 64 (BitVec.ofNat 64 (i + 1)))
            ((lookupName_cons_ne _ _ (by decide)).trans hinc2)
        have hmem2 : ({ sC with pc := "for.body", pre := some "cleanup" } : State).mem
            = b3MemFold o (64 * blk0) k0 (ent.take (i + 1)) mem0 := by
          show sC.mem = b3MemFold o (64 * blk0) k0 (ent.take (i + 1)) mem0
          rw [hsC]
          exact hmem1
        obtain ⟨e3, mem3, hrun3, hmem3⟩ :=
          ih (i + 1) (k + ctpop (ent.get ⟨i, hilen⟩)) e2
            { sC with pc := "for.body", pre := some "cleanup" }
            "cleanup" (reg "%k.addr.1") (reg "%inc")
            (by omega) (by omega) rfl rfl rfl rfl hvk2 hvi2 hframe2 hkNext hmem2
        refine ⟨e3, mem3, ?_, hmem3⟩
        rw [pos8Cursor_drop_succ ent k i hilen]
        refine runFuel_mono_le
          (n := b3BlockSteps (ent.get ⟨i, hilen⟩) + 1 + (b3RunSteps (ent.drop (i + 1)) + r' + 1)) ?_ ?_
        · rw [b3RunSteps_drop_succ ent i hilen]; omega
        · rw [runFuel_of_Jumps (Jumps.comp hjumps1 (Jumps.one hjump2))]
          exact hrun3

/-! ### The entry stream -/

/-- The initial state's five parameter cells and its block. -/
theorem b3_init (blk0 nblk k : Nat) (mem : Mem) (e o : Nat) :
    let S0 : State := { (initState entryB3Function
      [.ptr e, .int 64 blk0, .int 64 nblk, .ptr o, .int 64 k]) with mem := mem }
    S0.pc = "entry" ∧
      lookupName S0.env "%ent" = some (.ptr e) ∧
      lookupName S0.env "%blk0" = some (.int 64 (BitVec.ofNat 64 blk0)) ∧
      lookupName S0.env "%nblk" = some (.int 64 (BitVec.ofNat 64 nblk)) ∧
      lookupName S0.env "%out" = some (.ptr o) ∧
      lookupName S0.env "%k" = some (.int 64 (BitVec.ofNat 64 k)) := by
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [initState, entryB3Function, b3Entry, b3LoopExit, b3Body, b3Kernel, b3Kernel2,
      b3TailGuard, b3TailPreheader, b3TailLoop, b3Join, b3Advance, List.zip, List.map, lookupName]

theorem b3Entry_body (env : Env) (s : State) (nblk : Nat)
    (hnblk : lookupName env "%nblk" = some (.int 64 (BitVec.ofNat 64 nblk))) :
    ∃ env', denoteCode entryCalls b3Entry.instrs (withEnv env s) = some (withEnv env' s) ∧
      lookupName env' "%cmp9.not" = some (.int 1 (BitVec.ofBool (BitVec.ofNat 64 nblk = 0))) := by
  refine ⟨?env', ?hrun, ?hnot⟩
  case hrun =>
    simp only [b3Entry, reg, lit]
    ent_step (step_icmp_eq_imm env s "%cmp9.not" "%nblk" 64 (BitVec.ofNat 64 nblk)
      (BitVec.ofInt 64 0) (by ent_auto))
    rw [ofInt64_zero]
    simp only [denoteCode, denoteRun, State.bindAll, Option.bind]
    rfl
  case hnot => ent_auto

theorem b3Entry_step_zero (env : Env) (s : State) (nblk : Nat)
    (hpc : s.pc = "entry")
    (hnblk : lookupName env "%nblk" = some (.int 64 (BitVec.ofNat 64 nblk)))
    (h0 : nblk = 0) :
    ∃ env', denoteCode entryCalls b3Entry.instrs (withEnv env s) = some (withEnv env' s) ∧
      step entryCalls entryB3Function (withEnv env s)
        = .jump (withEnv env' { s with pc := "for.cond.cleanup", pre := some "entry" }) ∧
      lookupName env' "%cmp9.not" = some (.int 1 1) := by
  obtain ⟨env', hbody, hnot⟩ := b3Entry_body env s nblk hnblk
  have hb : BitVec.ofBool (BitVec.ofNat 64 nblk = 0) = (1 : BitVec 1) := by
    subst h0
    rfl
  refine ⟨env', hbody, ?_, ?_⟩
  · rw [b3_step_of (withEnv env s) "entry" b3Entry (withEnv env' s) hpc findBlock_b3Entry hbody]
    show execTerm (withEnv env' s) (.condbr (.reg "%cmp9.not") "for.cond.cleanup" "for.body")
      = .jump (withEnv env' { s with pc := "for.cond.cleanup", pre := some "entry" })
    have hop := JsonB8Steps.evalOperand_reg_of env' s "%cmp9.not"
      (.int 1 (BitVec.ofBool (BitVec.ofNat 64 nblk = 0))) hnot
    rw [execTerm_condbr_true (c := .reg "%cmp9.not") (t := "for.cond.cleanup")
      (f := "for.body") hop hb]
    rw [show (withEnv env' s).pc = "entry" from hpc]
    rfl
  · rwa [hb] at hnot

theorem b3Entry_step_pos (env : Env) (s : State) (nblk : Nat)
    (hpc : s.pc = "entry")
    (hnblk : lookupName env "%nblk" = some (.int 64 (BitVec.ofNat 64 nblk)))
    (hnblk64 : nblk < 2 ^ 64)
    (h0 : nblk ≠ 0) :
    ∃ env', denoteCode entryCalls b3Entry.instrs (withEnv env s) = some (withEnv env' s) ∧
      step entryCalls entryB3Function (withEnv env s)
        = .jump (withEnv env' { s with pc := "for.body", pre := some "entry" }) ∧
      lookupName env' "%cmp9.not" = some (.int 1 0) := by
  obtain ⟨env', hbody, hnot⟩ := b3Entry_body env s nblk hnblk
  have hne : ¬ (BitVec.ofNat 64 nblk = 0) := by
    intro h
    have h1 : (BitVec.ofNat 64 nblk).toNat = nblk := toNat_ofNat64 nblk hnblk64
    rw [h] at h1
    simp at h1
    omega
  have hb : BitVec.ofBool (BitVec.ofNat 64 nblk = 0) = (0 : BitVec 1) := by
    have hd : decide (BitVec.ofNat 64 nblk = 0) = false := decide_eq_false hne
    rw [hd]; rfl
  refine ⟨env', hbody, ?_, ?_⟩
  · rw [b3_step_of (withEnv env s) "entry" b3Entry (withEnv env' s) hpc findBlock_b3Entry hbody]
    show execTerm (withEnv env' s) (.condbr (.reg "%cmp9.not") "for.cond.cleanup" "for.body")
      = .jump (withEnv env' { s with pc := "for.body", pre := some "entry" })
    have hop := JsonB8Steps.evalOperand_reg_of env' s "%cmp9.not"
      (.int 1 (BitVec.ofBool (BitVec.ofNat 64 nblk = 0))) hnot
    rw [execTerm_condbr_false (c := .reg "%cmp9.not") (t := "for.cond.cleanup")
      (f := "for.body") hop hb]
    rw [show (withEnv env' s).pc = "entry" from hpc]
    rfl
  · rwa [hb] at hnot

/-- **The entry stream, in the block kernel.**  The run from the initial state
returns the stream's cursor and the fold of every block's stores; the lanes up to
the cursor hold the model's positions, and every read outside the output span is
unchanged. -/
theorem entry_b3_refines (ent : List (BitVec 64)) (blk0 nblk k : Nat) (mem : Mem)
    (e o : Nat)
    (hnblk : nblk = ent.length)
    (hblk : 64 * (blk0 + nblk) + 63 < 2 ^ 32)
    (hent : readBytes mem e (8 * ent.length) = some (wordsOf ent))
    (hdisj : e + 8 * ent.length ≤ o ∨ o + 4 * (k + 64 * ent.length + 8) ≤ e)
    (hk63 : k + 64 * ent.length + 9 < 2 ^ 63) :
    ∃ (k' : Nat) (mem' : Mem),
      runFuel entryCalls (b3RunSteps ent + nblk + 2) entryB3Function
        { (initState entryB3Function [.ptr e, .int 64 blk0, .int 64 nblk, .ptr o, .int 64 k]) with mem := mem }
          = some (.ret (some (.int 64 (BitVec.ofNat 64 k'))) mem') ∧
      k' = k + (ent.map ctpop).sum ∧
      readLanes32 mem' (o + 4 * k) (k' - k) = streamPrefix ent blk0 nblk ∧
      (∀ a, a < o + 4 * k ∨ o + 4 * (k' + 3) ≤ a → readByte mem' a = readByte mem a) := by
  let S0 : State := { (initState entryB3Function
    [.ptr e, .int 64 blk0, .int 64 nblk, .ptr o, .int 64 k]) with mem := mem }
  obtain ⟨hpc0, hent0, hblk0, hNb, hout0, hk0⟩ := b3_init blk0 nblk k mem e o
  by_cases hz : nblk = 0
  · -- no block runs: the entry test branches straight to `for.cond.cleanup`
    obtain ⟨e1, hrun1, hstep1, hnot⟩ :=
      b3Entry_step_zero S0.env S0 nblk hpc0 hNb hz
    have hk1 : lookupName e1 "%k" = some (.int 64 (BitVec.ofNat 64 k)) := by
      have h := b8_preserved b3Entry.instrs ["%k"] (by decide)
        (withEnv S0.env S0) (withEnv e1 S0) hrun1 "%k" (by decide)
      have h' : lookupName e1 "%k" = lookupName S0.env "%k" := by simpa only [withEnv] using h
      exact h'.trans hk0
    obtain ⟨e2, hbody2, hstep2, hk2⟩ :=
      b3Exit_step e1 { S0 with pc := "for.cond.cleanup", pre := some "entry" } k
        "entry" (.reg "%k") rfl rfl rfl (JsonB8Steps.evalOperand_reg_of e1 _ _ _ hk1)
    have he : ent = [] := List.eq_nil_of_length_eq_zero (by omega)
    have hfuel : b3RunSteps ent + nblk + 2 = 2 := by
      rw [he, hz]; rfl
    refine ⟨k, mem, ?_, ?_, ?_, ?_⟩
    · show runFuel entryCalls (b3RunSteps ent + nblk + 2) entryB3Function (withEnv S0.env S0)
        = some (.ret (some (.int 64 (BitVec.ofNat 64 k))) mem)
      rw [hfuel]
      exact (b3_runFuel_jump hstep1).trans (b3_runFuel_ret (n := 0) hstep2)
    · rw [he]; simp
    · rw [he]; simp [streamPrefix, readLanes32]
    · intro a ha
      rfl
  · -- the loop runs: `entry` falls into `for.body` with the parameter cells
    have hpos : 1 ≤ nblk := by omega
    obtain ⟨e1, hrun1, hstep1, hnot⟩ :=
      b3Entry_step_pos S0.env S0 nblk hpc0 hNb (by omega) hz
    have hfr : ∀ n ∈ ["%ent", "%blk0", "%nblk", "%out", "%k"],
        lookupName e1 n = lookupName S0.env n := by
      intro n hn
      have h := b8_preserved b3Entry.instrs ["%ent", "%blk0", "%nblk", "%out", "%k"] (by decide)
        (withEnv S0.env S0) (withEnv e1 S0) hrun1 n hn
      simpa only [withEnv] using h
    have hframe1 : B8Frame e1 e o blk0 nblk :=
      ⟨(hfr "%ent" (by decide)).trans hent0, (hfr "%blk0" (by decide)).trans hblk0,
        (hfr "%nblk" (by decide)).trans hNb, (hfr "%out" (by decide)).trans hout0⟩
    obtain ⟨e2, mem2, hrun2, hmem2⟩ :=
      b3_loop_run ent blk0 nblk k o e mem hent hblk hk63 hdisj hnblk
        nblk 0 k e1 { S0 with pc := "for.body", pre := some "entry" }
        "entry" (.reg "%k") (lit 64 0)
        hpos (by omega) rfl rfl rfl rfl
        (JsonB8Steps.evalOperand_reg_of e1 _ _ _ ((hfr "%k" (by decide)).trans hk0))
        (by
          show evalOperand _ (.imm (.int 64 (BitVec.ofInt 64 0))) = some (.int 64 (BitVec.ofNat 64 0))
          rw [ofInt64_zero]
          rfl)
        hframe1 rfl rfl
    refine ⟨pos8Cursor ent k, mem2, ?_, ?_, ?_, ?_⟩
    · -- one entry step, then the loop's own run
      show runFuel entryCalls (b3RunSteps ent + nblk + 2) entryB3Function (withEnv S0.env S0)
        = some (.ret (some (.int 64 (BitVec.ofNat 64 (pos8Cursor ent k)))) mem2)
      rw [show b3RunSteps ent + nblk + 2 = (b3RunSteps ent + nblk + 1) + 1 from by omega]
      rw [b3_runFuel_jump hstep1]
      exact hrun2
    · -- the count
      rw [pos8Cursor_eq_sum]
    · -- the words
      rw [hmem2]
      have hcap : 64 * blk0 + 64 * ent.length < 2 ^ 32 := by
        rw [← hnblk]; omega
      have hb : (64 * blk0) % 64 = 0 := Nat.mul_mod_right 64 blk0
      have hlen : pos8Cursor ent k - k = (ent.map ctpop).sum := by
        rw [pos8Cursor_eq_sum]; omega
      rw [hlen]
      rw [show readLanes32 (b3MemFold o (64 * blk0) k ent mem) (o + 4 * k) ((ent.map ctpop).sum)
          = some (b8Stream ent (64 * blk0)) from b3MemFold_read o (64 * blk0) k ent mem hb hcap]
      rw [b8Stream_eq_mapIdx, pos8Stream_eq_streamPrefix, hnblk]
    · -- the frame
      intro a ha
      rw [hmem2]
      exact readByte_congr_of_readBytes_one _ _ a
        (b3MemFold_frame (o := o) (base := 64 * blk0) (k := k) (ent := ent)
          (mem := mem) a 1 (by
            rcases ha with h | h
            · left; omega
            · right
              have hc : pos8Cursor ent k ≤ k + 64 * ent.length := by
                have h1 := pos8Cursor_le ent k
                omega
              omega))

end LeanLLVM.Refinement.JsonB3Steps
