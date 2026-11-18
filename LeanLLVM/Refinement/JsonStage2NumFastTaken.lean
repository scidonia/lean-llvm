/-
`num_fast_el1`'s eight-digit fast path: the taken guard's entry into
`intRunInv`.

`if.then22`'s guard refused is the dispatch's own path, which
`JsonStage2NumFastStarts.intRun_start` composes; taken, the block enters
`while.body.preheader` and the eight-digit loop.  `JsonStage2NumFastSeams`
chains that loop's blocks — the preheader's reader call, `cleanup`'s fold and
its two guards, `while.body`'s second call, `cleanup.thread`'s carry and
`while.end`'s merge — and composes the last two groups into `while.end`
(`fpFastSecond_run`, `fpFastSecond_run_refuse`).  What it leaves is the
composition of those pieces into the run's own entry, which is this module.

**The four paths.**  The first reader's answer decides the path, and `cleanup`'s
guard bounds it:

* the first read refuses — the answer is zero — and `cleanup.thread` carries the
  preheader's own cells to `while.end`: the lead counted, the index after it, the
  accumulator the lead digit's value;
* the first read succeeds and the guard refuses (`%add > %n`): `cleanup`'s fold
  is `while.end`'s, the count is `9` and the index after the group;
* the first read succeeds, the guard is taken and the second read refuses: the
  second `cleanup.thread` carries the first fold, the count `9` and the index
  after the first group;
* both reads succeed and the second fold's own count guard refuses at
  `9 + 8`: `while.end` takes the seventeen digits' fold.

`fpWhileEnd_entry` is the last two steps of every path: the merge's test to
`land.lhs.true41.preheader` and that block's `%6`/`%7` to `land.lhs.true41`,
where `intRunInv` holds at the exit's index and count.  The four path lemmas
compose it with their own blocks, and `fpTakenGuard_entry` is the case split at
the two reader answers, stated as the four implications the reader's `Option`
answer admits.

**The merge's other edge.**  Every statement here has the exit index strictly
inside the lexeme, because that is what `intRunInv` reads: the head tests the
byte at its index, and `i0 < n` is the byte's presence.  When the exit index
reaches `%n` instead, `while.end` leaves for `if.end68` (`fpWhileEnd_step_merge`)
and the block's denotation there is `ifEnd68_denote_loop`, already proved.

**The reader's local.**  The fast path writes the reader's word into `%v8`'s
local, so the memory the loop leaves is not the walk's.  The lexeme's read and
the second group's slice are stated at the walk's memory, and the paths carry
the separation the write needs: the local is either entirely below the lexeme or
entirely above it (`readBytes_writeBytes_local`).  That hypothesis is the
staging's, not the code's: `%v8` is a local the caller does not hand the
conversion.
-/
import LeanLLVM.Refinement.JsonStage2NumFastSeams

set_option autoImplicit false
set_option maxRecDepth 50000
set_option maxHeartbeats 1000000
/- The paths' `hpre` names the edge the state arrived by; no block reads `pre`, so
the tactic proofs never consume it.  The hypothesis is the statement's content,
not the proof's. -/
set_option linter.unusedVariables false

namespace LeanLLVM.Refinement

open LeanLLVM
open LeanLLVM.Refinement.BlockEval
open LeanLLVM.JSON

namespace NumFastTaken

/-! ### The `Nat` readings the loop's cells carry

The blocks write `%i.0 + 1`, `%i.0 + 9`, `%add563 + 8` and `%idig + 8` as
`BitVec` sums; the invariant reads the same words as `Nat`s.  The two lemmas
below are the conversions, and the third is the pointer the reader's call is
given: a `getelementptr i8` at a `Nat` index, read back as the address. -/

/-- A `Nat` index's 64-bit reading, sign-extended to itself: the `getelementptr`
address the reader's call is given. -/
theorem ofNat64_signExtend_toNat {j : Nat} (hj : j < 2 ^ 64) :
    ((BitVec.ofNat 64 j).signExtend 64).toNat = j := by
  rw [BitVec.signExtend_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hj]

/-- The reader's word as a `Nat`: the `i32` local's reading. -/
theorem ofNat32_toNat {w : Nat} (hw : w < 2 ^ 32) :
    (BitVec.ofNat 32 w).toNat = w := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hw]

/-- A state denoted at its own environment is itself. -/
theorem stateAt_env_self (s : State) : stateAt s.env s = s := rfl

/-! ### A written range outside a read

The fast path's local is disjoint from the lexeme, so the write of the reader's
word leaves the lexeme's bytes where they were.  The general form is the
per-byte `readByte_writeBytes_outside` lifted to a sequence; the local form is
the four-byte instance the two readers use. -/

/-- A sequence read outside a written range is the read of the memory underneath. -/
theorem readBytes_writeBytes_outside (m : Mem) (bs : List UInt8) :
    ∀ (n addr start : Nat), (addr + n ≤ start ∨ start + bs.length ≤ addr) →
      readBytes (writeBytes m start bs) addr n = readBytes m addr n
  | 0, addr, start, _ => rfl
  | n + 1, addr, start, h => by
      rcases h with h | h
      · exact readBytes_writeBytes_below m bs (n + 1) addr start h
      · simp only [readBytes]
        rw [readByte_writeBytes_above m bs h]
        cases hr : readByte m addr with
        | none => rfl
        | some b =>
            rw [readBytes_writeBytes_outside m bs n (addr + 1) start (Or.inr (by omega))]

/-- The reader's local is outside the lexeme: the write of the reader's word does
not disturb the bytes the walk read. -/
theorem readBytes_writeBytes_local (m : Mem) {v w addr n : Nat}
    (hsep : v + 4 ≤ addr ∨ addr + n ≤ v) :
    readBytes (writeBytes m v (natToBytes w 4)) addr n = readBytes m addr n := by
  rcases hsep with h | h
  · exact readBytes_writeBytes_outside m (natToBytes w 4) n addr v
      (Or.inr (by rw [natToBytes_length]; exact h))
  · exact readBytes_writeBytes_outside m (natToBytes w 4) n addr v (Or.inl h)

/-! ### The merge's three cells and the preheader's

The two builders `fpWhileEndEnv` and `intPreheaderEnv` stack their cells in
front of the environment the earlier block left, so a cell read through them is
a chain of peels.  The readings are hoisted here, one per cell, so each step's
hypotheses are small terms. -/

theorem fpWhileEndEnv_i (env : Env) (i idig ip nv : BitVec 64) :
    lookupName (NumFastSeams.fpWhileEndEnv env i idig ip nv) "%i.1558"
      = some (.int 64 i) := by
  simp only [NumFastSeams.fpWhileEndEnv]; block_lk

theorem fpWhileEndEnv_idig (env : Env) (i idig ip nv : BitVec 64) :
    lookupName (NumFastSeams.fpWhileEndEnv env i idig ip nv) "%idig.0560"
      = some (.int 64 idig) := by
  simp only [NumFastSeams.fpWhileEndEnv]; block_lk

theorem fpWhileEndEnv_ip (env : Env) (i idig ip nv : BitVec 64) :
    lookupName (NumFastSeams.fpWhileEndEnv env i idig ip nv) "%ip.0562"
      = some (.int 64 ip) := by
  simp only [NumFastSeams.fpWhileEndEnv]; block_lk

theorem fpWhileEndEnv_n {env : Env} {i idig ip nv : BitVec 64}
    (h : lookupName env "%n" = some (.int 64 nv)) :
    lookupName (NumFastSeams.fpWhileEndEnv env i idig ip nv) "%n"
      = some (.int 64 nv) := by
  simp only [NumFastSeams.fpWhileEndEnv]; block_lk

theorem fpWhileEndEnv_p {env : Env} {i idig ip nv : BitVec 64} {p : Nat}
    (h : lookupName env "%p" = some (.ptr p)) :
    lookupName (NumFastSeams.fpWhileEndEnv env i idig ip nv) "%p"
      = some (.ptr p) := by
  simp only [NumFastSeams.fpWhileEndEnv]; block_lk

theorem intPreheaderEnv_i {env : Env} {nv iv dv i : BitVec 64}
    (h : lookupName env "%i.1558" = some (.int 64 i)) :
    lookupName (NumFastStarts.intPreheaderEnv env nv iv dv) "%i.1558"
      = some (.int 64 i) := by
  simp only [NumFastStarts.intPreheaderEnv]; block_lk

theorem intPreheaderEnv_idig {env : Env} {nv iv dv idig : BitVec 64}
    (h : lookupName env "%idig.0560" = some (.int 64 idig)) :
    lookupName (NumFastStarts.intPreheaderEnv env nv iv dv) "%idig.0560"
      = some (.int 64 idig) := by
  simp only [NumFastStarts.intPreheaderEnv]; block_lk

theorem intPreheaderEnv_ip {env : Env} {nv iv dv ip : BitVec 64}
    (h : lookupName env "%ip.0562" = some (.int 64 ip)) :
    lookupName (NumFastStarts.intPreheaderEnv env nv iv dv) "%ip.0562"
      = some (.int 64 ip) := by
  simp only [NumFastStarts.intPreheaderEnv]; block_lk

theorem intPreheaderEnv_n {env : Env} {nv iv dv : BitVec 64}
    (h : lookupName env "%n" = some (.int 64 nv)) :
    lookupName (NumFastStarts.intPreheaderEnv env nv iv dv) "%n"
      = some (.int 64 nv) := by
  simp only [NumFastStarts.intPreheaderEnv]; block_lk

theorem intPreheaderEnv_p {env : Env} {nv iv dv : BitVec 64} {p : Nat}
    (h : lookupName env "%p" = some (.ptr p)) :
    lookupName (NumFastStarts.intPreheaderEnv env nv iv dv) "%p"
      = some (.ptr p) := by
  simp only [NumFastStarts.intPreheaderEnv]; block_lk

/-! ### The merge's two steps to the digit head

`while.end` merges the loop's three cells and tests the index against the
length; a true sends it to `land.lhs.true41.preheader`, whose `%6 = %idig + %n`
and `%7 = %6 - %i` are the two words `intRunInv`'s budget is read from.  This is
the last two steps of every path below. -/

/-- **`while.end` to the digit head.**  From the loop's merge, with the three
cells read as the run's start — the index `i0`, the count `d0` and the
accumulator the digits' fold from `i0 - d0` — two control steps reach
`land.lhs.true41` at `intRunInv` with the budget `n - i0`. -/
theorem fpWhileEnd_entry {epow : Int → Option EPow} {env : Env} {s : State}
    {i idig ip : BitVec 64} {mem : Mem} {p n i0 d0 : Nat} {bs : List UInt8}
    (hpc : s.pc = "while.end")
    (hden : denoteCode (stage2NumFastCalls epow) NumFastSeams.fpWhileEndInstrs
      (stateAt env s) = some (stateAt (NumFastSeams.fpWhileEndEnv env i idig ip
        (BitVec.ofNat 64 n)) s))
    (hbit : evalICmp .ult i (BitVec.ofNat 64 n) = 1)
    (hmem : s.mem = mem)
    (hp : lookupName (NumFastSeams.fpWhileEndEnv env i idig ip (BitVec.ofNat 64 n)) "%p"
      = some (.ptr p))
    (hn : lookupName (NumFastSeams.fpWhileEndEnv env i idig ip (BitVec.ofNat 64 n)) "%n"
      = some (.int 64 (BitVec.ofNat 64 n)))
    (hread : readBytes mem p n = some bs)
    (hi : i = BitVec.ofNat 64 i0) (hid : idig = BitVec.ofNat 64 d0)
    (hip : ip = BitVec.ofNat 64 (digitFold bs (i0 - d0) (min d0 19)))
    (hltn : i0 < n) (hnlt : n < 2 ^ 63) (hd0 : d0 ≤ i0) :
    ∃ e : State, intRunInv mem p n i0 d0 bs (n - i0) e 0 ∧
      ∀ k, runFuel (stage2NumFastCalls epow) (2 + k) numFastBody (stateAt env s)
        = runFuel (stage2NumFastCalls epow) k numFastBody e := by
  have hstep1 : step (stage2NumFastCalls epow) numFastBody (stateAt env s) =
      .jump (stateAt (NumFastSeams.fpWhileEndEnv env i idig ip (BitVec.ofNat 64 n))
        { s with pc := "land.lhs.true41.preheader", pre := some "while.end" }) :=
    NumFastSeams.fpWhileEnd_step_head (epow := epow) (i := i) (idig := idig)
      (ip := ip) (nv := BitVec.ofNat 64 n) hpc hden hbit
  have hid' : lookupName (NumFastSeams.fpWhileEndEnv env i idig ip
      (BitVec.ofNat 64 n)) "%idig.0560"
      = some (.int 64 idig) := fpWhileEndEnv_idig env i idig ip (BitVec.ofNat 64 n)
  have hi' : lookupName (NumFastSeams.fpWhileEndEnv env i idig ip
      (BitVec.ofNat 64 n)) "%i.1558"
      = some (.int 64 i) := fpWhileEndEnv_i env i idig ip (BitVec.ofNat 64 n)
  have hstep2 : step (stage2NumFastCalls epow) numFastBody
      (stateAt (NumFastSeams.fpWhileEndEnv env i idig ip (BitVec.ofNat 64 n))
        { s with pc := "land.lhs.true41.preheader", pre := some "while.end" }) =
      .jump (stateAt (NumFastStarts.intPreheaderEnv
          (NumFastSeams.fpWhileEndEnv env i idig ip (BitVec.ofNat 64 n))
          (BitVec.ofNat 64 n) i idig)
        { s with pc := "land.lhs.true41", pre := some "land.lhs.true41.preheader" }) :=
    NumFastStarts.intPreheader_step (calls := stage2NumFastCalls epow)
      (nv := BitVec.ofNat 64 n) (iv := i) (dv := idig) rfl hid' hi' hn
  have hi'' : lookupName (NumFastSeams.fpWhileEndEnv env i idig ip
      (BitVec.ofNat 64 n)) "%i.1558"
      = some (.int 64 (BitVec.ofNat 64 i0)) := by rw [fpWhileEndEnv_i, hi]
  have hid'' : lookupName (NumFastSeams.fpWhileEndEnv env i idig ip
      (BitVec.ofNat 64 n)) "%idig.0560"
      = some (.int 64 (BitVec.ofNat 64 d0)) := by rw [fpWhileEndEnv_idig, hid]
  have hip'' : lookupName (NumFastSeams.fpWhileEndEnv env i idig ip
      (BitVec.ofNat 64 n)) "%ip.0562"
      = some (.int 64 (BitVec.ofNat 64 (digitFold bs (i0 - d0) (min d0 19)))) := by
    rw [fpWhileEndEnv_ip, hip]
  refine ⟨stateAt (NumFastStarts.intPreheaderEnv
      (NumFastSeams.fpWhileEndEnv env i idig ip (BitVec.ofNat 64 n))
      (BitVec.ofNat 64 n) i idig)
      { s with pc := "land.lhs.true41", pre := some "land.lhs.true41.preheader" },
    ?_, ?_⟩
  · refine NumFastStarts.intRunInv_entry (mem := mem) (p := p) (n := n)
      (i0 := i0) (d0 := d0) (bs := bs) rfl rfl ?_ hltn hnlt hd0 ?_ ?_ hread ?_ ?_ ?_ ?_
    · simpa only [stateAt] using hmem
    · simpa only [stateAt] using intPreheaderEnv_p hp
    · simpa only [stateAt] using intPreheaderEnv_n hn
    · rw [← hi, ← hid]
      simp only [stateAt, NumFastStarts.intPreheaderEnv]
      block_lk
    · simpa only [stateAt] using intPreheaderEnv_i hi''
    · simpa only [stateAt] using intPreheaderEnv_idig hid''
    · simpa only [stateAt] using intPreheaderEnv_ip hip''
  · intro k
    rw [show 2 + k = 1 + (1 + k) from by omega,
      runFuel_jump_prefix hstep1, runFuel_jump_prefix hstep2]

/-! ### The four paths

Each path fixes the state at `while.body.preheader` (the taken guard's edge) and
composes its own blocks with `fpWhileEnd_entry`.  The hypotheses on the entry
state are the cells `if.then22` left: the pointer, the reader's local, the
index after the lead, the guard's own sum, the lead digit's value and the
length.  The reader's bytes are the walk's, at the offsets the call computes,
and the local's separation is the staging's. -/

/-- **The first read refuses.**  The preheader's zero answer leaves for
`cleanup.thread`, whose three `phi`s carry the preheader's own cells — the index
after the lead, the count one and the lead digit's value — and `while.end`
merges them.  Four steps reach the head at `i0 = start + 1`, `d0 = 1`. -/
theorem fpTaken_refuse1 {epow : Int → Option EPow} {env : Env} {s : State}
    {a v8a start n lead : Nat} {bs bs8 : List UInt8}
    (hpc : s.pc = "while.body.preheader")
    (hpre : s.pre = some "if.then22")
    (hp : lookupName env "%p" = some (.ptr a))
    (hv8 : lookupName env "%v8" = some (.ptr v8a))
    (hinc : lookupName env "%inc26"
      = some (.int 64 (BitVec.ofNat 64 (start + 1))))
    (h563 : lookupName env "%add563"
      = some (.int 64 (BitVec.ofNat 64 (start + 9))))
    (hconv : lookupName env "%conv25" = some (.int 64 (BitVec.ofNat 64 lead)))
    (hn : lookupName env "%n" = some (.int 64 (BitVec.ofNat 64 n)))
    (hread : readBytes s.mem a n = some bs)
    (hslice : readBytes s.mem (a + (start + 1)) 8 = some bs8)
    (hstart : start + 9 ≤ n) (hnlt : n < 2 ^ 63)
    (hlead : lead = digitFold bs start 1)
    (hval : d8Value bs8 = none) :
    ∃ e : State, intRunInv s.mem a n (start + 1) 1 bs (n - (start + 1)) e 0 ∧
      ∀ k, runFuel (stage2NumFastCalls epow) (4 + k) numFastBody (stateAt env s)
        = runFuel (stage2NumFastCalls epow) k numFastBody e := by
  have hpos : ((BitVec.ofNat 64 (start + 1)).signExtend 64).toNat < 2 ^ 63 := by
    rw [ofNat64_signExtend_toNat (by omega)]; omega
  have hslice' : readBytes s.mem
      (a + ((BitVec.ofNat 64 (start + 1)).signExtend 64).toNat) 8 = some bs8 := by
    rw [ofNat64_signExtend_toNat (by omega)]; exact hslice
  let st1 : State := { s with pc := "cleanup.thread", pre := some "while.body.preheader" }
  have hstep1 : step (stage2NumFastCalls epow) numFastBody (stateAt env s) =
      .jump (stateAt (NumFastSeams.fpPreEnv env a (BitVec.ofNat 64 (start + 1)) v8a 0)
        st1) :=
    NumFastSeams.fpPreheader_step_refuse (epow := epow) hpc hp hinc hv8 hpos hslice' hval
  have hinc1 : lookupName (NumFastSeams.fpPreEnv env a (BitVec.ofNat 64 (start + 1)) v8a 0)
      "%inc26" = some (.int 64 (BitVec.ofNat 64 (start + 1))) := by
    simp only [NumFastSeams.fpPreEnv]; block_lk
  have hconv1 : lookupName (NumFastSeams.fpPreEnv env a (BitVec.ofNat 64 (start + 1)) v8a 0)
      "%conv25" = some (.int 64 (BitVec.ofNat 64 lead)) := by
    simp only [NumFastSeams.fpPreEnv]; block_lk
  have hv81 : lookupName (NumFastSeams.fpPreEnv env a (BitVec.ofNat 64 (start + 1)) v8a 0)
      "%v8" = some (.ptr v8a) := by
    simp only [NumFastSeams.fpPreEnv]; block_lk
  let st2 : State := { st1 with pc := "while.end", pre := some "cleanup.thread" }
  have hstep2 : step (stage2NumFastCalls epow) numFastBody
      (stateAt (NumFastSeams.fpPreEnv env a (BitVec.ofNat 64 (start + 1)) v8a 0) st1) =
      .jump (stateAt (NumFastSeams.fpCleanupThreadEnv
          (NumFastSeams.fpPreEnv env a (BitVec.ofNat 64 (start + 1)) v8a 0)
          (BitVec.ofNat 64 (start + 1)) 0x1#64 (BitVec.ofNat 64 lead)) st2) :=
    NumFastSeams.fpCleanupThread_step (epow := epow) rfl rfl hinc1 hconv1 hv81
  have hi2 : lookupName (NumFastSeams.fpCleanupThreadEnv
      (NumFastSeams.fpPreEnv env a (BitVec.ofNat 64 (start + 1)) v8a 0)
      (BitVec.ofNat 64 (start + 1)) 0x1#64 (BitVec.ofNat 64 lead)) "%i.1567.lcssa"
      = some (.int 64 (BitVec.ofNat 64 (start + 1))) := by
    simp only [NumFastSeams.fpCleanupThreadEnv]; block_lk
  have hid2 : lookupName (NumFastSeams.fpCleanupThreadEnv
      (NumFastSeams.fpPreEnv env a (BitVec.ofNat 64 (start + 1)) v8a 0)
      (BitVec.ofNat 64 (start + 1)) 0x1#64 (BitVec.ofNat 64 lead)) "%idig.0566.lcssa"
      = some (.int 64 0x1#64) := by
    simp only [NumFastSeams.fpCleanupThreadEnv]; block_lk
  have hip2 : lookupName (NumFastSeams.fpCleanupThreadEnv
      (NumFastSeams.fpPreEnv env a (BitVec.ofNat 64 (start + 1)) v8a 0)
      (BitVec.ofNat 64 (start + 1)) 0x1#64 (BitVec.ofNat 64 lead)) "%ip.0565.lcssa"
      = some (.int 64 (BitVec.ofNat 64 lead)) := by
    simp only [NumFastSeams.fpCleanupThreadEnv]; block_lk
  have hn2 : lookupName (NumFastSeams.fpCleanupThreadEnv
      (NumFastSeams.fpPreEnv env a (BitVec.ofNat 64 (start + 1)) v8a 0)
      (BitVec.ofNat 64 (start + 1)) 0x1#64 (BitVec.ofNat 64 lead)) "%n"
      = some (.int 64 (BitVec.ofNat 64 n)) := by
    simp only [NumFastSeams.fpCleanupThreadEnv, NumFastSeams.fpPreEnv]; block_lk
  have hden : denoteCode (stage2NumFastCalls epow) NumFastSeams.fpWhileEndInstrs
      (stateAt (NumFastSeams.fpCleanupThreadEnv
        (NumFastSeams.fpPreEnv env a (BitVec.ofNat 64 (start + 1)) v8a 0)
        (BitVec.ofNat 64 (start + 1)) 0x1#64 (BitVec.ofNat 64 lead)) st2) =
      some (stateAt (NumFastSeams.fpWhileEndEnv
        (NumFastSeams.fpCleanupThreadEnv
          (NumFastSeams.fpPreEnv env a (BitVec.ofNat 64 (start + 1)) v8a 0)
          (BitVec.ofNat 64 (start + 1)) 0x1#64 (BitVec.ofNat 64 lead))
        (BitVec.ofNat 64 (start + 1)) 0x1#64 (BitVec.ofNat 64 lead)
        (BitVec.ofNat 64 n)) st2) :=
    NumFastSeams.fpWhileEnd_denote_thread (epow := epow) rfl hi2 hid2 hip2 hn2
  have hbit : evalICmp .ult (BitVec.ofNat 64 (start + 1)) (BitVec.ofNat 64 n) = 1 :=
    NumFastSeams.ult_ofNat_one (by omega) (by omega)
  have hp' : lookupName (NumFastSeams.fpWhileEndEnv
      (NumFastSeams.fpCleanupThreadEnv
        (NumFastSeams.fpPreEnv env a (BitVec.ofNat 64 (start + 1)) v8a 0)
        (BitVec.ofNat 64 (start + 1)) 0x1#64 (BitVec.ofNat 64 lead))
      (BitVec.ofNat 64 (start + 1)) 0x1#64 (BitVec.ofNat 64 lead)
      (BitVec.ofNat 64 n)) "%p" = some (.ptr a) :=
    fpWhileEndEnv_p (by
      simp only [NumFastSeams.fpCleanupThreadEnv, NumFastSeams.fpPreEnv]; block_lk)
  have hn' : lookupName (NumFastSeams.fpWhileEndEnv
      (NumFastSeams.fpCleanupThreadEnv
        (NumFastSeams.fpPreEnv env a (BitVec.ofNat 64 (start + 1)) v8a 0)
        (BitVec.ofNat 64 (start + 1)) 0x1#64 (BitVec.ofNat 64 lead))
      (BitVec.ofNat 64 (start + 1)) 0x1#64 (BitVec.ofNat 64 lead)
      (BitVec.ofNat 64 n)) "%n" = some (.int 64 (BitVec.ofNat 64 n)) :=
    fpWhileEndEnv_n hn2
  obtain ⟨e, hinv, hcont⟩ := fpWhileEnd_entry (epow := epow)
    (env := NumFastSeams.fpCleanupThreadEnv
      (NumFastSeams.fpPreEnv env a (BitVec.ofNat 64 (start + 1)) v8a 0)
      (BitVec.ofNat 64 (start + 1)) 0x1#64 (BitVec.ofNat 64 lead))
    (s := st2)
    (i := BitVec.ofNat 64 (start + 1)) (idig := 0x1#64)
    (ip := BitVec.ofNat 64 lead)
    (mem := s.mem) (p := a) (n := n) (i0 := start + 1) (d0 := 1) (bs := bs)
    rfl hden hbit rfl hp' hn' hread rfl rfl (by
      rw [show start + 1 - 1 = start from by omega, show min 1 19 = 1 from by decide]
      exact congrArg (BitVec.ofNat 64) hlead) (by omega) hnlt (by omega)
  refine ⟨e, hinv, ?_⟩
  intro k
  rw [show 4 + k = 1 + (1 + (2 + k)) from by omega,
    runFuel_jump_prefix hstep1, runFuel_jump_prefix hstep2, hcont k]

/-- **The first read succeeds and the guard refuses.**  `cleanup` folds the
group — `%ip * 10 ^ 8 + %4` — and tests the advanced index and the count; a
refused conjunction leaves for `while.end` with the count nine and the index
after the group.  Four steps reach the head at `i0 = start + 9`, `d0 = 9`. -/
theorem fpTaken_exit {epow : Int → Option EPow} {env : Env} {s : State}
    {a v8a start n w lead : Nat} {bs bs8 : List UInt8}
    (hpc : s.pc = "while.body.preheader")
    (hpre : s.pre = some "if.then22")
    (hp : lookupName env "%p" = some (.ptr a))
    (hv8 : lookupName env "%v8" = some (.ptr v8a))
    (hinc : lookupName env "%inc26"
      = some (.int 64 (BitVec.ofNat 64 (start + 1))))
    (h563 : lookupName env "%add563"
      = some (.int 64 (BitVec.ofNat 64 (start + 9))))
    (hconv : lookupName env "%conv25" = some (.int 64 (BitVec.ofNat 64 lead)))
    (hn : lookupName env "%n" = some (.int 64 (BitVec.ofNat 64 n)))
    (hread : readBytes s.mem a n = some bs)
    (hslice : readBytes s.mem (a + (start + 1)) 8 = some bs8)
    (hstart : start + 9 ≤ n) (hnlt : n < 2 ^ 63)
    (hlead : lead = digitFold bs start 1)
    (hval : d8Value bs8 = some w) (hw : w < 2 ^ 32)
    (hsep : v8a + 4 ≤ a ∨ a + n ≤ v8a)
    (hguard : NumFastSeams.fpGuard
      (BitVec.ofNat 64 (start + 9) + 0x8#64) 0x9#64 (BitVec.ofNat 64 n) = 0)
    (hmore : start + 9 < n) :
    ∃ e : State, intRunInv (writeBytes s.mem v8a (natToBytes w 4)) a n (start + 9) 9 bs
      (n - (start + 9)) e 0 ∧
      ∀ k, runFuel (stage2NumFastCalls epow) (4 + k) numFastBody (stateAt env s)
        = runFuel (stage2NumFastCalls epow) k numFastBody e := by
  have hpos : ((BitVec.ofNat 64 (start + 1)).signExtend 64).toNat < 2 ^ 63 := by
    rw [ofNat64_signExtend_toNat (by omega)]; omega
  have hslice' : readBytes s.mem
      (a + ((BitVec.ofNat 64 (start + 1)).signExtend 64).toNat) 8 = some bs8 := by
    rw [ofNat64_signExtend_toNat (by omega)]; exact hslice
  let st1 : State := { s with mem := writeBytes s.mem v8a (natToBytes w 4),
                               next := s.next, pc := "cleanup",
                               pre := some "while.body.preheader" }
  have hstep1 : step (stage2NumFastCalls epow) numFastBody (stateAt env s) =
      .jump (stateAt (NumFastSeams.fpPreEnv env a (BitVec.ofNat 64 (start + 1)) v8a 1)
        st1) :=
    NumFastSeams.fpPreheader_step (epow := epow) hpc hp hinc hv8 hpos hslice' hval hw
  have hback : readBytes (writeBytes s.mem v8a (natToBytes w 4)) v8a 4
      = some (natToBytes w 4) :=
    (NumFastSeams.numD8Answer_writes (p := a + (start + 1)) (v := v8a) (w := w)
      (bs := bs8) (mem := s.mem) (next := s.next) hslice hval hw).2.1
  have hread1 : readBytes (writeBytes s.mem v8a (natToBytes w 4)) v8a 4
      = some (natToBytes (BitVec.ofNat 32 w).toNat 4) := by
    rw [ofNat32_toNat hw]; exact hback
  have hconv1 : lookupName (NumFastSeams.fpPreEnv env a (BitVec.ofNat 64 (start + 1)) v8a 1)
      "%conv25" = some (.int 64 (BitVec.ofNat 64 lead)) := by
    simp only [NumFastSeams.fpPreEnv]; block_lk
  have h563_1 : lookupName (NumFastSeams.fpPreEnv env a (BitVec.ofNat 64 (start + 1)) v8a 1)
      "%add563" = some (.int 64 (BitVec.ofNat 64 (start + 9))) := by
    simp only [NumFastSeams.fpPreEnv]; block_lk
  have hv8_1 : lookupName (NumFastSeams.fpPreEnv env a (BitVec.ofNat 64 (start + 1)) v8a 1)
      "%v8" = some (.ptr v8a) := by
    simp only [NumFastSeams.fpPreEnv]; block_lk
  have hn1 : lookupName (NumFastSeams.fpPreEnv env a (BitVec.ofNat 64 (start + 1)) v8a 1)
      "%n" = some (.int 64 (BitVec.ofNat 64 n)) := by
    simp only [NumFastSeams.fpPreEnv]; block_lk
  have hden1 : denoteCode (stage2NumFastCalls epow) NumFastSeams.fpCleanupInstrs
      (stateAt (NumFastSeams.fpPreEnv env a (BitVec.ofNat 64 (start + 1)) v8a 1) st1) =
      some (stateAt (NumFastSeams.fpCleanupEnv
        (NumFastSeams.fpPreEnv env a (BitVec.ofNat 64 (start + 1)) v8a 1)
        (BitVec.ofNat 64 lead) (BitVec.ofNat 64 (start + 9)) 0x9#64
        (BitVec.ofNat 64 n) (BitVec.ofNat 32 w)) st1) :=
    NumFastSeams.fpCleanup_denote_pre (epow := epow) rfl hconv1 h563_1 hv8_1 hread1 hn1
  let st2 : State := { st1 with pc := "while.end", pre := some "cleanup" }
  have hstep2 : step (stage2NumFastCalls epow) numFastBody
      (stateAt (NumFastSeams.fpPreEnv env a (BitVec.ofNat 64 (start + 1)) v8a 1) st1) =
      .jump (stateAt (NumFastSeams.fpCleanupEnv
        (NumFastSeams.fpPreEnv env a (BitVec.ofNat 64 (start + 1)) v8a 1)
        (BitVec.ofNat 64 lead) (BitVec.ofNat 64 (start + 9)) 0x9#64
        (BitVec.ofNat 64 n) (BitVec.ofNat 32 w)) st2) :=
    NumFastSeams.fpCleanup_step_end (epow := epow) rfl hden1 hguard
  have hfold : BitVec.ofNat 64 lead * 0x5f5e100#64 + BitVec.ofNat 64 w
      = BitVec.ofNat 64 (digitFold bs start 9) :=
    NumFastSeams.fpFirstFold hread hlead hslice hstart hval
  have hip2 : lookupName (NumFastSeams.fpCleanupEnv
      (NumFastSeams.fpPreEnv env a (BitVec.ofNat 64 (start + 1)) v8a 1)
      (BitVec.ofNat 64 lead) (BitVec.ofNat 64 (start + 9)) 0x9#64
      (BitVec.ofNat 64 n) (BitVec.ofNat 32 w)) "%add35"
      = some (.int 64 (BitVec.ofNat 64 (digitFold bs start 9))) := by
    have hcell : lookupName (NumFastSeams.fpCleanupEnv
        (NumFastSeams.fpPreEnv env a (BitVec.ofNat 64 (start + 1)) v8a 1)
        (BitVec.ofNat 64 lead) (BitVec.ofNat 64 (start + 9)) 0x9#64
        (BitVec.ofNat 64 n) (BitVec.ofNat 32 w)) "%add35"
        = some (.int 64 (BitVec.ofNat 64 lead * 0x5f5e100#64
            + BitVec.ofNat 64 (BitVec.ofNat 32 w).toNat)) := by
      simp only [NumFastSeams.fpCleanupEnv]; block_lk
    rw [hcell, ofNat32_toNat hw, hfold]
  have hid2 : lookupName (NumFastSeams.fpCleanupEnv
      (NumFastSeams.fpPreEnv env a (BitVec.ofNat 64 (start + 1)) v8a 1)
      (BitVec.ofNat 64 lead) (BitVec.ofNat 64 (start + 9)) 0x9#64
      (BitVec.ofNat 64 n) (BitVec.ofNat 32 w)) "%add29569933"
      = some (.int 64 0x9#64) := by
    simp only [NumFastSeams.fpCleanupEnv]; block_lk
  have hi2 : lookupName (NumFastSeams.fpCleanupEnv
      (NumFastSeams.fpPreEnv env a (BitVec.ofNat 64 (start + 1)) v8a 1)
      (BitVec.ofNat 64 lead) (BitVec.ofNat 64 (start + 9)) 0x9#64
      (BitVec.ofNat 64 n) (BitVec.ofNat 32 w)) "%add568934"
      = some (.int 64 (BitVec.ofNat 64 (start + 9))) := by
    simp only [NumFastSeams.fpCleanupEnv]; block_lk
  have hn2 : lookupName (NumFastSeams.fpCleanupEnv
      (NumFastSeams.fpPreEnv env a (BitVec.ofNat 64 (start + 1)) v8a 1)
      (BitVec.ofNat 64 lead) (BitVec.ofNat 64 (start + 9)) 0x9#64
      (BitVec.ofNat 64 n) (BitVec.ofNat 32 w)) "%n"
      = some (.int 64 (BitVec.ofNat 64 n)) := by
    simp only [NumFastSeams.fpCleanupEnv, NumFastSeams.fpPreEnv]; block_lk
  have hden : denoteCode (stage2NumFastCalls epow) NumFastSeams.fpWhileEndInstrs
      (stateAt (NumFastSeams.fpCleanupEnv
        (NumFastSeams.fpPreEnv env a (BitVec.ofNat 64 (start + 1)) v8a 1)
        (BitVec.ofNat 64 lead) (BitVec.ofNat 64 (start + 9)) 0x9#64
        (BitVec.ofNat 64 n) (BitVec.ofNat 32 w)) st2) =
      some (stateAt (NumFastSeams.fpWhileEndEnv
        (NumFastSeams.fpCleanupEnv
          (NumFastSeams.fpPreEnv env a (BitVec.ofNat 64 (start + 1)) v8a 1)
          (BitVec.ofNat 64 lead) (BitVec.ofNat 64 (start + 9)) 0x9#64
          (BitVec.ofNat 64 n) (BitVec.ofNat 32 w))
        (BitVec.ofNat 64 (start + 9)) 0x9#64
        (BitVec.ofNat 64 (digitFold bs start 9)) (BitVec.ofNat 64 n)) st2) :=
    NumFastSeams.fpWhileEnd_denote_cleanup (epow := epow) rfl hip2 hid2 hi2 hn2
  have hbit : evalICmp .ult (BitVec.ofNat 64 (start + 9)) (BitVec.ofNat 64 n) = 1 :=
    NumFastSeams.ult_ofNat_one hmore (by omega)
  have hread' : readBytes (writeBytes s.mem v8a (natToBytes w 4)) a n = some bs := by
    rw [readBytes_writeBytes_local (m := s.mem) (w := w) hsep]; exact hread
  have hp' : lookupName (NumFastSeams.fpWhileEndEnv
      (NumFastSeams.fpCleanupEnv
        (NumFastSeams.fpPreEnv env a (BitVec.ofNat 64 (start + 1)) v8a 1)
        (BitVec.ofNat 64 lead) (BitVec.ofNat 64 (start + 9)) 0x9#64
        (BitVec.ofNat 64 n) (BitVec.ofNat 32 w))
      (BitVec.ofNat 64 (start + 9)) 0x9#64
      (BitVec.ofNat 64 (digitFold bs start 9)) (BitVec.ofNat 64 n)) "%p"
      = some (.ptr a) :=
    fpWhileEndEnv_p (by
      simp only [NumFastSeams.fpCleanupEnv, NumFastSeams.fpPreEnv]; block_lk)
  have hn' : lookupName (NumFastSeams.fpWhileEndEnv
      (NumFastSeams.fpCleanupEnv
        (NumFastSeams.fpPreEnv env a (BitVec.ofNat 64 (start + 1)) v8a 1)
        (BitVec.ofNat 64 lead) (BitVec.ofNat 64 (start + 9)) 0x9#64
        (BitVec.ofNat 64 n) (BitVec.ofNat 32 w))
      (BitVec.ofNat 64 (start + 9)) 0x9#64
      (BitVec.ofNat 64 (digitFold bs start 9)) (BitVec.ofNat 64 n)) "%n"
      = some (.int 64 (BitVec.ofNat 64 n)) :=
    fpWhileEndEnv_n hn2
  obtain ⟨e, hinv, hcont⟩ := fpWhileEnd_entry (epow := epow)
    (env := NumFastSeams.fpCleanupEnv
      (NumFastSeams.fpPreEnv env a (BitVec.ofNat 64 (start + 1)) v8a 1)
      (BitVec.ofNat 64 lead) (BitVec.ofNat 64 (start + 9)) 0x9#64
      (BitVec.ofNat 64 n) (BitVec.ofNat 32 w))
    (s := st2)
    (i := BitVec.ofNat 64 (start + 9)) (idig := 0x9#64)
    (ip := BitVec.ofNat 64 (digitFold bs start 9))
    (mem := writeBytes s.mem v8a (natToBytes w 4)) (p := a) (n := n)
    (i0 := start + 9) (d0 := 9) (bs := bs)
    rfl hden hbit rfl hp' hn' hread' rfl rfl (by
      rw [show start + 9 - 9 = start from by omega, show min 9 19 = 9 from by decide])
    hmore hnlt (by omega)
  refine ⟨e, hinv, ?_⟩
  intro k
  rw [show 4 + k = 1 + (1 + (2 + k)) from by omega,
    runFuel_jump_prefix hstep1, runFuel_jump_prefix hstep2, hcont k]

/-- **The second read refuses.**  The first fold has already advanced the index
and the count; the second reader's zero answer leaves for `cleanup.thread`,
whose `phi`s carry `while.body`'s own cells — the index after the first group,
the count nine and the first fold — and `while.end` merges them.  Six steps
reach the head at `i0 = start + 9`, `d0 = 9`. -/
theorem fpTaken_refuse2 {epow : Int → Option EPow} {env : Env} {s : State}
    {a v8a start n w lead : Nat} {bs bs8a bs8b : List UInt8}
    (hpc : s.pc = "while.body.preheader")
    (hpre : s.pre = some "if.then22")
    (hp : lookupName env "%p" = some (.ptr a))
    (hv8 : lookupName env "%v8" = some (.ptr v8a))
    (hinc : lookupName env "%inc26"
      = some (.int 64 (BitVec.ofNat 64 (start + 1))))
    (h563 : lookupName env "%add563"
      = some (.int 64 (BitVec.ofNat 64 (start + 9))))
    (hconv : lookupName env "%conv25" = some (.int 64 (BitVec.ofNat 64 lead)))
    (hn : lookupName env "%n" = some (.int 64 (BitVec.ofNat 64 n)))
    (hread : readBytes s.mem a n = some bs)
    (hslicea : readBytes s.mem (a + (start + 1)) 8 = some bs8a)
    (hsliceb : readBytes s.mem (a + (start + 9)) 8 = some bs8b)
    (hstart : start + 9 ≤ n) (hnlt : n < 2 ^ 63)
    (hlead : lead = digitFold bs start 1)
    (hval : d8Value bs8a = some w) (hw : w < 2 ^ 32)
    (hsep : v8a + 4 ≤ a ∨ a + n ≤ v8a)
    (hsep2 : v8a + 4 ≤ a + (start + 9) ∨ a + (start + 9) + 8 ≤ v8a)
    (hguard : NumFastSeams.fpGuard
      (BitVec.ofNat 64 (start + 9) + 0x8#64) 0x9#64 (BitVec.ofNat 64 n) = 1)
    (hmore : start + 9 < n)
    (hval2 : d8Value bs8b = none) :
    ∃ e : State, intRunInv (writeBytes s.mem v8a (natToBytes w 4)) a n (start + 9) 9 bs
      (n - (start + 9)) e 0 ∧
      ∀ k, runFuel (stage2NumFastCalls epow) (6 + k) numFastBody (stateAt env s)
        = runFuel (stage2NumFastCalls epow) k numFastBody e := by
  have hpos : ((BitVec.ofNat 64 (start + 1)).signExtend 64).toNat < 2 ^ 63 := by
    rw [ofNat64_signExtend_toNat (by omega)]; omega
  have hpos9 : ((BitVec.ofNat 64 (start + 9)).signExtend 64).toNat < 2 ^ 63 := by
    rw [ofNat64_signExtend_toNat (by omega)]; omega
  have hslicea' : readBytes s.mem
      (a + ((BitVec.ofNat 64 (start + 1)).signExtend 64).toNat) 8 = some bs8a := by
    rw [ofNat64_signExtend_toNat (by omega)]; exact hslicea
  let st1 : State := { s with mem := writeBytes s.mem v8a (natToBytes w 4),
                               next := s.next, pc := "cleanup",
                               pre := some "while.body.preheader" }
  have hstep1 : step (stage2NumFastCalls epow) numFastBody (stateAt env s) =
      .jump (stateAt (NumFastSeams.fpPreEnv env a (BitVec.ofNat 64 (start + 1)) v8a 1)
        st1) :=
    NumFastSeams.fpPreheader_step (epow := epow) hpc hp hinc hv8 hpos hslicea' hval hw
  have hback : readBytes (writeBytes s.mem v8a (natToBytes w 4)) v8a 4
      = some (natToBytes w 4) :=
    (NumFastSeams.numD8Answer_writes (p := a + (start + 1)) (v := v8a) (w := w)
      (bs := bs8a) (mem := s.mem) (next := s.next) hslicea hval hw).2.1
  have hread1 : readBytes (writeBytes s.mem v8a (natToBytes w 4)) v8a 4
      = some (natToBytes (BitVec.ofNat 32 w).toNat 4) := by
    rw [ofNat32_toNat hw]; exact hback
  have hp1 : lookupName (NumFastSeams.fpPreEnv env a (BitVec.ofNat 64 (start + 1)) v8a 1)
      "%p" = some (.ptr a) := by
    simp only [NumFastSeams.fpPreEnv]; block_lk
  have hconv1 : lookupName (NumFastSeams.fpPreEnv env a (BitVec.ofNat 64 (start + 1)) v8a 1)
      "%conv25" = some (.int 64 (BitVec.ofNat 64 lead)) := by
    simp only [NumFastSeams.fpPreEnv]; block_lk
  have h563_1 : lookupName (NumFastSeams.fpPreEnv env a (BitVec.ofNat 64 (start + 1)) v8a 1)
      "%add563" = some (.int 64 (BitVec.ofNat 64 (start + 9))) := by
    simp only [NumFastSeams.fpPreEnv]; block_lk
  have hv8_1 : lookupName (NumFastSeams.fpPreEnv env a (BitVec.ofNat 64 (start + 1)) v8a 1)
      "%v8" = some (.ptr v8a) := by
    simp only [NumFastSeams.fpPreEnv]; block_lk
  have hn1 : lookupName (NumFastSeams.fpPreEnv env a (BitVec.ofNat 64 (start + 1)) v8a 1)
      "%n" = some (.int 64 (BitVec.ofNat 64 n)) := by
    simp only [NumFastSeams.fpPreEnv]; block_lk
  have hread2 : readBytes (writeBytes s.mem v8a (natToBytes w 4))
      (a + ((BitVec.ofNat 64 (start + 9)).signExtend 64).toNat) 8 = some bs8b := by
    rw [ofNat64_signExtend_toNat (by omega)]
    rw [readBytes_writeBytes_local (m := s.mem) (w := w) hsep2]
    exact hsliceb
  obtain ⟨e2, hpc2, hpre2, hmem2, henv2, hcont2⟩ :=
    NumFastSeams.fpFastSecond_run_refuse (epow := epow)
      (env := NumFastSeams.fpPreEnv env a (BitVec.ofNat 64 (start + 1)) v8a 1)
      (s := st1)
      (a := a) (v8a := v8a) (ip := BitVec.ofNat 64 lead)
      (add568 := BitVec.ofNat 64 (start + 9)) (nv := BitVec.ofNat 64 n)
      (w := BitVec.ofNat 32 w) (bs8 := bs8b)
      rfl rfl hp1 hconv1 h563_1 hv8_1 hn1 hread1 hguard hpos9 hread2 hval2
  have hi3 : lookupName e2.env "%i.1567.lcssa"
      = some (.int 64 (BitVec.ofNat 64 (start + 9))) := by
    rw [henv2]
    simp only [NumFastSeams.fpSecondThreadEnv, NumFastSeams.fpCleanupThreadEnv]; block_lk
  have hid3 : lookupName e2.env "%idig.0566.lcssa" = some (.int 64 0x9#64) := by
    rw [henv2]
    simp only [NumFastSeams.fpSecondThreadEnv, NumFastSeams.fpCleanupThreadEnv]; block_lk
  have hip3 : lookupName e2.env "%ip.0565.lcssa"
      = some (.int 64 (BitVec.ofNat 64 (digitFold bs start 9))) := by
    rw [henv2]
    have hcell : lookupName (NumFastSeams.fpSecondThreadEnv
        (NumFastSeams.fpPreEnv env a (BitVec.ofNat 64 (start + 1)) v8a 1)
        a v8a (BitVec.ofNat 64 lead) (BitVec.ofNat 64 (start + 9))
        (BitVec.ofNat 64 n) (BitVec.ofNat 32 w)) "%ip.0565.lcssa"
        = some (.int 64 (BitVec.ofNat 64 lead * 0x5f5e100#64
            + BitVec.ofNat 64 (BitVec.ofNat 32 w).toNat)) := by
      simp only [NumFastSeams.fpSecondThreadEnv, NumFastSeams.fpCleanupThreadEnv]; block_lk
    have hfold : BitVec.ofNat 64 lead * 0x5f5e100#64 + BitVec.ofNat 64 w
        = BitVec.ofNat 64 (digitFold bs start 9) :=
      NumFastSeams.fpFirstFold hread hlead hslicea hstart hval
    rw [hcell, ofNat32_toNat hw, hfold]
  have hn3 : lookupName e2.env "%n" = some (.int 64 (BitVec.ofNat 64 n)) := by
    rw [henv2]
    simp only [NumFastSeams.fpSecondThreadEnv, NumFastSeams.fpCleanupThreadEnv,
      NumFastSeams.fpBodyEnv2r, NumFastSeams.fpBodyEnv, NumFastSeams.fpFirstEnv,
      NumFastSeams.fpPreEnv]; block_lk
  have hden : denoteCode (stage2NumFastCalls epow) NumFastSeams.fpWhileEndInstrs
      (stateAt e2.env e2) = some (stateAt (NumFastSeams.fpWhileEndEnv e2.env
        (BitVec.ofNat 64 (start + 9)) 0x9#64
        (BitVec.ofNat 64 (digitFold bs start 9)) (BitVec.ofNat 64 n)) e2) :=
    NumFastSeams.fpWhileEnd_denote_thread (epow := epow) (env := e2.env) (s := e2)
      hpre2 hi3 hid3 hip3 hn3
  have hbit : evalICmp .ult (BitVec.ofNat 64 (start + 9)) (BitVec.ofNat 64 n) = 1 :=
    NumFastSeams.ult_ofNat_one hmore (by omega)
  have hread' : readBytes (writeBytes s.mem v8a (natToBytes w 4)) a n = some bs := by
    rw [readBytes_writeBytes_local (m := s.mem) (w := w) hsep]; exact hread
  have hp3 : lookupName (NumFastSeams.fpWhileEndEnv e2.env
      (BitVec.ofNat 64 (start + 9)) 0x9#64
      (BitVec.ofNat 64 (digitFold bs start 9)) (BitVec.ofNat 64 n)) "%p"
      = some (.ptr a) :=
    fpWhileEndEnv_p (by
      rw [henv2]
      simp only [NumFastSeams.fpSecondThreadEnv, NumFastSeams.fpCleanupThreadEnv,
        NumFastSeams.fpPreEnv]; block_lk)
  have hn3' : lookupName (NumFastSeams.fpWhileEndEnv e2.env
      (BitVec.ofNat 64 (start + 9)) 0x9#64
      (BitVec.ofNat 64 (digitFold bs start 9)) (BitVec.ofNat 64 n)) "%n"
      = some (.int 64 (BitVec.ofNat 64 n)) :=
    fpWhileEndEnv_n hn3
  obtain ⟨e, hinv, hcont⟩ := fpWhileEnd_entry (epow := epow)
    (env := e2.env) (s := e2)
    (i := BitVec.ofNat 64 (start + 9)) (idig := 0x9#64)
    (ip := BitVec.ofNat 64 (digitFold bs start 9))
    (mem := writeBytes s.mem v8a (natToBytes w 4)) (p := a) (n := n)
    (i0 := start + 9) (d0 := 9) (bs := bs)
    hpc2 hden hbit hmem2 hp3 hn3' hread' rfl rfl (by
      rw [show start + 9 - 9 = start from by omega, show min 9 19 = 9 from by decide])
    hmore hnlt (by omega)
  rw [stateAt_env_self e2] at hcont
  refine ⟨e, hinv, ?_⟩
  intro k
  rw [show 6 + k = 1 + (3 + (2 + k)) from by omega,
    runFuel_jump_prefix hstep1, hcont2 (2 + k), hcont k]

/-- **The second fold.**  Both readers answer, the first `cleanup` takes the
second group and the second `cleanup` folds it; its own count guard refuses at
`9 + 8`, so `while.end` merges the seventeen digits' accumulator with the count
`17` and the index after the second group.  Six steps reach the head at
`i0 = start + 17`, `d0 = 17`. -/
theorem fpTaken_fold2 {epow : Int → Option EPow} {env : Env} {s : State}
    {a v8a start n w w2 lead : Nat} {bs bs8a bs8b : List UInt8}
    (hpc : s.pc = "while.body.preheader")
    (hpre : s.pre = some "if.then22")
    (hp : lookupName env "%p" = some (.ptr a))
    (hv8 : lookupName env "%v8" = some (.ptr v8a))
    (hinc : lookupName env "%inc26"
      = some (.int 64 (BitVec.ofNat 64 (start + 1))))
    (h563 : lookupName env "%add563"
      = some (.int 64 (BitVec.ofNat 64 (start + 9))))
    (hconv : lookupName env "%conv25" = some (.int 64 (BitVec.ofNat 64 lead)))
    (hn : lookupName env "%n" = some (.int 64 (BitVec.ofNat 64 n)))
    (hread : readBytes s.mem a n = some bs)
    (hslicea : readBytes s.mem (a + (start + 1)) 8 = some bs8a)
    (hsliceb : readBytes s.mem (a + (start + 9)) 8 = some bs8b)
    (hstart : start + 9 ≤ n) (hnlt : n < 2 ^ 63)
    (hlead : lead = digitFold bs start 1)
    (hval : d8Value bs8a = some w) (hw : w < 2 ^ 32)
    (hsep : v8a + 4 ≤ a ∨ a + n ≤ v8a)
    (hsep2 : v8a + 4 ≤ a + (start + 9) ∨ a + (start + 9) + 8 ≤ v8a)
    (hguard : NumFastSeams.fpGuard
      (BitVec.ofNat 64 (start + 9) + 0x8#64) 0x9#64 (BitVec.ofNat 64 n) = 1)
    (hmore : start + 17 < n)
    (hval2 : d8Value bs8b = some w2) (hw2 : w2 < 2 ^ 32) :
    ∃ e : State, intRunInv (writeBytes (writeBytes s.mem v8a (natToBytes w 4)) v8a
      (natToBytes w2 4)) a n (start + 17) 17 bs (n - (start + 17)) e 0 ∧
      ∀ k, runFuel (stage2NumFastCalls epow) (6 + k) numFastBody (stateAt env s)
        = runFuel (stage2NumFastCalls epow) k numFastBody e := by
  have hpos : ((BitVec.ofNat 64 (start + 1)).signExtend 64).toNat < 2 ^ 63 := by
    rw [ofNat64_signExtend_toNat (by omega)]; omega
  have hpos9 : ((BitVec.ofNat 64 (start + 9)).signExtend 64).toNat < 2 ^ 63 := by
    rw [ofNat64_signExtend_toNat (by omega)]; omega
  have hslicea' : readBytes s.mem
      (a + ((BitVec.ofNat 64 (start + 1)).signExtend 64).toNat) 8 = some bs8a := by
    rw [ofNat64_signExtend_toNat (by omega)]; exact hslicea
  let st1 : State := { s with mem := writeBytes s.mem v8a (natToBytes w 4),
                               next := s.next, pc := "cleanup",
                               pre := some "while.body.preheader" }
  have hstep1 : step (stage2NumFastCalls epow) numFastBody (stateAt env s) =
      .jump (stateAt (NumFastSeams.fpPreEnv env a (BitVec.ofNat 64 (start + 1)) v8a 1)
        st1) :=
    NumFastSeams.fpPreheader_step (epow := epow) hpc hp hinc hv8 hpos hslicea' hval hw
  have hback : readBytes (writeBytes s.mem v8a (natToBytes w 4)) v8a 4
      = some (natToBytes w 4) :=
    (NumFastSeams.numD8Answer_writes (p := a + (start + 1)) (v := v8a) (w := w)
      (bs := bs8a) (mem := s.mem) (next := s.next) hslicea hval hw).2.1
  have hread1 : readBytes (writeBytes s.mem v8a (natToBytes w 4)) v8a 4
      = some (natToBytes (BitVec.ofNat 32 w).toNat 4) := by
    rw [ofNat32_toNat hw]; exact hback
  have hp1 : lookupName (NumFastSeams.fpPreEnv env a (BitVec.ofNat 64 (start + 1)) v8a 1)
      "%p" = some (.ptr a) := by
    simp only [NumFastSeams.fpPreEnv]; block_lk
  have hconv1 : lookupName (NumFastSeams.fpPreEnv env a (BitVec.ofNat 64 (start + 1)) v8a 1)
      "%conv25" = some (.int 64 (BitVec.ofNat 64 lead)) := by
    simp only [NumFastSeams.fpPreEnv]; block_lk
  have h563_1 : lookupName (NumFastSeams.fpPreEnv env a (BitVec.ofNat 64 (start + 1)) v8a 1)
      "%add563" = some (.int 64 (BitVec.ofNat 64 (start + 9))) := by
    simp only [NumFastSeams.fpPreEnv]; block_lk
  have hv8_1 : lookupName (NumFastSeams.fpPreEnv env a (BitVec.ofNat 64 (start + 1)) v8a 1)
      "%v8" = some (.ptr v8a) := by
    simp only [NumFastSeams.fpPreEnv]; block_lk
  have hn1 : lookupName (NumFastSeams.fpPreEnv env a (BitVec.ofNat 64 (start + 1)) v8a 1)
      "%n" = some (.int 64 (BitVec.ofNat 64 n)) := by
    simp only [NumFastSeams.fpPreEnv]; block_lk
  have hread2 : readBytes (writeBytes s.mem v8a (natToBytes w 4))
      (a + ((BitVec.ofNat 64 (start + 9)).signExtend 64).toNat) 8 = some bs8b := by
    rw [ofNat64_signExtend_toNat (by omega)]
    rw [readBytes_writeBytes_local (m := s.mem) (w := w) hsep2]
    exact hsliceb
  obtain ⟨e2, hpc2, hpre2, hmem2, henv2, hcont2⟩ :=
    NumFastSeams.fpFastSecond_run (epow := epow)
      (env := NumFastSeams.fpPreEnv env a (BitVec.ofNat 64 (start + 1)) v8a 1)
      (s := st1)
      (a := a) (v8a := v8a) (ip := BitVec.ofNat 64 lead)
      (add568 := BitVec.ofNat 64 (start + 9)) (nv := BitVec.ofNat 64 n)
      (w := BitVec.ofNat 32 w) (w2 := w2) (bs8 := bs8b)
      rfl rfl hp1 hconv1 h563_1 hv8_1 hn1 hread1 hguard hpos9 hread2 hval2 hw2
  have hfold1 : BitVec.ofNat 64 lead * 0x5f5e100#64 + BitVec.ofNat 64 w
      = BitVec.ofNat 64 (digitFold bs start 9) :=
    NumFastSeams.fpFirstFold hread hlead hslicea hstart hval
  have hfold2 : BitVec.ofNat 64 (digitFold bs start 9) * 0x5f5e100#64
      + BitVec.ofNat 64 w2 = BitVec.ofNat 64 (digitFold bs start 17) :=
    NumFastSeams.fpSecondFold hread hsliceb (by omega) hval2
  have hip3 : lookupName e2.env "%add35"
      = some (.int 64 (BitVec.ofNat 64 (digitFold bs start 17))) := by
    rw [henv2]
    have hcell : lookupName (NumFastSeams.fpSecondEnv
        (NumFastSeams.fpPreEnv env a (BitVec.ofNat 64 (start + 1)) v8a 1)
        a v8a (BitVec.ofNat 64 lead) (BitVec.ofNat 64 (start + 9))
        (BitVec.ofNat 64 n) (BitVec.ofNat 32 w) w2) "%add35"
        = some (.int 64 ((BitVec.ofNat 64 lead * 0x5f5e100#64
            + BitVec.ofNat 64 (BitVec.ofNat 32 w).toNat) * 0x5f5e100#64
            + BitVec.ofNat 64 (BitVec.ofNat 32 w2).toNat)) := by
      simp only [NumFastSeams.fpSecondEnv, NumFastSeams.fpCleanupEnv]; block_lk
    rw [hcell, ofNat32_toNat hw, ofNat32_toNat hw2, hfold1, hfold2]
  have hid3 : lookupName e2.env "%add29569933" = some (.int 64 0x11#64) := by
    rw [henv2]
    have hcell : lookupName (NumFastSeams.fpSecondEnv
        (NumFastSeams.fpPreEnv env a (BitVec.ofNat 64 (start + 1)) v8a 1)
        a v8a (BitVec.ofNat 64 lead) (BitVec.ofNat 64 (start + 9))
        (BitVec.ofNat 64 n) (BitVec.ofNat 32 w) w2) "%add29569933"
        = some (.int 64 (0x9#64 + 0x8#64)) := by
      simp only [NumFastSeams.fpSecondEnv, NumFastSeams.fpCleanupEnv]; block_lk
    rw [hcell]
    have h : (0x9#64 + 0x8#64 : BitVec 64) = 0x11#64 := by decide
    rw [h]
  have hi3 : lookupName e2.env "%add568934"
      = some (.int 64 (BitVec.ofNat 64 (start + 17))) := by
    rw [henv2]
    have hcell : lookupName (NumFastSeams.fpSecondEnv
        (NumFastSeams.fpPreEnv env a (BitVec.ofNat 64 (start + 1)) v8a 1)
        a v8a (BitVec.ofNat 64 lead) (BitVec.ofNat 64 (start + 9))
        (BitVec.ofNat 64 n) (BitVec.ofNat 32 w) w2) "%add568934"
        = some (.int 64 (BitVec.ofNat 64 (start + 9) + 0x8#64)) := by
      simp only [NumFastSeams.fpSecondEnv, NumFastSeams.fpCleanupEnv]; block_lk
    rw [hcell]
    have h : BitVec.ofNat 64 (start + 9) + 0x8#64 = BitVec.ofNat 64 (start + 17) := by
      rw [NumFastStarts.ofNat64_add_const (j := start + 9) (k := 8) (by omega)]
    rw [h]
  have hn3 : lookupName e2.env "%n" = some (.int 64 (BitVec.ofNat 64 n)) := by
    rw [henv2]
    simp only [NumFastSeams.fpSecondEnv, NumFastSeams.fpCleanupEnv,
      NumFastSeams.fpBodyEnv2, NumFastSeams.fpBodyEnv, NumFastSeams.fpFirstEnv,
      NumFastSeams.fpPreEnv]; block_lk
  have hden : denoteCode (stage2NumFastCalls epow) NumFastSeams.fpWhileEndInstrs
      (stateAt e2.env e2) = some (stateAt (NumFastSeams.fpWhileEndEnv e2.env
        (BitVec.ofNat 64 (start + 17)) 0x11#64
        (BitVec.ofNat 64 (digitFold bs start 17)) (BitVec.ofNat 64 n)) e2) :=
    NumFastSeams.fpWhileEnd_denote_cleanup (epow := epow) (env := e2.env) (s := e2)
      hpre2 hip3 hid3 hi3 hn3
  have hbit : evalICmp .ult (BitVec.ofNat 64 (start + 17)) (BitVec.ofNat 64 n) = 1 :=
    NumFastSeams.ult_ofNat_one hmore (by omega)
  have hread' : readBytes (writeBytes (writeBytes s.mem v8a (natToBytes w 4)) v8a
      (natToBytes w2 4)) a n = some bs := by
    rw [readBytes_writeBytes_local (m := writeBytes s.mem v8a (natToBytes w 4))
      (w := w2) hsep, readBytes_writeBytes_local (m := s.mem) (w := w) hsep]
    exact hread
  have hp3 : lookupName (NumFastSeams.fpWhileEndEnv e2.env
      (BitVec.ofNat 64 (start + 17)) 0x11#64
      (BitVec.ofNat 64 (digitFold bs start 17)) (BitVec.ofNat 64 n)) "%p"
      = some (.ptr a) :=
    fpWhileEndEnv_p (by
      rw [henv2]
      simp only [NumFastSeams.fpSecondEnv, NumFastSeams.fpCleanupEnv,
        NumFastSeams.fpBodyEnv2, NumFastSeams.fpBodyEnv, NumFastSeams.fpFirstEnv,
        NumFastSeams.fpPreEnv]; block_lk)
  have hn3' : lookupName (NumFastSeams.fpWhileEndEnv e2.env
      (BitVec.ofNat 64 (start + 17)) 0x11#64
      (BitVec.ofNat 64 (digitFold bs start 17)) (BitVec.ofNat 64 n)) "%n"
      = some (.int 64 (BitVec.ofNat 64 n)) :=
    fpWhileEndEnv_n hn3
  obtain ⟨e, hinv, hcont⟩ := fpWhileEnd_entry (epow := epow)
    (env := e2.env) (s := e2)
    (i := BitVec.ofNat 64 (start + 17)) (idig := 0x11#64)
    (ip := BitVec.ofNat 64 (digitFold bs start 17))
    (mem := writeBytes (writeBytes s.mem v8a (natToBytes w 4)) v8a (natToBytes w2 4))
    (p := a) (n := n) (i0 := start + 17) (d0 := 17) (bs := bs)
    hpc2 hden hbit hmem2 hp3 hn3' hread' rfl rfl (by
      rw [show start + 17 - 17 = start from by omega,
        show min 17 19 = 17 from by decide])
    hmore hnlt (by omega)
  rw [stateAt_env_self e2] at hcont
  refine ⟨e, hinv, ?_⟩
  intro k
  rw [show 6 + k = 1 + (3 + (2 + k)) from by omega,
    runFuel_jump_prefix hstep1, hcont2 (2 + k), hcont k]

/-! ### The case split at the two reader answers

The four implications above are the reader's `Option` answer's four shapes: the
first read's `none`, and its `some` split by the guard and then by the second
read's answer. -/

/-- **The taken guard's entry into `intRunInv`.**  At `while.body.preheader`
with `if.then22`'s cells and the walk's lexeme readable, the fast path's four
paths reach the digit head at the run's invariant:

* the first read refuses: four steps, `i0 = start + 1`, `d0 = 1`;
* the first read succeeds and the guard refuses: four steps, `i0 = start + 9`,
  `d0 = 9`, under `start + 9 < n`;
* the first read succeeds, the guard is taken and the second read refuses: six
  steps, `i0 = start + 9`, `d0 = 9`, under `start + 9 < n`;
* both reads succeed: six steps, `i0 = start + 17`, `d0 = 17`, under
  `start + 17 < n`.

The two-group branches take the second group's eight bytes as readable and the
reader's local as separated from them, because those branches are the ones that
read and write there; a lexeme that stops before the second group is covered by
the first two branches, which do not ask for either.  `hsep` is the same
separation at the first group, which both folds write to. -/
theorem fpTakenGuard_entry {epow : Int → Option EPow} {env : Env} {s : State}
    {a v8a start n lead : Nat} {bs bs8a bs8b : List UInt8}
    (hpc : s.pc = "while.body.preheader")
    (hpre : s.pre = some "if.then22")
    (hp : lookupName env "%p" = some (.ptr a))
    (hv8 : lookupName env "%v8" = some (.ptr v8a))
    (hinc : lookupName env "%inc26"
      = some (.int 64 (BitVec.ofNat 64 (start + 1))))
    (h563 : lookupName env "%add563"
      = some (.int 64 (BitVec.ofNat 64 (start + 9))))
    (hconv : lookupName env "%conv25" = some (.int 64 (BitVec.ofNat 64 lead)))
    (hn : lookupName env "%n" = some (.int 64 (BitVec.ofNat 64 n)))
    (hread : readBytes s.mem a n = some bs)
    (hslicea : readBytes s.mem (a + (start + 1)) 8 = some bs8a)
    (hstart : start + 9 ≤ n) (hnlt : n < 2 ^ 63)
    (hlead : lead = digitFold bs start 1)
    (hsep : v8a + 4 ≤ a ∨ a + n ≤ v8a) :
    (d8Value bs8a = none →
        ∃ e : State, intRunInv s.mem a n (start + 1) 1 bs (n - (start + 1)) e 0 ∧
          ∀ k, runFuel (stage2NumFastCalls epow) (4 + k) numFastBody (stateAt env s)
            = runFuel (stage2NumFastCalls epow) k numFastBody e)
    ∧ (∀ (w : Nat), d8Value bs8a = some w → w < 2 ^ 32 →
        NumFastSeams.fpGuard (BitVec.ofNat 64 (start + 9) + 0x8#64) 0x9#64
          (BitVec.ofNat 64 n) = 0 →
        start + 9 < n →
        ∃ e : State, intRunInv (writeBytes s.mem v8a (natToBytes w 4)) a n (start + 9) 9 bs
      (n - (start + 9)) e 0 ∧
          ∀ k, runFuel (stage2NumFastCalls epow) (4 + k) numFastBody (stateAt env s)
            = runFuel (stage2NumFastCalls epow) k numFastBody e)
    ∧ (readBytes s.mem (a + (start + 9)) 8 = some bs8b →
        (v8a + 4 ≤ a + (start + 9) ∨ a + (start + 9) + 8 ≤ v8a) →
        ∀ (w : Nat), d8Value bs8a = some w → w < 2 ^ 32 →
        NumFastSeams.fpGuard (BitVec.ofNat 64 (start + 9) + 0x8#64) 0x9#64
          (BitVec.ofNat 64 n) = 1 →
        start + 9 < n → d8Value bs8b = none →
        ∃ e : State, intRunInv (writeBytes s.mem v8a (natToBytes w 4)) a n (start + 9) 9 bs
      (n - (start + 9)) e 0 ∧
          ∀ k, runFuel (stage2NumFastCalls epow) (6 + k) numFastBody (stateAt env s)
            = runFuel (stage2NumFastCalls epow) k numFastBody e)
    ∧ (readBytes s.mem (a + (start + 9)) 8 = some bs8b →
        (v8a + 4 ≤ a + (start + 9) ∨ a + (start + 9) + 8 ≤ v8a) →
        ∀ (w w2 : Nat), d8Value bs8a = some w → w < 2 ^ 32 →
        NumFastSeams.fpGuard (BitVec.ofNat 64 (start + 9) + 0x8#64) 0x9#64
          (BitVec.ofNat 64 n) = 1 →
        start + 17 < n → d8Value bs8b = some w2 → w2 < 2 ^ 32 →
        ∃ e : State, intRunInv (writeBytes (writeBytes s.mem v8a (natToBytes w 4)) v8a
      (natToBytes w2 4)) a n (start + 17) 17 bs (n - (start + 17)) e 0 ∧
          ∀ k, runFuel (stage2NumFastCalls epow) (6 + k) numFastBody (stateAt env s)
            = runFuel (stage2NumFastCalls epow) k numFastBody e) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hnone
    exact fpTaken_refuse1 hpc hpre hp hv8 hinc h563 hconv hn hread hslicea hstart hnlt
      hlead hnone
  · intro w hsome hw hguard hmore
    exact fpTaken_exit hpc hpre hp hv8 hinc h563 hconv hn hread hslicea hstart hnlt
      hlead hsome hw hsep hguard hmore
  · intro hsliceb hsep2 w hsome hw hguard hmore hnone
    exact fpTaken_refuse2 hpc hpre hp hv8 hinc h563 hconv hn hread hslicea hsliceb
      hstart hnlt hlead hsome hw hsep hsep2 hguard hmore hnone
  · intro hsliceb hsep2 w w2 hsome hw hguard hmore hsome2 hw2
    exact fpTaken_fold2 hpc hpre hp hv8 hinc h563 hconv hn hread hslicea hsliceb
      hstart hnlt hlead hsome hw hsep hsep2 hguard hmore hsome2 hw2

/-! ### The guard's own block

`if.then22` writes the lead's value, the index after it, the guard's sum and the
guard's own test; taken, the block's `condbr` enters `while.body.preheader`.  The
step below is that edge, and `fpIfThen22_entry` composes it with the case split,
so the entry is stated at the dispatch's own block: the guard's zero is the `Nat`
fact that the fast path has its nine bytes, and the leader's value is the fold's
first digit.

The guard's own arithmetic: `%cmp27564.not = (%i.0 + 9 ugt %n)` is zero exactly
when `%n` is not below `%i.0 + 9`, so `%i.0 + 9 ≤ %n` at the `Nat` readings
(`taken_fast_guard`); `%inc26` and `%add563` are the block's own sums, read as
`%i.0 + 1` and `%i.0 + 9`; and `%conv25` is the leader's low nibble, which is the
digit's value and so `digitFold`'s first digit. -/

/-- **`if.then22`'s taken edge.**  The guard's zero enters the fast path's
preheader; the block's own cells are the environment the reader's call reads. -/
theorem fpIfThen22_step_taken {calls : Calls} {env : Env} {s : State} {i0 : Nat}
    {b0 : UInt8} {n : Nat}
    (hpc : s.pc = "if.then22")
    (h1 : lookupName env "%1" = some (.int 8 (JsonScanLane.vByte b0)))
    (hi : lookupName env "%i.0" = some (.int 64 (BitVec.ofNat 64 i0)))
    (hn : lookupName env "%n" = some (.int 64 (BitVec.ofNat 64 n)))
    (hbit : evalICmp .ugt (BitVec.ofNat 64 i0 + 0x9#64) (BitVec.ofNat 64 n) = 0) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (NumFastStarts.ifThen22Env env i0 b0 n)
        { s with pc := "while.body.preheader", pre := some "if.then22" }) := by
  refine numFast_step_at (s' := stateAt (NumFastStarts.ifThen22Env env i0 b0 n) s)
    (b := ⟨"if.then22",
      [Instr.binop "%3" (BinOp.and) 8 (Operand.reg "%1") (Operand.imm (Const.int 8 0x0f#8)),
       Instr.zext "%conv25" 8 64 (Operand.reg "%3"),
       Instr.binop "%inc26" (BinOp.add) 64 (Operand.reg "%i.0")
         (Operand.imm (Const.int 64 0x0000000000000001#64)),
       Instr.binop "%add563" (BinOp.add) 64 (Operand.reg "%i.0")
         (Operand.imm (Const.int 64 0x0000000000000009#64)),
       Instr.icmp "%cmp27564.not" (IPred.ugt) 64 (Operand.reg "%add563")
         (Operand.reg "%n")],
      Term.condbr (Operand.reg "%cmp27564.not") "while.end" "while.body.preheader"⟩)
    ?_ ?_ ?_
  · simpa only [stateAt, hpc] using numFast_findBlock_if_then22
  · simpa only [denoteCode_nil] using
      NumFastStarts.ifThen22_denote (calls := calls) h1 hi hn
  · have hlk : lookupName (NumFastStarts.ifThen22Env env i0 b0 n) "%cmp27564.not"
        = some (.int 1
          (evalICmp .ugt (BitVec.ofNat 64 i0 + 0x9#64) (BitVec.ofNat 64 n))) :=
      lookupName_cons_self ..
    rw [numFast_execTerm_condbr_zero _ "%cmp27564.not" "while.end" "while.body.preheader"
      hlk hbit]
    simp only [stateAt, hpc]

/-- **The guard's taken sum, as a `Nat`.**  `%add563 ugt %n` at zero is
`i0 + 9 ≤ n`. -/
theorem taken_fast_guard {i0 n : Nat} (h64 : i0 + 9 < 2 ^ 64)
    (hbit : evalICmp .ugt (BitVec.ofNat 64 i0 + 0x9#64) (BitVec.ofNat 64 n) = 0) :
    i0 + 9 ≤ n := by
  by_contra hcon
  have hn64 : n < 2 ^ 64 := by omega
  have hlt : (BitVec.ofNat 64 n).toNat <
      (BitVec.ofNat 64 i0 + 0x9#64).toNat := by
    rw [NumFastStarts.toNat_add_const h64, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn64]
    omega
  have hone := (NumFastStarts.ugt_iff_one (BitVec.ofNat 64 i0 + 0x9#64)
    (BitVec.ofNat 64 n)).mpr hlt
  rw [hbit] at hone
  exact absurd hone (by decide)

/-- **The guard's taken entry, at `if.then22`.**  At the dispatch's block with
the byte after the sign a lead digit and the guard's sum inside the length, the
taken edge enters the fast path and the four paths reach the run's invariant:
five steps for the one-group paths and seven for the two-group ones. -/
theorem fpIfThen22_entry {epow : Int → Option EPow} {env : Env} {s : State}
    {a v8a start n lead : Nat} {b0 : UInt8} {bs : List UInt8}
    (hpc : s.pc = "if.then22")
    (hpre : s.pre = some "if.else")
    (hp : lookupName env "%p" = some (.ptr a))
    (hv8 : lookupName env "%v8" = some (.ptr v8a))
    (h1 : lookupName env "%1" = some (.int 8 (JsonScanLane.vByte b0)))
    (hi : lookupName env "%i.0" = some (.int 64 (BitVec.ofNat 64 start)))
    (hn : lookupName env "%n" = some (.int 64 (BitVec.ofNat 64 n)))
    (hread : readBytes s.mem a n = some bs)
    (hltn : start < n)
    (hbyte : readByte s.mem (a + start) = some b0)
    (hlead : lead = (JsonScanLane.vByte b0 &&& 0x0f#8).toNat)
    (hdig : 0x31 ≤ b0 ∧ b0 ≤ 0x39)
    (hsep : v8a + 4 ≤ a ∨ a + n ≤ v8a)
    (hnlt : n < 2 ^ 63)
    (hbit : evalICmp .ugt (BitVec.ofNat 64 start + 0x9#64) (BitVec.ofNat 64 n) = 0) :
    (d8Value ((bs.drop (start + 1)).take 8) = none →
        ∃ e : State, intRunInv s.mem a n (start + 1) 1 bs (n - (start + 1)) e 0 ∧
          ∀ k, runFuel (stage2NumFastCalls epow) (5 + k) numFastBody (stateAt env s)
            = runFuel (stage2NumFastCalls epow) k numFastBody e)
    ∧ (∀ (w : Nat), d8Value ((bs.drop (start + 1)).take 8) = some w → w < 2 ^ 32 →
        NumFastSeams.fpGuard (BitVec.ofNat 64 (start + 9) + 0x8#64) 0x9#64
          (BitVec.ofNat 64 n) = 0 →
        start + 9 < n →
        ∃ e : State, intRunInv (writeBytes s.mem v8a (natToBytes w 4)) a n (start + 9) 9 bs
          (n - (start + 9)) e 0 ∧
          ∀ k, runFuel (stage2NumFastCalls epow) (5 + k) numFastBody (stateAt env s)
            = runFuel (stage2NumFastCalls epow) k numFastBody e)
    ∧ (readBytes s.mem (a + (start + 9)) 8
          = some ((bs.drop (start + 9)).take 8) →
        (v8a + 4 ≤ a + (start + 9) ∨ a + (start + 9) + 8 ≤ v8a) →
        ∀ (w : Nat), d8Value ((bs.drop (start + 1)).take 8) = some w → w < 2 ^ 32 →
        NumFastSeams.fpGuard (BitVec.ofNat 64 (start + 9) + 0x8#64) 0x9#64
          (BitVec.ofNat 64 n) = 1 →
        start + 9 < n → d8Value ((bs.drop (start + 9)).take 8) = none →
        ∃ e : State, intRunInv (writeBytes s.mem v8a (natToBytes w 4)) a n (start + 9) 9 bs
          (n - (start + 9)) e 0 ∧
          ∀ k, runFuel (stage2NumFastCalls epow) (7 + k) numFastBody (stateAt env s)
            = runFuel (stage2NumFastCalls epow) k numFastBody e)
    ∧ (readBytes s.mem (a + (start + 9)) 8
          = some ((bs.drop (start + 9)).take 8) →
        (v8a + 4 ≤ a + (start + 9) ∨ a + (start + 9) + 8 ≤ v8a) →
        ∀ (w w2 : Nat), d8Value ((bs.drop (start + 1)).take 8) = some w → w < 2 ^ 32 →
        NumFastSeams.fpGuard (BitVec.ofNat 64 (start + 9) + 0x8#64) 0x9#64
          (BitVec.ofNat 64 n) = 1 →
        start + 17 < n → d8Value ((bs.drop (start + 9)).take 8) = some w2 → w2 < 2 ^ 32 →
        ∃ e : State, intRunInv (writeBytes (writeBytes s.mem v8a (natToBytes w 4)) v8a
          (natToBytes w2 4)) a n (start + 17) 17 bs (n - (start + 17)) e 0 ∧
          ∀ k, runFuel (stage2NumFastCalls epow) (7 + k) numFastBody (stateAt env s)
            = runFuel (stage2NumFastCalls epow) k numFastBody e) := by
  have hguard : start + 9 ≤ n := taken_fast_guard (by omega) hbit
  have hblen : bs.length = n := JsonEntrySteps.readBytes_length s.mem a n hread
  have hb_toNat : 49 ≤ b0.toNat ∧ b0.toNat ≤ 57 :=
    ⟨UInt8.le_iff_toNat_le.mp hdig.1, UInt8.le_iff_toNat_le.mp hdig.2⟩
  have hdigB : IsDigitB b0 = true := by
    unfold IsDigitB
    rw [Bool.and_eq_true]
    exact ⟨decide_eq_true (UInt8.le_iff_toNat_le.mpr (by
        show (0x30 : UInt8).toNat ≤ b0.toNat
        rw [show (0x30 : UInt8).toNat = 48 from by decide]; omega)),
      decide_eq_true (UInt8.le_iff_toNat_le.mpr (by
        show b0.toNat ≤ (0x39 : UInt8).toNat
        rw [show (0x39 : UInt8).toNat = 57 from by decide]; omega))⟩
  have hget : bs.getD start 0 = b0 := getD_of_readBytes hread hltn hbyte
  have hfold : lead = digitFold bs start 1 := by
    rw [hlead, digit_and_toNat hdigB]
    rw [show (1 : Nat) = 0 + 1 from rfl, digitFold_succ (by omega),
      Nat.add_zero, digitFold_zero, Nat.zero_mul, Nat.zero_add, hget]
  have hstep0 : step (stage2NumFastCalls epow) numFastBody (stateAt env s) =
      .jump (stateAt (NumFastStarts.ifThen22Env env start b0 n)
        { s with pc := "while.body.preheader", pre := some "if.then22" }) :=
    fpIfThen22_step_taken (calls := stage2NumFastCalls epow) hpc h1 hi hn hbit
  have hinc' : lookupName (NumFastStarts.ifThen22Env env start b0 n) "%inc26"
      = some (.int 64 (BitVec.ofNat 64 (start + 1))) := by
    simp only [NumFastStarts.ifThen22Env]
    rw [ofNat64_add_one (by omega)]
    block_lk
  have h563' : lookupName (NumFastStarts.ifThen22Env env start b0 n) "%add563"
      = some (.int 64 (BitVec.ofNat 64 (start + 9))) := by
    simp only [NumFastStarts.ifThen22Env]
    rw [NumFastStarts.ofNat64_add_const (j := start) (k := 9) (by omega)]
    block_lk
  have hconv' : lookupName (NumFastStarts.ifThen22Env env start b0 n) "%conv25"
      = some (.int 64 (BitVec.ofNat 64 lead)) := by
    simp only [NumFastStarts.ifThen22Env, ← hlead]; block_lk
  have hp' : lookupName (NumFastStarts.ifThen22Env env start b0 n) "%p"
      = some (.ptr a) := by
    simp only [NumFastStarts.ifThen22Env]; block_lk
  have hv8' : lookupName (NumFastStarts.ifThen22Env env start b0 n) "%v8"
      = some (.ptr v8a) := by
    simp only [NumFastStarts.ifThen22Env]; block_lk
  have hn' : lookupName (NumFastStarts.ifThen22Env env start b0 n) "%n"
      = some (.int 64 (BitVec.ofNat 64 n)) := by
    simp only [NumFastStarts.ifThen22Env]; block_lk
  have hslicea : readBytes s.mem (a + (start + 1)) 8
      = some ((bs.drop (start + 1)).take 8) := by
    obtain ⟨-, hdrop⟩ := readBytes_split s.mem a (start + 1) (n - (start + 1))
      (bs := bs) (by
        rw [Nat.add_sub_cancel' (by omega : start + 1 ≤ n)]; exact hread)
    obtain ⟨h8, -⟩ := readBytes_split s.mem (a + (start + 1)) 8
      (n - (start + 1) - 8) (by
        rw [show 8 + (n - (start + 1) - 8) = n - (start + 1) from by omega]
        exact hdrop)
    exact h8
  have hbase := fpTakenGuard_entry (epow := epow)
    (env := NumFastStarts.ifThen22Env env start b0 n)
    (s := { s with pc := "while.body.preheader", pre := some "if.then22" })
    (a := a) (v8a := v8a) (start := start) (n := n) (lead := lead)
    (bs := bs) (bs8a := (bs.drop (start + 1)).take 8)
    (bs8b := (bs.drop (start + 9)).take 8)
    rfl rfl hp' hv8' hinc' h563' hconv' hn' hread hslicea hguard hnlt hfold hsep
  exact ⟨fun hnone => by
      obtain ⟨e, hinv, hcont⟩ := hbase.1 hnone
      exact ⟨e, hinv, fun k => by
        rw [show 5 + k = 1 + (4 + k) from by omega,
          runFuel_jump_prefix hstep0, hcont k]⟩,
    fun w hsome hw hgd hmore => by
      obtain ⟨e, hinv, hcont⟩ := hbase.2.1 w hsome hw hgd hmore
      exact ⟨e, hinv, fun k => by
        rw [show 5 + k = 1 + (4 + k) from by omega,
          runFuel_jump_prefix hstep0, hcont k]⟩,
    fun hsb hsep2 w hsome hw hgd hmore hnone => by
      obtain ⟨e, hinv, hcont⟩ := hbase.2.2.1 hsb hsep2 w hsome hw hgd hmore hnone
      exact ⟨e, hinv, fun k => by
        rw [show 7 + k = 1 + (6 + k) from by omega,
          runFuel_jump_prefix hstep0, hcont k]⟩,
    fun hsb hsep2 w w2 hsome hw hgd hmore hsome2 hw2 => by
      obtain ⟨e, hinv, hcont⟩ :=
        hbase.2.2.2 hsb hsep2 w w2 hsome hw hgd hmore hsome2 hw2
      exact ⟨e, hinv, fun k => by
        rw [show 7 + k = 1 + (6 + k) from by omega,
          runFuel_jump_prefix hstep0, hcont k]⟩⟩

/-! ### The fraction's eight-digit entry

`while.cond91.preheader` is the fraction's guard: `%add92582 = %i.5 + 9` and
`%cmp93583.not = %add92582 > %n`, so its zero says the fraction has its nine
bytes and its one is the refusal `fracRun_start` is stated behind.  Taken, the
block enters `while.body100.preheader`, whose reader is the same `num_d8_el1`
call the integer path makes at `while.body.preheader`; `cleanup112` folds the
group into `%fr` at the `10 ^ 8` weight, `while.body100` reads the second group,
`cleanup112.thread` carries a refusal, and `while.end115` merges whichever edge
left.

The accumulator starts at zero and the count at zero, so the four shapes are the
integer fast path's at the fraction's own start: a refused first read leaves the
count `0` at the index `start`, and the loop's two edges leave `8` at
`start + 8` or `16` at `start + 16`.  The loop's count test is
`%add96588941 < 12`, so a second group is admitted only at `8` — `fpGuard_sixteen`
is the second fold's immediate refusal — and at most sixteen digits are taken,
inside `digitFold`'s nineteen-digit cap. -/

/-- The fraction path's cell lookup.  The two-group shapes read through three
builders, so the general form's `assumption` probe — which asks `isDefEq` to
compare the whole goal with every hypothesis — is left to the end: the peel runs
first and the cell is taken before any definitional comparison. -/
macro "frac_lk" : tactic => `(tactic|
  (first
   | (simp (config := { failIfUnchanged := false }) only [cells]
      repeat rw [lookupName_cons_ne _ _ (by decide)]
      first
       | rw [lookupName_cons_self]
       | rfl)
   | assumption))

/-- The fraction preheader's environment: the reader's return, its own test, and
the pointer the call was given. -/
def fpPre100Env (env : Env) (a : Nat) (idx : BitVec 64) (v8a : Nat)
    (call : BitVec 32) : Env :=
  ("%tobool104.not940", .int 1 (evalICmp .eq call 0x0#32)) ::
  ("%call103939", .int 32 call) ::
  ("%add.ptr102938", .ptr (a + (idx.signExtend 64).toNat)) :: env

/-- `while.body100.preheader`, from its `findBlock` pin. -/
def fpBody100PreInstrs : List Instr :=
  [Instr.callVoid "llvm.lifetime.start.p0" [((Ty.int 64), (Operand.imm (Const.int 64 0x0000000000000004#64))),
                       (Ty.ptr, (Operand.reg "%v8101"))],
   Instr.gep "%add.ptr102938" (Ty.int 8) (Operand.reg "%p") (Operand.reg "%inc77"),
   Instr.call "%call103939" (Ty.int 32) "num_d8_el1" [(Ty.ptr, (Operand.reg "%add.ptr102938")),
                       (Ty.ptr, (Operand.reg "%v8101"))],
   Instr.icmp "%tobool104.not940" (IPred.eq) 32 (Operand.reg "%call103939")
     (Operand.imm (Const.int 32 0x00000000#32))]

theorem findBlock_fpBody100Pre :
    numFastBody.findBlock "while.body100.preheader" =
      some ⟨"while.body100.preheader", fpBody100PreInstrs,
        Term.condbr (Operand.reg "%tobool104.not940") "cleanup112.thread" "cleanup112"⟩ := by
  simpa only [fpBody100PreInstrs] using numFast_findBlock_while_body100_preheader

/-- `while.body100.preheader`'s chain at a successful reader: the marker, the
pointer arithmetic, the call's answer and its test. -/
theorem fpPre100_denote_ok {epow : Int → Option EPow} {env : Env} {s : State}
    {a v8a w : Nat} {idx : BitVec 64} {bs : List UInt8}
    (hp : lookupName env "%p" = some (.ptr a))
    (hi : lookupName env "%inc77" = some (.int 64 idx))
    (hv8 : lookupName env "%v8101" = some (.ptr v8a))
    (hpos : (idx.signExtend 64).toNat < 2 ^ 63)
    (hread : readBytes s.mem (a + (idx.signExtend 64).toNat) 8 = some bs)
    (hval : d8Value bs = some w) (hw : w < 2 ^ 32) :
    denoteCode (stage2NumFastCalls epow) fpBody100PreInstrs (stateAt env s) =
      some (stateAt (fpPre100Env env a idx v8a 1)
        { s with mem := writeBytes s.mem v8a (natToBytes w 4), next := s.next }) := by
  unfold fpBody100PreInstrs
  rw [denoteCode_callVoid_some (stage2NumFastCalls epow) env s "llvm.lifetime.start.p0"
    [((Ty.int 64), (Operand.imm (Const.int 64 0x0000000000000004#64))),
     (Ty.ptr, (Operand.reg "%v8101"))]
    [.int 64 0x0000000000000004#64, .ptr v8a]
    { ret := .int 1 0, mem := s.mem, next := s.next }
    (evalOperands_lifetimeMark (s := s) (w := 4) (ptr := "%v8101") hv8)
    (stage2NumFastCalls_lifetime epow
      [.int 64 0x0000000000000004#64, .ptr v8a] s.mem s.next) _]
  rw [denoteCode_gep8_reg (stage2NumFastCalls epow) env _ "%add.ptr102938" "%p" "%inc77"
    hp hi hpos _]
  rw [denoteCode_call_some (stage2NumFastCalls epow)
    (("%add.ptr102938", .ptr (a + (idx.signExtend 64).toNat)) :: env)
    { s with mem := s.mem, next := s.next }
    "%call103939" (Ty.int 32) "num_d8_el1"
    [(Ty.ptr, (Operand.reg "%add.ptr102938")), (Ty.ptr, (Operand.reg "%v8101"))]
    [.ptr (a + (idx.signExtend 64).toNat), .ptr v8a]
    { ret := .int 32 1, mem := writeBytes s.mem v8a (natToBytes w 4), next := s.next }
    (by
      have hcell : lookupName
          (("%add.ptr102938", .ptr (a + (idx.signExtend 64).toNat)) :: env)
          "%add.ptr102938" = some (.ptr (a + (idx.signExtend 64).toNat)) :=
        lookupName_cons_self ..
      have htail : lookupName
          (("%add.ptr102938", .ptr (a + (idx.signExtend 64).toNat)) :: env) "%v8101"
          = some (.ptr v8a) :=
        lookupName_cons_tail (k := "%add.ptr102938")
          (v := .ptr (a + (idx.signExtend 64).toNat)) (by decide) hv8
      simp only [evalOperands, evalOperand, stateAt, hcell, htail])
    (by
      rw [stage2NumFastCalls_num_d8]
      exact numD8Answer_read hread hval)]
  rw [LeanLLVM.Refinement.JsonScanLane.denoteCode_icmp_imm_w (stage2NumFastCalls epow)
    (("%call103939", .int 32 1) :: ("%add.ptr102938", .ptr (a + (idx.signExtend 64).toNat))
      :: env)
    { s with mem := writeBytes s.mem v8a (natToBytes w 4), next := s.next }
    "%tobool104.not940" "%call103939" .eq (lookupName_cons_self ..) _]
  simp only [denoteCode, denoteRun, State.bindAll, stateAt, fpPre100Env]

/-- `while.body100.preheader`'s chain at a refused reader: the answer is zero
and the memory is the walk's. -/
theorem fpPre100_denote_refuse {epow : Int → Option EPow} {env : Env} {s : State}
    {a v8a : Nat} {idx : BitVec 64} {bs : List UInt8}
    (hp : lookupName env "%p" = some (.ptr a))
    (hi : lookupName env "%inc77" = some (.int 64 idx))
    (hv8 : lookupName env "%v8101" = some (.ptr v8a))
    (hpos : (idx.signExtend 64).toNat < 2 ^ 63)
    (hread : readBytes s.mem (a + (idx.signExtend 64).toNat) 8 = some bs)
    (hval : d8Value bs = none) :
    denoteCode (stage2NumFastCalls epow) fpBody100PreInstrs (stateAt env s) =
      some (stateAt (fpPre100Env env a idx v8a 0)
        { s with mem := s.mem, next := s.next }) := by
  unfold fpBody100PreInstrs
  rw [denoteCode_callVoid_some (stage2NumFastCalls epow) env s "llvm.lifetime.start.p0"
    [((Ty.int 64), (Operand.imm (Const.int 64 0x0000000000000004#64))),
     (Ty.ptr, (Operand.reg "%v8101"))]
    [.int 64 0x0000000000000004#64, .ptr v8a]
    { ret := .int 1 0, mem := s.mem, next := s.next }
    (evalOperands_lifetimeMark (s := s) (w := 4) (ptr := "%v8101") hv8)
    (stage2NumFastCalls_lifetime epow
      [.int 64 0x0000000000000004#64, .ptr v8a] s.mem s.next) _]
  rw [denoteCode_gep8_reg (stage2NumFastCalls epow) env _ "%add.ptr102938" "%p" "%inc77"
    hp hi hpos _]
  rw [denoteCode_call_some (stage2NumFastCalls epow)
    (("%add.ptr102938", .ptr (a + (idx.signExtend 64).toNat)) :: env)
    { s with mem := s.mem, next := s.next }
    "%call103939" (Ty.int 32) "num_d8_el1"
    [(Ty.ptr, (Operand.reg "%add.ptr102938")), (Ty.ptr, (Operand.reg "%v8101"))]
    [.ptr (a + (idx.signExtend 64).toNat), .ptr v8a]
    { ret := .int 32 0, mem := s.mem, next := s.next }
    (by
      have hcell : lookupName
          (("%add.ptr102938", .ptr (a + (idx.signExtend 64).toNat)) :: env)
          "%add.ptr102938" = some (.ptr (a + (idx.signExtend 64).toNat)) :=
        lookupName_cons_self ..
      have htail : lookupName
          (("%add.ptr102938", .ptr (a + (idx.signExtend 64).toNat)) :: env) "%v8101"
          = some (.ptr v8a) :=
        lookupName_cons_tail (k := "%add.ptr102938")
          (v := .ptr (a + (idx.signExtend 64).toNat)) (by decide) hv8
      simp only [evalOperands, evalOperand, stateAt, hcell, htail])
    (by
      rw [stage2NumFastCalls_num_d8]
      exact numD8Answer_refuse hread hval)]
  rw [LeanLLVM.Refinement.JsonScanLane.denoteCode_icmp_imm_w (stage2NumFastCalls epow)
    (("%call103939", .int 32 0) :: ("%add.ptr102938", .ptr (a + (idx.signExtend 64).toNat))
      :: env)
    { s with mem := s.mem, next := s.next }
    "%tobool104.not940" "%call103939" .eq (lookupName_cons_self ..) _]
  simp only [denoteCode, denoteRun, State.bindAll, stateAt, fpPre100Env]

/-- The fraction preheader's step, taken: a success leaves for `cleanup112` with
the word written into `%v8101`'s local. -/
theorem fpPre100_step_ok {epow : Int → Option EPow} {env : Env} {s : State}
    {a v8a w : Nat} {idx : BitVec 64} {bs : List UInt8}
    (hpc : s.pc = "while.body100.preheader")
    (hp : lookupName env "%p" = some (.ptr a))
    (hi : lookupName env "%inc77" = some (.int 64 idx))
    (hv8 : lookupName env "%v8101" = some (.ptr v8a))
    (hpos : (idx.signExtend 64).toNat < 2 ^ 63)
    (hread : readBytes s.mem (a + (idx.signExtend 64).toNat) 8 = some bs)
    (hval : d8Value bs = some w) (hw : w < 2 ^ 32) :
    step (stage2NumFastCalls epow) numFastBody (stateAt env s) =
      .jump (stateAt (fpPre100Env env a idx v8a 1)
        { s with mem := writeBytes s.mem v8a (natToBytes w 4), next := s.next,
                 pc := "cleanup112", pre := some "while.body100.preheader" }) := by
  have hbit : evalICmp .eq ((1 : BitVec 32)) (0 : BitVec 32) = 0 := by decide
  refine numFast_step_at (s' := stateAt (fpPre100Env env a idx v8a 1)
      { s with mem := writeBytes s.mem v8a (natToBytes w 4), next := s.next })
    (b := ⟨"while.body100.preheader", fpBody100PreInstrs,
      Term.condbr (Operand.reg "%tobool104.not940") "cleanup112.thread" "cleanup112"⟩)
    ?_ ?_ ?_
  · simpa only [stateAt, hpc, fpBody100PreInstrs] using findBlock_fpBody100Pre
  · simpa only [denoteCode_nil] using
      fpPre100_denote_ok (epow := epow) hp hi hv8 hpos hread hval hw
  · have hlk : lookupName (fpPre100Env env a idx v8a 1) "%tobool104.not940"
        = some (.int 1 (evalICmp .eq ((1 : BitVec 32)) (0 : BitVec 32))) :=
      lookupName_cons_self ..
    rw [hbit] at hlk
    rw [numFast_execTerm_condbr_zero _ "%tobool104.not940" "cleanup112.thread"
      "cleanup112" hlk rfl]
    simp only [stateAt, hpc]

/-- The fraction preheader's step, refused: the reader's zero leaves for
`cleanup112.thread` with the walk's memory. -/
theorem fpPre100_step_refuse {epow : Int → Option EPow} {env : Env} {s : State}
    {a v8a : Nat} {idx : BitVec 64} {bs : List UInt8}
    (hpc : s.pc = "while.body100.preheader")
    (hp : lookupName env "%p" = some (.ptr a))
    (hi : lookupName env "%inc77" = some (.int 64 idx))
    (hv8 : lookupName env "%v8101" = some (.ptr v8a))
    (hpos : (idx.signExtend 64).toNat < 2 ^ 63)
    (hread : readBytes s.mem (a + (idx.signExtend 64).toNat) 8 = some bs)
    (hval : d8Value bs = none) :
    step (stage2NumFastCalls epow) numFastBody (stateAt env s) =
      .jump (stateAt (fpPre100Env env a idx v8a 0)
        { s with pc := "cleanup112.thread", pre := some "while.body100.preheader" }) := by
  have hbit : evalICmp .eq ((0 : BitVec 32)) (0 : BitVec 32) = 1 := by decide
  refine numFast_step_at (s' := stateAt (fpPre100Env env a idx v8a 0)
      { s with mem := s.mem, next := s.next })
    (b := ⟨"while.body100.preheader", fpBody100PreInstrs,
      Term.condbr (Operand.reg "%tobool104.not940") "cleanup112.thread" "cleanup112"⟩)
    ?_ ?_ ?_
  · simpa only [stateAt, hpc, fpBody100PreInstrs] using findBlock_fpBody100Pre
  · simpa only [denoteCode_nil] using
      fpPre100_denote_refuse (epow := epow) hp hi hv8 hpos hread hval
  · have hlk : lookupName (fpPre100Env env a idx v8a 0) "%tobool104.not940"
        = some (.int 1 (evalICmp .eq ((0 : BitVec 32)) (0 : BitVec 32))) :=
      lookupName_cons_self ..
    rw [hbit] at hlk
    rw [numFast_execTerm_condbr_one _ "%tobool104.not940" "cleanup112.thread"
      "cleanup112" hlk rfl]
    simp only [stateAt, hpc]

/-- `cleanup112.thread`'s three carried cells, in the order the `phi` run
installs them: the last `phi` first. -/
def fpCleanupThread112Env (env : Env) (i fdig fr : BitVec 64) : Env :=
  ("%fr.0584.lcssa", .int 64 fr) :: ("%fdig.0585.lcssa", .int 64 fdig) ::
  ("%i.6586.lcssa", .int 64 i) :: env

/-- `cleanup112.thread`, from its `findBlock` pin. -/
def fpCleanupThread112Instrs : List Instr :=
  [Instr.phi "%i.6586.lcssa" (Ty.int 64) [("while.body100.preheader", (Operand.reg "%inc77")),
                                       ("while.body100", (Operand.reg "%add92587942"))],
   Instr.phi "%fdig.0585.lcssa" (Ty.int 64) [("while.body100.preheader", (Operand.imm (Const.int 64 0x0000000000000000#64))),
                                       ("while.body100", (Operand.reg "%add96588941"))],
   Instr.phi "%fr.0584.lcssa" (Ty.int 64) [("while.body100.preheader", (Operand.imm (Const.int 64 0x0000000000000000#64))),
                                       ("while.body100", (Operand.reg "%add109"))],
   Instr.callVoid "llvm.lifetime.end.p0" [((Ty.int 64), (Operand.imm (Const.int 64 0x0000000000000004#64))),
                       (Ty.ptr, (Operand.reg "%v8101"))]]

theorem findBlock_fpCleanupThread112 :
    numFastBody.findBlock "cleanup112.thread" =
      some ⟨"cleanup112.thread", fpCleanupThread112Instrs, Term.br "while.end115"⟩ := by
  simpa only [fpCleanupThread112Instrs] using numFast_findBlock_cleanup112_thread

/-- The closing marker at the fraction's local: the block's `llvm.lifetime.end`
answers the identity. -/
theorem fpCleanupThread112_denote_pre {epow : Int → Option EPow} {env : Env} {s : State}
    {idx : BitVec 64} {v8a : Nat}
    (hpre : s.pre = some "while.body100.preheader")
    (hi : lookupName env "%inc77" = some (.int 64 idx))
    (hv8 : lookupName env "%v8101" = some (.ptr v8a)) :
    denoteCode (stage2NumFastCalls epow) fpCleanupThread112Instrs (stateAt env s) =
      some (stateAt (fpCleanupThread112Env env idx 0 0) s) := by
  unfold fpCleanupThread112Instrs
  block_phi_run
  rotate_left 1
  · exact hpre
  · rfl
  · simp only [phiIncoming]; rfl
  · exact evalOperand_reg_of env s "%inc77" _ hi
  · simp only [phiIncoming]; rfl
  · exact evalOperand_lit_of _ 64 0
  · simp only [phiIncoming]; rfl
  · exact evalOperand_lit_of _ 64 0
  have hv8' : lookupName
      (runCells [("%i.6586.lcssa", .int 64 idx),
        ("%fdig.0585.lcssa", .int 64 (0 : BitVec 64)),
        ("%fr.0584.lcssa", .int 64 (0 : BitVec 64))] env) "%v8101" = some (.ptr v8a) := by
    simp only [runCells]
    rw [lookupName_cons_ne _ _ (by decide : ("%fr.0584.lcssa" : String) ≠ "%v8101"),
      lookupName_cons_ne _ _ (by decide : ("%fdig.0585.lcssa" : String) ≠ "%v8101"),
      lookupName_cons_ne _ _ (by decide : ("%i.6586.lcssa" : String) ≠ "%v8101")]
    exact hv8
  rw [denoteCode_callVoid_some (stage2NumFastCalls epow)
      (runCells [("%i.6586.lcssa", .int 64 idx),
        ("%fdig.0585.lcssa", .int 64 (0 : BitVec 64)),
        ("%fr.0584.lcssa", .int 64 (0 : BitVec 64))] env) s
      "llvm.lifetime.end.p0"
      [((Ty.int 64), (Operand.imm (Const.int 64 0x0000000000000004#64))),
       (Ty.ptr, (Operand.reg "%v8101"))]
      [.int 64 0x0000000000000004#64, .ptr v8a]
      { ret := .int 1 0, mem := s.mem, next := s.next }
      (evalOperands_lifetimeMark (s := s) (w := 4) (ptr := "%v8101") hv8')
      (NumFastSeams.stage2NumFastCalls_lifetime_end epow
        [.int 64 0x0000000000000004#64, .ptr v8a] s.mem s.next) []]
  simp only [denoteCode_nil, stateAt, fpCleanupThread112Env, runCells]

/-- `cleanup112.thread` from the second group's refusal: the index, the count and
the fraction are `while.body100`'s cells, unchanged by the failed read. -/
theorem fpCleanupThread112_denote_body {epow : Int → Option EPow} {env : Env} {s : State}
    {i fdig fr : BitVec 64} {v8a : Nat}
    (hpre : s.pre = some "while.body100")
    (hi : lookupName env "%add92587942" = some (.int 64 i))
    (hfd : lookupName env "%add96588941" = some (.int 64 fdig))
    (hfr : lookupName env "%add109" = some (.int 64 fr))
    (hv8 : lookupName env "%v8101" = some (.ptr v8a)) :
    denoteCode (stage2NumFastCalls epow) fpCleanupThread112Instrs (stateAt env s) =
      some (stateAt (fpCleanupThread112Env env i fdig fr) s) := by
  unfold fpCleanupThread112Instrs
  block_phi_run
  rotate_left 1
  · exact hpre
  · rfl
  · simp only [phiIncoming]; rfl
  · exact evalOperand_reg_of env s "%add92587942" _ hi
  · simp only [phiIncoming]; rfl
  · exact evalOperand_reg_of env s "%add96588941" _ hfd
  · simp only [phiIncoming]; rfl
  · exact evalOperand_reg_of env s "%add109" _ hfr
  have hv8' : lookupName
      (runCells [("%i.6586.lcssa", .int 64 i), ("%fdig.0585.lcssa", .int 64 fdig),
        ("%fr.0584.lcssa", .int 64 fr)] env) "%v8101" = some (.ptr v8a) := by
    simp only [runCells]
    rw [lookupName_cons_ne _ _ (by decide : ("%fr.0584.lcssa" : String) ≠ "%v8101"),
      lookupName_cons_ne _ _ (by decide : ("%fdig.0585.lcssa" : String) ≠ "%v8101"),
      lookupName_cons_ne _ _ (by decide : ("%i.6586.lcssa" : String) ≠ "%v8101")]
    exact hv8
  rw [denoteCode_callVoid_some (stage2NumFastCalls epow)
      (runCells [("%i.6586.lcssa", .int 64 i), ("%fdig.0585.lcssa", .int 64 fdig),
        ("%fr.0584.lcssa", .int 64 fr)] env) s
      "llvm.lifetime.end.p0"
      [((Ty.int 64), (Operand.imm (Const.int 64 0x0000000000000004#64))),
       (Ty.ptr, (Operand.reg "%v8101"))]
      [.int 64 0x0000000000000004#64, .ptr v8a]
      { ret := .int 1 0, mem := s.mem, next := s.next }
      (evalOperands_lifetimeMark (s := s) (w := 4) (ptr := "%v8101") hv8')
      (NumFastSeams.stage2NumFastCalls_lifetime_end epow
        [.int 64 0x0000000000000004#64, .ptr v8a] s.mem s.next) []]
  simp only [denoteCode_nil, stateAt, fpCleanupThread112Env, runCells]

/-- `cleanup112.thread`'s step from the first group's refusal: an unconditional
branch to `while.end115`. -/
theorem fpCleanupThread112_step {epow : Int → Option EPow} {env : Env} {s : State}
    {idx : BitVec 64} {v8a : Nat}
    (hpc : s.pc = "cleanup112.thread")
    (hpre : s.pre = some "while.body100.preheader")
    (hi : lookupName env "%inc77" = some (.int 64 idx))
    (hv8 : lookupName env "%v8101" = some (.ptr v8a)) :
    step (stage2NumFastCalls epow) numFastBody (stateAt env s) =
      .jump (stateAt (fpCleanupThread112Env env idx 0 0)
        { s with pc := "while.end115", pre := some "cleanup112.thread" }) := by
  refine numFast_step_at (s' := stateAt (fpCleanupThread112Env env idx 0 0) s)
    (b := ⟨"cleanup112.thread", fpCleanupThread112Instrs, Term.br "while.end115"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc, fpCleanupThread112Instrs] using findBlock_fpCleanupThread112
  · simpa only [denoteCode_nil] using
      fpCleanupThread112_denote_pre (epow := epow) hpre hi hv8
  · simp only [execTerm, stateAt, hpc]

/-- `cleanup112.thread`'s step from the second group: the same branch, at
`while.body100`'s cells. -/
theorem fpCleanupThread112_step_body {epow : Int → Option EPow} {env : Env} {s : State}
    {i fdig fr : BitVec 64} {v8a : Nat}
    (hpc : s.pc = "cleanup112.thread")
    (hpre : s.pre = some "while.body100")
    (hi : lookupName env "%add92587942" = some (.int 64 i))
    (hfd : lookupName env "%add96588941" = some (.int 64 fdig))
    (hfr : lookupName env "%add109" = some (.int 64 fr))
    (hv8 : lookupName env "%v8101" = some (.ptr v8a)) :
    step (stage2NumFastCalls epow) numFastBody (stateAt env s) =
      .jump (stateAt (fpCleanupThread112Env env i fdig fr)
        { s with pc := "while.end115", pre := some "cleanup112.thread" }) := by
  refine numFast_step_at (s' := stateAt (fpCleanupThread112Env env i fdig fr) s)
    (b := ⟨"cleanup112.thread", fpCleanupThread112Instrs, Term.br "while.end115"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc, fpCleanupThread112Instrs] using findBlock_fpCleanupThread112
  · simpa only [denoteCode_nil] using
      fpCleanupThread112_denote_body (epow := epow) hpre hi hfd hfr hv8
  · simp only [execTerm, stateAt, hpc]

/-! #### Reading `%p` and `%n` through the builders

The path's states stack four builders over the walk's environment, so the two
cells every block reads are twenty-nine peels from the front.  These eight
lemmas are that chain one builder at a time: each peels its own names and hands
the tail's fact back, so a composition names the cells once instead of asking a
lookup tactic to walk the whole nest. -/

theorem fpPre100Env_p {env : Env} {a : Nat} {idx : BitVec 64} {v8a : Nat}
    {call : BitVec 32} {p : Nat} (h : lookupName env "%p" = some (.ptr p)) :
    lookupName (fpPre100Env env a idx v8a call) "%p" = some (.ptr p) := by
  simp only [fpPre100Env]
  repeat rw [lookupName_cons_ne _ _ (by decide)]
  exact h

theorem fpPre100Env_n {env : Env} {a : Nat} {idx : BitVec 64} {v8a : Nat}
    {call : BitVec 32} {n : Nat}
    (h : lookupName env "%n" = some (.int 64 (BitVec.ofNat 64 n))) :
    lookupName (fpPre100Env env a idx v8a call) "%n"
      = some (.int 64 (BitVec.ofNat 64 n)) := by
  simp only [fpPre100Env]
  repeat rw [lookupName_cons_ne _ _ (by decide)]
  exact h

theorem fpBody100Env_p {env : Env} {a v8a : Nat} {idx add96 : BitVec 64}
    {call : BitVec 32} {p : Nat} (h : lookupName env "%p" = some (.ptr p)) :
    lookupName (NumFastSeams.fpBody100Env env a v8a idx add96 call) "%p"
      = some (.ptr p) := by
  simp only [NumFastSeams.fpBody100Env]
  repeat rw [lookupName_cons_ne _ _ (by decide)]
  exact h

theorem fpBody100Env_n {env : Env} {a v8a : Nat} {idx add96 : BitVec 64}
    {call : BitVec 32} {n : Nat}
    (h : lookupName env "%n" = some (.int 64 (BitVec.ofNat 64 n))) :
    lookupName (NumFastSeams.fpBody100Env env a v8a idx add96 call) "%n"
      = some (.int 64 (BitVec.ofNat 64 n)) := by
  simp only [NumFastSeams.fpBody100Env]
  repeat rw [lookupName_cons_ne _ _ (by decide)]
  exact h

theorem fpCleanup112Env_p {env : Env} {fr add92 add96 nv : BitVec 64} {w : BitVec 32}
    {p : Nat} (h : lookupName env "%p" = some (.ptr p)) :
    lookupName (NumFastSeams.fpCleanup112Env env fr add92 add96 nv w) "%p"
      = some (.ptr p) := by
  simp only [NumFastSeams.fpCleanup112Env]
  repeat rw [lookupName_cons_ne _ _ (by decide)]
  exact h

theorem fpCleanup112Env_n {env : Env} {fr add92 add96 nv : BitVec 64} {w : BitVec 32}
    {n : Nat} (h : lookupName env "%n" = some (.int 64 (BitVec.ofNat 64 n))) :
    lookupName (NumFastSeams.fpCleanup112Env env fr add92 add96 nv w) "%n"
      = some (.int 64 (BitVec.ofNat 64 n)) := by
  simp only [NumFastSeams.fpCleanup112Env]
  repeat rw [lookupName_cons_ne _ _ (by decide)]
  exact h

theorem fpCleanupThread112Env_p {env : Env} {i fdig fr : BitVec 64} {p : Nat}
    (h : lookupName env "%p" = some (.ptr p)) :
    lookupName (fpCleanupThread112Env env i fdig fr) "%p" = some (.ptr p) := by
  simp only [fpCleanupThread112Env]
  repeat rw [lookupName_cons_ne _ _ (by decide)]
  exact h

theorem fpCleanupThread112Env_n {env : Env} {i fdig fr : BitVec 64} {n : Nat}
    (h : lookupName env "%n" = some (.int 64 (BitVec.ofNat 64 n))) :
    lookupName (fpCleanupThread112Env env i fdig fr) "%n"
      = some (.int 64 (BitVec.ofNat 64 n)) := by
  simp only [fpCleanupThread112Env]
  repeat rw [lookupName_cons_ne _ _ (by decide)]
  exact h

/-- The fraction preheader's two cells are stacked in front of the merge's, so a
cell read through it is a chain of peels. -/
theorem fracPreheaderEnv_i {env : Env} {nv iv dv : BitVec 64} {i : BitVec 64}
    (h : lookupName env "%i.6552" = some (.int 64 i)) :
    lookupName (NumFastStarts.fracPreheaderEnv env nv iv dv) "%i.6552"
      = some (.int 64 i) := by
  simp only [NumFastStarts.fracPreheaderEnv]; block_lk

theorem fracPreheaderEnv_d {env : Env} {nv iv dv : BitVec 64} {d : BitVec 64}
    (h : lookupName env "%fdig.0554" = some (.int 64 d)) :
    lookupName (NumFastStarts.fracPreheaderEnv env nv iv dv) "%fdig.0554"
      = some (.int 64 d) := by
  simp only [NumFastStarts.fracPreheaderEnv]; block_lk

theorem fracPreheaderEnv_f {env : Env} {nv iv dv : BitVec 64} {f : BitVec 64}
    (h : lookupName env "%fr.0556" = some (.int 64 f)) :
    lookupName (NumFastStarts.fracPreheaderEnv env nv iv dv) "%fr.0556"
      = some (.int 64 f) := by
  simp only [NumFastStarts.fracPreheaderEnv]; block_lk

theorem fracPreheaderEnv_n {env : Env} {nv iv dv : BitVec 64}
    (h : lookupName env "%n" = some (.int 64 nv)) :
    lookupName (NumFastStarts.fracPreheaderEnv env nv iv dv) "%n"
      = some (.int 64 nv) := by
  simp only [NumFastStarts.fracPreheaderEnv]; block_lk

theorem fracPreheaderEnv_p {env : Env} {nv iv dv : BitVec 64} {p : Nat}
    (h : lookupName env "%p" = some (.ptr p)) :
    lookupName (NumFastStarts.fracPreheaderEnv env nv iv dv) "%p"
      = some (.ptr p) := by
  simp only [NumFastStarts.fracPreheaderEnv]; block_lk

/-- The fraction merge's cells, read through its builder. -/
theorem fpWhileEnd115Env_i (env : Env) (i fr fdig nv : BitVec 64) :
    lookupName (NumFastSeams.fpWhileEnd115Env env i fr fdig nv) "%i.6552"
      = some (.int 64 i) := by
  simp only [NumFastSeams.fpWhileEnd115Env]; block_lk

theorem fpWhileEnd115Env_fdig (env : Env) (i fr fdig nv : BitVec 64) :
    lookupName (NumFastSeams.fpWhileEnd115Env env i fr fdig nv) "%fdig.0554"
      = some (.int 64 fdig) := by
  simp only [NumFastSeams.fpWhileEnd115Env]; block_lk

theorem fpWhileEnd115Env_fr (env : Env) (i fr fdig nv : BitVec 64) :
    lookupName (NumFastSeams.fpWhileEnd115Env env i fr fdig nv) "%fr.0556"
      = some (.int 64 fr) := by
  simp only [NumFastSeams.fpWhileEnd115Env]; block_lk

theorem fpWhileEnd115Env_n {env : Env} {i fr fdig nv : BitVec 64}
    (h : lookupName env "%n" = some (.int 64 nv)) :
    lookupName (NumFastSeams.fpWhileEnd115Env env i fr fdig nv) "%n"
      = some (.int 64 nv) := by
  simp only [NumFastSeams.fpWhileEnd115Env]; block_lk

theorem fpWhileEnd115Env_p {env : Env} {i fr fdig nv : BitVec 64} {p : Nat}
    (h : lookupName env "%p" = some (.ptr p)) :
    lookupName (NumFastSeams.fpWhileEnd115Env env i fr fdig nv) "%p"
      = some (.ptr p) := by
  simp only [NumFastSeams.fpWhileEnd115Env]; block_lk

/-! #### The two-group stages, one builder at a time

A two-group path's state is three builders over the preheader's — the first
`cleanup112`'s fold, `while.body100`'s reader, and either the second fold or the
reader's refusal's `cleanup112.thread`.  Left inline, a cell's statement carries
the whole nest, and every proof that compares two such statements pays for the
nest again; the stages below name it one builder at a time, so each lookup peels
one builder and the cell stays a short term at every use. -/

theorem fpPre100Env_v8 {env : Env} {a : Nat} {idx : BitVec 64} {v8a : Nat}
    {call : BitVec 32} {p : Nat}
    (h : lookupName env "%v8101" = some (.ptr p)) :
    lookupName (fpPre100Env env a idx v8a call) "%v8101" = some (.ptr p) := by
  simp only [fpPre100Env]
  repeat rw [lookupName_cons_ne _ _ (by decide)]
  exact h

theorem fpPre100Env_add92582 {env : Env} {a : Nat} {idx : BitVec 64} {v8a : Nat}
    {call : BitVec 32} {x : BitVec 64}
    (h : lookupName env "%add92582" = some (.int 64 x)) :
    lookupName (fpPre100Env env a idx v8a call) "%add92582" = some (.int 64 x) := by
  simp only [fpPre100Env]
  repeat rw [lookupName_cons_ne _ _ (by decide)]
  exact h

theorem fpCleanup112Env_add92587942 (env : Env) (fr add92 add96 nv : BitVec 64)
    (w : BitVec 32) :
    lookupName (NumFastSeams.fpCleanup112Env env fr add92 add96 nv w) "%add92587942"
      = some (.int 64 add92) := by
  simp only [NumFastSeams.fpCleanup112Env]; frac_lk

theorem fpCleanup112Env_add96588941 (env : Env) (fr add92 add96 nv : BitVec 64)
    (w : BitVec 32) :
    lookupName (NumFastSeams.fpCleanup112Env env fr add92 add96 nv w) "%add96588941"
      = some (.int 64 add96) := by
  simp only [NumFastSeams.fpCleanup112Env]; frac_lk

theorem fpCleanup112Env_add92 (env : Env) (fr add92 add96 nv : BitVec 64)
    (w : BitVec 32) :
    lookupName (NumFastSeams.fpCleanup112Env env fr add92 add96 nv w) "%add92"
      = some (.int 64 (add92 + 0x8#64)) := by
  simp only [NumFastSeams.fpCleanup112Env]; frac_lk

theorem fpCleanup112Env_add109 (env : Env) (fr add92 add96 nv : BitVec 64)
    (w : BitVec 32) :
    lookupName (NumFastSeams.fpCleanup112Env env fr add92 add96 nv w) "%add109"
      = some (.int 64 (fr * (0x5f5e100#64) + BitVec.ofNat 64 w.toNat)) := by
  simp only [NumFastSeams.fpCleanup112Env]; frac_lk

theorem fpCleanup112Env_v8 {env : Env} {fr add92 add96 nv : BitVec 64} {w : BitVec 32}
    {p : Nat} (h : lookupName env "%v8101" = some (.ptr p)) :
    lookupName (NumFastSeams.fpCleanup112Env env fr add92 add96 nv w) "%v8101"
      = some (.ptr p) := by
  simp only [NumFastSeams.fpCleanup112Env]
  repeat rw [lookupName_cons_ne _ _ (by decide)]
  exact h

theorem fpBody100Env_add96 (env : Env) (a v8a : Nat) (idx add96 : BitVec 64)
    (call : BitVec 32) :
    lookupName (NumFastSeams.fpBody100Env env a v8a idx add96 call) "%add96"
      = some (.int 64 (add96 + 0x8#64)) := by
  simp only [NumFastSeams.fpBody100Env]; frac_lk

theorem fpBody100Env_add92587942 {env : Env} {a v8a : Nat} {idx add96 : BitVec 64}
    {call : BitVec 32} {x : BitVec 64}
    (h : lookupName env "%add92587942" = some (.int 64 x)) :
    lookupName (NumFastSeams.fpBody100Env env a v8a idx add96 call) "%add92587942"
      = some (.int 64 x) := by
  simp only [NumFastSeams.fpBody100Env]
  repeat rw [lookupName_cons_ne _ _ (by decide)]
  exact h

theorem fpBody100Env_add96588941 {env : Env} {a v8a : Nat} {idx add96 : BitVec 64}
    {call : BitVec 32} {x : BitVec 64}
    (h : lookupName env "%add96588941" = some (.int 64 x)) :
    lookupName (NumFastSeams.fpBody100Env env a v8a idx add96 call) "%add96588941"
      = some (.int 64 x) := by
  simp only [NumFastSeams.fpBody100Env]
  repeat rw [lookupName_cons_ne _ _ (by decide)]
  exact h

theorem fpBody100Env_add92 {env : Env} {a v8a : Nat} {idx add96 : BitVec 64}
    {call : BitVec 32} {x : BitVec 64}
    (h : lookupName env "%add92" = some (.int 64 x)) :
    lookupName (NumFastSeams.fpBody100Env env a v8a idx add96 call) "%add92"
      = some (.int 64 x) := by
  simp only [NumFastSeams.fpBody100Env]
  repeat rw [lookupName_cons_ne _ _ (by decide)]
  exact h

theorem fpBody100Env_add109 {env : Env} {a v8a : Nat} {idx add96 : BitVec 64}
    {call : BitVec 32} {x : BitVec 64}
    (h : lookupName env "%add109" = some (.int 64 x)) :
    lookupName (NumFastSeams.fpBody100Env env a v8a idx add96 call) "%add109"
      = some (.int 64 x) := by
  simp only [NumFastSeams.fpBody100Env]
  repeat rw [lookupName_cons_ne _ _ (by decide)]
  exact h

theorem fpBody100Env_v8 {env : Env} {a v8a : Nat} {idx add96 : BitVec 64}
    {call : BitVec 32} {p : Nat}
    (h : lookupName env "%v8101" = some (.ptr p)) :
    lookupName (NumFastSeams.fpBody100Env env a v8a idx add96 call) "%v8101"
      = some (.ptr p) := by
  simp only [NumFastSeams.fpBody100Env]
  repeat rw [lookupName_cons_ne _ _ (by decide)]
  exact h

theorem fpCleanupThread112Env_i (env : Env) (i fdig fr : BitVec 64) :
    lookupName (fpCleanupThread112Env env i fdig fr) "%i.6586.lcssa"
      = some (.int 64 i) := by
  simp only [fpCleanupThread112Env]; frac_lk

theorem fpCleanupThread112Env_fdig (env : Env) (i fdig fr : BitVec 64) :
    lookupName (fpCleanupThread112Env env i fdig fr) "%fdig.0585.lcssa"
      = some (.int 64 fdig) := by
  simp only [fpCleanupThread112Env]; frac_lk

theorem fpCleanupThread112Env_fr (env : Env) (i fdig fr : BitVec 64) :
    lookupName (fpCleanupThread112Env env i fdig fr) "%fr.0584.lcssa"
      = some (.int 64 fr) := by
  simp only [fpCleanupThread112Env]; frac_lk

theorem fpCleanupThread112Env_v8 {env : Env} {i fdig fr : BitVec 64} {p : Nat}
    (h : lookupName env "%v8101" = some (.ptr p)) :
    lookupName (fpCleanupThread112Env env i fdig fr) "%v8101" = some (.ptr p) := by
  simp only [fpCleanupThread112Env]
  repeat rw [lookupName_cons_ne _ _ (by decide)]
  exact h

/-- The fraction preheader's answer at the guard's taken edge: the reader's
return, its test and the pointer, over the walk's environment. -/
def fracPre100Env (env : Env) (a start v8a : Nat) : Env :=
  fpPre100Env env a (BitVec.ofNat 64 start) v8a 1

theorem fracPre100Env_p {env : Env} {a start v8a : Nat} {p : Nat}
    (h : lookupName env "%p" = some (.ptr p)) :
    lookupName (fracPre100Env env a start v8a) "%p" = some (.ptr p) := by
  simp only [fracPre100Env]; exact fpPre100Env_p h

theorem fracPre100Env_v8 {env : Env} {a start v8a : Nat} {p : Nat}
    (h : lookupName env "%v8101" = some (.ptr p)) :
    lookupName (fracPre100Env env a start v8a) "%v8101" = some (.ptr p) := by
  simp only [fracPre100Env]; exact fpPre100Env_v8 h

theorem fracPre100Env_n {env : Env} {a start v8a : Nat} {m : Nat}
    (h : lookupName env "%n" = some (.int 64 (BitVec.ofNat 64 m))) :
    lookupName (fracPre100Env env a start v8a) "%n"
      = some (.int 64 (BitVec.ofNat 64 m)) := by
  simp only [fracPre100Env]; exact fpPre100Env_n h

theorem fracPre100Env_add92582 {env : Env} {a start v8a : Nat}
    (h : lookupName env "%add92582"
      = some (.int 64 (BitVec.ofNat 64 (start + 8)))) :
    lookupName (fracPre100Env env a start v8a) "%add92582"
      = some (.int 64 (BitVec.ofNat 64 (start + 8))) := by
  simp only [fracPre100Env]; exact fpPre100Env_add92582 h

/-- The first group's fold: `cleanup112`'s cells over the preheader's answer. -/
def fracFold1Env (env : Env) (a v8a start n w : Nat) : Env :=
  NumFastSeams.fpCleanup112Env (fracPre100Env env a start v8a) 0
    (BitVec.ofNat 64 (start + 8)) 0x8#64 (BitVec.ofNat 64 n) (BitVec.ofNat 32 w)

theorem fracFold1Env_p {env : Env} {a v8a start n w : Nat} {p : Nat}
    (h : lookupName env "%p" = some (.ptr p)) :
    lookupName (fracFold1Env env a v8a start n w) "%p" = some (.ptr p) := by
  simp only [fracFold1Env]; exact fpCleanup112Env_p (fracPre100Env_p h)

theorem fracFold1Env_n {env : Env} {a v8a start n w : Nat} {m : Nat}
    (h : lookupName env "%n" = some (.int 64 (BitVec.ofNat 64 m))) :
    lookupName (fracFold1Env env a v8a start n w) "%n"
      = some (.int 64 (BitVec.ofNat 64 m)) := by
  simp only [fracFold1Env]; exact fpCleanup112Env_n (fracPre100Env_n h)

theorem fracFold1Env_v8 {env : Env} {a v8a start n w : Nat} {p : Nat}
    (h : lookupName env "%v8101" = some (.ptr p)) :
    lookupName (fracFold1Env env a v8a start n w) "%v8101" = some (.ptr p) := by
  simp only [fracFold1Env]; exact fpCleanup112Env_v8 h

theorem fracFold1Env_add92587942 (env : Env) (a v8a start n w : Nat) :
    lookupName (fracFold1Env env a v8a start n w) "%add92587942"
      = some (.int 64 (BitVec.ofNat 64 (start + 8))) := by
  simp only [fracFold1Env]; exact fpCleanup112Env_add92587942 ..

theorem fracFold1Env_add96588941 (env : Env) (a v8a start n w : Nat) :
    lookupName (fracFold1Env env a v8a start n w) "%add96588941"
      = some (.int 64 0x8#64) := by
  simp only [fracFold1Env]; exact fpCleanup112Env_add96588941 ..

theorem fracFold1Env_add92 (env : Env) (a v8a start n w : Nat) :
    lookupName (fracFold1Env env a v8a start n w) "%add92"
      = some (.int 64 (BitVec.ofNat 64 (start + 8) + 0x8#64)) := by
  simp only [fracFold1Env]; exact fpCleanup112Env_add92 ..

theorem fracFold1Env_add109 (env : Env) (a v8a start n w : Nat) :
    lookupName (fracFold1Env env a v8a start n w) "%add109"
      = some (.int 64 ((0 : BitVec 64) * (0x5f5e100#64)
          + BitVec.ofNat 64 (BitVec.ofNat 32 w).toNat)) := by
  simp only [fracFold1Env]; exact fpCleanup112Env_add109 ..

/-- `while.body100` at a successful reader: its cells over the first fold. -/
def fracBody2Env (env : Env) (a v8a start n w : Nat) : Env :=
  NumFastSeams.fpBody100Env (fracFold1Env env a v8a start n w) a v8a
    (BitVec.ofNat 64 (start + 8)) 0x8#64 1

theorem fracBody2Env_p {env : Env} {a v8a start n w : Nat} {p : Nat}
    (h : lookupName env "%p" = some (.ptr p)) :
    lookupName (fracBody2Env env a v8a start n w) "%p" = some (.ptr p) := by
  simp only [fracBody2Env]; exact fpBody100Env_p (fracFold1Env_p h)

theorem fracBody2Env_n {env : Env} {a v8a start n w : Nat} {m : Nat}
    (h : lookupName env "%n" = some (.int 64 (BitVec.ofNat 64 m))) :
    lookupName (fracBody2Env env a v8a start n w) "%n"
      = some (.int 64 (BitVec.ofNat 64 m)) := by
  simp only [fracBody2Env]; exact fpBody100Env_n (fracFold1Env_n h)

theorem fracBody2Env_v8 {env : Env} {a v8a start n w : Nat} {p : Nat}
    (h : lookupName env "%v8101" = some (.ptr p)) :
    lookupName (fracBody2Env env a v8a start n w) "%v8101" = some (.ptr p) := by
  simp only [fracBody2Env]; exact fpBody100Env_v8 (fracFold1Env_v8 h)

theorem fracBody2Env_add109 (env : Env) (a v8a start n w : Nat) :
    lookupName (fracBody2Env env a v8a start n w) "%add109"
      = some (.int 64 ((0 : BitVec 64) * (0x5f5e100#64)
          + BitVec.ofNat 64 (BitVec.ofNat 32 w).toNat)) := by
  simp only [fracBody2Env]; exact fpBody100Env_add109 (fracFold1Env_add109 ..)

theorem fracBody2Env_add92 (env : Env) (a v8a start n w : Nat) :
    lookupName (fracBody2Env env a v8a start n w) "%add92"
      = some (.int 64 (BitVec.ofNat 64 (start + 8) + 0x8#64)) := by
  simp only [fracBody2Env]; exact fpBody100Env_add92 (fracFold1Env_add92 ..)

theorem fracBody2Env_add96 (env : Env) (a v8a start n w : Nat) :
    lookupName (fracBody2Env env a v8a start n w) "%add96"
      = some (.int 64 (0x8#64 + 0x8#64)) := by
  simp only [fracBody2Env]; exact fpBody100Env_add96 ..

/-- `while.body100` at a refused reader: the same cells, the answer zero. -/
def fracBody2EnvR (env : Env) (a v8a start n w : Nat) : Env :=
  NumFastSeams.fpBody100Env (fracFold1Env env a v8a start n w) a v8a
    (BitVec.ofNat 64 (start + 8)) 0x8#64 0

theorem fracBody2EnvR_p {env : Env} {a v8a start n w : Nat} {p : Nat}
    (h : lookupName env "%p" = some (.ptr p)) :
    lookupName (fracBody2EnvR env a v8a start n w) "%p" = some (.ptr p) := by
  simp only [fracBody2EnvR]; exact fpBody100Env_p (fracFold1Env_p h)

theorem fracBody2EnvR_n {env : Env} {a v8a start n w : Nat} {m : Nat}
    (h : lookupName env "%n" = some (.int 64 (BitVec.ofNat 64 m))) :
    lookupName (fracBody2EnvR env a v8a start n w) "%n"
      = some (.int 64 (BitVec.ofNat 64 m)) := by
  simp only [fracBody2EnvR]; exact fpBody100Env_n (fracFold1Env_n h)

theorem fracBody2EnvR_v8 {env : Env} {a v8a start n w : Nat} {p : Nat}
    (h : lookupName env "%v8101" = some (.ptr p)) :
    lookupName (fracBody2EnvR env a v8a start n w) "%v8101" = some (.ptr p) := by
  simp only [fracBody2EnvR]; exact fpBody100Env_v8 (fracFold1Env_v8 h)

theorem fracBody2EnvR_add92587942 (env : Env) (a v8a start n w : Nat) :
    lookupName (fracBody2EnvR env a v8a start n w) "%add92587942"
      = some (.int 64 (BitVec.ofNat 64 (start + 8))) := by
  simp only [fracBody2EnvR]
  exact fpBody100Env_add92587942 (fracFold1Env_add92587942 ..)

theorem fracBody2EnvR_add96588941 (env : Env) (a v8a start n w : Nat) :
    lookupName (fracBody2EnvR env a v8a start n w) "%add96588941"
      = some (.int 64 0x8#64) := by
  simp only [fracBody2EnvR]
  exact fpBody100Env_add96588941 (fracFold1Env_add96588941 ..)

theorem fracBody2EnvR_add109 (env : Env) (a v8a start n w : Nat) :
    lookupName (fracBody2EnvR env a v8a start n w) "%add109"
      = some (.int 64 ((0 : BitVec 64) * (0x5f5e100#64)
          + BitVec.ofNat 64 (BitVec.ofNat 32 w).toNat)) := by
  simp only [fracBody2EnvR]; exact fpBody100Env_add109 (fracFold1Env_add109 ..)

/-- The second fold: `cleanup112`'s cells over the second reader's. -/
def fracFold2Env (env : Env) (a v8a start n w w2 : Nat) : Env :=
  NumFastSeams.fpCleanup112Env (fracBody2Env env a v8a start n w)
    (BitVec.ofNat 64 w) (BitVec.ofNat 64 (start + 16)) 0x10#64
    (BitVec.ofNat 64 n) (BitVec.ofNat 32 w2)

theorem fracFold2Env_p {env : Env} {a v8a start n w w2 : Nat} {p : Nat}
    (h : lookupName env "%p" = some (.ptr p)) :
    lookupName (fracFold2Env env a v8a start n w w2) "%p" = some (.ptr p) := by
  simp only [fracFold2Env]; exact fpCleanup112Env_p (fracBody2Env_p h)

theorem fracFold2Env_n {env : Env} {a v8a start n w w2 : Nat} {m : Nat}
    (h : lookupName env "%n" = some (.int 64 (BitVec.ofNat 64 m))) :
    lookupName (fracFold2Env env a v8a start n w w2) "%n"
      = some (.int 64 (BitVec.ofNat 64 m)) := by
  simp only [fracFold2Env]; exact fpCleanup112Env_n (fracBody2Env_n h)

theorem fracFold2Env_add109 (env : Env) (a v8a start n w w2 : Nat) :
    lookupName (fracFold2Env env a v8a start n w w2) "%add109"
      = some (.int 64 (BitVec.ofNat 64 w * (0x5f5e100#64)
          + BitVec.ofNat 64 (BitVec.ofNat 32 w2).toNat)) := by
  simp only [fracFold2Env]; exact fpCleanup112Env_add109 ..

theorem fracFold2Env_add96588941 (env : Env) (a v8a start n w w2 : Nat) :
    lookupName (fracFold2Env env a v8a start n w w2) "%add96588941"
      = some (.int 64 0x10#64) := by
  simp only [fracFold2Env]; exact fpCleanup112Env_add96588941 ..

theorem fracFold2Env_add92587942 (env : Env) (a v8a start n w w2 : Nat) :
    lookupName (fracFold2Env env a v8a start n w w2) "%add92587942"
      = some (.int 64 (BitVec.ofNat 64 (start + 16))) := by
  simp only [fracFold2Env]; exact fpCleanup112Env_add92587942 ..

/-- The second read's refusal: `cleanup112.thread`'s cells over the refused
reader. -/
def fracThread2Env (env : Env) (a v8a start n w : Nat) : Env :=
  fpCleanupThread112Env (fracBody2EnvR env a v8a start n w)
    (BitVec.ofNat 64 (start + 8)) 0x8#64 (BitVec.ofNat 64 w)

theorem fracThread2Env_p {env : Env} {a v8a start n w : Nat} {p : Nat}
    (h : lookupName env "%p" = some (.ptr p)) :
    lookupName (fracThread2Env env a v8a start n w) "%p" = some (.ptr p) := by
  simp only [fracThread2Env]; exact fpCleanupThread112Env_p (fracBody2EnvR_p h)

theorem fracThread2Env_n {env : Env} {a v8a start n w : Nat} {m : Nat}
    (h : lookupName env "%n" = some (.int 64 (BitVec.ofNat 64 m))) :
    lookupName (fracThread2Env env a v8a start n w) "%n"
      = some (.int 64 (BitVec.ofNat 64 m)) := by
  simp only [fracThread2Env]; exact fpCleanupThread112Env_n (fracBody2EnvR_n h)

theorem fracThread2Env_i (env : Env) (a v8a start n w : Nat) :
    lookupName (fracThread2Env env a v8a start n w) "%i.6586.lcssa"
      = some (.int 64 (BitVec.ofNat 64 (start + 8))) := by
  simp only [fracThread2Env]; exact fpCleanupThread112Env_i ..

theorem fracThread2Env_fdig (env : Env) (a v8a start n w : Nat) :
    lookupName (fracThread2Env env a v8a start n w) "%fdig.0585.lcssa"
      = some (.int 64 0x8#64) := by
  simp only [fracThread2Env]; exact fpCleanupThread112Env_fdig ..

theorem fracThread2Env_fr (env : Env) (a v8a start n w : Nat) :
    lookupName (fracThread2Env env a v8a start n w) "%fr.0584.lcssa"
      = some (.int 64 (BitVec.ofNat 64 w)) := by
  simp only [fracThread2Env]; exact fpCleanupThread112Env_fr ..

/-- **`while.end115` to the fraction head.**  From the merge with the three cells
read as the run's start — the index `i0`, the count `d0` and the fraction the
digits' fold from `i0 - d0` — two control steps reach `land.lhs.true119` at
`fracRunInv` with the budget `n - i0`. -/
theorem fpWhileEnd115_entry {epow : Int → Option EPow} {env : Env} {s : State}
    {i fr fdig : BitVec 64} {mem : Mem} {p n i0 d0 : Nat} {bs : List UInt8}
    (hpc : s.pc = "while.end115")
    (hden : denoteCode (stage2NumFastCalls epow) NumFastSeams.fpWhileEnd115Instrs
      (stateAt env s) = some (stateAt (NumFastSeams.fpWhileEnd115Env env i fr fdig
        (BitVec.ofNat 64 n)) s))
    (hbit : evalICmp .ult i (BitVec.ofNat 64 n) = 1)
    (hmem : s.mem = mem)
    (hp : lookupName (NumFastSeams.fpWhileEnd115Env env i fr fdig (BitVec.ofNat 64 n)) "%p"
      = some (.ptr p))
    (hn : lookupName (NumFastSeams.fpWhileEnd115Env env i fr fdig (BitVec.ofNat 64 n)) "%n"
      = some (.int 64 (BitVec.ofNat 64 n)))
    (hread : readBytes mem p n = some bs)
    (hparts : fracPartCells env)
    (hi : i = BitVec.ofNat 64 i0) (hfd : fdig = BitVec.ofNat 64 d0)
    (hfr : fr = BitVec.ofNat 64 (digitFold bs (i0 - d0) (min d0 19)))
    (hltn : i0 < n) (hnlt : n < 2 ^ 63) (hd0 : d0 ≤ i0) :
    ∃ e : State, fracRunInv mem p n i0 d0 bs (n - i0) e 0 ∧
      ∀ k, runFuel (stage2NumFastCalls epow) (2 + k) numFastBody (stateAt env s)
        = runFuel (stage2NumFastCalls epow) k numFastBody e := by
  have hstep1 : step (stage2NumFastCalls epow) numFastBody (stateAt env s) =
      .jump (stateAt (NumFastSeams.fpWhileEnd115Env env i fr fdig (BitVec.ofNat 64 n))
        { s with pc := "land.lhs.true119.preheader", pre := some "while.end115" }) :=
    NumFastSeams.fpWhileEnd115_step_head (epow := epow) (i := i) (fr := fr)
      (fdig := fdig) (nv := BitVec.ofNat 64 n) hpc hden hbit
  have hfr' : lookupName (NumFastSeams.fpWhileEnd115Env env i fr fdig
      (BitVec.ofNat 64 n)) "%fr.0556" = some (.int 64 fr) :=
    fpWhileEnd115Env_fr env i fr fdig (BitVec.ofNat 64 n)
  have hfd' : lookupName (NumFastSeams.fpWhileEnd115Env env i fr fdig
      (BitVec.ofNat 64 n)) "%fdig.0554" = some (.int 64 fdig) :=
    fpWhileEnd115Env_fdig env i fr fdig (BitVec.ofNat 64 n)
  have hi' : lookupName (NumFastSeams.fpWhileEnd115Env env i fr fdig
      (BitVec.ofNat 64 n)) "%i.6552" = some (.int 64 i) :=
    fpWhileEnd115Env_i env i fr fdig (BitVec.ofNat 64 n)
  have hstep2 : step (stage2NumFastCalls epow) numFastBody
      (stateAt (NumFastSeams.fpWhileEnd115Env env i fr fdig (BitVec.ofNat 64 n))
        { s with pc := "land.lhs.true119.preheader", pre := some "while.end115" }) =
      .jump (stateAt (NumFastStarts.fracPreheaderEnv
          (NumFastSeams.fpWhileEnd115Env env i fr fdig (BitVec.ofNat 64 n))
          (BitVec.ofNat 64 n) i fdig)
        { s with pc := "land.lhs.true119", pre := some "land.lhs.true119.preheader" }) :=
    NumFastStarts.fracPreheader_step (calls := stage2NumFastCalls epow)
      (nv := BitVec.ofNat 64 n) (iv := i) (dv := fdig) rfl hfd' hi' hn
  have hi'' : lookupName (NumFastSeams.fpWhileEnd115Env env i fr fdig
      (BitVec.ofNat 64 n)) "%i.6552" = some (.int 64 (BitVec.ofNat 64 i0)) := by
    rw [fpWhileEnd115Env_i, hi]
  have hfd'' : lookupName (NumFastSeams.fpWhileEnd115Env env i fr fdig
      (BitVec.ofNat 64 n)) "%fdig.0554" = some (.int 64 (BitVec.ofNat 64 d0)) := by
    rw [fpWhileEnd115Env_fdig, hfd]
  have hfr'' : lookupName (NumFastSeams.fpWhileEnd115Env env i fr fdig
      (BitVec.ofNat 64 n)) "%fr.0556"
      = some (.int 64 (BitVec.ofNat 64 (digitFold bs (i0 - d0) (min d0 19)))) := by
    rw [fpWhileEnd115Env_fr, hfr]
  refine ⟨stateAt (NumFastStarts.fracPreheaderEnv
      (NumFastSeams.fpWhileEnd115Env env i fr fdig (BitVec.ofNat 64 n))
      (BitVec.ofNat 64 n) i fdig)
      { s with pc := "land.lhs.true119", pre := some "land.lhs.true119.preheader" },
    ?_, ?_⟩
  · refine NumFastStarts.fracRunInv_entry (mem := mem) (p := p) (n := n)
      (i0 := i0) (d0 := d0) (bs := bs) rfl rfl ?_ hltn hnlt hd0 ?_ ?_ hread ?_ ?_ ?_ ?_ ?_
    · simpa only [stateAt] using hmem
    · simpa only [stateAt] using fracPreheaderEnv_p hp
    · simpa only [stateAt] using fracPreheaderEnv_n hn
    · rw [← hi, ← hfd]
      simp only [stateAt, NumFastStarts.fracPreheaderEnv]
      block_lk
    · obtain ⟨idigv, ipv, hidigv, hipv⟩ := hparts
      refine ⟨idigv, ipv, ?_, ?_⟩
      · simp only [stateAt, NumFastStarts.fracPreheaderEnv,
          NumFastSeams.fpWhileEnd115Env]
        block_lk
      · simp only [stateAt, NumFastStarts.fracPreheaderEnv,
          NumFastSeams.fpWhileEnd115Env]
        block_lk
    · simpa only [stateAt] using fracPreheaderEnv_i hi''
    · simpa only [stateAt] using fracPreheaderEnv_d hfd''
    · simpa only [stateAt] using fracPreheaderEnv_f hfr''
  · intro k
    rw [show 2 + k = 1 + (1 + k) from by omega,
      runFuel_jump_prefix hstep1, runFuel_jump_prefix hstep2]

/-! ### The fraction's four paths

Each path fixes the state at `while.body100.preheader` (the taken guard's edge)
and composes its blocks with `fpWhileEnd115_entry`.  The entry hypotheses are
the cells the guard left: the pointer, the reader's local, the index after the
`.`, the guard's own sum and the length.  The reader's bytes are the walk's, at
the offsets the call computes, and the local's separation is the staging's. -/

/-- **The first read refuses.**  The preheader's zero answer leaves for
`cleanup112.thread`, whose three `phi`s carry the preheader's own cells — the
index after the `.`, the count zero and the fraction zero — and `while.end115`
merges them.  Four steps reach the head at `i0 = start`, `d0 = 0`. -/
theorem fracTaken_refuse1 {epow : Int → Option EPow} {env : Env} {s : State}
    {a v8a start n : Nat} {bs bs8 : List UInt8}
    (hpc : s.pc = "while.body100.preheader")
    (hparts : fracPartCells env)
    (hpre : s.pre = some "while.cond91.preheader")
    (hp : lookupName env "%p" = some (.ptr a))
    (hv8 : lookupName env "%v8101" = some (.ptr v8a))
    (hinc : lookupName env "%inc77" = some (.int 64 (BitVec.ofNat 64 start)))
    (h563 : lookupName env "%add92582" = some (.int 64 (BitVec.ofNat 64 (start + 8))))
    (hn : lookupName env "%n" = some (.int 64 (BitVec.ofNat 64 n)))
    (hread : readBytes s.mem a n = some bs)
    (hslice : readBytes s.mem (a + start) 8 = some bs8)
    (hstart : start + 8 ≤ n) (hnlt : n < 2 ^ 63)
    (hval : d8Value bs8 = none) :
    ∃ e : State, fracRunInv s.mem a n start 0 bs (n - start) e 0 ∧
      ∀ k, runFuel (stage2NumFastCalls epow) (4 + k) numFastBody (stateAt env s)
        = runFuel (stage2NumFastCalls epow) k numFastBody e := by
  have hpos : ((BitVec.ofNat 64 start).signExtend 64).toNat < 2 ^ 63 := by
    rw [ofNat64_signExtend_toNat (by omega)]; omega
  have hslice' : readBytes s.mem
      (a + ((BitVec.ofNat 64 start).signExtend 64).toNat) 8 = some bs8 := by
    rw [ofNat64_signExtend_toNat (by omega)]; exact hslice
  let st1 : State := { s with pc := "cleanup112.thread", pre := some "while.body100.preheader" }
  have hstep1 : step (stage2NumFastCalls epow) numFastBody (stateAt env s) =
      .jump (stateAt (fpPre100Env env a (BitVec.ofNat 64 start) v8a 0) st1) :=
    fpPre100_step_refuse (epow := epow) hpc hp hinc hv8 hpos hslice' hval
  have hinc1 : lookupName (fpPre100Env env a (BitVec.ofNat 64 start) v8a 0) "%inc77"
      = some (.int 64 (BitVec.ofNat 64 start)) := by
    simp only [fpPre100Env]; block_lk
  have hv81 : lookupName (fpPre100Env env a (BitVec.ofNat 64 start) v8a 0) "%v8101"
      = some (.ptr v8a) := by
    simp only [fpPre100Env]; block_lk
  let st2 : State := { st1 with pc := "while.end115", pre := some "cleanup112.thread" }
  have hstep2 : step (stage2NumFastCalls epow) numFastBody
      (stateAt (fpPre100Env env a (BitVec.ofNat 64 start) v8a 0) st1) =
      .jump (stateAt (fpCleanupThread112Env
          (fpPre100Env env a (BitVec.ofNat 64 start) v8a 0)
          (BitVec.ofNat 64 start) 0 0) st2) :=
    fpCleanupThread112_step (epow := epow) rfl rfl hinc1 hv81
  have hi2 : lookupName (fpCleanupThread112Env
      (fpPre100Env env a (BitVec.ofNat 64 start) v8a 0)
      (BitVec.ofNat 64 start) 0 0) "%i.6586.lcssa"
      = some (.int 64 (BitVec.ofNat 64 start)) := by
    simp only [fpCleanupThread112Env]; frac_lk
  have hfd2 : lookupName (fpCleanupThread112Env
      (fpPre100Env env a (BitVec.ofNat 64 start) v8a 0)
      (BitVec.ofNat 64 start) 0 0) "%fdig.0585.lcssa" = some (.int 64 0) := by
    simp only [fpCleanupThread112Env]; frac_lk
  have hfr2 : lookupName (fpCleanupThread112Env
      (fpPre100Env env a (BitVec.ofNat 64 start) v8a 0)
      (BitVec.ofNat 64 start) 0 0) "%fr.0584.lcssa" = some (.int 64 0) := by
    simp only [fpCleanupThread112Env]; frac_lk
  have hn2 : lookupName (fpCleanupThread112Env
      (fpPre100Env env a (BitVec.ofNat 64 start) v8a 0)
      (BitVec.ofNat 64 start) 0 0) "%n"
      = some (.int 64 (BitVec.ofNat 64 n)) := by
    simp only [fpCleanupThread112Env, fpPre100Env]; block_lk
  have hden : denoteCode (stage2NumFastCalls epow) NumFastSeams.fpWhileEnd115Instrs
      (stateAt (fpCleanupThread112Env
        (fpPre100Env env a (BitVec.ofNat 64 start) v8a 0)
        (BitVec.ofNat 64 start) 0 0) st2) =
      some (stateAt (NumFastSeams.fpWhileEnd115Env
        (fpCleanupThread112Env
          (fpPre100Env env a (BitVec.ofNat 64 start) v8a 0)
          (BitVec.ofNat 64 start) 0 0)
        (BitVec.ofNat 64 start) 0 0 (BitVec.ofNat 64 n)) st2) :=
    NumFastSeams.fpWhileEnd115_denote_thread (epow := epow) rfl hfr2 hfd2 hi2 hn2
  have hbit : evalICmp .ult (BitVec.ofNat 64 start) (BitVec.ofNat 64 n) = 1 :=
    NumFastSeams.ult_ofNat_one (by omega) (by omega)
  have hp' : lookupName (NumFastSeams.fpWhileEnd115Env
      (fpCleanupThread112Env
        (fpPre100Env env a (BitVec.ofNat 64 start) v8a 0)
        (BitVec.ofNat 64 start) 0 0)
      (BitVec.ofNat 64 start) 0 0 (BitVec.ofNat 64 n)) "%p" = some (.ptr a) :=
    fpWhileEnd115Env_p (by
      simp only [fpCleanupThread112Env, fpPre100Env]; block_lk)
  have hn' : lookupName (NumFastSeams.fpWhileEnd115Env
      (fpCleanupThread112Env
        (fpPre100Env env a (BitVec.ofNat 64 start) v8a 0)
        (BitVec.ofNat 64 start) 0 0)
      (BitVec.ofNat 64 start) 0 0 (BitVec.ofNat 64 n)) "%n"
      = some (.int 64 (BitVec.ofNat 64 n)) :=
    fpWhileEnd115Env_n hn2
  obtain ⟨e, hinv, hcont⟩ := fpWhileEnd115_entry (epow := epow)
    (env := fpCleanupThread112Env
      (fpPre100Env env a (BitVec.ofNat 64 start) v8a 0)
      (BitVec.ofNat 64 start) 0 0)
    (s := st2)
    (i := BitVec.ofNat 64 start) (fr := 0) (fdig := 0)
    (mem := s.mem) (p := a) (n := n) (i0 := start) (d0 := 0) (bs := bs)
    rfl hden hbit rfl hp' hn' hread
    (by obtain ⟨idigv, ipv, hidigv, hipv⟩ := hparts
        exact ⟨idigv, ipv, by
          simp only [fpCleanupThread112Env, fpPre100Env]; block_lk, by
          simp only [fpCleanupThread112Env, fpPre100Env]; block_lk⟩)
    rfl rfl
    (by rw [Nat.sub_zero, show min 0 19 = 0 from by decide, digitFold_zero]; rfl)
    (by omega) hnlt (by omega)
  refine ⟨e, hinv, ?_⟩
  intro k
  rw [show 4 + k = 1 + (1 + (2 + k)) from by omega,
    runFuel_jump_prefix hstep1, runFuel_jump_prefix hstep2, hcont k]

/-- The first group's fold at the fraction's zero: the reader's eight bytes are
the digits from `start`, and `0 * 10 ^ 8 + w` is their fold. -/
theorem fracFirstFold {bs bs8 : List UInt8} {m : Mem} {a start n w : Nat}
    (hread : readBytes m a n = some bs)
    (hslice : readBytes m (a + start) 8 = some bs8)
    (hstart : start + 8 ≤ n) (hval : d8Value bs8 = some w) :
    (0 : BitVec 64) * (0x5f5e100#64) + BitVec.ofNat 64 w
      = BitVec.ofNat 64 (digitFold bs start 8) := by
  have hw : w = digitFold bs start 8 := NumFastSeams.d8Value_slice hread hslice hstart hval
  rw [hw]; simp

/-- **The first read succeeds and the loop refuses.**  `cleanup112` folds the
group — `0 * 10 ^ 8 + %14` — and tests the advanced index and the count; a
refused conjunction leaves for `while.end115` with the count eight and the index
after the group.  Four steps reach the head at `i0 = start + 8`, `d0 = 8`. -/
theorem fracTaken_exit {epow : Int → Option EPow} {env : Env} {s : State}
    {a v8a start n w : Nat} {bs bs8 : List UInt8}
    (hpc : s.pc = "while.body100.preheader")
    (hparts : fracPartCells env)
    (hpre : s.pre = some "while.cond91.preheader")
    (hp : lookupName env "%p" = some (.ptr a))
    (hv8 : lookupName env "%v8101" = some (.ptr v8a))
    (hinc : lookupName env "%inc77" = some (.int 64 (BitVec.ofNat 64 start)))
    (h563 : lookupName env "%add92582" = some (.int 64 (BitVec.ofNat 64 (start + 8))))
    (hn : lookupName env "%n" = some (.int 64 (BitVec.ofNat 64 n)))
    (hread : readBytes s.mem a n = some bs)
    (hslice : readBytes s.mem (a + start) 8 = some bs8)
    (hstart : start + 8 ≤ n) (hnlt : n < 2 ^ 63)
    (hval : d8Value bs8 = some w) (hw : w < 2 ^ 32)
    (hsep : v8a + 4 ≤ a ∨ a + n ≤ v8a)
    (hguard : NumFastSeams.fpGuard
      (BitVec.ofNat 64 (start + 8) + 0x8#64) 0x8#64 (BitVec.ofNat 64 n) = 0)
    (hmore : start + 8 < n) :
    ∃ e : State, fracRunInv (writeBytes s.mem v8a (natToBytes w 4)) a n (start + 8) 8 bs
      (n - (start + 8)) e 0 ∧
      ∀ k, runFuel (stage2NumFastCalls epow) (4 + k) numFastBody (stateAt env s)
        = runFuel (stage2NumFastCalls epow) k numFastBody e := by
  have hpos : ((BitVec.ofNat 64 start).signExtend 64).toNat < 2 ^ 63 := by
    rw [ofNat64_signExtend_toNat (by omega)]; omega
  have hslice' : readBytes s.mem
      (a + ((BitVec.ofNat 64 start).signExtend 64).toNat) 8 = some bs8 := by
    rw [ofNat64_signExtend_toNat (by omega)]; exact hslice
  let st1 : State := { s with mem := writeBytes s.mem v8a (natToBytes w 4),
                               next := s.next, pc := "cleanup112",
                               pre := some "while.body100.preheader" }
  have hstep1 : step (stage2NumFastCalls epow) numFastBody (stateAt env s) =
      .jump (stateAt (fpPre100Env env a (BitVec.ofNat 64 start) v8a 1) st1) :=
    fpPre100_step_ok (epow := epow) hpc hp hinc hv8 hpos hslice' hval hw
  have hback : readBytes (writeBytes s.mem v8a (natToBytes w 4)) v8a 4
      = some (natToBytes w 4) :=
    (NumFastSeams.numD8Answer_writes (p := a + start) (v := v8a) (w := w)
      (bs := bs8) (mem := s.mem) (next := s.next) hslice hval hw).2.1
  have hread1 : readBytes (writeBytes s.mem v8a (natToBytes w 4)) v8a 4
      = some (natToBytes (BitVec.ofNat 32 w).toNat 4) := by
    rw [ofNat32_toNat hw]; exact hback
  have h563_1 : lookupName (fpPre100Env env a (BitVec.ofNat 64 start) v8a 1) "%add92582"
      = some (.int 64 (BitVec.ofNat 64 (start + 8))) := by
    simp only [fpPre100Env]; block_lk
  have hv8_1 : lookupName (fpPre100Env env a (BitVec.ofNat 64 start) v8a 1) "%v8101"
      = some (.ptr v8a) := by
    simp only [fpPre100Env]; block_lk
  have hn1 : lookupName (fpPre100Env env a (BitVec.ofNat 64 start) v8a 1) "%n"
      = some (.int 64 (BitVec.ofNat 64 n)) := by
    simp only [fpPre100Env]; block_lk
  have hden1 : denoteCode (stage2NumFastCalls epow) NumFastSeams.fpCleanup112Instrs
      (stateAt (fpPre100Env env a (BitVec.ofNat 64 start) v8a 1) st1) =
      some (stateAt (NumFastSeams.fpCleanup112Env
        (fpPre100Env env a (BitVec.ofNat 64 start) v8a 1)
        0 (BitVec.ofNat 64 (start + 8)) 0x8#64
        (BitVec.ofNat 64 n) (BitVec.ofNat 32 w)) st1) :=
    NumFastSeams.fpCleanup112_denote_pre (epow := epow) (fr := 0) rfl h563_1 hv8_1 hread1 hn1
  let st2 : State := { st1 with pc := "while.end115", pre := some "cleanup112" }
  have hstep2 : step (stage2NumFastCalls epow) numFastBody
      (stateAt (fpPre100Env env a (BitVec.ofNat 64 start) v8a 1) st1) =
      .jump (stateAt (NumFastSeams.fpCleanup112Env
        (fpPre100Env env a (BitVec.ofNat 64 start) v8a 1)
        0 (BitVec.ofNat 64 (start + 8)) 0x8#64
        (BitVec.ofNat 64 n) (BitVec.ofNat 32 w)) st2) :=
    NumFastSeams.fpCleanup112_step_end (epow := epow) rfl hden1 hguard
  have hfold : (0 : BitVec 64) * (0x5f5e100#64) + BitVec.ofNat 64 w
      = BitVec.ofNat 64 (digitFold bs start 8) :=
    fracFirstFold hread hslice hstart hval
  have hip2 : lookupName (NumFastSeams.fpCleanup112Env
      (fpPre100Env env a (BitVec.ofNat 64 start) v8a 1)
      0 (BitVec.ofNat 64 (start + 8)) 0x8#64
      (BitVec.ofNat 64 n) (BitVec.ofNat 32 w)) "%add109"
      = some (.int 64 (BitVec.ofNat 64 (digitFold bs start 8))) := by
    have hcell : lookupName (NumFastSeams.fpCleanup112Env
        (fpPre100Env env a (BitVec.ofNat 64 start) v8a 1)
        0 (BitVec.ofNat 64 (start + 8)) 0x8#64
        (BitVec.ofNat 64 n) (BitVec.ofNat 32 w)) "%add109"
        = some (.int 64 (0 * (0x5f5e100#64)
            + BitVec.ofNat 64 (BitVec.ofNat 32 w).toNat)) := by
      simp only [NumFastSeams.fpCleanup112Env]; frac_lk
    rw [hcell, ofNat32_toNat hw, hfold]
  have hfd2 : lookupName (NumFastSeams.fpCleanup112Env
      (fpPre100Env env a (BitVec.ofNat 64 start) v8a 1)
      0 (BitVec.ofNat 64 (start + 8)) 0x8#64
      (BitVec.ofNat 64 n) (BitVec.ofNat 32 w)) "%add96588941"
      = some (.int 64 0x8#64) := by
    simp only [NumFastSeams.fpCleanup112Env]; frac_lk
  have hi2 : lookupName (NumFastSeams.fpCleanup112Env
      (fpPre100Env env a (BitVec.ofNat 64 start) v8a 1)
      0 (BitVec.ofNat 64 (start + 8)) 0x8#64
      (BitVec.ofNat 64 n) (BitVec.ofNat 32 w)) "%add92587942"
      = some (.int 64 (BitVec.ofNat 64 (start + 8))) := by
    simp only [NumFastSeams.fpCleanup112Env]; frac_lk
  have hn2 : lookupName (NumFastSeams.fpCleanup112Env
      (fpPre100Env env a (BitVec.ofNat 64 start) v8a 1)
      0 (BitVec.ofNat 64 (start + 8)) 0x8#64
      (BitVec.ofNat 64 n) (BitVec.ofNat 32 w)) "%n"
      = some (.int 64 (BitVec.ofNat 64 n)) := by
    simp only [NumFastSeams.fpCleanup112Env, fpPre100Env]; block_lk
  have hden : denoteCode (stage2NumFastCalls epow) NumFastSeams.fpWhileEnd115Instrs
      (stateAt (NumFastSeams.fpCleanup112Env
        (fpPre100Env env a (BitVec.ofNat 64 start) v8a 1)
        0 (BitVec.ofNat 64 (start + 8)) 0x8#64
        (BitVec.ofNat 64 n) (BitVec.ofNat 32 w)) st2) =
      some (stateAt (NumFastSeams.fpWhileEnd115Env
        (NumFastSeams.fpCleanup112Env
          (fpPre100Env env a (BitVec.ofNat 64 start) v8a 1)
          0 (BitVec.ofNat 64 (start + 8)) 0x8#64
          (BitVec.ofNat 64 n) (BitVec.ofNat 32 w))
        (BitVec.ofNat 64 (start + 8)) (BitVec.ofNat 64 (digitFold bs start 8)) 0x8#64
        (BitVec.ofNat 64 n)) st2) :=
    NumFastSeams.fpWhileEnd115_denote_cleanup (epow := epow) rfl hip2 hfd2 hi2 hn2
  have hbit : evalICmp .ult (BitVec.ofNat 64 (start + 8)) (BitVec.ofNat 64 n) = 1 :=
    NumFastSeams.ult_ofNat_one hmore (by omega)
  have hread' : readBytes (writeBytes s.mem v8a (natToBytes w 4)) a n = some bs := by
    rw [readBytes_writeBytes_local (m := s.mem) (w := w) hsep]; exact hread
  have hp' : lookupName (NumFastSeams.fpWhileEnd115Env
      (NumFastSeams.fpCleanup112Env
        (fpPre100Env env a (BitVec.ofNat 64 start) v8a 1)
        0 (BitVec.ofNat 64 (start + 8)) 0x8#64
        (BitVec.ofNat 64 n) (BitVec.ofNat 32 w))
      (BitVec.ofNat 64 (start + 8)) (BitVec.ofNat 64 (digitFold bs start 8)) 0x8#64
      (BitVec.ofNat 64 n)) "%p" = some (.ptr a) :=
    fpWhileEnd115Env_p (by
      simp only [NumFastSeams.fpCleanup112Env, fpPre100Env]; block_lk)
  have hn' : lookupName (NumFastSeams.fpWhileEnd115Env
      (NumFastSeams.fpCleanup112Env
        (fpPre100Env env a (BitVec.ofNat 64 start) v8a 1)
        0 (BitVec.ofNat 64 (start + 8)) 0x8#64
        (BitVec.ofNat 64 n) (BitVec.ofNat 32 w))
      (BitVec.ofNat 64 (start + 8)) (BitVec.ofNat 64 (digitFold bs start 8)) 0x8#64
      (BitVec.ofNat 64 n)) "%n" = some (.int 64 (BitVec.ofNat 64 n)) :=
    fpWhileEnd115Env_n hn2
  obtain ⟨e, hinv, hcont⟩ := fpWhileEnd115_entry (epow := epow)
    (env := NumFastSeams.fpCleanup112Env
      (fpPre100Env env a (BitVec.ofNat 64 start) v8a 1)
      0 (BitVec.ofNat 64 (start + 8)) 0x8#64
      (BitVec.ofNat 64 n) (BitVec.ofNat 32 w))
    (s := st2)
    (i := BitVec.ofNat 64 (start + 8)) (fr := BitVec.ofNat 64 (digitFold bs start 8))
    (fdig := 0x8#64)
    (mem := writeBytes s.mem v8a (natToBytes w 4)) (p := a) (n := n)
    (i0 := start + 8) (d0 := 8) (bs := bs)
    rfl hden hbit rfl hp' hn' hread'
    (by obtain ⟨idigv, ipv, hidigv, hipv⟩ := hparts
        exact ⟨idigv, ipv, by
          simp only [NumFastSeams.fpCleanup112Env, fpPre100Env]; block_lk, by
          simp only [NumFastSeams.fpCleanup112Env, fpPre100Env]; block_lk⟩)
    rfl (by decide)
    (by rw [show start + 8 - 8 = start from by omega,
      show min 8 19 = 8 from by decide])
    hmore hnlt (by omega)
  refine ⟨e, hinv, ?_⟩
  intro k
  rw [show 4 + k = 1 + (1 + (2 + k)) from by omega,
    runFuel_jump_prefix hstep1, runFuel_jump_prefix hstep2, hcont k]

/-- The second fold's count test is immediate: `%add96588941` has reached
sixteen, so `%15` is zero whatever the index test is. -/
theorem fpGuard_sixteen (add nv : BitVec 64) :
    NumFastSeams.fpGuard add (0x10#64) nv = 0 := by
  unfold NumFastSeams.fpGuard
  rw [show evalICmp .ult (0x10#64) (0xc#64) = 0 from by decide]
  split <;> rfl

/-- **The second read refuses.**  The first fold has advanced the index and the
count; the second reader's zero answer leaves for `cleanup112.thread`, whose
`phi`s carry `while.body100`'s own cells — the index after the first group, the
count eight and the first fold — and `while.end115` merges them.  Six steps
reach the head at `i0 = start + 8`, `d0 = 8`. -/
theorem fracTaken_refuse2 {epow : Int → Option EPow} {env : Env} {s : State}
    {a v8a start n w : Nat} {bs bs8a bs8b : List UInt8}
    (hpc : s.pc = "while.body100.preheader")
    (hparts : fracPartCells env)
    (hpre : s.pre = some "while.cond91.preheader")
    (hp : lookupName env "%p" = some (.ptr a))
    (hv8 : lookupName env "%v8101" = some (.ptr v8a))
    (hinc : lookupName env "%inc77" = some (.int 64 (BitVec.ofNat 64 start)))
    (h563 : lookupName env "%add92582" = some (.int 64 (BitVec.ofNat 64 (start + 8))))
    (hn : lookupName env "%n" = some (.int 64 (BitVec.ofNat 64 n)))
    (hread : readBytes s.mem a n = some bs)
    (hslice : readBytes s.mem (a + start) 8 = some bs8a)
    (hsliceb : readBytes s.mem (a + (start + 8)) 8 = some bs8b)
    (hstart : start + 8 ≤ n) (hnlt : n < 2 ^ 63)
    (hval : d8Value bs8a = some w) (hw : w < 2 ^ 32)
    (hsep : v8a + 4 ≤ a ∨ a + n ≤ v8a)
    (hsep2 : v8a + 4 ≤ a + (start + 8) ∨ a + (start + 8) + 8 ≤ v8a)
    (hguard : NumFastSeams.fpGuard
      (BitVec.ofNat 64 (start + 8) + 0x8#64) 0x8#64 (BitVec.ofNat 64 n) = 1)
    (hmore : start + 8 < n) (hval2 : d8Value bs8b = none) :
    ∃ e : State, fracRunInv (writeBytes s.mem v8a (natToBytes w 4)) a n (start + 8) 8 bs
      (n - (start + 8)) e 0 ∧
      ∀ k, runFuel (stage2NumFastCalls epow) (6 + k) numFastBody (stateAt env s)
        = runFuel (stage2NumFastCalls epow) k numFastBody e := by
  have hpos : ((BitVec.ofNat 64 start).signExtend 64).toNat < 2 ^ 63 := by
    rw [ofNat64_signExtend_toNat (by omega)]; omega
  have hslice' : readBytes s.mem
      (a + ((BitVec.ofNat 64 start).signExtend 64).toNat) 8 = some bs8a := by
    rw [ofNat64_signExtend_toNat (by omega)]; exact hslice
  let st1 : State := { s with mem := writeBytes s.mem v8a (natToBytes w 4),
                               next := s.next, pc := "cleanup112",
                               pre := some "while.body100.preheader" }
  have hstep1 : step (stage2NumFastCalls epow) numFastBody (stateAt env s) =
      .jump (stateAt (fracPre100Env env a start v8a) st1) :=
    fpPre100_step_ok (epow := epow) hpc hp hinc hv8 hpos hslice' hval hw
  have hback : readBytes (writeBytes s.mem v8a (natToBytes w 4)) v8a 4
      = some (natToBytes w 4) :=
    (NumFastSeams.numD8Answer_writes (p := a + start) (v := v8a) (w := w)
      (bs := bs8a) (mem := s.mem) (next := s.next) hslice hval hw).2.1
  have hread1 : readBytes (writeBytes s.mem v8a (natToBytes w 4)) v8a 4
      = some (natToBytes (BitVec.ofNat 32 w).toNat 4) := by
    rw [ofNat32_toNat hw]; exact hback
  have hden1 : denoteCode (stage2NumFastCalls epow) NumFastSeams.fpCleanup112Instrs
      (stateAt (fracPre100Env env a start v8a) st1) =
      some (stateAt (fracFold1Env env a v8a start n w) st1) :=
    NumFastSeams.fpCleanup112_denote_pre (epow := epow) (fr := 0) rfl
      (fracPre100Env_add92582 h563) (fracPre100Env_v8 hv8) hread1
      (fracPre100Env_n hn)
  let st2 : State := { st1 with pc := "while.body100", pre := some "cleanup112" }
  have hstep2 : step (stage2NumFastCalls epow) numFastBody
      (stateAt (fracPre100Env env a start v8a) st1) =
      .jump (stateAt (fracFold1Env env a v8a start n w) st2) :=
    NumFastSeams.fpCleanup112_step_body (epow := epow) rfl hden1 hguard
  have hp2 : lookupName (fracFold1Env env a v8a start n w) "%p" = some (.ptr a) :=
    fracFold1Env_p hp
  have h92_2 : lookupName (fracFold1Env env a v8a start n w) "%add92587942"
      = some (.int 64 (BitVec.ofNat 64 (start + 8))) :=
    fracFold1Env_add92587942 ..
  have h96_2 : lookupName (fracFold1Env env a v8a start n w) "%add96588941"
      = some (.int 64 0x8#64) := fracFold1Env_add96588941 ..
  have hv8_2 : lookupName (fracFold1Env env a v8a start n w) "%v8101"
      = some (.ptr v8a) := fracFold1Env_v8 hv8
  have hpos2 : ((BitVec.ofNat 64 (start + 8)).signExtend 64).toNat < 2 ^ 63 := by
    rw [ofNat64_signExtend_toNat (by omega)]; omega
  have hread2 : readBytes (stateAt (fracFold1Env env a v8a start n w) st2).mem
      (a + ((BitVec.ofNat 64 (start + 8)).signExtend 64).toNat) 8 = some bs8b := by
    rw [ofNat64_signExtend_toNat (by omega)]
    have hm : (stateAt (fracFold1Env env a v8a start n w) st2).mem
        = writeBytes s.mem v8a (natToBytes w 4) := rfl
    rw [hm, readBytes_writeBytes_local (m := s.mem) (w := w) hsep2]
    exact hsliceb
  have hstep3 : step (stage2NumFastCalls epow) numFastBody
      (stateAt (fracFold1Env env a v8a start n w) st2) =
      .jump (stateAt (fracBody2EnvR env a v8a start n w)
        { st2 with pc := "cleanup112.thread", pre := some "while.body100" }) :=
    NumFastSeams.fpBody100_step_refuse (epow := epow) rfl hp2 h92_2 h96_2 hv8_2 hpos2
      hread2 hval2
  have hi3 : lookupName (fracBody2EnvR env a v8a start n w) "%add92587942"
      = some (.int 64 (BitVec.ofNat 64 (start + 8))) := fracBody2EnvR_add92587942 ..
  have hfd3 : lookupName (fracBody2EnvR env a v8a start n w) "%add96588941"
      = some (.int 64 0x8#64) := fracBody2EnvR_add96588941 ..
  have hfr3 : lookupName (fracBody2EnvR env a v8a start n w) "%add109"
      = some (.int 64 (BitVec.ofNat 64 w)) := by
    rw [fracBody2EnvR_add109 .., ofNat32_toNat hw]; simp
  have hv8_3 : lookupName (fracBody2EnvR env a v8a start n w) "%v8101"
      = some (.ptr v8a) := fracBody2EnvR_v8 hv8
  have hstep4 : step (stage2NumFastCalls epow) numFastBody
      (stateAt (fracBody2EnvR env a v8a start n w)
        { st2 with pc := "cleanup112.thread", pre := some "while.body100" }) =
      .jump (stateAt (fracThread2Env env a v8a start n w)
        { st2 with pc := "while.end115", pre := some "cleanup112.thread" }) :=
    fpCleanupThread112_step_body (epow := epow) rfl rfl hi3 hfd3 hfr3 hv8_3
  have hden : denoteCode (stage2NumFastCalls epow) NumFastSeams.fpWhileEnd115Instrs
      (stateAt (fracThread2Env env a v8a start n w)
        { st2 with pc := "while.end115", pre := some "cleanup112.thread" }) =
      some (stateAt (NumFastSeams.fpWhileEnd115Env (fracThread2Env env a v8a start n w)
        (BitVec.ofNat 64 (start + 8)) (BitVec.ofNat 64 w) 0x8#64 (BitVec.ofNat 64 n))
        { st2 with pc := "while.end115", pre := some "cleanup112.thread" }) :=
    NumFastSeams.fpWhileEnd115_denote_thread (epow := epow) rfl
      (fracThread2Env_fr ..) (fracThread2Env_fdig ..) (fracThread2Env_i ..)
      (fracThread2Env_n hn)
  have hbit : evalICmp .ult (BitVec.ofNat 64 (start + 8)) (BitVec.ofNat 64 n) = 1 :=
    NumFastSeams.ult_ofNat_one hmore (by omega)
  have hfold : w = digitFold bs start 8 := NumFastSeams.d8Value_slice hread hslice hstart hval
  have hread' : readBytes (writeBytes s.mem v8a (natToBytes w 4)) a n = some bs := by
    rw [readBytes_writeBytes_local (m := s.mem) (w := w) hsep]; exact hread
  obtain ⟨e, hinv, hcont⟩ := fpWhileEnd115_entry (epow := epow)
    (env := fracThread2Env env a v8a start n w)
    (s := { st2 with pc := "while.end115", pre := some "cleanup112.thread" })
    (i := BitVec.ofNat 64 (start + 8)) (fr := BitVec.ofNat 64 w) (fdig := 0x8#64)
    (mem := writeBytes s.mem v8a (natToBytes w 4)) (p := a) (n := n)
    (i0 := start + 8) (d0 := 8) (bs := bs)
    rfl hden hbit rfl (fpWhileEnd115Env_p (fracThread2Env_p hp))
    (fpWhileEnd115Env_n (fracThread2Env_n hn))
    hread'
    (by obtain ⟨idigv, ipv, hidigv, hipv⟩ := hparts
        exact ⟨idigv, ipv, by
          simp only [fracThread2Env]; block_lk, by
          simp only [fracThread2Env]; block_lk⟩)
    rfl (by decide)
    (by rw [hfold, show start + 8 - 8 = start from by omega,
      show min 8 19 = 8 from by decide])
    hmore hnlt (by omega)
  refine ⟨e, hinv, ?_⟩
  intro k
  rw [show 6 + k = 1 + (1 + (1 + (1 + (2 + k)))) from by omega,
    runFuel_jump_prefix hstep1, runFuel_jump_prefix hstep2,
    runFuel_jump_prefix hstep3, runFuel_jump_prefix hstep4, hcont k]

/-- **Both reads succeed.**  Sixteen digits are taken: the second fold is
`%add109 * 10 ^ 8 + %14`, the index advances by sixteen, and the loop's count
test refuses the third group.  Six steps reach the head at `i0 = start + 16`,
`d0 = 16`. -/
theorem fracTaken_fold2 {epow : Int → Option EPow} {env : Env} {s : State}
    {a v8a start n w w2 : Nat} {bs bs8a bs8b : List UInt8}
    (hpc : s.pc = "while.body100.preheader")
    (hparts : fracPartCells env)
    (hpre : s.pre = some "while.cond91.preheader")
    (hp : lookupName env "%p" = some (.ptr a))
    (hv8 : lookupName env "%v8101" = some (.ptr v8a))
    (hinc : lookupName env "%inc77" = some (.int 64 (BitVec.ofNat 64 start)))
    (h563 : lookupName env "%add92582" = some (.int 64 (BitVec.ofNat 64 (start + 8))))
    (hn : lookupName env "%n" = some (.int 64 (BitVec.ofNat 64 n)))
    (hread : readBytes s.mem a n = some bs)
    (hslicea : readBytes s.mem (a + start) 8 = some bs8a)
    (hsliceb : readBytes s.mem (a + (start + 8)) 8 = some bs8b)
    (hstart : start + 8 ≤ n) (hnlt : n < 2 ^ 63)
    (hval : d8Value bs8a = some w) (hw : w < 2 ^ 32)
    (hsep : v8a + 4 ≤ a ∨ a + n ≤ v8a)
    (hsep2 : v8a + 4 ≤ a + (start + 8) ∨ a + (start + 8) + 8 ≤ v8a)
    (hguard : NumFastSeams.fpGuard
      (BitVec.ofNat 64 (start + 8) + 0x8#64) 0x8#64 (BitVec.ofNat 64 n) = 1)
    (hmore : start + 16 < n) (hval2 : d8Value bs8b = some w2) (hw2 : w2 < 2 ^ 32) :
    ∃ e : State, fracRunInv (writeBytes (writeBytes s.mem v8a (natToBytes w 4)) v8a
      (natToBytes w2 4)) a n (start + 16) 16 bs (n - (start + 16)) e 0 ∧
      ∀ k, runFuel (stage2NumFastCalls epow) (6 + k) numFastBody (stateAt env s)
        = runFuel (stage2NumFastCalls epow) k numFastBody e := by
  have hpos : ((BitVec.ofNat 64 start).signExtend 64).toNat < 2 ^ 63 := by
    rw [ofNat64_signExtend_toNat (by omega)]; omega
  have hslice' : readBytes s.mem
      (a + ((BitVec.ofNat 64 start).signExtend 64).toNat) 8 = some bs8a := by
    rw [ofNat64_signExtend_toNat (by omega)]; exact hslicea
  let st1 : State := { s with mem := writeBytes s.mem v8a (natToBytes w 4),
                               next := s.next, pc := "cleanup112",
                               pre := some "while.body100.preheader" }
  have hstep1 : step (stage2NumFastCalls epow) numFastBody (stateAt env s) =
      .jump (stateAt (fracPre100Env env a start v8a) st1) :=
    fpPre100_step_ok (epow := epow) hpc hp hinc hv8 hpos hslice' hval hw
  have hback : readBytes (writeBytes s.mem v8a (natToBytes w 4)) v8a 4
      = some (natToBytes w 4) :=
    (NumFastSeams.numD8Answer_writes (p := a + start) (v := v8a) (w := w)
      (bs := bs8a) (mem := s.mem) (next := s.next) hslicea hval hw).2.1
  have hread1 : readBytes (writeBytes s.mem v8a (natToBytes w 4)) v8a 4
      = some (natToBytes (BitVec.ofNat 32 w).toNat 4) := by
    rw [ofNat32_toNat hw]; exact hback
  have hden1 : denoteCode (stage2NumFastCalls epow) NumFastSeams.fpCleanup112Instrs
      (stateAt (fracPre100Env env a start v8a) st1) =
      some (stateAt (fracFold1Env env a v8a start n w) st1) :=
    NumFastSeams.fpCleanup112_denote_pre (epow := epow) (fr := 0) rfl
      (fracPre100Env_add92582 h563) (fracPre100Env_v8 hv8) hread1
      (fracPre100Env_n hn)
  let st2 : State := { st1 with pc := "while.body100", pre := some "cleanup112" }
  have hstep2 : step (stage2NumFastCalls epow) numFastBody
      (stateAt (fracPre100Env env a start v8a) st1) =
      .jump (stateAt (fracFold1Env env a v8a start n w) st2) :=
    NumFastSeams.fpCleanup112_step_body (epow := epow) rfl hden1 hguard
  have hp2 : lookupName (fracFold1Env env a v8a start n w) "%p" = some (.ptr a) :=
    fracFold1Env_p hp
  have h92_2 : lookupName (fracFold1Env env a v8a start n w) "%add92587942"
      = some (.int 64 (BitVec.ofNat 64 (start + 8))) :=
    fracFold1Env_add92587942 ..
  have h96_2 : lookupName (fracFold1Env env a v8a start n w) "%add96588941"
      = some (.int 64 0x8#64) := fracFold1Env_add96588941 ..
  have hv8_2 : lookupName (fracFold1Env env a v8a start n w) "%v8101"
      = some (.ptr v8a) := fracFold1Env_v8 hv8
  have hpos2 : ((BitVec.ofNat 64 (start + 8)).signExtend 64).toNat < 2 ^ 63 := by
    rw [ofNat64_signExtend_toNat (by omega)]; omega
  have hread2 : readBytes (stateAt (fracFold1Env env a v8a start n w) st2).mem
      (a + ((BitVec.ofNat 64 (start + 8)).signExtend 64).toNat) 8 = some bs8b := by
    rw [ofNat64_signExtend_toNat (by omega)]
    have hm : (stateAt (fracFold1Env env a v8a start n w) st2).mem
        = writeBytes s.mem v8a (natToBytes w 4) := rfl
    rw [hm, readBytes_writeBytes_local (m := s.mem) (w := w) hsep2]
    exact hsliceb
  let st3 : State := { st2 with mem := writeBytes st2.mem v8a (natToBytes w2 4), next := st2.next, pc := "cleanup112", pre := some "while.body100" }
  let st4 : State := { st2 with mem := writeBytes st2.mem v8a (natToBytes w2 4), next := st2.next, pc := "while.end115", pre := some "cleanup112" }
  have hstep3 : step (stage2NumFastCalls epow) numFastBody
      (stateAt (fracFold1Env env a v8a start n w) st2) =
      .jump (stateAt (fracBody2Env env a v8a start n w) st3) :=
    NumFastSeams.fpBody100_step_ok (epow := epow) rfl hp2 h92_2 h96_2 hv8_2 hpos2
      hread2 hval2 hw2
  have hv8_3 : lookupName (fracBody2Env env a v8a start n w) "%v8101"
      = some (.ptr v8a) := fracBody2Env_v8 hv8
  have hn_3 : lookupName (fracBody2Env env a v8a start n w) "%n"
      = some (.int 64 (BitVec.ofNat 64 n)) := fracBody2Env_n hn
  have hback2 : readBytes (writeBytes st2.mem v8a (natToBytes w2 4)) v8a 4
      = some (natToBytes w2 4) :=
    (NumFastSeams.numD8Answer_writes (v := v8a) (w := w2)
      (bs := bs8b) (mem := st2.mem) (next := st2.next) hread2 hval2 hw2).2.1
  have hread3 : readBytes (writeBytes st2.mem v8a (natToBytes w2 4)) v8a 4
      = some (natToBytes (BitVec.ofNat 32 w2).toNat 4) := by
    rw [ofNat32_toNat hw2]; exact hback2
  have hfr3 : lookupName (fracBody2Env env a v8a start n w) "%add109"
      = some (.int 64 (BitVec.ofNat 64 w)) := by
    rw [fracBody2Env_add109 .., ofNat32_toNat hw]; simp
  have h92_3 : lookupName (fracBody2Env env a v8a start n w) "%add92"
      = some (.int 64 (BitVec.ofNat 64 (start + 16))) := by
    rw [fracBody2Env_add92 .., NumFastStarts.ofNat64_add_const (by omega)]
  have h96_3 : lookupName (fracBody2Env env a v8a start n w) "%add96"
      = some (.int 64 0x10#64) := by
    simpa only [show ((0x8#64 : BitVec 64) + 0x8#64) = 0x10#64 from by decide]
      using fracBody2Env_add96 ..
  have hden3 : denoteCode (stage2NumFastCalls epow) NumFastSeams.fpCleanup112Instrs
      (stateAt (fracBody2Env env a v8a start n w) st3) =
      some (stateAt (fracFold2Env env a v8a start n w w2) st3) :=
    NumFastSeams.fpCleanup112_denote_body (epow := epow) rfl hfr3 h92_3 h96_3 hv8_3
      hread3 hn_3
  have hbit2 : NumFastSeams.fpGuard ((BitVec.ofNat 64 (start + 16)) + 0x8#64) 0x10#64
      (BitVec.ofNat 64 n) = 0 := fpGuard_sixteen _ _
  have hstep4 : step (stage2NumFastCalls epow) numFastBody
      (stateAt (fracBody2Env env a v8a start n w) st3) =
      .jump (stateAt (fracFold2Env env a v8a start n w w2) st4) :=
    NumFastSeams.fpCleanup112_step_end (epow := epow) rfl hden3 hbit2
  have hfold8 : w = digitFold bs start 8 := NumFastSeams.d8Value_slice hread hslicea hstart hval
  have hw2fold : w2 = digitFold bs (start + 8) 8 :=
    NumFastSeams.d8Value_slice hread hsliceb (by omega) hval2
  have hblen : bs.length = n := JsonEntrySteps.readBytes_length s.mem a n hread
  have hsplit16 : digitFold bs start 16
      = digitFold bs start 8 * 10 ^ 8 + digitFold bs (start + 8) 8 := by
    have := NumFastSeams.digitFold_split (bs := bs) (start := start) (k := 8) (m := 8) (by omega)
    simpa only [show (8 : Nat) + 8 = 16 from rfl] using this
  have hfr4 : lookupName (fracFold2Env env a v8a start n w w2) "%add109"
      = some (.int 64 (BitVec.ofNat 64 (digitFold bs start 16))) := by
    rw [fracFold2Env_add109 .., ofNat32_toNat hw2, hfold8, hw2fold]
    rw [show (0x5f5e100#64) = BitVec.ofNat 64 (10 ^ 8) from by decide,
      BitVec.ofNat_mul_ofNat, BitVec.ofNat_add_ofNat, hsplit16]
  have hfd4 : lookupName (fracFold2Env env a v8a start n w w2) "%add96588941"
      = some (.int 64 0x10#64) := fracFold2Env_add96588941 ..
  have hi4 : lookupName (fracFold2Env env a v8a start n w w2) "%add92587942"
      = some (.int 64 (BitVec.ofNat 64 (start + 16))) :=
    fracFold2Env_add92587942 ..
  have hn4 : lookupName (fracFold2Env env a v8a start n w w2) "%n"
      = some (.int 64 (BitVec.ofNat 64 n)) := fracFold2Env_n hn
  have hden4 : denoteCode (stage2NumFastCalls epow) NumFastSeams.fpWhileEnd115Instrs
      (stateAt (fracFold2Env env a v8a start n w w2) st4) =
      some (stateAt (NumFastSeams.fpWhileEnd115Env (fracFold2Env env a v8a start n w w2)
        (BitVec.ofNat 64 (start + 16)) (BitVec.ofNat 64 (digitFold bs start 16)) 0x10#64
        (BitVec.ofNat 64 n)) st4) :=
    NumFastSeams.fpWhileEnd115_denote_cleanup (epow := epow) rfl hfr4 hfd4 hi4 hn4
  have hbit3 : evalICmp .ult (BitVec.ofNat 64 (start + 16)) (BitVec.ofNat 64 n) = 1 :=
    NumFastSeams.ult_ofNat_one hmore (by omega)
  have hread' : readBytes (writeBytes (writeBytes s.mem v8a (natToBytes w 4)) v8a
      (natToBytes w2 4)) a n = some bs := by
    rw [readBytes_writeBytes_local (m := writeBytes s.mem v8a (natToBytes w 4))
      (w := w2) hsep]
    rw [readBytes_writeBytes_local (m := s.mem) (w := w) hsep]
    exact hread
  have hmem : (stateAt (fracFold2Env env a v8a start n w w2) st4).mem
      = writeBytes (writeBytes s.mem v8a (natToBytes w 4)) v8a (natToBytes w2 4) := rfl
  obtain ⟨e, hinv, hcont⟩ := fpWhileEnd115_entry (epow := epow)
    (env := fracFold2Env env a v8a start n w w2)
    (s := st4)
    (i := BitVec.ofNat 64 (start + 16)) (fr := BitVec.ofNat 64 (digitFold bs start 16))
    (fdig := 0x10#64)
    (mem := writeBytes (writeBytes s.mem v8a (natToBytes w 4)) v8a (natToBytes w2 4))
    (p := a) (n := n) (i0 := start + 16) (d0 := 16) (bs := bs)
    rfl hden4 hbit3 hmem (fpWhileEnd115Env_p (fracFold2Env_p hp))
    (fpWhileEnd115Env_n (fracFold2Env_n hn))
    hread'
    (by obtain ⟨idigv, ipv, hidigv, hipv⟩ := hparts
        exact ⟨idigv, ipv, by
          simp only [fracFold2Env]; block_lk, by
          simp only [fracFold2Env]; block_lk⟩)
    rfl (by decide)
    (by rw [show start + 16 - 16 = start from by omega,
      show min 16 19 = 16 from by decide])
    hmore hnlt (by omega)
  refine ⟨e, hinv, ?_⟩
  intro k
  rw [show 6 + k = 1 + (1 + (1 + (1 + (2 + k)))) from by omega,
    runFuel_jump_prefix hstep1, runFuel_jump_prefix hstep2,
    runFuel_jump_prefix hstep3, runFuel_jump_prefix hstep4, hcont k]

/-- **The fraction's case split at the two reader answers.**  At the fraction's
preheader with the guard's zero, the four shapes above are the four answers: the
first read's `none`, and its `some` split by the loop's guard and then by the
second read's answer.  The two-group branches take the second group's eight bytes
as readable and the reader's local as separated from them; a lexeme that stops
before the second group is the first two branches. -/
theorem fracTakenGuard_entry {epow : Int → Option EPow} {env : Env} {s : State}
    {a v8a start n : Nat} {bs bs8a bs8b : List UInt8}
    (hpc : s.pc = "while.body100.preheader")
    (hparts : fracPartCells env)
    (hpre : s.pre = some "while.cond91.preheader")
    (hp : lookupName env "%p" = some (.ptr a))
    (hv8 : lookupName env "%v8101" = some (.ptr v8a))
    (hinc : lookupName env "%inc77" = some (.int 64 (BitVec.ofNat 64 start)))
    (h563 : lookupName env "%add92582" = some (.int 64 (BitVec.ofNat 64 (start + 8))))
    (hn : lookupName env "%n" = some (.int 64 (BitVec.ofNat 64 n)))
    (hread : readBytes s.mem a n = some bs)
    (hslicea : readBytes s.mem (a + start) 8 = some bs8a)
    (hstart : start + 8 ≤ n) (hnlt : n < 2 ^ 63)
    (hsep : v8a + 4 ≤ a ∨ a + n ≤ v8a) :
    (d8Value bs8a = none →
        ∃ e : State, fracRunInv s.mem a n start 0 bs (n - start) e 0 ∧
          ∀ k, runFuel (stage2NumFastCalls epow) (4 + k) numFastBody (stateAt env s)
            = runFuel (stage2NumFastCalls epow) k numFastBody e)
    ∧ (∀ (w : Nat), d8Value bs8a = some w → w < 2 ^ 32 →
        NumFastSeams.fpGuard (BitVec.ofNat 64 (start + 8) + 0x8#64) 0x8#64
          (BitVec.ofNat 64 n) = 0 →
        start + 8 < n →
        ∃ e : State, fracRunInv (writeBytes s.mem v8a (natToBytes w 4)) a n (start + 8) 8 bs
          (n - (start + 8)) e 0 ∧
          ∀ k, runFuel (stage2NumFastCalls epow) (4 + k) numFastBody (stateAt env s)
            = runFuel (stage2NumFastCalls epow) k numFastBody e)
    ∧ (readBytes s.mem (a + (start + 8)) 8 = some bs8b →
        (v8a + 4 ≤ a + (start + 8) ∨ a + (start + 8) + 8 ≤ v8a) →
        ∀ (w : Nat), d8Value bs8a = some w → w < 2 ^ 32 →
        NumFastSeams.fpGuard (BitVec.ofNat 64 (start + 8) + 0x8#64) 0x8#64
          (BitVec.ofNat 64 n) = 1 →
        start + 8 < n → d8Value bs8b = none →
        ∃ e : State, fracRunInv (writeBytes s.mem v8a (natToBytes w 4)) a n (start + 8) 8 bs
          (n - (start + 8)) e 0 ∧
          ∀ k, runFuel (stage2NumFastCalls epow) (6 + k) numFastBody (stateAt env s)
            = runFuel (stage2NumFastCalls epow) k numFastBody e)
    ∧ (readBytes s.mem (a + (start + 8)) 8 = some bs8b →
        (v8a + 4 ≤ a + (start + 8) ∨ a + (start + 8) + 8 ≤ v8a) →
        ∀ (w w2 : Nat), d8Value bs8a = some w → w < 2 ^ 32 →
        NumFastSeams.fpGuard (BitVec.ofNat 64 (start + 8) + 0x8#64) 0x8#64
          (BitVec.ofNat 64 n) = 1 →
        start + 16 < n → d8Value bs8b = some w2 → w2 < 2 ^ 32 →
        ∃ e : State, fracRunInv (writeBytes (writeBytes s.mem v8a (natToBytes w 4)) v8a
          (natToBytes w2 4)) a n (start + 16) 16 bs (n - (start + 16)) e 0 ∧
          ∀ k, runFuel (stage2NumFastCalls epow) (6 + k) numFastBody (stateAt env s)
            = runFuel (stage2NumFastCalls epow) k numFastBody e) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hnone
    exact fracTaken_refuse1 hpc hparts hpre hp hv8 hinc h563 hn hread hslicea hstart
      hnlt hnone
  · intro w hsome hw hguard hmore
    exact fracTaken_exit hpc hparts hpre hp hv8 hinc h563 hn hread hslicea hstart hnlt
      hsome hw hsep hguard hmore
  · intro hsliceb hsep2 w hsome hw hguard hmore hnone
    exact fracTaken_refuse2 hpc hparts hpre hp hv8 hinc h563 hn hread hslicea hsliceb
      hstart hnlt hsome hw hsep hsep2 hguard hmore hnone
  · intro hsliceb hsep2 w w2 hsome hw hguard hmore hsome2 hw2
    exact fracTaken_fold2 hpc hparts hpre hp hv8 hinc h563 hn hread hslicea hsliceb
      hstart hnlt hsome hw hsep hsep2 hguard hmore hsome2 hw2

/-! ### The fraction's guard block

`while.cond91.preheader` writes `%add92582 = %i.5 + 9` and tests it against the
length; taken, the block's `condbr` enters `while.body100.preheader`.  The step
below is that edge, and `fracWhileCond91_entry` composes it with the case split,
so the entry is stated at the guard's own block: the guard's zero is the `Nat`
fact that the fraction has its nine bytes. -/

/-- **`while.cond91.preheader`'s taken edge.**  The guard's zero enters the
fraction's preheader. -/
theorem whileCond91Preheader_step_taken {calls : Calls} {env : Env} {s : State}
    {i5 : Nat} {nv : BitVec 64}
    (hpc : s.pc = "while.cond91.preheader")
    (hi : lookupName env "%i.5" = some (.int 64 (BitVec.ofNat 64 i5)))
    (hn : lookupName env "%n" = some (.int 64 nv))
    (hbit : evalICmp .ugt (BitVec.ofNat 64 i5 + 0x9#64) nv = 0) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (NumFastStarts.whileCond91PreheaderEnv env i5 nv)
        { s with pc := "while.body100.preheader", pre := some "while.cond91.preheader" }) := by
  refine numFast_step_at (s' := stateAt (NumFastStarts.whileCond91PreheaderEnv env i5 nv) s)
    (b := ⟨"while.cond91.preheader",
      [Instr.binop "%add92582" (BinOp.add) 64 (Operand.reg "%i.5")
        (Operand.imm (Const.int 64 0x0000000000000009#64)),
       Instr.icmp "%cmp93583.not" (IPred.ugt) 64 (Operand.reg "%add92582")
         (Operand.reg "%n")],
      Term.condbr (Operand.reg "%cmp93583.not") "while.end115" "while.body100.preheader"⟩)
    ?_ ?_ ?_
  · simpa only [stateAt, hpc] using numFast_findBlock_while_cond91_preheader
  · simpa only [denoteCode_nil] using
      NumFastStarts.whileCond91Preheader_denote (calls := calls) hi hn
  · have hlk : lookupName (NumFastStarts.whileCond91PreheaderEnv env i5 nv) "%cmp93583.not"
        = some (.int 1 (evalICmp .ugt (BitVec.ofNat 64 i5 + 0x9#64) nv)) :=
      lookupName_cons_self ..
    rw [numFast_execTerm_condbr_zero _ "%cmp93583.not" "while.end115"
      "while.body100.preheader" hlk hbit]
    simp only [stateAt, hpc]

/-- **The fraction's taken guard's entry into `fracRunInv`.**  At
`while.cond91.preheader` with the guard's zero — the fraction has its nine bytes
— the fast path's four answers reach the fraction head's invariant at
`(start, 0)`, `(start + 8, 8)`, `(start + 8, 8)` or `(start + 16, 16)`, in six
steps for the one-group shapes and eight for the two-group ones. -/
theorem fracWhileCond91_entry {epow : Int → Option EPow} {env : Env} {s : State}
    {a v8a i5 n : Nat} {bs : List UInt8}
    (hpc : s.pc = "while.cond91.preheader")
    (hparts : fracPartCells env)
    (hp : lookupName env "%p" = some (.ptr a))
    (hv8 : lookupName env "%v8101" = some (.ptr v8a))
    (hi5 : lookupName env "%i.5" = some (.int 64 (BitVec.ofNat 64 i5)))
    (hinc : lookupName env "%inc77" = some (.int 64 (BitVec.ofNat 64 (i5 + 1))))
    (hn : lookupName env "%n" = some (.int 64 (BitVec.ofNat 64 n)))
    (hread : readBytes s.mem a n = some bs)
    (hstart : i5 + 9 ≤ n) (hnlt : n < 2 ^ 63)
    (hsep : v8a + 4 ≤ a ∨ a + n ≤ v8a)
    (hsep2 : v8a + 4 ≤ a + (i5 + 1 + 8) ∨ a + (i5 + 1 + 8) + 8 ≤ v8a)
    (hbit : evalICmp .ugt (BitVec.ofNat 64 i5 + 0x9#64) (BitVec.ofNat 64 n) = 0) :
    (d8Value ((bs.drop (i5 + 1)).take 8) = none →
        ∃ e : State, fracRunInv s.mem a n (i5 + 1) 0 bs (n - (i5 + 1)) e 0 ∧
          ∀ k, runFuel (stage2NumFastCalls epow) (5 + k) numFastBody (stateAt env s)
            = runFuel (stage2NumFastCalls epow) k numFastBody e)
    ∧ (∀ (w : Nat), d8Value ((bs.drop (i5 + 1)).take 8) = some w → w < 2 ^ 32 →
        NumFastSeams.fpGuard (BitVec.ofNat 64 (i5 + 1 + 8) + 0x8#64) 0x8#64
          (BitVec.ofNat 64 n) = 0 →
        i5 + 1 + 8 < n →
        ∃ e : State, fracRunInv (writeBytes s.mem v8a (natToBytes w 4)) a n (i5 + 1 + 8) 8 bs
          (n - (i5 + 1 + 8)) e 0 ∧
          ∀ k, runFuel (stage2NumFastCalls epow) (5 + k) numFastBody (stateAt env s)
            = runFuel (stage2NumFastCalls epow) k numFastBody e)
    ∧ (readBytes s.mem (a + (i5 + 1 + 8)) 8 = some ((bs.drop (i5 + 1 + 8)).take 8) →
        (v8a + 4 ≤ a + (i5 + 1 + 8) ∨ a + (i5 + 1 + 8) + 8 ≤ v8a) →
        ∀ (w : Nat), d8Value ((bs.drop (i5 + 1)).take 8) = some w → w < 2 ^ 32 →
        NumFastSeams.fpGuard (BitVec.ofNat 64 (i5 + 1 + 8) + 0x8#64) 0x8#64
          (BitVec.ofNat 64 n) = 1 →
        i5 + 1 + 8 < n → d8Value ((bs.drop (i5 + 1 + 8)).take 8) = none →
        ∃ e : State, fracRunInv (writeBytes s.mem v8a (natToBytes w 4)) a n (i5 + 1 + 8) 8 bs
          (n - (i5 + 1 + 8)) e 0 ∧
          ∀ k, runFuel (stage2NumFastCalls epow) (7 + k) numFastBody (stateAt env s)
            = runFuel (stage2NumFastCalls epow) k numFastBody e)
    ∧ (readBytes s.mem (a + (i5 + 1 + 8)) 8 = some ((bs.drop (i5 + 1 + 8)).take 8) →
        (v8a + 4 ≤ a + (i5 + 1 + 8) ∨ a + (i5 + 1 + 8) + 8 ≤ v8a) →
        ∀ (w w2 : Nat), d8Value ((bs.drop (i5 + 1)).take 8) = some w → w < 2 ^ 32 →
        NumFastSeams.fpGuard (BitVec.ofNat 64 (i5 + 1 + 8) + 0x8#64) 0x8#64
          (BitVec.ofNat 64 n) = 1 →
        i5 + 1 + 16 < n → d8Value ((bs.drop (i5 + 1 + 8)).take 8) = some w2 →
        w2 < 2 ^ 32 →
        ∃ e : State, fracRunInv (writeBytes (writeBytes s.mem v8a (natToBytes w 4)) v8a
          (natToBytes w2 4)) a n (i5 + 1 + 16) 16 bs (n - (i5 + 1 + 16)) e 0 ∧
          ∀ k, runFuel (stage2NumFastCalls epow) (7 + k) numFastBody (stateAt env s)
            = runFuel (stage2NumFastCalls epow) k numFastBody e) := by
  have hstep0 : step (stage2NumFastCalls epow) numFastBody (stateAt env s) =
      .jump (stateAt (NumFastStarts.whileCond91PreheaderEnv env i5 (BitVec.ofNat 64 n))
        { s with pc := "while.body100.preheader", pre := some "while.cond91.preheader" }) :=
    whileCond91Preheader_step_taken (calls := stage2NumFastCalls epow) hpc hi5 hn hbit
  have hp' : lookupName (NumFastStarts.whileCond91PreheaderEnv env i5 (BitVec.ofNat 64 n))
      "%p" = some (.ptr a) := by
    simp only [NumFastStarts.whileCond91PreheaderEnv]; block_lk
  have hv8' : lookupName (NumFastStarts.whileCond91PreheaderEnv env i5 (BitVec.ofNat 64 n))
      "%v8101" = some (.ptr v8a) := by
    simp only [NumFastStarts.whileCond91PreheaderEnv]; block_lk
  have hn' : lookupName (NumFastStarts.whileCond91PreheaderEnv env i5 (BitVec.ofNat 64 n))
      "%n" = some (.int 64 (BitVec.ofNat 64 n)) := by
    simp only [NumFastStarts.whileCond91PreheaderEnv]; block_lk
  have hinc' : lookupName (NumFastStarts.whileCond91PreheaderEnv env i5 (BitVec.ofNat 64 n))
      "%inc77" = some (.int 64 (BitVec.ofNat 64 (i5 + 1))) := by
    simp only [NumFastStarts.whileCond91PreheaderEnv]; block_lk
  have h92' : lookupName (NumFastStarts.whileCond91PreheaderEnv env i5 (BitVec.ofNat 64 n))
      "%add92582" = some (.int 64 (BitVec.ofNat 64 (i5 + 1 + 8))) := by
    simp only [NumFastStarts.whileCond91PreheaderEnv]
    rw [NumFastStarts.ofNat64_add_const (j := i5) (k := 9) (by omega)]
    rw [show i5 + 9 = i5 + 1 + 8 from by omega]
    frac_lk
  have hslicea : readBytes s.mem (a + (i5 + 1)) 8
      = some ((bs.drop (i5 + 1)).take 8) := by
    obtain ⟨-, hdrop⟩ := readBytes_split s.mem a (i5 + 1) (n - (i5 + 1))
      (bs := bs) (by
        rw [Nat.add_sub_cancel' (by omega)]; exact hread)
    obtain ⟨h8, -⟩ := readBytes_split s.mem (a + (i5 + 1)) 8
      (n - (i5 + 1) - 8) (by
        rw [show 8 + (n - (i5 + 1) - 8) = n - (i5 + 1) from by omega]
        exact hdrop)
    exact h8
  have hbase := fracTakenGuard_entry (epow := epow)
    (env := NumFastStarts.whileCond91PreheaderEnv env i5 (BitVec.ofNat 64 n))
    (s := { s with pc := "while.body100.preheader", pre := some "while.cond91.preheader" })
    (a := a) (v8a := v8a) (start := i5 + 1) (n := n)
    (bs := bs) (bs8a := (bs.drop (i5 + 1)).take 8)
    (bs8b := (bs.drop (i5 + 1 + 8)).take 8)
    rfl
    (by obtain ⟨idigv, ipv, hidigv, hipv⟩ := hparts
        exact ⟨idigv, ipv, by
          simp only [NumFastStarts.whileCond91PreheaderEnv]; block_lk, by
          simp only [NumFastStarts.whileCond91PreheaderEnv]; block_lk⟩)
    rfl hp' hv8' hinc' h92' hn' hread hslicea (by omega) hnlt hsep
  exact ⟨fun hnone => by
      obtain ⟨e, hinv, hcont⟩ := hbase.1 hnone
      exact ⟨e, hinv, fun k => by
        rw [show 5 + k = 1 + (4 + k) from by omega,
          runFuel_jump_prefix hstep0, hcont k]⟩,
    fun w hsome hw hgd hmore => by
      obtain ⟨e, hinv, hcont⟩ := hbase.2.1 w hsome hw hgd hmore
      exact ⟨e, hinv, fun k => by
        rw [show 5 + k = 1 + (4 + k) from by omega,
          runFuel_jump_prefix hstep0, hcont k]⟩,
    fun hsb hsep2' w hsome hw hgd hmore hnone => by
      obtain ⟨e, hinv, hcont⟩ := hbase.2.2.1 hsb hsep2' w hsome hw hgd hmore hnone
      exact ⟨e, hinv, fun k => by
        rw [show 7 + k = 1 + (6 + k) from by omega,
          runFuel_jump_prefix hstep0, hcont k]⟩,
    fun hsb hsep2' w w2 hsome hw hgd hmore hsome2 hw2 => by
      obtain ⟨e, hinv, hcont⟩ :=
        hbase.2.2.2 hsb hsep2' w w2 hsome hw hgd hmore hsome2 hw2
      exact ⟨e, hinv, fun k => by
        rw [show 7 + k = 1 + (6 + k) from by omega,
          runFuel_jump_prefix hstep0, hcont k]⟩⟩

/-! ### Axiom footprints

The two memory lemmas are the per-byte `readByte_writeBytes_outside` lifted to a
sequence, and the projections are the builders' peels; the compositions add the
runs' `ult_ofNat_one`, whose two-valued branch is the tree's `Classical.choice`.
Nothing below is a `sorry`: the instrument prints `sorryAx` for a `sorry`-backed
declaration, so the pins are evidence and not decoration. -/

/-- info: 'LeanLLVM.Refinement.NumFastTaken.readBytes_writeBytes_outside' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms readBytes_writeBytes_outside

/-- info: 'LeanLLVM.Refinement.NumFastTaken.readBytes_writeBytes_local' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms readBytes_writeBytes_local

/-- info: 'LeanLLVM.Refinement.NumFastTaken.fpWhileEndEnv_i' depends on axioms: [propext] -/
#guard_msgs in
#print axioms fpWhileEndEnv_i

/-- info: 'LeanLLVM.Refinement.NumFastTaken.fpWhileEnd_entry' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms fpWhileEnd_entry

/-- info: 'LeanLLVM.Refinement.NumFastTaken.fpTaken_refuse1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms fpTaken_refuse1

/-- info: 'LeanLLVM.Refinement.NumFastTaken.fpTaken_exit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms fpTaken_exit

/-- info: 'LeanLLVM.Refinement.NumFastTaken.fpTaken_refuse2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms fpTaken_refuse2

/-- info: 'LeanLLVM.Refinement.NumFastTaken.fpTaken_fold2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms fpTaken_fold2

/-- info: 'LeanLLVM.Refinement.NumFastTaken.fpTakenGuard_entry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms fpTakenGuard_entry

/-- info: 'LeanLLVM.Refinement.NumFastTaken.taken_fast_guard' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms taken_fast_guard

/-- info: 'LeanLLVM.Refinement.NumFastTaken.fpIfThen22_step_taken' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms fpIfThen22_step_taken

/-- info: 'LeanLLVM.Refinement.NumFastTaken.fpIfThen22_entry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms fpIfThen22_entry

/-- info: 'LeanLLVM.Refinement.NumFastTaken.fracTaken_refuse1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms fracTaken_refuse1

/-- info: 'LeanLLVM.Refinement.NumFastTaken.fracTaken_exit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms fracTaken_exit

/-- info: 'LeanLLVM.Refinement.NumFastTaken.fracTaken_refuse2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms fracTaken_refuse2

/-- info: 'LeanLLVM.Refinement.NumFastTaken.fracTaken_fold2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms fracTaken_fold2

/-- info: 'LeanLLVM.Refinement.NumFastTaken.fracTakenGuard_entry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms fracTakenGuard_entry

/-- info: 'LeanLLVM.Refinement.NumFastTaken.whileCond91Preheader_step_taken' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms whileCond91Preheader_step_taken

/-- info: 'LeanLLVM.Refinement.NumFastTaken.fracWhileCond91_entry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms fracWhileCond91_entry

end NumFastTaken

end LeanLLVM.Refinement
