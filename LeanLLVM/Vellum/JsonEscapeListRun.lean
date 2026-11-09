/-
The list body's run after its lane loop, and the record it is read at.

`escapeListFunction` is one program with two backward edges: the `xl_lanes` set-bit
loop, closed on `LoopFuel`'s carried-word induction in `JsonEscapeListLoop`, and the
`xl_emit` batch loop, which is the remaining-block shape — its exit test compares the
residual word with zero rather than with its own next iterate — and is not on that
induction.  Between them sit the seed blocks (`entry`, `if.then.i`, `if.end.i`),
traced in `JsonEscapeListBody`, and the blocks `xl_lanes.exit`, `if.end.i4`,
`for.body.preheader.i.i`, `while.body.preheader.i.i` and `xl_emit.exit`.

This module traces those blocks against the pinned AST and carries the record's
memory through them.  Three things are stated here, and nothing claims the record:

* **The byte arithmetic the record's staging needs.**  The carry's sixteen bytes as
  the two words the entry block loads; the count as the 64-bit value `if.end.i4`
  loads; and the reason the inlined first batch's `or` and the out-of-line batch's
  `add` agree on the lanes the batch *claims*.  They do not agree on the eight-entry
  reserve: `%conv ||| 64` and `%conv + 64` differ whenever bit six of the base is
  set, which is exactly where the record is silent, so the first batch's store is
  kept as its own memory expression rather than folded into `batchMem`.

* **`xl_lanes.exit`'s step**, which stores the outgoing carry, forms the position
  word `(w | ctl) & im` and the position base `blk0.tr << 6`, and branches to the
  emitter's exit or to the first batch.  It is stated at a state and a predecessor so
  the two ways the lanes loop can leave it — the seed fixed at `if.end.i`, and the
  loop's own exit — are the same lemma applied twice.

* **The staging's disjointness is used, not assumed.**  The count's slot is read back
  after the carry's stores and after every batch, so the trace's memory facts are
  stated at the *input* memory plus the writes the record names, and the two
  exclusions in `Γ_escape_positions.pre` are what make them sound.

The module imports `JsonEscapeListLoop`, so its direction is
`JsonEscapeListRun → ListLoop → ListBody → Steps`: the module that defines the trace
lemma is importable by the one that states the record's theorem, which is the test
`JsonEscapeSteps` itself cannot meet here because `JsonEscapeListBody` imports it.
-/
import LeanLLVM.Vellum.JsonEscapeListLoop
import LeanLLVM.Vellum.JsonEscapeListLanes
import LeanLLVM.Vellum.JsonEscapeBatchEntries

namespace LeanLLVM.Vellum

open LeanLLVM
open LeanLLVM.JSON
open LeanLLVM.Vellum.JsonEscapeIR
open LeanLLVM.Vellum.JsonS1MasksIR
open LeanLLVM.Vellum.JsonScanSpec
open LeanLLVM.Vellum.JsonEscapeIntrinsics
open LeanLLVM.Vellum.BitLanes
open LeanLLVM.Vellum.JsonB8Steps

/-! ### The staging's byte facts -/

theorem flagBytes_eq_prevWord (b : Bool) :
    flagBytes b = natToBytes (prevBackslashWord b).toNat 8 := by
  rw [prevBackslashWord_toNat]
  rfl

/-- The carry slot's sixteen bytes are the two words the entry block loads. -/
theorem carry_words {mem : Mem} {carry : Nat} {prevb prevs : Bool}
    (h : readBytes mem carry 16 = some (flagBytes prevb ++ flagBytes prevs)) :
    readBytes mem carry 8 = some (natToBytes (prevBackslashWord prevb).toNat 8) ∧
      readBytes mem (carry + 8) 8 =
        some (natToBytes (prevBackslashWord prevs).toNat 8) := by
  have h16 : readBytes mem carry (8 + 8) = some (flagBytes prevb ++ flagBytes prevs) := h
  obtain ⟨h1, h2⟩ := readBytes_split mem carry 8 8 h16
  have hlen : (flagBytes prevb).length = 8 := by
    rw [flagBytes_eq_prevWord, natToBytes_length]
  have ht : (flagBytes prevb ++ flagBytes prevs).take 8 = flagBytes prevb := by
    rw [← hlen, List.take_left]
  have hd : (flagBytes prevb ++ flagBytes prevs).drop 8 = flagBytes prevs := by
    rw [← hlen, List.drop_left]
  refine ⟨?_, ?_⟩
  · rw [h1, ht, flagBytes_eq_prevWord]
  · rw [h2, hd, flagBytes_eq_prevWord]

/-- A 64-bit load of the count's eight bytes binds `BitVec.ofNat 64 xn0`. -/
theorem b_load64_nat (env : Env) (s : State) (d p : String) (a xn0 : Nat)
    (hp : lookupName env p = some (.ptr a))
    (hv : readBytes s.mem a 8 = some (natToBytes xn0 8)) :
    evalInstr escapeCalls (withEnv env s) (.load d (.int 64) (.reg p)) =
      some (withEnv ((d, .int 64 (BitVec.ofNat 64 xn0)) :: env) s) := by
  have hval : loadValue s.mem (.int 64) a = some (.int 64 (BitVec.ofNat 64 xn0)) := by
    rw [loadValue_i64_of_readBytes hv]
    have hb : bytesToNat (natToBytes xn0 8) = xn0 % 256 ^ 8 := natToBytes_toNat xn0 8
    rw [hb, show (256 : Nat) ^ 8 = 2 ^ 64 from by decide]
    rw [show BitVec.ofNat 64 (xn0 % 2 ^ 64) = BitVec.ofNat 64 xn0 from by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_mod]]
  exact evalInstr_load (hp := evalOperand_reg_of env s p (.ptr a) hp) (hv := hval)

/-- `store i64` at a state whose memory is named, so a chain of stores keeps one
memory expression rather than nesting record updates. -/
theorem b_store64_mem (env : Env) (s : State) (m : Mem) (r p : String) (x : BitVec 64) (a : Nat)
    (hv : lookupName env r = some (.int 64 x))
    (hp : lookupName env p = some (.ptr a)) :
    evalInstr escapeCalls (withEnv env { s with mem := m })
        (.store (.int 64) (.reg r) (.reg p)) =
      some (withEnv env { s with mem := writeBytes m a (natToBytes x.toNat 8) }) := by
  refine evalInstr_store (s := withEnv env { s with mem := m })
    (s' := withEnv env { s with mem := writeBytes m a (natToBytes x.toNat 8) })
    (vv := .int 64 x) (a := a) ?_ ?_ ?_
  · exact evalOperand_reg_of env { s with mem := m } r (.int 64 x) hv
  · exact evalOperand_reg_of env { s with mem := m } p (.ptr a) hp
  · simp [storeValue, withEnv]

/-- `%d = gep i32, ptr %base, %off` at a 32-bit index: four bytes per step. -/
theorem b_gep4_reg32 (env : Env) (s : State) (d base off : String) (a : Nat)
    (x : BitVec 32) (k : Nat)
    (hb : lookupName env base = some (.ptr a))
    (ho : lookupName env off = some (.int 32 x))
    (hk : (x.signExtend 64).toNat = k) (hpos : k < 2 ^ 63) :
    evalInstr escapeCalls (withEnv env s) (.gep d (.int 32) (.reg base) (.reg off)) =
      some (withEnv ((d, .ptr (a + k * 4)) :: env) s) := by
  rw [evalInstr_gep (hb := evalOperand_reg_of env s base (.ptr a) hb)
    (ho := evalOperand_reg_of env s off (.int 32 x) ho) (hpos := by rw [hk]; exact hpos)]
  simp only [withEnv, State.bind, hk, Ty.sizeBytes]

/-- `%d = gep i32, ptr %base, %off` at a 64-bit index: four bytes per step. -/
theorem b_gep4_reg64 (env : Env) (s : State) (d base off : String) (a : Nat)
    (x : BitVec 64) (k : Nat)
    (hb : lookupName env base = some (.ptr a))
    (ho : lookupName env off = some (.int 64 x))
    (hk : (x.signExtend 64).toNat = k) (hpos : k < 2 ^ 63) :
    evalInstr escapeCalls (withEnv env s) (.gep d (.int 32) (.reg base) (.reg off)) =
      some (withEnv ((d, .ptr (a + k * 4)) :: env) s) := by
  rw [evalInstr_gep (hb := evalOperand_reg_of env s base (.ptr a) hb)
    (ho := evalOperand_reg_of env s off (.int 64 x) ho) (hpos := by rw [hk]; exact hpos)]
  simp only [withEnv, State.bind, hk, Ty.sizeBytes]

/-- `%d = zext i32 %src to i64`. -/
theorem b_zext32_64 (env : Env) (s : State) (d src : String) (x : BitVec 32)
    (h : lookupName env src = some (.int 32 x)) :
    evalInstr escapeCalls (withEnv env s) (.zext d 32 64 (.reg src)) =
      some (withEnv ((d, .int 64 (BitVec.ofNat 64 x.toNat)) :: env) s) := by
  rw [evalInstr_zext (hv := evalOperand_reg_of env s src (.int 32 x) h)]
  simp only [withEnv, State.bind]

/-- **Addition carries nothing when the operands' set bits are disjoint.**  Stated
at a multiple of a power of two plus a value below it, which is the shape the
inlined batch's `or` has: the base is shifted by six and the claimed lane is below
sixty-four. -/
theorem nat_lor_mul_two_pow_add {m b n : Nat} (hb : b < 2 ^ n) :
    m * 2 ^ n ||| b = m * 2 ^ n + b := by
  apply Nat.eq_of_testBit_eq
  intro k
  rw [Nat.testBit_or, Nat.testBit_mul_two_pow]
  by_cases hk : n ≤ k
  · have hb0 : b.testBit k = false := by
      apply Nat.testBit_lt_two_pow
      calc b < 2 ^ n := hb
        _ ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) hk
    rw [decide_eq_true hk, Bool.true_and, hb0, Bool.or_false]
    have hdiv : (m * 2 ^ n + b) / 2 ^ k = m / 2 ^ (k - n) := by
      have hsplit : 2 ^ k = 2 ^ n * 2 ^ (k - n) := by
        rw [← Nat.pow_add, Nat.add_sub_cancel' hk]
      have hlow : (m * 2 ^ n + b) / 2 ^ n = m := by
        rw [Nat.add_comm, Nat.add_mul_div_right b m (Nat.two_pow_pos n),
          Nat.div_eq_of_lt hb, Nat.zero_add]
      rw [hsplit, ← Nat.div_div_eq_div_mul, hlow]
    have hR : (m * 2 ^ n + b).testBit k = m.testBit (k - n) := by
      have h1 : (m * 2 ^ n + b).testBit k =
          ((m * 2 ^ n + b) / 2 ^ k).testBit 0 := by
        simpa using (Nat.testBit_div_two_pow (n := k) (x := m * 2 ^ n + b) (i := 0)).symm
      have h2 : (m / 2 ^ (k - n)).testBit 0 = m.testBit (k - n) := by
        simpa using Nat.testBit_div_two_pow (n := k - n) (x := m) (i := 0)
      rw [h1, hdiv, h2]
    rw [hR]
  · have hlt : k < n := Nat.lt_of_not_le hk
    rw [decide_eq_false hk, Bool.false_and, Bool.false_or]
    have hR : (m * 2 ^ n + b).testBit k = b.testBit k := by
      have hmod : (m * 2 ^ n + b) % 2 ^ n = b := by
        rw [Nat.add_comm, Nat.mul_comm m (2 ^ n), Nat.add_mul_mod_self_left,
          Nat.mod_eq_of_lt hb]
      have h := Nat.testBit_mod_two_pow (m * 2 ^ n + b) n k
      rw [hmod, decide_eq_true hlt, Bool.true_and] at h
      exact h.symm
    rw [hR]

/-- A word shifted by six is a multiple of sixty-four. -/
theorem shiftLeft_six_toNat (z : BitVec 32) :
    (z <<< 6).toNat = (z.toNat * 64) % 2 ^ 32 := by
  rw [show (64 : Nat) = 2 ^ 6 from by decide]
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]

theorem shiftLeft_six_mod (z : BitVec 32) : (z <<< 6).toNat % 64 = 0 := by
  rw [shiftLeft_six_toNat, show (64 : Nat) = 2 ^ 6 from by decide,
    show (2 : Nat) ^ 32 = 2 ^ 6 * 2 ^ 26 from by decide,
    show (2 : Nat) ^ 6 * 2 ^ 26 = 2 ^ 26 * 2 ^ 6 from by rw [Nat.mul_comm]]
  rw [Nat.mul_mod_mul_right, Nat.mul_mod_left]

/-- **(base ||| lane) is base + lane** at a base that is a multiple of sixty-four
and a lane below sixty-four: the inlined batch's store and the out-of-line batch's
agree exactly on the lanes the batch claims. -/
theorem bv32_or_lane_toNat {z c : BitVec 32} {lane : Nat} (hc : c.toNat = lane)
    (hl : lane < 64) :
    ((z <<< 6) ||| c).toNat = (z <<< 6).toNat + lane := by
  rw [BitVec.toNat_or, hc]
  obtain ⟨m, hm⟩ : ∃ m, (z <<< 6).toNat = m * 64 := ⟨(z <<< 6).toNat / 64, by
    have := shiftLeft_six_mod z
    omega⟩
  have hl' : lane < 2 ^ 6 := by
    have h64 : (2 : Nat) ^ 6 = 64 := by decide
    omega
  rw [hm, show m * 64 = m * 2 ^ 6 from by rw [show (64 : Nat) = 2 ^ 6 from by decide]]
  exact nat_lor_mul_two_pow_add hl'

/-! ### `xl_lanes.exit`

Eleven instruction lines and a `condbr`: the exit word's outgoing carry, the
position word the batch and the emitter read, the position base, and the branch to
the emitter's exit or to the first batch. -/

def lstExitIncoming : List (String × Operand) :=
  [("if.end.i", .reg "%or13.i"), ("do.body.i", .reg "%e.1.i")]

theorem lstLanesExit_instrs :
    lstLanesExit.instrs =
      [ .phi "%e.2.i" (.int 64) lstExitIncoming,
        .binop "%shr.i" .lshr 64 (.reg "%bs") (.imm (.int 64 (BitVec.ofInt 64 63))),
        .store (.int 64) (.reg "%shr.i") (.reg "%carry"),
        .binop "%shr2757.i" .and 64 (.reg "%e.2.i") (.reg "%bs"),
        .binop "%and29.i" .lshr 64 (.reg "%shr2757.i")
          (.imm (.int 64 (BitVec.ofInt 64 63))),
        .store (.int 64) (.reg "%and29.i") (.reg "%arrayidx1"),
        .binop "%or30.i" .or 64 (.reg "%e.2.i") (.reg "%ctl"),
        .binop "%and31.i" .and 64 (.reg "%or30.i") (.reg "%im"),
        .trunc "%blk0.tr" 64 32 (.reg "%blk0"),
        .binop "%conv" .shl 32 (.reg "%blk0.tr") (.imm (.int 32 (BitVec.ofInt 32 6))),
        .icmp "%tobool.not.i3" .eq 64 (.reg "%and31.i")
          (.imm (.int 64 (BitVec.ofInt 64 0)))] := by decide

theorem lstLanesExit_term :
    lstLanesExit.term = .condbr (.reg "%tobool.not.i3") "xl_emit.exit" "if.end.i4" := by
  decide

/-- The two carry stores the exit block makes, in order. -/
def lxMem1 (mem : Mem) (bs : BitVec 64) (carry : Nat) : Mem :=
  writeBytes mem carry (natToBytes (bs >>> 63).toNat 8)

def lxMem2 (mem : Mem) (bs w : BitVec 64) (carry : Nat) : Mem :=
  writeBytes (lxMem1 mem bs carry) (carry + 8) (natToBytes ((w &&& bs) >>> 63).toNat 8)

def lx1 (env : Env) (w : BitVec 64) : Env :=
  ("%e.2.i", .int 64 w) :: env

def lx2 (env : Env) (bs w : BitVec 64) : Env :=
  ("%shr.i", .int 64 (bs >>> 63)) :: lx1 env w

def lx3 (env : Env) (bs w : BitVec 64) : Env :=
  ("%shr2757.i", .int 64 (w &&& bs)) :: lx2 env bs w

def lx4 (env : Env) (bs w : BitVec 64) : Env :=
  ("%and29.i", .int 64 ((w &&& bs) >>> 63)) :: lx3 env bs w

def lx5 (env : Env) (bs ctl w : BitVec 64) : Env :=
  ("%or30.i", .int 64 (w ||| ctl)) :: lx4 env bs w

/-- The word the batch and the emitter read. -/
def lxWord (ctl im w : BitVec 64) : BitVec 64 := (w ||| ctl) &&& im

/-- The block the exit test leaves for: the emitter's exit at an empty position
word, the first batch otherwise. -/
def lxNext (ctl im w : BitVec 64) : String :=
  if lxWord ctl im w = 0 then "xl_emit.exit" else "if.end.i4"

/-- The position base, as the exit block truncates and shifts it. -/
def lxBase (blk0 : BitVec 64) : BitVec 32 :=
  (BitVec.ofNat 32 (blk0.toNat % 2 ^ 32)) <<< 6

def lx6 (env : Env) (bs ctl im w : BitVec 64) : Env :=
  ("%and31.i", .int 64 (lxWord ctl im w)) :: lx5 env bs ctl w

def lx7 (env : Env) (bs ctl im w blk0 : BitVec 64) : Env :=
  ("%blk0.tr", .int 32 (BitVec.ofNat 32 (blk0.toNat % 2 ^ 32))) :: lx6 env bs ctl im w

def lx8 (env : Env) (bs ctl im w blk0 : BitVec 64) : Env :=
  ("%conv", .int 32 (lxBase blk0)) :: lx7 env bs ctl im w blk0

def lx9 (env : Env) (bs ctl im w blk0 : BitVec 64) : Env :=
  ("%tobool.not.i3", .int 1 (evalICmp .eq (lxWord ctl im w) (BitVec.ofInt 64 0))) ::
    lx8 env bs ctl im w blk0

macro "lx_simp" : tactic => `(tactic|
  (simp only [lx9, lx8, lx7, lx6, lx5, lx4, lx3, lx2, lx1, lxWord, lxBase,
    List.cons_append]))

macro "lx_lk" : tactic => `(tactic|
  (first
   | assumption
   | (repeat rw [lookupName_cons_ne _ _ (by decide)]
      try (first
        | rw [lookupName_cons_self]
        | rfl
        | assumption))))

/-- The exit block's straight-line run: the two carry stores, the position word and
the position base, at the environment `lx9` and the memory `lxMem2`. -/
theorem lstLanesExit_denote (env : Env) (s : State) (bs ctl im blk0 w : BitVec 64)
    (carry : Nat) (p : String) (op : Operand)
    (hpre : (withEnv env s).pre = some p) (hinc : phiIncoming p lstExitIncoming = some op)
    (hop : evalOperand (withEnv env s) op = some (.int 64 w))
    (hbs : lookupName env "%bs" = some (.int 64 bs))
    (hctl : lookupName env "%ctl" = some (.int 64 ctl))
    (him : lookupName env "%im" = some (.int 64 im))
    (hblk : lookupName env "%blk0" = some (.int 64 blk0))
    (hcarry : lookupName env "%carry" = some (.ptr carry))
    (harr : lookupName env "%arrayidx1" = some (.ptr (carry + 8))) :
    denoteCode escapeCalls lstLanesExit.instrs (withEnv env s) =
      some (withEnv (lx9 env bs ctl im w blk0)
        { s with mem := lxMem2 s.mem bs w carry }) := by
  rw [lstLanesExit_instrs]
  rw [denoteCode_cons_of _ _ _ _ _ (evalInstr_phi hpre hinc hop)]
  rw [show (withEnv env s).bind "%e.2.i" (.int 64 w) = withEnv (lx1 env w) s from rfl]
  rw [denoteCode_cons_of _ _ _ _ _ (b_lshr64_63 _ s "%shr.i" "%bs" bs (by lx_simp; lx_lk))]
  rw [show withEnv (("%shr.i", .int 64 (bs >>> 63)) :: lx1 env w) s =
    withEnv (lx2 env bs w) s from rfl]
  rw [denoteCode_cons_of _ _ _ _ _ (b_store64 _ s "%shr.i" "%carry" (bs >>> 63) carry
    (by lx_simp; lx_lk) (by lx_simp; lx_lk))]
  rw [show writeBytes s.mem carry (natToBytes (bs >>> 63).toNat 8) = lxMem1 s.mem bs carry
    from rfl]
  rw [denoteCode_cons_of _ _ _ _ _
    (b_and64 _ { s with mem := lxMem1 s.mem bs carry } "%shr2757.i" "%e.2.i" "%bs" w bs
      (by lx_simp; lx_lk) (by lx_simp; lx_lk))]
  rw [show withEnv (("%shr2757.i", .int 64 (w &&& bs)) :: lx2 env bs w)
      { s with mem := lxMem1 s.mem bs carry } =
    withEnv (lx3 env bs w) { s with mem := lxMem1 s.mem bs carry } from rfl]
  rw [denoteCode_cons_of _ _ _ _ _
    (b_lshr64_63 _ { s with mem := lxMem1 s.mem bs carry } "%and29.i" "%shr2757.i" (w &&& bs)
      (by lx_simp; lx_lk))]
  rw [show withEnv (("%and29.i", .int 64 ((w &&& bs) >>> 63)) :: lx3 env bs w)
      { s with mem := lxMem1 s.mem bs carry } =
    withEnv (lx4 env bs w) { s with mem := lxMem1 s.mem bs carry } from rfl]
  rw [denoteCode_cons_of _ _ _ _ _
    (b_store64_mem (lx4 env bs w) s (lxMem1 s.mem bs carry)
      "%and29.i" "%arrayidx1" ((w &&& bs) >>> 63) (carry + 8)
      (by lx_simp; lx_lk) (by lx_simp; lx_lk))]
  rw [show (withEnv (lx4 env bs w) { s with
      mem := writeBytes (lxMem1 s.mem bs carry) (carry + 8)
        (natToBytes ((w &&& bs) >>> 63).toNat 8) }) =
    withEnv (lx4 env bs w) { s with mem := lxMem2 s.mem bs w carry } from rfl]
  rw [denoteCode_cons_of _ _ _ _ _
    (b_or64 _ { s with mem := lxMem2 s.mem bs w carry } "%or30.i" "%e.2.i" "%ctl" w ctl
      (by lx_simp; lx_lk) (by lx_simp; lx_lk))]
  rw [show withEnv (("%or30.i", .int 64 (w ||| ctl)) :: lx4 env bs w)
      { s with mem := lxMem2 s.mem bs w carry } =
    withEnv (lx5 env bs ctl w) { s with mem := lxMem2 s.mem bs w carry } from rfl]
  rw [denoteCode_cons_of _ _ _ _ _
    (b_and64 _ { s with mem := lxMem2 s.mem bs w carry } "%and31.i" "%or30.i" "%im"
      (w ||| ctl) im (by lx_simp; lx_lk) (by lx_simp; lx_lk))]
  rw [show withEnv (("%and31.i", .int 64 ((w ||| ctl) &&& im)) :: lx5 env bs ctl w)
      { s with mem := lxMem2 s.mem bs w carry } =
    withEnv (lx6 env bs ctl im w) { s with mem := lxMem2 s.mem bs w carry } from rfl]
  rw [denoteCode_cons_of _ _ _ _ _
    (b_trunc _ { s with mem := lxMem2 s.mem bs w carry } "%blk0.tr" "%blk0" blk0
      (by lx_simp; lx_lk))]
  rw [show withEnv (("%blk0.tr", .int 32 (BitVec.ofNat 32 (blk0.toNat % 2 ^ 32))) ::
      lx6 env bs ctl im w) { s with mem := lxMem2 s.mem bs w carry } =
    withEnv (lx7 env bs ctl im w blk0) { s with mem := lxMem2 s.mem bs w carry } from rfl]
  rw [denoteCode_cons_of _ _ _ _ _
    (b_shl32_six _ { s with mem := lxMem2 s.mem bs w carry } "%conv" "%blk0.tr"
      (BitVec.ofNat 32 (blk0.toNat % 2 ^ 32)) (by lx_simp; lx_lk))]
  rw [show withEnv (("%conv", .int 32 ((BitVec.ofNat 32 (blk0.toNat % 2 ^ 32)) <<< 6)) ::
      lx7 env bs ctl im w blk0) { s with mem := lxMem2 s.mem bs w carry } =
    withEnv (lx8 env bs ctl im w blk0) { s with mem := lxMem2 s.mem bs w carry } from rfl]
  rw [denoteCode_cons_of _ _ _ _ _
    (b_icmp_eq64_imm _ { s with mem := lxMem2 s.mem bs w carry } "%tobool.not.i3"
      "%and31.i" ((w ||| ctl) &&& im) (BitVec.ofInt 64 0) (by lx_simp; lx_lk))]
  rw [show withEnv (("%tobool.not.i3",
      .int 1 (evalICmp .eq ((w ||| ctl) &&& im) (BitVec.ofInt 64 0))) ::
      lx8 env bs ctl im w blk0) { s with mem := lxMem2 s.mem bs w carry } =
    withEnv (lx9 env bs ctl im w blk0) { s with mem := lxMem2 s.mem bs w carry } from rfl]
  rfl

/-- **`xl_lanes.exit`'s one control step.**  The block stores the outgoing carry,
forms the position word and the position base, and jumps to the emitter's exit when
the word is empty and to the first batch when it is not.

The conclusion carries the cells the batch blocks read — the word, the base, the
stream, the count's slot and the carry's second slot — and the two stores' memory. -/
theorem lstLanesExit_step (env : Env) (s : State) (bs ctl im blk0 w : BitVec 64)
    (carry : Nat) (p : String) (op : Operand)
    (hpc : (withEnv env s).pc = "xl_lanes.exit")
    (hpre : (withEnv env s).pre = some p) (hinc : phiIncoming p lstExitIncoming = some op)
    (hop : evalOperand (withEnv env s) op = some (.int 64 w))
    (hbs : lookupName env "%bs" = some (.int 64 bs))
    (hctl : lookupName env "%ctl" = some (.int 64 ctl))
    (him : lookupName env "%im" = some (.int 64 im))
    (hblk : lookupName env "%blk0" = some (.int 64 blk0))
    (hcarry : lookupName env "%carry" = some (.ptr carry))
    (harr : lookupName env "%arrayidx1" = some (.ptr (carry + 8))) :
    step escapeCalls escapeListFunction (withEnv env s) =
      .jump (withEnv (lx9 env bs ctl im w blk0)
        { s with mem := lxMem2 s.mem bs w carry,
                 pc := lxNext ctl im w,
                 pre := some "xl_lanes.exit" }) ∧
      lookupName (lx9 env bs ctl im w blk0) "%and31.i" = some (.int 64 (lxWord ctl im w)) ∧
      lookupName (lx9 env bs ctl im w blk0) "%conv" = some (.int 32 (lxBase blk0)) ∧
      lookupName (lx9 env bs ctl im w blk0) "%xp" = lookupName env "%xp" ∧
      lookupName (lx9 env bs ctl im w blk0) "%xn" = lookupName env "%xn" ∧
      lookupName (lx9 env bs ctl im w blk0) "%carry" = lookupName env "%carry" ∧
      lookupName (lx9 env bs ctl im w blk0) "%arrayidx1" = lookupName env "%arrayidx1" := by
  have hbody := lstLanesExit_denote env s bs ctl im blk0 w carry p op hpre hinc hop
    hbs hctl him hblk hcarry harr
  have hstep : step escapeCalls escapeListFunction (withEnv env s) =
      execTerm (withEnv (lx9 env bs ctl im w blk0) { s with mem := lxMem2 s.mem bs w carry })
        lstLanesExit.term :=
    step_of (withEnv env s) "xl_lanes.exit" lstLanesExit _ hpc findBlock_lanesExit hbody
  have hval : evalOperand (withEnv (lx9 env bs ctl im w blk0)
      { s with mem := lxMem2 s.mem bs w carry }) (.reg "%tobool.not.i3") =
      some (.int 1 (evalICmp .eq (lxWord ctl im w) (BitVec.ofInt 64 0))) := by
    show lookupName (lx9 env bs ctl im w blk0) "%tobool.not.i3" = _
    lx_simp; lx_lk
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hstep, lstLanesExit_term]
    have hpc' : s.pc = "xl_lanes.exit" := hpc
    by_cases hz : lxWord ctl im w = 0
    · have hnext : lxNext ctl im w = "xl_emit.exit" := by
        unfold lxNext; rw [ite_eq_left hz]
      rw [execTerm_condbr_one _ _ _ _ _ hval ((evalICmp_eq_one_iff _ _).mpr hz), hnext]
      simp [withEnv, hpc']
    · have h0 : evalICmp .eq (lxWord ctl im w) (BitVec.ofInt 64 0) = (0 : BitVec 1) :=
        (evalICmp_eq_zero_iff _ _).mpr hz
      have hnext : lxNext ctl im w = "if.end.i4" := by
        unfold lxNext; rw [ite_eq_right hz]
      rw [execTerm_condbr_zero _ _ _ _ _ hval h0, hnext]
      simp [withEnv, hpc']
  all_goals lx_simp
  all_goals lx_lk

/-! ### `for.body.preheader.i.i`, `while.body.preheader.i.i` and `xl_emit.exit`

The three blocks between the lanes loop and the writer.  The preheader clears eight
lanes of the position word at the immediate the fixture carries — `x + -1` then `x`
and-ed, `clearStep` at `BitVec.ofInt 64 (-1)` rather than at the notation's `-1` — and
`cSt8_eq_clearLow` bridges its word to the one the batch arithmetic is stated at.
-/

theorem lstForPre_instrs :
    lstForPre.instrs =
      [        .binop "%sub.i.i" .add 64 (.reg "%and31.i") (.imm (.int 64 (BitVec.ofInt 64 (-1)))),
        .binop "%and.i.i" .and 64 (.reg "%sub.i.i") (.reg "%and31.i"),
        .binop "%sub.1.i.i" .add 64 (.reg "%and.i.i") (.imm (.int 64 (BitVec.ofInt 64 (-1)))),
        .binop "%and.1.i.i" .and 64 (.reg "%sub.1.i.i") (.reg "%and.i.i"),
        .binop "%sub.2.i.i" .add 64 (.reg "%and.1.i.i") (.imm (.int 64 (BitVec.ofInt 64 (-1)))),
        .binop "%and.2.i.i" .and 64 (.reg "%sub.2.i.i") (.reg "%and.1.i.i"),
        .binop "%sub.3.i.i" .add 64 (.reg "%and.2.i.i") (.imm (.int 64 (BitVec.ofInt 64 (-1)))),
        .binop "%and.3.i.i" .and 64 (.reg "%sub.3.i.i") (.reg "%and.2.i.i"),
        .binop "%sub.4.i.i" .add 64 (.reg "%and.3.i.i") (.imm (.int 64 (BitVec.ofInt 64 (-1)))),
        .binop "%and.4.i.i" .and 64 (.reg "%sub.4.i.i") (.reg "%and.3.i.i"),
        .binop "%sub.5.i.i" .add 64 (.reg "%and.4.i.i") (.imm (.int 64 (BitVec.ofInt 64 (-1)))),
        .binop "%and.5.i.i" .and 64 (.reg "%sub.5.i.i") (.reg "%and.4.i.i"),
        .binop "%sub.6.i.i" .add 64 (.reg "%and.5.i.i") (.imm (.int 64 (BitVec.ofInt 64 (-1)))),
        .binop "%and.6.i.i" .and 64 (.reg "%sub.6.i.i") (.reg "%and.5.i.i"),
        .binop "%sub.7.i.i" .add 64 (.reg "%and.6.i.i") (.imm (.int 64 (BitVec.ofInt 64 (-1)))),
        .binop "%and.7.i.i" .and 64 (.reg "%sub.7.i.i") (.reg "%and.6.i.i"),
        .icmp "%tobool6.not42.i.i" .eq 64 (.reg "%and.7.i.i")
          (.imm (.int 64 (BitVec.ofInt 64 0)))] := by decide

theorem lstForPre_term :
    lstForPre.term =
      .condbr (.reg "%tobool6.not42.i.i") "xl_emit.exit" "while.body.preheader.i.i" := by
  decide

/-- The clear step at the immediate the block's instructions carry. -/
def cSt (x : BitVec 64) : BitVec 64 := (x + BitVec.ofInt 64 (-1)) &&& x

/-- Eight clear steps, as the preheader applies them. -/
def cSt8 (x : BitVec 64) : BitVec 64 :=
  cSt (cSt (cSt (cSt (cSt (cSt (cSt (cSt x)))))))

theorem neg_one_eq_ofInt : (-1 : BitVec 64) = BitVec.ofInt 64 (-1) := by decide

theorem cSt_eq_clearStep (x : BitVec 64) : cSt x = clearStep x := by
  unfold cSt clearStep
  rw [neg_one_eq_ofInt]

/-- Eight of the block's steps are `clearLow`'s eight. -/
theorem cSt8_eq_clearLow (esc : BitVec 64) : cSt8 esc = clearLow esc 8 := by
  simp [cSt8, cSt, clearLow, clearStep]

/-- The block the preheader leaves for: the emitter's exit when the eight clears
have taken the whole word, the batch loop otherwise. -/
def fpNext (esc : BitVec 64) : String :=
  if clearLow esc 8 = 0 then "xl_emit.exit" else "while.body.preheader.i.i"


/-- The preheader's environment, one alias per instruction. -/
def fp1 (env : Env) (esc : BitVec 64) : Env :=
  ("%sub.i.i", .int 64 (esc + BitVec.ofInt 64 (-1))) :: env

def fp2 (env : Env) (esc : BitVec 64) : Env :=
  ("%and.i.i", .int 64 ((cSt esc))) :: fp1 env esc

def fp3 (env : Env) (esc : BitVec 64) : Env :=
  ("%sub.1.i.i", .int 64 ((cSt esc) + BitVec.ofInt 64 (-1))) :: fp2 env esc

def fp4 (env : Env) (esc : BitVec 64) : Env :=
  ("%and.1.i.i", .int 64 ((cSt (cSt esc)))) :: fp3 env esc

def fp5 (env : Env) (esc : BitVec 64) : Env :=
  ("%sub.2.i.i", .int 64 ((cSt (cSt esc)) + BitVec.ofInt 64 (-1))) :: fp4 env esc

def fp6 (env : Env) (esc : BitVec 64) : Env :=
  ("%and.2.i.i", .int 64 ((cSt (cSt (cSt esc))))) :: fp5 env esc

def fp7 (env : Env) (esc : BitVec 64) : Env :=
  ("%sub.3.i.i", .int 64 ((cSt (cSt (cSt esc))) + BitVec.ofInt 64 (-1))) :: fp6 env esc

def fp8 (env : Env) (esc : BitVec 64) : Env :=
  ("%and.3.i.i", .int 64 ((cSt (cSt (cSt (cSt esc)))))) :: fp7 env esc

def fp9 (env : Env) (esc : BitVec 64) : Env :=
  ("%sub.4.i.i", .int 64 ((cSt (cSt (cSt (cSt esc)))) + BitVec.ofInt 64 (-1))) :: fp8 env esc

def fp10 (env : Env) (esc : BitVec 64) : Env :=
  ("%and.4.i.i", .int 64 ((cSt (cSt (cSt (cSt (cSt esc))))))) :: fp9 env esc

def fp11 (env : Env) (esc : BitVec 64) : Env :=
  ("%sub.5.i.i", .int 64 ((cSt (cSt (cSt (cSt (cSt esc))))) + BitVec.ofInt 64 (-1))) :: fp10 env esc

def fp12 (env : Env) (esc : BitVec 64) : Env :=
  ("%and.5.i.i", .int 64 ((cSt (cSt (cSt (cSt (cSt (cSt esc)))))))) :: fp11 env esc

def fp13 (env : Env) (esc : BitVec 64) : Env :=
  ("%sub.6.i.i", .int 64 ((cSt (cSt (cSt (cSt (cSt (cSt esc)))))) + BitVec.ofInt 64 (-1))) :: fp12 env esc

def fp14 (env : Env) (esc : BitVec 64) : Env :=
  ("%and.6.i.i", .int 64 ((cSt (cSt (cSt (cSt (cSt (cSt (cSt esc))))))))) :: fp13 env esc

def fp15 (env : Env) (esc : BitVec 64) : Env :=
  ("%sub.7.i.i", .int 64 ((cSt (cSt (cSt (cSt (cSt (cSt (cSt esc))))))) + BitVec.ofInt 64 (-1))) :: fp14 env esc

def fp16 (env : Env) (esc : BitVec 64) : Env :=
  ("%and.7.i.i", .int 64 ((cSt (cSt (cSt (cSt (cSt (cSt (cSt (cSt esc)))))))))) :: fp15 env esc

def fp17 (env : Env) (esc : BitVec 64) : Env :=
  ("%tobool6.not42.i.i", .int 1 (evalICmp .eq (cSt8 esc) (BitVec.ofInt 64 0))) ::
    fp16 env esc

/-- The state the preheader leaves. -/
def fpSucc (env : Env) (s : State) (esc : BitVec 64) : State :=
  { s with env := fp17 env esc, pc := fpNext esc,
           pre := some "for.body.preheader.i.i" }

macro "fp_simp" : tactic => `(tactic|
  (try (simp only [fp17, fp16, fp15, fp14, fp13, fp12, fp11, fp10, fp9, fp8, fp7, fp6, fp5, fp4, fp3, fp2, fp1, cSt8, cSt, List.cons_append])))

macro "fp_lk" : tactic => `(tactic|
  (first
   | assumption
   | (repeat rw [lookupName_cons_ne _ _ (by decide)]
      try (first
        | rw [lookupName_cons_self]
        | rfl
        | assumption))))

/-- The preheader's straight-line run: eight clears of the position word. -/
theorem lstForPre_denote (env : Env) (s : State) (esc : BitVec 64)
    (hesc : lookupName env "%and31.i" = some (.int 64 esc)) :
    denoteCode escapeCalls lstForPre.instrs (withEnv env s) =
      some (withEnv (fp17 env esc) s) := by
  rw [lstForPre_instrs]
  rw [denoteCode_cons_of _ _ _ _ _ (b_add64_imm _ s "%sub.i.i" "%and31.i"
    (esc) (BitVec.ofInt 64 (-1)) (by fp_simp; fp_lk))]
  rw [denoteCode_cons_of _ _ _ _ _ (b_and64 _ s "%and.i.i" "%sub.i.i" "%and31.i"
    (esc + BitVec.ofInt 64 (-1)) (esc)
    (by fp_simp; fp_lk) (by fp_simp; fp_lk))]
  rw [denoteCode_cons_of _ _ _ _ _ (b_add64_imm _ s "%sub.1.i.i" "%and.i.i"
    ((cSt esc)) (BitVec.ofInt 64 (-1)) (by fp_simp; fp_lk))]
  rw [denoteCode_cons_of _ _ _ _ _ (b_and64 _ s "%and.1.i.i" "%sub.1.i.i" "%and.i.i"
    ((cSt esc) + BitVec.ofInt 64 (-1)) ((cSt esc))
    (by fp_simp; fp_lk) (by fp_simp; fp_lk))]
  rw [denoteCode_cons_of _ _ _ _ _ (b_add64_imm _ s "%sub.2.i.i" "%and.1.i.i"
    ((cSt (cSt esc))) (BitVec.ofInt 64 (-1)) (by fp_simp; fp_lk))]
  rw [denoteCode_cons_of _ _ _ _ _ (b_and64 _ s "%and.2.i.i" "%sub.2.i.i" "%and.1.i.i"
    ((cSt (cSt esc)) + BitVec.ofInt 64 (-1)) ((cSt (cSt esc)))
    (by fp_simp; fp_lk) (by fp_simp; fp_lk))]
  rw [denoteCode_cons_of _ _ _ _ _ (b_add64_imm _ s "%sub.3.i.i" "%and.2.i.i"
    ((cSt (cSt (cSt esc)))) (BitVec.ofInt 64 (-1)) (by fp_simp; fp_lk))]
  rw [denoteCode_cons_of _ _ _ _ _ (b_and64 _ s "%and.3.i.i" "%sub.3.i.i" "%and.2.i.i"
    ((cSt (cSt (cSt esc))) + BitVec.ofInt 64 (-1)) ((cSt (cSt (cSt esc))))
    (by fp_simp; fp_lk) (by fp_simp; fp_lk))]
  rw [denoteCode_cons_of _ _ _ _ _ (b_add64_imm _ s "%sub.4.i.i" "%and.3.i.i"
    ((cSt (cSt (cSt (cSt esc))))) (BitVec.ofInt 64 (-1)) (by fp_simp; fp_lk))]
  rw [denoteCode_cons_of _ _ _ _ _ (b_and64 _ s "%and.4.i.i" "%sub.4.i.i" "%and.3.i.i"
    ((cSt (cSt (cSt (cSt esc)))) + BitVec.ofInt 64 (-1)) ((cSt (cSt (cSt (cSt esc)))))
    (by fp_simp; fp_lk) (by fp_simp; fp_lk))]
  rw [denoteCode_cons_of _ _ _ _ _ (b_add64_imm _ s "%sub.5.i.i" "%and.4.i.i"
    ((cSt (cSt (cSt (cSt (cSt esc)))))) (BitVec.ofInt 64 (-1)) (by fp_simp; fp_lk))]
  rw [denoteCode_cons_of _ _ _ _ _ (b_and64 _ s "%and.5.i.i" "%sub.5.i.i" "%and.4.i.i"
    ((cSt (cSt (cSt (cSt (cSt esc))))) + BitVec.ofInt 64 (-1)) ((cSt (cSt (cSt (cSt (cSt esc))))))
    (by fp_simp; fp_lk) (by fp_simp; fp_lk))]
  rw [denoteCode_cons_of _ _ _ _ _ (b_add64_imm _ s "%sub.6.i.i" "%and.5.i.i"
    ((cSt (cSt (cSt (cSt (cSt (cSt esc))))))) (BitVec.ofInt 64 (-1)) (by fp_simp; fp_lk))]
  rw [denoteCode_cons_of _ _ _ _ _ (b_and64 _ s "%and.6.i.i" "%sub.6.i.i" "%and.5.i.i"
    ((cSt (cSt (cSt (cSt (cSt (cSt esc)))))) + BitVec.ofInt 64 (-1)) ((cSt (cSt (cSt (cSt (cSt (cSt esc)))))))
    (by fp_simp; fp_lk) (by fp_simp; fp_lk))]
  rw [denoteCode_cons_of _ _ _ _ _ (b_add64_imm _ s "%sub.7.i.i" "%and.6.i.i"
    ((cSt (cSt (cSt (cSt (cSt (cSt (cSt esc)))))))) (BitVec.ofInt 64 (-1)) (by fp_simp; fp_lk))]
  rw [denoteCode_cons_of _ _ _ _ _ (b_and64 _ s "%and.7.i.i" "%sub.7.i.i" "%and.6.i.i"
    ((cSt (cSt (cSt (cSt (cSt (cSt (cSt esc))))))) + BitVec.ofInt 64 (-1)) ((cSt (cSt (cSt (cSt (cSt (cSt (cSt esc))))))))
    (by fp_simp; fp_lk) (by fp_simp; fp_lk))]
  rw [denoteCode_cons_of _ _ _ _ _ (b_icmp_eq64_imm _ s "%tobool6.not42.i.i" "%and.7.i.i"
    (cSt8 esc) (BitVec.ofInt 64 0) (by fp_simp; fp_lk))]
  rfl

/-- **`for.body.preheader.i.i`'s one control step.** -/
theorem lstForPre_step (env : Env) (s : State) (esc : BitVec 64)
    (hpc : (withEnv env s).pc = "for.body.preheader.i.i")
    (hesc : lookupName env "%and31.i" = some (.int 64 esc)) :
    step escapeCalls escapeListFunction (withEnv env s) =
      .jump (fpSucc env s esc) := by
  have hbody := lstForPre_denote env s esc hesc
  have hstep : step escapeCalls escapeListFunction (withEnv env s) =
      execTerm (withEnv (fp17 env esc) s) lstForPre.term :=
    step_of (withEnv env s) "for.body.preheader.i.i" lstForPre _ hpc findBlock_forPre hbody
  have hval : evalOperand (withEnv (fp17 env esc) s) (.reg "%tobool6.not42.i.i") =
      some (.int 1 (evalICmp .eq (cSt8 esc) (BitVec.ofInt 64 0))) := by
    show lookupName (fp17 env esc) "%tobool6.not42.i.i" = _
    fp_simp; fp_lk
  have hpc' : s.pc = "for.body.preheader.i.i" := hpc
  rw [hstep, lstForPre_term]
  have hword : cSt8 esc = clearLow esc 8 := cSt8_eq_clearLow esc
  by_cases hz : clearLow esc 8 = 0
  · have hz' : cSt8 esc = 0 := by rw [hword]; exact hz
    have hnext : fpNext esc = "xl_emit.exit" := by
      unfold fpNext; rw [ite_eq_left hz]
    rw [execTerm_condbr_one _ _ _ _ _ hval ((evalICmp_eq_one_iff _ _).mpr hz')]
    simp only [fpSucc]
    rw [hnext]
    simp [withEnv, hpc']
  · have hz' : cSt8 esc ≠ 0 := by rw [hword]; exact hz
    have h0 : evalICmp .eq (cSt8 esc) (BitVec.ofInt 64 0) = (0 : BitVec 1) :=
      (evalICmp_eq_zero_iff _ _).mpr hz'
    have hnext : fpNext esc = "while.body.preheader.i.i" := by
      unfold fpNext; rw [ite_eq_right hz]
    rw [execTerm_condbr_zero _ _ _ _ _ hval h0]
    simp only [fpSucc]
    rw [hnext]
    simp [withEnv, hpc']

/-! ### `while.body.preheader.i.i` -/

theorem lstWhilePre_instrs :
    lstWhilePre.instrs =
      [ .gep "%add.ptr5.i.i" (.int 8) (.reg "%add.ptr.i.i")
          (.imm (.int 64 (BitVec.ofInt 64 32)))] := by decide

theorem lstWhilePre_term : lstWhilePre.term = .br "while.body.i.i" := by decide

/-- The batch loop's first cursor: the first batch's start plus its eight entries. -/
def wpEnv (env : Env) (o : Nat) : Env :=
  ("%add.ptr5.i.i", .ptr (o + 32)) :: env

/-- The state the batch preheader leaves. -/
def wpSucc (env : Env) (s : State) (o : Nat) : State :=
  { s with env := wpEnv env o, pc := "while.body.i.i",
           pre := some "while.body.preheader.i.i" }

/-- **`while.body.preheader.i.i`'s one control step**: the cursor the writer starts
from, thirty-two bytes past the first batch's base. -/
theorem lstWhilePre_step (env : Env) (s : State) (o : Nat)
    (hpc : (withEnv env s).pc = "while.body.preheader.i.i")
    (ho : lookupName env "%add.ptr.i.i" = some (.ptr o)) :
    step escapeCalls escapeListFunction (withEnv env s) =
      .jump (wpSucc env s o) := by
  have hbody : denoteCode escapeCalls lstWhilePre.instrs (withEnv env s) =
      some (withEnv (wpEnv env o) s) := by
    rw [lstWhilePre_instrs]
    rw [denoteCode_cons_of _ _ _ _ _ (b_gep8_imm _ s "%add.ptr5.i.i" "%add.ptr.i.i" o 32
      (BitVec.ofInt 64 32) (by b_lk ho) (by decide) (by decide))]
    rfl
  have hstep : step escapeCalls escapeListFunction (withEnv env s) =
      execTerm (withEnv (wpEnv env o) s) lstWhilePre.term :=
    step_of (withEnv env s) "while.body.preheader.i.i" lstWhilePre _ hpc findBlock_whilePre hbody
  have hpc' : s.pc = "while.body.preheader.i.i" := hpc
  rw [hstep, lstWhilePre_term]
  simp only [execTerm, wpSucc, withEnv, hpc']

/-! ### `xl_emit.exit` -/

theorem lstEmitExit_instrs : lstEmitExit.instrs = [] := by decide

theorem lstEmitExit_term : lstEmitExit.term = .ret (.void) none := by decide

/-- **`xl_emit.exit`'s one step**: the entry point's `void` return. -/
theorem lstEmitExit_step (env : Env) (s : State)
    (hpc : (withEnv env s).pc = "xl_emit.exit") :
    step escapeCalls escapeListFunction (withEnv env s) = .ret none (withEnv env s) := by
  have hstep : step escapeCalls escapeListFunction (withEnv env s) =
      execTerm (withEnv env s) lstEmitExit.term :=
    step_of (withEnv env s) "xl_emit.exit" lstEmitExit _ hpc findBlock_emitExit (by rfl)
  rw [hstep, lstEmitExit_term]
  simp only [execTerm]


/-! ### Axiom footprints -/

/-- info: 'LeanLLVM.Vellum.cSt8_eq_clearLow' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms cSt8_eq_clearLow

/-- info: 'LeanLLVM.Vellum.cSt_eq_clearStep' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms cSt_eq_clearStep

/-- info: 'LeanLLVM.Vellum.lstForPre_denote' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms lstForPre_denote

/-- info: 'LeanLLVM.Vellum.lstForPre_step' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms lstForPre_step

/-- info: 'LeanLLVM.Vellum.lstWhilePre_step' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms lstWhilePre_step

/-- info: 'LeanLLVM.Vellum.lstEmitExit_step' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms lstEmitExit_step

/-! ### Axiom footprints -/

/-- info: 'LeanLLVM.Vellum.carry_words' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms carry_words

/-- info: 'LeanLLVM.Vellum.b_load64_nat' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms b_load64_nat

/-- info: 'LeanLLVM.Vellum.b_store64_mem' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms b_store64_mem

/-- info: 'LeanLLVM.Vellum.b_gep4_reg32' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms b_gep4_reg32

/-- info: 'LeanLLVM.Vellum.b_gep4_reg64' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms b_gep4_reg64

/-- info: 'LeanLLVM.Vellum.b_zext32_64' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms b_zext32_64

/-- info: 'LeanLLVM.Vellum.nat_lor_mul_two_pow_add' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms nat_lor_mul_two_pow_add

/-- info: 'LeanLLVM.Vellum.shiftLeft_six_toNat' depends on axioms: [propext] -/
#guard_msgs in
#print axioms shiftLeft_six_toNat

/-- info: 'LeanLLVM.Vellum.bv32_or_lane_toNat' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms bv32_or_lane_toNat

/-- info: 'LeanLLVM.Vellum.lstLanesExit_denote' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms lstLanesExit_denote

/-- info: 'LeanLLVM.Vellum.lstLanesExit_step' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms lstLanesExit_step

end LeanLLVM.Vellum
