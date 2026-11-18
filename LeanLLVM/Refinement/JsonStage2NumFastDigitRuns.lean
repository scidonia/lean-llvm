/-
`num_fast_el1`'s three digit runs, at the pinned body: the arms the scan's
`BoundLoop` instances take as parameters, discharged from the blocks' own
instruction lists, and the counters they carry.

`JsonStage2NumFastScan` fixes the integer run's shape at `land.lhs.true41` and
states its two arms as per-iteration facts; the fraction run at
`land.lhs.true119` and the exponent run at `land.lhs.true195` have the same
shape and no instance.  What kept the arms out of the tree was the pins: an arm
is a `runFuel` prefix over the run's four blocks, and the blocks' instruction
lists were only inline in `findBlock` equations.  `JsonStage2HelperIRNumFast`
now names all three runs' blocks (a regeneration of
`capture-stage2-helpers.sh --emit-pins`), and this module is the arms.

**The shape, once per run.**  Each run is a head that loads the byte at the
carried index and tests it against `'0' … '9'`, a body that guards the
accumulator's digit count, an `if.then` that accumulates, and an `if.end` that
increments the index and tests the index against the lexeme's length.  The
head has two predecessors — its preheader and the back edge — and the invariant
carries both edges' phi sources.  The exits are the head's own non-digit branch
and the `if.end`'s end-of-lexeme branch (one block for the integer run's
`if.end68`/`if.end230`, the fraction's `if.end144`/`if.end230`, and
`cleanup223.thread` for both of the exponent's).

**The counters.**  Each run's `Exit` carries the register facts it stops with:
the index it stopped at and the count it advanced to, `start + (stop - start)`.
The instance's `run_from` therefore hands back the counters with the exit, and
`*_counters` reads them.  The exponent run's carried register is its
accumulator rather than a count, and its `Exit` states the accumulator's *cell*
and not the fold's value: the accumulator is read at the merge by
`JsonStage2NumFastSeams.expExit_merge`, which takes the cell's reading as
`expAcc` of the exponent's digits as a hypothesis (`hacc`, since the exit state
is existential) and `expSelect_tie` turns it into `expVal`.  A run-internal
`fold` conjunct on `expRunInv` would state the same reading at the invariant;
nothing here claims it.

**The boundary.**  The runs' *starts* — the index after the sign, after the
`.`, after the `e` and its sign — are the inlined scan's dispatch, and they are
`JsonStage2NumFastStarts`': `intRun_start`, `fracRun_start` and `expRun_start`
each reach the run's head with this module's invariant at `c = 0` and the
counter the dispatch fixed.  What that module does not cover is named there —
the two eight-digit fast paths, and the exponent's marker nest that fixes
`%i.11`.  The counters are therefore stated at the body relative to the run's
start (`i0`, `d0`), and the model-facing corollaries in
`JsonStage2NumFastCounters` read them at the dispatch's start facts.  Nothing
here restates a block's text: every step rewrites with the pin's own
instruction-list equation.

The digit test is the emitted byte rule: `(b - 0x30) <u 10` at `i8`, which is
`IsDigitB b` (`isDigitB_ult`), so the head's branch is the scan's test rather
than a second reading of the byte.
-/
import LeanLLVM.Refinement.JsonStage2NumFastCalls
import LeanLLVM.Refinement.JsonScanLane
import LeanLLVM.Refinement.JsonStage2NumFastScan

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 1000000

namespace LeanLLVM.Refinement

open LeanLLVM
open LeanLLVM.Refinement.BlockEval
open LeanLLVM.JSON

-- The scan's region is call-free: every block between the dispatch and the run's
-- exit is arithmetic and loads, so the environment's answers cannot reach it.
-- The runs are therefore stated at an arbitrary `calls`, which is what lets a
-- caller append its own prefix — the fast paths answer `num_d8_el1` — to a run
-- proved once.
variable {calls : Calls}

/-! ### The digit test, as the emitted byte rule

The head's `%9 = add i8 %8, -48` followed by `icmp ult i8 %9, 10` is `IsDigitB`
on the loaded byte.  The two readings are the same function: `-48` is `0xd0` at
`i8`, and the sum's `Nat` reading is `b + 208` mod `256`, which lies in `[0, 9]`
exactly on `'0' … '9'`. -/

/-- The byte's value, as the load binds it. -/
theorem vByte_toNat (b : UInt8) : (JsonScanLane.vByte b).toNat = b.toNat := by
  simp [JsonScanLane.vByte]

theorem mod256_of_ge (b : Nat) (hb : b < 256) (h : 48 ≤ b) :
    (b + 208) % 256 = b - 48 := by
  have h1 : b + 208 = (b - 48) + 256 := by omega
  rw [h1, Nat.add_mod, show (256 : Nat) % 256 = 0 from rfl, Nat.add_zero, Nat.mod_mod]
  exact Nat.mod_eq_of_lt (by omega)

theorem mod256_of_lt (b : Nat) (hb : b < 48) : (b + 208) % 256 = b + 208 := by
  rw [Nat.mod_eq_of_lt (by omega)]

theorem bv_add_toNat (x y : BitVec 8) : (x + y).toNat = (x.toNat + y.toNat) % 256 :=
  BitVec.toNat_add x y

/-- **The emitted byte rule is the digit test.**  `%9 = %8 - 48` and
`icmp ult %9, 10` holds exactly when the byte is `'0' … '9'`. -/
theorem isDigitB_iff_ult (b : UInt8) :
    (JsonScanLane.vByte b + 0xd0#8).ult (0x0a#8) = true ↔ IsDigitB b = true := by
  unfold IsDigitB
  rw [Bool.and_eq_true, BitVec.ult_iff_toNat_lt]
  simp only [decide_eq_true_eq, UInt8.le_iff_toNat_le]
  have h10 : (0x0a#8 : BitVec 8).toNat = 10 := by decide
  have h208 : (0xd0#8 : BitVec 8).toNat = 208 := by decide
  have h30 : (0x30 : UInt8).toNat = 48 := by decide
  have h39 : (0x39 : UInt8).toNat = 57 := by decide
  rw [h10, bv_add_toNat, h208, vByte_toNat, h30, h39]
  constructor
  · intro h
    have hb := b.toNat_lt
    have hge : 48 ≤ b.toNat := by
      by_contra hlt
      have hmod := mod256_of_lt b.toNat (by omega)
      omega
    refine ⟨hge, ?_⟩
    have hmod := mod256_of_ge b.toNat hb hge
    omega
  · rintro ⟨h1, h2⟩
    have hb := b.toNat_lt
    have hmod := mod256_of_ge b.toNat hb h1
    omega

/-- The rule's `Bool` form: the comparison's result is `IsDigitB`. -/
theorem isDigitB_ult (b : UInt8) :
    (JsonScanLane.vByte b + 0xd0#8).ult (0x0a#8) = IsDigitB b := by
  apply Bool.eq_iff_iff.mpr
  exact isDigitB_iff_ult b

/-- The comparison's value, as `evalICmp` binds it. -/
theorem evalICmp_ult_digit (b : UInt8) :
    evalICmp .ult (JsonScanLane.vByte b + 0xd0#8) (0x0a#8)
      = BitVec.ofBool (IsDigitB b) := by
  unfold evalICmp
  exact congrArg BitVec.ofBool (isDigitB_ult b)

/-! ### The chain steps the runs need and the fragment names elsewhere

`mul i64` is `walkDenoteCode_mul_imm`'s shape at the generic layer; the digit
runs are below the walk, so the step is stated here against `evalInstr_binop`.
The remaining steps (`load i8`, `add`/`and`/`icmp` at `i8`) are
`JsonScanLane`'s, whose widths are the instruction's. -/

theorem evalInstr_mul_imm (calls : Calls) (env : Env) (s : State) (d a : String)
    {x c : BitVec 64} (ha : lookupName env a = some (.int 64 x)) :
    evalInstr calls (stateAt env s) (.binop d .mul 64 (.reg a) (.imm (.int 64 c))) =
      some (stateAt ((d, .int 64 (x * c)) :: env) s) := by
  have ha' : evalOperand (stateAt env s) (.reg a) = some (.int 64 x) :=
    BlockEval.evalOperand_reg_of env s a (.int 64 x) ha
  have hr : evalBinopNat .mul 64 x.toNat c.toNat = some (x * c).toNat := by
    simp [evalBinopNat, evalBinop, BitVec.ofNat_toNat]
  simpa only [stateAt, State.bind, BitVec.ofNat_toNat, BitVec.setWidth_eq] using
    (LeanLLVM.Refinement.JsonS1MasksIR.evalInstr_binop (s := stateAt env s) (d := d)
      (op := .mul) (w := 64) (a := .reg a) (b := .imm (.int 64 c)) ha'
      (BlockEval.evalOperand_lit_of (stateAt env s) 64 c) hr)

/-- The chain step for `mul i64`. -/
theorem denoteCode_mul_imm (calls : Calls) (env : Env) (s : State) (d a : String)
    {x c : BitVec 64} (ha : lookupName env a = some (.int 64 x)) (is : List Instr) :
    denoteCode calls (.binop d .mul 64 (.reg a) (.imm (.int 64 c)) :: is) (stateAt env s) =
      denoteCode calls is (stateAt ((d, .int 64 (x * c)) :: env) s) := by
  rw [BlockEval.denoteCode_cons_of _ _ _ _ _ (evalInstr_mul_imm calls env s d a ha)]

/-- An index below `2 ^ 63` sign-extends to itself. -/
theorem sExt_ofNat64 {j : Nat} (hj : j < 2 ^ 63) :
    ((BitVec.ofNat 64 j).signExtend 64).toNat = j := by
  simp [BitVec.toNat_ofNat, BitVec.signExtend]
  omega

/-- A one-byte read is one `readByte`. -/
theorem readBytes_one_some {m : Mem} {a : Nat} {b : UInt8} :
    readBytes m a 1 = some [b] ↔ readByte m a = some b := by
  rw [JsonEntrySteps.readBytes_one]
  cases readByte m a with
  | none => simp
  | some b' => simp

/-- A 64-bit word's successor, as the blocks' `add` writes it. -/
theorem ofNat64_add_one {j : Nat} (hj : j + 1 < 2 ^ 64) :
    BitVec.ofNat 64 j + (1#64) = BitVec.ofNat 64 (j + 1) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat,
    show (1 : Nat) % 2 ^ 64 = 1 from by decide,
    Nat.mod_eq_of_lt (by omega : j < 2 ^ 64), Nat.mod_eq_of_lt hj]

/-- The successor, as a 64-bit cell: both the block's `add` and the invariant's
`j + 1` write the same word. -/
theorem int_succ_eq (j : Nat) (hj : j + 1 < 2 ^ 64) :
    (some (.int 64 (BitVec.ofNat 64 j + (1#64))) : Option Value) =
      some (.int 64 (BitVec.ofNat 64 (j + 1))) := by
  rw [ofNat64_add_one hj]

/-! ### The accumulator's value

Each run's accumulator is not free: it holds the decimal value of the digits the
run has consumed.  `digitFold bs start len` is that value — the bytes at `start`,
the first `len` of them, read base ten — and one accumulating iteration is the
blocks' own `ip * 10 + digit`: a consumed byte is a digit (`IsDigitB`), whose low
nibble, `%10 = and %8, 15`, is its difference from `'0'`.

The `19` the ties carry is the accumulators' guard (`%idig.3574 < 19` at
`while.body52`, `%fdig.3594 < 19` at `while.body130`): past nineteen digits the
blocks stop accumulating, so the tie is stated over `min len 19` and holds on
both sides of the guard. -/

/-- The value the digit runs' accumulators compute: the bytes at `start`, the
first `len` of them, folded base ten. -/
def digitFold (bs : List UInt8) (start len : Nat) : Nat :=
  ((bs.drop start).take len).foldl (fun acc b => acc * 10 + (b.toNat - 0x30)) 0

/-- A digit byte's low nibble is its difference from `'0'` — the value the
blocks' `%10 = and %8, 15` and `%conv60 = zext %10` compute. -/
theorem digit_and_toNat {b : UInt8} (hb : IsDigitB b = true) :
    (JsonScanLane.vByte b &&& 0x0f#8).toNat = b.toNat - 0x30 := by
  unfold IsDigitB at hb
  rw [Bool.and_eq_true] at hb
  obtain ⟨h1, h2⟩ := hb
  rw [decide_eq_true_eq] at h1 h2
  have h30 : (0x30 : UInt8).toNat = 48 := by decide
  have h39 : (0x39 : UInt8).toNat = 57 := by decide
  have hb1 : 48 ≤ b.toNat := by rw [← h30]; exact UInt8.le_iff_toNat_le.mp h1
  have hb2 : b.toNat ≤ 57 := by rw [← h39]; exact UInt8.le_iff_toNat_le.mp h2
  have hr : b.toNat % 16 = b.toNat - 48 := by
    have hsplit : b.toNat = 48 + (b.toNat - 48) := by omega
    have hlt : b.toNat - 48 < 16 := by omega
    conv_lhs => rw [hsplit]
    rw [Nat.add_mod, show (48 : Nat) % 16 = 0 from by decide, Nat.zero_add,
      Nat.mod_mod, Nat.mod_eq_of_lt hlt]
  rw [BitVec.toNat_and, JsonScanLane.vByte_toNat,
    show (0x0f#8 : BitVec 8).toNat = 15 from by decide,
    show (15 : Nat) = 2 ^ 4 - 1 from by decide,
    Nat.and_two_pow_sub_one_eq_mod, hr]

/-- The fold's successor: one more digit multiplies by ten and adds it. -/
theorem digitFold_succ {bs : List UInt8} {start k : Nat}
    (hlen : start + k < bs.length) :
    digitFold bs start (k + 1)
      = digitFold bs start k * 10 + ((bs.getD (start + k) 0).toNat - 0x30) := by
  have hk : (bs.drop start)[k]? = some (bs.getD (start + k) 0) := by
    rw [List.getElem?_drop, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (by omega)]
    rfl
  simp only [digitFold, List.take_succ, hk, Option.toList_some, List.foldl_append,
    List.foldl_cons, List.foldl_nil]

/-- No digits consumed: the fold is zero, which is the accumulator's value at a
run's start before it accumulates anything. -/
theorem digitFold_zero (bs : List UInt8) (start : Nat) : digitFold bs start 0 = 0 := by
  simp only [digitFold, Nat.min_zero, List.take_zero, List.foldl_nil]

/-- A 64-bit word's ten-fold and add, as the block's `%add61`/`%add139` writes it:
`ofNat` truncates both sides alike, so no bound on the value is needed. -/
theorem ofNat_mul10_add (v d : Nat) :
    BitVec.ofNat 64 v * (10 : BitVec 64) + BitVec.ofNat 64 d
      = BitVec.ofNat 64 (v * 10 + d) := by
  rw [show (10 : BitVec 64) = BitVec.ofNat 64 10 from rfl,
    BitVec.ofNat_mul_ofNat, BitVec.ofNat_add_ofNat]

/-- `min` at a length below the cap: one more digit is one more. -/
theorem min_succ_of_lt {k cap : Nat} (h : k < cap) :
    min (k + 1) cap = min k cap + 1 := by
  rw [Nat.min_eq_left (by omega), Nat.min_eq_left (by omega)]

/-- `min` at a length past the cap: the cap has already been reached. -/
theorem min_succ_of_le {k cap : Nat} (h : cap ≤ k) :
    min (k + 1) cap = min k cap := by
  rw [Nat.min_eq_right (by omega), Nat.min_eq_right (by omega)]

/-- The accumulator guard taken, as the count: `%idig.3574 < 19` at a counter
below `2 ^ 64` is `d0 + c < 19`. -/
theorem ofNat_ult_true {k : Nat} (hk : k < 2 ^ 64)
    (h : (BitVec.ofNat 64 k).ult (19#64) = true) : k < 19 := by
  have h' : (BitVec.ofNat 64 k).toNat < (19#64 : BitVec 64).toNat :=
    BitVec.ult_iff_toNat_lt.mp h
  rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk,
    show (19#64 : BitVec 64).toNat = 19 from by decide] at h'

/-- The accumulator guard refused, as the count: the counter already reached
nineteen. -/
theorem ofNat_ult_false {k : Nat} (hk : k < 2 ^ 64)
    (h : (BitVec.ofNat 64 k).ult (19#64) = false) : 19 ≤ k := by
  by_contra hlt
  have hklt : k < 19 := by omega
  have htrue : (BitVec.ofNat 64 k).ult (19#64) = true := by
    apply BitVec.ult_iff_toNat_lt.mpr
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk,
      show (19#64 : BitVec 64).toNat = 19 from by decide]
    exact hklt
  rw [htrue] at h
  exact absurd h (by decide)

/-- **One accumulating iteration's arithmetic.**  With the register the fold at
the digits consumed and the next byte a digit, the block's
`ip * 10 + (and %8, 15)` is the fold one digit longer. -/
theorem digitFold_step {bs : List UInt8} {start k : Nat} {b : UInt8} {ip : BitVec 64}
    (hk : k < 19) (hlen : start + k < bs.length)
    (hbyte : bs.getD (start + k) 0 = b) (hdig : IsDigitB b = true)
    (hip : ip = BitVec.ofNat 64 (digitFold bs start k)) :
    ip * 10 + BitVec.ofNat 64 (JsonScanLane.vByte b &&& 0x0f#8).toNat
      = BitVec.ofNat 64 (digitFold bs start (k + 1)) := by
  subst hip
  rw [digitFold_succ hlen, hbyte, digit_and_toNat hdig, ofNat_mul10_add]

/-- The frozen iteration's arithmetic: the guard refused, so the register is the
fold at the cap already and stays it. -/
theorem digitFold_frozen {bs : List UInt8} {start k : Nat} {ip : BitVec 64}
    (h : 19 ≤ k) (hip : ip = BitVec.ofNat 64 (digitFold bs start (min k 19))) :
    ip = BitVec.ofNat 64 (digitFold bs start (min (k + 1) 19)) := by
  rw [min_succ_of_le h]; exact hip

/-- **One accumulating iteration, at the run's own indices.**  The same step
stated with the counter `c` and the digits' start `i0 - d0` kept apart, so the
caller supplies `i0 + c < bs.length` at the run's own index rather than the sum
of a subtraction. -/
theorem digitFold_step_at {bs : List UInt8} {i0 d0 c : Nat} {b : UInt8} {ip : BitVec 64}
    (hd0 : d0 ≤ i0) (hk : d0 + c < 19) (hlen : i0 + c < bs.length)
    (hbyte : bs.getD (i0 + c) 0 = b) (hdig : IsDigitB b = true)
    (hip : ip = BitVec.ofNat 64 (digitFold bs (i0 - d0) (min (d0 + c) 19))) :
    ip * 10 + BitVec.ofNat 64 (JsonScanLane.vByte b &&& 0x0f#8).toNat
      = BitVec.ofNat 64 (digitFold bs (i0 - d0) (min (d0 + c + 1) 19)) := by
  have hidx : i0 - d0 + (d0 + c) = i0 + c := by
    rw [← Nat.add_assoc, Nat.sub_add_cancel hd0]
  have hklt : min (d0 + c) 19 = d0 + c := Nat.min_eq_left (by omega)
  have hstep : min (d0 + c + 1) 19 = d0 + c + 1 := by
    rw [min_succ_of_lt hk, Nat.min_eq_left (by omega)]
  rw [hstep]
  refine digitFold_step hk ?_ ?_ hdig ?_
  · rw [hidx]; exact hlen
  · rwa [hidx]
  · rw [← hklt]; exact hip

/-- The byte a run is about to consume, as the invariant's list reads it: the
memory's byte at `start + k` is the list's, since the list is the range's. -/
theorem getD_of_readBytes {m : Mem} {p n k : Nat} {bs : List UInt8} {b : UInt8}
    (h : readBytes m p n = some bs) (hk : k < n) (hb : readByte m (p + k) = some b) :
    bs.getD k 0 = b := by
  have hsome : readByte m (p + k) = some (bs.getD k 0) := readByte_of_readBytes h hk
  exact Option.some.inj (hsome.symm.trans hb)

/-! ### The integer run: `land.lhs.true41`

The head's three `phi`s, its byte load and its test; the exit is `if.end68` at
the head and `if.end230` at `if.end62`. -/

def intHeadPhiEnv (env : Env) (j : Nat) (idig ip : BitVec 64) : Env :=
  ("%ip.3573", .int 64 ip) ::
  ("%idig.3574", .int 64 idig) ::
  ("%i.4575", .int 64 (BitVec.ofNat 64 j)) :: env

def intHeadEnv (env : Env) (a j : Nat) (b : UInt8) (idig ip : BitVec 64) : Env :=
  ("%or.cond440", .int 1 (BitVec.ofBool (IsDigitB b))) ::
  ("%9", .int 8 (JsonScanLane.vByte b + 0xd0#8)) ::
  ("%8", .int 8 (JsonScanLane.vByte b)) ::
  ("%arrayidx42", .ptr (a + j)) :: intHeadPhiEnv env j idig ip

theorem lookup_intHeadPhiEnv_p (env : Env) (j : Nat) (idig ip : BitVec 64) (a : Nat) :
    lookupName (intHeadPhiEnv env j idig ip) "%p" = some (.ptr a) ↔
      lookupName env "%p" = some (.ptr a) := by
  simp only [intHeadPhiEnv,
    lookupName_cons_ne (k := "%ip.3573") (n := "%p") _ _ (by decide),
    lookupName_cons_ne (k := "%idig.3574") (n := "%p") _ _ (by decide),
    lookupName_cons_ne (k := "%i.4575") (n := "%p") _ _ (by decide)]

theorem lookup_intHeadPhiEnv_n (env : Env) (j : Nat) (idig ip : BitVec 64) (n : BitVec 64) :
    lookupName (intHeadPhiEnv env j idig ip) "%n" = some (.int 64 n) ↔
      lookupName env "%n" = some (.int 64 n) := by
  simp only [intHeadPhiEnv,
    lookupName_cons_ne (k := "%ip.3573") (n := "%n") _ _ (by decide),
    lookupName_cons_ne (k := "%idig.3574") (n := "%n") _ _ (by decide),
    lookupName_cons_ne (k := "%i.4575") (n := "%n") _ _ (by decide)]

theorem lookup_intHeadPhiEnv_i (env : Env) (j : Nat) (idig ip : BitVec 64) :
    lookupName (intHeadPhiEnv env j idig ip) "%i.4575"
      = some (.int 64 (BitVec.ofNat 64 j)) := by
  simp only [intHeadPhiEnv,
    lookupName_cons_ne (k := "%ip.3573") (n := "%i.4575") _ _ (by decide),
    lookupName_cons_ne (k := "%idig.3574") (n := "%i.4575") _ _ (by decide),
    lookupName_cons_self]

theorem lookup_intHeadPhiEnv_idig (env : Env) (j : Nat) (idig ip : BitVec 64) :
    lookupName (intHeadPhiEnv env j idig ip) "%idig.3574" = some (.int 64 idig) := by
  simp only [intHeadPhiEnv,
    lookupName_cons_ne (k := "%ip.3573") (n := "%idig.3574") _ _ (by decide),
    lookupName_cons_self]

/-! #### The head, at its two edges

The block's four instructions after the `phi` run, given the run's environment.
Its `denoteCode` is the pin's instruction list and nothing else. -/

theorem intHead_denote_phi {calls : Calls} {env : Env} {s : State} {a j : Nat}
    {b : UInt8} {idig ip : BitVec 64}
    (hp : lookupName (intHeadPhiEnv env j idig ip) "%p" = some (.ptr a))
    (hj : j < 2 ^ 63)
    (hread : readByte s.mem (a + j) = some b) :
    denoteCode calls
      [Instr.gep "%arrayidx42" (Ty.int 8) (Operand.reg "%p") (Operand.reg "%i.4575"),
       Instr.load "%8" (Ty.int 8) (Operand.reg "%arrayidx42"),
       Instr.binop "%9" (BinOp.add) 8 (Operand.reg "%8") (Operand.imm (Const.int 8 0xd0#8)),
       Instr.icmp "%or.cond440" (IPred.ult) 8 (Operand.reg "%9")
         (Operand.imm (Const.int 8 0x0a#8))]
      (stateAt (intHeadPhiEnv env j idig ip) s) =
    some (stateAt (intHeadEnv env a j b idig ip) s) := by
  have ho : lookupName (intHeadPhiEnv env j idig ip) "%i.4575"
      = some (.int 64 (BitVec.ofNat 64 j)) := lookup_intHeadPhiEnv_i env j idig ip
  have hpos : ((BitVec.ofNat 64 j).signExtend 64).toNat < 2 ^ 63 := by
    rw [sExt_ofNat64 hj]; exact hj
  rw [denoteCode_gep8_reg _ _ _ "%arrayidx42" "%p" "%i.4575" hp ho hpos _]
  rw [sExt_ofNat64 hj]
  have ha8 : lookupName
      (("%arrayidx42", .ptr (a + j)) :: intHeadPhiEnv env j idig ip) "%arrayidx42"
      = some (.ptr (a + j)) := lookupName_cons_self ..
  rw [JsonScanLane.denoteCode_load_i8 _ _ _ "%8" "%arrayidx42" ha8
    (readBytes_one_some.mpr hread) _]
  have ha9 : lookupName
      (("%8", .int 8 (JsonScanLane.vByte b)) ::
        ("%arrayidx42", .ptr (a + j)) :: intHeadPhiEnv env j idig ip) "%8"
      = some (.int 8 (JsonScanLane.vByte b)) := lookupName_cons_self ..
  rw [JsonScanLane.denoteCode_add_imm_w _ _ _ "%9" "%8" 8 ha9 _]
  have ha10 : lookupName
      (("%9", .int 8 (JsonScanLane.vByte b + 0xd0#8)) ::
        ("%8", .int 8 (JsonScanLane.vByte b)) ::
        ("%arrayidx42", .ptr (a + j)) :: intHeadPhiEnv env j idig ip) "%9"
      = some (.int 8 (JsonScanLane.vByte b + 0xd0#8)) := lookupName_cons_self ..
  rw [JsonScanLane.denoteCode_icmp_imm_w _ _ _ "%or.cond440" "%9" .ult ha10 _]
  simp only [denoteCode, denoteRun, State.bindAll, stateAt, intHeadEnv, intHeadPhiEnv,
    evalICmp_ult_digit]

/-! The `phi` run, entry edge: `%i.1558`, `%idig.0560`, `%ip.0562`. -/

theorem intHead_run_entry {calls : Calls} {env : Env} {s : State} {j : Nat}
    {idig ip : BitVec 64}
    (hpre : s.pre = some "land.lhs.true41.preheader")
    (hhi : evalOperand (stateAt env s) (.reg "%i.1558")
      = some (.int 64 (BitVec.ofNat 64 j)))
    (hhd : evalOperand (stateAt env s) (.reg "%idig.0560") = some (.int 64 idig))
    (hhp : evalOperand (stateAt env s) (.reg "%ip.0562") = some (.int 64 ip)) :
    denoteCode calls numFastLandLhsTrue41Instrs (stateAt env s) =
      denoteCode calls
        [Instr.gep "%arrayidx42" (Ty.int 8) (Operand.reg "%p") (Operand.reg "%i.4575"),
         Instr.load "%8" (Ty.int 8) (Operand.reg "%arrayidx42"),
         Instr.binop "%9" (BinOp.add) 8 (Operand.reg "%8") (Operand.imm (Const.int 8 0xd0#8)),
         Instr.icmp "%or.cond440" (IPred.ult) 8 (Operand.reg "%9")
           (Operand.imm (Const.int 8 0x0a#8))]
        (stateAt (intHeadPhiEnv env j idig ip) s) := by
  unfold numFastLandLhsTrue41Instrs
  block_phi_run
  rotate_left 1
  · exact hpre
  · rfl
  · simp only [phiIncoming]; rfl
  · exact hhi
  · simp only [phiIncoming]; rfl
  · exact hhd
  · simp only [phiIncoming]; rfl
  · exact hhp
  · simp only [runCells, intHeadPhiEnv, stateAt]

/-! The `phi` run, back edge: `%inc64`, `%inc63`, `%ip.4`. -/

theorem intHead_run_back {calls : Calls} {env : Env} {s : State} {j : Nat}
    {idig ip : BitVec 64}
    (hpre : s.pre = some "if.end62")
    (hhi : evalOperand (stateAt env s) (.reg "%inc64")
      = some (.int 64 (BitVec.ofNat 64 j)))
    (hhd : evalOperand (stateAt env s) (.reg "%inc63") = some (.int 64 idig))
    (hhp : evalOperand (stateAt env s) (.reg "%ip.4") = some (.int 64 ip)) :
    denoteCode calls numFastLandLhsTrue41Instrs (stateAt env s) =
      denoteCode calls
        [Instr.gep "%arrayidx42" (Ty.int 8) (Operand.reg "%p") (Operand.reg "%i.4575"),
         Instr.load "%8" (Ty.int 8) (Operand.reg "%arrayidx42"),
         Instr.binop "%9" (BinOp.add) 8 (Operand.reg "%8") (Operand.imm (Const.int 8 0xd0#8)),
         Instr.icmp "%or.cond440" (IPred.ult) 8 (Operand.reg "%9")
           (Operand.imm (Const.int 8 0x0a#8))]
        (stateAt (intHeadPhiEnv env j idig ip) s) := by
  unfold numFastLandLhsTrue41Instrs
  block_phi_run
  rotate_left 1
  · exact hpre
  · rfl
  · simp only [phiIncoming]; rfl
  · exact hhi
  · simp only [phiIncoming]; rfl
  · exact hhd
  · simp only [phiIncoming]; rfl
  · exact hhp
  · simp only [runCells, intHeadPhiEnv, stateAt]

/-- The head's whole `denoteCode`, entry edge. -/
theorem intHead_denote_entry {calls : Calls} {env : Env} {s : State} {a j : Nat}
    {b : UInt8} {idig ip : BitVec 64}
    (hpre : s.pre = some "land.lhs.true41.preheader")
    (hp : lookupName env "%p" = some (.ptr a))
    (hhi : evalOperand (stateAt env s) (.reg "%i.1558")
      = some (.int 64 (BitVec.ofNat 64 j)))
    (hhd : evalOperand (stateAt env s) (.reg "%idig.0560") = some (.int 64 idig))
    (hhp : evalOperand (stateAt env s) (.reg "%ip.0562") = some (.int 64 ip))
    (hj : j < 2 ^ 63) (hread : readByte s.mem (a + j) = some b) :
    denoteCode calls numFastLandLhsTrue41Instrs (stateAt env s) =
      some (stateAt (intHeadEnv env a j b idig ip) s) := by
  rw [intHead_run_entry (calls := calls) hpre hhi hhd hhp]
  exact intHead_denote_phi ((lookup_intHeadPhiEnv_p env j idig ip a).mpr hp) hj hread

/-- The head's whole `denoteCode`, back edge. -/
theorem intHead_denote_back {calls : Calls} {env : Env} {s : State} {a j : Nat}
    {b : UInt8} {idig ip : BitVec 64}
    (hpre : s.pre = some "if.end62")
    (hp : lookupName env "%p" = some (.ptr a))
    (hhi : evalOperand (stateAt env s) (.reg "%inc64")
      = some (.int 64 (BitVec.ofNat 64 j)))
    (hhd : evalOperand (stateAt env s) (.reg "%inc63") = some (.int 64 idig))
    (hhp : evalOperand (stateAt env s) (.reg "%ip.4") = some (.int 64 ip))
    (hj : j < 2 ^ 63) (hread : readByte s.mem (a + j) = some b) :
    denoteCode calls numFastLandLhsTrue41Instrs (stateAt env s) =
      some (stateAt (intHeadEnv env a j b idig ip) s) := by
  rw [intHead_run_back (calls := calls) hpre hhi hhd hhp]
  exact intHead_denote_phi ((lookup_intHeadPhiEnv_p env j idig ip a).mpr hp) hj hread

/-! ### The integer run's body: `while.body52`, `if.then55`, `if.end62` -/

def intBodyEnv (env : Env) (idig : BitVec 64) : Env :=
  ("%cmp53", .int 1 (evalICmp .ult idig (19#64))) :: env

theorem intBodyEnv_p (env : Env) (idig : BitVec 64) (a : Nat) :
    lookupName (intBodyEnv env idig) "%p" = some (.ptr a) ↔
      lookupName env "%p" = some (.ptr a) := by
  simp only [intBodyEnv, lookupName_cons_ne (k := "%cmp53") (n := "%p") _ _ (by decide)]

theorem intBodyEnv_n (env : Env) (idig : BitVec 64) (n : BitVec 64) :
    lookupName (intBodyEnv env idig) "%n" = some (.int 64 n) ↔
      lookupName env "%n" = some (.int 64 n) := by
  simp only [intBodyEnv, lookupName_cons_ne (k := "%cmp53") (n := "%n") _ _ (by decide)]

theorem intBody_denote {calls : Calls} {env : Env} {s : State} {idig : BitVec 64}
    (hid : lookupName env "%idig.3574" = some (.int 64 idig)) :
    denoteCode calls numFastWhileBody52Instrs (stateAt env s) =
      some (stateAt (intBodyEnv env idig) s) := by
  unfold numFastWhileBody52Instrs
  block_eval

/-- `while.body52`, the guard taken: the accumulator's digit count is below
nineteen, so the block leaves for `if.then55`. -/
theorem intBody_step_taken {env : Env} {s : State} {idig : BitVec 64}
    (hpc : s.pc = "while.body52")
    (hid : lookupName env "%idig.3574" = some (.int 64 idig))
    (hlt : idig.ult (19#64) = true) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (intBodyEnv env idig)
        { s with pc := "if.then55", pre := some "while.body52" }) := by
  refine numFast_step_at (s' := stateAt (intBodyEnv env idig) s)
    (b := ⟨"while.body52", numFastWhileBody52Instrs,
      Term.condbr (.reg "%cmp53") "if.then55" "if.end62"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using numFast_findBlock_while_body52
  · simpa only [denoteCode_nil] using intBody_denote hid
  · have hlk : lookupName (intBodyEnv env idig) "%cmp53"
        = some (.int 1 (evalICmp .ult idig (19#64))) := by
      simp only [intBodyEnv, lookupName_cons_self]
    have hb : evalICmp .ult idig (19#64) = 1 := by
      unfold evalICmp; rw [hlt]; rfl
    rw [numFast_execTerm_condbr_one _ "%cmp53" _ _ hlk hb]
    simp only [stateAt, hpc]

/-- `while.body52`, the guard refused: the count is nineteen or more, so the
block leaves for `if.end62` without accumulating. -/
theorem intBody_step_skip {env : Env} {s : State} {idig : BitVec 64}
    (hpc : s.pc = "while.body52")
    (hid : lookupName env "%idig.3574" = some (.int 64 idig))
    (hlt : idig.ult (19#64) = false) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (intBodyEnv env idig)
        { s with pc := "if.end62", pre := some "while.body52" }) := by
  refine numFast_step_at (s' := stateAt (intBodyEnv env idig) s)
    (b := ⟨"while.body52", numFastWhileBody52Instrs,
      Term.condbr (.reg "%cmp53") "if.then55" "if.end62"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using numFast_findBlock_while_body52
  · simpa only [denoteCode_nil] using intBody_denote hid
  · have hlk : lookupName (intBodyEnv env idig) "%cmp53"
        = some (.int 1 (evalICmp .ult idig (19#64))) := by
      simp only [intBodyEnv, lookupName_cons_self]
    have hb : evalICmp .ult idig (19#64) = 0 := by
      unfold evalICmp; rw [hlt]; rfl
    rw [numFast_execTerm_condbr_zero _ "%cmp53" _ _ hlk hb]
    simp only [stateAt, hpc]

/-- `if.then55`'s environment: the product, the nibble, its extension and the
sum. -/
def intIfThenEnv (env : Env) (ip : BitVec 64) (b : UInt8) : Env :=
  ("%add61", .int 64
      (ip * 10 + BitVec.ofNat 64 (JsonScanLane.vByte b &&& 0x0f#8).toNat)) ::
  ("%conv60", .int 64 (BitVec.ofNat 64 (JsonScanLane.vByte b &&& 0x0f#8).toNat)) ::
  ("%10", .int 8 (JsonScanLane.vByte b &&& 0x0f#8)) ::
  ("%mul56", .int 64 (ip * 10)) :: env

theorem intIfThenEnv_p (env : Env) (ip : BitVec 64) (b : UInt8) (a : Nat) :
    lookupName (intIfThenEnv env ip b) "%p" = some (.ptr a) ↔
      lookupName env "%p" = some (.ptr a) := by
  simp only [intIfThenEnv, lookupName_cons_ne (k := "%add61") (n := "%p") _ _ (by decide),
    lookupName_cons_ne (k := "%conv60") (n := "%p") _ _ (by decide),
    lookupName_cons_ne (k := "%10") (n := "%p") _ _ (by decide),
    lookupName_cons_ne (k := "%mul56") (n := "%p") _ _ (by decide)]

theorem intIfThenEnv_n (env : Env) (ip : BitVec 64) (b : UInt8) (n : BitVec 64) :
    lookupName (intIfThenEnv env ip b) "%n" = some (.int 64 n) ↔
      lookupName env "%n" = some (.int 64 n) := by
  simp only [intIfThenEnv, lookupName_cons_ne (k := "%add61") (n := "%n") _ _ (by decide),
    lookupName_cons_ne (k := "%conv60") (n := "%n") _ _ (by decide),
    lookupName_cons_ne (k := "%10") (n := "%n") _ _ (by decide),
    lookupName_cons_ne (k := "%mul56") (n := "%n") _ _ (by decide)]

theorem intIfThen_denote {calls : Calls} {env : Env} {s : State} {ip : BitVec 64}
    {b : UInt8}
    (hip : lookupName env "%ip.3573" = some (.int 64 ip))
    (h8 : lookupName env "%8" = some (.int 8 (JsonScanLane.vByte b))) :
    denoteCode calls numFastIfThen55Instrs (stateAt env s) =
      some (stateAt (intIfThenEnv env ip b) s) := by
  unfold numFastIfThen55Instrs
  rw [denoteCode_mul_imm _ _ _ "%mul56" "%ip.3573" hip _]
  rw [JsonScanLane.denoteCode_and_imm_w _ _ _ "%10" "%8" (w := 8) (by block_lk) _]
  rw [denoteCode_zext _ _ _ "%conv60" "%10" 8 64 (by block_lk) _]
  rw [denoteCode_add_reg _ _ _ "%add61" "%mul56" "%conv60" (by block_lk) (by block_lk) _]
  simp only [denoteCode, denoteRun, State.bindAll, stateAt, intIfThenEnv]
  rfl

theorem intIfThen_step {env : Env} {s : State} {ip : BitVec 64} {b : UInt8}
    (hpc : s.pc = "if.then55")
    (hip : lookupName env "%ip.3573" = some (.int 64 ip))
    (h8 : lookupName env "%8" = some (.int 8 (JsonScanLane.vByte b))) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (intIfThenEnv env ip b)
        { s with pc := "if.end62", pre := some "if.then55" }) := by
  refine numFast_step_at (s' := stateAt (intIfThenEnv env ip b) s)
    (b := ⟨"if.then55", numFastIfThen55Instrs, Term.br "if.end62"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using numFast_findBlock_if_then55
  · simpa only [denoteCode_nil] using intIfThen_denote hip h8
  · simp only [execTerm, stateAt, hpc]

/-- `if.end62`'s environment: the `ip` `phi`, the two increments and the
end-of-lexeme test. -/
def intIfEndEnv (env : Env) (ip idig i n : BitVec 64) : Env :=
  ("%exitcond.not", .int 1 (evalICmp .eq (i + 1#64) n)) ::
  ("%inc64", .int 64 (i + 1#64)) ::
  ("%inc63", .int 64 (idig + 1#64)) ::
  ("%ip.4", .int 64 ip) :: env

theorem intIfEndEnv_p (env : Env) (ip idig i n : BitVec 64) (a : Nat) :
    lookupName (intIfEndEnv env ip idig i n) "%p" = some (.ptr a) ↔
      lookupName env "%p" = some (.ptr a) := by
  simp only [intIfEndEnv, lookupName_cons_ne (k := "%exitcond.not") (n := "%p") _ _ (by decide),
    lookupName_cons_ne (k := "%inc64") (n := "%p") _ _ (by decide),
    lookupName_cons_ne (k := "%inc63") (n := "%p") _ _ (by decide),
    lookupName_cons_ne (k := "%ip.4") (n := "%p") _ _ (by decide)]

theorem intIfEndEnv_n (env : Env) (ip idig i n : BitVec 64) (m : BitVec 64) :
    lookupName (intIfEndEnv env ip idig i n) "%n" = some (.int 64 m) ↔
      lookupName env "%n" = some (.int 64 m) := by
  simp only [intIfEndEnv, lookupName_cons_ne (k := "%exitcond.not") (n := "%n") _ _ (by decide),
    lookupName_cons_ne (k := "%inc64") (n := "%n") _ _ (by decide),
    lookupName_cons_ne (k := "%inc63") (n := "%n") _ _ (by decide),
    lookupName_cons_ne (k := "%ip.4") (n := "%n") _ _ (by decide)]

theorem intIfEnd_denote {calls : Calls} {env : Env} {s : State} {idig i n : BitVec 64}
    {p : String} {op : Operand} {ipv : BitVec 64}
    (hpre : s.pre = some p)
    (hinc : phiIncoming p
      [("if.then55", (Operand.reg "%add61")), ("while.body52", (Operand.reg "%ip.3573"))]
      = some op)
    (hop : evalOperand (stateAt env s) op = some (.int 64 ipv))
    (hid : lookupName env "%idig.3574" = some (.int 64 idig))
    (hi : lookupName env "%i.4575" = some (.int 64 i))
    (hn : lookupName env "%n" = some (.int 64 n)) :
    denoteCode calls numFastIfEnd62Instrs (stateAt env s) =
      some (stateAt (intIfEndEnv env ipv idig i n) s) := by
  unfold numFastIfEnd62Instrs
  rw [denoteCode_phi _ _ _ "%ip.4" (Ty.int 64)
    [("if.then55", (Operand.reg "%add61")), ("while.body52", (Operand.reg "%ip.3573"))]
    hpre hinc hop _ (by decide)]
  rw [denoteCode_add_imm _ _ _ "%inc63" "%idig.3574" (by block_lk) _]
  rw [denoteCode_add_imm _ _ _ "%inc64" "%i.4575" (by block_lk) _]
  rw [denoteCode_icmp_eq_reg _ _ _ "%exitcond.not" "%inc64" "%n" (by block_lk) (by block_lk) _]
  simp only [denoteCode, denoteRun, State.bindAll, stateAt, intIfEndEnv]

/-- `if.end62`, the index reached the length: the block leaves for
`if.end230`. -/
theorem intIfEnd_step_exit {env : Env} {s : State} {idig i n : BitVec 64}
    {p : String} {op : Operand} {ipv : BitVec 64}
    (hpc : s.pc = "if.end62")
    (hpre : s.pre = some p)
    (hinc : phiIncoming p
      [("if.then55", (Operand.reg "%add61")), ("while.body52", (Operand.reg "%ip.3573"))]
      = some op)
    (hop : evalOperand (stateAt env s) op = some (.int 64 ipv))
    (hid : lookupName env "%idig.3574" = some (.int 64 idig))
    (hi : lookupName env "%i.4575" = some (.int 64 i))
    (hn : lookupName env "%n" = some (.int 64 n))
    (heq : evalICmp .eq (i + 1#64) n = 1) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (intIfEndEnv env ipv idig i n)
        { s with pc := "if.end230", pre := some "if.end62" }) := by
  refine numFast_step_at (s' := stateAt (intIfEndEnv env ipv idig i n) s)
    (b := ⟨"if.end62", numFastIfEnd62Instrs,
      Term.condbr (.reg "%exitcond.not") "if.end230" "land.lhs.true41"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using numFast_findBlock_if_end62
  · simpa only [denoteCode_nil] using intIfEnd_denote hpre hinc hop hid hi hn
  · have hlk : lookupName (intIfEndEnv env ipv idig i n) "%exitcond.not"
        = some (.int 1 (evalICmp .eq (i + 1#64) n)) := by
      simp only [intIfEndEnv, lookupName_cons_self]
    rw [numFast_execTerm_condbr_one _ "%exitcond.not" _ _ hlk heq]
    simp only [stateAt, hpc]

/-- `if.end62`, the index is inside the lexeme: the block leaves for the head. -/
theorem intIfEnd_step_loop {env : Env} {s : State} {idig i n : BitVec 64}
    {p : String} {op : Operand} {ipv : BitVec 64}
    (hpc : s.pc = "if.end62")
    (hpre : s.pre = some p)
    (hinc : phiIncoming p
      [("if.then55", (Operand.reg "%add61")), ("while.body52", (Operand.reg "%ip.3573"))]
      = some op)
    (hop : evalOperand (stateAt env s) op = some (.int 64 ipv))
    (hid : lookupName env "%idig.3574" = some (.int 64 idig))
    (hi : lookupName env "%i.4575" = some (.int 64 i))
    (hn : lookupName env "%n" = some (.int 64 n))
    (heq : evalICmp .eq (i + 1#64) n = 0) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (intIfEndEnv env ipv idig i n)
        { s with pc := "land.lhs.true41", pre := some "if.end62" }) := by
  refine numFast_step_at (s' := stateAt (intIfEndEnv env ipv idig i n) s)
    (b := ⟨"if.end62", numFastIfEnd62Instrs,
      Term.condbr (.reg "%exitcond.not") "if.end230" "land.lhs.true41"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using numFast_findBlock_if_end62
  · simpa only [denoteCode_nil] using intIfEnd_denote hpre hinc hop hid hi hn
  · have hlk : lookupName (intIfEndEnv env ipv idig i n) "%exitcond.not"
        = some (.int 1 (evalICmp .eq (i + 1#64) n)) := by
      simp only [intIfEndEnv, lookupName_cons_self]
    rw [numFast_execTerm_condbr_zero _ "%exitcond.not" _ _ hlk heq]
    simp only [stateAt, hpc]

/-! #### The head's control step, at the two edges and the two test outcomes -/

theorem intHead_step_entry_digit {env : Env} {s : State} {a j : Nat} {b : UInt8}
    {idig ip : BitVec 64}
    (hpc : s.pc = "land.lhs.true41")
    (hpre : s.pre = some "land.lhs.true41.preheader")
    (hp : lookupName env "%p" = some (.ptr a))
    (hhi : evalOperand (stateAt env s) (.reg "%i.1558")
      = some (.int 64 (BitVec.ofNat 64 j)))
    (hhd : evalOperand (stateAt env s) (.reg "%idig.0560") = some (.int 64 idig))
    (hhp : evalOperand (stateAt env s) (.reg "%ip.0562") = some (.int 64 ip))
    (hj : j < 2 ^ 63) (hread : readByte s.mem (a + j) = some b)
    (hdigit : IsDigitB b = true) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (intHeadEnv env a j b idig ip)
        { s with pc := "while.body52", pre := some "land.lhs.true41" }) := by
  refine numFast_step_at (s' := stateAt (intHeadEnv env a j b idig ip) s)
    (b := ⟨"land.lhs.true41", numFastLandLhsTrue41Instrs,
      Term.condbr (.reg "%or.cond440") "while.body52" "if.end68"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using numFast_findBlock_land_lhs_true41
  · simpa only [denoteCode_nil] using intHead_denote_entry hpre hp hhi hhd hhp hj hread
  · have hlk : lookupName (intHeadEnv env a j b idig ip) "%or.cond440"
        = some (.int 1 (BitVec.ofBool (IsDigitB b))) := by
      simp only [intHeadEnv, lookupName_cons_self]
    have hb1 : BitVec.ofBool (IsDigitB b) = (1 : BitVec 1) := by
      rw [hdigit]; rfl
    rw [numFast_execTerm_condbr_one _ "%or.cond440" _ _ hlk hb1]
    simp only [stateAt, hpc]

theorem intHead_step_entry_nondigit {env : Env} {s : State} {a j : Nat} {b : UInt8}
    {idig ip : BitVec 64}
    (hpc : s.pc = "land.lhs.true41")
    (hpre : s.pre = some "land.lhs.true41.preheader")
    (hp : lookupName env "%p" = some (.ptr a))
    (hhi : evalOperand (stateAt env s) (.reg "%i.1558")
      = some (.int 64 (BitVec.ofNat 64 j)))
    (hhd : evalOperand (stateAt env s) (.reg "%idig.0560") = some (.int 64 idig))
    (hhp : evalOperand (stateAt env s) (.reg "%ip.0562") = some (.int 64 ip))
    (hj : j < 2 ^ 63) (hread : readByte s.mem (a + j) = some b)
    (hdigit : IsDigitB b = false) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (intHeadEnv env a j b idig ip)
        { s with pc := "if.end68", pre := some "land.lhs.true41" }) := by
  refine numFast_step_at (s' := stateAt (intHeadEnv env a j b idig ip) s)
    (b := ⟨"land.lhs.true41", numFastLandLhsTrue41Instrs,
      Term.condbr (.reg "%or.cond440") "while.body52" "if.end68"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using numFast_findBlock_land_lhs_true41
  · simpa only [denoteCode_nil] using intHead_denote_entry hpre hp hhi hhd hhp hj hread
  · have hlk : lookupName (intHeadEnv env a j b idig ip) "%or.cond440"
        = some (.int 1 (BitVec.ofBool (IsDigitB b))) := by
      simp only [intHeadEnv, lookupName_cons_self]
    have hb1 : BitVec.ofBool (IsDigitB b) = (0 : BitVec 1) := by
      rw [hdigit]; rfl
    rw [numFast_execTerm_condbr_zero _ "%or.cond440" _ _ hlk hb1]
    simp only [stateAt, hpc]

theorem intHead_step_back_digit {env : Env} {s : State} {a j : Nat} {b : UInt8}
    {idig ip : BitVec 64}
    (hpc : s.pc = "land.lhs.true41")
    (hpre : s.pre = some "if.end62")
    (hp : lookupName env "%p" = some (.ptr a))
    (hhi : evalOperand (stateAt env s) (.reg "%inc64")
      = some (.int 64 (BitVec.ofNat 64 j)))
    (hhd : evalOperand (stateAt env s) (.reg "%inc63") = some (.int 64 idig))
    (hhp : evalOperand (stateAt env s) (.reg "%ip.4") = some (.int 64 ip))
    (hj : j < 2 ^ 63) (hread : readByte s.mem (a + j) = some b)
    (hdigit : IsDigitB b = true) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (intHeadEnv env a j b idig ip)
        { s with pc := "while.body52", pre := some "land.lhs.true41" }) := by
  refine numFast_step_at (s' := stateAt (intHeadEnv env a j b idig ip) s)
    (b := ⟨"land.lhs.true41", numFastLandLhsTrue41Instrs,
      Term.condbr (.reg "%or.cond440") "while.body52" "if.end68"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using numFast_findBlock_land_lhs_true41
  · simpa only [denoteCode_nil] using intHead_denote_back hpre hp hhi hhd hhp hj hread
  · have hlk : lookupName (intHeadEnv env a j b idig ip) "%or.cond440"
        = some (.int 1 (BitVec.ofBool (IsDigitB b))) := by
      simp only [intHeadEnv, lookupName_cons_self]
    have hb1 : BitVec.ofBool (IsDigitB b) = (1 : BitVec 1) := by
      rw [hdigit]; rfl
    rw [numFast_execTerm_condbr_one _ "%or.cond440" _ _ hlk hb1]
    simp only [stateAt, hpc]

theorem intHead_step_back_nondigit {env : Env} {s : State} {a j : Nat} {b : UInt8}
    {idig ip : BitVec 64}
    (hpc : s.pc = "land.lhs.true41")
    (hpre : s.pre = some "if.end62")
    (hp : lookupName env "%p" = some (.ptr a))
    (hhi : evalOperand (stateAt env s) (.reg "%inc64")
      = some (.int 64 (BitVec.ofNat 64 j)))
    (hhd : evalOperand (stateAt env s) (.reg "%inc63") = some (.int 64 idig))
    (hhp : evalOperand (stateAt env s) (.reg "%ip.4") = some (.int 64 ip))
    (hj : j < 2 ^ 63) (hread : readByte s.mem (a + j) = some b)
    (hdigit : IsDigitB b = false) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (intHeadEnv env a j b idig ip)
        { s with pc := "if.end68", pre := some "land.lhs.true41" }) := by
  refine numFast_step_at (s' := stateAt (intHeadEnv env a j b idig ip) s)
    (b := ⟨"land.lhs.true41", numFastLandLhsTrue41Instrs,
      Term.condbr (.reg "%or.cond440") "while.body52" "if.end68"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using numFast_findBlock_land_lhs_true41
  · simpa only [denoteCode_nil] using intHead_denote_back hpre hp hhi hhd hhp hj hread
  · have hlk : lookupName (intHeadEnv env a j b idig ip) "%or.cond440"
        = some (.int 1 (BitVec.ofBool (IsDigitB b))) := by
      simp only [intHeadEnv, lookupName_cons_self]
    have hb1 : BitVec.ofBool (IsDigitB b) = (0 : BitVec 1) := by
      rw [hdigit]; rfl
    rw [numFast_execTerm_condbr_zero _ "%or.cond440" _ _ hlk hb1]
    simp only [stateAt, hpc]

/-! ### The integer run's invariant, test and exit -/

/-- The end-of-lexeme exit's cells: the run stopped at the lexeme's end, so the
index is the length, and the block it leaves for is `if.end230` from `if.end62`.
It carries the cursor, the length, the count `d0 + (n - i0)` the count cell reads,
the accumulator's value at those digits, and the count `%7` the digit head's
preheader formed: `if.end230`'s `%idig.4709716730` phi reads it on this edge, so
a composed run exit has to hand it on.  The cursor and the length are the cells
every later block reads. -/
def intRunEndWord (bs : List UInt8) (p n i0 d0 : Nat) (e : State) : Prop :=
  e.pc = "if.end230" ∧ e.pre = some "if.end62" ∧ n < 2 ^ 64 ∧
  lookupName e.env "%p" = some (.ptr p) ∧
  lookupName e.env "%n" = some (.int 64 (BitVec.ofNat 64 n)) ∧
  lookupName e.env "%inc64" = some (.int 64 (BitVec.ofNat 64 n)) ∧
  lookupName e.env "%inc63"
    = some (.int 64 (BitVec.ofNat 64 (d0 + (n - i0)))) ∧
  lookupName e.env "%ip.4"
    = some (.int 64
      (BitVec.ofNat 64 (digitFold bs (i0 - d0) (min (d0 + (n - i0)) 19)))) ∧
  lookupName e.env "%7"
    = some (.int 64 (BitVec.ofNat 64 d0 + BitVec.ofNat 64 n - BitVec.ofNat 64 i0))

/-- The exit states: the head's non-digit branch (`if.end68`) or the
end-of-lexeme branch (`intRunEndWord`), each carrying the cursor, the length, the
count at the index it stopped at and the accumulator's value at the digits the
count names, and each naming its predecessor.  The non-digit exit's index is
inside the lexeme, so the `.` test reads a byte; it also hands the byte it
stopped on and that byte's non-digit answer, read at the run's own memory — the
exit state is opaque to a composition, so a reader that has to know whether the
run stopped at the lexeme's end or on a non-digit cannot re-read the byte
itself. -/
def intRunExit (mem0 : Mem) (bs : List UInt8) (p n i0 d0 : Nat) (e : State) : Prop :=
  (e.pc = "if.end68" ∧ e.pre = some "land.lhs.true41" ∧
      lookupName e.env "%p" = some (.ptr p) ∧
      lookupName e.env "%n" = some (.int 64 (BitVec.ofNat 64 n)) ∧
      ∃ i1, i0 ≤ i1 ∧ i1 < n ∧
        lookupName e.env "%i.4575" = some (.int 64 (BitVec.ofNat 64 i1)) ∧
        lookupName e.env "%idig.3574"
          = some (.int 64 (BitVec.ofNat 64 (d0 + (i1 - i0)))) ∧
        lookupName e.env "%ip.3573"
          = some (.int 64
            (BitVec.ofNat 64 (digitFold bs (i0 - d0) (min (d0 + (i1 - i0)) 19)))) ∧
        ∃ b, readByte mem0 (p + i1) = some b ∧ IsDigitB b = false)
  ∨ intRunEndWord bs p n i0 d0 e

/-- The head's test, at the run's own start: the remaining length is one short
of the counter, or the byte at the counter is not a digit. -/
def intRunAtBound (mem0 : Mem) (p n i0 : Nat) (s : State) (c : Nat) : Bool :=
  decide (n - i0 ≤ c + 1) || !numFastDigitAt mem0 p (i0 + c)

/-- The run's invariant: the head with the counters at `c`, the byte readable at
`i0 + c`, the edge's phi sources at `i0 + c` and `d0 + c`, and the accumulator
at the digits consumed — the fold over `min (d0 + c) 19` of the bytes from
`i0 - d0`, which is where the integer part's digits begin.  `%7` is the count
the head's preheader formed from the entry counters; the run never rewrites it,
and the end-of-lexeme exit reads it as the merge's `%idig.4709716730`, so it is
carried at every iteration. -/
def intRunInv (mem0 : Mem) (p n i0 d0 : Nat) (bs : List UInt8) (r : Nat)
    (s : State) (c : Nat) : Prop :=
  s.pc = "land.lhs.true41" ∧ s.mem = mem0 ∧ c + r = n - i0 ∧ i0 + c < n ∧
  n < 2 ^ 63 ∧ d0 ≤ i0 ∧
  lookupName s.env "%p" = some (.ptr p) ∧
  lookupName s.env "%n" = some (.int 64 (BitVec.ofNat 64 n)) ∧
  readBytes mem0 p n = some bs ∧
  lookupName s.env "%7"
    = some (.int 64 (BitVec.ofNat 64 d0 + BitVec.ofNat 64 n - BitVec.ofNat 64 i0)) ∧
  ((s.pre = some "land.lhs.true41.preheader" ∧
      lookupName s.env "%i.1558" = some (.int 64 (BitVec.ofNat 64 (i0 + c))) ∧
      lookupName s.env "%idig.0560" = some (.int 64 (BitVec.ofNat 64 (d0 + c))) ∧
      lookupName s.env "%ip.0562"
        = some (.int 64 (BitVec.ofNat 64 (digitFold bs (i0 - d0) (min (d0 + c) 19)))))
   ∨ (s.pre = some "if.end62" ∧
      lookupName s.env "%inc64" = some (.int 64 (BitVec.ofNat 64 (i0 + c))) ∧
      lookupName s.env "%inc63" = some (.int 64 (BitVec.ofNat 64 (d0 + c))) ∧
      lookupName s.env "%ip.4"
        = some (.int 64 (BitVec.ofNat 64 (digitFold bs (i0 - d0) (min (d0 + c) 19))))))

/-- A readable trace's byte is present. -/
theorem readByte_of_readBytes_lt {m : Mem} {a n : Nat} {bs : List UInt8}
    (h : readBytes m a n = some bs) {j : Nat} (hj : j < n) :
    ∃ b, readByte m (a + j) = some b :=
  ⟨_, readByte_of_readBytes h hj⟩

/-- The equality test at unequal words. -/
theorem evalICmp_eq_ne {w : Nat} {a b : BitVec w} (h : a ≠ b) : evalICmp .eq a b = 0 := by
  unfold evalICmp
  simp [h]

/-- The equality test at one word. -/
theorem evalICmp_eq_refl {w : Nat} (a : BitVec w) : evalICmp .eq a a = 1 := by
  unfold evalICmp
  simp

/-- The head's edge facts at `i0 + c` and `d0 + c`, as the loop arm reads them. -/
theorem intRun_digit_of_bound {mem0 : Mem} {p n i0 : Nat} {bs : List UInt8} {s : State}
    {c : Nat}
    (hread : readBytes mem0 p n = some bs) (hltn : i0 + c < n)
    (h : intRunAtBound mem0 p n i0 s c = false) :
    ∃ b, readByte mem0 (p + (i0 + c)) = some b :=
  readByte_of_readBytes_lt hread hltn

/-- **The integer run's back edge.**  From the head's test refused — the byte at
the counter is a digit and the counter is more than one short of the length — one
iteration re-enters the head with the counter advanced by one, the accumulator
guard taken or not, and the end-of-lexeme test refused. -/
theorem intRun_step_loop {mem0 : Mem} {p n i0 d0 r : Nat} {bs : List UInt8}
    {s : State} {c : Nat}
    (hinv : intRunInv mem0 p n i0 d0 bs (r + 1) s c)
    (hb : intRunAtBound mem0 p n i0 s c = false) :
    ∃ (e : State) (c' : Nat) (j : Nat), j ≤ 4 ∧ e.pc = "land.lhs.true41" ∧ c < c' ∧
      intRunInv mem0 p n i0 d0 bs r e c' ∧
      ∀ k, runFuel calls (j + k) numFastBody s =
        runFuel calls k numFastBody e := by
  obtain ⟨hpc, hmem, hsum, hltn, hnlt, hd0le, hp, hn, hread, h7, hpre⟩ := hinv
  have hblen : bs.length = n := JsonEntrySteps.readBytes_length mem0 p n hread
  unfold intRunAtBound at hb
  obtain ⟨hnoD, hdig⟩ := Bool.or_eq_false_iff.mp hb
  have hno : ¬ (n - i0 ≤ c + 1) := of_decide_eq_false hnoD
  have hdigitAt : numFastDigitAt mem0 p (i0 + c) = true := by simpa using hdig
  obtain ⟨b, hbyte⟩ := readByte_of_readBytes_lt hread hltn
  have hbyte_s : readByte s.mem (p + (i0 + c)) = some b := by rw [hmem]; exact hbyte
  have hdigitB : IsDigitB b = true := by
    unfold numFastDigitAt at hdigitAt
    rw [hbyte] at hdigitAt
    simpa using hdigitAt
  have hj : i0 + c < 2 ^ 63 := by omega
  have hnext : i0 + c + 1 < n := by omega
  have hnext64 : i0 + c + 1 < 2 ^ 64 := by omega
  have hd0next64 : d0 + c + 1 < 2 ^ 64 := by omega
  have hneqN : BitVec.ofNat 64 (i0 + c + 1) ≠ BitVec.ofNat 64 n := by
    intro h
    have h2 := congrArg BitVec.toNat h
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt hnext64, Nat.mod_eq_of_lt (by omega)] at h2
    omega
  rcases hpre with hent | hback
  · obtain ⟨hpre0, hi, hid, hipv⟩ := hent
    let ip : BitVec 64 := BitVec.ofNat 64 (digitFold bs (i0 - d0) (min (d0 + c) 19))
    let e0 : State := stateAt (intHeadEnv s.env p (i0 + c) b
        (BitVec.ofNat 64 (d0 + c)) ip)
      { s with pc := "while.body52", pre := some "land.lhs.true41" }
    have hstep1 : step calls numFastBody s = .jump e0 :=
      intHead_step_entry_digit (env := s.env) (s := s) (a := p) (j := i0 + c) (b := b)
        (idig := BitVec.ofNat 64 (d0 + c)) (ip := ip) hpc hpre0 hp
        (BlockEval.evalOperand_reg_of s.env s "%i.1558" _ hi)
        (BlockEval.evalOperand_reg_of s.env s "%idig.0560" _ hid)
        (BlockEval.evalOperand_reg_of s.env s "%ip.0562" _ hipv) hj hbyte_s hdigitB
    have hidig0 : lookupName e0.env "%idig.3574"
        = some (.int 64 (BitVec.ofNat 64 (d0 + c))) := by
      simp only [e0, stateAt, intHeadEnv, intHeadPhiEnv]
      block_lk
    by_cases hguard : (BitVec.ofNat 64 (d0 + c)).ult (19#64) = true
    · -- the accumulator guard holds
      let e1 : State := stateAt (intBodyEnv e0.env (BitVec.ofNat 64 (d0 + c)))
          { e0 with pc := "if.then55", pre := some "while.body52" }
      have hstep2 : step calls numFastBody e0 = .jump e1 :=
        intBody_step_taken (env := e0.env) (s := e0) (idig := BitVec.ofNat 64 (d0 + c))
          (by simp only [e0, stateAt]) hidig0 hguard
      have hip1 : lookupName e1.env "%ip.3573" = some (.int 64 ip) := by
        simp only [e1, e0, stateAt, intBodyEnv, intHeadEnv, intHeadPhiEnv]
        block_lk
      have h8 : lookupName e1.env "%8" = some (.int 8 (JsonScanLane.vByte b)) := by
        simp only [e1, e0, stateAt, intBodyEnv, intHeadEnv, intHeadPhiEnv]
        block_lk
      let e2 : State := stateAt (intIfThenEnv e1.env ip b)
          { e1 with pc := "if.end62", pre := some "if.then55" }
      have hstep3 : step calls numFastBody e1 = .jump e2 :=
        intIfThen_step (env := e1.env) (s := e1) (by simp only [e1, stateAt]) hip1 h8
      have hphi : phiIncoming "if.then55"
          [("if.then55", (Operand.reg "%add61")),
           ("while.body52", (Operand.reg "%ip.3573"))] = some (Operand.reg "%add61") := by
        simp only [phiIncoming]; rfl
      have hphiOp : evalOperand (stateAt e2.env e2) (Operand.reg "%add61")
          = some (.int 64
            (ip * 10 + BitVec.ofNat 64 (JsonScanLane.vByte b &&& 0x0f#8).toNat)) := by
        refine BlockEval.evalOperand_reg_of e2.env e2 "%add61" _ ?_
        simp only [e2, e1, stateAt, intIfThenEnv, lookupName_cons_self]
      have hidig2 : lookupName e2.env "%idig.3574"
          = some (.int 64 (BitVec.ofNat 64 (d0 + c))) := by
        simp only [e2, e1, e0, stateAt, intIfThenEnv, intBodyEnv, intHeadEnv,
          intHeadPhiEnv]
        block_lk
      have hi2 : lookupName e2.env "%i.4575"
          = some (.int 64 (BitVec.ofNat 64 (i0 + c))) := by
        simp only [e2, e1, e0, stateAt, intIfThenEnv, intBodyEnv, intHeadEnv,
          intHeadPhiEnv]
        block_lk
      have hn2 : lookupName e2.env "%n" = some (.int 64 (BitVec.ofNat 64 n)) := by
        simp only [e2, e1, e0, stateAt, intIfThenEnv, intBodyEnv, intHeadEnv,
          intHeadPhiEnv]
        block_lk
      have hbits : evalICmp .eq
          (BitVec.ofNat 64 (i0 + c) + (1#64)) (BitVec.ofNat 64 n) = 0 := by
        rw [ofNat64_add_one hnext64]
        exact evalICmp_eq_ne hneqN
      let e3 : State := stateAt
          (intIfEndEnv e2.env
            (ip * 10 + BitVec.ofNat 64 (JsonScanLane.vByte b &&& 0x0f#8).toNat)
            (BitVec.ofNat 64 (d0 + c)) (BitVec.ofNat 64 (i0 + c))
            (BitVec.ofNat 64 n))
          { e2 with pc := "land.lhs.true41", pre := some "if.end62" }
      have hstep4 : step calls numFastBody e2 = .jump e3 :=
        intIfEnd_step_loop (env := e2.env) (s := e2) (by simp only [e2, stateAt])
          (idig := BitVec.ofNat 64 (d0 + c))
          (i := BitVec.ofNat 64 (i0 + c)) (n := BitVec.ofNat 64 n)
          (p := "if.then55") (op := Operand.reg "%add61")
          (ipv := ip * 10 + BitVec.ofNat 64 (JsonScanLane.vByte b &&& 0x0f#8).toNat)
          (by simp only [e2, stateAt]) hphi hphiOp hidig2 hi2 hn2 hbits
      refine ⟨e3, c + 1, 4, by omega, ?_, by omega, ?_, ?_⟩
      · simp only [e3, stateAt]
      · -- the invariant at the new head
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · simp only [e3, stateAt]
        · simp only [e3, stateAt]; exact hmem
        · omega
        · omega
        · exact hnlt
        · exact hd0le
        · simp only [e3, e2, e1, e0, stateAt, intIfEndEnv, intIfThenEnv, intBodyEnv,
            intHeadEnv, intHeadPhiEnv]
          block_lk
        · simp only [e3, e2, e1, e0, stateAt, intIfEndEnv, intIfThenEnv, intBodyEnv,
            intHeadEnv, intHeadPhiEnv]
          block_lk
        · simpa only [e3, stateAt] using hread
        · simp only [e3, e2, e1, e0, stateAt, intIfEndEnv, intIfThenEnv, intBodyEnv,
            intHeadEnv, intHeadPhiEnv]
          block_lk
        · right
          refine ⟨by simp only [e3, stateAt], ?_, ?_, ?_⟩
          · simp only [e3, e2, e1, e0, stateAt, intIfEndEnv, intIfThenEnv, intBodyEnv,
              intHeadEnv, intHeadPhiEnv]
            block_lk
            exact int_succ_eq _ hnext64
          · simp only [e3, e2, e1, e0, stateAt, intIfEndEnv, intIfThenEnv, intBodyEnv,
              intHeadEnv, intHeadPhiEnv]
            block_lk
            exact int_succ_eq _ hd0next64
          · have hbyteD : bs.getD (i0 + c) 0 = b :=
              getD_of_readBytes hread (by omega) hbyte
            have hnew : ip * 10 + BitVec.ofNat 64
                (JsonScanLane.vByte b &&& 0x0f#8).toNat
                = BitVec.ofNat 64
                  (digitFold bs (i0 - d0) (min (d0 + c + 1) 19)) :=
              digitFold_step_at hd0le (ofNat_ult_true (by omega) hguard)
                (by rw [hblen]; exact hltn) hbyteD hdigitB rfl
            simp only [e3, stateAt, intIfEndEnv]
            block_lk
            exact congrArg (fun x : BitVec 64 => some (Value.int 64 x)) hnew
      · intro k
        rw [show 4 + k = 1 + (1 + (1 + (1 + k))) from by omega,
          runFuel_jump_prefix hstep1 (1 + (1 + (1 + k))),
          runFuel_jump_prefix hstep2 (1 + (1 + k)),
          runFuel_jump_prefix hstep3 (1 + k),
          runFuel_jump_prefix hstep4 k]
    · -- the accumulator guard refused
      have hguard' : (BitVec.ofNat 64 (d0 + c)).ult (19#64) = false := by
        cases h : (BitVec.ofNat 64 (d0 + c)).ult (19#64)
        · rfl
        · exact absurd h hguard
      let e1 : State := stateAt (intBodyEnv e0.env (BitVec.ofNat 64 (d0 + c)))
          { e0 with pc := "if.end62", pre := some "while.body52" }
      have hstep2 : step calls numFastBody e0 = .jump e1 :=
        intBody_step_skip (env := e0.env) (s := e0) (idig := BitVec.ofNat 64 (d0 + c))
          (by simp only [e0, stateAt]) hidig0 hguard'
      have hphi : phiIncoming "while.body52"
          [("if.then55", (Operand.reg "%add61")),
           ("while.body52", (Operand.reg "%ip.3573"))] = some (Operand.reg "%ip.3573") := by
        simp only [phiIncoming]; rfl
      have hip1 : lookupName e1.env "%ip.3573" = some (.int 64 ip) := by
        simp only [e1, e0, stateAt, intBodyEnv, intHeadEnv, intHeadPhiEnv]
        block_lk
      have hphiOp : evalOperand (stateAt e1.env e1) (Operand.reg "%ip.3573")
          = some (.int 64 ip) :=
        BlockEval.evalOperand_reg_of e1.env e1 "%ip.3573" _ hip1
      have hidig1 : lookupName e1.env "%idig.3574"
          = some (.int 64 (BitVec.ofNat 64 (d0 + c))) := by
        simp only [e1, e0, stateAt, intBodyEnv, intHeadEnv, intHeadPhiEnv]
        block_lk
      have hi1 : lookupName e1.env "%i.4575"
          = some (.int 64 (BitVec.ofNat 64 (i0 + c))) := by
        simp only [e1, e0, stateAt, intBodyEnv, intHeadEnv, intHeadPhiEnv]
        block_lk
      have hn1 : lookupName e1.env "%n" = some (.int 64 (BitVec.ofNat 64 n)) := by
        simp only [e1, e0, stateAt, intBodyEnv, intHeadEnv, intHeadPhiEnv]
        block_lk
      have hbits : evalICmp .eq
          (BitVec.ofNat 64 (i0 + c) + (1#64)) (BitVec.ofNat 64 n) = 0 := by
        rw [ofNat64_add_one hnext64]
        exact evalICmp_eq_ne hneqN
      let e2 : State := stateAt
          (intIfEndEnv e1.env ip (BitVec.ofNat 64 (d0 + c))
            (BitVec.ofNat 64 (i0 + c)) (BitVec.ofNat 64 n))
          { e1 with pc := "land.lhs.true41", pre := some "if.end62" }
      have hstep3 : step calls numFastBody e1 = .jump e2 :=
        intIfEnd_step_loop (env := e1.env) (s := e1) (by simp only [e1, stateAt])
          (idig := BitVec.ofNat 64 (d0 + c))
          (i := BitVec.ofNat 64 (i0 + c)) (n := BitVec.ofNat 64 n)
          (p := "while.body52") (op := Operand.reg "%ip.3573") (ipv := ip)
          (by simp only [e1, stateAt]) hphi hphiOp hidig1 hi1 hn1 hbits
      refine ⟨e2, c + 1, 3, by omega, ?_, by omega, ?_, ?_⟩
      · simp only [e2, stateAt]
      · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · simp only [e2, stateAt]
        · simp only [e2, stateAt]; exact hmem
        · omega
        · omega
        · exact hnlt
        · exact hd0le
        · simp only [e2, e1, e0, stateAt, intIfEndEnv, intBodyEnv, intHeadEnv,
            intHeadPhiEnv]
          block_lk
        · simp only [e2, e1, e0, stateAt, intIfEndEnv, intBodyEnv, intHeadEnv,
            intHeadPhiEnv]
          block_lk
        · simpa only [e2, stateAt] using hread
        · simp only [e2, e1, e0, stateAt, intIfEndEnv, intBodyEnv, intHeadEnv,
            intHeadPhiEnv]
          block_lk
        · right
          refine ⟨by simp only [e2, stateAt], ?_, ?_, ?_⟩
          · simp only [e2, e1, e0, stateAt, intIfEndEnv, intBodyEnv, intHeadEnv,
              intHeadPhiEnv]
            block_lk
            exact int_succ_eq _ hnext64
          · simp only [e2, e1, e0, stateAt, intIfEndEnv, intBodyEnv, intHeadEnv,
              intHeadPhiEnv]
            block_lk
            exact int_succ_eq _ hd0next64
          · have hfrozen : ip = BitVec.ofNat 64
                (digitFold bs (i0 - d0) (min (d0 + c + 1) 19)) :=
              digitFold_frozen (ofNat_ult_false (by omega) hguard') rfl
            simp only [e2, stateAt, intIfEndEnv]
            block_lk
            exact congrArg (fun x : BitVec 64 => some (Value.int 64 x)) hfrozen
      · intro k
        rw [show 3 + k = 1 + (1 + (1 + k)) from by omega,
          runFuel_jump_prefix hstep1 (1 + (1 + k)),
          runFuel_jump_prefix hstep2 (1 + k),
          runFuel_jump_prefix hstep3 k]
  · obtain ⟨hpre0, hi, hid, hipv⟩ := hback
    let ip : BitVec 64 := BitVec.ofNat 64 (digitFold bs (i0 - d0) (min (d0 + c) 19))
    let e0 : State := stateAt (intHeadEnv s.env p (i0 + c) b
        (BitVec.ofNat 64 (d0 + c)) ip)
      { s with pc := "while.body52", pre := some "land.lhs.true41" }
    have hstep1 : step calls numFastBody s = .jump e0 :=
      intHead_step_back_digit (env := s.env) (s := s) (a := p) (j := i0 + c) (b := b)
        (idig := BitVec.ofNat 64 (d0 + c)) (ip := ip) hpc hpre0 hp
        (BlockEval.evalOperand_reg_of s.env s "%inc64" _ hi)
        (BlockEval.evalOperand_reg_of s.env s "%inc63" _ hid)
        (BlockEval.evalOperand_reg_of s.env s "%ip.4" _ hipv) hj hbyte_s hdigitB
    have hidig0 : lookupName e0.env "%idig.3574"
        = some (.int 64 (BitVec.ofNat 64 (d0 + c))) := by
      simp only [e0, stateAt, intHeadEnv, intHeadPhiEnv]
      block_lk
    by_cases hguard : (BitVec.ofNat 64 (d0 + c)).ult (19#64) = true
    · -- the accumulator guard holds
      let e1 : State := stateAt (intBodyEnv e0.env (BitVec.ofNat 64 (d0 + c)))
          { e0 with pc := "if.then55", pre := some "while.body52" }
      have hstep2 : step calls numFastBody e0 = .jump e1 :=
        intBody_step_taken (env := e0.env) (s := e0) (idig := BitVec.ofNat 64 (d0 + c))
          (by simp only [e0, stateAt]) hidig0 hguard
      have hip1 : lookupName e1.env "%ip.3573" = some (.int 64 ip) := by
        simp only [e1, e0, stateAt, intBodyEnv, intHeadEnv, intHeadPhiEnv]
        block_lk
      have h8 : lookupName e1.env "%8" = some (.int 8 (JsonScanLane.vByte b)) := by
        simp only [e1, e0, stateAt, intBodyEnv, intHeadEnv, intHeadPhiEnv]
        block_lk
      let e2 : State := stateAt (intIfThenEnv e1.env ip b)
          { e1 with pc := "if.end62", pre := some "if.then55" }
      have hstep3 : step calls numFastBody e1 = .jump e2 :=
        intIfThen_step (env := e1.env) (s := e1) (by simp only [e1, stateAt]) hip1 h8
      have hphi : phiIncoming "if.then55"
          [("if.then55", (Operand.reg "%add61")),
           ("while.body52", (Operand.reg "%ip.3573"))] = some (Operand.reg "%add61") := by
        simp only [phiIncoming]; rfl
      have hphiOp : evalOperand (stateAt e2.env e2) (Operand.reg "%add61")
          = some (.int 64
            (ip * 10 + BitVec.ofNat 64 (JsonScanLane.vByte b &&& 0x0f#8).toNat)) := by
        refine BlockEval.evalOperand_reg_of e2.env e2 "%add61" _ ?_
        simp only [e2, e1, stateAt, intIfThenEnv, lookupName_cons_self]
      have hidig2 : lookupName e2.env "%idig.3574"
          = some (.int 64 (BitVec.ofNat 64 (d0 + c))) := by
        simp only [e2, e1, e0, stateAt, intIfThenEnv, intBodyEnv, intHeadEnv,
          intHeadPhiEnv]
        block_lk
      have hi2 : lookupName e2.env "%i.4575"
          = some (.int 64 (BitVec.ofNat 64 (i0 + c))) := by
        simp only [e2, e1, e0, stateAt, intIfThenEnv, intBodyEnv, intHeadEnv,
          intHeadPhiEnv]
        block_lk
      have hn2 : lookupName e2.env "%n" = some (.int 64 (BitVec.ofNat 64 n)) := by
        simp only [e2, e1, e0, stateAt, intIfThenEnv, intBodyEnv, intHeadEnv,
          intHeadPhiEnv]
        block_lk
      have hbits : evalICmp .eq
          (BitVec.ofNat 64 (i0 + c) + (1#64)) (BitVec.ofNat 64 n) = 0 := by
        rw [ofNat64_add_one hnext64]
        exact evalICmp_eq_ne hneqN
      let e3 : State := stateAt
          (intIfEndEnv e2.env
            (ip * 10 + BitVec.ofNat 64 (JsonScanLane.vByte b &&& 0x0f#8).toNat)
            (BitVec.ofNat 64 (d0 + c)) (BitVec.ofNat 64 (i0 + c))
            (BitVec.ofNat 64 n))
          { e2 with pc := "land.lhs.true41", pre := some "if.end62" }
      have hstep4 : step calls numFastBody e2 = .jump e3 :=
        intIfEnd_step_loop (env := e2.env) (s := e2) (by simp only [e2, stateAt])
          (idig := BitVec.ofNat 64 (d0 + c))
          (i := BitVec.ofNat 64 (i0 + c)) (n := BitVec.ofNat 64 n)
          (p := "if.then55") (op := Operand.reg "%add61")
          (ipv := ip * 10 + BitVec.ofNat 64 (JsonScanLane.vByte b &&& 0x0f#8).toNat)
          (by simp only [e2, stateAt]) hphi hphiOp hidig2 hi2 hn2 hbits
      refine ⟨e3, c + 1, 4, by omega, ?_, by omega, ?_, ?_⟩
      · simp only [e3, stateAt]
      · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · simp only [e3, stateAt]
        · simp only [e3, stateAt]; exact hmem
        · omega
        · omega
        · exact hnlt
        · exact hd0le
        · simp only [e3, e2, e1, e0, stateAt, intIfEndEnv, intIfThenEnv, intBodyEnv,
            intHeadEnv, intHeadPhiEnv]
          block_lk
        · simp only [e3, e2, e1, e0, stateAt, intIfEndEnv, intIfThenEnv, intBodyEnv,
            intHeadEnv, intHeadPhiEnv]
          block_lk
        · simpa only [e3, stateAt] using hread
        · simp only [e3, e2, e1, e0, stateAt, intIfEndEnv, intIfThenEnv, intBodyEnv,
            intHeadEnv, intHeadPhiEnv]
          block_lk
        · right
          refine ⟨by simp only [e3, stateAt], ?_, ?_, ?_⟩
          · simp only [e3, e2, e1, e0, stateAt, intIfEndEnv, intIfThenEnv, intBodyEnv,
              intHeadEnv, intHeadPhiEnv]
            block_lk
            exact int_succ_eq _ hnext64
          · simp only [e3, e2, e1, e0, stateAt, intIfEndEnv, intIfThenEnv, intBodyEnv,
              intHeadEnv, intHeadPhiEnv]
            block_lk
            exact int_succ_eq _ hd0next64
          · have hbyteD : bs.getD (i0 + c) 0 = b :=
              getD_of_readBytes hread (by omega) hbyte
            have hnew : ip * 10 + BitVec.ofNat 64
                (JsonScanLane.vByte b &&& 0x0f#8).toNat
                = BitVec.ofNat 64
                  (digitFold bs (i0 - d0) (min (d0 + c + 1) 19)) :=
              digitFold_step_at hd0le (ofNat_ult_true (by omega) hguard)
                (by rw [hblen]; exact hltn) hbyteD hdigitB rfl
            simp only [e3, stateAt, intIfEndEnv]
            block_lk
            exact congrArg (fun x : BitVec 64 => some (Value.int 64 x)) hnew
      · intro k
        rw [show 4 + k = 1 + (1 + (1 + (1 + k))) from by omega,
          runFuel_jump_prefix hstep1 (1 + (1 + (1 + k))),
          runFuel_jump_prefix hstep2 (1 + (1 + k)),
          runFuel_jump_prefix hstep3 (1 + k),
          runFuel_jump_prefix hstep4 k]
    · -- the accumulator guard refused
      have hguard' : (BitVec.ofNat 64 (d0 + c)).ult (19#64) = false := by
        cases h : (BitVec.ofNat 64 (d0 + c)).ult (19#64)
        · rfl
        · exact absurd h hguard
      let e1 : State := stateAt (intBodyEnv e0.env (BitVec.ofNat 64 (d0 + c)))
          { e0 with pc := "if.end62", pre := some "while.body52" }
      have hstep2 : step calls numFastBody e0 = .jump e1 :=
        intBody_step_skip (env := e0.env) (s := e0) (idig := BitVec.ofNat 64 (d0 + c))
          (by simp only [e0, stateAt]) hidig0 hguard'
      have hphi : phiIncoming "while.body52"
          [("if.then55", (Operand.reg "%add61")),
           ("while.body52", (Operand.reg "%ip.3573"))] = some (Operand.reg "%ip.3573") := by
        simp only [phiIncoming]; rfl
      have hip1 : lookupName e1.env "%ip.3573" = some (.int 64 ip) := by
        simp only [e1, e0, stateAt, intBodyEnv, intHeadEnv, intHeadPhiEnv]
        block_lk
      have hphiOp : evalOperand (stateAt e1.env e1) (Operand.reg "%ip.3573")
          = some (.int 64 ip) :=
        BlockEval.evalOperand_reg_of e1.env e1 "%ip.3573" _ hip1
      have hidig1 : lookupName e1.env "%idig.3574"
          = some (.int 64 (BitVec.ofNat 64 (d0 + c))) := by
        simp only [e1, e0, stateAt, intBodyEnv, intHeadEnv, intHeadPhiEnv]
        block_lk
      have hi1 : lookupName e1.env "%i.4575"
          = some (.int 64 (BitVec.ofNat 64 (i0 + c))) := by
        simp only [e1, e0, stateAt, intBodyEnv, intHeadEnv, intHeadPhiEnv]
        block_lk
      have hn1 : lookupName e1.env "%n" = some (.int 64 (BitVec.ofNat 64 n)) := by
        simp only [e1, e0, stateAt, intBodyEnv, intHeadEnv, intHeadPhiEnv]
        block_lk
      have hbits : evalICmp .eq
          (BitVec.ofNat 64 (i0 + c) + (1#64)) (BitVec.ofNat 64 n) = 0 := by
        rw [ofNat64_add_one hnext64]
        exact evalICmp_eq_ne hneqN
      let e2 : State := stateAt
          (intIfEndEnv e1.env ip (BitVec.ofNat 64 (d0 + c))
            (BitVec.ofNat 64 (i0 + c)) (BitVec.ofNat 64 n))
          { e1 with pc := "land.lhs.true41", pre := some "if.end62" }
      have hstep3 : step calls numFastBody e1 = .jump e2 :=
        intIfEnd_step_loop (env := e1.env) (s := e1) (by simp only [e1, stateAt])
          (idig := BitVec.ofNat 64 (d0 + c))
          (i := BitVec.ofNat 64 (i0 + c)) (n := BitVec.ofNat 64 n)
          (p := "while.body52") (op := Operand.reg "%ip.3573") (ipv := ip)
          (by simp only [e1, stateAt]) hphi hphiOp hidig1 hi1 hn1 hbits
      refine ⟨e2, c + 1, 3, by omega, ?_, by omega, ?_, ?_⟩
      · simp only [e2, stateAt]
      · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · simp only [e2, stateAt]
        · simp only [e2, stateAt]; exact hmem
        · omega
        · omega
        · exact hnlt
        · exact hd0le
        · simp only [e2, e1, e0, stateAt, intIfEndEnv, intBodyEnv, intHeadEnv,
            intHeadPhiEnv]
          block_lk
        · simp only [e2, e1, e0, stateAt, intIfEndEnv, intBodyEnv, intHeadEnv,
            intHeadPhiEnv]
          block_lk
        · simpa only [e2, stateAt] using hread
        · simp only [e2, e1, e0, stateAt, intIfEndEnv, intBodyEnv, intHeadEnv,
            intHeadPhiEnv]
          block_lk
        · right
          refine ⟨by simp only [e2, stateAt], ?_, ?_, ?_⟩
          · simp only [e2, e1, e0, stateAt, intIfEndEnv, intBodyEnv, intHeadEnv,
              intHeadPhiEnv]
            block_lk
            exact int_succ_eq _ hnext64
          · simp only [e2, e1, e0, stateAt, intIfEndEnv, intBodyEnv, intHeadEnv,
              intHeadPhiEnv]
            block_lk
            exact int_succ_eq _ hd0next64
          · have hfrozen : ip = BitVec.ofNat 64
                (digitFold bs (i0 - d0) (min (d0 + c + 1) 19)) :=
              digitFold_frozen (ofNat_ult_false (by omega) hguard') rfl
            simp only [e2, stateAt, intIfEndEnv]
            block_lk
            exact congrArg (fun x : BitVec 64 => some (Value.int 64 x)) hfrozen
      · intro k
        rw [show 3 + k = 1 + (1 + (1 + k)) from by omega,
          runFuel_jump_prefix hstep1 (1 + (1 + k)),
          runFuel_jump_prefix hstep2 (1 + k),
          runFuel_jump_prefix hstep3 k]

/-! ### The integer run's exit arm

The head's test holds, so the iteration stops: either the byte at the counter is
not a digit and the head leaves for `if.end68`, or the counter is one short of the
length and the iteration runs `if.end62`'s end-of-lexeme branch into `if.end230`.
The exit carries the counters either way, which is what `ExitWord` reads. -/

/-- The exit's blocks. -/
def intRunExitBlock (e : State) : Prop :=
  e.pc = "if.end68" ∨ e.pc = "if.end230"

/-- The counters the exit hands back, read off `intRunExit`. -/
theorem intRunExit_count (mem0 : Mem) (bs : List UInt8) (p n i0 d0 : Nat) (e : State)
    (h : intRunExit mem0 bs p n i0 d0 e) :
    (∃ i1, e.pc = "if.end68" ∧
      lookupName e.env "%idig.3574"
        = some (.int 64 (BitVec.ofNat 64 (d0 + (i1 - i0))))) ∨
    (e.pc = "if.end230" ∧
      lookupName e.env "%inc63"
        = some (.int 64 (BitVec.ofNat 64 (d0 + (n - i0))))) := by
  rcases h with ⟨hpc, _, _, _, i1, _, _, _, hcnt, _, _, _, _⟩
    | ⟨hpc, _, _, _, _, _, hcnt, _, _⟩
  · exact Or.inl ⟨i1, hpc, hcnt⟩
  · exact Or.inr ⟨hpc, hcnt⟩

/-- At the bound with the counter short of the length, the byte is not a
digit. -/
theorem intRun_bound_nondigit {mem0 : Mem} {p n i0 : Nat} {bs : List UInt8}
    {s : State} {c : Nat} (hread : readBytes mem0 p n = some bs) (hltn : i0 + c < n)
    (hb : intRunAtBound mem0 p n i0 s c = true) (hno : ¬ n - i0 ≤ c + 1) :
    ∃ b, readByte mem0 (p + (i0 + c)) = some b ∧ IsDigitB b = false := by
  unfold intRunAtBound at hb
  rcases Bool.or_eq_true_iff.mp hb with hle | hdig
  · exact absurd (of_decide_eq_true hle) hno
  · obtain ⟨b, hb'⟩ := readByte_of_readBytes_lt hread hltn
    have hfalse : numFastDigitAt mem0 p (i0 + c) = false := by simpa using hdig
    refine ⟨b, hb', ?_⟩
    unfold numFastDigitAt at hfalse
    rw [hb'] at hfalse
    simpa using hfalse

/-- **The integer run's exit.**  From the head's test taken — either the counter
is one short of the length, or the byte at it is not a digit — one iteration
leaves at an exit block carrying the counters.  The digit case spends four steps
(the head, `while.body52`, `if.then55` when its guard holds, and `if.end62`); the
non-digit case spends the head's step alone. -/
theorem intRun_step_exit {mem0 : Mem} {p n i0 d0 r : Nat} {bs : List UInt8}
    {s : State} {c : Nat}
    (hinv : intRunInv mem0 p n i0 d0 bs r s c)
    (hb : intRunAtBound mem0 p n i0 s c = true) :
    ∃ (e : State) (j : Nat), j ≤ 4 ∧ intRunExitBlock e ∧
      intRunExit mem0 bs p n i0 d0 e ∧
      ∀ k, runFuel calls (j + k) numFastBody s =
        runFuel calls k numFastBody e := by
  obtain ⟨hpc, hmem, hsum, hltn, hnlt, hd0le, hp, hn, hread, h7, hpre⟩ := hinv
  have hblen : bs.length = n := JsonEntrySteps.readBytes_length mem0 p n hread
  have hd0next64 : d0 + c + 1 < 2 ^ 64 := by omega
  obtain ⟨b, hbyte⟩ := readByte_of_readBytes_lt hread hltn
  have hbyte_s : readByte s.mem (p + (i0 + c)) = some b := by rw [hmem]; exact hbyte
  have hj : i0 + c < 2 ^ 63 := by omega
  by_cases hle : n - i0 ≤ c + 1
  · -- the counter is one short of the length: the end-of-lexeme branch exits
    have hnext64 : i0 + c + 1 < 2 ^ 64 := by omega
    have h_eq : i0 + c + 1 = n := by omega
    have hbits : evalICmp .eq (BitVec.ofNat 64 (i0 + c) + (1#64))
        (BitVec.ofNat 64 n) = 1 := by
      rw [ofNat64_add_one hnext64, show i0 + c + 1 = n from h_eq]
      exact evalICmp_eq_refl _
    have hcnt64 : d0 + (i0 + c + 1 - i0) = d0 + c + 1 := by omega
    by_cases hdigit : IsDigitB b = true
    · -- the byte is a digit: the iteration reaches `if.end230` at `i0 + c + 1`
      rcases hpre with hent | hback
      · obtain ⟨hpre0, hi, hid, hipv⟩ := hent
        let ip : BitVec 64 := BitVec.ofNat 64 (digitFold bs (i0 - d0) (min (d0 + c) 19))
        let e0 : State := stateAt (intHeadEnv s.env p (i0 + c) b
            (BitVec.ofNat 64 (d0 + c)) ip)
          { s with pc := "while.body52", pre := some "land.lhs.true41" }
        have hstep1 : step calls numFastBody s = .jump e0 :=
          intHead_step_entry_digit (env := s.env) (s := s) (a := p) (j := i0 + c)
            (b := b) (idig := BitVec.ofNat 64 (d0 + c)) (ip := ip) hpc hpre0 hp
            (BlockEval.evalOperand_reg_of s.env s "%i.1558" _ hi)
            (BlockEval.evalOperand_reg_of s.env s "%idig.0560" _ hid)
            (BlockEval.evalOperand_reg_of s.env s "%ip.0562" _ hipv) hj hbyte_s hdigit
        have hidig0 : lookupName e0.env "%idig.3574"
            = some (.int 64 (BitVec.ofNat 64 (d0 + c))) := by
          simp only [e0, stateAt, intHeadEnv, intHeadPhiEnv]
          block_lk
        by_cases hguard : (BitVec.ofNat 64 (d0 + c)).ult (19#64) = true
        · let e1 : State := stateAt (intBodyEnv e0.env (BitVec.ofNat 64 (d0 + c)))
              { e0 with pc := "if.then55", pre := some "while.body52" }
          have hstep2 : step calls numFastBody e0 = .jump e1 :=
            intBody_step_taken (env := e0.env) (s := e0)
              (idig := BitVec.ofNat 64 (d0 + c)) (by simp only [e0, stateAt])
              hidig0 hguard
          have hip1 : lookupName e1.env "%ip.3573" = some (.int 64 ip) := by
            simp only [e1, e0, stateAt, intBodyEnv, intHeadEnv, intHeadPhiEnv]
            block_lk
          have h8 : lookupName e1.env "%8" = some (.int 8 (JsonScanLane.vByte b)) := by
            simp only [e1, e0, stateAt, intBodyEnv, intHeadEnv, intHeadPhiEnv]
            block_lk
          let e2 : State := stateAt (intIfThenEnv e1.env ip b)
              { e1 with pc := "if.end62", pre := some "if.then55" }
          have hstep3 : step calls numFastBody e1 = .jump e2 :=
            intIfThen_step (env := e1.env) (s := e1) (by simp only [e1, stateAt])
              hip1 h8
          have hphi : phiIncoming "if.then55"
              [("if.then55", (Operand.reg "%add61")),
               ("while.body52", (Operand.reg "%ip.3573"))] = some (Operand.reg "%add61") := by
            simp only [phiIncoming]; rfl
          have hphiOp : evalOperand (stateAt e2.env e2) (Operand.reg "%add61")
              = some (.int 64
                (ip * 10 + BitVec.ofNat 64
                  (JsonScanLane.vByte b &&& 0x0f#8).toNat)) := by
            refine BlockEval.evalOperand_reg_of e2.env e2 "%add61" _ ?_
            simp only [e2, e1, stateAt, intIfThenEnv, lookupName_cons_self]
          have hidig2 : lookupName e2.env "%idig.3574"
              = some (.int 64 (BitVec.ofNat 64 (d0 + c))) := by
            simp only [e2, e1, e0, stateAt, intIfThenEnv, intBodyEnv, intHeadEnv,
              intHeadPhiEnv]
            block_lk
          have hi2 : lookupName e2.env "%i.4575"
              = some (.int 64 (BitVec.ofNat 64 (i0 + c))) := by
            simp only [e2, e1, e0, stateAt, intIfThenEnv, intBodyEnv, intHeadEnv,
              intHeadPhiEnv]
            block_lk
          have hn2 : lookupName e2.env "%n"
              = some (.int 64 (BitVec.ofNat 64 n)) := by
            simp only [e2, e1, e0, stateAt, intIfThenEnv, intBodyEnv, intHeadEnv,
              intHeadPhiEnv]
            block_lk
          let e3 : State := stateAt
              (intIfEndEnv e2.env
                (ip * 10 + BitVec.ofNat 64 (JsonScanLane.vByte b &&& 0x0f#8).toNat)
                (BitVec.ofNat 64 (d0 + c)) (BitVec.ofNat 64 (i0 + c))
                (BitVec.ofNat 64 n))
              { e2 with pc := "if.end230", pre := some "if.end62" }
          have hstep4 : step calls numFastBody e2 = .jump e3 :=
            intIfEnd_step_exit (env := e2.env) (s := e2)
              (idig := BitVec.ofNat 64 (d0 + c))
              (i := BitVec.ofNat 64 (i0 + c)) (n := BitVec.ofNat 64 n)
              (p := "if.then55") (op := Operand.reg "%add61")
              (ipv := ip * 10 + BitVec.ofNat 64
                (JsonScanLane.vByte b &&& 0x0f#8).toNat)
              (by simp only [e2, stateAt]) (by simp only [e2, stateAt]) hphi hphiOp
              hidig2 hi2 hn2 hbits
          refine ⟨e3, 4, by omega, Or.inr (by simp only [e3, stateAt]), ?_, ?_⟩
          · refine Or.inr ⟨by simp only [e3, stateAt], by simp only [e3, stateAt], ?_⟩
            refine ⟨by omega, ?_, ?_, ?_, ?_, ?_, ?_⟩
            · simp only [e3, e2, e1, e0, stateAt, intIfEndEnv, intIfThenEnv, intBodyEnv,
                intHeadEnv, intHeadPhiEnv]
              block_lk
            · simp only [e3, e2, e1, e0, stateAt, intIfEndEnv, intIfThenEnv, intBodyEnv,
                intHeadEnv, intHeadPhiEnv]
              block_lk
            · rw [← h_eq]
              simp only [e3, stateAt, intIfEndEnv]
              block_lk
              exact int_succ_eq _ hnext64
            · rw [← h_eq]
              simp only [e3, stateAt, intIfEndEnv]
              rw [hcnt64]
              block_lk
              exact int_succ_eq _ hd0next64
            · have hbyteD : bs.getD (i0 + c) 0 = b :=
                getD_of_readBytes hread (by omega) hbyte
              have hval : ip * 10 + BitVec.ofNat 64
                  (JsonScanLane.vByte b &&& 0x0f#8).toNat
                  = BitVec.ofNat 64
                    (digitFold bs (i0 - d0) (min (d0 + (i0 + c + 1 - i0)) 19)) := by
                rw [hcnt64]
                exact digitFold_step_at hd0le (ofNat_ult_true (by omega) hguard)
                  (by rw [hblen]; omega) hbyteD hdigit rfl
              rw [← h_eq]
              simp only [e3, stateAt, intIfEndEnv]
              block_lk
              exact congrArg (fun x : BitVec 64 => some (Value.int 64 x)) hval
            · simp only [e3, e2, e1, e0, stateAt, intIfEndEnv, intIfThenEnv, intBodyEnv,
                intHeadEnv, intHeadPhiEnv]
              block_lk
          · intro k
            rw [show 4 + k = 1 + (1 + (1 + (1 + k))) from by omega,
              runFuel_jump_prefix hstep1 (1 + (1 + (1 + k))),
              runFuel_jump_prefix hstep2 (1 + (1 + k)),
              runFuel_jump_prefix hstep3 (1 + k),
              runFuel_jump_prefix hstep4 k]
        · have hguard' : (BitVec.ofNat 64 (d0 + c)).ult (19#64) = false := by
            cases h : (BitVec.ofNat 64 (d0 + c)).ult (19#64)
            · rfl
            · exact absurd h hguard
          let e1 : State := stateAt (intBodyEnv e0.env (BitVec.ofNat 64 (d0 + c)))
              { e0 with pc := "if.end62", pre := some "while.body52" }
          have hstep2 : step calls numFastBody e0 = .jump e1 :=
            intBody_step_skip (env := e0.env) (s := e0)
              (idig := BitVec.ofNat 64 (d0 + c)) (by simp only [e0, stateAt])
              hidig0 hguard'
          have hphi : phiIncoming "while.body52"
              [("if.then55", (Operand.reg "%add61")),
               ("while.body52", (Operand.reg "%ip.3573"))] = some (Operand.reg "%ip.3573") := by
            simp only [phiIncoming]; rfl
          have hip1 : lookupName e1.env "%ip.3573" = some (.int 64 ip) := by
            simp only [e1, e0, stateAt, intBodyEnv, intHeadEnv, intHeadPhiEnv]
            block_lk
          have hphiOp : evalOperand (stateAt e1.env e1) (Operand.reg "%ip.3573")
              = some (.int 64 ip) :=
            BlockEval.evalOperand_reg_of e1.env e1 "%ip.3573" _ hip1
          have hidig1 : lookupName e1.env "%idig.3574"
              = some (.int 64 (BitVec.ofNat 64 (d0 + c))) := by
            simp only [e1, e0, stateAt, intBodyEnv, intHeadEnv, intHeadPhiEnv]
            block_lk
          have hi1 : lookupName e1.env "%i.4575"
              = some (.int 64 (BitVec.ofNat 64 (i0 + c))) := by
            simp only [e1, e0, stateAt, intBodyEnv, intHeadEnv, intHeadPhiEnv]
            block_lk
          have hn1 : lookupName e1.env "%n"
              = some (.int 64 (BitVec.ofNat 64 n)) := by
            simp only [e1, e0, stateAt, intBodyEnv, intHeadEnv, intHeadPhiEnv]
            block_lk
          let e2 : State := stateAt
              (intIfEndEnv e1.env ip (BitVec.ofNat 64 (d0 + c))
                (BitVec.ofNat 64 (i0 + c)) (BitVec.ofNat 64 n))
              { e1 with pc := "if.end230", pre := some "if.end62" }
          have hstep3 : step calls numFastBody e1 = .jump e2 :=
            intIfEnd_step_exit (env := e1.env) (s := e1)
              (idig := BitVec.ofNat 64 (d0 + c))
              (i := BitVec.ofNat 64 (i0 + c)) (n := BitVec.ofNat 64 n)
              (p := "while.body52") (op := Operand.reg "%ip.3573") (ipv := ip)
              (by simp only [e1, stateAt]) (by simp only [e1, stateAt]) hphi hphiOp
              hidig1 hi1 hn1 hbits
          refine ⟨e2, 3, by omega, Or.inr (by simp only [e2, stateAt]), ?_, ?_⟩
          · refine Or.inr ⟨by simp only [e2, stateAt], by simp only [e2, stateAt], ?_⟩
            refine ⟨by omega, ?_, ?_, ?_, ?_, ?_, ?_⟩
            · simp only [e2, e1, e0, stateAt, intIfEndEnv, intBodyEnv, intHeadEnv,
                intHeadPhiEnv]
              block_lk
            · simp only [e2, e1, e0, stateAt, intIfEndEnv, intBodyEnv, intHeadEnv,
                intHeadPhiEnv]
              block_lk
            · rw [← h_eq]
              simp only [e2, stateAt, intIfEndEnv]
              block_lk
              exact int_succ_eq _ hnext64
            · rw [← h_eq]
              simp only [e2, stateAt, intIfEndEnv]
              rw [hcnt64]
              block_lk
              exact int_succ_eq _ hd0next64
            · have hval : ip = BitVec.ofNat 64
                  (digitFold bs (i0 - d0) (min (d0 + (i0 + c + 1 - i0)) 19)) := by
                rw [hcnt64]
                exact digitFold_frozen (ofNat_ult_false (by omega) hguard') rfl
              rw [← h_eq]
              simp only [e2, stateAt, intIfEndEnv]
              block_lk
              exact congrArg (fun x : BitVec 64 => some (Value.int 64 x)) hval
            · simp only [e2, e1, e0, stateAt, intIfEndEnv, intBodyEnv, intHeadEnv,
                intHeadPhiEnv]
              block_lk
          · intro k
            rw [show 3 + k = 1 + (1 + (1 + k)) from by omega,
              runFuel_jump_prefix hstep1 (1 + (1 + k)),
              runFuel_jump_prefix hstep2 (1 + k),
              runFuel_jump_prefix hstep3 k]
      · obtain ⟨hpre0, hi, hid, hipv⟩ := hback
        let ip : BitVec 64 := BitVec.ofNat 64 (digitFold bs (i0 - d0) (min (d0 + c) 19))
        let e0 : State := stateAt (intHeadEnv s.env p (i0 + c) b
            (BitVec.ofNat 64 (d0 + c)) ip)
          { s with pc := "while.body52", pre := some "land.lhs.true41" }
        have hstep1 : step calls numFastBody s = .jump e0 :=
          intHead_step_back_digit (env := s.env) (s := s) (a := p) (j := i0 + c)
            (b := b) (idig := BitVec.ofNat 64 (d0 + c)) (ip := ip) hpc hpre0 hp
            (BlockEval.evalOperand_reg_of s.env s "%inc64" _ hi)
            (BlockEval.evalOperand_reg_of s.env s "%inc63" _ hid)
            (BlockEval.evalOperand_reg_of s.env s "%ip.4" _ hipv) hj hbyte_s hdigit
        have hidig0 : lookupName e0.env "%idig.3574"
            = some (.int 64 (BitVec.ofNat 64 (d0 + c))) := by
          simp only [e0, stateAt, intHeadEnv, intHeadPhiEnv]
          block_lk
        by_cases hguard : (BitVec.ofNat 64 (d0 + c)).ult (19#64) = true
        · let e1 : State := stateAt (intBodyEnv e0.env (BitVec.ofNat 64 (d0 + c)))
              { e0 with pc := "if.then55", pre := some "while.body52" }
          have hstep2 : step calls numFastBody e0 = .jump e1 :=
            intBody_step_taken (env := e0.env) (s := e0)
              (idig := BitVec.ofNat 64 (d0 + c)) (by simp only [e0, stateAt])
              hidig0 hguard
          have hip1 : lookupName e1.env "%ip.3573" = some (.int 64 ip) := by
            simp only [e1, e0, stateAt, intBodyEnv, intHeadEnv, intHeadPhiEnv]
            block_lk
          have h8 : lookupName e1.env "%8" = some (.int 8 (JsonScanLane.vByte b)) := by
            simp only [e1, e0, stateAt, intBodyEnv, intHeadEnv, intHeadPhiEnv]
            block_lk
          let e2 : State := stateAt (intIfThenEnv e1.env ip b)
              { e1 with pc := "if.end62", pre := some "if.then55" }
          have hstep3 : step calls numFastBody e1 = .jump e2 :=
            intIfThen_step (env := e1.env) (s := e1) (by simp only [e1, stateAt])
              hip1 h8
          have hphi : phiIncoming "if.then55"
              [("if.then55", (Operand.reg "%add61")),
               ("while.body52", (Operand.reg "%ip.3573"))] = some (Operand.reg "%add61") := by
            simp only [phiIncoming]; rfl
          have hphiOp : evalOperand (stateAt e2.env e2) (Operand.reg "%add61")
              = some (.int 64
                (ip * 10 + BitVec.ofNat 64
                  (JsonScanLane.vByte b &&& 0x0f#8).toNat)) := by
            refine BlockEval.evalOperand_reg_of e2.env e2 "%add61" _ ?_
            simp only [e2, e1, stateAt, intIfThenEnv, lookupName_cons_self]
          have hidig2 : lookupName e2.env "%idig.3574"
              = some (.int 64 (BitVec.ofNat 64 (d0 + c))) := by
            simp only [e2, e1, e0, stateAt, intIfThenEnv, intBodyEnv, intHeadEnv,
              intHeadPhiEnv]
            block_lk
          have hi2 : lookupName e2.env "%i.4575"
              = some (.int 64 (BitVec.ofNat 64 (i0 + c))) := by
            simp only [e2, e1, e0, stateAt, intIfThenEnv, intBodyEnv, intHeadEnv,
              intHeadPhiEnv]
            block_lk
          have hn2 : lookupName e2.env "%n"
              = some (.int 64 (BitVec.ofNat 64 n)) := by
            simp only [e2, e1, e0, stateAt, intIfThenEnv, intBodyEnv, intHeadEnv,
              intHeadPhiEnv]
            block_lk
          let e3 : State := stateAt
              (intIfEndEnv e2.env
                (ip * 10 + BitVec.ofNat 64 (JsonScanLane.vByte b &&& 0x0f#8).toNat)
                (BitVec.ofNat 64 (d0 + c)) (BitVec.ofNat 64 (i0 + c))
                (BitVec.ofNat 64 n))
              { e2 with pc := "if.end230", pre := some "if.end62" }
          have hstep4 : step calls numFastBody e2 = .jump e3 :=
            intIfEnd_step_exit (env := e2.env) (s := e2)
              (idig := BitVec.ofNat 64 (d0 + c))
              (i := BitVec.ofNat 64 (i0 + c)) (n := BitVec.ofNat 64 n)
              (p := "if.then55") (op := Operand.reg "%add61")
              (ipv := ip * 10 + BitVec.ofNat 64
                (JsonScanLane.vByte b &&& 0x0f#8).toNat)
              (by simp only [e2, stateAt]) (by simp only [e2, stateAt]) hphi hphiOp
              hidig2 hi2 hn2 hbits
          refine ⟨e3, 4, by omega, Or.inr (by simp only [e3, stateAt]), ?_, ?_⟩
          · refine Or.inr ⟨by simp only [e3, stateAt], by simp only [e3, stateAt], ?_⟩
            refine ⟨by omega, ?_, ?_, ?_, ?_, ?_, ?_⟩
            · simp only [e3, e2, e1, e0, stateAt, intIfEndEnv, intIfThenEnv, intBodyEnv,
                intHeadEnv, intHeadPhiEnv]
              block_lk
            · simp only [e3, e2, e1, e0, stateAt, intIfEndEnv, intIfThenEnv, intBodyEnv,
                intHeadEnv, intHeadPhiEnv]
              block_lk
            · rw [← h_eq]
              simp only [e3, stateAt, intIfEndEnv]
              block_lk
              exact int_succ_eq _ hnext64
            · rw [← h_eq]
              simp only [e3, stateAt, intIfEndEnv]
              rw [hcnt64]
              block_lk
              exact int_succ_eq _ hd0next64
            · have hbyteD : bs.getD (i0 + c) 0 = b :=
                getD_of_readBytes hread (by omega) hbyte
              have hval : ip * 10 + BitVec.ofNat 64
                  (JsonScanLane.vByte b &&& 0x0f#8).toNat
                  = BitVec.ofNat 64
                    (digitFold bs (i0 - d0) (min (d0 + (i0 + c + 1 - i0)) 19)) := by
                rw [hcnt64]
                exact digitFold_step_at hd0le (ofNat_ult_true (by omega) hguard)
                  (by rw [hblen]; omega) hbyteD hdigit rfl
              rw [← h_eq]
              simp only [e3, stateAt, intIfEndEnv]
              block_lk
              exact congrArg (fun x : BitVec 64 => some (Value.int 64 x)) hval
            · simp only [e3, e2, e1, e0, stateAt, intIfEndEnv, intIfThenEnv, intBodyEnv,
                intHeadEnv, intHeadPhiEnv]
              block_lk
          · intro k
            rw [show 4 + k = 1 + (1 + (1 + (1 + k))) from by omega,
              runFuel_jump_prefix hstep1 (1 + (1 + (1 + k))),
              runFuel_jump_prefix hstep2 (1 + (1 + k)),
              runFuel_jump_prefix hstep3 (1 + k),
              runFuel_jump_prefix hstep4 k]
        · have hguard' : (BitVec.ofNat 64 (d0 + c)).ult (19#64) = false := by
            cases h : (BitVec.ofNat 64 (d0 + c)).ult (19#64)
            · rfl
            · exact absurd h hguard
          let e1 : State := stateAt (intBodyEnv e0.env (BitVec.ofNat 64 (d0 + c)))
              { e0 with pc := "if.end62", pre := some "while.body52" }
          have hstep2 : step calls numFastBody e0 = .jump e1 :=
            intBody_step_skip (env := e0.env) (s := e0)
              (idig := BitVec.ofNat 64 (d0 + c)) (by simp only [e0, stateAt])
              hidig0 hguard'
          have hphi : phiIncoming "while.body52"
              [("if.then55", (Operand.reg "%add61")),
               ("while.body52", (Operand.reg "%ip.3573"))] = some (Operand.reg "%ip.3573") := by
            simp only [phiIncoming]; rfl
          have hip1 : lookupName e1.env "%ip.3573" = some (.int 64 ip) := by
            simp only [e1, e0, stateAt, intBodyEnv, intHeadEnv, intHeadPhiEnv]
            block_lk
          have hphiOp : evalOperand (stateAt e1.env e1) (Operand.reg "%ip.3573")
              = some (.int 64 ip) :=
            BlockEval.evalOperand_reg_of e1.env e1 "%ip.3573" _ hip1
          have hidig1 : lookupName e1.env "%idig.3574"
              = some (.int 64 (BitVec.ofNat 64 (d0 + c))) := by
            simp only [e1, e0, stateAt, intBodyEnv, intHeadEnv, intHeadPhiEnv]
            block_lk
          have hi1 : lookupName e1.env "%i.4575"
              = some (.int 64 (BitVec.ofNat 64 (i0 + c))) := by
            simp only [e1, e0, stateAt, intBodyEnv, intHeadEnv, intHeadPhiEnv]
            block_lk
          have hn1 : lookupName e1.env "%n"
              = some (.int 64 (BitVec.ofNat 64 n)) := by
            simp only [e1, e0, stateAt, intBodyEnv, intHeadEnv, intHeadPhiEnv]
            block_lk
          let e2 : State := stateAt
              (intIfEndEnv e1.env ip (BitVec.ofNat 64 (d0 + c))
                (BitVec.ofNat 64 (i0 + c)) (BitVec.ofNat 64 n))
              { e1 with pc := "if.end230", pre := some "if.end62" }
          have hstep3 : step calls numFastBody e1 = .jump e2 :=
            intIfEnd_step_exit (env := e1.env) (s := e1)
              (idig := BitVec.ofNat 64 (d0 + c))
              (i := BitVec.ofNat 64 (i0 + c)) (n := BitVec.ofNat 64 n)
              (p := "while.body52") (op := Operand.reg "%ip.3573") (ipv := ip)
              (by simp only [e1, stateAt]) (by simp only [e1, stateAt]) hphi hphiOp
              hidig1 hi1 hn1 hbits
          refine ⟨e2, 3, by omega, Or.inr (by simp only [e2, stateAt]), ?_, ?_⟩
          · refine Or.inr ⟨by simp only [e2, stateAt], by simp only [e2, stateAt], ?_⟩
            refine ⟨by omega, ?_, ?_, ?_, ?_, ?_, ?_⟩
            · simp only [e2, e1, e0, stateAt, intIfEndEnv, intBodyEnv, intHeadEnv,
                intHeadPhiEnv]
              block_lk
            · simp only [e2, e1, e0, stateAt, intIfEndEnv, intBodyEnv, intHeadEnv,
                intHeadPhiEnv]
              block_lk
            · rw [← h_eq]
              simp only [e2, stateAt, intIfEndEnv]
              block_lk
              exact int_succ_eq _ hnext64
            · rw [← h_eq]
              simp only [e2, stateAt, intIfEndEnv]
              rw [hcnt64]
              block_lk
              exact int_succ_eq _ hd0next64
            · have hval : ip = BitVec.ofNat 64
                  (digitFold bs (i0 - d0) (min (d0 + (i0 + c + 1 - i0)) 19)) := by
                rw [hcnt64]
                exact digitFold_frozen (ofNat_ult_false (by omega) hguard') rfl
              rw [← h_eq]
              simp only [e2, stateAt, intIfEndEnv]
              block_lk
              exact congrArg (fun x : BitVec 64 => some (Value.int 64 x)) hval
            · simp only [e2, e1, e0, stateAt, intIfEndEnv, intBodyEnv, intHeadEnv,
                intHeadPhiEnv]
              block_lk
          · intro k
            rw [show 3 + k = 1 + (1 + (1 + k)) from by omega,
              runFuel_jump_prefix hstep1 (1 + (1 + k)),
              runFuel_jump_prefix hstep2 (1 + k),
              runFuel_jump_prefix hstep3 k]
    · -- the byte is not a digit: the head leaves for `if.end68`
        have hdigit' : IsDigitB b = false := by
          cases h : IsDigitB b
          · rfl
          · exact absurd h hdigit
        rcases hpre with hent | hback
        · obtain ⟨hpre0, hi, hid, hipv⟩ := hent
          let ip : BitVec 64 := BitVec.ofNat 64 (digitFold bs (i0 - d0) (min (d0 + c) 19))
          let e0 : State := stateAt (intHeadEnv s.env p (i0 + c) b
              (BitVec.ofNat 64 (d0 + c)) ip)
            { s with pc := "if.end68", pre := some "land.lhs.true41" }
          have hstep1 : step calls numFastBody s = .jump e0 :=
            intHead_step_entry_nondigit (env := s.env) (s := s) (a := p) (j := i0 + c)
              (b := b) (idig := BitVec.ofNat 64 (d0 + c)) (ip := ip) hpc hpre0 hp
              (BlockEval.evalOperand_reg_of s.env s "%i.1558" _ hi)
              (BlockEval.evalOperand_reg_of s.env s "%idig.0560" _ hid)
              (BlockEval.evalOperand_reg_of s.env s "%ip.0562" _ hipv) hj hbyte_s hdigit'
          refine ⟨e0, 1, by omega, Or.inl (by simp only [e0, stateAt]), ?_, ?_⟩
          · refine Or.inl ⟨by simp only [e0, stateAt], by simp only [e0, stateAt],
              by simp only [e0, stateAt, intHeadEnv, intHeadPhiEnv]; block_lk,
              by simp only [e0, stateAt, intHeadEnv, intHeadPhiEnv]; block_lk,
              i0 + c, by omega, hltn, ?_, ?_, ?_,
              b, by rw [← hmem]; exact hbyte_s, hdigit'⟩
            · simp only [e0, stateAt, intHeadEnv, intHeadPhiEnv]
              block_lk
            · simp only [e0, stateAt, intHeadEnv, intHeadPhiEnv]
              rw [show d0 + (i0 + c - i0) = d0 + c from by omega]
              block_lk
            · have hval : ip = BitVec.ofNat 64
                  (digitFold bs (i0 - d0) (min (d0 + (i0 + c - i0)) 19)) := by
                rw [show d0 + (i0 + c - i0) = d0 + c from by omega]
              simp only [e0, stateAt, intHeadEnv, intHeadPhiEnv]
              block_lk
              exact congrArg (fun x : BitVec 64 => some (Value.int 64 x)) hval
          · intro k
            rw [runFuel_jump_prefix hstep1 k]
        · obtain ⟨hpre0, hi, hid, hipv⟩ := hback
          let ip : BitVec 64 := BitVec.ofNat 64 (digitFold bs (i0 - d0) (min (d0 + c) 19))
          let e0 : State := stateAt (intHeadEnv s.env p (i0 + c) b
              (BitVec.ofNat 64 (d0 + c)) ip)
            { s with pc := "if.end68", pre := some "land.lhs.true41" }
          have hstep1 : step calls numFastBody s = .jump e0 :=
            intHead_step_back_nondigit (env := s.env) (s := s) (a := p) (j := i0 + c)
              (b := b) (idig := BitVec.ofNat 64 (d0 + c)) (ip := ip) hpc hpre0 hp
              (BlockEval.evalOperand_reg_of s.env s "%inc64" _ hi)
              (BlockEval.evalOperand_reg_of s.env s "%inc63" _ hid)
              (BlockEval.evalOperand_reg_of s.env s "%ip.4" _ hipv) hj hbyte_s hdigit'
          refine ⟨e0, 1, by omega, Or.inl (by simp only [e0, stateAt]), ?_, ?_⟩
          · refine Or.inl ⟨by simp only [e0, stateAt], by simp only [e0, stateAt],
              by simp only [e0, stateAt, intHeadEnv, intHeadPhiEnv]; block_lk,
              by simp only [e0, stateAt, intHeadEnv, intHeadPhiEnv]; block_lk,
              i0 + c, by omega, hltn, ?_, ?_, ?_,
              b, by rw [← hmem]; exact hbyte_s, hdigit'⟩
            · simp only [e0, stateAt, intHeadEnv, intHeadPhiEnv]
              block_lk
            · simp only [e0, stateAt, intHeadEnv, intHeadPhiEnv]
              rw [show d0 + (i0 + c - i0) = d0 + c from by omega]
              block_lk
            · have hval : ip = BitVec.ofNat 64
                  (digitFold bs (i0 - d0) (min (d0 + (i0 + c - i0)) 19)) := by
                rw [show d0 + (i0 + c - i0) = d0 + c from by omega]
              simp only [e0, stateAt, intHeadEnv, intHeadPhiEnv]
              block_lk
              exact congrArg (fun x : BitVec 64 => some (Value.int 64 x)) hval
          · intro k
            rw [runFuel_jump_prefix hstep1 k]
  · -- the counter is not at the bound: the byte is not a digit
    obtain ⟨b', hbyte', hdigit'⟩ :=
      intRun_bound_nondigit hread hltn hb hle
    have hbyte'_s : readByte s.mem (p + (i0 + c)) = some b' := by rw [hmem]; exact hbyte'
    have hbb : b = b' := Option.some.inj (hbyte.symm.trans hbyte')
    subst hbb
    rcases hpre with hent | hback
    · obtain ⟨hpre0, hi, hid, hipv⟩ := hent
      let ip : BitVec 64 := BitVec.ofNat 64 (digitFold bs (i0 - d0) (min (d0 + c) 19))
      let e0 : State := stateAt (intHeadEnv s.env p (i0 + c) b
          (BitVec.ofNat 64 (d0 + c)) ip)
        { s with pc := "if.end68", pre := some "land.lhs.true41" }
      have hstep1 : step calls numFastBody s = .jump e0 :=
        intHead_step_entry_nondigit (env := s.env) (s := s) (a := p) (j := i0 + c)
          (b := b) (idig := BitVec.ofNat 64 (d0 + c)) (ip := ip) hpc hpre0 hp
          (BlockEval.evalOperand_reg_of s.env s "%i.1558" _ hi)
          (BlockEval.evalOperand_reg_of s.env s "%idig.0560" _ hid)
          (BlockEval.evalOperand_reg_of s.env s "%ip.0562" _ hipv) hj hbyte_s hdigit'
      refine ⟨e0, 1, by omega, Or.inl (by simp only [e0, stateAt]), ?_, ?_⟩
      · refine Or.inl ⟨by simp only [e0, stateAt], by simp only [e0, stateAt],
          by simp only [e0, stateAt, intHeadEnv, intHeadPhiEnv]; block_lk,
          by simp only [e0, stateAt, intHeadEnv, intHeadPhiEnv]; block_lk,
          i0 + c, by omega, hltn, ?_, ?_, ?_,
          b, by rw [← hmem]; exact hbyte'_s, hdigit'⟩
        · simp only [e0, stateAt, intHeadEnv, intHeadPhiEnv]
          block_lk
        · simp only [e0, stateAt, intHeadEnv, intHeadPhiEnv]
          rw [show d0 + (i0 + c - i0) = d0 + c from by omega]
          block_lk
        · have hval : ip = BitVec.ofNat 64
              (digitFold bs (i0 - d0) (min (d0 + (i0 + c - i0)) 19)) := by
            rw [show d0 + (i0 + c - i0) = d0 + c from by omega]
          simp only [e0, stateAt, intHeadEnv, intHeadPhiEnv]
          block_lk
          exact congrArg (fun x : BitVec 64 => some (Value.int 64 x)) hval
      · intro k
        rw [runFuel_jump_prefix hstep1 k]
    · obtain ⟨hpre0, hi, hid, hipv⟩ := hback
      let ip : BitVec 64 := BitVec.ofNat 64 (digitFold bs (i0 - d0) (min (d0 + c) 19))
      let e0 : State := stateAt (intHeadEnv s.env p (i0 + c) b
          (BitVec.ofNat 64 (d0 + c)) ip)
        { s with pc := "if.end68", pre := some "land.lhs.true41" }
      have hstep1 : step calls numFastBody s = .jump e0 :=
        intHead_step_back_nondigit (env := s.env) (s := s) (a := p) (j := i0 + c)
          (b := b) (idig := BitVec.ofNat 64 (d0 + c)) (ip := ip) hpc hpre0 hp
          (BlockEval.evalOperand_reg_of s.env s "%inc64" _ hi)
          (BlockEval.evalOperand_reg_of s.env s "%inc63" _ hid)
          (BlockEval.evalOperand_reg_of s.env s "%ip.4" _ hipv) hj hbyte_s hdigit'
      refine ⟨e0, 1, by omega, Or.inl (by simp only [e0, stateAt]), ?_, ?_⟩
      · refine Or.inl ⟨by simp only [e0, stateAt], by simp only [e0, stateAt],
          by simp only [e0, stateAt, intHeadEnv, intHeadPhiEnv]; block_lk,
          by simp only [e0, stateAt, intHeadEnv, intHeadPhiEnv]; block_lk,
          i0 + c, by omega, hltn, ?_, ?_, ?_,
          b, by rw [← hmem]; exact hbyte'_s, hdigit'⟩
        · simp only [e0, stateAt, intHeadEnv, intHeadPhiEnv]
          block_lk
        · simp only [e0, stateAt, intHeadEnv, intHeadPhiEnv]
          rw [show d0 + (i0 + c - i0) = d0 + c from by omega]
          block_lk
        · have hval : ip = BitVec.ofNat 64
              (digitFold bs (i0 - d0) (min (d0 + (i0 + c - i0)) 19)) := by
            rw [show d0 + (i0 + c - i0) = d0 + c from by omega]
          simp only [e0, stateAt, intHeadEnv, intHeadPhiEnv]
          block_lk
          exact congrArg (fun x : BitVec 64 => some (Value.int 64 x)) hval
      · intro k
        rw [runFuel_jump_prefix hstep1 k]

/-- **The integer run is a `BoundLoop`.**  The counter starts at the run's own
start `i0`, the bound is the distance to the lexeme's end, and one iteration is
at most four control steps.  The arms are `intRun_step_exit` and
`intRun_step_loop`, and the exit carries the counters. -/
def intRunBoundLoop (mem0 : Mem) (p n i0 d0 : Nat) (bs : List UInt8) (cost : Nat)
    (hcost : 4 ≤ cost) : BoundLoop calls numFastBody where
  head := "land.lhs.true41"
  exitBlock := "if.end68"
  N := n - i0
  cost := cost
  Inv := intRunInv mem0 p n i0 d0 bs
  atBound := intRunAtBound mem0 p n i0
  Exit := intRunExitBlock
  ExitWord := intRunExit mem0 bs p n i0 d0
  step_exit := by
    intro r s c hinv hb
    have hb' : intRunAtBound mem0 p n i0 s c = true := hb
    obtain ⟨e, j, hj, hexit, hword, hrun⟩ := intRun_step_exit hinv hb'
    exact ⟨e, j, by omega, hexit, hword, hrun⟩
  step_loop := by
    intro r s c hinv hb
    obtain ⟨e, c', j, hj, hpc, hlt, hinv', hrun⟩ := intRun_step_loop hinv hb
    exact ⟨e, c', j, by omega, hpc, hlt, hinv', hrun⟩
  exit_at_zero := by
    intro s c h
    obtain ⟨_, _, hsum, _, _, _, _, _, _, _, _⟩ := h
    unfold intRunAtBound
    have hle : decide (n - i0 ≤ c + 1) = true := decide_eq_true (by omega)
    rw [hle]
    simp
  budget := by
    intro r s c h
    obtain ⟨_, _, hsum, _, _, _, _, _, _, _, _⟩ := h
    omega

/-- **The integer run reaches its exit.**  At the whole distance as its budget,
the head reaches an exit carrying the counters within `(n - i0 + 1) * cost` control
steps.  `cost = 4` covers both exits. -/
theorem intRun_run (mem0 : Mem) (p n i0 d0 : Nat) (bs : List UInt8) (cost : Nat)
    (hcost : 4 ≤ cost) (s : State) (c : Nat)
    (hinv : intRunInv mem0 p n i0 d0 bs (n - i0) s c) (k : Nat) :
    ∃ (e : State) (j : Nat), j ≤ (n - i0 + 1) * cost ∧ intRunExitBlock e ∧
      intRunExit mem0 bs p n i0 d0 e ∧
      runFuel calls (j + k) numFastBody s =
        runFuel calls k numFastBody e :=
  (intRunBoundLoop mem0 p n i0 d0 bs cost hcost).run s c hinv k

/-- **The run's end-of-lexeme exit when every remaining byte is a digit.**  The
non-digit exit's own stop byte is a non-digit, so a lexeme whose bytes from the
run's start to its end are digits rules that arm out and leaves the end-of-lexeme
one — the arm a composition needs to know the run stopped at the lexeme's end. -/
theorem intRun_step_end230 {mem0 : Mem} {p n i0 d0 r : Nat} {bs : List UInt8}
    {s : State} {c : Nat}
    (hinv : intRunInv mem0 p n i0 d0 bs r s c)
    (hb : intRunAtBound mem0 p n i0 s c = true)
    (hdigits : ∀ k, i0 ≤ k → k < n → IsDigitB (bs.getD k 0) = true) :
    ∃ (e : State) (j : Nat), j ≤ 4 ∧ intRunEndWord bs p n i0 d0 e ∧
      ∀ k, runFuel calls (j + k) numFastBody s =
        runFuel calls k numFastBody e := by
  obtain ⟨e, j, hj, _, hexit, hrun⟩ := intRun_step_exit hinv hb
  obtain ⟨_, _, _, _, _, _, _, _, hread, _, _⟩ := hinv
  rcases hexit with ⟨_, _, _, _, i1, hi0, hi1lt, _, _, _, b, hbytei, hbd⟩ | hend
  · have hbs : bs.getD i1 0 = b := getD_of_readBytes hread hi1lt hbytei
    have hdig := hdigits i1 hi0 hi1lt
    rw [hbs, hbd] at hdig
    exact absurd hdig (by decide)
  · exact ⟨e, j, hj, hend, hrun⟩

/-- **The integer run's end-of-lexeme loop.**  With every byte from the run's
start to the lexeme's end a digit, the run's only bound is the lexeme's end, so
its exit is the end-of-lexeme one and the exit word is `intRunEndWord`. -/
def intRunEndBoundLoop (mem0 : Mem) (p n i0 d0 : Nat) (bs : List UInt8) (cost : Nat)
    (hcost : 4 ≤ cost)
    (hdigits : ∀ k, i0 ≤ k → k < n → IsDigitB (bs.getD k 0) = true) :
    BoundLoop calls numFastBody where
  head := "land.lhs.true41"
  exitBlock := "if.end230"
  N := n - i0
  cost := cost
  Inv := intRunInv mem0 p n i0 d0 bs
  atBound := intRunAtBound mem0 p n i0
  Exit := fun e => e.pc = "if.end230"
  ExitWord := intRunEndWord bs p n i0 d0
  step_exit := by
    intro r s c hinv hb
    obtain ⟨e, j, hj, hword, hrun⟩ := intRun_step_end230 hinv hb hdigits
    exact ⟨e, j, by omega, hword.1, hword, hrun⟩
  step_loop := by
    intro r s c hinv hb
    obtain ⟨e, c', j, hj, hpc, hlt, hinv', hrun⟩ := intRun_step_loop hinv hb
    exact ⟨e, c', j, by omega, hpc, hlt, hinv', hrun⟩
  exit_at_zero := by
    intro s c h
    obtain ⟨_, _, hsum, _, _, _, _, _, _, _, _⟩ := h
    unfold intRunAtBound
    have hle : decide (n - i0 ≤ c + 1) = true := decide_eq_true (by omega)
    rw [hle]
    simp
  budget := by
    intro r s c h
    obtain ⟨_, _, hsum, _, _, _, _, _, _, _, _⟩ := h
    omega

/-- **The integer run reaches the lexeme's end.**  At the whole distance as its
budget, a run whose remaining bytes are all digits leaves at `if.end230` with the
end-of-lexeme exit word within `(n - i0 + 1) * cost` control steps. -/
theorem intRun_end_run (mem0 : Mem) (p n i0 d0 : Nat) (bs : List UInt8) (cost : Nat)
    (hcost : 4 ≤ cost)
    (hdigits : ∀ k, i0 ≤ k → k < n → IsDigitB (bs.getD k 0) = true)
    (s : State) (c : Nat)
    (hinv : intRunInv mem0 p n i0 d0 bs (n - i0) s c) (k : Nat) :
    ∃ (e : State) (j : Nat), j ≤ (n - i0 + 1) * cost ∧ e.pc = "if.end230" ∧
      intRunEndWord bs p n i0 d0 e ∧
      runFuel calls (j + k) numFastBody s =
        runFuel calls k numFastBody e :=
  (intRunEndBoundLoop mem0 p n i0 d0 bs cost hcost hdigits).run s c hinv k

/-! ### The fraction run: `land.lhs.true119`

The same four-block shape as the integer run, with `%fdig.3594` the digit count,
`%fr.3593` the accumulator, `%i.9595` the index, and the exits `if.end144` (the
head's non-digit branch) and `if.end230` (`if.end140`'s end-of-lexeme branch). -/

def fracHeadPhiEnv (env : Env) (j : Nat) (fdig fr : BitVec 64) : Env :=
  ("%fr.3593", .int 64 fr) ::
  ("%fdig.3594", .int 64 fdig) ::
  ("%i.9595", .int 64 (BitVec.ofNat 64 j)) :: env

def fracHeadEnv (env : Env) (a j : Nat) (b : UInt8) (fdig fr : BitVec 64) : Env :=
  ("%or.cond443", .int 1 (BitVec.ofBool (IsDigitB b))) ::
  ("%19", .int 8 (JsonScanLane.vByte b + 0xd0#8)) ::
  ("%18", .int 8 (JsonScanLane.vByte b)) ::
  ("%arrayidx120", .ptr (a + j)) :: fracHeadPhiEnv env j fdig fr

theorem lookup_fracHeadPhiEnv_p (env : Env) (j : Nat) (fdig fr : BitVec 64) (a : Nat) :
    lookupName (fracHeadPhiEnv env j fdig fr) "%p" = some (.ptr a) ↔
      lookupName env "%p" = some (.ptr a) := by
  simp only [fracHeadPhiEnv,
    lookupName_cons_ne (k := "%fr.3593") (n := "%p") _ _ (by decide),
    lookupName_cons_ne (k := "%fdig.3594") (n := "%p") _ _ (by decide),
    lookupName_cons_ne (k := "%i.9595") (n := "%p") _ _ (by decide)]

theorem lookup_fracHeadPhiEnv_n (env : Env) (j : Nat) (fdig fr : BitVec 64)
    (n : BitVec 64) :
    lookupName (fracHeadPhiEnv env j fdig fr) "%n" = some (.int 64 n) ↔
      lookupName env "%n" = some (.int 64 n) := by
  simp only [fracHeadPhiEnv,
    lookupName_cons_ne (k := "%fr.3593") (n := "%n") _ _ (by decide),
    lookupName_cons_ne (k := "%fdig.3594") (n := "%n") _ _ (by decide),
    lookupName_cons_ne (k := "%i.9595") (n := "%n") _ _ (by decide)]

theorem lookup_fracHeadPhiEnv_i (env : Env) (j : Nat) (fdig fr : BitVec 64) :
    lookupName (fracHeadPhiEnv env j fdig fr) "%i.9595"
      = some (.int 64 (BitVec.ofNat 64 j)) := by
  simp only [fracHeadPhiEnv,
    lookupName_cons_ne (k := "%fr.3593") (n := "%i.9595") _ _ (by decide),
    lookupName_cons_ne (k := "%fdig.3594") (n := "%i.9595") _ _ (by decide),
    lookupName_cons_self]

theorem lookup_fracHeadPhiEnv_fdig (env : Env) (j : Nat) (fdig fr : BitVec 64) :
    lookupName (fracHeadPhiEnv env j fdig fr) "%fdig.3594" = some (.int 64 fdig) := by
  simp only [fracHeadPhiEnv,
    lookupName_cons_ne (k := "%fr.3593") (n := "%fdig.3594") _ _ (by decide),
    lookupName_cons_self]

theorem fracHead_denote_phi {calls : Calls} {env : Env} {s : State} {a j : Nat}
    {b : UInt8} {fdig fr : BitVec 64}
    (hp : lookupName (fracHeadPhiEnv env j fdig fr) "%p" = some (.ptr a))
    (hj : j < 2 ^ 63)
    (hread : readByte s.mem (a + j) = some b) :
    denoteCode calls
      [Instr.gep "%arrayidx120" (Ty.int 8) (Operand.reg "%p") (Operand.reg "%i.9595"),
       Instr.load "%18" (Ty.int 8) (Operand.reg "%arrayidx120"),
       Instr.binop "%19" (BinOp.add) 8 (Operand.reg "%18")
         (Operand.imm (Const.int 8 0xd0#8)),
       Instr.icmp "%or.cond443" (IPred.ult) 8 (Operand.reg "%19")
         (Operand.imm (Const.int 8 0x0a#8))]
      (stateAt (fracHeadPhiEnv env j fdig fr) s) =
    some (stateAt (fracHeadEnv env a j b fdig fr) s) := by
  have ho : lookupName (fracHeadPhiEnv env j fdig fr) "%i.9595"
      = some (.int 64 (BitVec.ofNat 64 j)) := lookup_fracHeadPhiEnv_i env j fdig fr
  have hpos : ((BitVec.ofNat 64 j).signExtend 64).toNat < 2 ^ 63 := by
    rw [sExt_ofNat64 hj]; exact hj
  rw [denoteCode_gep8_reg _ _ _ "%arrayidx120" "%p" "%i.9595" hp ho hpos _]
  rw [sExt_ofNat64 hj]
  have ha8 : lookupName
      (("%arrayidx120", .ptr (a + j)) :: fracHeadPhiEnv env j fdig fr) "%arrayidx120"
      = some (.ptr (a + j)) := lookupName_cons_self ..
  rw [JsonScanLane.denoteCode_load_i8 _ _ _ "%18" "%arrayidx120" ha8
    (readBytes_one_some.mpr hread) _]
  have ha9 : lookupName
      (("%18", .int 8 (JsonScanLane.vByte b)) ::
        ("%arrayidx120", .ptr (a + j)) :: fracHeadPhiEnv env j fdig fr) "%18"
      = some (.int 8 (JsonScanLane.vByte b)) := lookupName_cons_self ..
  rw [JsonScanLane.denoteCode_add_imm_w _ _ _ "%19" "%18" 8 ha9 _]
  have ha10 : lookupName
      (("%19", .int 8 (JsonScanLane.vByte b + 0xd0#8)) ::
        ("%18", .int 8 (JsonScanLane.vByte b)) ::
        ("%arrayidx120", .ptr (a + j)) :: fracHeadPhiEnv env j fdig fr) "%19"
      = some (.int 8 (JsonScanLane.vByte b + 0xd0#8)) := lookupName_cons_self ..
  rw [JsonScanLane.denoteCode_icmp_imm_w _ _ _ "%or.cond443" "%19" .ult ha10 _]
  simp only [denoteCode, denoteRun, State.bindAll, stateAt, fracHeadEnv, fracHeadPhiEnv,
    evalICmp_ult_digit]

theorem fracHead_run_entry {calls : Calls} {env : Env} {s : State} {j : Nat}
    {fdig fr : BitVec 64}
    (hpre : s.pre = some "land.lhs.true119.preheader")
    (hhi : evalOperand (stateAt env s) (.reg "%i.6552")
      = some (.int 64 (BitVec.ofNat 64 j)))
    (hhd : evalOperand (stateAt env s) (.reg "%fdig.0554") = some (.int 64 fdig))
    (hhf : evalOperand (stateAt env s) (.reg "%fr.0556") = some (.int 64 fr)) :
    denoteCode calls numFastLandLhsTrue119Instrs (stateAt env s) =
      denoteCode calls
        [Instr.gep "%arrayidx120" (Ty.int 8) (Operand.reg "%p") (Operand.reg "%i.9595"),
         Instr.load "%18" (Ty.int 8) (Operand.reg "%arrayidx120"),
         Instr.binop "%19" (BinOp.add) 8 (Operand.reg "%18")
           (Operand.imm (Const.int 8 0xd0#8)),
         Instr.icmp "%or.cond443" (IPred.ult) 8 (Operand.reg "%19")
           (Operand.imm (Const.int 8 0x0a#8))]
        (stateAt (fracHeadPhiEnv env j fdig fr) s) := by
  unfold numFastLandLhsTrue119Instrs
  block_phi_run
  rotate_left 1
  · exact hpre
  · rfl
  · simp only [phiIncoming]; rfl
  · exact hhi
  · simp only [phiIncoming]; rfl
  · exact hhd
  · simp only [phiIncoming]; rfl
  · exact hhf
  · simp only [runCells, fracHeadPhiEnv, stateAt]

theorem fracHead_run_back {calls : Calls} {env : Env} {s : State} {j : Nat}
    {fdig fr : BitVec 64}
    (hpre : s.pre = some "if.end140")
    (hhi : evalOperand (stateAt env s) (.reg "%inc142")
      = some (.int 64 (BitVec.ofNat 64 j)))
    (hhd : evalOperand (stateAt env s) (.reg "%inc141") = some (.int 64 fdig))
    (hhf : evalOperand (stateAt env s) (.reg "%fr.4") = some (.int 64 fr)) :
    denoteCode calls numFastLandLhsTrue119Instrs (stateAt env s) =
      denoteCode calls
        [Instr.gep "%arrayidx120" (Ty.int 8) (Operand.reg "%p") (Operand.reg "%i.9595"),
         Instr.load "%18" (Ty.int 8) (Operand.reg "%arrayidx120"),
         Instr.binop "%19" (BinOp.add) 8 (Operand.reg "%18")
           (Operand.imm (Const.int 8 0xd0#8)),
         Instr.icmp "%or.cond443" (IPred.ult) 8 (Operand.reg "%19")
           (Operand.imm (Const.int 8 0x0a#8))]
        (stateAt (fracHeadPhiEnv env j fdig fr) s) := by
  unfold numFastLandLhsTrue119Instrs
  block_phi_run
  rotate_left 1
  · exact hpre
  · rfl
  · simp only [phiIncoming]; rfl
  · exact hhi
  · simp only [phiIncoming]; rfl
  · exact hhd
  · simp only [phiIncoming]; rfl
  · exact hhf
  · simp only [runCells, fracHeadPhiEnv, stateAt]

theorem fracHead_denote_entry {calls : Calls} {env : Env} {s : State} {a j : Nat}
    {b : UInt8} {fdig fr : BitVec 64}
    (hpre : s.pre = some "land.lhs.true119.preheader")
    (hp : lookupName env "%p" = some (.ptr a))
    (hhi : evalOperand (stateAt env s) (.reg "%i.6552")
      = some (.int 64 (BitVec.ofNat 64 j)))
    (hhd : evalOperand (stateAt env s) (.reg "%fdig.0554") = some (.int 64 fdig))
    (hhf : evalOperand (stateAt env s) (.reg "%fr.0556") = some (.int 64 fr))
    (hj : j < 2 ^ 63) (hread : readByte s.mem (a + j) = some b) :
    denoteCode calls numFastLandLhsTrue119Instrs (stateAt env s) =
      some (stateAt (fracHeadEnv env a j b fdig fr) s) := by
  rw [fracHead_run_entry (calls := calls) hpre hhi hhd hhf]
  exact fracHead_denote_phi ((lookup_fracHeadPhiEnv_p env j fdig fr a).mpr hp) hj hread

theorem fracHead_denote_back {calls : Calls} {env : Env} {s : State} {a j : Nat}
    {b : UInt8} {fdig fr : BitVec 64}
    (hpre : s.pre = some "if.end140")
    (hp : lookupName env "%p" = some (.ptr a))
    (hhi : evalOperand (stateAt env s) (.reg "%inc142")
      = some (.int 64 (BitVec.ofNat 64 j)))
    (hhd : evalOperand (stateAt env s) (.reg "%inc141") = some (.int 64 fdig))
    (hhf : evalOperand (stateAt env s) (.reg "%fr.4") = some (.int 64 fr))
    (hj : j < 2 ^ 63) (hread : readByte s.mem (a + j) = some b) :
    denoteCode calls numFastLandLhsTrue119Instrs (stateAt env s) =
      some (stateAt (fracHeadEnv env a j b fdig fr) s) := by
  rw [fracHead_run_back (calls := calls) hpre hhi hhd hhf]
  exact fracHead_denote_phi ((lookup_fracHeadPhiEnv_p env j fdig fr a).mpr hp) hj hread

/-! #### The fraction run's body and its two accumulator branches -/

def fracBodyEnv (env : Env) (fdig : BitVec 64) : Env :=
  ("%cmp131", .int 1 (evalICmp .ult fdig (19#64))) :: env

theorem fracBodyEnv_p (env : Env) (fdig : BitVec 64) (a : Nat) :
    lookupName (fracBodyEnv env fdig) "%p" = some (.ptr a) ↔
      lookupName env "%p" = some (.ptr a) := by
  simp only [fracBodyEnv, lookupName_cons_ne (k := "%cmp131") (n := "%p") _ _ (by decide)]

theorem fracBodyEnv_n (env : Env) (fdig : BitVec 64) (n : BitVec 64) :
    lookupName (fracBodyEnv env fdig) "%n" = some (.int 64 n) ↔
      lookupName env "%n" = some (.int 64 n) := by
  simp only [fracBodyEnv, lookupName_cons_ne (k := "%cmp131") (n := "%n") _ _ (by decide)]

theorem fracBody_denote {calls : Calls} {env : Env} {s : State} {fdig : BitVec 64}
    (hf : lookupName env "%fdig.3594" = some (.int 64 fdig)) :
    denoteCode calls numFastWhileBody130Instrs (stateAt env s) =
      some (stateAt (fracBodyEnv env fdig) s) := by
  unfold numFastWhileBody130Instrs
  block_eval

theorem fracBody_step_taken {env : Env} {s : State} {fdig : BitVec 64}
    (hpc : s.pc = "while.body130")
    (hf : lookupName env "%fdig.3594" = some (.int 64 fdig))
    (hlt : fdig.ult (19#64) = true) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (fracBodyEnv env fdig)
        { s with pc := "if.then133", pre := some "while.body130" }) := by
  refine numFast_step_at (s' := stateAt (fracBodyEnv env fdig) s)
    (b := ⟨"while.body130", numFastWhileBody130Instrs,
      Term.condbr (.reg "%cmp131") "if.then133" "if.end140"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc, numFastWhileBody130Instrs]
      using numFast_findBlock_while_body130
  · simpa only [denoteCode_nil] using fracBody_denote hf
  · have hlk : lookupName (fracBodyEnv env fdig) "%cmp131"
        = some (.int 1 (evalICmp .ult fdig (19#64))) := by
      simp only [fracBodyEnv, lookupName_cons_self]
    have hb : evalICmp .ult fdig (19#64) = 1 := by
      unfold evalICmp; rw [hlt]; rfl
    rw [numFast_execTerm_condbr_one _ "%cmp131" _ _ hlk hb]
    simp only [stateAt, hpc]

theorem fracBody_step_skip {env : Env} {s : State} {fdig : BitVec 64}
    (hpc : s.pc = "while.body130")
    (hf : lookupName env "%fdig.3594" = some (.int 64 fdig))
    (hlt : fdig.ult (19#64) = false) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (fracBodyEnv env fdig)
        { s with pc := "if.end140", pre := some "while.body130" }) := by
  refine numFast_step_at (s' := stateAt (fracBodyEnv env fdig) s)
    (b := ⟨"while.body130", numFastWhileBody130Instrs,
      Term.condbr (.reg "%cmp131") "if.then133" "if.end140"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc, numFastWhileBody130Instrs]
      using numFast_findBlock_while_body130
  · simpa only [denoteCode_nil] using fracBody_denote hf
  · have hlk : lookupName (fracBodyEnv env fdig) "%cmp131"
        = some (.int 1 (evalICmp .ult fdig (19#64))) := by
      simp only [fracBodyEnv, lookupName_cons_self]
    have hb : evalICmp .ult fdig (19#64) = 0 := by
      unfold evalICmp; rw [hlt]; rfl
    rw [numFast_execTerm_condbr_zero _ "%cmp131" _ _ hlk hb]
    simp only [stateAt, hpc]

def fracIfThenEnv (env : Env) (fr : BitVec 64) (b : UInt8) : Env :=
  ("%add139", .int 64
      (fr * 10 + BitVec.ofNat 64 (JsonScanLane.vByte b &&& 0x0f#8).toNat)) ::
  ("%conv138", .int 64 (BitVec.ofNat 64 (JsonScanLane.vByte b &&& 0x0f#8).toNat)) ::
  ("%20", .int 8 (JsonScanLane.vByte b &&& 0x0f#8)) ::
  ("%mul134", .int 64 (fr * 10)) :: env

theorem fracIfThenEnv_p (env : Env) (fr : BitVec 64) (b : UInt8) (a : Nat) :
    lookupName (fracIfThenEnv env fr b) "%p" = some (.ptr a) ↔
      lookupName env "%p" = some (.ptr a) := by
  simp only [fracIfThenEnv, lookupName_cons_ne (k := "%add139") (n := "%p") _ _ (by decide),
    lookupName_cons_ne (k := "%conv138") (n := "%p") _ _ (by decide),
    lookupName_cons_ne (k := "%20") (n := "%p") _ _ (by decide),
    lookupName_cons_ne (k := "%mul134") (n := "%p") _ _ (by decide)]

theorem fracIfThenEnv_n (env : Env) (fr : BitVec 64) (b : UInt8) (n : BitVec 64) :
    lookupName (fracIfThenEnv env fr b) "%n" = some (.int 64 n) ↔
      lookupName env "%n" = some (.int 64 n) := by
  simp only [fracIfThenEnv, lookupName_cons_ne (k := "%add139") (n := "%n") _ _ (by decide),
    lookupName_cons_ne (k := "%conv138") (n := "%n") _ _ (by decide),
    lookupName_cons_ne (k := "%20") (n := "%n") _ _ (by decide),
    lookupName_cons_ne (k := "%mul134") (n := "%n") _ _ (by decide)]

theorem fracIfThen_denote {calls : Calls} {env : Env} {s : State} {fr : BitVec 64}
    {b : UInt8}
    (hfr : lookupName env "%fr.3593" = some (.int 64 fr))
    (h8 : lookupName env "%18" = some (.int 8 (JsonScanLane.vByte b))) :
    denoteCode calls numFastIfThen133Instrs (stateAt env s) =
      some (stateAt (fracIfThenEnv env fr b) s) := by
  unfold numFastIfThen133Instrs
  rw [denoteCode_mul_imm _ _ _ "%mul134" "%fr.3593" hfr _]
  rw [JsonScanLane.denoteCode_and_imm_w _ _ _ "%20" "%18" (w := 8) (by block_lk) _]
  rw [denoteCode_zext _ _ _ "%conv138" "%20" 8 64 (by block_lk) _]
  rw [denoteCode_add_reg _ _ _ "%add139" "%mul134" "%conv138" (by block_lk) (by block_lk) _]
  simp only [denoteCode, denoteRun, State.bindAll, stateAt, fracIfThenEnv]
  rfl

theorem fracIfThen_step {env : Env} {s : State} {fr : BitVec 64} {b : UInt8}
    (hpc : s.pc = "if.then133")
    (hfr : lookupName env "%fr.3593" = some (.int 64 fr))
    (h8 : lookupName env "%18" = some (.int 8 (JsonScanLane.vByte b))) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (fracIfThenEnv env fr b)
        { s with pc := "if.end140", pre := some "if.then133" }) := by
  refine numFast_step_at (s' := stateAt (fracIfThenEnv env fr b) s)
    (b := ⟨"if.then133", numFastIfThen133Instrs, Term.br "if.end140"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc, numFastIfThen133Instrs]
      using numFast_findBlock_if_then133
  · simpa only [denoteCode_nil] using fracIfThen_denote hfr h8
  · simp only [execTerm, stateAt, hpc]

def fracIfEndEnv (env : Env) (fr fdig i n : BitVec 64) : Env :=
  ("%exitcond702.not", .int 1 (evalICmp .eq (i + 1#64) n)) ::
  ("%inc142", .int 64 (i + 1#64)) ::
  ("%inc141", .int 64 (fdig + 1#64)) ::
  ("%fr.4", .int 64 fr) :: env

theorem fracIfEndEnv_p (env : Env) (fr fdig i n : BitVec 64) (a : Nat) :
    lookupName (fracIfEndEnv env fr fdig i n) "%p" = some (.ptr a) ↔
      lookupName env "%p" = some (.ptr a) := by
  simp only [fracIfEndEnv,
    lookupName_cons_ne (k := "%exitcond702.not") (n := "%p") _ _ (by decide),
    lookupName_cons_ne (k := "%inc142") (n := "%p") _ _ (by decide),
    lookupName_cons_ne (k := "%inc141") (n := "%p") _ _ (by decide),
    lookupName_cons_ne (k := "%fr.4") (n := "%p") _ _ (by decide)]

theorem fracIfEndEnv_n (env : Env) (fr fdig i n : BitVec 64) (m : BitVec 64) :
    lookupName (fracIfEndEnv env fr fdig i n) "%n" = some (.int 64 m) ↔
      lookupName env "%n" = some (.int 64 m) := by
  simp only [fracIfEndEnv,
    lookupName_cons_ne (k := "%exitcond702.not") (n := "%n") _ _ (by decide),
    lookupName_cons_ne (k := "%inc142") (n := "%n") _ _ (by decide),
    lookupName_cons_ne (k := "%inc141") (n := "%n") _ _ (by decide),
    lookupName_cons_ne (k := "%fr.4") (n := "%n") _ _ (by decide)]

theorem fracIfEnd_denote {calls : Calls} {env : Env} {s : State} {fdig i n : BitVec 64}
    {p : String} {op : Operand} {frv : BitVec 64}
    (hpre : s.pre = some p)
    (hinc : phiIncoming p
      [("if.then133", (Operand.reg "%add139")), ("while.body130", (Operand.reg "%fr.3593"))]
      = some op)
    (hop : evalOperand (stateAt env s) op = some (.int 64 frv))
    (hf : lookupName env "%fdig.3594" = some (.int 64 fdig))
    (hi : lookupName env "%i.9595" = some (.int 64 i))
    (hn : lookupName env "%n" = some (.int 64 n)) :
    denoteCode calls numFastIfEnd140Instrs (stateAt env s) =
      some (stateAt (fracIfEndEnv env frv fdig i n) s) := by
  unfold numFastIfEnd140Instrs
  rw [denoteCode_phi _ _ _ "%fr.4" (Ty.int 64)
    [("if.then133", (Operand.reg "%add139")),
     ("while.body130", (Operand.reg "%fr.3593"))]
    hpre hinc hop _ (by decide)]
  rw [denoteCode_add_imm _ _ _ "%inc141" "%fdig.3594" (by block_lk) _]
  rw [denoteCode_add_imm _ _ _ "%inc142" "%i.9595" (by block_lk) _]
  rw [denoteCode_icmp_eq_reg _ _ _ "%exitcond702.not" "%inc142" "%n"
    (by block_lk) (by block_lk) _]
  simp only [denoteCode, denoteRun, State.bindAll, stateAt, fracIfEndEnv]

theorem fracIfEnd_step_exit {env : Env} {s : State} {fdig i n : BitVec 64}
    {p : String} {op : Operand} {frv : BitVec 64}
    (hpc : s.pc = "if.end140")
    (hpre : s.pre = some p)
    (hinc : phiIncoming p
      [("if.then133", (Operand.reg "%add139")), ("while.body130", (Operand.reg "%fr.3593"))]
      = some op)
    (hop : evalOperand (stateAt env s) op = some (.int 64 frv))
    (hf : lookupName env "%fdig.3594" = some (.int 64 fdig))
    (hi : lookupName env "%i.9595" = some (.int 64 i))
    (hn : lookupName env "%n" = some (.int 64 n))
    (heq : evalICmp .eq (i + 1#64) n = 1) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (fracIfEndEnv env frv fdig i n)
        { s with pc := "if.end230", pre := some "if.end140" }) := by
  refine numFast_step_at (s' := stateAt (fracIfEndEnv env frv fdig i n) s)
    (b := ⟨"if.end140", numFastIfEnd140Instrs,
      Term.condbr (.reg "%exitcond702.not") "if.end230" "land.lhs.true119"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc, numFastIfEnd140Instrs]
      using numFast_findBlock_if_end140
  · simpa only [denoteCode_nil] using fracIfEnd_denote hpre hinc hop hf hi hn
  · have hlk : lookupName (fracIfEndEnv env frv fdig i n) "%exitcond702.not"
        = some (.int 1 (evalICmp .eq (i + 1#64) n)) := by
      simp only [fracIfEndEnv, lookupName_cons_self]
    rw [numFast_execTerm_condbr_one _ "%exitcond702.not" _ _ hlk heq]
    simp only [stateAt, hpc]

theorem fracIfEnd_step_loop {env : Env} {s : State} {fdig i n : BitVec 64}
    {p : String} {op : Operand} {frv : BitVec 64}
    (hpc : s.pc = "if.end140")
    (hpre : s.pre = some p)
    (hinc : phiIncoming p
      [("if.then133", (Operand.reg "%add139")), ("while.body130", (Operand.reg "%fr.3593"))]
      = some op)
    (hop : evalOperand (stateAt env s) op = some (.int 64 frv))
    (hf : lookupName env "%fdig.3594" = some (.int 64 fdig))
    (hi : lookupName env "%i.9595" = some (.int 64 i))
    (hn : lookupName env "%n" = some (.int 64 n))
    (heq : evalICmp .eq (i + 1#64) n = 0) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (fracIfEndEnv env frv fdig i n)
        { s with pc := "land.lhs.true119", pre := some "if.end140" }) := by
  refine numFast_step_at (s' := stateAt (fracIfEndEnv env frv fdig i n) s)
    (b := ⟨"if.end140", numFastIfEnd140Instrs,
      Term.condbr (.reg "%exitcond702.not") "if.end230" "land.lhs.true119"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc, numFastIfEnd140Instrs]
      using numFast_findBlock_if_end140
  · simpa only [denoteCode_nil] using fracIfEnd_denote hpre hinc hop hf hi hn
  · have hlk : lookupName (fracIfEndEnv env frv fdig i n) "%exitcond702.not"
        = some (.int 1 (evalICmp .eq (i + 1#64) n)) := by
      simp only [fracIfEndEnv, lookupName_cons_self]
    rw [numFast_execTerm_condbr_zero _ "%exitcond702.not" _ _ hlk heq]
    simp only [stateAt, hpc]

theorem fracHead_step_entry_digit {env : Env} {s : State} {a j : Nat} {b : UInt8}
    {fdig fr : BitVec 64}
    (hpc : s.pc = "land.lhs.true119")
    (hpre : s.pre = some "land.lhs.true119.preheader")
    (hp : lookupName env "%p" = some (.ptr a))
    (hhi : evalOperand (stateAt env s) (.reg "%i.6552")
      = some (.int 64 (BitVec.ofNat 64 j)))
    (hhd : evalOperand (stateAt env s) (.reg "%fdig.0554") = some (.int 64 fdig))
    (hhf : evalOperand (stateAt env s) (.reg "%fr.0556") = some (.int 64 fr))
    (hj : j < 2 ^ 63) (hread : readByte s.mem (a + j) = some b)
    (hdigit : IsDigitB b = true) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (fracHeadEnv env a j b fdig fr)
        { s with pc := "while.body130", pre := some "land.lhs.true119" }) := by
  refine numFast_step_at (s' := stateAt (fracHeadEnv env a j b fdig fr) s)
    (b := ⟨"land.lhs.true119", numFastLandLhsTrue119Instrs,
      Term.condbr (.reg "%or.cond443") "while.body130" "if.end144"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc, numFastLandLhsTrue119Instrs]
      using numFast_findBlock_land_lhs_true119
  · simpa only [denoteCode_nil] using fracHead_denote_entry hpre hp hhi hhd hhf hj hread
  · have hlk : lookupName (fracHeadEnv env a j b fdig fr) "%or.cond443"
        = some (.int 1 (BitVec.ofBool (IsDigitB b))) := by
      simp only [fracHeadEnv, lookupName_cons_self]
    have hb1 : BitVec.ofBool (IsDigitB b) = (1 : BitVec 1) := by
      rw [hdigit]; rfl
    rw [numFast_execTerm_condbr_one _ "%or.cond443" _ _ hlk hb1]
    simp only [stateAt, hpc]

theorem fracHead_step_entry_nondigit {env : Env} {s : State} {a j : Nat} {b : UInt8}
    {fdig fr : BitVec 64}
    (hpc : s.pc = "land.lhs.true119")
    (hpre : s.pre = some "land.lhs.true119.preheader")
    (hp : lookupName env "%p" = some (.ptr a))
    (hhi : evalOperand (stateAt env s) (.reg "%i.6552")
      = some (.int 64 (BitVec.ofNat 64 j)))
    (hhd : evalOperand (stateAt env s) (.reg "%fdig.0554") = some (.int 64 fdig))
    (hhf : evalOperand (stateAt env s) (.reg "%fr.0556") = some (.int 64 fr))
    (hj : j < 2 ^ 63) (hread : readByte s.mem (a + j) = some b)
    (hdigit : IsDigitB b = false) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (fracHeadEnv env a j b fdig fr)
        { s with pc := "if.end144", pre := some "land.lhs.true119" }) := by
  refine numFast_step_at (s' := stateAt (fracHeadEnv env a j b fdig fr) s)
    (b := ⟨"land.lhs.true119", numFastLandLhsTrue119Instrs,
      Term.condbr (.reg "%or.cond443") "while.body130" "if.end144"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc, numFastLandLhsTrue119Instrs]
      using numFast_findBlock_land_lhs_true119
  · simpa only [denoteCode_nil] using fracHead_denote_entry hpre hp hhi hhd hhf hj hread
  · have hlk : lookupName (fracHeadEnv env a j b fdig fr) "%or.cond443"
        = some (.int 1 (BitVec.ofBool (IsDigitB b))) := by
      simp only [fracHeadEnv, lookupName_cons_self]
    have hb1 : BitVec.ofBool (IsDigitB b) = (0 : BitVec 1) := by
      rw [hdigit]; rfl
    rw [numFast_execTerm_condbr_zero _ "%or.cond443" _ _ hlk hb1]
    simp only [stateAt, hpc]

theorem fracHead_step_back_digit {env : Env} {s : State} {a j : Nat} {b : UInt8}
    {fdig fr : BitVec 64}
    (hpc : s.pc = "land.lhs.true119")
    (hpre : s.pre = some "if.end140")
    (hp : lookupName env "%p" = some (.ptr a))
    (hhi : evalOperand (stateAt env s) (.reg "%inc142")
      = some (.int 64 (BitVec.ofNat 64 j)))
    (hhd : evalOperand (stateAt env s) (.reg "%inc141") = some (.int 64 fdig))
    (hhf : evalOperand (stateAt env s) (.reg "%fr.4") = some (.int 64 fr))
    (hj : j < 2 ^ 63) (hread : readByte s.mem (a + j) = some b)
    (hdigit : IsDigitB b = true) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (fracHeadEnv env a j b fdig fr)
        { s with pc := "while.body130", pre := some "land.lhs.true119" }) := by
  refine numFast_step_at (s' := stateAt (fracHeadEnv env a j b fdig fr) s)
    (b := ⟨"land.lhs.true119", numFastLandLhsTrue119Instrs,
      Term.condbr (.reg "%or.cond443") "while.body130" "if.end144"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc, numFastLandLhsTrue119Instrs]
      using numFast_findBlock_land_lhs_true119
  · simpa only [denoteCode_nil] using fracHead_denote_back hpre hp hhi hhd hhf hj hread
  · have hlk : lookupName (fracHeadEnv env a j b fdig fr) "%or.cond443"
        = some (.int 1 (BitVec.ofBool (IsDigitB b))) := by
      simp only [fracHeadEnv, lookupName_cons_self]
    have hb1 : BitVec.ofBool (IsDigitB b) = (1 : BitVec 1) := by
      rw [hdigit]; rfl
    rw [numFast_execTerm_condbr_one _ "%or.cond443" _ _ hlk hb1]
    simp only [stateAt, hpc]

theorem fracHead_step_back_nondigit {env : Env} {s : State} {a j : Nat} {b : UInt8}
    {fdig fr : BitVec 64}
    (hpc : s.pc = "land.lhs.true119")
    (hpre : s.pre = some "if.end140")
    (hp : lookupName env "%p" = some (.ptr a))
    (hhi : evalOperand (stateAt env s) (.reg "%inc142")
      = some (.int 64 (BitVec.ofNat 64 j)))
    (hhd : evalOperand (stateAt env s) (.reg "%inc141") = some (.int 64 fdig))
    (hhf : evalOperand (stateAt env s) (.reg "%fr.4") = some (.int 64 fr))
    (hj : j < 2 ^ 63) (hread : readByte s.mem (a + j) = some b)
    (hdigit : IsDigitB b = false) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (fracHeadEnv env a j b fdig fr)
        { s with pc := "if.end144", pre := some "land.lhs.true119" }) := by
  refine numFast_step_at (s' := stateAt (fracHeadEnv env a j b fdig fr) s)
    (b := ⟨"land.lhs.true119", numFastLandLhsTrue119Instrs,
      Term.condbr (.reg "%or.cond443") "while.body130" "if.end144"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc, numFastLandLhsTrue119Instrs]
      using numFast_findBlock_land_lhs_true119
  · simpa only [denoteCode_nil] using fracHead_denote_back hpre hp hhi hhd hhf hj hread
  · have hlk : lookupName (fracHeadEnv env a j b fdig fr) "%or.cond443"
        = some (.int 1 (BitVec.ofBool (IsDigitB b))) := by
      simp only [fracHeadEnv, lookupName_cons_self]
    have hb1 : BitVec.ofBool (IsDigitB b) = (0 : BitVec 1) := by
      rw [hdigit]; rfl
    rw [numFast_execTerm_condbr_zero _ "%or.cond443" _ _ hlk hb1]
    simp only [stateAt, hpc]

/-! #### The fraction run's invariant, arms and instance -/

/-- The integer part's two cells, as the fraction run carries them: `if.end230`'s
fraction edge reads `%idig.4` and `%ip.5`, which the merge before the run wrote
and the run never touches. -/
def fracPartCells (env : Env) : Prop :=
  ∃ idig5 ip5 : BitVec 64,
    lookupName env "%idig.4" = some (.int 64 idig5) ∧
    lookupName env "%ip.5" = some (.int 64 ip5)

/-- The fraction run's end-of-lexeme exit's cells: the run stopped at the
lexeme's end, so the index is the length, and the block it leaves for is
`if.end230` from `if.end140`.  It carries the cursor, the length, the count
`d0 + (n - i0)`, the accumulator's value at those digits, the count `%17` the
head's preheader formed (`if.end230`'s `%fdig.4719727` phi reads it), and the
integer part's two cells `%idig.4`/`%ip.5`, which the run carries untouched from
the merge before it and whose phis the same block reads. -/
def fracRunEndWord (bs : List UInt8) (p n i0 d0 : Nat) (e : State) : Prop :=
  e.pc = "if.end230" ∧ e.pre = some "if.end140" ∧ n < 2 ^ 64 ∧
  lookupName e.env "%p" = some (.ptr p) ∧
  lookupName e.env "%n" = some (.int 64 (BitVec.ofNat 64 n)) ∧
  lookupName e.env "%inc142" = some (.int 64 (BitVec.ofNat 64 n)) ∧
  lookupName e.env "%inc141"
    = some (.int 64 (BitVec.ofNat 64 (d0 + (n - i0)))) ∧
  lookupName e.env "%fr.4"
    = some (.int 64
      (BitVec.ofNat 64 (digitFold bs (i0 - d0) (min (d0 + (n - i0)) 19)))) ∧
  lookupName e.env "%17"
    = some (.int 64 (BitVec.ofNat 64 d0 + BitVec.ofNat 64 n - BitVec.ofNat 64 i0)) ∧
  fracPartCells e.env

/-- The fraction run's exits: `if.end144` at the head's non-digit branch, or
`if.end230` at `if.end140`'s end-of-lexeme branch (`fracRunEndWord`); each
carries the cursor, the length, the count and the accumulator's value at the
digits the count names, and names its predecessor, and the non-digit exit's index
is inside the lexeme and hands the byte it stopped on and that byte's non-digit
answer, read at the run's own memory — the exit state is opaque to a composition,
so the reader cannot re-read it. -/
def fracRunExit (mem0 : Mem) (bs : List UInt8) (p n i0 d0 : Nat) (e : State) : Prop :=
  (e.pc = "if.end144" ∧ e.pre = some "land.lhs.true119" ∧
      lookupName e.env "%p" = some (.ptr p) ∧
      lookupName e.env "%n" = some (.int 64 (BitVec.ofNat 64 n)) ∧
      ∃ i1, i0 ≤ i1 ∧ i1 < n ∧
        lookupName e.env "%i.9595" = some (.int 64 (BitVec.ofNat 64 i1)) ∧
        lookupName e.env "%fdig.3594"
          = some (.int 64 (BitVec.ofNat 64 (d0 + (i1 - i0)))) ∧
        lookupName e.env "%fr.3593"
          = some (.int 64
            (BitVec.ofNat 64 (digitFold bs (i0 - d0) (min (d0 + (i1 - i0)) 19)))) ∧
        ∃ b, readByte mem0 (p + i1) = some b ∧ IsDigitB b = false)
  ∨ fracRunEndWord bs p n i0 d0 e

def fracRunAtBound (mem0 : Mem) (p n i0 : Nat) (s : State) (c : Nat) : Bool :=
  decide (n - i0 ≤ c + 1) || !numFastDigitAt mem0 p (i0 + c)

def fracRunInv (mem0 : Mem) (p n i0 d0 : Nat) (bs : List UInt8) (r : Nat)
    (s : State) (c : Nat) : Prop :=
  s.pc = "land.lhs.true119" ∧ s.mem = mem0 ∧ c + r = n - i0 ∧ i0 + c < n ∧
  n < 2 ^ 63 ∧ d0 ≤ i0 ∧
  lookupName s.env "%p" = some (.ptr p) ∧
  lookupName s.env "%n" = some (.int 64 (BitVec.ofNat 64 n)) ∧
  readBytes mem0 p n = some bs ∧
  lookupName s.env "%17"
    = some (.int 64 (BitVec.ofNat 64 d0 + BitVec.ofNat 64 n - BitVec.ofNat 64 i0)) ∧
  fracPartCells s.env ∧
  ((s.pre = some "land.lhs.true119.preheader" ∧
      lookupName s.env "%i.6552" = some (.int 64 (BitVec.ofNat 64 (i0 + c))) ∧
      lookupName s.env "%fdig.0554" = some (.int 64 (BitVec.ofNat 64 (d0 + c))) ∧
      lookupName s.env "%fr.0556"
        = some (.int 64 (BitVec.ofNat 64 (digitFold bs (i0 - d0) (min (d0 + c) 19)))))
   ∨ (s.pre = some "if.end140" ∧
      lookupName s.env "%inc142" = some (.int 64 (BitVec.ofNat 64 (i0 + c))) ∧
      lookupName s.env "%inc141" = some (.int 64 (BitVec.ofNat 64 (d0 + c))) ∧
      lookupName s.env "%fr.4"
        = some (.int 64 (BitVec.ofNat 64 (digitFold bs (i0 - d0) (min (d0 + c) 19))))))

theorem fracRun_bound_nondigit {mem0 : Mem} {p n i0 : Nat} {bs : List UInt8}
    {s : State} {c : Nat} (hread : readBytes mem0 p n = some bs)
    (hltn : i0 + c < n) (hb : fracRunAtBound mem0 p n i0 s c = true)
    (hno : ¬ n - i0 ≤ c + 1) :
    ∃ b, readByte mem0 (p + (i0 + c)) = some b ∧ IsDigitB b = false := by
  unfold fracRunAtBound at hb
  rcases Bool.or_eq_true_iff.mp hb with hle | hdig
  · exact absurd (of_decide_eq_true hle) hno
  · obtain ⟨b, hb'⟩ := readByte_of_readBytes_lt hread hltn
    have hfalse : numFastDigitAt mem0 p (i0 + c) = false := by simpa using hdig
    refine ⟨b, hb', ?_⟩
    unfold numFastDigitAt at hfalse
    rw [hb'] at hfalse
    simpa using hfalse

/-- **The fraction run's back edge.** -/
theorem fracRun_step_loop {mem0 : Mem} {p n i0 d0 r : Nat} {bs : List UInt8}
    {s : State} {c : Nat}
    (hinv : fracRunInv mem0 p n i0 d0 bs (r + 1) s c)
    (hb : fracRunAtBound mem0 p n i0 s c = false) :
    ∃ (e : State) (c' : Nat) (j : Nat), j ≤ 4 ∧ e.pc = "land.lhs.true119" ∧ c < c' ∧
      fracRunInv mem0 p n i0 d0 bs r e c' ∧
      ∀ k, runFuel calls (j + k) numFastBody s =
        runFuel calls k numFastBody e := by
  obtain ⟨hpc, hmem, hsum, hltn, hnlt, hd0le, hp, hn, hread, h17,
    ⟨idig5, ip5, hidig5, hip5⟩, hpre⟩ := hinv
  have hblen : bs.length = n := JsonEntrySteps.readBytes_length mem0 p n hread
  unfold fracRunAtBound at hb
  obtain ⟨hnoD, hdig⟩ := Bool.or_eq_false_iff.mp hb
  have hno : ¬ (n - i0 ≤ c + 1) := of_decide_eq_false hnoD
  have hdigitAt : numFastDigitAt mem0 p (i0 + c) = true := by simpa using hdig
  obtain ⟨b, hbyte⟩ := readByte_of_readBytes_lt hread hltn
  have hbyte_s : readByte s.mem (p + (i0 + c)) = some b := by rw [hmem]; exact hbyte
  have hdigitB : IsDigitB b = true := by
    unfold numFastDigitAt at hdigitAt
    rw [hbyte] at hdigitAt
    simpa using hdigitAt
  have hj : i0 + c < 2 ^ 63 := by omega
  have hnext : i0 + c + 1 < n := by omega
  have hnext64 : i0 + c + 1 < 2 ^ 64 := by omega
  have hd0next64 : d0 + c + 1 < 2 ^ 64 := by omega
  have hneqN : BitVec.ofNat 64 (i0 + c + 1) ≠ BitVec.ofNat 64 n := by
    intro h
    have h2 := congrArg BitVec.toNat h
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt hnext64, Nat.mod_eq_of_lt (by omega)] at h2
    omega
  rcases hpre with hent | hback
  · obtain ⟨hpre0, hi, hid, hfr⟩ := hent
    let fr : BitVec 64 := BitVec.ofNat 64 (digitFold bs (i0 - d0) (min (d0 + c) 19))
    let e0 : State := stateAt (fracHeadEnv s.env p (i0 + c) b
        (BitVec.ofNat 64 (d0 + c)) fr)
      { s with pc := "while.body130", pre := some "land.lhs.true119" }
    have hstep1 : step calls numFastBody s = .jump e0 :=
      fracHead_step_entry_digit (env := s.env) (s := s) (a := p) (j := i0 + c)
        (b := b) (fdig := BitVec.ofNat 64 (d0 + c)) (fr := fr) hpc hpre0 hp
        (BlockEval.evalOperand_reg_of s.env s "%i.6552" _ hi)
        (BlockEval.evalOperand_reg_of s.env s "%fdig.0554" _ hid)
        (BlockEval.evalOperand_reg_of s.env s "%fr.0556" _ hfr) hj hbyte_s hdigitB
    have hidig0 : lookupName e0.env "%fdig.3594"
        = some (.int 64 (BitVec.ofNat 64 (d0 + c))) := by
      simp only [e0, stateAt, fracHeadEnv, fracHeadPhiEnv]
      block_lk
    by_cases hguard : (BitVec.ofNat 64 (d0 + c)).ult (19#64) = true
    · let e1 : State := stateAt (fracBodyEnv e0.env (BitVec.ofNat 64 (d0 + c)))
          { e0 with pc := "if.then133", pre := some "while.body130" }
      have hstep2 : step calls numFastBody e0 = .jump e1 :=
        fracBody_step_taken (env := e0.env) (s := e0)
          (fdig := BitVec.ofNat 64 (d0 + c)) (by simp only [e0, stateAt])
          hidig0 hguard
      have hfr1 : lookupName e1.env "%fr.3593" = some (.int 64 fr) := by
        simp only [e1, e0, stateAt, fracBodyEnv, fracHeadEnv, fracHeadPhiEnv]
        block_lk
      have h8 : lookupName e1.env "%18" = some (.int 8 (JsonScanLane.vByte b)) := by
        simp only [e1, e0, stateAt, fracBodyEnv, fracHeadEnv, fracHeadPhiEnv]
        block_lk
      let e2 : State := stateAt (fracIfThenEnv e1.env fr b)
          { e1 with pc := "if.end140", pre := some "if.then133" }
      have hstep3 : step calls numFastBody e1 = .jump e2 :=
        fracIfThen_step (env := e1.env) (s := e1) (by simp only [e1, stateAt])
          hfr1 h8
      have hphi : phiIncoming "if.then133"
          [("if.then133", (Operand.reg "%add139")),
           ("while.body130", (Operand.reg "%fr.3593"))] = some (Operand.reg "%add139") := by
        simp only [phiIncoming]; rfl
      have hphiOp : evalOperand (stateAt e2.env e2) (Operand.reg "%add139")
          = some (.int 64
            (fr * 10 + BitVec.ofNat 64 (JsonScanLane.vByte b &&& 0x0f#8).toNat)) := by
        refine BlockEval.evalOperand_reg_of e2.env e2 "%add139" _ ?_
        simp only [e2, e1, stateAt, fracIfThenEnv, lookupName_cons_self]
      have hidig2 : lookupName e2.env "%fdig.3594"
          = some (.int 64 (BitVec.ofNat 64 (d0 + c))) := by
        simp only [e2, e1, e0, stateAt, fracIfThenEnv, fracBodyEnv, fracHeadEnv,
          fracHeadPhiEnv]
        block_lk
      have hi2 : lookupName e2.env "%i.9595"
          = some (.int 64 (BitVec.ofNat 64 (i0 + c))) := by
        simp only [e2, e1, e0, stateAt, fracIfThenEnv, fracBodyEnv, fracHeadEnv,
          fracHeadPhiEnv]
        block_lk
      have hn2 : lookupName e2.env "%n" = some (.int 64 (BitVec.ofNat 64 n)) := by
        simp only [e2, e1, e0, stateAt, fracIfThenEnv, fracBodyEnv, fracHeadEnv,
          fracHeadPhiEnv]
        block_lk
      have hbits : evalICmp .eq
          (BitVec.ofNat 64 (i0 + c) + (1#64)) (BitVec.ofNat 64 n) = 0 := by
        rw [ofNat64_add_one hnext64]
        exact evalICmp_eq_ne hneqN
      let e3 : State := stateAt
          (fracIfEndEnv e2.env
            (fr * 10 + BitVec.ofNat 64 (JsonScanLane.vByte b &&& 0x0f#8).toNat)
            (BitVec.ofNat 64 (d0 + c)) (BitVec.ofNat 64 (i0 + c))
            (BitVec.ofNat 64 n))
          { e2 with pc := "land.lhs.true119", pre := some "if.end140" }
      have hstep4 : step calls numFastBody e2 = .jump e3 :=
        fracIfEnd_step_loop (env := e2.env) (s := e2)
          (fdig := BitVec.ofNat 64 (d0 + c))
          (i := BitVec.ofNat 64 (i0 + c)) (n := BitVec.ofNat 64 n)
          (p := "if.then133") (op := Operand.reg "%add139")
          (frv := fr * 10 + BitVec.ofNat 64
            (JsonScanLane.vByte b &&& 0x0f#8).toNat)
          (by simp only [e2, stateAt]) (by simp only [e2, stateAt]) hphi hphiOp
          hidig2 hi2 hn2 hbits
      refine ⟨e3, c + 1, 4, by omega, ?_, by omega, ?_, ?_⟩
      · simp only [e3, stateAt]
      · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · simp only [e3, stateAt]
        · simp only [e3, stateAt]; exact hmem
        · omega
        · omega
        · exact hnlt
        · exact hd0le
        · simp only [e3, e2, e1, e0, stateAt, fracIfEndEnv, fracIfThenEnv,
            fracBodyEnv, fracHeadEnv, fracHeadPhiEnv]
          block_lk
        · simp only [e3, e2, e1, e0, stateAt, fracIfEndEnv, fracIfThenEnv,
            fracBodyEnv, fracHeadEnv, fracHeadPhiEnv]
          block_lk
        · simpa only [e3, stateAt] using hread
        · simp only [e3, e2, e1, e0, stateAt, fracIfEndEnv, fracIfThenEnv,
            fracBodyEnv, fracHeadEnv, fracHeadPhiEnv]
          block_lk
        · refine ⟨idig5, ip5, ?_, ?_⟩
          · simp only [e3, e2, e1, e0, stateAt, fracIfEndEnv, fracIfThenEnv,
              fracBodyEnv, fracHeadEnv, fracHeadPhiEnv]
            block_lk
          · simp only [e3, e2, e1, e0, stateAt, fracIfEndEnv, fracIfThenEnv,
              fracBodyEnv, fracHeadEnv, fracHeadPhiEnv]
            block_lk
        · right
          refine ⟨by simp only [e3, stateAt], ?_, ?_, ?_⟩
          · simp only [e3, e2, e1, e0, stateAt, fracIfEndEnv, fracIfThenEnv,
              fracBodyEnv, fracHeadEnv, fracHeadPhiEnv]
            block_lk
            exact int_succ_eq _ hnext64
          · simp only [e3, e2, e1, e0, stateAt, fracIfEndEnv, fracIfThenEnv,
              fracBodyEnv, fracHeadEnv, fracHeadPhiEnv]
            block_lk
            exact int_succ_eq _ hd0next64
          · have hbyteD : bs.getD (i0 + c) 0 = b :=
              getD_of_readBytes hread (by omega) hbyte
            have hnew : fr * 10 + BitVec.ofNat 64
                (JsonScanLane.vByte b &&& 0x0f#8).toNat
                = BitVec.ofNat 64
                  (digitFold bs (i0 - d0) (min (d0 + c + 1) 19)) :=
              digitFold_step_at hd0le (ofNat_ult_true (by omega) hguard)
                (by rw [hblen]; exact hltn) hbyteD hdigitB rfl
            simp only [e3, stateAt, fracIfEndEnv]
            block_lk
            exact congrArg (fun x : BitVec 64 => some (Value.int 64 x)) hnew
      · intro k
        rw [show 4 + k = 1 + (1 + (1 + (1 + k))) from by omega,
          runFuel_jump_prefix hstep1 (1 + (1 + (1 + k))),
          runFuel_jump_prefix hstep2 (1 + (1 + k)),
          runFuel_jump_prefix hstep3 (1 + k),
          runFuel_jump_prefix hstep4 k]
    · have hguard' : (BitVec.ofNat 64 (d0 + c)).ult (19#64) = false := by
        cases h : (BitVec.ofNat 64 (d0 + c)).ult (19#64)
        · rfl
        · exact absurd h hguard
      let e1 : State := stateAt (fracBodyEnv e0.env (BitVec.ofNat 64 (d0 + c)))
          { e0 with pc := "if.end140", pre := some "while.body130" }
      have hstep2 : step calls numFastBody e0 = .jump e1 :=
        fracBody_step_skip (env := e0.env) (s := e0)
          (fdig := BitVec.ofNat 64 (d0 + c)) (by simp only [e0, stateAt])
          hidig0 hguard'
      have hphi : phiIncoming "while.body130"
          [("if.then133", (Operand.reg "%add139")),
           ("while.body130", (Operand.reg "%fr.3593"))] = some (Operand.reg "%fr.3593") := by
        simp only [phiIncoming]; rfl
      have hfr1 : lookupName e1.env "%fr.3593" = some (.int 64 fr) := by
        simp only [e1, e0, stateAt, fracBodyEnv, fracHeadEnv, fracHeadPhiEnv]
        block_lk
      have hphiOp : evalOperand (stateAt e1.env e1) (Operand.reg "%fr.3593")
          = some (.int 64 fr) :=
        BlockEval.evalOperand_reg_of e1.env e1 "%fr.3593" _ hfr1
      have hidig1 : lookupName e1.env "%fdig.3594"
          = some (.int 64 (BitVec.ofNat 64 (d0 + c))) := by
        simp only [e1, e0, stateAt, fracBodyEnv, fracHeadEnv, fracHeadPhiEnv]
        block_lk
      have hi1 : lookupName e1.env "%i.9595"
          = some (.int 64 (BitVec.ofNat 64 (i0 + c))) := by
        simp only [e1, e0, stateAt, fracBodyEnv, fracHeadEnv, fracHeadPhiEnv]
        block_lk
      have hn1 : lookupName e1.env "%n" = some (.int 64 (BitVec.ofNat 64 n)) := by
        simp only [e1, e0, stateAt, fracBodyEnv, fracHeadEnv, fracHeadPhiEnv]
        block_lk
      have hbits : evalICmp .eq
          (BitVec.ofNat 64 (i0 + c) + (1#64)) (BitVec.ofNat 64 n) = 0 := by
        rw [ofNat64_add_one hnext64]
        exact evalICmp_eq_ne hneqN
      let e2 : State := stateAt
          (fracIfEndEnv e1.env fr (BitVec.ofNat 64 (d0 + c))
            (BitVec.ofNat 64 (i0 + c)) (BitVec.ofNat 64 n))
          { e1 with pc := "land.lhs.true119", pre := some "if.end140" }
      have hstep3 : step calls numFastBody e1 = .jump e2 :=
        fracIfEnd_step_loop (env := e1.env) (s := e1)
          (fdig := BitVec.ofNat 64 (d0 + c))
          (i := BitVec.ofNat 64 (i0 + c)) (n := BitVec.ofNat 64 n)
          (p := "while.body130") (op := Operand.reg "%fr.3593") (frv := fr)
          (by simp only [e1, stateAt]) (by simp only [e1, stateAt]) hphi hphiOp
          hidig1 hi1 hn1 hbits
      refine ⟨e2, c + 1, 3, by omega, ?_, by omega, ?_, ?_⟩
      · simp only [e2, stateAt]
      · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · simp only [e2, stateAt]
        · simp only [e2, stateAt]; exact hmem
        · omega
        · omega
        · exact hnlt
        · exact hd0le
        · simp only [e2, e1, e0, stateAt, fracIfEndEnv, fracBodyEnv, fracHeadEnv,
            fracHeadPhiEnv]
          block_lk
        · simp only [e2, e1, e0, stateAt, fracIfEndEnv, fracBodyEnv, fracHeadEnv,
            fracHeadPhiEnv]
          block_lk
        · simpa only [e2, stateAt] using hread
        · simp only [e2, e1, e0, stateAt, fracIfEndEnv, fracBodyEnv, fracHeadEnv,
            fracHeadPhiEnv]
          block_lk
        · refine ⟨idig5, ip5, ?_, ?_⟩
          · simp only [e2, e1, e0, stateAt, fracIfEndEnv, fracBodyEnv, fracHeadEnv,
              fracHeadPhiEnv]
            block_lk
          · simp only [e2, e1, e0, stateAt, fracIfEndEnv, fracBodyEnv, fracHeadEnv,
              fracHeadPhiEnv]
            block_lk
        · right
          refine ⟨by simp only [e2, stateAt], ?_, ?_, ?_⟩
          · simp only [e2, e1, e0, stateAt, fracIfEndEnv, fracBodyEnv, fracHeadEnv,
              fracHeadPhiEnv]
            block_lk
            exact int_succ_eq _ hnext64
          · simp only [e2, e1, e0, stateAt, fracIfEndEnv, fracBodyEnv, fracHeadEnv,
              fracHeadPhiEnv]
            block_lk
            exact int_succ_eq _ hd0next64
          · have hfrozen : fr = BitVec.ofNat 64
                (digitFold bs (i0 - d0) (min (d0 + c + 1) 19)) :=
              digitFold_frozen (ofNat_ult_false (by omega) hguard') rfl
            simp only [e2, stateAt, fracIfEndEnv]
            block_lk
            exact congrArg (fun x : BitVec 64 => some (Value.int 64 x)) hfrozen
      · intro k
        rw [show 3 + k = 1 + (1 + (1 + k)) from by omega,
          runFuel_jump_prefix hstep1 (1 + (1 + k)),
          runFuel_jump_prefix hstep2 (1 + k),
          runFuel_jump_prefix hstep3 k]
  · obtain ⟨hpre0, hi, hid, hfr⟩ := hback
    let fr : BitVec 64 := BitVec.ofNat 64 (digitFold bs (i0 - d0) (min (d0 + c) 19))
    let e0 : State := stateAt (fracHeadEnv s.env p (i0 + c) b
        (BitVec.ofNat 64 (d0 + c)) fr)
      { s with pc := "while.body130", pre := some "land.lhs.true119" }
    have hstep1 : step calls numFastBody s = .jump e0 :=
      fracHead_step_back_digit (env := s.env) (s := s) (a := p) (j := i0 + c)
        (b := b) (fdig := BitVec.ofNat 64 (d0 + c)) (fr := fr) hpc hpre0 hp
        (BlockEval.evalOperand_reg_of s.env s "%inc142" _ hi)
        (BlockEval.evalOperand_reg_of s.env s "%inc141" _ hid)
        (BlockEval.evalOperand_reg_of s.env s "%fr.4" _ hfr) hj hbyte_s hdigitB
    have hidig0 : lookupName e0.env "%fdig.3594"
        = some (.int 64 (BitVec.ofNat 64 (d0 + c))) := by
      simp only [e0, stateAt, fracHeadEnv, fracHeadPhiEnv]
      block_lk
    by_cases hguard : (BitVec.ofNat 64 (d0 + c)).ult (19#64) = true
    · let e1 : State := stateAt (fracBodyEnv e0.env (BitVec.ofNat 64 (d0 + c)))
          { e0 with pc := "if.then133", pre := some "while.body130" }
      have hstep2 : step calls numFastBody e0 = .jump e1 :=
        fracBody_step_taken (env := e0.env) (s := e0)
          (fdig := BitVec.ofNat 64 (d0 + c)) (by simp only [e0, stateAt])
          hidig0 hguard
      have hfr1 : lookupName e1.env "%fr.3593" = some (.int 64 fr) := by
        simp only [e1, e0, stateAt, fracBodyEnv, fracHeadEnv, fracHeadPhiEnv]
        block_lk
      have h8 : lookupName e1.env "%18" = some (.int 8 (JsonScanLane.vByte b)) := by
        simp only [e1, e0, stateAt, fracBodyEnv, fracHeadEnv, fracHeadPhiEnv]
        block_lk
      let e2 : State := stateAt (fracIfThenEnv e1.env fr b)
          { e1 with pc := "if.end140", pre := some "if.then133" }
      have hstep3 : step calls numFastBody e1 = .jump e2 :=
        fracIfThen_step (env := e1.env) (s := e1) (by simp only [e1, stateAt])
          hfr1 h8
      have hphi : phiIncoming "if.then133"
          [("if.then133", (Operand.reg "%add139")),
           ("while.body130", (Operand.reg "%fr.3593"))] = some (Operand.reg "%add139") := by
        simp only [phiIncoming]; rfl
      have hphiOp : evalOperand (stateAt e2.env e2) (Operand.reg "%add139")
          = some (.int 64
            (fr * 10 + BitVec.ofNat 64 (JsonScanLane.vByte b &&& 0x0f#8).toNat)) := by
        refine BlockEval.evalOperand_reg_of e2.env e2 "%add139" _ ?_
        simp only [e2, e1, stateAt, fracIfThenEnv, lookupName_cons_self]
      have hidig2 : lookupName e2.env "%fdig.3594"
          = some (.int 64 (BitVec.ofNat 64 (d0 + c))) := by
        simp only [e2, e1, e0, stateAt, fracIfThenEnv, fracBodyEnv, fracHeadEnv,
          fracHeadPhiEnv]
        block_lk
      have hi2 : lookupName e2.env "%i.9595"
          = some (.int 64 (BitVec.ofNat 64 (i0 + c))) := by
        simp only [e2, e1, e0, stateAt, fracIfThenEnv, fracBodyEnv, fracHeadEnv,
          fracHeadPhiEnv]
        block_lk
      have hn2 : lookupName e2.env "%n" = some (.int 64 (BitVec.ofNat 64 n)) := by
        simp only [e2, e1, e0, stateAt, fracIfThenEnv, fracBodyEnv, fracHeadEnv,
          fracHeadPhiEnv]
        block_lk
      have hbits : evalICmp .eq
          (BitVec.ofNat 64 (i0 + c) + (1#64)) (BitVec.ofNat 64 n) = 0 := by
        rw [ofNat64_add_one hnext64]
        exact evalICmp_eq_ne hneqN
      let e3 : State := stateAt
          (fracIfEndEnv e2.env
            (fr * 10 + BitVec.ofNat 64 (JsonScanLane.vByte b &&& 0x0f#8).toNat)
            (BitVec.ofNat 64 (d0 + c)) (BitVec.ofNat 64 (i0 + c))
            (BitVec.ofNat 64 n))
          { e2 with pc := "land.lhs.true119", pre := some "if.end140" }
      have hstep4 : step calls numFastBody e2 = .jump e3 :=
        fracIfEnd_step_loop (env := e2.env) (s := e2)
          (fdig := BitVec.ofNat 64 (d0 + c))
          (i := BitVec.ofNat 64 (i0 + c)) (n := BitVec.ofNat 64 n)
          (p := "if.then133") (op := Operand.reg "%add139")
          (frv := fr * 10 + BitVec.ofNat 64
            (JsonScanLane.vByte b &&& 0x0f#8).toNat)
          (by simp only [e2, stateAt]) (by simp only [e2, stateAt]) hphi hphiOp
          hidig2 hi2 hn2 hbits
      refine ⟨e3, c + 1, 4, by omega, ?_, by omega, ?_, ?_⟩
      · simp only [e3, stateAt]
      · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · simp only [e3, stateAt]
        · simp only [e3, stateAt]; exact hmem
        · omega
        · omega
        · exact hnlt
        · exact hd0le
        · simp only [e3, e2, e1, e0, stateAt, fracIfEndEnv, fracIfThenEnv,
            fracBodyEnv, fracHeadEnv, fracHeadPhiEnv]
          block_lk
        · simp only [e3, e2, e1, e0, stateAt, fracIfEndEnv, fracIfThenEnv,
            fracBodyEnv, fracHeadEnv, fracHeadPhiEnv]
          block_lk
        · simpa only [e3, stateAt] using hread
        · simp only [e3, e2, e1, e0, stateAt, fracIfEndEnv, fracIfThenEnv,
            fracBodyEnv, fracHeadEnv, fracHeadPhiEnv]
          block_lk
        · refine ⟨idig5, ip5, ?_, ?_⟩
          · simp only [e3, e2, e1, e0, stateAt, fracIfEndEnv, fracIfThenEnv,
              fracBodyEnv, fracHeadEnv, fracHeadPhiEnv]
            block_lk
          · simp only [e3, e2, e1, e0, stateAt, fracIfEndEnv, fracIfThenEnv,
              fracBodyEnv, fracHeadEnv, fracHeadPhiEnv]
            block_lk
        · right
          refine ⟨by simp only [e3, stateAt], ?_, ?_, ?_⟩
          · simp only [e3, e2, e1, e0, stateAt, fracIfEndEnv, fracIfThenEnv,
              fracBodyEnv, fracHeadEnv, fracHeadPhiEnv]
            block_lk
            exact int_succ_eq _ hnext64
          · simp only [e3, e2, e1, e0, stateAt, fracIfEndEnv, fracIfThenEnv,
              fracBodyEnv, fracHeadEnv, fracHeadPhiEnv]
            block_lk
            exact int_succ_eq _ hd0next64
          · have hbyteD : bs.getD (i0 + c) 0 = b :=
              getD_of_readBytes hread (by omega) hbyte
            have hnew : fr * 10 + BitVec.ofNat 64
                (JsonScanLane.vByte b &&& 0x0f#8).toNat
                = BitVec.ofNat 64
                  (digitFold bs (i0 - d0) (min (d0 + c + 1) 19)) :=
              digitFold_step_at hd0le (ofNat_ult_true (by omega) hguard)
                (by rw [hblen]; exact hltn) hbyteD hdigitB rfl
            simp only [e3, stateAt, fracIfEndEnv]
            block_lk
            exact congrArg (fun x : BitVec 64 => some (Value.int 64 x)) hnew
      · intro k
        rw [show 4 + k = 1 + (1 + (1 + (1 + k))) from by omega,
          runFuel_jump_prefix hstep1 (1 + (1 + (1 + k))),
          runFuel_jump_prefix hstep2 (1 + (1 + k)),
          runFuel_jump_prefix hstep3 (1 + k),
          runFuel_jump_prefix hstep4 k]
    · have hguard' : (BitVec.ofNat 64 (d0 + c)).ult (19#64) = false := by
        cases h : (BitVec.ofNat 64 (d0 + c)).ult (19#64)
        · rfl
        · exact absurd h hguard
      let e1 : State := stateAt (fracBodyEnv e0.env (BitVec.ofNat 64 (d0 + c)))
          { e0 with pc := "if.end140", pre := some "while.body130" }
      have hstep2 : step calls numFastBody e0 = .jump e1 :=
        fracBody_step_skip (env := e0.env) (s := e0)
          (fdig := BitVec.ofNat 64 (d0 + c)) (by simp only [e0, stateAt])
          hidig0 hguard'
      have hphi : phiIncoming "while.body130"
          [("if.then133", (Operand.reg "%add139")),
           ("while.body130", (Operand.reg "%fr.3593"))] = some (Operand.reg "%fr.3593") := by
        simp only [phiIncoming]; rfl
      have hfr1 : lookupName e1.env "%fr.3593" = some (.int 64 fr) := by
        simp only [e1, e0, stateAt, fracBodyEnv, fracHeadEnv, fracHeadPhiEnv]
        block_lk
      have hphiOp : evalOperand (stateAt e1.env e1) (Operand.reg "%fr.3593")
          = some (.int 64 fr) :=
        BlockEval.evalOperand_reg_of e1.env e1 "%fr.3593" _ hfr1
      have hidig1 : lookupName e1.env "%fdig.3594"
          = some (.int 64 (BitVec.ofNat 64 (d0 + c))) := by
        simp only [e1, e0, stateAt, fracBodyEnv, fracHeadEnv, fracHeadPhiEnv]
        block_lk
      have hi1 : lookupName e1.env "%i.9595"
          = some (.int 64 (BitVec.ofNat 64 (i0 + c))) := by
        simp only [e1, e0, stateAt, fracBodyEnv, fracHeadEnv, fracHeadPhiEnv]
        block_lk
      have hn1 : lookupName e1.env "%n" = some (.int 64 (BitVec.ofNat 64 n)) := by
        simp only [e1, e0, stateAt, fracBodyEnv, fracHeadEnv, fracHeadPhiEnv]
        block_lk
      have hbits : evalICmp .eq
          (BitVec.ofNat 64 (i0 + c) + (1#64)) (BitVec.ofNat 64 n) = 0 := by
        rw [ofNat64_add_one hnext64]
        exact evalICmp_eq_ne hneqN
      let e2 : State := stateAt
          (fracIfEndEnv e1.env fr (BitVec.ofNat 64 (d0 + c))
            (BitVec.ofNat 64 (i0 + c)) (BitVec.ofNat 64 n))
          { e1 with pc := "land.lhs.true119", pre := some "if.end140" }
      have hstep3 : step calls numFastBody e1 = .jump e2 :=
        fracIfEnd_step_loop (env := e1.env) (s := e1)
          (fdig := BitVec.ofNat 64 (d0 + c))
          (i := BitVec.ofNat 64 (i0 + c)) (n := BitVec.ofNat 64 n)
          (p := "while.body130") (op := Operand.reg "%fr.3593") (frv := fr)
          (by simp only [e1, stateAt]) (by simp only [e1, stateAt]) hphi hphiOp
          hidig1 hi1 hn1 hbits
      refine ⟨e2, c + 1, 3, by omega, ?_, by omega, ?_, ?_⟩
      · simp only [e2, stateAt]
      · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · simp only [e2, stateAt]
        · simp only [e2, stateAt]; exact hmem
        · omega
        · omega
        · exact hnlt
        · exact hd0le
        · simp only [e2, e1, e0, stateAt, fracIfEndEnv, fracBodyEnv, fracHeadEnv,
            fracHeadPhiEnv]
          block_lk
        · simp only [e2, e1, e0, stateAt, fracIfEndEnv, fracBodyEnv, fracHeadEnv,
            fracHeadPhiEnv]
          block_lk
        · simpa only [e2, stateAt] using hread
        · simp only [e2, e1, e0, stateAt, fracIfEndEnv, fracBodyEnv, fracHeadEnv,
            fracHeadPhiEnv]
          block_lk
        · refine ⟨idig5, ip5, ?_, ?_⟩
          · simp only [e2, e1, e0, stateAt, fracIfEndEnv, fracBodyEnv, fracHeadEnv,
              fracHeadPhiEnv]
            block_lk
          · simp only [e2, e1, e0, stateAt, fracIfEndEnv, fracBodyEnv, fracHeadEnv,
              fracHeadPhiEnv]
            block_lk
        · right
          refine ⟨by simp only [e2, stateAt], ?_, ?_, ?_⟩
          · simp only [e2, e1, e0, stateAt, fracIfEndEnv, fracBodyEnv, fracHeadEnv,
              fracHeadPhiEnv]
            block_lk
            exact int_succ_eq _ hnext64
          · simp only [e2, e1, e0, stateAt, fracIfEndEnv, fracBodyEnv, fracHeadEnv,
              fracHeadPhiEnv]
            block_lk
            exact int_succ_eq _ hd0next64
          · have hfrozen : fr = BitVec.ofNat 64
                (digitFold bs (i0 - d0) (min (d0 + c + 1) 19)) :=
              digitFold_frozen (ofNat_ult_false (by omega) hguard') rfl
            simp only [e2, stateAt, fracIfEndEnv]
            block_lk
            exact congrArg (fun x : BitVec 64 => some (Value.int 64 x)) hfrozen
      · intro k
        rw [show 3 + k = 1 + (1 + (1 + k)) from by omega,
          runFuel_jump_prefix hstep1 (1 + (1 + k)),
          runFuel_jump_prefix hstep2 (1 + k),
          runFuel_jump_prefix hstep3 k]

/-! #### The fraction run's exit arm and instance -/

def fracRunExitBlock (e : State) : Prop :=
  e.pc = "if.end144" ∨ e.pc = "if.end230"

theorem fracRunExit_count (mem0 : Mem) (bs : List UInt8) (p n i0 d0 : Nat) (e : State)
    (h : fracRunExit mem0 bs p n i0 d0 e) :
    (∃ i1, e.pc = "if.end144" ∧
      lookupName e.env "%fdig.3594"
        = some (.int 64 (BitVec.ofNat 64 (d0 + (i1 - i0))))) ∨
    (e.pc = "if.end230" ∧
      lookupName e.env "%inc141"
        = some (.int 64 (BitVec.ofNat 64 (d0 + (n - i0))))) := by
  rcases h with ⟨hpc, _, _, _, i1, _, _, _, hcnt, _, _, _, _⟩
    | ⟨hpc, _, _, _, _, _, hcnt, _, _, _⟩
  · exact Or.inl ⟨i1, hpc, hcnt⟩
  · exact Or.inr ⟨hpc, hcnt⟩

theorem fracRun_step_exit {mem0 : Mem} {p n i0 d0 r : Nat} {bs : List UInt8}
    {s : State} {c : Nat}
    (hinv : fracRunInv mem0 p n i0 d0 bs r s c)
    (hb : fracRunAtBound mem0 p n i0 s c = true) :
    ∃ (e : State) (j : Nat), j ≤ 4 ∧ fracRunExitBlock e ∧
      fracRunExit mem0 bs p n i0 d0 e ∧
      ∀ k, runFuel calls (j + k) numFastBody s =
        runFuel calls k numFastBody e := by
  obtain ⟨hpc, hmem, hsum, hltn, hnlt, hd0le, hp, hn, hread, h17,
    ⟨idig5, ip5, hidig5, hip5⟩, hpre⟩ := hinv
  have hblen : bs.length = n := JsonEntrySteps.readBytes_length mem0 p n hread
  have hd0next64 : d0 + c + 1 < 2 ^ 64 := by omega
  obtain ⟨b, hbyte⟩ := readByte_of_readBytes_lt hread hltn
  have hbyte_s : readByte s.mem (p + (i0 + c)) = some b := by rw [hmem]; exact hbyte
  have hj : i0 + c < 2 ^ 63 := by omega
  by_cases hle : n - i0 ≤ c + 1
  · have hnext64 : i0 + c + 1 < 2 ^ 64 := by omega
    have h_eq : i0 + c + 1 = n := by omega
    have hbits : evalICmp .eq (BitVec.ofNat 64 (i0 + c) + (1#64))
        (BitVec.ofNat 64 n) = 1 := by
      rw [ofNat64_add_one hnext64, show i0 + c + 1 = n from h_eq]
      exact evalICmp_eq_refl _
    have hcnt64 : d0 + (i0 + c + 1 - i0) = d0 + c + 1 := by omega
    by_cases hdigit : IsDigitB b = true
    · rcases hpre with hent | hback
      · obtain ⟨hpre0, hi, hid, hfr⟩ := hent
        let fr : BitVec 64 := BitVec.ofNat 64 (digitFold bs (i0 - d0) (min (d0 + c) 19))
        let e0 : State := stateAt (fracHeadEnv s.env p (i0 + c) b
            (BitVec.ofNat 64 (d0 + c)) fr)
          { s with pc := "while.body130", pre := some "land.lhs.true119" }
        have hstep1 : step calls numFastBody s = .jump e0 :=
          fracHead_step_entry_digit (env := s.env) (s := s) (a := p) (j := i0 + c)
            (b := b) (fdig := BitVec.ofNat 64 (d0 + c)) (fr := fr) hpc hpre0 hp
            (BlockEval.evalOperand_reg_of s.env s "%i.6552" _ hi)
            (BlockEval.evalOperand_reg_of s.env s "%fdig.0554" _ hid)
            (BlockEval.evalOperand_reg_of s.env s "%fr.0556" _ hfr) hj hbyte_s hdigit
        have hidig0 : lookupName e0.env "%fdig.3594"
            = some (.int 64 (BitVec.ofNat 64 (d0 + c))) := by
          simp only [e0, stateAt, fracHeadEnv, fracHeadPhiEnv]
          block_lk
        by_cases hguard : (BitVec.ofNat 64 (d0 + c)).ult (19#64) = true
        · let e1 : State := stateAt (fracBodyEnv e0.env (BitVec.ofNat 64 (d0 + c)))
              { e0 with pc := "if.then133", pre := some "while.body130" }
          have hstep2 : step calls numFastBody e0 = .jump e1 :=
            fracBody_step_taken (env := e0.env) (s := e0)
              (fdig := BitVec.ofNat 64 (d0 + c)) (by simp only [e0, stateAt])
              hidig0 hguard
          have hfr1 : lookupName e1.env "%fr.3593" = some (.int 64 fr) := by
            simp only [e1, e0, stateAt, fracBodyEnv, fracHeadEnv, fracHeadPhiEnv]
            block_lk
          have h8 : lookupName e1.env "%18" = some (.int 8 (JsonScanLane.vByte b)) := by
            simp only [e1, e0, stateAt, fracBodyEnv, fracHeadEnv, fracHeadPhiEnv]
            block_lk
          let e2 : State := stateAt (fracIfThenEnv e1.env fr b)
              { e1 with pc := "if.end140", pre := some "if.then133" }
          have hstep3 : step calls numFastBody e1 = .jump e2 :=
            fracIfThen_step (env := e1.env) (s := e1) (by simp only [e1, stateAt])
              hfr1 h8
          have hphi : phiIncoming "if.then133"
              [("if.then133", (Operand.reg "%add139")),
               ("while.body130", (Operand.reg "%fr.3593"))] = some (Operand.reg "%add139") := by
            simp only [phiIncoming]; rfl
          have hphiOp : evalOperand (stateAt e2.env e2) (Operand.reg "%add139")
              = some (.int 64
                (fr * 10 + BitVec.ofNat 64
                  (JsonScanLane.vByte b &&& 0x0f#8).toNat)) := by
            refine BlockEval.evalOperand_reg_of e2.env e2 "%add139" _ ?_
            simp only [e2, e1, stateAt, fracIfThenEnv, lookupName_cons_self]
          have hidig2 : lookupName e2.env "%fdig.3594"
              = some (.int 64 (BitVec.ofNat 64 (d0 + c))) := by
            simp only [e2, e1, e0, stateAt, fracIfThenEnv, fracBodyEnv, fracHeadEnv,
              fracHeadPhiEnv]
            block_lk
          have hi2 : lookupName e2.env "%i.9595"
              = some (.int 64 (BitVec.ofNat 64 (i0 + c))) := by
            simp only [e2, e1, e0, stateAt, fracIfThenEnv, fracBodyEnv, fracHeadEnv,
              fracHeadPhiEnv]
            block_lk
          have hn2 : lookupName e2.env "%n"
              = some (.int 64 (BitVec.ofNat 64 n)) := by
            simp only [e2, e1, e0, stateAt, fracIfThenEnv, fracBodyEnv, fracHeadEnv,
              fracHeadPhiEnv]
            block_lk
          let e3 : State := stateAt
              (fracIfEndEnv e2.env
                (fr * 10 + BitVec.ofNat 64 (JsonScanLane.vByte b &&& 0x0f#8).toNat)
                (BitVec.ofNat 64 (d0 + c)) (BitVec.ofNat 64 (i0 + c))
                (BitVec.ofNat 64 n))
              { e2 with pc := "if.end230", pre := some "if.end140" }
          have hstep4 : step calls numFastBody e2 = .jump e3 :=
            fracIfEnd_step_exit (env := e2.env) (s := e2)
              (fdig := BitVec.ofNat 64 (d0 + c))
              (i := BitVec.ofNat 64 (i0 + c)) (n := BitVec.ofNat 64 n)
              (p := "if.then133") (op := Operand.reg "%add139")
              (frv := fr * 10 + BitVec.ofNat 64
                (JsonScanLane.vByte b &&& 0x0f#8).toNat)
              (by simp only [e2, stateAt]) (by simp only [e2, stateAt]) hphi hphiOp
              hidig2 hi2 hn2 hbits
          refine ⟨e3, 4, by omega, Or.inr (by simp only [e3, stateAt]), ?_, ?_⟩
          · refine Or.inr ⟨by simp only [e3, stateAt], by simp only [e3, stateAt], ?_⟩
            refine ⟨by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
            · simp only [e3, e2, e1, e0, stateAt, fracIfEndEnv, fracIfThenEnv, fracBodyEnv,
                fracHeadEnv, fracHeadPhiEnv]
              block_lk
            · simp only [e3, e2, e1, e0, stateAt, fracIfEndEnv, fracIfThenEnv, fracBodyEnv,
                fracHeadEnv, fracHeadPhiEnv]
              block_lk
            · rw [← h_eq]
              simp only [e3, stateAt, fracIfEndEnv]
              block_lk
              exact int_succ_eq _ hnext64
            · rw [← h_eq]
              simp only [e3, stateAt, fracIfEndEnv]
              rw [hcnt64]
              block_lk
              exact int_succ_eq _ hd0next64
            · have hbyteD : bs.getD (i0 + c) 0 = b :=
                getD_of_readBytes hread (by omega) hbyte
              have hval : fr * 10 + BitVec.ofNat 64
                  (JsonScanLane.vByte b &&& 0x0f#8).toNat
                  = BitVec.ofNat 64
                    (digitFold bs (i0 - d0) (min (d0 + (i0 + c + 1 - i0)) 19)) := by
                rw [hcnt64]
                exact digitFold_step_at hd0le (ofNat_ult_true (by omega) hguard)
                  (by rw [hblen]; omega) hbyteD hdigit rfl
              rw [← h_eq]
              simp only [e3, stateAt, fracIfEndEnv]
              block_lk
              exact congrArg (fun x : BitVec 64 => some (Value.int 64 x)) hval
            · simp only [e3, e2, e1, e0, stateAt, fracIfEndEnv, fracIfThenEnv, fracBodyEnv,
                fracHeadEnv, fracHeadPhiEnv]
              block_lk
            · refine ⟨idig5, ip5, ?_, ?_⟩
              · simp only [e3, e2, e1, e0, stateAt, fracIfEndEnv, fracIfThenEnv, fracBodyEnv,
                  fracHeadEnv, fracHeadPhiEnv]
                block_lk
              · simp only [e3, e2, e1, e0, stateAt, fracIfEndEnv, fracIfThenEnv, fracBodyEnv,
                  fracHeadEnv, fracHeadPhiEnv]
                block_lk
          · intro k
            rw [show 4 + k = 1 + (1 + (1 + (1 + k))) from by omega,
              runFuel_jump_prefix hstep1 (1 + (1 + (1 + k))),
              runFuel_jump_prefix hstep2 (1 + (1 + k)),
              runFuel_jump_prefix hstep3 (1 + k),
              runFuel_jump_prefix hstep4 k]
        · have hguard' : (BitVec.ofNat 64 (d0 + c)).ult (19#64) = false := by
            cases h : (BitVec.ofNat 64 (d0 + c)).ult (19#64)
            · rfl
            · exact absurd h hguard
          let e1 : State := stateAt (fracBodyEnv e0.env (BitVec.ofNat 64 (d0 + c)))
              { e0 with pc := "if.end140", pre := some "while.body130" }
          have hstep2 : step calls numFastBody e0 = .jump e1 :=
            fracBody_step_skip (env := e0.env) (s := e0)
              (fdig := BitVec.ofNat 64 (d0 + c)) (by simp only [e0, stateAt])
              hidig0 hguard'
          have hphi : phiIncoming "while.body130"
              [("if.then133", (Operand.reg "%add139")),
               ("while.body130", (Operand.reg "%fr.3593"))] = some (Operand.reg "%fr.3593") := by
            simp only [phiIncoming]; rfl
          have hfr1 : lookupName e1.env "%fr.3593" = some (.int 64 fr) := by
            simp only [e1, e0, stateAt, fracBodyEnv, fracHeadEnv, fracHeadPhiEnv]
            block_lk
          have hphiOp : evalOperand (stateAt e1.env e1) (Operand.reg "%fr.3593")
              = some (.int 64 fr) :=
            BlockEval.evalOperand_reg_of e1.env e1 "%fr.3593" _ hfr1
          have hidig1 : lookupName e1.env "%fdig.3594"
              = some (.int 64 (BitVec.ofNat 64 (d0 + c))) := by
            simp only [e1, e0, stateAt, fracBodyEnv, fracHeadEnv, fracHeadPhiEnv]
            block_lk
          have hi1 : lookupName e1.env "%i.9595"
              = some (.int 64 (BitVec.ofNat 64 (i0 + c))) := by
            simp only [e1, e0, stateAt, fracBodyEnv, fracHeadEnv, fracHeadPhiEnv]
            block_lk
          have hn1 : lookupName e1.env "%n"
              = some (.int 64 (BitVec.ofNat 64 n)) := by
            simp only [e1, e0, stateAt, fracBodyEnv, fracHeadEnv, fracHeadPhiEnv]
            block_lk
          let e2 : State := stateAt
              (fracIfEndEnv e1.env fr (BitVec.ofNat 64 (d0 + c))
                (BitVec.ofNat 64 (i0 + c)) (BitVec.ofNat 64 n))
              { e1 with pc := "if.end230", pre := some "if.end140" }
          have hstep3 : step calls numFastBody e1 = .jump e2 :=
            fracIfEnd_step_exit (env := e1.env) (s := e1)
              (fdig := BitVec.ofNat 64 (d0 + c))
              (i := BitVec.ofNat 64 (i0 + c)) (n := BitVec.ofNat 64 n)
              (p := "while.body130") (op := Operand.reg "%fr.3593") (frv := fr)
              (by simp only [e1, stateAt]) (by simp only [e1, stateAt]) hphi hphiOp
              hidig1 hi1 hn1 hbits
          refine ⟨e2, 3, by omega, Or.inr (by simp only [e2, stateAt]), ?_, ?_⟩
          · refine Or.inr ⟨by simp only [e2, stateAt], by simp only [e2, stateAt], ?_⟩
            refine ⟨by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
            · simp only [e2, e1, e0, stateAt, fracIfEndEnv, fracBodyEnv, fracHeadEnv,
                fracHeadPhiEnv]
              block_lk
            · simp only [e2, e1, e0, stateAt, fracIfEndEnv, fracBodyEnv, fracHeadEnv,
                fracHeadPhiEnv]
              block_lk
            · rw [← h_eq]
              simp only [e2, stateAt, fracIfEndEnv]
              block_lk
              exact int_succ_eq _ hnext64
            · rw [← h_eq]
              simp only [e2, stateAt, fracIfEndEnv]
              rw [hcnt64]
              block_lk
              exact int_succ_eq _ hd0next64
            · have hval : fr = BitVec.ofNat 64
                  (digitFold bs (i0 - d0) (min (d0 + (i0 + c + 1 - i0)) 19)) := by
                rw [hcnt64]
                exact digitFold_frozen (ofNat_ult_false (by omega) hguard') rfl
              rw [← h_eq]
              simp only [e2, stateAt, fracIfEndEnv]
              block_lk
              exact congrArg (fun x : BitVec 64 => some (Value.int 64 x)) hval
            · simp only [e2, e1, e0, stateAt, fracIfEndEnv, fracBodyEnv, fracHeadEnv,
                fracHeadPhiEnv]
              block_lk
            · refine ⟨idig5, ip5, ?_, ?_⟩
              · simp only [e2, e1, e0, stateAt, fracIfEndEnv, fracBodyEnv, fracHeadEnv,
                  fracHeadPhiEnv]
                block_lk
              · simp only [e2, e1, e0, stateAt, fracIfEndEnv, fracBodyEnv, fracHeadEnv,
                  fracHeadPhiEnv]
                block_lk
          · intro k
            rw [show 3 + k = 1 + (1 + (1 + k)) from by omega,
              runFuel_jump_prefix hstep1 (1 + (1 + k)),
              runFuel_jump_prefix hstep2 (1 + k),
              runFuel_jump_prefix hstep3 k]
      · obtain ⟨hpre0, hi, hid, hfr⟩ := hback
        let fr : BitVec 64 := BitVec.ofNat 64 (digitFold bs (i0 - d0) (min (d0 + c) 19))
        let e0 : State := stateAt (fracHeadEnv s.env p (i0 + c) b
            (BitVec.ofNat 64 (d0 + c)) fr)
          { s with pc := "while.body130", pre := some "land.lhs.true119" }
        have hstep1 : step calls numFastBody s = .jump e0 :=
          fracHead_step_back_digit (env := s.env) (s := s) (a := p) (j := i0 + c)
            (b := b) (fdig := BitVec.ofNat 64 (d0 + c)) (fr := fr) hpc hpre0 hp
            (BlockEval.evalOperand_reg_of s.env s "%inc142" _ hi)
            (BlockEval.evalOperand_reg_of s.env s "%inc141" _ hid)
            (BlockEval.evalOperand_reg_of s.env s "%fr.4" _ hfr) hj hbyte_s hdigit
        have hidig0 : lookupName e0.env "%fdig.3594"
            = some (.int 64 (BitVec.ofNat 64 (d0 + c))) := by
          simp only [e0, stateAt, fracHeadEnv, fracHeadPhiEnv]
          block_lk
        by_cases hguard : (BitVec.ofNat 64 (d0 + c)).ult (19#64) = true
        · let e1 : State := stateAt (fracBodyEnv e0.env (BitVec.ofNat 64 (d0 + c)))
              { e0 with pc := "if.then133", pre := some "while.body130" }
          have hstep2 : step calls numFastBody e0 = .jump e1 :=
            fracBody_step_taken (env := e0.env) (s := e0)
              (fdig := BitVec.ofNat 64 (d0 + c)) (by simp only [e0, stateAt])
              hidig0 hguard
          have hfr1 : lookupName e1.env "%fr.3593" = some (.int 64 fr) := by
            simp only [e1, e0, stateAt, fracBodyEnv, fracHeadEnv, fracHeadPhiEnv]
            block_lk
          have h8 : lookupName e1.env "%18" = some (.int 8 (JsonScanLane.vByte b)) := by
            simp only [e1, e0, stateAt, fracBodyEnv, fracHeadEnv, fracHeadPhiEnv]
            block_lk
          let e2 : State := stateAt (fracIfThenEnv e1.env fr b)
              { e1 with pc := "if.end140", pre := some "if.then133" }
          have hstep3 : step calls numFastBody e1 = .jump e2 :=
            fracIfThen_step (env := e1.env) (s := e1) (by simp only [e1, stateAt])
              hfr1 h8
          have hphi : phiIncoming "if.then133"
              [("if.then133", (Operand.reg "%add139")),
               ("while.body130", (Operand.reg "%fr.3593"))] = some (Operand.reg "%add139") := by
            simp only [phiIncoming]; rfl
          have hphiOp : evalOperand (stateAt e2.env e2) (Operand.reg "%add139")
              = some (.int 64
                (fr * 10 + BitVec.ofNat 64
                  (JsonScanLane.vByte b &&& 0x0f#8).toNat)) := by
            refine BlockEval.evalOperand_reg_of e2.env e2 "%add139" _ ?_
            simp only [e2, e1, stateAt, fracIfThenEnv, lookupName_cons_self]
          have hidig2 : lookupName e2.env "%fdig.3594"
              = some (.int 64 (BitVec.ofNat 64 (d0 + c))) := by
            simp only [e2, e1, e0, stateAt, fracIfThenEnv, fracBodyEnv, fracHeadEnv,
              fracHeadPhiEnv]
            block_lk
          have hi2 : lookupName e2.env "%i.9595"
              = some (.int 64 (BitVec.ofNat 64 (i0 + c))) := by
            simp only [e2, e1, e0, stateAt, fracIfThenEnv, fracBodyEnv, fracHeadEnv,
              fracHeadPhiEnv]
            block_lk
          have hn2 : lookupName e2.env "%n"
              = some (.int 64 (BitVec.ofNat 64 n)) := by
            simp only [e2, e1, e0, stateAt, fracIfThenEnv, fracBodyEnv, fracHeadEnv,
              fracHeadPhiEnv]
            block_lk
          let e3 : State := stateAt
              (fracIfEndEnv e2.env
                (fr * 10 + BitVec.ofNat 64 (JsonScanLane.vByte b &&& 0x0f#8).toNat)
                (BitVec.ofNat 64 (d0 + c)) (BitVec.ofNat 64 (i0 + c))
                (BitVec.ofNat 64 n))
              { e2 with pc := "if.end230", pre := some "if.end140" }
          have hstep4 : step calls numFastBody e2 = .jump e3 :=
            fracIfEnd_step_exit (env := e2.env) (s := e2)
              (fdig := BitVec.ofNat 64 (d0 + c))
              (i := BitVec.ofNat 64 (i0 + c)) (n := BitVec.ofNat 64 n)
              (p := "if.then133") (op := Operand.reg "%add139")
              (frv := fr * 10 + BitVec.ofNat 64
                (JsonScanLane.vByte b &&& 0x0f#8).toNat)
              (by simp only [e2, stateAt]) (by simp only [e2, stateAt]) hphi hphiOp
              hidig2 hi2 hn2 hbits
          refine ⟨e3, 4, by omega, Or.inr (by simp only [e3, stateAt]), ?_, ?_⟩
          · refine Or.inr ⟨by simp only [e3, stateAt], by simp only [e3, stateAt], ?_⟩
            refine ⟨by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
            · simp only [e3, e2, e1, e0, stateAt, fracIfEndEnv, fracIfThenEnv, fracBodyEnv,
                fracHeadEnv, fracHeadPhiEnv]
              block_lk
            · simp only [e3, e2, e1, e0, stateAt, fracIfEndEnv, fracIfThenEnv, fracBodyEnv,
                fracHeadEnv, fracHeadPhiEnv]
              block_lk
            · rw [← h_eq]
              simp only [e3, stateAt, fracIfEndEnv]
              block_lk
              exact int_succ_eq _ hnext64
            · rw [← h_eq]
              simp only [e3, stateAt, fracIfEndEnv]
              rw [hcnt64]
              block_lk
              exact int_succ_eq _ hd0next64
            · have hbyteD : bs.getD (i0 + c) 0 = b :=
                getD_of_readBytes hread (by omega) hbyte
              have hval : fr * 10 + BitVec.ofNat 64
                  (JsonScanLane.vByte b &&& 0x0f#8).toNat
                  = BitVec.ofNat 64
                    (digitFold bs (i0 - d0) (min (d0 + (i0 + c + 1 - i0)) 19)) := by
                rw [hcnt64]
                exact digitFold_step_at hd0le (ofNat_ult_true (by omega) hguard)
                  (by rw [hblen]; omega) hbyteD hdigit rfl
              rw [← h_eq]
              simp only [e3, stateAt, fracIfEndEnv]
              block_lk
              exact congrArg (fun x : BitVec 64 => some (Value.int 64 x)) hval
            · simp only [e3, e2, e1, e0, stateAt, fracIfEndEnv, fracIfThenEnv, fracBodyEnv,
                fracHeadEnv, fracHeadPhiEnv]
              block_lk
            · refine ⟨idig5, ip5, ?_, ?_⟩
              · simp only [e3, e2, e1, e0, stateAt, fracIfEndEnv, fracIfThenEnv, fracBodyEnv,
                  fracHeadEnv, fracHeadPhiEnv]
                block_lk
              · simp only [e3, e2, e1, e0, stateAt, fracIfEndEnv, fracIfThenEnv, fracBodyEnv,
                  fracHeadEnv, fracHeadPhiEnv]
                block_lk
          · intro k
            rw [show 4 + k = 1 + (1 + (1 + (1 + k))) from by omega,
              runFuel_jump_prefix hstep1 (1 + (1 + (1 + k))),
              runFuel_jump_prefix hstep2 (1 + (1 + k)),
              runFuel_jump_prefix hstep3 (1 + k),
              runFuel_jump_prefix hstep4 k]
        · have hguard' : (BitVec.ofNat 64 (d0 + c)).ult (19#64) = false := by
            cases h : (BitVec.ofNat 64 (d0 + c)).ult (19#64)
            · rfl
            · exact absurd h hguard
          let e1 : State := stateAt (fracBodyEnv e0.env (BitVec.ofNat 64 (d0 + c)))
              { e0 with pc := "if.end140", pre := some "while.body130" }
          have hstep2 : step calls numFastBody e0 = .jump e1 :=
            fracBody_step_skip (env := e0.env) (s := e0)
              (fdig := BitVec.ofNat 64 (d0 + c)) (by simp only [e0, stateAt])
              hidig0 hguard'
          have hphi : phiIncoming "while.body130"
              [("if.then133", (Operand.reg "%add139")),
               ("while.body130", (Operand.reg "%fr.3593"))] = some (Operand.reg "%fr.3593") := by
            simp only [phiIncoming]; rfl
          have hfr1 : lookupName e1.env "%fr.3593" = some (.int 64 fr) := by
            simp only [e1, e0, stateAt, fracBodyEnv, fracHeadEnv, fracHeadPhiEnv]
            block_lk
          have hphiOp : evalOperand (stateAt e1.env e1) (Operand.reg "%fr.3593")
              = some (.int 64 fr) :=
            BlockEval.evalOperand_reg_of e1.env e1 "%fr.3593" _ hfr1
          have hidig1 : lookupName e1.env "%fdig.3594"
              = some (.int 64 (BitVec.ofNat 64 (d0 + c))) := by
            simp only [e1, e0, stateAt, fracBodyEnv, fracHeadEnv, fracHeadPhiEnv]
            block_lk
          have hi1 : lookupName e1.env "%i.9595"
              = some (.int 64 (BitVec.ofNat 64 (i0 + c))) := by
            simp only [e1, e0, stateAt, fracBodyEnv, fracHeadEnv, fracHeadPhiEnv]
            block_lk
          have hn1 : lookupName e1.env "%n"
              = some (.int 64 (BitVec.ofNat 64 n)) := by
            simp only [e1, e0, stateAt, fracBodyEnv, fracHeadEnv, fracHeadPhiEnv]
            block_lk
          let e2 : State := stateAt
              (fracIfEndEnv e1.env fr (BitVec.ofNat 64 (d0 + c))
                (BitVec.ofNat 64 (i0 + c)) (BitVec.ofNat 64 n))
              { e1 with pc := "if.end230", pre := some "if.end140" }
          have hstep3 : step calls numFastBody e1 = .jump e2 :=
            fracIfEnd_step_exit (env := e1.env) (s := e1)
              (fdig := BitVec.ofNat 64 (d0 + c))
              (i := BitVec.ofNat 64 (i0 + c)) (n := BitVec.ofNat 64 n)
              (p := "while.body130") (op := Operand.reg "%fr.3593") (frv := fr)
              (by simp only [e1, stateAt]) (by simp only [e1, stateAt]) hphi hphiOp
              hidig1 hi1 hn1 hbits
          refine ⟨e2, 3, by omega, Or.inr (by simp only [e2, stateAt]), ?_, ?_⟩
          · refine Or.inr ⟨by simp only [e2, stateAt], by simp only [e2, stateAt], ?_⟩
            refine ⟨by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
            · simp only [e2, e1, e0, stateAt, fracIfEndEnv, fracBodyEnv, fracHeadEnv,
                fracHeadPhiEnv]
              block_lk
            · simp only [e2, e1, e0, stateAt, fracIfEndEnv, fracBodyEnv, fracHeadEnv,
                fracHeadPhiEnv]
              block_lk
            · rw [← h_eq]
              simp only [e2, stateAt, fracIfEndEnv]
              block_lk
              exact int_succ_eq _ hnext64
            · rw [← h_eq]
              simp only [e2, stateAt, fracIfEndEnv]
              rw [hcnt64]
              block_lk
              exact int_succ_eq _ hd0next64
            · have hval : fr = BitVec.ofNat 64
                  (digitFold bs (i0 - d0) (min (d0 + (i0 + c + 1 - i0)) 19)) := by
                rw [hcnt64]
                exact digitFold_frozen (ofNat_ult_false (by omega) hguard') rfl
              rw [← h_eq]
              simp only [e2, stateAt, fracIfEndEnv]
              block_lk
              exact congrArg (fun x : BitVec 64 => some (Value.int 64 x)) hval
            · simp only [e2, e1, e0, stateAt, fracIfEndEnv, fracBodyEnv, fracHeadEnv,
                fracHeadPhiEnv]
              block_lk
            · refine ⟨idig5, ip5, ?_, ?_⟩
              · simp only [e2, e1, e0, stateAt, fracIfEndEnv, fracBodyEnv, fracHeadEnv,
                  fracHeadPhiEnv]
                block_lk
              · simp only [e2, e1, e0, stateAt, fracIfEndEnv, fracBodyEnv, fracHeadEnv,
                  fracHeadPhiEnv]
                block_lk
          · intro k
            rw [show 3 + k = 1 + (1 + (1 + k)) from by omega,
              runFuel_jump_prefix hstep1 (1 + (1 + k)),
              runFuel_jump_prefix hstep2 (1 + k),
              runFuel_jump_prefix hstep3 k]
    · have hdigit' : IsDigitB b = false := by
        cases h : IsDigitB b
        · rfl
        · exact absurd h hdigit
      rcases hpre with hent | hback
      · obtain ⟨hpre0, hi, hid, hfr⟩ := hent
        let fr : BitVec 64 := BitVec.ofNat 64 (digitFold bs (i0 - d0) (min (d0 + c) 19))
        let e0 : State := stateAt (fracHeadEnv s.env p (i0 + c) b
            (BitVec.ofNat 64 (d0 + c)) fr)
          { s with pc := "if.end144", pre := some "land.lhs.true119" }
        have hstep1 : step calls numFastBody s = .jump e0 :=
          fracHead_step_entry_nondigit (env := s.env) (s := s) (a := p) (j := i0 + c)
            (b := b) (fdig := BitVec.ofNat 64 (d0 + c)) (fr := fr) hpc hpre0 hp
            (BlockEval.evalOperand_reg_of s.env s "%i.6552" _ hi)
            (BlockEval.evalOperand_reg_of s.env s "%fdig.0554" _ hid)
            (BlockEval.evalOperand_reg_of s.env s "%fr.0556" _ hfr) hj hbyte_s hdigit'
        refine ⟨e0, 1, by omega, Or.inl (by simp only [e0, stateAt]), ?_, ?_⟩
        · refine Or.inl ⟨by simp only [e0, stateAt], by simp only [e0, stateAt],
            by simp only [e0, stateAt, fracHeadEnv, fracHeadPhiEnv]; block_lk,
            by simp only [e0, stateAt, fracHeadEnv, fracHeadPhiEnv]; block_lk,
            i0 + c, by omega, hltn, ?_, ?_, ?_,
            b, by rw [← hmem]; exact hbyte_s, hdigit'⟩
          · simp only [e0, stateAt, fracHeadEnv, fracHeadPhiEnv]
            block_lk
          · simp only [e0, stateAt, fracHeadEnv, fracHeadPhiEnv]
            rw [show d0 + (i0 + c - i0) = d0 + c from by omega]
            block_lk
          · have hval : fr = BitVec.ofNat 64
                (digitFold bs (i0 - d0) (min (d0 + (i0 + c - i0)) 19)) := by
              rw [show d0 + (i0 + c - i0) = d0 + c from by omega]
            simp only [e0, stateAt, fracHeadEnv, fracHeadPhiEnv]
            block_lk
            exact congrArg (fun x : BitVec 64 => some (Value.int 64 x)) hval
        · intro k
          rw [runFuel_jump_prefix hstep1 k]
      · obtain ⟨hpre0, hi, hid, hfr⟩ := hback
        let fr : BitVec 64 := BitVec.ofNat 64 (digitFold bs (i0 - d0) (min (d0 + c) 19))
        let e0 : State := stateAt (fracHeadEnv s.env p (i0 + c) b
            (BitVec.ofNat 64 (d0 + c)) fr)
          { s with pc := "if.end144", pre := some "land.lhs.true119" }
        have hstep1 : step calls numFastBody s = .jump e0 :=
          fracHead_step_back_nondigit (env := s.env) (s := s) (a := p) (j := i0 + c)
            (b := b) (fdig := BitVec.ofNat 64 (d0 + c)) (fr := fr) hpc hpre0 hp
            (BlockEval.evalOperand_reg_of s.env s "%inc142" _ hi)
            (BlockEval.evalOperand_reg_of s.env s "%inc141" _ hid)
            (BlockEval.evalOperand_reg_of s.env s "%fr.4" _ hfr) hj hbyte_s hdigit'
        refine ⟨e0, 1, by omega, Or.inl (by simp only [e0, stateAt]), ?_, ?_⟩
        · refine Or.inl ⟨by simp only [e0, stateAt], by simp only [e0, stateAt],
            by simp only [e0, stateAt, fracHeadEnv, fracHeadPhiEnv]; block_lk,
            by simp only [e0, stateAt, fracHeadEnv, fracHeadPhiEnv]; block_lk,
            i0 + c, by omega, hltn, ?_, ?_, ?_,
            b, by rw [← hmem]; exact hbyte_s, hdigit'⟩
          · simp only [e0, stateAt, fracHeadEnv, fracHeadPhiEnv]
            block_lk
          · simp only [e0, stateAt, fracHeadEnv, fracHeadPhiEnv]
            rw [show d0 + (i0 + c - i0) = d0 + c from by omega]
            block_lk
          · have hval : fr = BitVec.ofNat 64
                (digitFold bs (i0 - d0) (min (d0 + (i0 + c - i0)) 19)) := by
              rw [show d0 + (i0 + c - i0) = d0 + c from by omega]
            simp only [e0, stateAt, fracHeadEnv, fracHeadPhiEnv]
            block_lk
            exact congrArg (fun x : BitVec 64 => some (Value.int 64 x)) hval
        · intro k
          rw [runFuel_jump_prefix hstep1 k]
  · obtain ⟨b', hbyte', hdigit'⟩ := fracRun_bound_nondigit hread hltn hb hle
    have hbyte'_s : readByte s.mem (p + (i0 + c)) = some b' := by rw [hmem]; exact hbyte'
    have hbb : b = b' := Option.some.inj (hbyte.symm.trans hbyte')
    subst hbb
    rcases hpre with hent | hback
    · obtain ⟨hpre0, hi, hid, hfr⟩ := hent
      let fr : BitVec 64 := BitVec.ofNat 64 (digitFold bs (i0 - d0) (min (d0 + c) 19))
      let e0 : State := stateAt (fracHeadEnv s.env p (i0 + c) b
          (BitVec.ofNat 64 (d0 + c)) fr)
        { s with pc := "if.end144", pre := some "land.lhs.true119" }
      have hstep1 : step calls numFastBody s = .jump e0 :=
        fracHead_step_entry_nondigit (env := s.env) (s := s) (a := p) (j := i0 + c)
          (b := b) (fdig := BitVec.ofNat 64 (d0 + c)) (fr := fr) hpc hpre0 hp
          (BlockEval.evalOperand_reg_of s.env s "%i.6552" _ hi)
          (BlockEval.evalOperand_reg_of s.env s "%fdig.0554" _ hid)
          (BlockEval.evalOperand_reg_of s.env s "%fr.0556" _ hfr) hj hbyte'_s hdigit'
      refine ⟨e0, 1, by omega, Or.inl (by simp only [e0, stateAt]), ?_, ?_⟩
      · refine Or.inl ⟨by simp only [e0, stateAt], by simp only [e0, stateAt],
          by simp only [e0, stateAt, fracHeadEnv, fracHeadPhiEnv]; block_lk,
          by simp only [e0, stateAt, fracHeadEnv, fracHeadPhiEnv]; block_lk,
          i0 + c, by omega, hltn, ?_, ?_, ?_,
          b, by rw [← hmem]; exact hbyte'_s, hdigit'⟩
        · simp only [e0, stateAt, fracHeadEnv, fracHeadPhiEnv]
          block_lk
        · simp only [e0, stateAt, fracHeadEnv, fracHeadPhiEnv]
          rw [show d0 + (i0 + c - i0) = d0 + c from by omega]
          block_lk
        · have hval : fr = BitVec.ofNat 64
              (digitFold bs (i0 - d0) (min (d0 + (i0 + c - i0)) 19)) := by
            rw [show d0 + (i0 + c - i0) = d0 + c from by omega]
          simp only [e0, stateAt, fracHeadEnv, fracHeadPhiEnv]
          block_lk
          exact congrArg (fun x : BitVec 64 => some (Value.int 64 x)) hval
      · intro k
        rw [runFuel_jump_prefix hstep1 k]
    · obtain ⟨hpre0, hi, hid, hfr⟩ := hback
      let fr : BitVec 64 := BitVec.ofNat 64 (digitFold bs (i0 - d0) (min (d0 + c) 19))
      let e0 : State := stateAt (fracHeadEnv s.env p (i0 + c) b
          (BitVec.ofNat 64 (d0 + c)) fr)
        { s with pc := "if.end144", pre := some "land.lhs.true119" }
      have hstep1 : step calls numFastBody s = .jump e0 :=
        fracHead_step_back_nondigit (env := s.env) (s := s) (a := p) (j := i0 + c)
          (b := b) (fdig := BitVec.ofNat 64 (d0 + c)) (fr := fr) hpc hpre0 hp
          (BlockEval.evalOperand_reg_of s.env s "%inc142" _ hi)
          (BlockEval.evalOperand_reg_of s.env s "%inc141" _ hid)
          (BlockEval.evalOperand_reg_of s.env s "%fr.4" _ hfr) hj hbyte'_s hdigit'
      refine ⟨e0, 1, by omega, Or.inl (by simp only [e0, stateAt]), ?_, ?_⟩
      · refine Or.inl ⟨by simp only [e0, stateAt], by simp only [e0, stateAt],
          by simp only [e0, stateAt, fracHeadEnv, fracHeadPhiEnv]; block_lk,
          by simp only [e0, stateAt, fracHeadEnv, fracHeadPhiEnv]; block_lk,
          i0 + c, by omega, hltn, ?_, ?_, ?_,
          b, by rw [← hmem]; exact hbyte'_s, hdigit'⟩
        · simp only [e0, stateAt, fracHeadEnv, fracHeadPhiEnv]
          block_lk
        · simp only [e0, stateAt, fracHeadEnv, fracHeadPhiEnv]
          rw [show d0 + (i0 + c - i0) = d0 + c from by omega]
          block_lk
        · have hval : fr = BitVec.ofNat 64
              (digitFold bs (i0 - d0) (min (d0 + (i0 + c - i0)) 19)) := by
            rw [show d0 + (i0 + c - i0) = d0 + c from by omega]
          simp only [e0, stateAt, fracHeadEnv, fracHeadPhiEnv]
          block_lk
          exact congrArg (fun x : BitVec 64 => some (Value.int 64 x)) hval
      · intro k
        rw [runFuel_jump_prefix hstep1 k]

def fracRunBoundLoop (mem0 : Mem) (p n i0 d0 : Nat) (bs : List UInt8) (cost : Nat)
    (hcost : 4 ≤ cost) : BoundLoop calls numFastBody where
  head := "land.lhs.true119"
  exitBlock := "if.end144"
  N := n - i0
  cost := cost
  Inv := fracRunInv mem0 p n i0 d0 bs
  atBound := fracRunAtBound mem0 p n i0
  Exit := fracRunExitBlock
  ExitWord := fracRunExit mem0 bs p n i0 d0
  step_exit := by
    intro r s c hinv hb
    obtain ⟨e, j, hj, hexit, hword, hrun⟩ := fracRun_step_exit hinv hb
    exact ⟨e, j, by omega, hexit, hword, hrun⟩
  step_loop := by
    intro r s c hinv hb
    obtain ⟨e, c', j, hj, hpc, hlt, hinv', hrun⟩ := fracRun_step_loop hinv hb
    exact ⟨e, c', j, by omega, hpc, hlt, hinv', hrun⟩
  exit_at_zero := by
    intro s c h
    obtain ⟨_, _, hsum, _, _, _, _, _, _, _, _, _⟩ := h
    unfold fracRunAtBound
    have hle : decide (n - i0 ≤ c + 1) = true := decide_eq_true (by omega)
    rw [hle]
    simp
  budget := by
    intro r s c h
    obtain ⟨_, _, hsum, _, _, _, _, _, _, _, _, _⟩ := h
    omega

theorem fracRun_run (mem0 : Mem) (p n i0 d0 : Nat) (bs : List UInt8) (cost : Nat)
    (hcost : 4 ≤ cost) (s : State) (c : Nat)
    (hinv : fracRunInv mem0 p n i0 d0 bs (n - i0) s c) (k : Nat) :
    ∃ (e : State) (j : Nat), j ≤ (n - i0 + 1) * cost ∧ fracRunExitBlock e ∧
      fracRunExit mem0 bs p n i0 d0 e ∧
      runFuel calls (j + k) numFastBody s =
        runFuel calls k numFastBody e :=
  (fracRunBoundLoop mem0 p n i0 d0 bs cost hcost).run s c hinv k

/-- **The fraction run's end-of-lexeme exit when every remaining byte is a
digit.**  The non-digit exit's own stop byte is a non-digit, so a lexeme whose
bytes from the run's start to its end are digits rules that arm out and leaves
`if.end140`'s end-of-lexeme edge — the arm a composition needs to know the run
stopped at the lexeme's end. -/
theorem fracRun_step_end230 {mem0 : Mem} {p n i0 d0 r : Nat} {bs : List UInt8}
    {s : State} {c : Nat}
    (hinv : fracRunInv mem0 p n i0 d0 bs r s c)
    (hb : fracRunAtBound mem0 p n i0 s c = true)
    (hdigits : ∀ k, i0 ≤ k → k < n → IsDigitB (bs.getD k 0) = true) :
    ∃ (e : State) (j : Nat), j ≤ 4 ∧ fracRunEndWord bs p n i0 d0 e ∧
      ∀ k, runFuel calls (j + k) numFastBody s =
        runFuel calls k numFastBody e := by
  obtain ⟨e, j, hj, _, hexit, hrun⟩ := fracRun_step_exit hinv hb
  obtain ⟨_, _, _, _, _, _, _, _, hread, _, _, _⟩ := hinv
  rcases hexit with ⟨_, _, _, _, i1, hi0, hi1lt, _, _, _, b, hbytei, hbd⟩ | hend
  · have hbs : bs.getD i1 0 = b := getD_of_readBytes hread hi1lt hbytei
    have hdig := hdigits i1 hi0 hi1lt
    rw [hbs, hbd] at hdig
    exact absurd hdig (by decide)
  · exact ⟨e, j, hj, hend, hrun⟩

/-- **The fraction run's end-of-lexeme loop.**  With every byte from the run's
start to the lexeme's end a digit, the run's only bound is the lexeme's end, so
its exit is the end-of-lexeme one and the exit word is `fracRunEndWord`. -/
def fracRunEndBoundLoop (mem0 : Mem) (p n i0 d0 : Nat) (bs : List UInt8) (cost : Nat)
    (hcost : 4 ≤ cost)
    (hdigits : ∀ k, i0 ≤ k → k < n → IsDigitB (bs.getD k 0) = true) :
    BoundLoop calls numFastBody where
  head := "land.lhs.true119"
  exitBlock := "if.end230"
  N := n - i0
  cost := cost
  Inv := fracRunInv mem0 p n i0 d0 bs
  atBound := fracRunAtBound mem0 p n i0
  Exit := fun e => e.pc = "if.end230"
  ExitWord := fracRunEndWord bs p n i0 d0
  step_exit := by
    intro r s c hinv hb
    obtain ⟨e, j, hj, hword, hrun⟩ := fracRun_step_end230 hinv hb hdigits
    exact ⟨e, j, by omega, hword.1, hword, hrun⟩
  step_loop := by
    intro r s c hinv hb
    obtain ⟨e, c', j, hj, hpc, hlt, hinv', hrun⟩ := fracRun_step_loop hinv hb
    exact ⟨e, c', j, by omega, hpc, hlt, hinv', hrun⟩
  exit_at_zero := by
    intro s c h
    obtain ⟨_, _, hsum, _, _, _, _, _, _, _, _, _⟩ := h
    unfold fracRunAtBound
    have hle : decide (n - i0 ≤ c + 1) = true := decide_eq_true (by omega)
    rw [hle]
    simp
  budget := by
    intro r s c h
    obtain ⟨_, _, hsum, _, _, _, _, _, _, _, _, _⟩ := h
    omega

/-- **The fraction run reaches the lexeme's end.**  At the whole distance as its
budget, a run whose remaining bytes are all digits leaves at `if.end230` with the
end-of-lexeme exit word within `(n - i0 + 1) * cost` control steps. -/
theorem fracRun_end_run (mem0 : Mem) (p n i0 d0 : Nat) (bs : List UInt8) (cost : Nat)
    (hcost : 4 ≤ cost)
    (hdigits : ∀ k, i0 ≤ k → k < n → IsDigitB (bs.getD k 0) = true)
    (s : State) (c : Nat)
    (hinv : fracRunInv mem0 p n i0 d0 bs (n - i0) s c) (k : Nat) :
    ∃ (e : State) (j : Nat), j ≤ (n - i0 + 1) * cost ∧ e.pc = "if.end230" ∧
      fracRunEndWord bs p n i0 d0 e ∧
      runFuel calls (j + k) numFastBody s =
        runFuel calls k numFastBody e :=
  (fracRunEndBoundLoop mem0 p n i0 d0 bs cost hcost hdigits).run s c hinv k

/-! ### The exponent run: `land.lhs.true195`

The third run differs in two ways: its accumulator is the exponent's value rather
than a digit count, and its guard is the signed `%exp10.0603 < 100000` (the
emitted saturation), so the accumulator is carried as the value it reads.  Both
exits land in `cleanup223.thread`.

The head's `exp10` phi has the immediate `0` on its entry edge
(`lor.lhs.false180`), so the entry arm carries no accumulator register: the phi
brings zero. -/

def expHeadPhiEnv (env : Env) (j : Nat) (v : BitVec 64) : Env :=
  ("%exp10.0603", .int 64 v) ::
  ("%i.12604", .int 64 (BitVec.ofNat 64 j)) :: env

def expHeadEnv (env : Env) (a j : Nat) (b : UInt8) (v : BitVec 64) : Env :=
  ("%or.cond445", .int 1 (BitVec.ofBool (IsDigitB b))) ::
  ("%26", .int 8 (JsonScanLane.vByte b + 0xd0#8)) ::
  ("%25", .int 8 (JsonScanLane.vByte b)) ::
  ("%arrayidx196", .ptr (a + j)) :: expHeadPhiEnv env j v

theorem lookup_expHeadPhiEnv_p (env : Env) (j : Nat) (v : BitVec 64) (a : Nat) :
    lookupName (expHeadPhiEnv env j v) "%p" = some (.ptr a) ↔
      lookupName env "%p" = some (.ptr a) := by
  simp only [expHeadPhiEnv,
    lookupName_cons_ne (k := "%exp10.0603") (n := "%p") _ _ (by decide),
    lookupName_cons_ne (k := "%i.12604") (n := "%p") _ _ (by decide)]

theorem lookup_expHeadPhiEnv_n (env : Env) (j : Nat) (v : BitVec 64) (n : BitVec 64) :
    lookupName (expHeadPhiEnv env j v) "%n" = some (.int 64 n) ↔
      lookupName env "%n" = some (.int 64 n) := by
  simp only [expHeadPhiEnv,
    lookupName_cons_ne (k := "%exp10.0603") (n := "%n") _ _ (by decide),
    lookupName_cons_ne (k := "%i.12604") (n := "%n") _ _ (by decide)]

theorem lookup_expHeadPhiEnv_i (env : Env) (j : Nat) (v : BitVec 64) :
    lookupName (expHeadPhiEnv env j v) "%i.12604"
      = some (.int 64 (BitVec.ofNat 64 j)) := by
  simp only [expHeadPhiEnv,
    lookupName_cons_ne (k := "%exp10.0603") (n := "%i.12604") _ _ (by decide),
    lookupName_cons_self]

theorem expHead_denote_phi {calls : Calls} {env : Env} {s : State} {a j : Nat}
    {b : UInt8} {v : BitVec 64}
    (hp : lookupName (expHeadPhiEnv env j v) "%p" = some (.ptr a))
    (hj : j < 2 ^ 63)
    (hread : readByte s.mem (a + j) = some b) :
    denoteCode calls
      [Instr.gep "%arrayidx196" (Ty.int 8) (Operand.reg "%p") (Operand.reg "%i.12604"),
       Instr.load "%25" (Ty.int 8) (Operand.reg "%arrayidx196"),
       Instr.binop "%26" (BinOp.add) 8 (Operand.reg "%25")
         (Operand.imm (Const.int 8 0xd0#8)),
       Instr.icmp "%or.cond445" (IPred.ult) 8 (Operand.reg "%26")
         (Operand.imm (Const.int 8 0x0a#8))]
      (stateAt (expHeadPhiEnv env j v) s) =
    some (stateAt (expHeadEnv env a j b v) s) := by
  have ho : lookupName (expHeadPhiEnv env j v) "%i.12604"
      = some (.int 64 (BitVec.ofNat 64 j)) := lookup_expHeadPhiEnv_i env j v
  have hpos : ((BitVec.ofNat 64 j).signExtend 64).toNat < 2 ^ 63 := by
    rw [sExt_ofNat64 hj]; exact hj
  rw [denoteCode_gep8_reg _ _ _ "%arrayidx196" "%p" "%i.12604" hp ho hpos _]
  rw [sExt_ofNat64 hj]
  have ha8 : lookupName
      (("%arrayidx196", .ptr (a + j)) :: expHeadPhiEnv env j v) "%arrayidx196"
      = some (.ptr (a + j)) := lookupName_cons_self ..
  rw [JsonScanLane.denoteCode_load_i8 _ _ _ "%25" "%arrayidx196" ha8
    (readBytes_one_some.mpr hread) _]
  have ha9 : lookupName
      (("%25", .int 8 (JsonScanLane.vByte b)) ::
        ("%arrayidx196", .ptr (a + j)) :: expHeadPhiEnv env j v) "%25"
      = some (.int 8 (JsonScanLane.vByte b)) := lookupName_cons_self ..
  rw [JsonScanLane.denoteCode_add_imm_w _ _ _ "%26" "%25" 8 ha9 _]
  have ha10 : lookupName
      (("%26", .int 8 (JsonScanLane.vByte b + 0xd0#8)) ::
        ("%25", .int 8 (JsonScanLane.vByte b)) ::
        ("%arrayidx196", .ptr (a + j)) :: expHeadPhiEnv env j v) "%26"
      = some (.int 8 (JsonScanLane.vByte b + 0xd0#8)) := lookupName_cons_self ..
  rw [JsonScanLane.denoteCode_icmp_imm_w _ _ _ "%or.cond445" "%26" .ult ha10 _]
  simp only [denoteCode, denoteRun, State.bindAll, stateAt, expHeadEnv, expHeadPhiEnv,
    evalICmp_ult_digit]

theorem expHead_run_entry {calls : Calls} {env : Env} {s : State} {j : Nat}
    (hpre : s.pre = some "lor.lhs.false180")
    (hhi : evalOperand (stateAt env s) (.reg "%i.11")
      = some (.int 64 (BitVec.ofNat 64 j))) :
    denoteCode calls numFastLandLhsTrue195Instrs (stateAt env s) =
      denoteCode calls
        [Instr.gep "%arrayidx196" (Ty.int 8) (Operand.reg "%p") (Operand.reg "%i.12604"),
         Instr.load "%25" (Ty.int 8) (Operand.reg "%arrayidx196"),
         Instr.binop "%26" (BinOp.add) 8 (Operand.reg "%25")
           (Operand.imm (Const.int 8 0xd0#8)),
         Instr.icmp "%or.cond445" (IPred.ult) 8 (Operand.reg "%26")
           (Operand.imm (Const.int 8 0x0a#8))]
        (stateAt (expHeadPhiEnv env j 0) s) := by
  unfold numFastLandLhsTrue195Instrs
  block_phi_run
  rotate_left 1
  · exact hpre
  · rfl
  · simp only [phiIncoming]; rfl
  · exact hhi
  · simp only [phiIncoming]; rfl
  · exact BlockEval.evalOperand_lit_of (stateAt env s) 64 0
  · simp only [runCells, expHeadPhiEnv, stateAt]

theorem expHead_run_back {calls : Calls} {env : Env} {s : State} {j : Nat}
    {v : BitVec 64}
    (hpre : s.pre = some "if.end216")
    (hhi : evalOperand (stateAt env s) (.reg "%inc217")
      = some (.int 64 (BitVec.ofNat 64 j)))
    (hhv : evalOperand (stateAt env s) (.reg "%exp10.1") = some (.int 64 v)) :
    denoteCode calls numFastLandLhsTrue195Instrs (stateAt env s) =
      denoteCode calls
        [Instr.gep "%arrayidx196" (Ty.int 8) (Operand.reg "%p") (Operand.reg "%i.12604"),
         Instr.load "%25" (Ty.int 8) (Operand.reg "%arrayidx196"),
         Instr.binop "%26" (BinOp.add) 8 (Operand.reg "%25")
           (Operand.imm (Const.int 8 0xd0#8)),
         Instr.icmp "%or.cond445" (IPred.ult) 8 (Operand.reg "%26")
           (Operand.imm (Const.int 8 0x0a#8))]
        (stateAt (expHeadPhiEnv env j v) s) := by
  unfold numFastLandLhsTrue195Instrs
  block_phi_run
  rotate_left 1
  · exact hpre
  · rfl
  · simp only [phiIncoming]; rfl
  · exact hhi
  · simp only [phiIncoming]; rfl
  · exact hhv
  · simp only [runCells, expHeadPhiEnv, stateAt]

theorem expHead_denote_entry {calls : Calls} {env : Env} {s : State} {a j : Nat}
    {b : UInt8}
    (hpre : s.pre = some "lor.lhs.false180")
    (hp : lookupName env "%p" = some (.ptr a))
    (hhi : evalOperand (stateAt env s) (.reg "%i.11")
      = some (.int 64 (BitVec.ofNat 64 j)))
    (hj : j < 2 ^ 63) (hread : readByte s.mem (a + j) = some b) :
    denoteCode calls numFastLandLhsTrue195Instrs (stateAt env s) =
      some (stateAt (expHeadEnv env a j b 0) s) := by
  rw [expHead_run_entry (calls := calls) hpre hhi]
  exact expHead_denote_phi ((lookup_expHeadPhiEnv_p env j 0 a).mpr hp) hj hread

theorem expHead_denote_back {calls : Calls} {env : Env} {s : State} {a j : Nat}
    {b : UInt8} {v : BitVec 64}
    (hpre : s.pre = some "if.end216")
    (hp : lookupName env "%p" = some (.ptr a))
    (hhi : evalOperand (stateAt env s) (.reg "%inc217")
      = some (.int 64 (BitVec.ofNat 64 j)))
    (hhv : evalOperand (stateAt env s) (.reg "%exp10.1") = some (.int 64 v))
    (hj : j < 2 ^ 63) (hread : readByte s.mem (a + j) = some b) :
    denoteCode calls numFastLandLhsTrue195Instrs (stateAt env s) =
      some (stateAt (expHeadEnv env a j b v) s) := by
  rw [expHead_run_back (calls := calls) hpre hhi hhv]
  exact expHead_denote_phi ((lookup_expHeadPhiEnv_p env j v a).mpr hp) hj hread

def expBodyEnv (env : Env) (v : BitVec 64) : Env :=
  ("%cmp207", .int 1 (evalICmp .slt v (100000#64))) :: env

theorem expBodyEnv_p (env : Env) (v : BitVec 64) (a : Nat) :
    lookupName (expBodyEnv env v) "%p" = some (.ptr a) ↔
      lookupName env "%p" = some (.ptr a) := by
  simp only [expBodyEnv, lookupName_cons_ne (k := "%cmp207") (n := "%p") _ _ (by decide)]

theorem expBodyEnv_n (env : Env) (v : BitVec 64) (n : BitVec 64) :
    lookupName (expBodyEnv env v) "%n" = some (.int 64 n) ↔
      lookupName env "%n" = some (.int 64 n) := by
  simp only [expBodyEnv, lookupName_cons_ne (k := "%cmp207") (n := "%n") _ _ (by decide)]

theorem expBody_denote {calls : Calls} {env : Env} {s : State} {v : BitVec 64}
    (hv : lookupName env "%exp10.0603" = some (.int 64 v)) :
    denoteCode calls numFastWhileBody206Instrs (stateAt env s) =
      some (stateAt (expBodyEnv env v) s) := by
  unfold numFastWhileBody206Instrs
  rw [JsonScanLane.denoteCode_icmp_imm_w _ _ _ "%cmp207" "%exp10.0603" .slt hv _]
  simp only [denoteCode, denoteRun, State.bindAll, stateAt, expBodyEnv]

theorem expBody_step_taken {env : Env} {s : State} {v : BitVec 64}
    (hpc : s.pc = "while.body206")
    (hv : lookupName env "%exp10.0603" = some (.int 64 v))
    (hlt : evalICmp .slt v (100000#64) = 1) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (expBodyEnv env v)
        { s with pc := "if.then209", pre := some "while.body206" }) := by
  refine numFast_step_at (s' := stateAt (expBodyEnv env v) s)
    (b := ⟨"while.body206", numFastWhileBody206Instrs,
      Term.condbr (.reg "%cmp207") "if.then209" "if.end216"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc, numFastWhileBody206Instrs]
      using numFast_findBlock_while_body206
  · simpa only [denoteCode_nil] using expBody_denote hv
  · have hlk : lookupName (expBodyEnv env v) "%cmp207"
        = some (.int 1 (evalICmp .slt v (100000#64))) := by
      simp only [expBodyEnv, lookupName_cons_self]
    rw [numFast_execTerm_condbr_one _ "%cmp207" _ _ hlk hlt]
    simp only [stateAt, hpc]

theorem expBody_step_skip {env : Env} {s : State} {v : BitVec 64}
    (hpc : s.pc = "while.body206")
    (hv : lookupName env "%exp10.0603" = some (.int 64 v))
    (hlt : evalICmp .slt v (100000#64) = 0) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (expBodyEnv env v)
        { s with pc := "if.end216", pre := some "while.body206" }) := by
  refine numFast_step_at (s' := stateAt (expBodyEnv env v) s)
    (b := ⟨"while.body206", numFastWhileBody206Instrs,
      Term.condbr (.reg "%cmp207") "if.then209" "if.end216"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc, numFastWhileBody206Instrs]
      using numFast_findBlock_while_body206
  · simpa only [denoteCode_nil] using expBody_denote hv
  · have hlk : lookupName (expBodyEnv env v) "%cmp207"
        = some (.int 1 (evalICmp .slt v (100000#64))) := by
      simp only [expBodyEnv, lookupName_cons_self]
    rw [numFast_execTerm_condbr_zero _ "%cmp207" _ _ hlk hlt]
    simp only [stateAt, hpc]

def expIfThenEnv (env : Env) (v : BitVec 64) (b : UInt8) : Env :=
  ("%add215", .int 64
      (v * 10 + BitVec.ofNat 64 (JsonScanLane.vByte b &&& 0x0f#8).toNat)) ::
  ("%conv214", .int 64 (BitVec.ofNat 64 (JsonScanLane.vByte b &&& 0x0f#8).toNat)) ::
  ("%27", .int 8 (JsonScanLane.vByte b &&& 0x0f#8)) ::
  ("%mul210", .int 64 (v * 10)) :: env

theorem expIfThenEnv_p (env : Env) (v : BitVec 64) (b : UInt8) (a : Nat) :
    lookupName (expIfThenEnv env v b) "%p" = some (.ptr a) ↔
      lookupName env "%p" = some (.ptr a) := by
  simp only [expIfThenEnv, lookupName_cons_ne (k := "%add215") (n := "%p") _ _ (by decide),
    lookupName_cons_ne (k := "%conv214") (n := "%p") _ _ (by decide),
    lookupName_cons_ne (k := "%27") (n := "%p") _ _ (by decide),
    lookupName_cons_ne (k := "%mul210") (n := "%p") _ _ (by decide)]

theorem expIfThenEnv_n (env : Env) (v : BitVec 64) (b : UInt8) (n : BitVec 64) :
    lookupName (expIfThenEnv env v b) "%n" = some (.int 64 n) ↔
      lookupName env "%n" = some (.int 64 n) := by
  simp only [expIfThenEnv, lookupName_cons_ne (k := "%add215") (n := "%n") _ _ (by decide),
    lookupName_cons_ne (k := "%conv214") (n := "%n") _ _ (by decide),
    lookupName_cons_ne (k := "%27") (n := "%n") _ _ (by decide),
    lookupName_cons_ne (k := "%mul210") (n := "%n") _ _ (by decide)]

theorem expIfThen_denote {calls : Calls} {env : Env} {s : State} {v : BitVec 64}
    {b : UInt8}
    (hv : lookupName env "%exp10.0603" = some (.int 64 v))
    (h8 : lookupName env "%25" = some (.int 8 (JsonScanLane.vByte b))) :
    denoteCode calls numFastIfThen209Instrs (stateAt env s) =
      some (stateAt (expIfThenEnv env v b) s) := by
  unfold numFastIfThen209Instrs
  rw [denoteCode_mul_imm _ _ _ "%mul210" "%exp10.0603" hv _]
  rw [JsonScanLane.denoteCode_and_imm_w _ _ _ "%27" "%25" (w := 8) (by block_lk) _]
  rw [denoteCode_zext _ _ _ "%conv214" "%27" 8 64 (by block_lk) _]
  rw [denoteCode_add_reg _ _ _ "%add215" "%mul210" "%conv214" (by block_lk) (by block_lk) _]
  simp only [denoteCode, denoteRun, State.bindAll, stateAt, expIfThenEnv]
  rfl

theorem expIfThen_step {env : Env} {s : State} {v : BitVec 64} {b : UInt8}
    (hpc : s.pc = "if.then209")
    (hv : lookupName env "%exp10.0603" = some (.int 64 v))
    (h8 : lookupName env "%25" = some (.int 8 (JsonScanLane.vByte b))) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (expIfThenEnv env v b)
        { s with pc := "if.end216", pre := some "if.then209" }) := by
  refine numFast_step_at (s' := stateAt (expIfThenEnv env v b) s)
    (b := ⟨"if.then209", numFastIfThen209Instrs, Term.br "if.end216"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc, numFastIfThen209Instrs]
      using numFast_findBlock_if_then209
  · simpa only [denoteCode_nil] using expIfThen_denote hv h8
  · simp only [execTerm, stateAt, hpc]

def expIfEndEnv (env : Env) (v i n : BitVec 64) : Env :=
  ("%exitcond703.not", .int 1 (evalICmp .eq (i + 1#64) n)) ::
  ("%inc217", .int 64 (i + 1#64)) ::
  ("%exp10.1", .int 64 v) :: env

theorem expIfEndEnv_p (env : Env) (v i n : BitVec 64) (a : Nat) :
    lookupName (expIfEndEnv env v i n) "%p" = some (.ptr a) ↔
      lookupName env "%p" = some (.ptr a) := by
  simp only [expIfEndEnv,
    lookupName_cons_ne (k := "%exitcond703.not") (n := "%p") _ _ (by decide),
    lookupName_cons_ne (k := "%inc217") (n := "%p") _ _ (by decide),
    lookupName_cons_ne (k := "%exp10.1") (n := "%p") _ _ (by decide)]

theorem expIfEndEnv_n (env : Env) (v i n : BitVec 64) (m : BitVec 64) :
    lookupName (expIfEndEnv env v i n) "%n" = some (.int 64 m) ↔
      lookupName env "%n" = some (.int 64 m) := by
  simp only [expIfEndEnv,
    lookupName_cons_ne (k := "%exitcond703.not") (n := "%n") _ _ (by decide),
    lookupName_cons_ne (k := "%inc217") (n := "%n") _ _ (by decide),
    lookupName_cons_ne (k := "%exp10.1") (n := "%n") _ _ (by decide)]

theorem expIfEnd_denote {calls : Calls} {env : Env} {s : State} {i n : BitVec 64}
    {p : String} {op : Operand} {vv : BitVec 64}
    (hpre : s.pre = some p)
    (hinc : phiIncoming p
      [("if.then209", (Operand.reg "%add215")), ("while.body206", (Operand.reg "%exp10.0603"))]
      = some op)
    (hop : evalOperand (stateAt env s) op = some (.int 64 vv))
    (hi : lookupName env "%i.12604" = some (.int 64 i))
    (hn : lookupName env "%n" = some (.int 64 n)) :
    denoteCode calls numFastIfEnd216Instrs (stateAt env s) =
      some (stateAt (expIfEndEnv env vv i n) s) := by
  unfold numFastIfEnd216Instrs
  rw [denoteCode_phi _ _ _ "%exp10.1" (Ty.int 64)
    [("if.then209", (Operand.reg "%add215")),
     ("while.body206", (Operand.reg "%exp10.0603"))]
    hpre hinc hop _ (by decide)]
  rw [denoteCode_add_imm _ _ _ "%inc217" "%i.12604" (by block_lk) _]
  rw [denoteCode_icmp_eq_reg _ _ _ "%exitcond703.not" "%inc217" "%n"
    (by block_lk) (by block_lk) _]
  simp only [denoteCode, denoteRun, State.bindAll, stateAt, expIfEndEnv]

theorem expIfEnd_step_exit {env : Env} {s : State} {i n : BitVec 64}
    {p : String} {op : Operand} {vv : BitVec 64}
    (hpc : s.pc = "if.end216")
    (hpre : s.pre = some p)
    (hinc : phiIncoming p
      [("if.then209", (Operand.reg "%add215")), ("while.body206", (Operand.reg "%exp10.0603"))]
      = some op)
    (hop : evalOperand (stateAt env s) op = some (.int 64 vv))
    (hi : lookupName env "%i.12604" = some (.int 64 i))
    (hn : lookupName env "%n" = some (.int 64 n))
    (heq : evalICmp .eq (i + 1#64) n = 1) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (expIfEndEnv env vv i n)
        { s with pc := "cleanup223.thread", pre := some "if.end216" }) := by
  refine numFast_step_at (s' := stateAt (expIfEndEnv env vv i n) s)
    (b := ⟨"if.end216", numFastIfEnd216Instrs,
      Term.condbr (.reg "%exitcond703.not") "cleanup223.thread" "land.lhs.true195"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc, numFastIfEnd216Instrs]
      using numFast_findBlock_if_end216
  · simpa only [denoteCode_nil] using expIfEnd_denote hpre hinc hop hi hn
  · have hlk : lookupName (expIfEndEnv env vv i n) "%exitcond703.not"
        = some (.int 1 (evalICmp .eq (i + 1#64) n)) := by
      simp only [expIfEndEnv, lookupName_cons_self]
    rw [numFast_execTerm_condbr_one _ "%exitcond703.not" _ _ hlk heq]
    simp only [stateAt, hpc]

theorem expIfEnd_step_loop {env : Env} {s : State} {i n : BitVec 64}
    {p : String} {op : Operand} {vv : BitVec 64}
    (hpc : s.pc = "if.end216")
    (hpre : s.pre = some p)
    (hinc : phiIncoming p
      [("if.then209", (Operand.reg "%add215")), ("while.body206", (Operand.reg "%exp10.0603"))]
      = some op)
    (hop : evalOperand (stateAt env s) op = some (.int 64 vv))
    (hi : lookupName env "%i.12604" = some (.int 64 i))
    (hn : lookupName env "%n" = some (.int 64 n))
    (heq : evalICmp .eq (i + 1#64) n = 0) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (expIfEndEnv env vv i n)
        { s with pc := "land.lhs.true195", pre := some "if.end216" }) := by
  refine numFast_step_at (s' := stateAt (expIfEndEnv env vv i n) s)
    (b := ⟨"if.end216", numFastIfEnd216Instrs,
      Term.condbr (.reg "%exitcond703.not") "cleanup223.thread" "land.lhs.true195"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc, numFastIfEnd216Instrs]
      using numFast_findBlock_if_end216
  · simpa only [denoteCode_nil] using expIfEnd_denote hpre hinc hop hi hn
  · have hlk : lookupName (expIfEndEnv env vv i n) "%exitcond703.not"
        = some (.int 1 (evalICmp .eq (i + 1#64) n)) := by
      simp only [expIfEndEnv, lookupName_cons_self]
    rw [numFast_execTerm_condbr_zero _ "%exitcond703.not" _ _ hlk heq]
    simp only [stateAt, hpc]

theorem expHead_step_entry_digit {env : Env} {s : State} {a j : Nat} {b : UInt8}
    (hpc : s.pc = "land.lhs.true195")
    (hpre : s.pre = some "lor.lhs.false180")
    (hp : lookupName env "%p" = some (.ptr a))
    (hhi : evalOperand (stateAt env s) (.reg "%i.11")
      = some (.int 64 (BitVec.ofNat 64 j)))
    (hj : j < 2 ^ 63) (hread : readByte s.mem (a + j) = some b)
    (hdigit : IsDigitB b = true) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (expHeadEnv env a j b 0)
        { s with pc := "while.body206", pre := some "land.lhs.true195" }) := by
  refine numFast_step_at (s' := stateAt (expHeadEnv env a j b 0) s)
    (b := ⟨"land.lhs.true195", numFastLandLhsTrue195Instrs,
      Term.condbr (.reg "%or.cond445") "while.body206" "cleanup223.thread"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc, numFastLandLhsTrue195Instrs]
      using numFast_findBlock_land_lhs_true195
  · simpa only [denoteCode_nil] using expHead_denote_entry hpre hp hhi hj hread
  · have hlk : lookupName (expHeadEnv env a j b 0) "%or.cond445"
        = some (.int 1 (BitVec.ofBool (IsDigitB b))) := by
      simp only [expHeadEnv, lookupName_cons_self]
    have hb1 : BitVec.ofBool (IsDigitB b) = (1 : BitVec 1) := by
      rw [hdigit]; rfl
    rw [numFast_execTerm_condbr_one _ "%or.cond445" _ _ hlk hb1]
    simp only [stateAt, hpc]

theorem expHead_step_entry_nondigit {env : Env} {s : State} {a j : Nat} {b : UInt8}
    (hpc : s.pc = "land.lhs.true195")
    (hpre : s.pre = some "lor.lhs.false180")
    (hp : lookupName env "%p" = some (.ptr a))
    (hhi : evalOperand (stateAt env s) (.reg "%i.11")
      = some (.int 64 (BitVec.ofNat 64 j)))
    (hj : j < 2 ^ 63) (hread : readByte s.mem (a + j) = some b)
    (hdigit : IsDigitB b = false) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (expHeadEnv env a j b 0)
        { s with pc := "cleanup223.thread", pre := some "land.lhs.true195" }) := by
  refine numFast_step_at (s' := stateAt (expHeadEnv env a j b 0) s)
    (b := ⟨"land.lhs.true195", numFastLandLhsTrue195Instrs,
      Term.condbr (.reg "%or.cond445") "while.body206" "cleanup223.thread"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc, numFastLandLhsTrue195Instrs]
      using numFast_findBlock_land_lhs_true195
  · simpa only [denoteCode_nil] using expHead_denote_entry hpre hp hhi hj hread
  · have hlk : lookupName (expHeadEnv env a j b 0) "%or.cond445"
        = some (.int 1 (BitVec.ofBool (IsDigitB b))) := by
      simp only [expHeadEnv, lookupName_cons_self]
    have hb1 : BitVec.ofBool (IsDigitB b) = (0 : BitVec 1) := by
      rw [hdigit]; rfl
    rw [numFast_execTerm_condbr_zero _ "%or.cond445" _ _ hlk hb1]
    simp only [stateAt, hpc]

theorem expHead_step_back_digit {env : Env} {s : State} {a j : Nat} {b : UInt8}
    {v : BitVec 64}
    (hpc : s.pc = "land.lhs.true195")
    (hpre : s.pre = some "if.end216")
    (hp : lookupName env "%p" = some (.ptr a))
    (hhi : evalOperand (stateAt env s) (.reg "%inc217")
      = some (.int 64 (BitVec.ofNat 64 j)))
    (hhv : evalOperand (stateAt env s) (.reg "%exp10.1") = some (.int 64 v))
    (hj : j < 2 ^ 63) (hread : readByte s.mem (a + j) = some b)
    (hdigit : IsDigitB b = true) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (expHeadEnv env a j b v)
        { s with pc := "while.body206", pre := some "land.lhs.true195" }) := by
  refine numFast_step_at (s' := stateAt (expHeadEnv env a j b v) s)
    (b := ⟨"land.lhs.true195", numFastLandLhsTrue195Instrs,
      Term.condbr (.reg "%or.cond445") "while.body206" "cleanup223.thread"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc, numFastLandLhsTrue195Instrs]
      using numFast_findBlock_land_lhs_true195
  · simpa only [denoteCode_nil] using expHead_denote_back hpre hp hhi hhv hj hread
  · have hlk : lookupName (expHeadEnv env a j b v) "%or.cond445"
        = some (.int 1 (BitVec.ofBool (IsDigitB b))) := by
      simp only [expHeadEnv, lookupName_cons_self]
    have hb1 : BitVec.ofBool (IsDigitB b) = (1 : BitVec 1) := by
      rw [hdigit]; rfl
    rw [numFast_execTerm_condbr_one _ "%or.cond445" _ _ hlk hb1]
    simp only [stateAt, hpc]

theorem expHead_step_back_nondigit {env : Env} {s : State} {a j : Nat} {b : UInt8}
    {v : BitVec 64}
    (hpc : s.pc = "land.lhs.true195")
    (hpre : s.pre = some "if.end216")
    (hp : lookupName env "%p" = some (.ptr a))
    (hhi : evalOperand (stateAt env s) (.reg "%inc217")
      = some (.int 64 (BitVec.ofNat 64 j)))
    (hhv : evalOperand (stateAt env s) (.reg "%exp10.1") = some (.int 64 v))
    (hj : j < 2 ^ 63) (hread : readByte s.mem (a + j) = some b)
    (hdigit : IsDigitB b = false) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (expHeadEnv env a j b v)
        { s with pc := "cleanup223.thread", pre := some "land.lhs.true195" }) := by
  refine numFast_step_at (s' := stateAt (expHeadEnv env a j b v) s)
    (b := ⟨"land.lhs.true195", numFastLandLhsTrue195Instrs,
      Term.condbr (.reg "%or.cond445") "while.body206" "cleanup223.thread"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc, numFastLandLhsTrue195Instrs]
      using numFast_findBlock_land_lhs_true195
  · simpa only [denoteCode_nil] using expHead_denote_back hpre hp hhi hhv hj hread
  · have hlk : lookupName (expHeadEnv env a j b v) "%or.cond445"
        = some (.int 1 (BitVec.ofBool (IsDigitB b))) := by
      simp only [expHeadEnv, lookupName_cons_self]
    have hb1 : BitVec.ofBool (IsDigitB b) = (0 : BitVec 1) := by
      rw [hdigit]; rfl
    rw [numFast_execTerm_condbr_zero _ "%or.cond445" _ _ hlk hb1]
    simp only [stateAt, hpc]

/-! #### The exponent run's invariant, arms and instance -/

/-- The four registers the exponent run carries untouched: the two digit parts'
cells and the fraction's, which `if.end230`'s `phi`s read and no block of the run
writes.  Stated as one conjunct, so a step carries the whole list rather than
four separate equations. -/
def expRunCarried (env : Env) : Prop :=
  ∃ idig5 ip5 fr5 fd5 : BitVec 64,
    lookupName env "%idig.4" = some (.int 64 idig5) ∧
    lookupName env "%ip.5" = some (.int 64 ip5) ∧
    lookupName env "%fr.5" = some (.int 64 fr5) ∧
    lookupName env "%fdig.4" = some (.int 64 fd5)

/-- The exponent run's exit: both branches land in `cleanup223.thread`, and the
register carrying the accumulator is the head's `%exp10.0603` on the entry edge
and the `if.end216` phi `%exp10.1` on the back edge.  Each disjunct names its
edge's predecessor, because the merge block `cleanup223.thread` the exit leaves
for is decided by that predecessor; `%esign.0` is the sign the same block's
select reads, and the four carried cells are what `if.end230`'s `phi`s read —
none of them is written by any block of the run, so the exit hands them on. -/
def expRunExit (st : State) : Prop :=
  st.pc = "cleanup223.thread" ∧
  ((st.pre = some "land.lhs.true195" ∧
      ∃ i1 v, lookupName st.env "%i.12604"
        = some (.int 64 (BitVec.ofNat 64 i1)) ∧
        lookupName st.env "%exp10.0603" = some (.int 64 v))
   ∨ (st.pre = some "if.end216" ∧
      ∃ i1 v, lookupName st.env "%inc217"
        = some (.int 64 (BitVec.ofNat 64 i1)) ∧
        lookupName st.env "%exp10.1" = some (.int 64 v))) ∧
  (∃ esign : BitVec 1, lookupName st.env "%esign.0" = some (.int 1 esign)) ∧
  expRunCarried st.env

def expRunAtBound (mem0 : Mem) (p n i0 : Nat) (s : State) (c : Nat) : Bool :=
  decide (n - i0 ≤ c + 1) || !numFastDigitAt mem0 p (i0 + c)

def expRunInv (mem0 : Mem) (p n i0 : Nat) (bs : List UInt8) (r : Nat)
    (s : State) (c : Nat) : Prop :=
  s.pc = "land.lhs.true195" ∧ s.mem = mem0 ∧ c + r = n - i0 ∧ i0 + c < n ∧
  n < 2 ^ 63 ∧
  lookupName s.env "%p" = some (.ptr p) ∧
  lookupName s.env "%n" = some (.int 64 (BitVec.ofNat 64 n)) ∧
  readBytes mem0 p n = some bs ∧
  ((s.pre = some "lor.lhs.false180" ∧
      lookupName s.env "%i.11" = some (.int 64 (BitVec.ofNat 64 (i0 + c))))
   ∨ (s.pre = some "if.end216" ∧
      lookupName s.env "%inc217" = some (.int 64 (BitVec.ofNat 64 (i0 + c))) ∧
      ∃ v : BitVec 64, lookupName s.env "%exp10.1" = some (.int 64 v))) ∧
  (∃ esign : BitVec 1, lookupName s.env "%esign.0" = some (.int 1 esign)) ∧
  expRunCarried s.env

theorem expRun_bound_nondigit {mem0 : Mem} {p n i0 : Nat} {bs : List UInt8}
    {s : State} {c : Nat} (hread : readBytes mem0 p n = some bs)
    (hltn : i0 + c < n) (hb : expRunAtBound mem0 p n i0 s c = true)
    (hno : ¬ n - i0 ≤ c + 1) :
    ∃ b, readByte mem0 (p + (i0 + c)) = some b ∧ IsDigitB b = false := by
  unfold expRunAtBound at hb
  rcases Bool.or_eq_true_iff.mp hb with hle | hdig
  · exact absurd (of_decide_eq_true hle) hno
  · obtain ⟨b, hb'⟩ := readByte_of_readBytes_lt hread hltn
    have hfalse : numFastDigitAt mem0 p (i0 + c) = false := by simpa using hdig
    refine ⟨b, hb', ?_⟩
    unfold numFastDigitAt at hfalse
    rw [hb'] at hfalse
    simpa using hfalse

/-- **The exponent run's back edge.** -/
theorem expRun_step_loop {mem0 : Mem} {p n i0 r : Nat} {bs : List UInt8}
    {s : State} {c : Nat}
    (hinv : expRunInv mem0 p n i0 bs (r + 1) s c)
    (hb : expRunAtBound mem0 p n i0 s c = false) :
    ∃ (e : State) (c' : Nat) (j : Nat), j ≤ 4 ∧ e.pc = "land.lhs.true195" ∧ c < c' ∧
      expRunInv mem0 p n i0 bs r e c' ∧
      ∀ k, runFuel calls (j + k) numFastBody s =
        runFuel calls k numFastBody e := by
  obtain ⟨hpc, hmem, hsum, hltn, hnlt, hp, hn, hread, hpre, hesign, hcarry⟩ := hinv
  unfold expRunAtBound at hb
  obtain ⟨hnoD, hdig⟩ := Bool.or_eq_false_iff.mp hb
  have hno : ¬ (n - i0 ≤ c + 1) := of_decide_eq_false hnoD
  have hdigitAt : numFastDigitAt mem0 p (i0 + c) = true := by simpa using hdig
  obtain ⟨b, hbyte⟩ := readByte_of_readBytes_lt hread hltn
  have hbyte_s : readByte s.mem (p + (i0 + c)) = some b := by rw [hmem]; exact hbyte
  have hdigitB : IsDigitB b = true := by
    unfold numFastDigitAt at hdigitAt
    rw [hbyte] at hdigitAt
    simpa using hdigitAt
  have hj : i0 + c < 2 ^ 63 := by omega
  have hnext : i0 + c + 1 < n := by omega
  have hnext64 : i0 + c + 1 < 2 ^ 64 := by omega
  have hneqN : BitVec.ofNat 64 (i0 + c + 1) ≠ BitVec.ofNat 64 n := by
    intro h
    have h2 := congrArg BitVec.toNat h
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt hnext64, Nat.mod_eq_of_lt (by omega)] at h2
    omega
  have hbits : evalICmp .eq (BitVec.ofNat 64 (i0 + c) + (1#64))
      (BitVec.ofNat 64 n) = 0 := by
    rw [ofNat64_add_one hnext64]
    exact evalICmp_eq_ne hneqN
  rcases hpre with hent | hback
  · obtain ⟨hpre0, hi⟩ := hent
    let e0 : State := stateAt (expHeadEnv s.env p (i0 + c) b 0)
      { s with pc := "while.body206", pre := some "land.lhs.true195" }
    have hstep1 : step calls numFastBody s = .jump e0 :=
      expHead_step_entry_digit (env := s.env) (s := s) (a := p) (j := i0 + c)
        (b := b) hpc hpre0 hp
        (BlockEval.evalOperand_reg_of s.env s "%i.11" _ hi) hj hbyte_s hdigitB
    have hexp0 : lookupName e0.env "%exp10.0603" = some (.int 64 0) := by
      simp only [e0, stateAt, expHeadEnv, expHeadPhiEnv]
      block_lk
    by_cases hguard : evalICmp .slt (0 : BitVec 64) (100000#64) = 1
    · let e1 : State := stateAt (expBodyEnv e0.env 0)
          { e0 with pc := "if.then209", pre := some "while.body206" }
      have hstep2 : step calls numFastBody e0 = .jump e1 :=
        expBody_step_taken (env := e0.env) (s := e0) (v := 0)
          (by simp only [e0, stateAt]) hexp0 hguard
      have hexp1 : lookupName e1.env "%exp10.0603" = some (.int 64 0) := by
        simp only [e1, e0, stateAt, expBodyEnv, expHeadEnv, expHeadPhiEnv]
        block_lk
      have h8 : lookupName e1.env "%25" = some (.int 8 (JsonScanLane.vByte b)) := by
        simp only [e1, e0, stateAt, expBodyEnv, expHeadEnv, expHeadPhiEnv]
        block_lk
      let e2 : State := stateAt (expIfThenEnv e1.env 0 b)
          { e1 with pc := "if.end216", pre := some "if.then209" }
      have hstep3 : step calls numFastBody e1 = .jump e2 :=
        expIfThen_step (env := e1.env) (s := e1) (by simp only [e1, stateAt])
          hexp1 h8
      have hphi : phiIncoming "if.then209"
          [("if.then209", (Operand.reg "%add215")),
           ("while.body206", (Operand.reg "%exp10.0603"))] = some (Operand.reg "%add215") := by
        simp only [phiIncoming]; rfl
      have hphiOp : evalOperand (stateAt e2.env e2) (Operand.reg "%add215")
          = some (.int 64
            (0 * 10 + BitVec.ofNat 64
              (JsonScanLane.vByte b &&& 0x0f#8).toNat)) := by
        refine BlockEval.evalOperand_reg_of e2.env e2 "%add215" _ ?_
        simp only [e2, e1, stateAt, expIfThenEnv, lookupName_cons_self]
      have hi2 : lookupName e2.env "%i.12604"
          = some (.int 64 (BitVec.ofNat 64 (i0 + c))) := by
        simp only [e2, e1, e0, stateAt, expIfThenEnv, expBodyEnv, expHeadEnv,
          expHeadPhiEnv]
        block_lk
      have hn2 : lookupName e2.env "%n" = some (.int 64 (BitVec.ofNat 64 n)) := by
        simp only [e2, e1, e0, stateAt, expIfThenEnv, expBodyEnv, expHeadEnv,
          expHeadPhiEnv]
        block_lk
      let e3 : State := stateAt
          (expIfEndEnv e2.env
            (0 * 10 + BitVec.ofNat 64 (JsonScanLane.vByte b &&& 0x0f#8).toNat)
            (BitVec.ofNat 64 (i0 + c)) (BitVec.ofNat 64 n))
          { e2 with pc := "land.lhs.true195", pre := some "if.end216" }
      have hstep4 : step calls numFastBody e2 = .jump e3 :=
        expIfEnd_step_loop (env := e2.env) (s := e2)
          (i := BitVec.ofNat 64 (i0 + c)) (n := BitVec.ofNat 64 n)
          (p := "if.then209") (op := Operand.reg "%add215")
          (vv := 0 * 10 + BitVec.ofNat 64
            (JsonScanLane.vByte b &&& 0x0f#8).toNat)
          (by simp only [e2, stateAt]) (by simp only [e2, stateAt]) hphi hphiOp
          hi2 hn2 hbits
      refine ⟨e3, c + 1, 4, by omega, ?_, by omega, ?_, ?_⟩
      · simp only [e3, stateAt]
      · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · simp only [e3, stateAt]
        · simp only [e3, stateAt]; exact hmem
        · omega
        · omega
        · exact hnlt
        · simp only [e3, e2, e1, e0, stateAt, expIfEndEnv, expIfThenEnv,
            expBodyEnv, expHeadEnv, expHeadPhiEnv]
          block_lk
        · simp only [e3, e2, e1, e0, stateAt, expIfEndEnv, expIfThenEnv,
            expBodyEnv, expHeadEnv, expHeadPhiEnv]
          block_lk
        · simpa only [e3, stateAt] using hread
        · right
          refine ⟨by simp only [e3, stateAt], ?_, ?_⟩
          · simp only [e3, e2, e1, e0, stateAt, expIfEndEnv, expIfThenEnv,
              expBodyEnv, expHeadEnv, expHeadPhiEnv]
            block_lk
            exact int_succ_eq _ hnext64
          · exact ⟨0 * 10 + BitVec.ofNat 64
              (JsonScanLane.vByte b &&& 0x0f#8).toNat,
              by simp only [e3, stateAt, expIfEndEnv]; block_lk⟩
        · obtain ⟨esg, hesg⟩ := hesign
          exact ⟨esg, by
            simp only [e3, e2, e1, e0, stateAt, expIfEndEnv, expIfThenEnv,
              expBodyEnv, expHeadEnv, expHeadPhiEnv]
            block_lk⟩
        · obtain ⟨idig5, ip5, fr5, fd5, h1, h2, h3, h4⟩ := hcarry
          refine ⟨idig5, ip5, fr5, fd5, ?_, ?_, ?_, ?_⟩
          all_goals
            simp only [e3, e2, e1, e0, stateAt, expIfEndEnv, expIfThenEnv,
              expBodyEnv, expHeadEnv, expHeadPhiEnv]
            block_lk
      · intro k
        rw [show 4 + k = 1 + (1 + (1 + (1 + k))) from by omega,
          runFuel_jump_prefix hstep1 (1 + (1 + (1 + k))),
          runFuel_jump_prefix hstep2 (1 + (1 + k)),
          runFuel_jump_prefix hstep3 (1 + k),
          runFuel_jump_prefix hstep4 k]
    · have hguard' : evalICmp .slt (0 : BitVec 64) (100000#64) = 0 := by
        unfold evalICmp at hguard ⊢
        cases hs : BitVec.slt (0 : BitVec 64) (100000#64)
        · rfl
        · rw [hs] at hguard
          exact absurd rfl hguard
      let e1 : State := stateAt (expBodyEnv e0.env 0)
          { e0 with pc := "if.end216", pre := some "while.body206" }
      have hstep2 : step calls numFastBody e0 = .jump e1 :=
        expBody_step_skip (env := e0.env) (s := e0) (v := 0)
          (by simp only [e0, stateAt]) hexp0 hguard'
      have hphi : phiIncoming "while.body206"
          [("if.then209", (Operand.reg "%add215")),
           ("while.body206", (Operand.reg "%exp10.0603"))]
          = some (Operand.reg "%exp10.0603") := by
        simp only [phiIncoming]; rfl
      have hexp1 : lookupName e1.env "%exp10.0603" = some (.int 64 0) := by
        simp only [e1, e0, stateAt, expBodyEnv, expHeadEnv, expHeadPhiEnv]
        block_lk
      have hphiOp : evalOperand (stateAt e1.env e1) (Operand.reg "%exp10.0603")
          = some (.int 64 0) :=
        BlockEval.evalOperand_reg_of e1.env e1 "%exp10.0603" _ hexp1
      have hi1 : lookupName e1.env "%i.12604"
          = some (.int 64 (BitVec.ofNat 64 (i0 + c))) := by
        simp only [e1, e0, stateAt, expBodyEnv, expHeadEnv, expHeadPhiEnv]
        block_lk
      have hn1 : lookupName e1.env "%n" = some (.int 64 (BitVec.ofNat 64 n)) := by
        simp only [e1, e0, stateAt, expBodyEnv, expHeadEnv, expHeadPhiEnv]
        block_lk
      let e2 : State := stateAt
          (expIfEndEnv e1.env 0 (BitVec.ofNat 64 (i0 + c)) (BitVec.ofNat 64 n))
          { e1 with pc := "land.lhs.true195", pre := some "if.end216" }
      have hstep3 : step calls numFastBody e1 = .jump e2 :=
        expIfEnd_step_loop (env := e1.env) (s := e1)
          (i := BitVec.ofNat 64 (i0 + c)) (n := BitVec.ofNat 64 n)
          (p := "while.body206") (op := Operand.reg "%exp10.0603") (vv := 0)
          (by simp only [e1, stateAt]) (by simp only [e1, stateAt]) hphi hphiOp
          hi1 hn1 hbits
      refine ⟨e2, c + 1, 3, by omega, ?_, by omega, ?_, ?_⟩
      · simp only [e2, stateAt]
      · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · simp only [e2, stateAt]
        · simp only [e2, stateAt]; exact hmem
        · omega
        · omega
        · exact hnlt
        · simp only [e2, e1, e0, stateAt, expIfEndEnv, expBodyEnv, expHeadEnv,
            expHeadPhiEnv]
          block_lk
        · simp only [e2, e1, e0, stateAt, expIfEndEnv, expBodyEnv, expHeadEnv,
            expHeadPhiEnv]
          block_lk
        · simpa only [e2, stateAt] using hread
        · right
          refine ⟨by simp only [e2, stateAt], ?_, ?_⟩
          · simp only [e2, e1, e0, stateAt, expIfEndEnv, expBodyEnv, expHeadEnv,
              expHeadPhiEnv]
            block_lk
            exact int_succ_eq _ hnext64
          · exact ⟨0, by simp only [e2, stateAt, expIfEndEnv]; block_lk⟩
        · obtain ⟨esg, hesg⟩ := hesign
          exact ⟨esg, by
            simp only [e2, e1, e0, stateAt, expIfEndEnv, expBodyEnv, expHeadEnv,
              expHeadPhiEnv]
            block_lk⟩
        · obtain ⟨idig5, ip5, fr5, fd5, h1, h2, h3, h4⟩ := hcarry
          refine ⟨idig5, ip5, fr5, fd5, ?_, ?_, ?_, ?_⟩
          all_goals
            simp only [e2, e1, e0, stateAt, expIfEndEnv, expBodyEnv, expHeadEnv,
              expHeadPhiEnv]
            block_lk
      · intro k
        rw [show 3 + k = 1 + (1 + (1 + k)) from by omega,
          runFuel_jump_prefix hstep1 (1 + (1 + k)),
          runFuel_jump_prefix hstep2 (1 + k),
          runFuel_jump_prefix hstep3 k]
  · obtain ⟨hpre0, hi, v, hvv⟩ := hback
    let e0 : State := stateAt (expHeadEnv s.env p (i0 + c) b v)
      { s with pc := "while.body206", pre := some "land.lhs.true195" }
    have hstep1 : step calls numFastBody s = .jump e0 :=
      expHead_step_back_digit (env := s.env) (s := s) (a := p) (j := i0 + c)
        (b := b) (v := v) hpc hpre0 hp
        (BlockEval.evalOperand_reg_of s.env s "%inc217" _ hi)
        (BlockEval.evalOperand_reg_of s.env s "%exp10.1" _ hvv) hj hbyte_s hdigitB
    have hexp0 : lookupName e0.env "%exp10.0603" = some (.int 64 v) := by
      simp only [e0, stateAt, expHeadEnv, expHeadPhiEnv]
      block_lk
    by_cases hguard : evalICmp .slt v (100000#64) = 1
    · let e1 : State := stateAt (expBodyEnv e0.env v)
          { e0 with pc := "if.then209", pre := some "while.body206" }
      have hstep2 : step calls numFastBody e0 = .jump e1 :=
        expBody_step_taken (env := e0.env) (s := e0) (v := v)
          (by simp only [e0, stateAt]) hexp0 hguard
      have hexp1 : lookupName e1.env "%exp10.0603" = some (.int 64 v) := by
        simp only [e1, e0, stateAt, expBodyEnv, expHeadEnv, expHeadPhiEnv]
        block_lk
      have h8 : lookupName e1.env "%25" = some (.int 8 (JsonScanLane.vByte b)) := by
        simp only [e1, e0, stateAt, expBodyEnv, expHeadEnv, expHeadPhiEnv]
        block_lk
      let e2 : State := stateAt (expIfThenEnv e1.env v b)
          { e1 with pc := "if.end216", pre := some "if.then209" }
      have hstep3 : step calls numFastBody e1 = .jump e2 :=
        expIfThen_step (env := e1.env) (s := e1) (by simp only [e1, stateAt])
          hexp1 h8
      have hphi : phiIncoming "if.then209"
          [("if.then209", (Operand.reg "%add215")),
           ("while.body206", (Operand.reg "%exp10.0603"))] = some (Operand.reg "%add215") := by
        simp only [phiIncoming]; rfl
      have hphiOp : evalOperand (stateAt e2.env e2) (Operand.reg "%add215")
          = some (.int 64
            (v * 10 + BitVec.ofNat 64
              (JsonScanLane.vByte b &&& 0x0f#8).toNat)) := by
        refine BlockEval.evalOperand_reg_of e2.env e2 "%add215" _ ?_
        simp only [e2, e1, stateAt, expIfThenEnv, lookupName_cons_self]
      have hi2 : lookupName e2.env "%i.12604"
          = some (.int 64 (BitVec.ofNat 64 (i0 + c))) := by
        simp only [e2, e1, e0, stateAt, expIfThenEnv, expBodyEnv, expHeadEnv,
          expHeadPhiEnv]
        block_lk
      have hn2 : lookupName e2.env "%n" = some (.int 64 (BitVec.ofNat 64 n)) := by
        simp only [e2, e1, e0, stateAt, expIfThenEnv, expBodyEnv, expHeadEnv,
          expHeadPhiEnv]
        block_lk
      let e3 : State := stateAt
          (expIfEndEnv e2.env
            (v * 10 + BitVec.ofNat 64 (JsonScanLane.vByte b &&& 0x0f#8).toNat)
            (BitVec.ofNat 64 (i0 + c)) (BitVec.ofNat 64 n))
          { e2 with pc := "land.lhs.true195", pre := some "if.end216" }
      have hstep4 : step calls numFastBody e2 = .jump e3 :=
        expIfEnd_step_loop (env := e2.env) (s := e2)
          (i := BitVec.ofNat 64 (i0 + c)) (n := BitVec.ofNat 64 n)
          (p := "if.then209") (op := Operand.reg "%add215")
          (vv := v * 10 + BitVec.ofNat 64
            (JsonScanLane.vByte b &&& 0x0f#8).toNat)
          (by simp only [e2, stateAt]) (by simp only [e2, stateAt]) hphi hphiOp
          hi2 hn2 hbits
      refine ⟨e3, c + 1, 4, by omega, ?_, by omega, ?_, ?_⟩
      · simp only [e3, stateAt]
      · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · simp only [e3, stateAt]
        · simp only [e3, stateAt]; exact hmem
        · omega
        · omega
        · exact hnlt
        · simp only [e3, e2, e1, e0, stateAt, expIfEndEnv, expIfThenEnv,
            expBodyEnv, expHeadEnv, expHeadPhiEnv]
          block_lk
        · simp only [e3, e2, e1, e0, stateAt, expIfEndEnv, expIfThenEnv,
            expBodyEnv, expHeadEnv, expHeadPhiEnv]
          block_lk
        · simpa only [e3, stateAt] using hread
        · right
          refine ⟨by simp only [e3, stateAt], ?_, ?_⟩
          · simp only [e3, e2, e1, e0, stateAt, expIfEndEnv, expIfThenEnv,
              expBodyEnv, expHeadEnv, expHeadPhiEnv]
            block_lk
            exact int_succ_eq _ hnext64
          · exact ⟨v * 10 + BitVec.ofNat 64
              (JsonScanLane.vByte b &&& 0x0f#8).toNat,
              by simp only [e3, stateAt, expIfEndEnv]; block_lk⟩
        · obtain ⟨esg, hesg⟩ := hesign
          exact ⟨esg, by
            simp only [e3, e2, e1, e0, stateAt, expIfEndEnv, expIfThenEnv,
              expBodyEnv, expHeadEnv, expHeadPhiEnv]
            block_lk⟩
        · obtain ⟨idig5, ip5, fr5, fd5, h1, h2, h3, h4⟩ := hcarry
          refine ⟨idig5, ip5, fr5, fd5, ?_, ?_, ?_, ?_⟩
          all_goals
            simp only [e3, e2, e1, e0, stateAt, expIfEndEnv, expIfThenEnv,
              expBodyEnv, expHeadEnv, expHeadPhiEnv]
            block_lk
      · intro k
        rw [show 4 + k = 1 + (1 + (1 + (1 + k))) from by omega,
          runFuel_jump_prefix hstep1 (1 + (1 + (1 + k))),
          runFuel_jump_prefix hstep2 (1 + (1 + k)),
          runFuel_jump_prefix hstep3 (1 + k),
          runFuel_jump_prefix hstep4 k]
    · have hguard' : evalICmp .slt v (100000#64) = 0 := by
        unfold evalICmp at hguard ⊢
        cases hs : BitVec.slt v (100000#64)
        · rfl
        · rw [hs] at hguard
          exact absurd rfl hguard
      let e1 : State := stateAt (expBodyEnv e0.env v)
          { e0 with pc := "if.end216", pre := some "while.body206" }
      have hstep2 : step calls numFastBody e0 = .jump e1 :=
        expBody_step_skip (env := e0.env) (s := e0) (v := v)
          (by simp only [e0, stateAt]) hexp0 hguard'
      have hphi : phiIncoming "while.body206"
          [("if.then209", (Operand.reg "%add215")),
           ("while.body206", (Operand.reg "%exp10.0603"))]
          = some (Operand.reg "%exp10.0603") := by
        simp only [phiIncoming]; rfl
      have hexp1 : lookupName e1.env "%exp10.0603" = some (.int 64 v) := by
        simp only [e1, e0, stateAt, expBodyEnv, expHeadEnv, expHeadPhiEnv]
        block_lk
      have hphiOp : evalOperand (stateAt e1.env e1) (Operand.reg "%exp10.0603")
          = some (.int 64 v) :=
        BlockEval.evalOperand_reg_of e1.env e1 "%exp10.0603" _ hexp1
      have hi1 : lookupName e1.env "%i.12604"
          = some (.int 64 (BitVec.ofNat 64 (i0 + c))) := by
        simp only [e1, e0, stateAt, expBodyEnv, expHeadEnv, expHeadPhiEnv]
        block_lk
      have hn1 : lookupName e1.env "%n" = some (.int 64 (BitVec.ofNat 64 n)) := by
        simp only [e1, e0, stateAt, expBodyEnv, expHeadEnv, expHeadPhiEnv]
        block_lk
      let e2 : State := stateAt
          (expIfEndEnv e1.env v (BitVec.ofNat 64 (i0 + c)) (BitVec.ofNat 64 n))
          { e1 with pc := "land.lhs.true195", pre := some "if.end216" }
      have hstep3 : step calls numFastBody e1 = .jump e2 :=
        expIfEnd_step_loop (env := e1.env) (s := e1)
          (i := BitVec.ofNat 64 (i0 + c)) (n := BitVec.ofNat 64 n)
          (p := "while.body206") (op := Operand.reg "%exp10.0603") (vv := v)
          (by simp only [e1, stateAt]) (by simp only [e1, stateAt]) hphi hphiOp
          hi1 hn1 hbits
      refine ⟨e2, c + 1, 3, by omega, ?_, by omega, ?_, ?_⟩
      · simp only [e2, stateAt]
      · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · simp only [e2, stateAt]
        · simp only [e2, stateAt]; exact hmem
        · omega
        · omega
        · exact hnlt
        · simp only [e2, e1, e0, stateAt, expIfEndEnv, expBodyEnv, expHeadEnv,
            expHeadPhiEnv]
          block_lk
        · simp only [e2, e1, e0, stateAt, expIfEndEnv, expBodyEnv, expHeadEnv,
            expHeadPhiEnv]
          block_lk
        · simpa only [e2, stateAt] using hread
        · right
          refine ⟨by simp only [e2, stateAt], ?_, ?_⟩
          · simp only [e2, e1, e0, stateAt, expIfEndEnv, expBodyEnv, expHeadEnv,
              expHeadPhiEnv]
            block_lk
            exact int_succ_eq _ hnext64
          · exact ⟨v, by simp only [e2, stateAt, expIfEndEnv]; block_lk⟩
        · obtain ⟨esg, hesg⟩ := hesign
          exact ⟨esg, by
            simp only [e2, e1, e0, stateAt, expIfEndEnv, expBodyEnv, expHeadEnv,
              expHeadPhiEnv]
            block_lk⟩
        · obtain ⟨idig5, ip5, fr5, fd5, h1, h2, h3, h4⟩ := hcarry
          refine ⟨idig5, ip5, fr5, fd5, ?_, ?_, ?_, ?_⟩
          all_goals
            simp only [e2, e1, e0, stateAt, expIfEndEnv, expBodyEnv, expHeadEnv,
              expHeadPhiEnv]
            block_lk
      · intro k
        rw [show 3 + k = 1 + (1 + (1 + k)) from by omega,
          runFuel_jump_prefix hstep1 (1 + (1 + k)),
          runFuel_jump_prefix hstep2 (1 + k),
          runFuel_jump_prefix hstep3 k]

/-- **The exponent run's exit.** -/
theorem expRun_step_exit {mem0 : Mem} {p n i0 r : Nat} {bs : List UInt8}
    {s : State} {c : Nat}
    (hinv : expRunInv mem0 p n i0 bs r s c)
    (hb : expRunAtBound mem0 p n i0 s c = true) :
    ∃ (e : State) (j : Nat), j ≤ 4 ∧ e.pc = "cleanup223.thread" ∧ expRunExit e ∧
      ∀ k, runFuel calls (j + k) numFastBody s =
        runFuel calls k numFastBody e := by
  obtain ⟨hpc, hmem, hsum, hltn, hnlt, hp, hn, hread, hpre, hesign, hcarry⟩ := hinv
  obtain ⟨b, hbyte⟩ := readByte_of_readBytes_lt hread hltn
  have hbyte_s : readByte s.mem (p + (i0 + c)) = some b := by rw [hmem]; exact hbyte
  have hj : i0 + c < 2 ^ 63 := by omega
  by_cases hle : n - i0 ≤ c + 1
  · have hnext64 : i0 + c + 1 < 2 ^ 64 := by omega
    have h_eq : i0 + c + 1 = n := by omega
    have hbits : evalICmp .eq (BitVec.ofNat 64 (i0 + c) + (1#64))
        (BitVec.ofNat 64 n) = 1 := by
      rw [ofNat64_add_one hnext64, show i0 + c + 1 = n from h_eq]
      exact evalICmp_eq_refl _
    by_cases hdigit : IsDigitB b = true
    · rcases hpre with hent | hback
      · obtain ⟨hpre0, hi⟩ := hent
        let e0 : State := stateAt (expHeadEnv s.env p (i0 + c) b 0)
          { s with pc := "while.body206", pre := some "land.lhs.true195" }
        have hstep1 : step calls numFastBody s = .jump e0 :=
          expHead_step_entry_digit (env := s.env) (s := s) (a := p) (j := i0 + c)
            (b := b) hpc hpre0 hp
            (BlockEval.evalOperand_reg_of s.env s "%i.11" _ hi) hj hbyte_s hdigit
        have hexp0 : lookupName e0.env "%exp10.0603" = some (.int 64 0) := by
          simp only [e0, stateAt, expHeadEnv, expHeadPhiEnv]
          block_lk
        by_cases hguard : evalICmp .slt (0 : BitVec 64) (100000#64) = 1
        · let e1 : State := stateAt (expBodyEnv e0.env 0)
              { e0 with pc := "if.then209", pre := some "while.body206" }
          have hstep2 : step calls numFastBody e0 = .jump e1 :=
            expBody_step_taken (env := e0.env) (s := e0) (v := 0)
              (by simp only [e0, stateAt]) hexp0 hguard
          have hexp1 : lookupName e1.env "%exp10.0603" = some (.int 64 0) := by
            simp only [e1, e0, stateAt, expBodyEnv, expHeadEnv, expHeadPhiEnv]
            block_lk
          have h8 : lookupName e1.env "%25" = some (.int 8 (JsonScanLane.vByte b)) := by
            simp only [e1, e0, stateAt, expBodyEnv, expHeadEnv, expHeadPhiEnv]
            block_lk
          let e2 : State := stateAt (expIfThenEnv e1.env 0 b)
              { e1 with pc := "if.end216", pre := some "if.then209" }
          have hstep3 : step calls numFastBody e1 = .jump e2 :=
            expIfThen_step (env := e1.env) (s := e1) (by simp only [e1, stateAt])
              hexp1 h8
          have hphi : phiIncoming "if.then209"
              [("if.then209", (Operand.reg "%add215")),
               ("while.body206", (Operand.reg "%exp10.0603"))] = some (Operand.reg "%add215") := by
            simp only [phiIncoming]; rfl
          have hphiOp : evalOperand (stateAt e2.env e2) (Operand.reg "%add215")
              = some (.int 64
                (0 * 10 + BitVec.ofNat 64
                  (JsonScanLane.vByte b &&& 0x0f#8).toNat)) := by
            refine BlockEval.evalOperand_reg_of e2.env e2 "%add215" _ ?_
            simp only [e2, e1, stateAt, expIfThenEnv, lookupName_cons_self]
          have hi2 : lookupName e2.env "%i.12604"
              = some (.int 64 (BitVec.ofNat 64 (i0 + c))) := by
            simp only [e2, e1, e0, stateAt, expIfThenEnv, expBodyEnv, expHeadEnv,
              expHeadPhiEnv]
            block_lk
          have hn2 : lookupName e2.env "%n"
              = some (.int 64 (BitVec.ofNat 64 n)) := by
            simp only [e2, e1, e0, stateAt, expIfThenEnv, expBodyEnv, expHeadEnv,
              expHeadPhiEnv]
            block_lk
          let e3 : State := stateAt
              (expIfEndEnv e2.env
                (0 * 10 + BitVec.ofNat 64 (JsonScanLane.vByte b &&& 0x0f#8).toNat)
                (BitVec.ofNat 64 (i0 + c)) (BitVec.ofNat 64 n))
              { e2 with pc := "cleanup223.thread", pre := some "if.end216" }
          have hstep4 : step calls numFastBody e2 = .jump e3 :=
            expIfEnd_step_exit (env := e2.env) (s := e2)
              (i := BitVec.ofNat 64 (i0 + c)) (n := BitVec.ofNat 64 n)
              (p := "if.then209") (op := Operand.reg "%add215")
              (vv := 0 * 10 + BitVec.ofNat 64
                (JsonScanLane.vByte b &&& 0x0f#8).toNat)
              (by simp only [e2, stateAt]) (by simp only [e2, stateAt]) hphi hphiOp
              hi2 hn2 hbits
          refine ⟨e3, 4, by omega, by simp only [e3, stateAt], ?_, ?_⟩
          · refine ⟨by simp only [e3, stateAt],
              Or.inr ⟨by simp only [e3, stateAt], i0 + c + 1,
                (0 * 10 + BitVec.ofNat 64 (JsonScanLane.vByte b &&& 0x0f#8).toNat),
                ?_, ?_⟩, ?_, ?_⟩
            · simp only [e3, stateAt, expIfEndEnv]
              block_lk
              exact int_succ_eq _ hnext64
            · simp only [e3, stateAt, expIfEndEnv]; block_lk
            · obtain ⟨esg, hesg⟩ := hesign
              exact ⟨esg, by
                simp only [e3, e2, e1, e0, stateAt, expIfEndEnv, expIfThenEnv,
                  expBodyEnv, expHeadEnv, expHeadPhiEnv]
                block_lk⟩
            · obtain ⟨idig5, ip5, fr5, fd5, h1, h2, h3, h4⟩ := hcarry
              refine ⟨idig5, ip5, fr5, fd5, ?_, ?_, ?_, ?_⟩
              all_goals
                simp only [e3, e2, e1, e0, stateAt, expIfEndEnv, expIfThenEnv,
                  expBodyEnv, expHeadEnv, expHeadPhiEnv]
                block_lk
          · intro k
            rw [show 4 + k = 1 + (1 + (1 + (1 + k))) from by omega,
              runFuel_jump_prefix hstep1 (1 + (1 + (1 + k))),
              runFuel_jump_prefix hstep2 (1 + (1 + k)),
              runFuel_jump_prefix hstep3 (1 + k),
              runFuel_jump_prefix hstep4 k]
        · have hguard' : evalICmp .slt (0 : BitVec 64) (100000#64) = 0 := by
            unfold evalICmp at hguard ⊢
            cases hs : BitVec.slt (0 : BitVec 64) (100000#64)
            · rfl
            · rw [hs] at hguard
              exact absurd rfl hguard
          let e1 : State := stateAt (expBodyEnv e0.env 0)
              { e0 with pc := "if.end216", pre := some "while.body206" }
          have hstep2 : step calls numFastBody e0 = .jump e1 :=
            expBody_step_skip (env := e0.env) (s := e0) (v := 0)
              (by simp only [e0, stateAt]) hexp0 hguard'
          have hphi : phiIncoming "while.body206"
              [("if.then209", (Operand.reg "%add215")),
               ("while.body206", (Operand.reg "%exp10.0603"))]
              = some (Operand.reg "%exp10.0603") := by
            simp only [phiIncoming]; rfl
          have hexp1 : lookupName e1.env "%exp10.0603" = some (.int 64 0) := by
            simp only [e1, e0, stateAt, expBodyEnv, expHeadEnv, expHeadPhiEnv]
            block_lk
          have hphiOp : evalOperand (stateAt e1.env e1) (Operand.reg "%exp10.0603")
              = some (.int 64 0) :=
            BlockEval.evalOperand_reg_of e1.env e1 "%exp10.0603" _ hexp1
          have hi1 : lookupName e1.env "%i.12604"
              = some (.int 64 (BitVec.ofNat 64 (i0 + c))) := by
            simp only [e1, e0, stateAt, expBodyEnv, expHeadEnv, expHeadPhiEnv]
            block_lk
          have hn1 : lookupName e1.env "%n"
              = some (.int 64 (BitVec.ofNat 64 n)) := by
            simp only [e1, e0, stateAt, expBodyEnv, expHeadEnv, expHeadPhiEnv]
            block_lk
          let e2 : State := stateAt
              (expIfEndEnv e1.env 0 (BitVec.ofNat 64 (i0 + c)) (BitVec.ofNat 64 n))
              { e1 with pc := "cleanup223.thread", pre := some "if.end216" }
          have hstep3 : step calls numFastBody e1 = .jump e2 :=
            expIfEnd_step_exit (env := e1.env) (s := e1)
              (i := BitVec.ofNat 64 (i0 + c)) (n := BitVec.ofNat 64 n)
              (p := "while.body206") (op := Operand.reg "%exp10.0603") (vv := 0)
              (by simp only [e1, stateAt]) (by simp only [e1, stateAt]) hphi hphiOp
              hi1 hn1 hbits
          refine ⟨e2, 3, by omega, by simp only [e2, stateAt], ?_, ?_⟩
          · refine ⟨by simp only [e2, stateAt],
              Or.inr ⟨by simp only [e2, stateAt], i0 + c + 1, 0, ?_, ?_⟩, ?_, ?_⟩
            · simp only [e2, stateAt, expIfEndEnv]
              block_lk
              exact int_succ_eq _ hnext64
            · simp only [e2, stateAt, expIfEndEnv]; block_lk
            · obtain ⟨esg, hesg⟩ := hesign
              exact ⟨esg, by
                simp only [e2, e1, e0, stateAt, expIfEndEnv, expBodyEnv, expHeadEnv,
                  expHeadPhiEnv]
                block_lk⟩
            · obtain ⟨idig5, ip5, fr5, fd5, h1, h2, h3, h4⟩ := hcarry
              refine ⟨idig5, ip5, fr5, fd5, ?_, ?_, ?_, ?_⟩
              all_goals
                simp only [e2, e1, e0, stateAt, expIfEndEnv, expBodyEnv, expHeadEnv,
                  expHeadPhiEnv]
                block_lk
          · intro k
            rw [show 3 + k = 1 + (1 + (1 + k)) from by omega,
              runFuel_jump_prefix hstep1 (1 + (1 + k)),
              runFuel_jump_prefix hstep2 (1 + k),
              runFuel_jump_prefix hstep3 k]
      · obtain ⟨hpre0, hi, v, hvv⟩ := hback
        let e0 : State := stateAt (expHeadEnv s.env p (i0 + c) b v)
          { s with pc := "while.body206", pre := some "land.lhs.true195" }
        have hstep1 : step calls numFastBody s = .jump e0 :=
          expHead_step_back_digit (env := s.env) (s := s) (a := p) (j := i0 + c)
            (b := b) (v := v) hpc hpre0 hp
            (BlockEval.evalOperand_reg_of s.env s "%inc217" _ hi)
            (BlockEval.evalOperand_reg_of s.env s "%exp10.1" _ hvv) hj hbyte_s hdigit
        have hexp0 : lookupName e0.env "%exp10.0603" = some (.int 64 v) := by
          simp only [e0, stateAt, expHeadEnv, expHeadPhiEnv]
          block_lk
        by_cases hguard : evalICmp .slt v (100000#64) = 1
        · let e1 : State := stateAt (expBodyEnv e0.env v)
              { e0 with pc := "if.then209", pre := some "while.body206" }
          have hstep2 : step calls numFastBody e0 = .jump e1 :=
            expBody_step_taken (env := e0.env) (s := e0) (v := v)
              (by simp only [e0, stateAt]) hexp0 hguard
          have hexp1 : lookupName e1.env "%exp10.0603" = some (.int 64 v) := by
            simp only [e1, e0, stateAt, expBodyEnv, expHeadEnv, expHeadPhiEnv]
            block_lk
          have h8 : lookupName e1.env "%25" = some (.int 8 (JsonScanLane.vByte b)) := by
            simp only [e1, e0, stateAt, expBodyEnv, expHeadEnv, expHeadPhiEnv]
            block_lk
          let e2 : State := stateAt (expIfThenEnv e1.env v b)
              { e1 with pc := "if.end216", pre := some "if.then209" }
          have hstep3 : step calls numFastBody e1 = .jump e2 :=
            expIfThen_step (env := e1.env) (s := e1) (by simp only [e1, stateAt])
              hexp1 h8
          have hphi : phiIncoming "if.then209"
              [("if.then209", (Operand.reg "%add215")),
               ("while.body206", (Operand.reg "%exp10.0603"))] = some (Operand.reg "%add215") := by
            simp only [phiIncoming]; rfl
          have hphiOp : evalOperand (stateAt e2.env e2) (Operand.reg "%add215")
              = some (.int 64
                (v * 10 + BitVec.ofNat 64
                  (JsonScanLane.vByte b &&& 0x0f#8).toNat)) := by
            refine BlockEval.evalOperand_reg_of e2.env e2 "%add215" _ ?_
            simp only [e2, e1, stateAt, expIfThenEnv, lookupName_cons_self]
          have hi2 : lookupName e2.env "%i.12604"
              = some (.int 64 (BitVec.ofNat 64 (i0 + c))) := by
            simp only [e2, e1, e0, stateAt, expIfThenEnv, expBodyEnv, expHeadEnv,
              expHeadPhiEnv]
            block_lk
          have hn2 : lookupName e2.env "%n"
              = some (.int 64 (BitVec.ofNat 64 n)) := by
            simp only [e2, e1, e0, stateAt, expIfThenEnv, expBodyEnv, expHeadEnv,
              expHeadPhiEnv]
            block_lk
          let e3 : State := stateAt
              (expIfEndEnv e2.env
                (v * 10 + BitVec.ofNat 64 (JsonScanLane.vByte b &&& 0x0f#8).toNat)
                (BitVec.ofNat 64 (i0 + c)) (BitVec.ofNat 64 n))
              { e2 with pc := "cleanup223.thread", pre := some "if.end216" }
          have hstep4 : step calls numFastBody e2 = .jump e3 :=
            expIfEnd_step_exit (env := e2.env) (s := e2)
              (i := BitVec.ofNat 64 (i0 + c)) (n := BitVec.ofNat 64 n)
              (p := "if.then209") (op := Operand.reg "%add215")
              (vv := v * 10 + BitVec.ofNat 64
                (JsonScanLane.vByte b &&& 0x0f#8).toNat)
              (by simp only [e2, stateAt]) (by simp only [e2, stateAt]) hphi hphiOp
              hi2 hn2 hbits
          refine ⟨e3, 4, by omega, by simp only [e3, stateAt], ?_, ?_⟩
          · refine ⟨by simp only [e3, stateAt],
              Or.inr ⟨by simp only [e3, stateAt], i0 + c + 1,
                (v * 10 + BitVec.ofNat 64 (JsonScanLane.vByte b &&& 0x0f#8).toNat),
                ?_, ?_⟩, ?_, ?_⟩
            · simp only [e3, stateAt, expIfEndEnv]
              block_lk
              exact int_succ_eq _ hnext64
            · simp only [e3, stateAt, expIfEndEnv]; block_lk
            · obtain ⟨esg, hesg⟩ := hesign
              exact ⟨esg, by
                simp only [e3, e2, e1, e0, stateAt, expIfEndEnv, expIfThenEnv,
                  expBodyEnv, expHeadEnv, expHeadPhiEnv]
                block_lk⟩
            · obtain ⟨idig5, ip5, fr5, fd5, h1, h2, h3, h4⟩ := hcarry
              refine ⟨idig5, ip5, fr5, fd5, ?_, ?_, ?_, ?_⟩
              all_goals
                simp only [e3, e2, e1, e0, stateAt, expIfEndEnv, expIfThenEnv,
                  expBodyEnv, expHeadEnv, expHeadPhiEnv]
                block_lk
          · intro k
            rw [show 4 + k = 1 + (1 + (1 + (1 + k))) from by omega,
              runFuel_jump_prefix hstep1 (1 + (1 + (1 + k))),
              runFuel_jump_prefix hstep2 (1 + (1 + k)),
              runFuel_jump_prefix hstep3 (1 + k),
              runFuel_jump_prefix hstep4 k]
        · have hguard' : evalICmp .slt v (100000#64) = 0 := by
            unfold evalICmp at hguard ⊢
            cases hs : BitVec.slt v (100000#64)
            · rfl
            · rw [hs] at hguard
              exact absurd rfl hguard
          let e1 : State := stateAt (expBodyEnv e0.env v)
              { e0 with pc := "if.end216", pre := some "while.body206" }
          have hstep2 : step calls numFastBody e0 = .jump e1 :=
            expBody_step_skip (env := e0.env) (s := e0) (v := v)
              (by simp only [e0, stateAt]) hexp0 hguard'
          have hphi : phiIncoming "while.body206"
              [("if.then209", (Operand.reg "%add215")),
               ("while.body206", (Operand.reg "%exp10.0603"))]
              = some (Operand.reg "%exp10.0603") := by
            simp only [phiIncoming]; rfl
          have hexp1 : lookupName e1.env "%exp10.0603" = some (.int 64 v) := by
            simp only [e1, e0, stateAt, expBodyEnv, expHeadEnv, expHeadPhiEnv]
            block_lk
          have hphiOp : evalOperand (stateAt e1.env e1) (Operand.reg "%exp10.0603")
              = some (.int 64 v) :=
            BlockEval.evalOperand_reg_of e1.env e1 "%exp10.0603" _ hexp1
          have hi1 : lookupName e1.env "%i.12604"
              = some (.int 64 (BitVec.ofNat 64 (i0 + c))) := by
            simp only [e1, e0, stateAt, expBodyEnv, expHeadEnv, expHeadPhiEnv]
            block_lk
          have hn1 : lookupName e1.env "%n"
              = some (.int 64 (BitVec.ofNat 64 n)) := by
            simp only [e1, e0, stateAt, expBodyEnv, expHeadEnv, expHeadPhiEnv]
            block_lk
          let e2 : State := stateAt
              (expIfEndEnv e1.env v (BitVec.ofNat 64 (i0 + c)) (BitVec.ofNat 64 n))
              { e1 with pc := "cleanup223.thread", pre := some "if.end216" }
          have hstep3 : step calls numFastBody e1 = .jump e2 :=
            expIfEnd_step_exit (env := e1.env) (s := e1)
              (i := BitVec.ofNat 64 (i0 + c)) (n := BitVec.ofNat 64 n)
              (p := "while.body206") (op := Operand.reg "%exp10.0603") (vv := v)
              (by simp only [e1, stateAt]) (by simp only [e1, stateAt]) hphi hphiOp
              hi1 hn1 hbits
          refine ⟨e2, 3, by omega, by simp only [e2, stateAt], ?_, ?_⟩
          · refine ⟨by simp only [e2, stateAt],
              Or.inr ⟨by simp only [e2, stateAt], i0 + c + 1, v, ?_, ?_⟩, ?_, ?_⟩
            · simp only [e2, stateAt, expIfEndEnv]
              block_lk
              exact int_succ_eq _ hnext64
            · simp only [e2, stateAt, expIfEndEnv]; block_lk
            · obtain ⟨esg, hesg⟩ := hesign
              exact ⟨esg, by
                simp only [e2, e1, e0, stateAt, expIfEndEnv, expBodyEnv, expHeadEnv,
                  expHeadPhiEnv]
                block_lk⟩
            · obtain ⟨idig5, ip5, fr5, fd5, h1, h2, h3, h4⟩ := hcarry
              refine ⟨idig5, ip5, fr5, fd5, ?_, ?_, ?_, ?_⟩
              all_goals
                simp only [e2, e1, e0, stateAt, expIfEndEnv, expBodyEnv, expHeadEnv,
                  expHeadPhiEnv]
                block_lk
          · intro k
            rw [show 3 + k = 1 + (1 + (1 + k)) from by omega,
              runFuel_jump_prefix hstep1 (1 + (1 + k)),
              runFuel_jump_prefix hstep2 (1 + k),
              runFuel_jump_prefix hstep3 k]
    · have hdigit' : IsDigitB b = false := by
        cases h : IsDigitB b
        · rfl
        · exact absurd h hdigit
      rcases hpre with hent | hback
      · obtain ⟨hpre0, hi⟩ := hent
        let e0 : State := stateAt (expHeadEnv s.env p (i0 + c) b 0)
          { s with pc := "cleanup223.thread", pre := some "land.lhs.true195" }
        have hstep1 : step calls numFastBody s = .jump e0 :=
          expHead_step_entry_nondigit (env := s.env) (s := s) (a := p) (j := i0 + c)
            (b := b) hpc hpre0 hp
            (BlockEval.evalOperand_reg_of s.env s "%i.11" _ hi) hj hbyte_s hdigit'
        refine ⟨e0, 1, by omega, by simp only [e0, stateAt], ?_, ?_⟩
        · refine ⟨by simp only [e0, stateAt],
            Or.inl ⟨by simp only [e0, stateAt], i0 + c, 0, ?_, ?_⟩, ?_, ?_⟩
          · simp only [e0, stateAt, expHeadEnv, expHeadPhiEnv]
            block_lk
          · simp only [e0, stateAt, expHeadEnv, expHeadPhiEnv]
            block_lk
          · obtain ⟨esg, hesg⟩ := hesign
            exact ⟨esg, by
              simp only [e0, stateAt, expHeadEnv, expHeadPhiEnv]
              block_lk⟩
          · obtain ⟨idig5, ip5, fr5, fd5, h1, h2, h3, h4⟩ := hcarry
            refine ⟨idig5, ip5, fr5, fd5, ?_, ?_, ?_, ?_⟩
            all_goals
              simp only [e0, stateAt, expHeadEnv, expHeadPhiEnv]
              block_lk
        · intro k
          rw [runFuel_jump_prefix hstep1 k]
      · obtain ⟨hpre0, hi, v, hvv⟩ := hback
        let e0 : State := stateAt (expHeadEnv s.env p (i0 + c) b v)
          { s with pc := "cleanup223.thread", pre := some "land.lhs.true195" }
        have hstep1 : step calls numFastBody s = .jump e0 :=
          expHead_step_back_nondigit (env := s.env) (s := s) (a := p) (j := i0 + c)
            (b := b) (v := v) hpc hpre0 hp
            (BlockEval.evalOperand_reg_of s.env s "%inc217" _ hi)
            (BlockEval.evalOperand_reg_of s.env s "%exp10.1" _ hvv) hj hbyte_s hdigit'
        refine ⟨e0, 1, by omega, by simp only [e0, stateAt], ?_, ?_⟩
        · refine ⟨by simp only [e0, stateAt],
            Or.inl ⟨by simp only [e0, stateAt], i0 + c, v, ?_, ?_⟩, ?_, ?_⟩
          · simp only [e0, stateAt, expHeadEnv, expHeadPhiEnv]
            block_lk
          · simp only [e0, stateAt, expHeadEnv, expHeadPhiEnv]
            block_lk
          · obtain ⟨esg, hesg⟩ := hesign
            exact ⟨esg, by
              simp only [e0, stateAt, expHeadEnv, expHeadPhiEnv]
              block_lk⟩
          · obtain ⟨idig5, ip5, fr5, fd5, h1, h2, h3, h4⟩ := hcarry
            refine ⟨idig5, ip5, fr5, fd5, ?_, ?_, ?_, ?_⟩
            all_goals
              simp only [e0, stateAt, expHeadEnv, expHeadPhiEnv]
              block_lk
        · intro k
          rw [runFuel_jump_prefix hstep1 k]
  · obtain ⟨b', hbyte', hdigit'⟩ := expRun_bound_nondigit hread hltn hb hle
    have hbyte'_s : readByte s.mem (p + (i0 + c)) = some b' := by rw [hmem]; exact hbyte'
    have hbb : b = b' := Option.some.inj (hbyte.symm.trans hbyte')
    subst hbb
    rcases hpre with hent | hback
    · obtain ⟨hpre0, hi⟩ := hent
      let e0 : State := stateAt (expHeadEnv s.env p (i0 + c) b 0)
        { s with pc := "cleanup223.thread", pre := some "land.lhs.true195" }
      have hstep1 : step calls numFastBody s = .jump e0 :=
        expHead_step_entry_nondigit (env := s.env) (s := s) (a := p) (j := i0 + c)
          (b := b) hpc hpre0 hp
          (BlockEval.evalOperand_reg_of s.env s "%i.11" _ hi) hj hbyte'_s hdigit'
      refine ⟨e0, 1, by omega, by simp only [e0, stateAt], ?_, ?_⟩
      · refine ⟨by simp only [e0, stateAt],
          Or.inl ⟨by simp only [e0, stateAt], i0 + c, 0, ?_, ?_⟩, ?_, ?_⟩
        · simp only [e0, stateAt, expHeadEnv, expHeadPhiEnv]
          block_lk
        · simp only [e0, stateAt, expHeadEnv, expHeadPhiEnv]
          block_lk
        · obtain ⟨esg, hesg⟩ := hesign
          exact ⟨esg, by
            simp only [e0, stateAt, expHeadEnv, expHeadPhiEnv]
            block_lk⟩
        · obtain ⟨idig5, ip5, fr5, fd5, h1, h2, h3, h4⟩ := hcarry
          refine ⟨idig5, ip5, fr5, fd5, ?_, ?_, ?_, ?_⟩
          all_goals
            simp only [e0, stateAt, expHeadEnv, expHeadPhiEnv]
            block_lk
      · intro k
        rw [runFuel_jump_prefix hstep1 k]
    · obtain ⟨hpre0, hi, v, hvv⟩ := hback
      let e0 : State := stateAt (expHeadEnv s.env p (i0 + c) b v)
        { s with pc := "cleanup223.thread", pre := some "land.lhs.true195" }
      have hstep1 : step calls numFastBody s = .jump e0 :=
        expHead_step_back_nondigit (env := s.env) (s := s) (a := p) (j := i0 + c)
          (b := b) (v := v) hpc hpre0 hp
          (BlockEval.evalOperand_reg_of s.env s "%inc217" _ hi)
          (BlockEval.evalOperand_reg_of s.env s "%exp10.1" _ hvv) hj hbyte'_s hdigit'
      refine ⟨e0, 1, by omega, by simp only [e0, stateAt], ?_, ?_⟩
      · refine ⟨by simp only [e0, stateAt],
          Or.inl ⟨by simp only [e0, stateAt], i0 + c, v, ?_, ?_⟩, ?_, ?_⟩
        · simp only [e0, stateAt, expHeadEnv, expHeadPhiEnv]
          block_lk
        · simp only [e0, stateAt, expHeadEnv, expHeadPhiEnv]
          block_lk
        · obtain ⟨esg, hesg⟩ := hesign
          exact ⟨esg, by
            simp only [e0, stateAt, expHeadEnv, expHeadPhiEnv]
            block_lk⟩
        · obtain ⟨idig5, ip5, fr5, fd5, h1, h2, h3, h4⟩ := hcarry
          refine ⟨idig5, ip5, fr5, fd5, ?_, ?_, ?_, ?_⟩
          all_goals
            simp only [e0, stateAt, expHeadEnv, expHeadPhiEnv]
            block_lk
      · intro k
        rw [runFuel_jump_prefix hstep1 k]

def expRunBoundLoop (mem0 : Mem) (p n i0 : Nat) (bs : List UInt8) (cost : Nat)
    (hcost : 4 ≤ cost) : BoundLoop calls numFastBody where
  head := "land.lhs.true195"
  exitBlock := "cleanup223.thread"
  N := n - i0
  cost := cost
  Inv := expRunInv mem0 p n i0 bs
  atBound := expRunAtBound mem0 p n i0
  Exit := fun e => e.pc = "cleanup223.thread"
  ExitWord := expRunExit
  step_exit := by
    intro r s c hinv hb
    obtain ⟨e, j, hj, hpc, hword, hrun⟩ := expRun_step_exit hinv hb
    exact ⟨e, j, by omega, hpc, hword, hrun⟩
  step_loop := by
    intro r s c hinv hb
    obtain ⟨e, c', j, hj, hpc, hlt, hinv', hrun⟩ := expRun_step_loop hinv hb
    exact ⟨e, c', j, by omega, hpc, hlt, hinv', hrun⟩
  exit_at_zero := by
    intro s c h
    obtain ⟨_, _, hsum, _, _, _, _, _, _, _, _⟩ := h
    unfold expRunAtBound
    have hle : decide (n - i0 ≤ c + 1) = true := decide_eq_true (by omega)
    rw [hle]
    simp
  budget := by
    intro r s c h
    obtain ⟨_, _, hsum, _, _, _, _, _, _, _, _⟩ := h
    omega

theorem expRun_run (mem0 : Mem) (p n i0 : Nat) (bs : List UInt8) (cost : Nat)
    (hcost : 4 ≤ cost) (s : State) (c : Nat)
    (hinv : expRunInv mem0 p n i0 bs (n - i0) s c) (k : Nat) :
    ∃ (e : State) (j : Nat), j ≤ (n - i0 + 1) * cost ∧ e.pc = "cleanup223.thread" ∧
      expRunExit e ∧
      runFuel calls (j + k) numFastBody s =
        runFuel calls k numFastBody e :=
  (expRunBoundLoop mem0 p n i0 bs cost hcost).run s c hinv k

/-! ### Axiom footprints -/

/-- info: 'LeanLLVM.Refinement.isDigitB_ult' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms isDigitB_ult

/-- info: 'LeanLLVM.Refinement.intRun_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms intRun_run

/-- info: 'LeanLLVM.Refinement.intRun_step_end230' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms intRun_step_end230

/-- info: 'LeanLLVM.Refinement.intRun_end_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms intRun_end_run

/-- info: 'LeanLLVM.Refinement.fracRun_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms fracRun_run

/-- info: 'LeanLLVM.Refinement.expRun_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms expRun_run

end LeanLLVM.Refinement
