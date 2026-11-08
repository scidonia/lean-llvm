/-
The stage-1 depth counter at the LLVM level.

`tests/v16/depth_count.ll` is `v16.generated.ll`'s `@depth_count` — the depth
counter of the stage-1 index stream — with the capture strip applied: the
`nocapture`, `readonly` and `writeonly` parameter attributes, the `align` on the
two loads and the four stores, and the `nuw` flag on the counter's add.  It is
the per-function text the refusal census reads, produced by the same strip that
yields `tests/v16/ci2.ll`, so the module elaborates the text the parser is
measured on rather than a hand-edited copy.  That strip instrument is not part of
this repository; the re-runnable check of the fixture is its
`repo-corpus.manifest` entry and `probes/census/repo-census.sh`.  The file is read
through `include_str` and so is not a `lake build` input: elaborate this module
from source after changing it, and note that the `#guard` below pins the parsed
module to the transcription, so a fixture edited at any instruction — `%more`'s
`ult` to `ule`, say — makes the pin false.

This is a refinement of an emitted kernel, not a model fact.  `depth_count` reads
four bytes and carries two integers; nothing here states anything about the
classifier's vocabulary, and the specification below is written for this kernel
alone.

Proved here: the whole function.  From an initial state whose four parameters are
bound and whose memory holds the index array and the bytes it points at, the
kernel's run returns and stores the depth fold over the token sequence, and
writes nothing outside the two statistics words — `depth_count_refines`.  The
fold is stated at `Int`, because the running depth is a signed quantity and the
kernel's `i64` arithmetic wraps; the kernel's registers are related to those
integers by `BitVec.ofInt 64`, so no hypothesis about the depth staying in range
is needed and none is claimed.

`LeanLLVMTest/Vellum.lean` restates the conclusion, pins the axiom footprint, and
records the mutated-transcription negative control beside the pin rather than
shipping a failing guard.
-/
import LeanLLVM.Parser
import LeanLLVM.Semantics
import LeanLLVM.Memory

-- The state-chain helpers below carry every register of a running block as a
-- parameter, so most of their binders are unused in any one definition.  The two
-- linters are off for this file rather than renaming binders that proof terms
-- name, and the heartbeat budget covers the loop induction.
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000

namespace LeanLLVM.Vellum.DepthCountRefine

open LeanLLVM

/-! ## The fixture -/

/-- The emitted kernel, stripped as the census reads it
(`tests/v16/depth_count.ll`). -/
def src : String := include_str "../../tests/v16/depth_count.ll"

def entryInstrs : List Instr :=
  [ .icmp "%nz" .eq 64 (.reg "%nidx") (.imm (.int 64 (BitVec.ofNat 64 0))) ]

def entryTerm : Term := .condbr (.reg "%nz") "exit0" "loop"

def loopInstrs : List Instr :=
  [ .phi "%k" (.int 64) [("entry", .imm (.int 64 (BitVec.ofNat 64 0))), ("loop", .reg "%kn")],
    .phi "%sp" (.int 64) [("entry", .imm (.int 64 (BitVec.ofNat 64 0))), ("loop", .reg "%spn")],
    .phi "%sum" (.int 64) [("entry", .imm (.int 64 (BitVec.ofNat 64 0))), ("loop", .reg "%sumn")],
    .gep "%ip" (.int 32) (.reg "%idx") (.reg "%k"),
    .load "%p32" (.int 32) (.reg "%ip"),
    .zext "%p" 32 64 (.reg "%p32"),
    .gep "%cp" (.int 8) (.reg "%buf") (.reg "%p"),
    .load "%c" (.int 8) (.reg "%cp"),
    .icmp "%o1" .eq 8 (.reg "%c") (.imm (.int 8 (BitVec.ofNat 8 123))),
    .icmp "%o2" .eq 8 (.reg "%c") (.imm (.int 8 (BitVec.ofNat 8 91))),
    .binop "%isopen" .or 1 (.reg "%o1") (.reg "%o2"),
    .icmp "%c1" .eq 8 (.reg "%c") (.imm (.int 8 (BitVec.ofNat 8 125))),
    .icmp "%c2" .eq 8 (.reg "%c") (.imm (.int 8 (BitVec.ofNat 8 93))),
    .binop "%isclose" .or 1 (.reg "%c1") (.reg "%c2"),
    .zext "%inc" 1 64 (.reg "%isopen"),
    .zext "%dec" 1 64 (.reg "%isclose"),
    .binop "%delta" .sub 64 (.reg "%inc") (.reg "%dec"),
    .binop "%spn" .add 64 (.reg "%sp") (.reg "%delta"),
    .binop "%sumn" .add 64 (.reg "%sum") (.reg "%spn"),
    .binop "%kn" .add 64 (.reg "%k") (.imm (.int 64 (BitVec.ofNat 64 1))),
    .icmp "%more" .ult 64 (.reg "%kn") (.reg "%nidx") ]

def loopTerm : Term := .condbr (.reg "%more") "loop" "exit"

def exitInstrs : List Instr :=
  [ .store (.int 64) (.reg "%spn") (.reg "%stats"),
    .gep "%stats1" (.int 64) (.reg "%stats") (.imm (.int 64 (BitVec.ofNat 64 1))),
    .store (.int 64) (.reg "%sumn") (.reg "%stats1") ]

def exitTerm : Term := .ret (.int 64) (some (.reg "%spn"))

def exit0Instrs : List Instr :=
  [ .store (.int 64) (.imm (.int 64 (BitVec.ofNat 64 0))) (.reg "%stats"),
    .gep "%statsz" (.int 64) (.reg "%stats") (.imm (.int 64 (BitVec.ofNat 64 1))),
    .store (.int 64) (.imm (.int 64 (BitVec.ofNat 64 0))) (.reg "%statsz") ]

def exit0Term : Term := .ret (.int 64) (some (.imm (.int 64 (BitVec.ofNat 64 0))))

def depthFunction : Function :=
  { name := "depth_count"
    retTy := .int 64
    params := [("%buf", .ptr), ("%idx", .ptr), ("%nidx", .int 64), ("%stats", .ptr)]
    blocks :=
      [ { name := "entry", instrs := entryInstrs, term := entryTerm },
        { name := "loop", instrs := loopInstrs, term := loopTerm },
        { name := "exit", instrs := exitInstrs, term := exitTerm },
        { name := "exit0", instrs := exit0Instrs, term := exit0Term } ] }

/- The pin: the parsed module is exactly the transcription above, block by
block and instruction by instruction. -/
#guard
  match parseModule src with
  | .ok m => m = { decls := [], functions := [depthFunction] }
  | .error _ => false

/-! ## The specification

The JsonScanSpec vocabulary is the classifier's: `IsDelimB`, `IsQuoteB`,
`IsBackslashB` and the lane masks.  None of it applies to a depth counter, which
reads four bytes and carries two integers.  What applies is the fold the kernel
is an implementation of: one step per token byte, adding `+1` for an opener,
`-1` for a closer, and accumulating the running depth into a second counter.

The values are stated at `Int`, because the running depth is a signed quantity
and the kernel's `i64` arithmetic wraps.  The kernel's registers are related to
these integers by `BitVec.ofInt 64`, which is exactly "the low 64 bits of the
integer": no hypothesis about the depth staying in range is needed, and none is
claimed. -/

/-- An opener: `{` or `[`. -/
def IsOpenB (c : UInt8) : Bool := decide (c = 123) || decide (c = 91)

/-- A closer: `}` or `]`. -/
def IsCloseB (c : UInt8) : Bool := decide (c = 125) || decide (c = 93)

/-- The step's integer contribution: `+1` for an opener, `-1` for a closer. -/
def openZ (c : UInt8) : Int := if IsOpenB c then 1 else 0

def closeZ (c : UInt8) : Int := if IsCloseB c then 1 else 0

def deltaZ (c : UInt8) : Int := openZ c - closeZ c

/-- One token: the running depth becomes `sp + delta`, and the accumulator gains
the new running depth. -/
def stepZ (st : Int × Int) (c : UInt8) : Int × Int :=
  let sp := st.1 + deltaZ c
  (sp, st.2 + sp)

/-- The fold over a token sequence: `(final depth, sum of the depths after each
token)`. -/
def depthSpec (cs : List UInt8) : Int × Int := cs.foldl stepZ (0, 0)

theorem depthSpec_nil : depthSpec [] = (0, 0) := rfl

theorem depthSpec_append (l : List UInt8) (c : UInt8) :
    depthSpec (l ++ [c]) = stepZ (depthSpec l) c := by
  simp [depthSpec, List.foldl_append]

/-- The token sequence's prefix of length `k + 1` is the prefix of length `k`
followed by token `k`. -/
theorem take_succ (l : List UInt8) (k : Nat) (hk : k < l.length) :
    l.take (k + 1) = l.take k ++ [l[k]] := by
  induction l generalizing k with
  | nil => simp at hk
  | cons a as ih =>
      cases k with
      | zero => rfl
      | succ j =>
          rw [List.take_succ_cons, List.take_succ_cons]
          have hj : j < as.length := by simpa using hk
          rw [ih j hj]
          simp

theorem take_succ' (l : List UInt8) (k : Nat) (hk : k < l.length) :
    l.take (k + 1) = l.take k ++ [l.get ⟨k, hk⟩] := by
  rw [take_succ l k hk]
  rfl

theorem take_all (l : List UInt8) (n : Nat) (h : l.length = n) : l.take n = l := by
  rw [List.take_of_length_le]
  omega

/-! ## The bridges from the kernel's bit arithmetic to the specification

Each is a decided statement over the bytes the kernel can load. -/

/-- `BitVec.ofNat 64` at a value below `2 ^ 63` reads back as that value. -/
theorem toNat_ofNat_of_lt {k : Nat} (h : k < 2^63) :
    (BitVec.ofNat 64 k).toNat = k := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]

/-- The `%kn` step: `ofNat 64 k + 1` is `ofNat 64 (k + 1)` below the wrap. -/
theorem ofNat64_succ (k : Nat) (h : k + 1 < 2^64) :
    (BitVec.ofNat 64 k) + (BitVec.ofNat 64 1) = BitVec.ofNat 64 (k + 1) := by
  rw [← BitVec.ofNat_add]

/-- `BitVec.ult` on `ofNat` operands is the natural order. -/
theorem ult_ofNat (a b : Nat) (ha : a < 2^64) (hb : b < 2^64) :
    BitVec.ult (BitVec.ofNat 64 a) (BitVec.ofNat 64 b) = decide (a < b) := by
  rw [BitVec.ult]
  simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]

/-- A one-bit decision read back as a natural is `if p then 1 else 0`. -/
theorem ofBool_toNat (p : Bool) : (BitVec.ofBool p).toNat = if p then 1 else 0 := by
  cases p <;> rfl

/-- The kernel's `zext i1 to i64` is the specification's integer. -/
theorem zext_bit_value (p : Bool) :
    BitVec.ofNat 64 (BitVec.ofBool p).toNat = BitVec.ofInt 64 (if p then (1 : Int) else 0) := by
  rw [ofBool_toNat]
  cases p <;> simp

/-- The kernel's `zext i1 to i64` over a `Bool`, in the form the simplifier
leaves the `ofBool`. -/
theorem zext_bool_value (p : Bool) :
    BitVec.ofNat 64 p.toNat = BitVec.ofInt 64 (if p = true then (1 : Int) else 0) := by
  cases p <;> simp

/-- `ofInt` distributes over subtraction.  The core has `ofInt_add` and
`ofInt_neg`, not this instance. -/
theorem ofInt_sub (a b : Int) :
    BitVec.ofInt 64 (a - b) = BitVec.ofInt 64 a - BitVec.ofInt 64 b := by
  rw [Int.sub_eq_add_neg, BitVec.ofInt_add, BitVec.ofInt_neg, BitVec.sub_eq_add_neg]

/-- The opener mask the kernel forms is the specification's predicate, over the
eight-bit value the loader produces. -/
theorem openBit_eq (x : BitVec 8) :
    (BitVec.ofBool (x = BitVec.ofNat 8 123) ||| BitVec.ofBool (x = BitVec.ofNat 8 91))
      = BitVec.ofBool (IsOpenB (UInt8.ofBitVec x)) := by
  revert x; decide

theorem closeBit_eq (x : BitVec 8) :
    (BitVec.ofBool (x = BitVec.ofNat 8 125) ||| BitVec.ofBool (x = BitVec.ofNat 8 93))
      = BitVec.ofBool (IsCloseB (UInt8.ofBitVec x)) := by
  revert x; decide

/-- The loaded byte is `UInt8.ofBitVec` of the lane the load leaves. -/
theorem ofBitVec_byte (t : UInt8) : UInt8.ofBitVec (BitVec.ofNat 8 t.toNat) = t := by
  rw [show (BitVec.ofNat 8 t.toNat : BitVec 8) = t.toBitVec from
    (BitVec.ofNat_toNat 8 t.toBitVec).trans (BitVec.setWidth_eq _)]

/-- A load of an `i32` over a little-endian encoding of a value below `2 ^ 32`
reads that value back. -/
theorem bytesToNat_natToBytes4 {a : Nat} (h : a < 2^32) :
    bytesToNat (natToBytes a 4) = a := by
  rw [natToBytes_toNat]
  rw [show (256 : Nat) ^ 4 = 2^32 from by decide]
  exact Nat.mod_eq_of_lt h

/-- A load of an `i8` over a one-byte read. -/
theorem bytesToNat_single (t : UInt8) : bytesToNat [t] = t.toNat := by
  simp [bytesToNat]



/-! ## The instruction shapes -/

/-- Execute a straight-line instruction sequence. -/
theorem denoteCode_cons_of (calls : Calls) (i : Instr) (is : List Instr) (s s' : State)
    (h : evalInstr calls s i = some s') :
    denoteCode calls (i :: is) s = denoteCode calls is s' := by
  simp only [denoteCode, h]

theorem evalInstr_icmp8 (calls : Calls) (s : State) (d r : String) (b v : BitVec 8)
    (h : lookupName s.env r = some (.int 8 b)) :
    evalInstr calls s (.icmp d .eq 8 (.reg r) (.imm (.int 8 v))) =
      some (s.bind d (.int 1 (BitVec.ofBool (b = v)))) := by
  simp [evalInstr, evalOperand, Const.toValue, h, Value.intToNat, evalICmpNat, evalICmp]

theorem evalInstr_or1_reg (calls : Calls) (s : State) (d r₁ r₂ : String)
    (a b : BitVec 1)
    (h₁ : lookupName s.env r₁ = some (.int 1 a))
    (h₂ : lookupName s.env r₂ = some (.int 1 b)) :
    evalInstr calls s (.binop d .or 1 (.reg r₁) (.reg r₂)) =
      some (s.bind d (.int 1 (a ||| b))) := by
  simp [evalInstr, evalOperand, h₁, h₂, Value.intToNat, evalBinopNat, evalBinop]

theorem evalInstr_zext1_64 (calls : Calls) (s : State) (d r : String) (b : BitVec 1)
    (h : lookupName s.env r = some (.int 1 b)) :
    evalInstr calls s (.zext d 1 64 (.reg r)) =
      some (s.bind d (.int 64 (BitVec.ofNat 64 b.toNat))) := by
  simp [evalInstr, evalOperand, h]

theorem evalInstr_zext32_64 (calls : Calls) (s : State) (d r : String) (b : BitVec 32)
    (h : lookupName s.env r = some (.int 32 b)) :
    evalInstr calls s (.zext d 32 64 (.reg r)) =
      some (s.bind d (.int 64 (BitVec.ofNat 64 b.toNat))) := by
  simp [evalInstr, evalOperand, h]

theorem evalInstr_add64 (calls : Calls) (s : State) (d r₁ r₂ : String)
    (a b : BitVec 64)
    (h₁ : lookupName s.env r₁ = some (.int 64 a))
    (h₂ : lookupName s.env r₂ = some (.int 64 b)) :
    evalInstr calls s (.binop d .add 64 (.reg r₁) (.reg r₂)) =
      some (s.bind d (.int 64 (a + b))) := by
  simp [evalInstr, evalOperand, h₁, h₂, Value.intToNat, evalBinopNat, evalBinop]
  rw [← BitVec.toNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem evalInstr_add64_imm (calls : Calls) (s : State) (d r : String)
    (a b : BitVec 64) (h : lookupName s.env r = some (.int 64 a)) :
    evalInstr calls s (.binop d .add 64 (.reg r) (.imm (.int 64 b))) =
      some (s.bind d (.int 64 (a + b))) := by
  simp [evalInstr, evalOperand, Const.toValue, h, Value.intToNat, evalBinopNat, evalBinop]
  rw [← BitVec.toNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem evalInstr_sub64 (calls : Calls) (s : State) (d r₁ r₂ : String)
    (a b : BitVec 64)
    (h₁ : lookupName s.env r₁ = some (.int 64 a))
    (h₂ : lookupName s.env r₂ = some (.int 64 b)) :
    evalInstr calls s (.binop d .sub 64 (.reg r₁) (.reg r₂)) =
      some (s.bind d (.int 64 (a - b))) := by
  simp [evalInstr, evalOperand, h₁, h₂, Value.intToNat, evalBinopNat, evalBinop]
  rw [show (18446744073709551616 : Nat) = 2 ^ 64 from rfl]
  rw [← BitVec.toNat_sub, BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem evalInstr_ult64 (calls : Calls) (s : State) (d r₁ r₂ : String)
    (a b : BitVec 64)
    (h₁ : lookupName s.env r₁ = some (.int 64 a))
    (h₂ : lookupName s.env r₂ = some (.int 64 b)) :
    evalInstr calls s (.icmp d .ult 64 (.reg r₁) (.reg r₂)) =
      some (s.bind d (.int 1 (BitVec.ofBool (BitVec.ult a b)))) := by
  simp [evalInstr, evalOperand, h₁, h₂, Value.intToNat, evalICmpNat, evalICmp]

theorem evalInstr_gep32_reg (calls : Calls) (s : State) (d base off : String)
    (addr : Nat) (o : BitVec 64)
    (hb : lookupName s.env base = some (.ptr addr))
    (ho : lookupName s.env off = some (.int 64 o))
    (h : o.toNat < 2^63) :
    evalInstr calls s (.gep d (.int 32) (.reg base) (.reg off)) =
      some (s.bind d (.ptr (addr + o.toNat * 4))) := by
  simp [evalInstr, evalOperand, hb, ho, h, Ty.sizeBytes]

theorem evalInstr_gep8_reg (calls : Calls) (s : State) (d base off : String)
    (addr : Nat) (o : BitVec 64)
    (hb : lookupName s.env base = some (.ptr addr))
    (ho : lookupName s.env off = some (.int 64 o))
    (h : o.toNat < 2^63) :
    evalInstr calls s (.gep d (.int 8) (.reg base) (.reg off)) =
      some (s.bind d (.ptr (addr + o.toNat))) := by
  simp [evalInstr, evalOperand, hb, ho, h, Ty.sizeBytes]

theorem evalInstr_gep64_imm (calls : Calls) (s : State) (d base : String)
    (addr : Nat) (o : BitVec 64)
    (hb : lookupName s.env base = some (.ptr addr))
    (h : o.toNat < 2^63) :
    evalInstr calls s (.gep d (.int 64) (.reg base) (.imm (.int 64 o))) =
      some (s.bind d (.ptr (addr + o.toNat * 8))) := by
  simp [evalInstr, evalOperand, Const.toValue, hb, h, Ty.sizeBytes]

theorem evalInstr_load32 (calls : Calls) (s : State) (p r : String)
    (addr : Nat) (bs : List UInt8)
    (h : lookupName s.env r = some (.ptr addr))
    (hr : readBytes s.mem addr 4 = some bs) :
    evalInstr calls s (.load p (.int 32) (.reg r)) =
      some (s.bind p (.int 32 (BitVec.ofNat 32 (bytesToNat bs)))) := by
  simp [evalInstr, evalOperand, h, loadValue, hr]

theorem evalInstr_load8 (calls : Calls) (s : State) (p r : String)
    (addr : Nat) (bs : List UInt8)
    (h : lookupName s.env r = some (.ptr addr))
    (hr : readBytes s.mem addr 1 = some bs) :
    evalInstr calls s (.load p (.int 8) (.reg r)) =
      some (s.bind p (.int 8 (BitVec.ofNat 8 (bytesToNat bs)))) := by
  simp [evalInstr, evalOperand, h, loadValue, hr]

theorem evalInstr_store64 (calls : Calls) (s : State) (v p : String)
    (x : BitVec 64) (addr : Nat)
    (hv : lookupName s.env v = some (.int 64 x))
    (hp : lookupName s.env p = some (.ptr addr)) :
    evalInstr calls s (.store (.int 64) (.reg v) (.reg p)) =
      some { s with mem := writeBytes s.mem addr (natToBytes x.toNat 8) } := by
  simp [evalInstr, evalOperand, hv, hp, storeValue]

theorem evalInstr_phi_reg (s : State) {calls : Calls} {d : String} {ty : Ty}
    {inc : List (String × Operand)} {pre : String}
    (op : String) (v : Value)
    (hpre : s.pre = some pre) (hinc : phiIncoming pre inc = some (.reg op))
    (hop : lookupName s.env op = some v) :
    evalInstr calls s (.phi d ty inc) = some (s.bind d v) := by
  rw [evalInstr_phi hpre hinc]
  simp [evalOperand, hop]

theorem evalInstr_phi_imm (s : State) {calls : Calls} {d : String} {ty : Ty}
    {inc : List (String × Operand)} {pre : String}
    (c : Const) (v : Value)
    (hpre : s.pre = some pre) (hinc : phiIncoming pre inc = some (.imm c))
    (hcv : Const.toValue c = some v) :
    evalInstr calls s (.phi d ty inc) = some (s.bind d v) := by
  rw [evalInstr_phi hpre hinc]
  simp [evalOperand, hcv]

/-! ## The values the body binds

Every register's value is named once, so the chain and the lemmas can be read
against each other. -/

def Vk (k : Nat) : Value := .int 64 (BitVec.ofNat 64 k)
def Vs (x : BitVec 64) : Value := .int 64 x
def Vip (pidx k : Nat) : Value := .ptr (pidx + k * 4)
def Vp32 (a : Nat) : Value := .int 32 (BitVec.ofNat 32 a)
def Vp (a : Nat) : Value := .int 64 (BitVec.ofNat 64 a)
def Vcp (pbuf a : Nat) : Value := .ptr (pbuf + a)
def Vc (t : UInt8) : Value := .int 8 (BitVec.ofNat 8 t.toNat)
def Vo (t : UInt8) (x : Nat) : Value :=
  .int 1 (BitVec.ofBool (BitVec.ofNat 8 t.toNat = BitVec.ofNat 8 x))
def Vopen (t : UInt8) : Value := .int 1 (BitVec.ofBool (IsOpenB t))
def Vclose (t : UInt8) : Value := .int 1 (BitVec.ofBool (IsCloseB t))
def Vinc (t : UInt8) : Value := .int 64 (BitVec.ofInt 64 (openZ t))
def Vdec (t : UInt8) : Value := .int 64 (BitVec.ofInt 64 (closeZ t))
def Vdelta (t : UInt8) : Value := .int 64 (BitVec.ofInt 64 (deltaZ t))
def Vspn (sp : BitVec 64) (t : UInt8) : Value :=
  .int 64 (sp + BitVec.ofInt 64 (deltaZ t))
def Vsumn (sum sp : BitVec 64) (t : UInt8) : Value :=
  .int 64 (sum + (sp + BitVec.ofInt 64 (deltaZ t)))
def Vkn (k : Nat) : Value := .int 64 (BitVec.ofNat 64 (k + 1))
def Vmore (n k : Nat) : Value := .int 1 (BitVec.ofBool (decide (k + 1 < n)))

/-! ## The chain the body computes -/

def c0 (s : State) (pidx pbuf n k : Nat) (sp sum : BitVec 64) (a : Nat) (t : UInt8) : State := s

def c1 (s : State) (pidx pbuf n k : Nat) (sp sum : BitVec 64) (a : Nat) (t : UInt8) : State :=
  (c0 s pidx pbuf n k sp sum a t).bind "%k" (Vk k)

def c2 (s : State) (pidx pbuf n k : Nat) (sp sum : BitVec 64) (a : Nat) (t : UInt8) : State :=
  (c1 s pidx pbuf n k sp sum a t).bind "%sp" (Vs sp)

def c3 (s : State) (pidx pbuf n k : Nat) (sp sum : BitVec 64) (a : Nat) (t : UInt8) : State :=
  (c2 s pidx pbuf n k sp sum a t).bind "%sum" (Vs sum)

def c4 (s : State) (pidx pbuf n k : Nat) (sp sum : BitVec 64) (a : Nat) (t : UInt8) : State :=
  (c3 s pidx pbuf n k sp sum a t).bind "%ip" (Vip pidx k)

def c5 (s : State) (pidx pbuf n k : Nat) (sp sum : BitVec 64) (a : Nat) (t : UInt8) : State :=
  (c4 s pidx pbuf n k sp sum a t).bind "%p32" (Vp32 a)

def c6 (s : State) (pidx pbuf n k : Nat) (sp sum : BitVec 64) (a : Nat) (t : UInt8) : State :=
  (c5 s pidx pbuf n k sp sum a t).bind "%p" (Vp a)

def c7 (s : State) (pidx pbuf n k : Nat) (sp sum : BitVec 64) (a : Nat) (t : UInt8) : State :=
  (c6 s pidx pbuf n k sp sum a t).bind "%cp" (Vcp pbuf a)

def c8 (s : State) (pidx pbuf n k : Nat) (sp sum : BitVec 64) (a : Nat) (t : UInt8) : State :=
  (c7 s pidx pbuf n k sp sum a t).bind "%c" (Vc t)

def c9 (s : State) (pidx pbuf n k : Nat) (sp sum : BitVec 64) (a : Nat) (t : UInt8) : State :=
  (c8 s pidx pbuf n k sp sum a t).bind "%o1" (Vo t 123)

def c10 (s : State) (pidx pbuf n k : Nat) (sp sum : BitVec 64) (a : Nat) (t : UInt8) : State :=
  (c9 s pidx pbuf n k sp sum a t).bind "%o2" (Vo t 91)

def c11 (s : State) (pidx pbuf n k : Nat) (sp sum : BitVec 64) (a : Nat) (t : UInt8) : State :=
  (c10 s pidx pbuf n k sp sum a t).bind "%isopen" (Vopen t)

def c12 (s : State) (pidx pbuf n k : Nat) (sp sum : BitVec 64) (a : Nat) (t : UInt8) : State :=
  (c11 s pidx pbuf n k sp sum a t).bind "%c1" (Vo t 125)

def c13 (s : State) (pidx pbuf n k : Nat) (sp sum : BitVec 64) (a : Nat) (t : UInt8) : State :=
  (c12 s pidx pbuf n k sp sum a t).bind "%c2" (Vo t 93)

def c14 (s : State) (pidx pbuf n k : Nat) (sp sum : BitVec 64) (a : Nat) (t : UInt8) : State :=
  (c13 s pidx pbuf n k sp sum a t).bind "%isclose" (Vclose t)

def c15 (s : State) (pidx pbuf n k : Nat) (sp sum : BitVec 64) (a : Nat) (t : UInt8) : State :=
  (c14 s pidx pbuf n k sp sum a t).bind "%inc" (Vinc t)

def c16 (s : State) (pidx pbuf n k : Nat) (sp sum : BitVec 64) (a : Nat) (t : UInt8) : State :=
  (c15 s pidx pbuf n k sp sum a t).bind "%dec" (Vdec t)

def c17 (s : State) (pidx pbuf n k : Nat) (sp sum : BitVec 64) (a : Nat) (t : UInt8) : State :=
  (c16 s pidx pbuf n k sp sum a t).bind "%delta" (Vdelta t)

def c18 (s : State) (pidx pbuf n k : Nat) (sp sum : BitVec 64) (a : Nat) (t : UInt8) : State :=
  (c17 s pidx pbuf n k sp sum a t).bind "%spn" (Vspn sp t)

def c19 (s : State) (pidx pbuf n k : Nat) (sp sum : BitVec 64) (a : Nat) (t : UInt8) : State :=
  (c18 s pidx pbuf n k sp sum a t).bind "%sumn" (Vsumn sum sp t)

def c20 (s : State) (pidx pbuf n k : Nat) (sp sum : BitVec 64) (a : Nat) (t : UInt8) : State :=
  (c19 s pidx pbuf n k sp sum a t).bind "%kn" (Vkn k)

def c21 (s : State) (pidx pbuf n k : Nat) (sp sum : BitVec 64) (a : Nat) (t : UInt8) : State :=
  (c20 s pidx pbuf n k sp sum a t).bind "%more" (Vmore n k)

/-! ## One step per instruction -/

/-- Instruction 1: the `%k` phi, selecting the entry's literal or the
previous iteration's `%kn`. -/
theorem step01 (calls : Calls) (s : State) (pidx pbuf : Nat) (n k : Nat)
    (sp sum : BitVec 64) (a : Nat) (t : UInt8)
    (hn : n < 2^63) (hk : k < 2^63)
    (hidx : lookupName s.env "%idx" = some (.ptr pidx))
    (hbuf : lookupName s.env "%buf" = some (.ptr pbuf))
    (hnidx : lookupName s.env "%nidx" = some (.int 64 (BitVec.ofNat 64 n)))
    (hread : readBytes s.mem (pidx + k * 4) 4 = some (natToBytes a 4))
    (hafit : a < 2^32)
    (htok : readBytes s.mem (pbuf + a) 1 = some [t])
    (hphi : (s.pre = some "entry" ∧ k = 0 ∧ sp = 0 ∧ sum = 0) ∨
            (s.pre = some "loop" ∧
              lookupName s.env "%kn" = some (.int 64 (BitVec.ofNat 64 k)) ∧
              lookupName s.env "%spn" = some (.int 64 sp) ∧
              lookupName s.env "%sumn" = some (.int 64 sum))) :
    evalInstr calls s
      (.phi "%k" (.int 64) [("entry", .imm (.int 64 (BitVec.ofNat 64 0))), ("loop", .reg "%kn")]) = some (c1 s pidx pbuf n k sp sum a t) := by
  rcases hphi with ⟨hpre, hk0, -, -⟩ | ⟨hpre, hkn, -, -⟩
  · subst hk0
    rw [evalInstr_phi_imm s (.int 64 (BitVec.ofNat 64 0)) (.int 64 (BitVec.ofNat 64 0)) hpre (by simp [phiIncoming]) (by rfl)]
    simp [c0, c1, Vk]
  · rw [evalInstr_phi_reg s "%kn" (.int 64 (BitVec.ofNat 64 k)) hpre (by simp [phiIncoming]) hkn]
    simp [c0, c1, Vk]

/-- Instruction 2: the `%sp` phi. -/
theorem step02 (calls : Calls) (s : State) (pidx pbuf : Nat) (n k : Nat)
    (sp sum : BitVec 64) (a : Nat) (t : UInt8)
    (hn : n < 2^63) (hk : k < 2^63)
    (hidx : lookupName s.env "%idx" = some (.ptr pidx))
    (hbuf : lookupName s.env "%buf" = some (.ptr pbuf))
    (hnidx : lookupName s.env "%nidx" = some (.int 64 (BitVec.ofNat 64 n)))
    (hread : readBytes s.mem (pidx + k * 4) 4 = some (natToBytes a 4))
    (hafit : a < 2^32)
    (htok : readBytes s.mem (pbuf + a) 1 = some [t])
    (hphi : (s.pre = some "entry" ∧ k = 0 ∧ sp = 0 ∧ sum = 0) ∨
            (s.pre = some "loop" ∧
              lookupName s.env "%kn" = some (.int 64 (BitVec.ofNat 64 k)) ∧
              lookupName s.env "%spn" = some (.int 64 sp) ∧
              lookupName s.env "%sumn" = some (.int 64 sum))) :
    evalInstr calls (c1 s pidx pbuf n k sp sum a t)
      (.phi "%sp" (.int 64) [("entry", .imm (.int 64 (BitVec.ofNat 64 0))), ("loop", .reg "%spn")]) = some (c2 s pidx pbuf n k sp sum a t) := by
  rcases hphi with ⟨hpre, hk0, hsp, -⟩ | ⟨hpre, -, hspn, -⟩
  · subst hk0; subst hsp
    rw [evalInstr_phi_imm (c1 s pidx pbuf n 0 0 sum a t) (.int 64 (BitVec.ofNat 64 0)) (.int 64 (BitVec.ofNat 64 0)) hpre
      (by simp [phiIncoming]) (by rfl)]
    simp [c1, c2, Vs, Vk]
  · rw [evalInstr_phi_reg (c1 s pidx pbuf n k sp sum a t) "%spn" (.int 64 sp) hpre
      (by simp [phiIncoming]) hspn]
    simp [c1, c2, Vs, Vk]

/-- Instruction 3: the `%sum` phi. -/
theorem step03 (calls : Calls) (s : State) (pidx pbuf : Nat) (n k : Nat)
    (sp sum : BitVec 64) (a : Nat) (t : UInt8)
    (hn : n < 2^63) (hk : k < 2^63)
    (hidx : lookupName s.env "%idx" = some (.ptr pidx))
    (hbuf : lookupName s.env "%buf" = some (.ptr pbuf))
    (hnidx : lookupName s.env "%nidx" = some (.int 64 (BitVec.ofNat 64 n)))
    (hread : readBytes s.mem (pidx + k * 4) 4 = some (natToBytes a 4))
    (hafit : a < 2^32)
    (htok : readBytes s.mem (pbuf + a) 1 = some [t])
    (hphi : (s.pre = some "entry" ∧ k = 0 ∧ sp = 0 ∧ sum = 0) ∨
            (s.pre = some "loop" ∧
              lookupName s.env "%kn" = some (.int 64 (BitVec.ofNat 64 k)) ∧
              lookupName s.env "%spn" = some (.int 64 sp) ∧
              lookupName s.env "%sumn" = some (.int 64 sum))) :
    evalInstr calls (c2 s pidx pbuf n k sp sum a t)
      (.phi "%sum" (.int 64) [("entry", .imm (.int 64 (BitVec.ofNat 64 0))), ("loop", .reg "%sumn")]) = some (c3 s pidx pbuf n k sp sum a t) := by
  rcases hphi with ⟨hpre, hk0, -, hsu⟩ | ⟨hpre, -, -, hsumn⟩
  · subst hk0; subst hsu
    rw [evalInstr_phi_imm (c2 s pidx pbuf n 0 sp 0 a t) (.int 64 (BitVec.ofNat 64 0)) (.int 64 (BitVec.ofNat 64 0)) hpre
      (by simp [phiIncoming]) (by rfl)]
    simp [c2, c3, Vs, Vk]
  · rw [evalInstr_phi_reg (c2 s pidx pbuf n k sp sum a t) "%sumn" (.int 64 sum) hpre
      (by simp [phiIncoming]) hsumn]
    simp [c2, c3, Vs, Vk]

/-- Instruction 4 of the loop body. -/
theorem step04 (calls : Calls) (s : State) (pidx pbuf : Nat) (n k : Nat)
    (sp sum : BitVec 64) (a : Nat) (t : UInt8)
    (hn : n < 2^63) (hk : k < 2^63)
    (hidx : lookupName s.env "%idx" = some (.ptr pidx))
    (hbuf : lookupName s.env "%buf" = some (.ptr pbuf))
    (hnidx : lookupName s.env "%nidx" = some (.int 64 (BitVec.ofNat 64 n)))
    (hread : readBytes s.mem (pidx + k * 4) 4 = some (natToBytes a 4))
    (hafit : a < 2^32)
    (htok : readBytes s.mem (pbuf + a) 1 = some [t]) :
    evalInstr calls (c3 s pidx pbuf n k sp sum a t) (.gep "%ip" (.int 32) (.reg "%idx") (.reg "%k")) =
      some (c4 s pidx pbuf n k sp sum a t) := by
  rw [evalInstr_gep32_reg calls (c3 s pidx pbuf n k sp sum a t) "%ip" "%idx" "%k" pidx
      (BitVec.ofNat 64 k)
      (by simpa [c0, c1, c2, c3, State.bind, lookupName] using hidx) (by simp [c0, c1, c2, c3, Vk, Vs, Vip, Vp32, Vp, Vcp, Vc, Vo, Vopen, Vclose, Vinc, Vdec, Vdelta, Vspn, Vsumn, Vkn, Vmore, State.bind, lookupName])
      (by rw [toNat_ofNat_of_lt hk]; exact hk)]
  simp [c4, Vip, toNat_ofNat_of_lt hk]

/-- Instruction 5 of the loop body. -/
theorem step05 (calls : Calls) (s : State) (pidx pbuf : Nat) (n k : Nat)
    (sp sum : BitVec 64) (a : Nat) (t : UInt8)
    (hn : n < 2^63) (hk : k < 2^63)
    (hidx : lookupName s.env "%idx" = some (.ptr pidx))
    (hbuf : lookupName s.env "%buf" = some (.ptr pbuf))
    (hnidx : lookupName s.env "%nidx" = some (.int 64 (BitVec.ofNat 64 n)))
    (hread : readBytes s.mem (pidx + k * 4) 4 = some (natToBytes a 4))
    (hafit : a < 2^32)
    (htok : readBytes s.mem (pbuf + a) 1 = some [t]) :
    evalInstr calls (c4 s pidx pbuf n k sp sum a t) (.load "%p32" (.int 32) (.reg "%ip")) =
      some (c5 s pidx pbuf n k sp sum a t) := by
  rw [evalInstr_load32 calls (c4 s pidx pbuf n k sp sum a t) "%p32" "%ip"
      (pidx + k * 4) (natToBytes a 4) (by simp [c0, c1, c2, c3, c4, Vk, Vs, Vip, Vp32, Vp, Vcp, Vc, Vo, Vopen, Vclose, Vinc, Vdec, Vdelta, Vspn, Vsumn, Vkn, Vmore, State.bind, lookupName]) hread]
  simp [c5, Vp32, bytesToNat_natToBytes4 hafit]

/-- Instruction 6 of the loop body. -/
theorem step06 (calls : Calls) (s : State) (pidx pbuf : Nat) (n k : Nat)
    (sp sum : BitVec 64) (a : Nat) (t : UInt8)
    (hn : n < 2^63) (hk : k < 2^63)
    (hidx : lookupName s.env "%idx" = some (.ptr pidx))
    (hbuf : lookupName s.env "%buf" = some (.ptr pbuf))
    (hnidx : lookupName s.env "%nidx" = some (.int 64 (BitVec.ofNat 64 n)))
    (hread : readBytes s.mem (pidx + k * 4) 4 = some (natToBytes a 4))
    (hafit : a < 2^32)
    (htok : readBytes s.mem (pbuf + a) 1 = some [t]) :
    evalInstr calls (c5 s pidx pbuf n k sp sum a t) (.zext "%p" 32 64 (.reg "%p32")) =
      some (c6 s pidx pbuf n k sp sum a t) := by
  rw [evalInstr_zext32_64 calls (c5 s pidx pbuf n k sp sum a t) "%p" "%p32"
      (BitVec.ofNat 32 a) (by simp [c0, c1, c2, c3, c4, c5, Vk, Vs, Vip, Vp32, Vp, Vcp, Vc, Vo, Vopen, Vclose, Vinc, Vdec, Vdelta, Vspn, Vsumn, Vkn, Vmore, State.bind, lookupName])]
  simp [c6, Vp, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : a < 2^32)]

/-- Instruction 7 of the loop body. -/
theorem step07 (calls : Calls) (s : State) (pidx pbuf : Nat) (n k : Nat)
    (sp sum : BitVec 64) (a : Nat) (t : UInt8)
    (hn : n < 2^63) (hk : k < 2^63)
    (hidx : lookupName s.env "%idx" = some (.ptr pidx))
    (hbuf : lookupName s.env "%buf" = some (.ptr pbuf))
    (hnidx : lookupName s.env "%nidx" = some (.int 64 (BitVec.ofNat 64 n)))
    (hread : readBytes s.mem (pidx + k * 4) 4 = some (natToBytes a 4))
    (hafit : a < 2^32)
    (htok : readBytes s.mem (pbuf + a) 1 = some [t]) :
    evalInstr calls (c6 s pidx pbuf n k sp sum a t) (.gep "%cp" (.int 8) (.reg "%buf") (.reg "%p")) =
      some (c7 s pidx pbuf n k sp sum a t) := by
  rw [evalInstr_gep8_reg calls (c6 s pidx pbuf n k sp sum a t) "%cp" "%buf" "%p" pbuf
      (BitVec.ofNat 64 a) (by simpa [c0, c1, c2, c3, c4, c5, c6, State.bind, lookupName] using hbuf) (by simp [c0, c1, c2, c3, c4, c5, c6, Vk, Vs, Vip, Vp32, Vp, Vcp, Vc, Vo, Vopen, Vclose, Vinc, Vdec, Vdelta, Vspn, Vsumn, Vkn, Vmore, State.bind, lookupName])
      (by rw [toNat_ofNat_of_lt (by omega)]; omega)]
  rw [toNat_ofNat_of_lt (by omega)]
  simp [c7, Vcp]

/-- Instruction 8 of the loop body. -/
theorem step08 (calls : Calls) (s : State) (pidx pbuf : Nat) (n k : Nat)
    (sp sum : BitVec 64) (a : Nat) (t : UInt8)
    (hn : n < 2^63) (hk : k < 2^63)
    (hidx : lookupName s.env "%idx" = some (.ptr pidx))
    (hbuf : lookupName s.env "%buf" = some (.ptr pbuf))
    (hnidx : lookupName s.env "%nidx" = some (.int 64 (BitVec.ofNat 64 n)))
    (hread : readBytes s.mem (pidx + k * 4) 4 = some (natToBytes a 4))
    (hafit : a < 2^32)
    (htok : readBytes s.mem (pbuf + a) 1 = some [t]) :
    evalInstr calls (c7 s pidx pbuf n k sp sum a t) (.load "%c" (.int 8) (.reg "%cp")) =
      some (c8 s pidx pbuf n k sp sum a t) := by
  rw [evalInstr_load8 calls (c7 s pidx pbuf n k sp sum a t) "%c" "%cp" (pbuf + a) [t]
      (by simp [c0, c1, c2, c3, c4, c5, c6, c7, Vk, Vs, Vip, Vp32, Vp, Vcp, Vc, Vo, Vopen, Vclose, Vinc, Vdec, Vdelta, Vspn, Vsumn, Vkn, Vmore, State.bind, lookupName]) htok]
  simp [c8, Vc, bytesToNat_single]

/-- Instruction 9 of the loop body. -/
theorem step09 (calls : Calls) (s : State) (pidx pbuf : Nat) (n k : Nat)
    (sp sum : BitVec 64) (a : Nat) (t : UInt8)
    (hn : n < 2^63) (hk : k < 2^63)
    (hidx : lookupName s.env "%idx" = some (.ptr pidx))
    (hbuf : lookupName s.env "%buf" = some (.ptr pbuf))
    (hnidx : lookupName s.env "%nidx" = some (.int 64 (BitVec.ofNat 64 n)))
    (hread : readBytes s.mem (pidx + k * 4) 4 = some (natToBytes a 4))
    (hafit : a < 2^32)
    (htok : readBytes s.mem (pbuf + a) 1 = some [t]) :
    evalInstr calls (c8 s pidx pbuf n k sp sum a t) (.icmp "%o1" .eq 8 (.reg "%c") (.imm (.int 8 (BitVec.ofNat 8 123)))) =
      some (c9 s pidx pbuf n k sp sum a t) := by
  rw [evalInstr_icmp8 calls (c8 s pidx pbuf n k sp sum a t) "%o1" "%c"
      (BitVec.ofNat 8 t.toNat) (BitVec.ofNat 8 123) (by simp [c0, c1, c2, c3, c4, c5, c6, c7, c8, Vk, Vs, Vip, Vp32, Vp, Vcp, Vc, Vo, Vopen, Vclose, Vinc, Vdec, Vdelta, Vspn, Vsumn, Vkn, Vmore, State.bind, lookupName])]
  simp [c9, Vo]

/-- Instruction 10 of the loop body. -/
theorem step10 (calls : Calls) (s : State) (pidx pbuf : Nat) (n k : Nat)
    (sp sum : BitVec 64) (a : Nat) (t : UInt8)
    (hn : n < 2^63) (hk : k < 2^63)
    (hidx : lookupName s.env "%idx" = some (.ptr pidx))
    (hbuf : lookupName s.env "%buf" = some (.ptr pbuf))
    (hnidx : lookupName s.env "%nidx" = some (.int 64 (BitVec.ofNat 64 n)))
    (hread : readBytes s.mem (pidx + k * 4) 4 = some (natToBytes a 4))
    (hafit : a < 2^32)
    (htok : readBytes s.mem (pbuf + a) 1 = some [t]) :
    evalInstr calls (c9 s pidx pbuf n k sp sum a t) (.icmp "%o2" .eq 8 (.reg "%c") (.imm (.int 8 (BitVec.ofNat 8 91)))) =
      some (c10 s pidx pbuf n k sp sum a t) := by
  rw [evalInstr_icmp8 calls (c9 s pidx pbuf n k sp sum a t) "%o2" "%c"
      (BitVec.ofNat 8 t.toNat) (BitVec.ofNat 8 91) (by simp [c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, Vk, Vs, Vip, Vp32, Vp, Vcp, Vc, Vo, Vopen, Vclose, Vinc, Vdec, Vdelta, Vspn, Vsumn, Vkn, Vmore, State.bind, lookupName])]
  simp [c10, Vo]

/-- Instruction 11 of the loop body. -/
theorem step11 (calls : Calls) (s : State) (pidx pbuf : Nat) (n k : Nat)
    (sp sum : BitVec 64) (a : Nat) (t : UInt8)
    (hn : n < 2^63) (hk : k < 2^63)
    (hidx : lookupName s.env "%idx" = some (.ptr pidx))
    (hbuf : lookupName s.env "%buf" = some (.ptr pbuf))
    (hnidx : lookupName s.env "%nidx" = some (.int 64 (BitVec.ofNat 64 n)))
    (hread : readBytes s.mem (pidx + k * 4) 4 = some (natToBytes a 4))
    (hafit : a < 2^32)
    (htok : readBytes s.mem (pbuf + a) 1 = some [t]) :
    evalInstr calls (c10 s pidx pbuf n k sp sum a t) (.binop "%isopen" .or 1 (.reg "%o1") (.reg "%o2")) =
      some (c11 s pidx pbuf n k sp sum a t) := by
  rw [evalInstr_or1_reg calls (c10 s pidx pbuf n k sp sum a t) "%isopen" "%o1" "%o2"
      (BitVec.ofBool (BitVec.ofNat 8 t.toNat = BitVec.ofNat 8 123))
      (BitVec.ofBool (BitVec.ofNat 8 t.toNat = BitVec.ofNat 8 91))
      (by simp [c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, Vk, Vs, Vip, Vp32, Vp, Vcp, Vc, Vo, Vopen, Vclose, Vinc, Vdec, Vdelta, Vspn, Vsumn, Vkn, Vmore, State.bind, lookupName]) (by simp [c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, Vk, Vs, Vip, Vp32, Vp, Vcp, Vc, Vo, Vopen, Vclose, Vinc, Vdec, Vdelta, Vspn, Vsumn, Vkn, Vmore, State.bind, lookupName])]
  rw [openBit_eq (BitVec.ofNat 8 t.toNat), ofBitVec_byte]
  simp [c11, Vopen]

/-- Instruction 12 of the loop body. -/
theorem step12 (calls : Calls) (s : State) (pidx pbuf : Nat) (n k : Nat)
    (sp sum : BitVec 64) (a : Nat) (t : UInt8)
    (hn : n < 2^63) (hk : k < 2^63)
    (hidx : lookupName s.env "%idx" = some (.ptr pidx))
    (hbuf : lookupName s.env "%buf" = some (.ptr pbuf))
    (hnidx : lookupName s.env "%nidx" = some (.int 64 (BitVec.ofNat 64 n)))
    (hread : readBytes s.mem (pidx + k * 4) 4 = some (natToBytes a 4))
    (hafit : a < 2^32)
    (htok : readBytes s.mem (pbuf + a) 1 = some [t]) :
    evalInstr calls (c11 s pidx pbuf n k sp sum a t) (.icmp "%c1" .eq 8 (.reg "%c") (.imm (.int 8 (BitVec.ofNat 8 125)))) =
      some (c12 s pidx pbuf n k sp sum a t) := by
  rw [evalInstr_icmp8 calls (c11 s pidx pbuf n k sp sum a t) "%c1" "%c"
      (BitVec.ofNat 8 t.toNat) (BitVec.ofNat 8 125) (by simp [c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, Vk, Vs, Vip, Vp32, Vp, Vcp, Vc, Vo, Vopen, Vclose, Vinc, Vdec, Vdelta, Vspn, Vsumn, Vkn, Vmore, State.bind, lookupName])]
  simp [c12, Vo]

/-- Instruction 13 of the loop body. -/
theorem step13 (calls : Calls) (s : State) (pidx pbuf : Nat) (n k : Nat)
    (sp sum : BitVec 64) (a : Nat) (t : UInt8)
    (hn : n < 2^63) (hk : k < 2^63)
    (hidx : lookupName s.env "%idx" = some (.ptr pidx))
    (hbuf : lookupName s.env "%buf" = some (.ptr pbuf))
    (hnidx : lookupName s.env "%nidx" = some (.int 64 (BitVec.ofNat 64 n)))
    (hread : readBytes s.mem (pidx + k * 4) 4 = some (natToBytes a 4))
    (hafit : a < 2^32)
    (htok : readBytes s.mem (pbuf + a) 1 = some [t]) :
    evalInstr calls (c12 s pidx pbuf n k sp sum a t) (.icmp "%c2" .eq 8 (.reg "%c") (.imm (.int 8 (BitVec.ofNat 8 93)))) =
      some (c13 s pidx pbuf n k sp sum a t) := by
  rw [evalInstr_icmp8 calls (c12 s pidx pbuf n k sp sum a t) "%c2" "%c"
      (BitVec.ofNat 8 t.toNat) (BitVec.ofNat 8 93) (by simp [c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, Vk, Vs, Vip, Vp32, Vp, Vcp, Vc, Vo, Vopen, Vclose, Vinc, Vdec, Vdelta, Vspn, Vsumn, Vkn, Vmore, State.bind, lookupName])]
  simp [c13, Vo]

/-- Instruction 14 of the loop body. -/
theorem step14 (calls : Calls) (s : State) (pidx pbuf : Nat) (n k : Nat)
    (sp sum : BitVec 64) (a : Nat) (t : UInt8)
    (hn : n < 2^63) (hk : k < 2^63)
    (hidx : lookupName s.env "%idx" = some (.ptr pidx))
    (hbuf : lookupName s.env "%buf" = some (.ptr pbuf))
    (hnidx : lookupName s.env "%nidx" = some (.int 64 (BitVec.ofNat 64 n)))
    (hread : readBytes s.mem (pidx + k * 4) 4 = some (natToBytes a 4))
    (hafit : a < 2^32)
    (htok : readBytes s.mem (pbuf + a) 1 = some [t]) :
    evalInstr calls (c13 s pidx pbuf n k sp sum a t) (.binop "%isclose" .or 1 (.reg "%c1") (.reg "%c2")) =
      some (c14 s pidx pbuf n k sp sum a t) := by
  rw [evalInstr_or1_reg calls (c13 s pidx pbuf n k sp sum a t) "%isclose" "%c1" "%c2"
      (BitVec.ofBool (BitVec.ofNat 8 t.toNat = BitVec.ofNat 8 125))
      (BitVec.ofBool (BitVec.ofNat 8 t.toNat = BitVec.ofNat 8 93))
      (by simp [c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, Vk, Vs, Vip, Vp32, Vp, Vcp, Vc, Vo, Vopen, Vclose, Vinc, Vdec, Vdelta, Vspn, Vsumn, Vkn, Vmore, State.bind, lookupName]) (by simp [c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, Vk, Vs, Vip, Vp32, Vp, Vcp, Vc, Vo, Vopen, Vclose, Vinc, Vdec, Vdelta, Vspn, Vsumn, Vkn, Vmore, State.bind, lookupName])]
  rw [closeBit_eq (BitVec.ofNat 8 t.toNat), ofBitVec_byte]
  simp [c14, Vclose]

/-- Instruction 15 of the loop body. -/
theorem step15 (calls : Calls) (s : State) (pidx pbuf : Nat) (n k : Nat)
    (sp sum : BitVec 64) (a : Nat) (t : UInt8)
    (hn : n < 2^63) (hk : k < 2^63)
    (hidx : lookupName s.env "%idx" = some (.ptr pidx))
    (hbuf : lookupName s.env "%buf" = some (.ptr pbuf))
    (hnidx : lookupName s.env "%nidx" = some (.int 64 (BitVec.ofNat 64 n)))
    (hread : readBytes s.mem (pidx + k * 4) 4 = some (natToBytes a 4))
    (hafit : a < 2^32)
    (htok : readBytes s.mem (pbuf + a) 1 = some [t]) :
    evalInstr calls (c14 s pidx pbuf n k sp sum a t) (.zext "%inc" 1 64 (.reg "%isopen")) =
      some (c15 s pidx pbuf n k sp sum a t) := by
  rw [evalInstr_zext1_64 calls (c14 s pidx pbuf n k sp sum a t) "%inc" "%isopen"
      (BitVec.ofBool (IsOpenB t)) (by simp [c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, Vk, Vs, Vip, Vp32, Vp, Vcp, Vc, Vo, Vopen, Vclose, Vinc, Vdec, Vdelta, Vspn, Vsumn, Vkn, Vmore, State.bind, lookupName])]
  simp [c15, Vinc, zext_bool_value, openZ]

/-- Instruction 16 of the loop body. -/
theorem step16 (calls : Calls) (s : State) (pidx pbuf : Nat) (n k : Nat)
    (sp sum : BitVec 64) (a : Nat) (t : UInt8)
    (hn : n < 2^63) (hk : k < 2^63)
    (hidx : lookupName s.env "%idx" = some (.ptr pidx))
    (hbuf : lookupName s.env "%buf" = some (.ptr pbuf))
    (hnidx : lookupName s.env "%nidx" = some (.int 64 (BitVec.ofNat 64 n)))
    (hread : readBytes s.mem (pidx + k * 4) 4 = some (natToBytes a 4))
    (hafit : a < 2^32)
    (htok : readBytes s.mem (pbuf + a) 1 = some [t]) :
    evalInstr calls (c15 s pidx pbuf n k sp sum a t) (.zext "%dec" 1 64 (.reg "%isclose")) =
      some (c16 s pidx pbuf n k sp sum a t) := by
  rw [evalInstr_zext1_64 calls (c15 s pidx pbuf n k sp sum a t) "%dec" "%isclose"
      (BitVec.ofBool (IsCloseB t)) (by simp [c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, Vk, Vs, Vip, Vp32, Vp, Vcp, Vc, Vo, Vopen, Vclose, Vinc, Vdec, Vdelta, Vspn, Vsumn, Vkn, Vmore, State.bind, lookupName])]
  simp [c16, Vdec, zext_bool_value, closeZ]

/-- Instruction 17 of the loop body. -/
theorem step17 (calls : Calls) (s : State) (pidx pbuf : Nat) (n k : Nat)
    (sp sum : BitVec 64) (a : Nat) (t : UInt8)
    (hn : n < 2^63) (hk : k < 2^63)
    (hidx : lookupName s.env "%idx" = some (.ptr pidx))
    (hbuf : lookupName s.env "%buf" = some (.ptr pbuf))
    (hnidx : lookupName s.env "%nidx" = some (.int 64 (BitVec.ofNat 64 n)))
    (hread : readBytes s.mem (pidx + k * 4) 4 = some (natToBytes a 4))
    (hafit : a < 2^32)
    (htok : readBytes s.mem (pbuf + a) 1 = some [t]) :
    evalInstr calls (c16 s pidx pbuf n k sp sum a t) (.binop "%delta" .sub 64 (.reg "%inc") (.reg "%dec")) =
      some (c17 s pidx pbuf n k sp sum a t) := by
  rw [evalInstr_sub64 calls (c16 s pidx pbuf n k sp sum a t) "%delta" "%inc" "%dec"
      (BitVec.ofInt 64 (openZ t)) (BitVec.ofInt 64 (closeZ t))
      (by simp [c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, Vk, Vs, Vip, Vp32, Vp, Vcp, Vc, Vo, Vopen, Vclose, Vinc, Vdec, Vdelta, Vspn, Vsumn, Vkn, Vmore, State.bind, lookupName]) (by simp [c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, Vk, Vs, Vip, Vp32, Vp, Vcp, Vc, Vo, Vopen, Vclose, Vinc, Vdec, Vdelta, Vspn, Vsumn, Vkn, Vmore, State.bind, lookupName])]
  simp [c17, Vdelta, ofInt_sub, deltaZ]

/-- Instruction 18 of the loop body. -/
theorem step18 (calls : Calls) (s : State) (pidx pbuf : Nat) (n k : Nat)
    (sp sum : BitVec 64) (a : Nat) (t : UInt8)
    (hn : n < 2^63) (hk : k < 2^63)
    (hidx : lookupName s.env "%idx" = some (.ptr pidx))
    (hbuf : lookupName s.env "%buf" = some (.ptr pbuf))
    (hnidx : lookupName s.env "%nidx" = some (.int 64 (BitVec.ofNat 64 n)))
    (hread : readBytes s.mem (pidx + k * 4) 4 = some (natToBytes a 4))
    (hafit : a < 2^32)
    (htok : readBytes s.mem (pbuf + a) 1 = some [t]) :
    evalInstr calls (c17 s pidx pbuf n k sp sum a t) (.binop "%spn" .add 64 (.reg "%sp") (.reg "%delta")) =
      some (c18 s pidx pbuf n k sp sum a t) := by
  rw [evalInstr_add64 calls (c17 s pidx pbuf n k sp sum a t) "%spn" "%sp" "%delta"
      sp (BitVec.ofInt 64 (deltaZ t)) (by simp [c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, c17, Vk, Vs, Vip, Vp32, Vp, Vcp, Vc, Vo, Vopen, Vclose, Vinc, Vdec, Vdelta, Vspn, Vsumn, Vkn, Vmore, State.bind, lookupName]) (by simp [c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, c17, Vk, Vs, Vip, Vp32, Vp, Vcp, Vc, Vo, Vopen, Vclose, Vinc, Vdec, Vdelta, Vspn, Vsumn, Vkn, Vmore, State.bind, lookupName])]
  simp [c18, Vspn]

/-- Instruction 19 of the loop body. -/
theorem step19 (calls : Calls) (s : State) (pidx pbuf : Nat) (n k : Nat)
    (sp sum : BitVec 64) (a : Nat) (t : UInt8)
    (hn : n < 2^63) (hk : k < 2^63)
    (hidx : lookupName s.env "%idx" = some (.ptr pidx))
    (hbuf : lookupName s.env "%buf" = some (.ptr pbuf))
    (hnidx : lookupName s.env "%nidx" = some (.int 64 (BitVec.ofNat 64 n)))
    (hread : readBytes s.mem (pidx + k * 4) 4 = some (natToBytes a 4))
    (hafit : a < 2^32)
    (htok : readBytes s.mem (pbuf + a) 1 = some [t]) :
    evalInstr calls (c18 s pidx pbuf n k sp sum a t) (.binop "%sumn" .add 64 (.reg "%sum") (.reg "%spn")) =
      some (c19 s pidx pbuf n k sp sum a t) := by
  rw [evalInstr_add64 calls (c18 s pidx pbuf n k sp sum a t) "%sumn" "%sum" "%spn"
      sum (sp + BitVec.ofInt 64 (deltaZ t)) (by simp [c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, c17, c18, Vk, Vs, Vip, Vp32, Vp, Vcp, Vc, Vo, Vopen, Vclose, Vinc, Vdec, Vdelta, Vspn, Vsumn, Vkn, Vmore, State.bind, lookupName]) (by simp [c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, c17, c18, Vk, Vs, Vip, Vp32, Vp, Vcp, Vc, Vo, Vopen, Vclose, Vinc, Vdec, Vdelta, Vspn, Vsumn, Vkn, Vmore, State.bind, lookupName])]
  simp [c19, Vsumn]

/-- Instruction 20 of the loop body. -/
theorem step20 (calls : Calls) (s : State) (pidx pbuf : Nat) (n k : Nat)
    (sp sum : BitVec 64) (a : Nat) (t : UInt8)
    (hn : n < 2^63) (hk : k < 2^63)
    (hidx : lookupName s.env "%idx" = some (.ptr pidx))
    (hbuf : lookupName s.env "%buf" = some (.ptr pbuf))
    (hnidx : lookupName s.env "%nidx" = some (.int 64 (BitVec.ofNat 64 n)))
    (hread : readBytes s.mem (pidx + k * 4) 4 = some (natToBytes a 4))
    (hafit : a < 2^32)
    (htok : readBytes s.mem (pbuf + a) 1 = some [t]) :
    evalInstr calls (c19 s pidx pbuf n k sp sum a t) (.binop "%kn" .add 64 (.reg "%k") (.imm (.int 64 (BitVec.ofNat 64 1)))) =
      some (c20 s pidx pbuf n k sp sum a t) := by
  rw [evalInstr_add64_imm calls (c19 s pidx pbuf n k sp sum a t) "%kn" "%k"
      (BitVec.ofNat 64 k) (BitVec.ofNat 64 1) (by simp [c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, c17, c18, c19, Vk, Vs, Vip, Vp32, Vp, Vcp, Vc, Vo, Vopen, Vclose, Vinc, Vdec, Vdelta, Vspn, Vsumn, Vkn, Vmore, State.bind, lookupName])]
  simp [c20, Vkn, ofNat64_succ k (by omega)]

/-- Instruction 21 of the loop body. -/
theorem step21 (calls : Calls) (s : State) (pidx pbuf : Nat) (n k : Nat)
    (sp sum : BitVec 64) (a : Nat) (t : UInt8)
    (hn : n < 2^63) (hk : k < 2^63)
    (hidx : lookupName s.env "%idx" = some (.ptr pidx))
    (hbuf : lookupName s.env "%buf" = some (.ptr pbuf))
    (hnidx : lookupName s.env "%nidx" = some (.int 64 (BitVec.ofNat 64 n)))
    (hread : readBytes s.mem (pidx + k * 4) 4 = some (natToBytes a 4))
    (hafit : a < 2^32)
    (htok : readBytes s.mem (pbuf + a) 1 = some [t]) :
    evalInstr calls (c20 s pidx pbuf n k sp sum a t) (.icmp "%more" .ult 64 (.reg "%kn") (.reg "%nidx")) =
      some (c21 s pidx pbuf n k sp sum a t) := by
  rw [evalInstr_ult64 calls (c20 s pidx pbuf n k sp sum a t) "%more" "%kn" "%nidx"
      (BitVec.ofNat 64 (k + 1)) (BitVec.ofNat 64 n)
      (by simp [c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, c17, c18, c19, c20, Vk, Vs, Vip, Vp32, Vp, Vcp, Vc, Vo, Vopen, Vclose, Vinc, Vdec, Vdelta, Vspn, Vsumn, Vkn, Vmore, State.bind, lookupName]) (by simpa [c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, c17, c18, c19, c20, State.bind, lookupName] using hnidx)]
  simp [c21, Vmore, ult_ofNat (k + 1) n (by omega) (by omega)]

/-- One execution of the loop block: the three phis take the head's values,
the body reads token `k` and the index the stream points at, and the three
outputs are the step's. -/
theorem loop_body (calls : Calls) (s : State) (pidx pbuf : Nat) (n k : Nat)
    (sp sum : BitVec 64) (a : Nat) (t : UInt8)
    (hn : n < 2^63) (hk : k < 2^63)
    (hidx : lookupName s.env "%idx" = some (.ptr pidx))
    (hbuf : lookupName s.env "%buf" = some (.ptr pbuf))
    (hnidx : lookupName s.env "%nidx" = some (.int 64 (BitVec.ofNat 64 n)))
    (hread : readBytes s.mem (pidx + k * 4) 4 = some (natToBytes a 4))
    (hafit : a < 2^32)
    (htok : readBytes s.mem (pbuf + a) 1 = some [t])
    (hphi : (s.pre = some "entry" ∧ k = 0 ∧ sp = 0 ∧ sum = 0) ∨
            (s.pre = some "loop" ∧
              lookupName s.env "%kn" = some (.int 64 (BitVec.ofNat 64 k)) ∧
              lookupName s.env "%spn" = some (.int 64 sp) ∧
              lookupName s.env "%sumn" = some (.int 64 sum))) :
    denoteCode calls loopInstrs s = some (c21 s pidx pbuf n k sp sum a t) := by
  rw [show loopInstrs = (.phi "%k" (.int 64) [("entry", .imm (.int 64 (BitVec.ofNat 64 0))), ("loop", .reg "%kn")]) :: List.drop 1 loopInstrs from rfl]
  rw [denoteCode_cons_of _ _ _ _ _ (step01 calls s pidx pbuf n k sp sum a t hn hk hidx hbuf hnidx hread hafit htok hphi)]
  rw [show List.drop 1 loopInstrs = (.phi "%sp" (.int 64) [("entry", .imm (.int 64 (BitVec.ofNat 64 0))), ("loop", .reg "%spn")]) :: List.drop 2 loopInstrs from rfl]
  rw [denoteCode_cons_of _ _ _ _ _ (step02 calls s pidx pbuf n k sp sum a t hn hk hidx hbuf hnidx hread hafit htok hphi)]
  rw [show List.drop 2 loopInstrs = (.phi "%sum" (.int 64) [("entry", .imm (.int 64 (BitVec.ofNat 64 0))), ("loop", .reg "%sumn")]) :: List.drop 3 loopInstrs from rfl]
  rw [denoteCode_cons_of _ _ _ _ _ (step03 calls s pidx pbuf n k sp sum a t hn hk hidx hbuf hnidx hread hafit htok hphi)]
  rw [show List.drop 3 loopInstrs = (.gep "%ip" (.int 32) (.reg "%idx") (.reg "%k")) :: List.drop 4 loopInstrs from rfl]
  rw [denoteCode_cons_of _ _ _ _ _ (step04 calls s pidx pbuf n k sp sum a t hn hk hidx hbuf hnidx hread hafit htok)]
  rw [show List.drop 4 loopInstrs = (.load "%p32" (.int 32) (.reg "%ip")) :: List.drop 5 loopInstrs from rfl]
  rw [denoteCode_cons_of _ _ _ _ _ (step05 calls s pidx pbuf n k sp sum a t hn hk hidx hbuf hnidx hread hafit htok)]
  rw [show List.drop 5 loopInstrs = (.zext "%p" 32 64 (.reg "%p32")) :: List.drop 6 loopInstrs from rfl]
  rw [denoteCode_cons_of _ _ _ _ _ (step06 calls s pidx pbuf n k sp sum a t hn hk hidx hbuf hnidx hread hafit htok)]
  rw [show List.drop 6 loopInstrs = (.gep "%cp" (.int 8) (.reg "%buf") (.reg "%p")) :: List.drop 7 loopInstrs from rfl]
  rw [denoteCode_cons_of _ _ _ _ _ (step07 calls s pidx pbuf n k sp sum a t hn hk hidx hbuf hnidx hread hafit htok)]
  rw [show List.drop 7 loopInstrs = (.load "%c" (.int 8) (.reg "%cp")) :: List.drop 8 loopInstrs from rfl]
  rw [denoteCode_cons_of _ _ _ _ _ (step08 calls s pidx pbuf n k sp sum a t hn hk hidx hbuf hnidx hread hafit htok)]
  rw [show List.drop 8 loopInstrs = (.icmp "%o1" .eq 8 (.reg "%c") (.imm (.int 8 (BitVec.ofNat 8 123)))) :: List.drop 9 loopInstrs from rfl]
  rw [denoteCode_cons_of _ _ _ _ _ (step09 calls s pidx pbuf n k sp sum a t hn hk hidx hbuf hnidx hread hafit htok)]
  rw [show List.drop 9 loopInstrs = (.icmp "%o2" .eq 8 (.reg "%c") (.imm (.int 8 (BitVec.ofNat 8 91)))) :: List.drop 10 loopInstrs from rfl]
  rw [denoteCode_cons_of _ _ _ _ _ (step10 calls s pidx pbuf n k sp sum a t hn hk hidx hbuf hnidx hread hafit htok)]
  rw [show List.drop 10 loopInstrs = (.binop "%isopen" .or 1 (.reg "%o1") (.reg "%o2")) :: List.drop 11 loopInstrs from rfl]
  rw [denoteCode_cons_of _ _ _ _ _ (step11 calls s pidx pbuf n k sp sum a t hn hk hidx hbuf hnidx hread hafit htok)]
  rw [show List.drop 11 loopInstrs = (.icmp "%c1" .eq 8 (.reg "%c") (.imm (.int 8 (BitVec.ofNat 8 125)))) :: List.drop 12 loopInstrs from rfl]
  rw [denoteCode_cons_of _ _ _ _ _ (step12 calls s pidx pbuf n k sp sum a t hn hk hidx hbuf hnidx hread hafit htok)]
  rw [show List.drop 12 loopInstrs = (.icmp "%c2" .eq 8 (.reg "%c") (.imm (.int 8 (BitVec.ofNat 8 93)))) :: List.drop 13 loopInstrs from rfl]
  rw [denoteCode_cons_of _ _ _ _ _ (step13 calls s pidx pbuf n k sp sum a t hn hk hidx hbuf hnidx hread hafit htok)]
  rw [show List.drop 13 loopInstrs = (.binop "%isclose" .or 1 (.reg "%c1") (.reg "%c2")) :: List.drop 14 loopInstrs from rfl]
  rw [denoteCode_cons_of _ _ _ _ _ (step14 calls s pidx pbuf n k sp sum a t hn hk hidx hbuf hnidx hread hafit htok)]
  rw [show List.drop 14 loopInstrs = (.zext "%inc" 1 64 (.reg "%isopen")) :: List.drop 15 loopInstrs from rfl]
  rw [denoteCode_cons_of _ _ _ _ _ (step15 calls s pidx pbuf n k sp sum a t hn hk hidx hbuf hnidx hread hafit htok)]
  rw [show List.drop 15 loopInstrs = (.zext "%dec" 1 64 (.reg "%isclose")) :: List.drop 16 loopInstrs from rfl]
  rw [denoteCode_cons_of _ _ _ _ _ (step16 calls s pidx pbuf n k sp sum a t hn hk hidx hbuf hnidx hread hafit htok)]
  rw [show List.drop 16 loopInstrs = (.binop "%delta" .sub 64 (.reg "%inc") (.reg "%dec")) :: List.drop 17 loopInstrs from rfl]
  rw [denoteCode_cons_of _ _ _ _ _ (step17 calls s pidx pbuf n k sp sum a t hn hk hidx hbuf hnidx hread hafit htok)]
  rw [show List.drop 17 loopInstrs = (.binop "%spn" .add 64 (.reg "%sp") (.reg "%delta")) :: List.drop 18 loopInstrs from rfl]
  rw [denoteCode_cons_of _ _ _ _ _ (step18 calls s pidx pbuf n k sp sum a t hn hk hidx hbuf hnidx hread hafit htok)]
  rw [show List.drop 18 loopInstrs = (.binop "%sumn" .add 64 (.reg "%sum") (.reg "%spn")) :: List.drop 19 loopInstrs from rfl]
  rw [denoteCode_cons_of _ _ _ _ _ (step19 calls s pidx pbuf n k sp sum a t hn hk hidx hbuf hnidx hread hafit htok)]
  rw [show List.drop 19 loopInstrs = (.binop "%kn" .add 64 (.reg "%k") (.imm (.int 64 (BitVec.ofNat 64 1)))) :: List.drop 20 loopInstrs from rfl]
  rw [denoteCode_cons_of _ _ _ _ _ (step20 calls s pidx pbuf n k sp sum a t hn hk hidx hbuf hnidx hread hafit htok)]
  rw [show List.drop 20 loopInstrs = (.icmp "%more" .ult 64 (.reg "%kn") (.reg "%nidx")) :: List.drop 21 loopInstrs from rfl]
  rw [denoteCode_cons_of _ _ _ _ _ (step21 calls s pidx pbuf n k sp sum a t hn hk hidx hbuf hnidx hread hafit htok)]
  rfl


/-! ## The initial state and the statistics memory -/

/-- The state the kernel starts from: the parser's own parameter list, bound by
`initState`, with the caller's memory supplied. -/
def start (m0 : Mem) (pbuf pidx pstats : Nat) (n : BitVec 64) : State :=
  { initState depthFunction [.ptr pbuf, .ptr pidx, .int 64 n, .ptr pstats] with mem := m0 }

/-- The memory the exit path leaves: the two statistics words, written in the
order the block writes them. -/
def statsMem (m0 : Mem) (pstats : Nat) (sp su : BitVec 64) : Mem :=
  writeBytes (writeBytes m0 pstats (natToBytes sp.toNat 8)) (pstats + 8)
    (natToBytes su.toNat 8)

theorem start_buf (m0 : Mem) (pbuf pidx pstats : Nat) (n : BitVec 64) :
    lookupName (start m0 pbuf pidx pstats n).env "%buf" = some (.ptr pbuf) := by
  simp [start, initState, depthFunction, List.zip, List.map, List.zipWith, lookupName]

theorem start_idx (m0 : Mem) (pbuf pidx pstats : Nat) (n : BitVec 64) :
    lookupName (start m0 pbuf pidx pstats n).env "%idx" = some (.ptr pidx) := by
  simp [start, initState, depthFunction, List.zip, List.map, List.zipWith, lookupName]

theorem start_nidx (m0 : Mem) (pbuf pidx pstats : Nat) (n : BitVec 64) :
    lookupName (start m0 pbuf pidx pstats n).env "%nidx" = some (.int 64 n) := by
  simp [start, initState, depthFunction, List.zip, List.map, List.zipWith, lookupName]

theorem start_stats (m0 : Mem) (pbuf pidx pstats : Nat) (n : BitVec 64) :
    lookupName (start m0 pbuf pidx pstats n).env "%stats" = some (.ptr pstats) := by
  simp [start, initState, depthFunction, List.zip, List.map, List.zipWith, lookupName]

theorem start_pc (m0 : Mem) (pbuf pidx pstats : Nat) (n : BitVec 64) :
    (start m0 pbuf pidx pstats n).pc = "entry" := by
  simp [start, initState, depthFunction, Function.entry?]

theorem start_pre (m0 : Mem) (pbuf pidx pstats : Nat) (n : BitVec 64) :
    (start m0 pbuf pidx pstats n).pre = none := rfl

theorem start_mem (m0 : Mem) (pbuf pidx pstats : Nat) (n : BitVec 64) :
    (start m0 pbuf pidx pstats n).mem = m0 := rfl

/-! ## Block lookup and the terminators -/

theorem findBlock_entry :
    depthFunction.findBlock "entry" = some ⟨"entry", entryInstrs, entryTerm⟩ := by
  simp [depthFunction, Function.findBlock, findBlockList]

theorem findBlock_loop :
    depthFunction.findBlock "loop" = some ⟨"loop", loopInstrs, loopTerm⟩ := by
  simp [depthFunction, Function.findBlock, findBlockList]

theorem findBlock_exit :
    depthFunction.findBlock "exit" = some ⟨"exit", exitInstrs, exitTerm⟩ := by
  simp [depthFunction, Function.findBlock, findBlockList]

theorem findBlock_exit0 :
    depthFunction.findBlock "exit0" = some ⟨"exit0", exit0Instrs, exit0Term⟩ := by
  simp [depthFunction, Function.findBlock, findBlockList]

theorem execTerm_condbr_true {s : State} {c : Operand} {bit : BitVec 1}
    {t f : String} (h : evalOperand s c = some (.int 1 bit))
    (hb : bit = 1) :
    execTerm s (.condbr c t f) = .jump { s with pc := t, pre := some s.pc } := by
  simp [execTerm, h, hb]

theorem execTerm_condbr_false {s : State} {c : Operand} {bit : BitVec 1}
    {t f : String} (h : evalOperand s c = some (.int 1 bit))
    (hb : bit = 0) :
    execTerm s (.condbr c t f) = .jump { s with pc := f, pre := some s.pc } := by
  simp [execTerm, h, hb]

theorem execTerm_ret_int64 {s : State} {v : Operand} {x : Value}
    (h : evalOperand s v = some x) :
    execTerm s (.ret (.int 64) (some v)) = .ret (some x) s := by
  simp [execTerm, h]

/-! ## The entry block -/

/-- The value `%nz` takes. -/
def Ve (n : Nat) : Value :=
  .int 1 (BitVec.ofBool (BitVec.ofNat 64 n = BitVec.ofNat 64 0))

def e1 (s : State) (n : Nat) : State := s.bind "%nz" (Ve n)

theorem evalInstr_icmp64_eq (calls : Calls) (s : State) (d r : String)
    (a b : BitVec 64) (h : lookupName s.env r = some (.int 64 a)) :
    evalInstr calls s (.icmp d .eq 64 (.reg r) (.imm (.int 64 b))) =
      some (s.bind d (.int 1 (BitVec.ofBool (a = b)))) := by
  simp [evalInstr, evalOperand, Const.toValue, h, Value.intToNat, evalICmpNat, evalICmp]

theorem entry_body (calls : Calls) (s : State) (n : Nat)
    (hnidx : lookupName s.env "%nidx" = some (.int 64 (BitVec.ofNat 64 n))) :
    denoteCode calls entryInstrs s = some (e1 s n) := by
  rw [show entryInstrs =
    [.icmp "%nz" .eq 64 (.reg "%nidx") (.imm (.int 64 (BitVec.ofNat 64 0)))] from rfl]
  simp [denoteCode, evalInstr_icmp64_eq calls s "%nz" "%nidx"
    (BitVec.ofNat 64 n) (BitVec.ofNat 64 0) hnidx, e1, Ve]

/-- `%nz` is one at `n = 0`. -/
theorem Ve_zero : Ve 0 = .int 1 (1 : BitVec 1) := by
  simp [Ve]

/-- `%nz` is zero at a nonzero `n` below the wrap. -/
theorem Ve_ne_zero {n : Nat} (h0 : n ≠ 0) (hn : n < 2^64) :
    Ve n = .int 1 (0 : BitVec 1) := by
  have hne : BitVec.ofNat 64 n ≠ BitVec.ofNat 64 0 := by
    intro h
    have h1 : (BitVec.ofNat 64 n).toNat = (BitVec.ofNat 64 0).toNat := by rw [h]
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn] at h1
    simp at h1
    exact h0 h1
  simp [Ve, hne]

/-- The value `%nz` reads is the one `Ve` names. -/
theorem e1_nz (s : State) (n : Nat) :
    lookupName (e1 s n).env "%nz" = some (Ve n) := by
  simp [e1, State.bind, lookupName]

/-! ## The exit path when `nidx` is zero -/

def x0a (s : State) (pstats : Nat) : State :=
  { s with mem := writeBytes s.mem pstats (natToBytes (BitVec.ofNat 64 0).toNat 8) }

def x0b (s : State) (pstats : Nat) : State :=
  (x0a s pstats).bind "%statsz" (.ptr (pstats + 8))

def x0c (s : State) (pstats : Nat) : State :=
  { x0b s pstats with
    mem := writeBytes (x0b s pstats).mem (pstats + 8)
      (natToBytes (BitVec.ofNat 64 0).toNat 8) }

def x0d (s : State) (pstats : Nat) : State := (x0c s pstats)

theorem evalInstr_store64_imm (calls : Calls) (s : State) (p : String)
    (x : BitVec 64) (addr : Nat)
    (hp : lookupName s.env p = some (.ptr addr)) :
    evalInstr calls s (.store (.int 64) (.imm (.int 64 x)) (.reg p)) =
      some { s with mem := writeBytes s.mem addr (natToBytes x.toNat 8) } := by
  simp [evalInstr, evalOperand, Const.toValue, hp, storeValue]

theorem step0a (calls : Calls) (s : State) (pstats : Nat)
    (hstats : lookupName s.env "%stats" = some (.ptr pstats)) :
    evalInstr calls s (.store (.int 64) (.imm (.int 64 (BitVec.ofNat 64 0))) (.reg "%stats")) =
      some (x0a s pstats) := by
  exact evalInstr_store64_imm calls s "%stats" (BitVec.ofNat 64 0) pstats hstats

theorem step0b (calls : Calls) (s : State) (pstats : Nat)
    (hstats : lookupName s.env "%stats" = some (.ptr pstats)) :
    evalInstr calls (x0a s pstats)
      (.gep "%statsz" (.int 64) (.reg "%stats") (.imm (.int 64 (BitVec.ofNat 64 1)))) =
      some (x0b s pstats) := by
  rw [evalInstr_gep64_imm calls (x0a s pstats) "%statsz" "%stats" pstats
    (BitVec.ofNat 64 1) (by simpa [x0a] using hstats)
    (by rw [BitVec.toNat_ofNat]; decide)]
  simp [x0b, x0a]

theorem step0c (calls : Calls) (s : State) (pstats : Nat) :
    evalInstr calls (x0b s pstats)
      (.store (.int 64) (.imm (.int 64 (BitVec.ofNat 64 0))) (.reg "%statsz")) =
      some (x0c s pstats) := by
  exact evalInstr_store64_imm calls (x0b s pstats) "%statsz"
    (BitVec.ofNat 64 0) (pstats + 8) (by simp [x0b, State.bind, lookupName])

theorem exit0_body (calls : Calls) (s : State) (pstats : Nat)
    (hstats : lookupName s.env "%stats" = some (.ptr pstats)) :
    denoteCode calls exit0Instrs s = some (x0c s pstats) := by
  rw [show exit0Instrs =
    [.store (.int 64) (.imm (.int 64 (BitVec.ofNat 64 0))) (.reg "%stats"),
     .gep "%statsz" (.int 64) (.reg "%stats") (.imm (.int 64 (BitVec.ofNat 64 1))),
     .store (.int 64) (.imm (.int 64 (BitVec.ofNat 64 0))) (.reg "%statsz")] from rfl]
  rw [denoteCode_cons_of _ _ _ _ _ (step0a calls s pstats hstats)]
  rw [denoteCode_cons_of _ _ _ _ _ (step0b calls s pstats hstats)]
  rw [denoteCode_cons_of _ _ _ _ _ (step0c calls s pstats)]
  rfl

theorem exit0_term (s : State) (pstats : Nat) :
    execTerm (x0c s pstats) exit0Term =
      .ret (some (.int 64 (BitVec.ofNat 64 0))) (x0c s pstats) := by
  rw [show exit0Term = .ret (.int 64) (some (.imm (.int 64 (BitVec.ofNat 64 0)))) from rfl]
  exact execTerm_ret_int64 (by simp [evalOperand, Const.toValue])

/-! ## Running one block -/

theorem step_of (calls : Calls) (s : State) (name : String) (b : Block) (s' : State)
    (hpc : s.pc = name) (hfind : depthFunction.findBlock name = some b)
    (hbody : denoteCode calls b.instrs s = some s') :
    step calls depthFunction s = execTerm s' b.term := by
  simp [step, hpc, hfind, hbody]

theorem runFuel_jump {calls : Calls} {s s' : State} {n : Nat}
    (h : step calls depthFunction s = .jump s') :
    runFuel calls (n + 1) depthFunction s = runFuel calls n depthFunction s' := by
  simp [runFuel, h]

theorem runFuel_ret {calls : Calls} {s s' : State} {v : Option Value} {n : Nat}
    (h : step calls depthFunction s = .ret v s') :
    runFuel calls (n + 1) depthFunction s = some (.ret v s'.mem) := by
  simp [runFuel, h]

/-! ## The exit block -/

def xea (s : State) (pstats : Nat) (spn : BitVec 64) : State :=
  { s with mem := writeBytes s.mem pstats (natToBytes spn.toNat 8) }

def xeb (s : State) (pstats : Nat) (spn : BitVec 64) : State :=
  (xea s pstats spn).bind "%stats1" (.ptr (pstats + 8))

def xec (s : State) (pstats : Nat) (spn sun : BitVec 64) : State :=
  { xeb s pstats spn with
    mem := writeBytes (xeb s pstats spn).mem (pstats + 8) (natToBytes sun.toNat 8) }

theorem step_ea (calls : Calls) (s : State) (pstats : Nat) (spn : BitVec 64)
    (hstats : lookupName s.env "%stats" = some (.ptr pstats))
    (hspn : lookupName s.env "%spn" = some (.int 64 spn)) :
    evalInstr calls s (.store (.int 64) (.reg "%spn") (.reg "%stats")) =
      some (xea s pstats spn) :=
  evalInstr_store64 calls s "%spn" "%stats" spn pstats hspn hstats

theorem step_eb (calls : Calls) (s : State) (pstats : Nat) (spn : BitVec 64)
    (hstats : lookupName s.env "%stats" = some (.ptr pstats)) :
    evalInstr calls (xea s pstats spn)
      (.gep "%stats1" (.int 64) (.reg "%stats") (.imm (.int 64 (BitVec.ofNat 64 1)))) =
      some (xeb s pstats spn) := by
  rw [evalInstr_gep64_imm calls (xea s pstats spn) "%stats1" "%stats" pstats
    (BitVec.ofNat 64 1) (by simpa [xea] using hstats)
    (by rw [BitVec.toNat_ofNat]; decide)]
  simp [xeb, xea]

theorem step_ec (calls : Calls) (s : State) (pstats : Nat) (spn sun : BitVec 64)
    (hsumn : lookupName s.env "%sumn" = some (.int 64 sun)) :
    evalInstr calls (xeb s pstats spn) (.store (.int 64) (.reg "%sumn") (.reg "%stats1")) =
      some (xec s pstats spn sun) :=
  evalInstr_store64 calls (xeb s pstats spn) "%sumn" "%stats1" sun (pstats + 8)
    (by simpa [xeb, xea, State.bind, lookupName] using hsumn) (by simp [xeb, State.bind, lookupName])

theorem exit_body (calls : Calls) (s : State) (pstats : Nat) (spn sun : BitVec 64)
    (hstats : lookupName s.env "%stats" = some (.ptr pstats))
    (hspn : lookupName s.env "%spn" = some (.int 64 spn))
    (hsumn : lookupName s.env "%sumn" = some (.int 64 sun)) :
    denoteCode calls exitInstrs s = some (xec s pstats spn sun) := by
  rw [show exitInstrs =
    [.store (.int 64) (.reg "%spn") (.reg "%stats"),
     .gep "%stats1" (.int 64) (.reg "%stats") (.imm (.int 64 (BitVec.ofNat 64 1))),
     .store (.int 64) (.reg "%sumn") (.reg "%stats1")] from rfl]
  rw [denoteCode_cons_of _ _ _ _ _ (step_ea calls s pstats spn hstats hspn)]
  rw [denoteCode_cons_of _ _ _ _ _ (step_eb calls s pstats spn hstats)]
  rw [denoteCode_cons_of _ _ _ _ _ (step_ec calls s pstats spn sun hsumn)]
  rfl

theorem exit_term (s : State) (pstats : Nat) (spn sun : BitVec 64)
    (hspn : lookupName s.env "%spn" = some (.int 64 spn)) :
    execTerm (xec s pstats spn sun) exitTerm =
      .ret (some (.int 64 spn)) (xec s pstats spn sun) := by
  rw [show exitTerm = .ret (.int 64) (some (.reg "%spn")) from rfl]
  exact execTerm_ret_int64 (by simp [evalOperand, xec, xeb, xea, State.bind, lookupName, hspn])

theorem xec_mem (s : State) (pstats : Nat) (spn sun : BitVec 64) :
    (xec s pstats spn sun).mem =
      writeBytes (writeBytes s.mem pstats (natToBytes spn.toNat 8)) (pstats + 8)
        (natToBytes sun.toNat 8) := by
  simp [xec, xeb, xea, State.bind]

/-! ## The loop head invariant -/

def LoopHead (m0 : Mem) (pidx pbuf pstats : Nat) (n : Nat) (tokens : List UInt8)
    (s : State) (k : Nat) (sp sum : BitVec 64) : Prop :=
  lookupName s.env "%stats" = some (.ptr pstats) ∧
  lookupName s.env "%idx" = some (.ptr pidx) ∧
  lookupName s.env "%buf" = some (.ptr pbuf) ∧
  lookupName s.env "%nidx" = some (.int 64 (BitVec.ofNat 64 n)) ∧
  s.mem = m0 ∧ s.pc = "loop" ∧
  ((s.pre = some "entry" ∧ k = 0 ∧ sp = 0 ∧ sum = 0) ∨
   (s.pre = some "loop" ∧
      lookupName s.env "%kn" = some (.int 64 (BitVec.ofNat 64 k)) ∧
      lookupName s.env "%spn" = some (.int 64 sp) ∧
      lookupName s.env "%sumn" = some (.int 64 sum))) ∧
  sp = BitVec.ofInt 64 (depthSpec (tokens.take k)).1 ∧
  sum = BitVec.ofInt 64 (depthSpec (tokens.take k)).2

theorem depthSpec_nil_snd : (depthSpec ([] : List UInt8)).2 = 0 := rfl

theorem loopHead_zero (m0 : Mem) (pidx pbuf pstats : Nat) (n : Nat) (tokens : List UInt8)
    (s : State)
    (hstats : lookupName s.env "%stats" = some (.ptr pstats))
    (hidx : lookupName s.env "%idx" = some (.ptr pidx))
    (hbuf : lookupName s.env "%buf" = some (.ptr pbuf))
    (hnidx : lookupName s.env "%nidx" = some (.int 64 (BitVec.ofNat 64 n)))
    (hmem : s.mem = m0) (hpc : s.pc = "loop") (hpre : s.pre = some "entry") :
    LoopHead m0 pidx pbuf pstats n tokens s 0 0 0 := by
  refine ⟨hstats, hidx, hbuf, hnidx, hmem, hpc, Or.inl ⟨hpre, rfl, rfl, rfl⟩, ?_, ?_⟩ <;>
    simp [depthSpec]

/-! ## What the body leaves behind -/

theorem c21_idx (s : State) (pidx pbuf n k : Nat) (sp sum : BitVec 64)
    (a : Nat) (t : UInt8) :
    lookupName (c21 s pidx pbuf n k sp sum a t).env "%idx" = lookupName s.env "%idx" := by
  simp [c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, c17, c18, c19, c20, c21, State.bind, lookupName]

theorem c21_buf (s : State) (pidx pbuf n k : Nat) (sp sum : BitVec 64)
    (a : Nat) (t : UInt8) :
    lookupName (c21 s pidx pbuf n k sp sum a t).env "%buf" = lookupName s.env "%buf" := by
  simp [c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, c17, c18, c19, c20, c21, State.bind, lookupName]

theorem c21_nidx (s : State) (pidx pbuf n k : Nat) (sp sum : BitVec 64)
    (a : Nat) (t : UInt8) :
    lookupName (c21 s pidx pbuf n k sp sum a t).env "%nidx" = lookupName s.env "%nidx" := by
  simp [c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, c17, c18, c19, c20, c21, State.bind, lookupName]

theorem c21_kn (s : State) (pidx pbuf n k : Nat) (sp sum : BitVec 64)
    (a : Nat) (t : UInt8) :
    lookupName (c21 s pidx pbuf n k sp sum a t).env "%kn" = some (Vkn k) := by
  simp [c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, c17, c18, c19, c20, c21, State.bind, lookupName]

theorem c21_spn (s : State) (pidx pbuf n k : Nat) (sp sum : BitVec 64)
    (a : Nat) (t : UInt8) :
    lookupName (c21 s pidx pbuf n k sp sum a t).env "%spn" = some (Vspn sp t) := by
  simp [c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, c17, c18, c19, c20, c21, State.bind, lookupName]

theorem c21_sumn (s : State) (pidx pbuf n k : Nat) (sp sum : BitVec 64)
    (a : Nat) (t : UInt8) :
    lookupName (c21 s pidx pbuf n k sp sum a t).env "%sumn" = some (Vsumn sum sp t) := by
  simp [c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, c17, c18, c19, c20, c21, State.bind, lookupName]

theorem c21_more (s : State) (pidx pbuf n k : Nat) (sp sum : BitVec 64)
    (a : Nat) (t : UInt8) :
    lookupName (c21 s pidx pbuf n k sp sum a t).env "%more" = some (Vmore n k) := by
  simp [c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, c17, c18, c19, c20, c21, State.bind, lookupName]

theorem c21_mem (s : State) (pidx pbuf n k : Nat) (sp sum : BitVec 64)
    (a : Nat) (t : UInt8) :
    (c21 s pidx pbuf n k sp sum a t).mem = s.mem := rfl

theorem c21_pc (s : State) (pidx pbuf n k : Nat) (sp sum : BitVec 64)
    (a : Nat) (t : UInt8) :
    (c21 s pidx pbuf n k sp sum a t).pc = s.pc := rfl

theorem c21_pre (s : State) (pidx pbuf n k : Nat) (sp sum : BitVec 64)
    (a : Nat) (t : UInt8) :
    (c21 s pidx pbuf n k sp sum a t).pre = s.pre := rfl

/-! ## One loop iteration's control transfer -/

theorem loop_step_loop (calls : Calls) (s : State) (pidx pbuf : Nat) (n k : Nat)
    (sp sum : BitVec 64) (a : Nat) (t : UInt8)
    (hn : n < 2^63) (hk : k < 2^63)
    (hidx : lookupName s.env "%idx" = some (.ptr pidx))
    (hbuf : lookupName s.env "%buf" = some (.ptr pbuf))
    (hnidx : lookupName s.env "%nidx" = some (.int 64 (BitVec.ofNat 64 n)))
    (hread : readBytes s.mem (pidx + k * 4) 4 = some (natToBytes a 4))
    (hafit : a < 2^32)
    (htok : readBytes s.mem (pbuf + a) 1 = some [t])
    (hphi : (s.pre = some "entry" ∧ k = 0 ∧ sp = 0 ∧ sum = 0) ∨
            (s.pre = some "loop" ∧
              lookupName s.env "%kn" = some (.int 64 (BitVec.ofNat 64 k)) ∧
              lookupName s.env "%spn" = some (.int 64 sp) ∧
              lookupName s.env "%sumn" = some (.int 64 sum)))
    (hpc : s.pc = "loop") (hlt : k + 1 < n) :
    step calls depthFunction s =
      .jump { c21 s pidx pbuf n k sp sum a t with pc := "loop", pre := some "loop" } := by
  have hb := loop_body calls s pidx pbuf n k sp sum a t hn hk hidx hbuf hnidx hread hafit htok hphi
  rw [step_of calls s "loop" ⟨"loop", loopInstrs, loopTerm⟩
    (c21 s pidx pbuf n k sp sum a t) hpc findBlock_loop hb]
  rw [show loopTerm = .condbr (.reg "%more") "loop" "exit" from rfl]
  have hop : evalOperand (c21 s pidx pbuf n k sp sum a t) (.reg "%more") =
      some (.int 1 (1 : BitVec 1)) := by
    show (some (Value.int 1 (BitVec.ofBool (decide (k + 1 < n)))) : Option Value) =
      some (Value.int 1 (1 : BitVec 1))
    rw [show decide (k + 1 < n) = true from decide_eq_true hlt]; rfl
  have hpc' : (c21 s pidx pbuf n k sp sum a t).pc = "loop" := by rw [c21_pc]; exact hpc
  rw [execTerm_condbr_true (t := "loop") (f := "exit") hop rfl]
  simp [hpc']

theorem loop_step_exit (calls : Calls) (s : State) (pidx pbuf : Nat) (n k : Nat)
    (sp sum : BitVec 64) (a : Nat) (t : UInt8)
    (hn : n < 2^63) (hk : k < 2^63)
    (hidx : lookupName s.env "%idx" = some (.ptr pidx))
    (hbuf : lookupName s.env "%buf" = some (.ptr pbuf))
    (hnidx : lookupName s.env "%nidx" = some (.int 64 (BitVec.ofNat 64 n)))
    (hread : readBytes s.mem (pidx + k * 4) 4 = some (natToBytes a 4))
    (hafit : a < 2^32)
    (htok : readBytes s.mem (pbuf + a) 1 = some [t])
    (hphi : (s.pre = some "entry" ∧ k = 0 ∧ sp = 0 ∧ sum = 0) ∨
            (s.pre = some "loop" ∧
              lookupName s.env "%kn" = some (.int 64 (BitVec.ofNat 64 k)) ∧
              lookupName s.env "%spn" = some (.int 64 sp) ∧
              lookupName s.env "%sumn" = some (.int 64 sum)))
    (hpc : s.pc = "loop") (hlt : ¬ k + 1 < n) :
    step calls depthFunction s =
      .jump { c21 s pidx pbuf n k sp sum a t with pc := "exit", pre := some "loop" } := by
  have hb := loop_body calls s pidx pbuf n k sp sum a t hn hk hidx hbuf hnidx hread hafit htok hphi
  rw [step_of calls s "loop" ⟨"loop", loopInstrs, loopTerm⟩
    (c21 s pidx pbuf n k sp sum a t) hpc findBlock_loop hb]
  rw [show loopTerm = .condbr (.reg "%more") "loop" "exit" from rfl]
  have hop : evalOperand (c21 s pidx pbuf n k sp sum a t) (.reg "%more") =
      some (.int 1 (0 : BitVec 1)) := by
    show (some (Value.int 1 (BitVec.ofBool (decide (k + 1 < n)))) : Option Value) =
      some (Value.int 1 (0 : BitVec 1))
    rw [show decide (k + 1 < n) = false from decide_eq_false hlt]; rfl
  have hpc' : (c21 s pidx pbuf n k sp sum a t).pc = "loop" := by rw [c21_pc]; exact hpc
  rw [execTerm_condbr_false (t := "loop") (f := "exit") hop rfl]
  simp [hpc']

/-- The outcome the kernel produces: the depth fold's two values, stored in the
statistics words and the first of them returned. -/
def Result (calls : Calls) (m0 : Mem) (pstats : Nat) (tokens : List UInt8) : Option Outcome :=
  some (.ret (some (.int 64 (BitVec.ofInt 64 (depthSpec tokens).1)))
    (statsMem m0 pstats (BitVec.ofInt 64 (depthSpec tokens).1)
      (BitVec.ofInt 64 (depthSpec tokens).2)))

theorem c21_stats (s : State) (pidx pbuf n k : Nat) (sp sum : BitVec 64)
    (a : Nat) (t : UInt8) :
    lookupName (c21 s pidx pbuf n k sp sum a t).env "%stats" = lookupName s.env "%stats" := by
  simp [c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, c17, c18,
    c19, c20, c21, State.bind, lookupName]

/-! ## The loop, by induction on the remaining count -/

theorem loop_run (calls : Calls) (pstats pidx pbuf : Nat) (m0 : Mem)
    (tokens : List UInt8) (idxs : Nat → Nat) (n : Nat)
    (hn : n < 2^63) (hlen : tokens.length = n)
    (hidx : ∀ (k : Nat), k < n → readBytes m0 (pidx + k * 4) 4 = some (natToBytes (idxs k) 4))
    (hfit : ∀ (k : Nat), k < n → idxs k < 2^32)
    (hbuf : ∀ (k : Nat) (hk : k < n),
      readBytes m0 (pbuf + idxs k) 1 = some [tokens.get ⟨k, by rw [hlen]; exact hk⟩]) :
    ∀ (k : Nat) (hk : k < n) (sp sum : BitVec 64) (s : State),
      LoopHead m0 pidx pbuf pstats n tokens s k sp sum →
      runFuel calls (n - k + 1) depthFunction s = Result calls m0 pstats tokens := by
  have aux : ∀ m, ∀ (k : Nat) (sp sum : BitVec 64) (s : State),
      n - k = m → k < n → LoopHead m0 pidx pbuf pstats n tokens s k sp sum →
      runFuel calls (m + 1) depthFunction s = Result calls m0 pstats tokens := by
    intro m
    induction m with
    | zero =>
        intro k sp sum s heq hk hinv
        omega
    | succ m ih =>
        intro k sp sum s heq hk hinv
        obtain ⟨hstatsS, hidxS, hbufS, hnikdS, hmemS, hpcS, hphiS, hspS, hsuS⟩ := hinv
        have hk63 : k < 2^63 := by omega
        have hread : readBytes s.mem (pidx + k * 4) 4 = some (natToBytes (idxs k) 4) := by
          rw [hmemS]; exact hidx k hk
        have htok : readBytes s.mem (pbuf + idxs k) 1 =
            some [tokens.get ⟨k, by omega⟩] := by
          rw [hmemS]; exact hbuf k hk
        have hspec : depthSpec (tokens.take (k + 1)) =
            stepZ (depthSpec (tokens.take k)) (tokens.get ⟨k, by omega⟩) := by
          rw [take_succ' tokens k (by rw [hlen]; omega), depthSpec_append]
        have hspn : sp + BitVec.ofInt 64 (deltaZ (tokens.get ⟨k, by omega⟩)) =
            BitVec.ofInt 64 (depthSpec (tokens.take (k + 1))).1 := by
          rw [hspec]; simp only [stepZ]; rw [hspS]
          exact (BitVec.ofInt_add _ _).symm
        have hsumn : sum + (sp + BitVec.ofInt 64 (deltaZ (tokens.get ⟨k, by omega⟩))) =
            BitVec.ofInt 64 (depthSpec (tokens.take (k + 1))).2 := by
          rw [hspec]; simp only [stepZ]; rw [hsuS, hspS]
          rw [← BitVec.ofInt_add, ← BitVec.ofInt_add]
        by_cases hlt : k + 1 < n
        · have hstep := loop_step_loop calls s pidx pbuf n k sp sum (idxs k)
            (tokens.get ⟨k, by omega⟩) hn hk63 hidxS hbufS hnikdS hread (hfit k hk) htok
            hphiS hpcS hlt
          rw [runFuel_jump hstep]
          refine ih (k + 1)
            (sp + BitVec.ofInt 64 (deltaZ (tokens.get ⟨k, by omega⟩)))
            (sum + (sp + BitVec.ofInt 64 (deltaZ (tokens.get ⟨k, by omega⟩))))
            _ (by omega) (by omega) ?_
          refine ⟨?_, ?_, ?_, ?_, ?_, ?_, Or.inr ⟨rfl, ?_, ?_, ?_⟩, ?_, ?_⟩
          · show lookupName (c21 s pidx pbuf n k sp sum (idxs k) (tokens.get ⟨k, by omega⟩)).env
              "%stats" = some (.ptr pstats)
            rw [c21_stats]; exact hstatsS
          · show lookupName (c21 s pidx pbuf n k sp sum (idxs k) (tokens.get ⟨k, by omega⟩)).env
              "%idx" = some (.ptr pidx)
            rw [c21_idx]; exact hidxS
          · show lookupName (c21 s pidx pbuf n k sp sum (idxs k) (tokens.get ⟨k, by omega⟩)).env
              "%buf" = some (.ptr pbuf)
            rw [c21_buf]; exact hbufS
          · show lookupName (c21 s pidx pbuf n k sp sum (idxs k) (tokens.get ⟨k, by omega⟩)).env
              "%nidx" = some (.int 64 (BitVec.ofNat 64 n))
            rw [c21_nidx]; exact hnikdS
          · show (c21 s pidx pbuf n k sp sum (idxs k) (tokens.get ⟨k, by omega⟩)).mem = m0
            rw [c21_mem]; exact hmemS
          · rfl
          · show lookupName (c21 s pidx pbuf n k sp sum (idxs k) (tokens.get ⟨k, by omega⟩)).env
              "%kn" = some (.int 64 (BitVec.ofNat 64 (k + 1)))
            exact c21_kn s pidx pbuf n k sp sum (idxs k) (tokens.get ⟨k, by omega⟩)
          · show lookupName (c21 s pidx pbuf n k sp sum (idxs k) (tokens.get ⟨k, by omega⟩)).env
              "%spn" = some (.int 64 (sp + BitVec.ofInt 64 (deltaZ (tokens.get ⟨k, by omega⟩))))
            exact c21_spn s pidx pbuf n k sp sum (idxs k) (tokens.get ⟨k, by omega⟩)
          · show lookupName (c21 s pidx pbuf n k sp sum (idxs k) (tokens.get ⟨k, by omega⟩)).env
              "%sumn" = some (.int 64
                (sum + (sp + BitVec.ofInt 64 (deltaZ (tokens.get ⟨k, by omega⟩)))))
            exact c21_sumn s pidx pbuf n k sp sum (idxs k) (tokens.get ⟨k, by omega⟩)
          · exact hspn
          · exact hsumn
        · have hk1 : k + 1 = n := by omega
          have hm0 : m = 0 := by omega
          have hstep := loop_step_exit calls s pidx pbuf n k sp sum (idxs k)
            (tokens.get ⟨k, by omega⟩) hn hk63 hidxS hbufS hnikdS hread (hfit k hk) htok
            hphiS hpcS hlt
          rw [runFuel_jump hstep]
          subst hm0
          have hstats1 : lookupName ({ c21 s pidx pbuf n k sp sum (idxs k)
                (tokens.get ⟨k, by omega⟩) with pc := "exit", pre := some "loop" } : State).env
              "%stats" = some (.ptr pstats) := by
            show lookupName (c21 s pidx pbuf n k sp sum (idxs k)
              (tokens.get ⟨k, by omega⟩)).env "%stats" = some (.ptr pstats)
            rw [c21_stats]; exact hstatsS
          have hspn1 : lookupName ({ c21 s pidx pbuf n k sp sum (idxs k)
                (tokens.get ⟨k, by omega⟩) with pc := "exit", pre := some "loop" } : State).env
              "%spn" = some (.int 64 (sp + BitVec.ofInt 64 (deltaZ (tokens.get ⟨k, by omega⟩)))) := by
            show lookupName (c21 s pidx pbuf n k sp sum (idxs k)
              (tokens.get ⟨k, by omega⟩)).env "%spn" = _
            exact c21_spn s pidx pbuf n k sp sum (idxs k) (tokens.get ⟨k, by omega⟩)
          have hsumn1 : lookupName ({ c21 s pidx pbuf n k sp sum (idxs k)
                (tokens.get ⟨k, by omega⟩) with pc := "exit", pre := some "loop" } : State).env
              "%sumn" = some (.int 64
                (sum + (sp + BitVec.ofInt 64 (deltaZ (tokens.get ⟨k, by omega⟩))))) := by
            show lookupName (c21 s pidx pbuf n k sp sum (idxs k)
              (tokens.get ⟨k, by omega⟩)).env "%sumn" = _
            exact c21_sumn s pidx pbuf n k sp sum (idxs k) (tokens.get ⟨k, by omega⟩)
          have hbody1 : denoteCode calls exitInstrs
              ({ c21 s pidx pbuf n k sp sum (idxs k) (tokens.get ⟨k, by omega⟩)
                  with pc := "exit", pre := some "loop" } : State) =
              some (xec ({ c21 s pidx pbuf n k sp sum (idxs k) (tokens.get ⟨k, by omega⟩)
                  with pc := "exit", pre := some "loop" } : State) pstats
                (sp + BitVec.ofInt 64 (deltaZ (tokens.get ⟨k, by omega⟩)))
                (sum + (sp + BitVec.ofInt 64 (deltaZ (tokens.get ⟨k, by omega⟩))))) :=
            exit_body calls _ pstats _ _ hstats1 hspn1 hsumn1
          have hstep2 : step calls depthFunction
              ({ c21 s pidx pbuf n k sp sum (idxs k) (tokens.get ⟨k, by omega⟩)
                  with pc := "exit", pre := some "loop" } : State) =
              .ret (some (.int 64 (sp + BitVec.ofInt 64 (deltaZ (tokens.get ⟨k, by omega⟩)))))
                (xec ({ c21 s pidx pbuf n k sp sum (idxs k) (tokens.get ⟨k, by omega⟩)
                    with pc := "exit", pre := some "loop" } : State) pstats
                  (sp + BitVec.ofInt 64 (deltaZ (tokens.get ⟨k, by omega⟩)))
                  (sum + (sp + BitVec.ofInt 64 (deltaZ (tokens.get ⟨k, by omega⟩))))) := by
            rw [step_of calls _ "exit" ⟨"exit", exitInstrs, exitTerm⟩ _ rfl findBlock_exit hbody1]
            exact exit_term _ pstats _ _ hspn1
          rw [runFuel_ret hstep2]
          have hspf : sp + BitVec.ofInt 64 (deltaZ (tokens.get ⟨k, by omega⟩)) =
              BitVec.ofInt 64 (depthSpec tokens).1 := by
            rw [hspn, hk1, take_all tokens n hlen]
          have hsuf : sum + (sp + BitVec.ofInt 64 (deltaZ (tokens.get ⟨k, by omega⟩))) =
              BitVec.ofInt 64 (depthSpec tokens).2 := by
            rw [hsumn, hk1, take_all tokens n hlen]
          rw [hsuf, hspf]
          simp [Result, statsMem, xec_mem, c21_mem, hmemS]
  intro k hk sp sum s hinv
  exact aux (n - k) k sp sum s rfl hk hinv

/-! ## The whole function -/

theorem entry_jump_zero (calls : Calls) (pbuf pidx pstats : Nat) (m0 : Mem) :
    step calls depthFunction (start m0 pbuf pidx pstats (BitVec.ofNat 64 0)) =
      .jump { e1 (start m0 pbuf pidx pstats (BitVec.ofNat 64 0)) 0
        with pc := "exit0", pre := some "entry" } := by
  rw [step_of calls _ "entry" ⟨"entry", entryInstrs, entryTerm⟩ _
    (start_pc m0 pbuf pidx pstats (BitVec.ofNat 64 0)) findBlock_entry
    (entry_body calls _ 0 (start_nidx m0 pbuf pidx pstats (BitVec.ofNat 64 0)))]
  rw [show entryTerm = .condbr (.reg "%nz") "exit0" "loop" from rfl]
  have hop : evalOperand
      (e1 (start m0 pbuf pidx pstats (BitVec.ofNat 64 0)) 0) (.reg "%nz") =
      some (.int 1 (1 : BitVec 1)) := by
    show (some (Value.int 1 (BitVec.ofBool (BitVec.ofNat 64 0 = BitVec.ofNat 64 0)))
      : Option Value) = some (Value.int 1 (1 : BitVec 1))
    rfl
  have hpc' : (e1 (start m0 pbuf pidx pstats (BitVec.ofNat 64 0)) 0).pc = "entry" := by
    show (start m0 pbuf pidx pstats (BitVec.ofNat 64 0)).pc = "entry"
    exact start_pc m0 pbuf pidx pstats (BitVec.ofNat 64 0)
  rw [execTerm_condbr_true (t := "exit0") (f := "loop") hop rfl]
  simp [hpc']

theorem run_zero (calls : Calls) (pbuf pidx pstats : Nat) (m0 : Mem) :
    runFuel calls 2 depthFunction (start m0 pbuf pidx pstats (BitVec.ofNat 64 0))
      = Result calls m0 pstats [] := by
  rw [runFuel_jump (entry_jump_zero calls pbuf pidx pstats m0)]
  have hstats1 : lookupName ({ e1 (start m0 pbuf pidx pstats (BitVec.ofNat 64 0)) 0
        with pc := "exit0", pre := some "entry" } : State).env "%stats" =
      some (.ptr pstats) := by
    show lookupName (e1 (start m0 pbuf pidx pstats (BitVec.ofNat 64 0)) 0).env "%stats" =
      some (.ptr pstats)
    rw [show lookupName (e1 (start m0 pbuf pidx pstats (BitVec.ofNat 64 0)) 0).env "%stats" =
        lookupName (start m0 pbuf pidx pstats (BitVec.ofNat 64 0)).env "%stats" from by
      simp [e1, State.bind, lookupName]]
    exact start_stats m0 pbuf pidx pstats (BitVec.ofNat 64 0)
  have hstep2 : step calls depthFunction
      ({ e1 (start m0 pbuf pidx pstats (BitVec.ofNat 64 0)) 0
          with pc := "exit0", pre := some "entry" } : State) =
      .ret (some (.int 64 (BitVec.ofNat 64 0)))
        (x0c ({ e1 (start m0 pbuf pidx pstats (BitVec.ofNat 64 0)) 0
            with pc := "exit0", pre := some "entry" } : State) pstats) := by
    rw [step_of calls _ "exit0" ⟨"exit0", exit0Instrs, exit0Term⟩ _ rfl findBlock_exit0
      (exit0_body calls _ pstats hstats1)]
    exact exit0_term _ pstats
  rw [runFuel_ret hstep2]
  simp [Result, statsMem, depthSpec, x0c, x0b, x0a, e1, State.bind, start_mem]

theorem entry_jump_pos (calls : Calls) (pbuf pidx pstats : Nat) (m0 : Mem) (n : Nat)
    (hn0 : n ≠ 0) (hn : n < 2^63) :
    step calls depthFunction (start m0 pbuf pidx pstats (BitVec.ofNat 64 n)) =
      .jump { e1 (start m0 pbuf pidx pstats (BitVec.ofNat 64 n)) n
        with pc := "loop", pre := some "entry" } := by
  rw [step_of calls _ "entry" ⟨"entry", entryInstrs, entryTerm⟩ _
    (start_pc m0 pbuf pidx pstats (BitVec.ofNat 64 n)) findBlock_entry
    (entry_body calls _ n (start_nidx m0 pbuf pidx pstats (BitVec.ofNat 64 n)))]
  rw [show entryTerm = .condbr (.reg "%nz") "exit0" "loop" from rfl]
  have hop : evalOperand (e1 (start m0 pbuf pidx pstats (BitVec.ofNat 64 n)) n) (.reg "%nz") =
      some (.int 1 (0 : BitVec 1)) := by
    show (some (Value.int 1 (BitVec.ofBool (BitVec.ofNat 64 n = BitVec.ofNat 64 0)))
      : Option Value) = some (Value.int 1 (0 : BitVec 1))
    have hne : BitVec.ofNat 64 n ≠ BitVec.ofNat 64 0 := by
      intro h
      have h1 : (BitVec.ofNat 64 n).toNat = (BitVec.ofNat 64 0).toNat := by rw [h]
      rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at h1
      simp at h1
      exact hn0 h1
    simp [hne]
  have hpc' : (e1 (start m0 pbuf pidx pstats (BitVec.ofNat 64 n)) n).pc = "entry" := by
    show (start m0 pbuf pidx pstats (BitVec.ofNat 64 n)).pc = "entry"
    exact start_pc m0 pbuf pidx pstats (BitVec.ofNat 64 n)
  rw [execTerm_condbr_false (t := "exit0") (f := "loop") hop rfl]
  simp [hpc']

/-- The kernel's refinement: from the caller's memory, the depth fold's two
values are the returned word and the statistics pair, and nothing else in
memory is touched.

`hn` is the model's own `gep` bound, not slack: `evalInstr`'s `gep` arm scales the
index by the element type's size and adds it only while the sign-extended 64-bit
index is below `2 ^ 63`; at or above that bound it subtracts instead, taking a
sign-extended index `v`'s magnitude `2 ^ 64 - v`, whose displacement is that
magnitude scaled by the element type's size, and it is `ub` there only where the
displacement exceeds the base
(`LeanLLVM/Semantics.lean`).  The loop
reaches `%ip = getelementptr i32, ptr %idx, i64 %k` at the top of every iteration,
so `hn` is what keeps every iteration on the **forward** branch, where the address
this theorem composes — `%idx + 4 * %k` — is the address the model computes for
`%ip`.  It is not a definedness hypothesis: a `%k` at or above the bound takes the
backward branch, which is a different run and not the one composed here.  The
second `gep`, `%cp`, needs no such hypothesis: `hfit` already confines the index it
loads from the array to `2 ^ 32`. -/
theorem depth_count_refines (calls : Calls) (pbuf pidx pstats : Nat) (m0 : Mem)
    (tokens : List UInt8) (idxs : Nat → Nat) (n : Nat)
    (hn : n < 2^63) (hlen : tokens.length = n)
    (hidx : ∀ (k : Nat), k < n → readBytes m0 (pidx + k * 4) 4 = some (natToBytes (idxs k) 4))
    (hfit : ∀ (k : Nat), k < n → idxs k < 2^32)
    (hbuf : ∀ (k : Nat) (hk : k < n),
      readBytes m0 (pbuf + idxs k) 1 = some [tokens.get ⟨k, by rw [hlen]; exact hk⟩]) :
    runFuel calls (n + 2) depthFunction (start m0 pbuf pidx pstats (BitVec.ofNat 64 n))
      = Result calls m0 pstats tokens := by
  by_cases hn0 : n = 0
  · subst hn0
    have htoks : tokens = [] := by
      have h0 : tokens.length = 0 := by omega
      exact List.eq_nil_of_length_eq_zero h0
    subst htoks
    have hrun := run_zero calls pbuf pidx pstats m0
    simpa using hrun
  · have hstep := entry_jump_pos calls pbuf pidx pstats m0 n hn0 hn
    rw [show n + 2 = (n + 1) + 1 from rfl]
    rw [runFuel_jump hstep]
    have hlr := loop_run calls pstats pidx pbuf m0 tokens idxs n hn hlen hidx hfit hbuf
      0 (by omega) 0 0
      ({ e1 (start m0 pbuf pidx pstats (BitVec.ofNat 64 n)) n
          with pc := "loop", pre := some "entry" } : State)
      (loopHead_zero m0 pidx pbuf pstats n tokens _
        (by
          show lookupName (e1 (start m0 pbuf pidx pstats (BitVec.ofNat 64 n)) n).env "%stats" =
            some (.ptr pstats)
          rw [show lookupName (e1 (start m0 pbuf pidx pstats (BitVec.ofNat 64 n)) n).env "%stats" =
              lookupName (start m0 pbuf pidx pstats (BitVec.ofNat 64 n)).env "%stats" from by
            simp [e1, State.bind, lookupName]]
          exact start_stats m0 pbuf pidx pstats (BitVec.ofNat 64 n))
        (by
          show lookupName (e1 (start m0 pbuf pidx pstats (BitVec.ofNat 64 n)) n).env "%idx" =
            some (.ptr pidx)
          rw [show lookupName (e1 (start m0 pbuf pidx pstats (BitVec.ofNat 64 n)) n).env "%idx" =
              lookupName (start m0 pbuf pidx pstats (BitVec.ofNat 64 n)).env "%idx" from by
            simp [e1, State.bind, lookupName]]
          exact start_idx m0 pbuf pidx pstats (BitVec.ofNat 64 n))
        (by
          show lookupName (e1 (start m0 pbuf pidx pstats (BitVec.ofNat 64 n)) n).env "%buf" =
            some (.ptr pbuf)
          rw [show lookupName (e1 (start m0 pbuf pidx pstats (BitVec.ofNat 64 n)) n).env "%buf" =
              lookupName (start m0 pbuf pidx pstats (BitVec.ofNat 64 n)).env "%buf" from by
            simp [e1, State.bind, lookupName]]
          exact start_buf m0 pbuf pidx pstats (BitVec.ofNat 64 n))
        (by
          show lookupName (e1 (start m0 pbuf pidx pstats (BitVec.ofNat 64 n)) n).env "%nidx" =
            some (.int 64 (BitVec.ofNat 64 n))
          rw [show lookupName (e1 (start m0 pbuf pidx pstats (BitVec.ofNat 64 n)) n).env "%nidx" =
              lookupName (start m0 pbuf pidx pstats (BitVec.ofNat 64 n)).env "%nidx" from by
            simp [e1, State.bind, lookupName]]
          exact start_nidx m0 pbuf pidx pstats (BitVec.ofNat 64 n))
        (by
          show (e1 (start m0 pbuf pidx pstats (BitVec.ofNat 64 n)) n).mem = m0
          rw [show (e1 (start m0 pbuf pidx pstats (BitVec.ofNat 64 n)) n).mem =
              (start m0 pbuf pidx pstats (BitVec.ofNat 64 n)).mem from by
            simp [e1, State.bind]]
          exact start_mem m0 pbuf pidx pstats (BitVec.ofNat 64 n))
        (by rfl) (by rfl))
    simpa using hlr

/-! ## The installation boundary

The comma-mask units carry a pure boundary contract,
`LeanLLVM.Vellum.commaContract`: one `BitVec 64` in, one out.  The depth kernel
is not that shape — it reads a buffer through an index array, is defined only on
a memory holding both, and writes the two statistics words — so that structure
does not describe it.  Its boundary is the statement `depth_count_refines`
proves, written once as a proposition so the installation certificate can name
it and the selector can compare a certificate field with it.

The statement is the theorem's own type, not a paraphrase beside it: every
hypothesis and the conclusion are repeated here, so `depth_count_refines` is an
inhabitant of `depthContract` and a hypothesis added to one and not the other
leaves the contract unproved. -/
def depthContract : Prop :=
  ∀ (calls : Calls) (pbuf pidx pstats : Nat) (m0 : Mem)
    (tokens : List UInt8) (idxs : Nat → Nat) (n : Nat)
    (hn : n < 2^63) (hlen : tokens.length = n)
    (hidx : ∀ (k : Nat), k < n →
      readBytes m0 (pidx + k * 4) 4 = some (natToBytes (idxs k) 4))
    (hfit : ∀ (k : Nat), k < n → idxs k < 2^32)
    (hbuf : ∀ (k : Nat) (hk : k < n),
      readBytes m0 (pbuf + idxs k) 1 = some [tokens.get ⟨k, by rw [hlen]; exact hk⟩]),
    runFuel calls (n + 2) depthFunction (start m0 pbuf pidx pstats (BitVec.ofNat 64 n))
      = Result calls m0 pstats tokens

/-- The installation boundary is exactly what the kernel theorem proves. -/
theorem depthContract_holds : depthContract := depth_count_refines

end LeanLLVM.Vellum.DepthCountRefine
