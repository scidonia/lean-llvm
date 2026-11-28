/-
Core data types shared by the syntax, the semantics and the transformations.

The model targets the LLVM IR that reaches the late optimisation pipeline: the
scalar integer core, a byte-addressed memory, and the value forms the captured
stage-2 helper bodies use.  Three aggregate forms are modelled: the fixed-length
vector `<n x iW>`, which the JSON block classifier is emitted in; the fixed-length
array `[N x T]`; and a named struct, which carries the byte extent the target
datalayout gives it.  A binary64 value is carried as its 64-bit pattern, the form
`bitcast` and memory read and write without loss.

Pointer provenance is deliberately outside the first slice, and the parser
refuses what it does not model rather than silently approximating it.
-/
namespace LeanLLVM

/-- LLVM value types modelled by the core.  A vector carries its element type,
so `<32 x i8>` and `<32 x i1>` are distinct types.  Two aggregate forms are
modelled, and both carry their layout: an array carries its element count and
element type, and a named struct carries the byte extent the target datalayout
gives it.  The struct's extent is the whole of what the model knows about it —
no fields, no field indices, no padding rule. -/
inductive Ty where
  | int (w : Nat)
  | ptr
  | void
  | vec (n : Nat) (elem : Ty)
  /-- `[N x T]`: `n` elements of `elem`, with no padding between elements. -/
  | array (n : Nat) (elem : Ty)
  /-- `%struct.<name>`, with the byte extent the target datalayout gives it. -/
  | struct (name : String) (bytes : Nat)
  /-- LLVM's `double`: an IEEE 754 binary64 value, carried as its 64-bit pattern
  in `Value.float`. -/
  | double
  deriving DecidableEq, Repr

/-- Number of bytes a value of this type occupies in memory.  A vector of
integers occupies its lane count times the lane width; any other element type is
not laid out, so its size is zero and an allocation of it moves the cursor
nowhere.  An array occupies its count times its element's size, which is LLVM's
allocated size exactly when the element's allocated and stored sizes agree — the
property `Ty.gepElemAdmitted` admits an element by.  A struct occupies its
declared extent, which is the allocated size and not the sum of any fields. -/
def Ty.sizeBytes : Ty → Nat
  | .int w => (w + 7) / 8
  | .ptr => 8
  | .void => 0
  | .vec n (.int w) => n * ((w + 7) / 8)
  | .vec _ _ => 0
  | .array n elem => n * elem.sizeBytes
  | .struct _ bytes => bytes
  | .double => 8

/-- A literal operand, as it appears in textual IR.  A splat is the vector
constant form `splat (<elem> <value>)`: the same integer in every lane.  It
carries its lane count, its lane width and its value, so a splat of a non-integer
— `splat (i8 undef)`, `splat (ptr null)` — has no representation and no printed
form.  The lane count is omitted by the printer because the operand's vector type
supplies it on re-parse.

`vector` is the other vector literal form, `<i8 34, i8 92, …>`: the lanes written
one by one.  It carries the lane width and the lanes and takes its lane count
from their length, so there is no count field that could disagree with the list;
the operand's `<n x iw>` type supplies the count on parse and the parser refuses
a list of another length.  Lanes are integers, so a list with `undef` in a lane
position has no representation and the parser refuses one by name; a `poison`
lane is the separate `vectorPoison` form, which keeps the per-lane placement.  A
hand-built list whose length disagrees with the operand type is not a value of
that type: `Value.vecLanes` refuses it by shape, which the semantics reads as
undefined behaviour.

`float` is a binary64 literal as its bit pattern: LLVM writes it as a decimal or
a `0x`-prefixed hexadecimal, and the pattern is what both spellings denote.

`vectorPoison` is a lane list with at least one `poison` lane, `<i64 poison, i64
0>`.  LLVM gives the literal a per-lane value: the poison lanes are poison and
the others are the values written.  `Const.toValue` keeps that placement as
`Value.vecPoison`, whose every read as a vector is undefined behaviour; the one
use that recovers a defined value is a lane write over every poison lane, which
`Const.poisonLaneInsert?` states and `evalInstr` applies. -/
inductive Const where
  | int (w : Nat) (v : BitVec w)
  | null
  | undef
  | poison
  | splat (n w : Nat) (v : BitVec w)
  | vector (w : Nat) (lanes : List (BitVec w))
  /-- A lane list carrying a `poison` lane: `lanes[k] = none` is a poison lane. -/
  | vectorPoison (w : Nat) (lanes : List (Option (BitVec w)))
  /-- A binary64 literal, as its bit pattern. -/
  | float (bits : BitVec 64)
  deriving DecidableEq, Repr

/-- A dynamically typed value.  Integer values carry their width, so arithmetic
is width-checked when an operand is read.  A vector value carries its lane count
and lane width, and its lanes are a list of exactly that many lanes; a list of
another length is a value the semantics does not produce, and `Value.vecLanes`
rejects it by shape.  A binary64 value is its 64-bit pattern: the pattern is the
value, so two spellings of a number that differ in bits (`+0` and `-0`) are
distinct, and a NaN keeps its payload.  `vecPoison` is a vector carrying at least
one poison lane, the value of the `vectorPoison` literal: `Value.vecLanes`
refuses it, so every use that reads it as a vector is `ub`, and only the lane
write that covers the poison lanes (`Const.poisonLaneInsert?`) produces a
readable vector from it.  `poison` is not a value a use observes:
a `phi` whose taken edge supplies a `poison` operand binds it into its
destination, and a read of that destination is undefined behaviour (`ub`) —
which is where `Const.toValue` already puts a `poison` immediate read directly.
The constructor is therefore what a cell holds between the edge's write and the
first read, and no other source produces it. -/
inductive Value where
  | int (w : Nat) (v : BitVec w)
  | ptr (addr : Nat)
  | vec (n w : Nat) (lanes : List (BitVec w))
  /-- A vector whose lane `k` is a poison lane when `lanes[k] = none`. -/
  | vecPoison (n w : Nat) (lanes : List (Option (BitVec w)))
  /-- A binary64 value, as its 64-bit pattern. -/
  | float (bits : BitVec 64)
  /-- The value a `phi` binds from a `poison` incoming: present in the cell,
  unreadable by any use. -/
  | poison
  deriving DecidableEq, Repr

/-- The value of a literal.  `undef` and `poison` are modelled as undefined
behaviour: the first slice has no nondeterministic semantics, so a program that
reads one — an operand the instruction reads directly — is `ub`.  That is an
over-approximation of LLVM's poison, not a refinement-direction guarantee: `Beh`
has a run that reaches `ub` admit every outcome, so where LLVM's poison is never
observed this model is more permissive than LLVM, not less.  The one place a
`poison` literal is not itself a use is a `phi`'s taken incoming, which binds
`Value.poison` into the destination instead of failing the selection: the use is
the read of that destination, and the literal stays `ub` when an instruction
reads it directly.  A splat is the
same value in every lane, and it is total: its element is an integer by
construction.  A lane list is the vector it writes, with the list's length as the
lane count.  A lane list carrying a poison lane is the `vecPoison` value: the
per-lane placement is kept, every read of it as a vector is `ub`, and the one
recovery is the lane write that covers the poison lane (`poisonLaneInsert?`). -/
def Const.toValue : Const → Option Value
  | .int w v => some (.int w v)
  | .null => some (.ptr 0)
  | .undef => none
  | .poison => none
  | .splat n w v => some (.vec n w (List.replicate n v))
  | .vector w lanes => some (.vec lanes.length w lanes)
  | .vectorPoison w lanes => some (.vecPoison lanes.length w lanes)
  | .float b => some (.float b)

/-- The lanes a lane write produces from a vector literal carrying poison lanes.

`k` is the written lane and `x` the defined value written there.  The write is
modelled on the literal's per-lane reading: the written lane becomes `x` and
every other lane keeps what the literal wrote.  The result is a value only when
the written lane is a poison lane and no poison lane survives the write —
`some lanes'` — and otherwise `none`, which the semantics reads as undefined
behaviour.  That is LLVM's reading: overwriting the only poison lane gives a
fully defined vector, while a poison lane the write does not cover makes the
value poison, and this model has no poison value to return. -/
def Const.poisonLaneInsert? (w : Nat) (lanes : List (Option (BitVec w))) (k x : Nat) :
    Option (List (BitVec w)) :=
  match lanes[k]? with
  | some none =>
      if (lanes.set k (some (BitVec.ofNat w x))).all (fun l => l.isSome) then
        some ((lanes.map (fun l => l.getD 0)).set k (BitVec.ofNat w x))
      else none
  | _ => none

/-- A lane write over a poison lane, with every lane defined after the write,
rebuilds the vector. -/
theorem Const.poisonLaneInsert?_eq_some {w : Nat} {lanes : List (Option (BitVec w))}
    {k x : Nat} (hk : lanes[k]? = some none)
    (hall : (lanes.set k (some (BitVec.ofNat w x))).all (fun l => l.isSome) = true) :
    Const.poisonLaneInsert? w lanes k x =
      some ((lanes.map (fun l => l.getD 0)).set k (BitVec.ofNat w x)) := by
  unfold Const.poisonLaneInsert?
  rw [hk]
  simp [hall]

/-- A lane write that leaves a poison lane uncovered has no value. -/
theorem Const.poisonLaneInsert?_eq_none {w : Nat} {lanes : List (Option (BitVec w))}
    {k x : Nat} (hk : lanes[k]? = some none)
    (hall : (lanes.set k (some (BitVec.ofNat w x))).all (fun l => l.isSome) = false) :
    Const.poisonLaneInsert? w lanes k x = none := by
  unfold Const.poisonLaneInsert?
  rw [hk]
  simp [hall]

/-- An instruction operand. -/
inductive Operand where
  | reg (name : String)
  /-- A global symbol read as the address the loader gave it: the text's
  `@.str.14`.  The symbol is stored without its `@`, as a callee's is, and the
  program text does not say what the address is — the run does.

  It is not a `Const`: a constant's value is a function of the constant
  (`Const.toValue`), while a symbol's is a function of the load, so it cannot be
  `Const.toValue`'s argument and sits on the operand instead, whose value
  `evalOperand` reads from the state. -/
  | global (name : String)
  | imm (c : Const)
  deriving DecidableEq, Repr

/-- The environment names an operand reads: a register's spelling, which begins
`%`, or a global symbol's, which begins `@`.  The names are the text's own
spellings, so the two kinds cannot collide and reading either is one lookup; a
global read is a name read — resolved from the environment the run supplies — so
it belongs in this list, and the transport lemmas that work over a read set
(`State.AgreeOn`) cover it unchanged. -/
def Operand.regs : Operand → List String
  | .reg n => [n]
  | .global n => [n]
  | .imm _ => []

/-- Binary integer operations. -/
inductive BinOp where
  | add | sub | mul | udiv | sdiv | urem | srem
  | and | or | xor | shl | lshr | ashr
  deriving DecidableEq, Repr, Inhabited

/-- Integer comparison predicates. -/
inductive IPred where
  | eq | ne | ult | ule | ugt | uge | slt | sle | sgt | sge
  deriving DecidableEq, Repr, Inhabited

/-- Floating-point comparison predicates.  The emission's one site is `oeq`;
the other fifteen are refused by name rather than given a meaning no body
needs. -/
inductive FPred where
  | oeq
  deriving DecidableEq, Repr, Inhabited

/-- Register environment.  Later bindings shadow earlier ones; the semantics
only ever extends it, and a pass may rely on a name being bound exactly once
(SSA). -/
abbrev Env := List (String × Value)

/-- The loader's assignment: the address of each global symbol a run may name.
The program text names the symbol; the address is not in the text, so it is a
staging input beside the arguments, the memory and the allocator base — the same
kind of fact as `initState`'s `next`, which reserves address `0` for `null`.

A run that reads a symbol this list does not bind is undefined behaviour, exactly
as a call the `Calls` environment does not resolve is.  The addresses must lie
outside `null`'s `0` and outside the allocator's range, because the model has no
object to keep them apart. -/
abbrev Globals := List (String × Nat)

/-- The environment bindings a global assignment adds: each symbol bound under
its own `@`-prefixed spelling to the pointer of its address. -/
def Globals.env (g : Globals) : Env := g.map fun (n, a) => (n, .ptr a)

/-- Memory, as a finite map from byte address to byte.  The representation is
an association list: small, total and easy to reason about. -/
abbrev Mem := List (Nat × UInt8)

/-- Look up a name in an association list. -/
def lookupName : List (String × α) → String → Option α
  | [], _ => none
  | (k, v) :: rest, n => if k = n then some v else lookupName rest n

@[simp] theorem lookupName_nil (n : String) : lookupName ([] : List (String × α)) n = none := rfl

@[simp] theorem lookupName_cons_self (k : String) (v : α) (rest : List (String × α)) :
    lookupName ((k, v) :: rest) k = some v := by
  simp [lookupName]

theorem lookupName_cons_ne {k n : String} (v : α) (rest : List (String × α)) (h : k ≠ n) :
    lookupName ((k, v) :: rest) n = lookupName rest n := by
  simp [lookupName, h]

theorem lookupName_cons_eq {k n : String} (v : α) (rest : List (String × α)) (h : k = n) :
    lookupName ((k, v) :: rest) n = some v := by
  subst h
  exact lookupName_cons_self k v rest

/-- Read one byte. -/
def readByte : Mem → Nat → Option UInt8
  | [], _ => none
  | (a, b) :: rest, addr => if a = addr then some b else readByte rest addr

/-- Write one byte, replacing an existing cell at the same address. -/
def writeByte : Mem → Nat → UInt8 → Mem
  | [], addr, b => [(addr, b)]
  | (a, b') :: rest, addr, b =>
      if a = addr then (a, b) :: rest else (a, b') :: writeByte rest addr b

/-- Read `n` consecutive bytes starting at `addr`. -/
def readBytes (m : Mem) (addr : Nat) : Nat → Option (List UInt8)
  | 0 => some []
  | n + 1 =>
      match readByte m addr with
      | none => none
      | some b =>
          match readBytes m (addr + 1) n with
          | none => none
          | some bs => some (b :: bs)

/-- Write `bs` consecutively starting at `addr`. -/
def writeBytes (m : Mem) : Nat → List UInt8 → Mem
  | _, [] => m
  | addr, b :: bs => writeBytes (writeByte m addr b) (addr + 1) bs

/-- Little-endian interpretation of a byte sequence. -/
def bytesToNat : List UInt8 → Nat
  | [] => 0
  | b :: bs => b.toNat + 256 * bytesToNat bs

/-- Little-endian encoding of the low `n` bytes of `v`. -/
def natToBytes (v : Nat) : Nat → List UInt8
  | 0 => []
  | n + 1 => UInt8.ofNat (v % 256) :: natToBytes (v / 256) n

end LeanLLVM
