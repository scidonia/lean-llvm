/-
An executable, total-so-far-as-it-goes semantics for the internal IR.

Control flow is a step function over basic blocks, and the fuel-indexed run is
the semantics the refinement relation is stated over.  `none` from `runFuel`
means "out of fuel", which is how divergence is represented: no finite number
of steps produces an outcome.

Undefined behaviour is a distinguished outcome (`ub`), not a stuck state.  A
`ub` reached on any prefix makes every outcome possible, which is exactly what
`Beh` below records.

Calls are instructions whose callee is resolved by an explicit environment
(`Calls`) rather than by the function being executed.  The environment is
deterministic and returns what the callee leaves behind — its value, its memory
and the allocator state the caller resumes from — so a call is a memory channel
between caller and callee.  An unresolved call is `ub`.
-/
import LeanLLVM.Syntax

namespace LeanLLVM

/-- Machine state: register environment, memory, next free byte address, the
block currently being executed, and the block it was entered from.

The predecessor field is written by the `jump` transition and by nothing else,
and read by `phi` and by nothing else: `initState` sets it to `none`, because
the entry block has no predecessor.  A program without a `phi` never observes
it, which is the non-interference theorem below. -/
structure State where
  env : Env
  mem : Mem
  next : Nat
  pc : String
  pre : Option String
  deriving Repr

/-- The same state with a different predecessor.  Used to state that the field
is not observable by a `phi`-free program. -/
def State.setPre (s : State) (p : Option String) : State := { s with pre := p }

@[simp] theorem State.setPre_self (s : State) : s.setPre s.pre = s := rfl

/-- Two states agree on every field except the predecessor: the registers, the
memory, the allocator state and the block are equal, and only the block the
state was entered from may differ.  This is the relation `phi`-free code cannot
distinguish. -/
def State.SameExceptPre (s t : State) : Prop :=
  s.env = t.env ∧ s.mem = t.mem ∧ s.next = t.next ∧ s.pc = t.pc

theorem State.sameExceptPre_refl (s : State) : s.SameExceptPre s :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Two states agreeing outside the predecessor are one `setPre` apart: the
state with `t`'s predecessor is `t` itself. -/
theorem State.setPre_eq_of_sameExceptPre {s t : State} (h : s.SameExceptPre t) :
    s.setPre t.pre = t := by
  cases s with
  | mk env mem next pc pre =>
    cases t with
    | mk env' mem' next' pc' pre' =>
      simp only [State.SameExceptPre] at h
      obtain ⟨rfl, rfl, rfl, rfl⟩ := h
      rfl

/-- The predecessor field is not part of an operand read or of a jump's source
block, so replacing it leaves those projections alone. -/
@[simp] theorem State.setPre_pc (s : State) (p : Option String) :
    (s.setPre p).pc = s.pc := rfl

@[simp] theorem State.setPre_env (s : State) (p : Option String) :
    (s.setPre p).env = s.env := rfl

@[simp] theorem State.setPre_mem (s : State) (p : Option String) :
    (s.setPre p).mem = s.mem := rfl

@[simp] theorem State.setPre_next (s : State) (p : Option String) :
    (s.setPre p).next = s.next := rfl

/-- Bind a register to a value. -/
def State.bind (s : State) (n : String) (v : Value) : State :=
  { s with env := (n, v) :: s.env }

/-- Bind a list of registers in the order the block wrote them.  The last entry
ends at the head of the environment, exactly where binding each in turn would
leave it, so a group's install is the install its members would each have made. -/
def State.bindAll (s : State) : List (String × Value) → State
  | [] => s
  | (n, v) :: rest => (s.bind n v).bindAll rest

theorem State.bind_setPre (s : State) (p : Option String) (n : String) (v : Value) :
    (s.setPre p).bind n v = (s.bind n v).setPre p := rfl

theorem State.bindAll_setPre (s : State) (p : Option String)
    (bs : List (String × Value)) :
    (s.setPre p).bindAll bs = (s.bindAll bs).setPre p := by
  induction bs generalizing s with
  | nil => rfl
  | cons b rest ih =>
      obtain ⟨n, v⟩ := b
      simp only [State.bindAll, State.bind_setPre]
      exact ih (s.bind n v)

/-- What a callee leaves behind: the value it returns, the memory after its
writes, and the allocator state the caller resumes from.  The memory is the
complete memory the callee leaves, not a delta: the caller adopts it, so a callee
that allocates or writes must return the caller's memory with its own writes
applied, and a callee that writes outside its own frame erases caller state. -/
structure CallOutcome where
  ret : Value
  mem : Mem
  next : Nat
  deriving Repr

/-- The values a call can return, indexed by callee symbol and argument list.
This is the linker's selection seen from the semantics: an entry maps a symbol,
an argument list, the caller's memory and the caller's allocator state to what
the callee leaves.  A missing entry is an unresolved call, which is `ub`.  The
allocator is shared: the callee receives the caller's `next` and the caller
resumes from the value the callee returns. -/
abbrev Calls := String → List Value → Mem → Nat → Option CallOutcome

/-- The environment in which no call resolves. -/
def noCalls : Calls := fun _ _ _ _ => none

/-- Read an operand. -/
def evalOperand (s : State) : Operand → Option Value
  | .reg n => lookupName s.env n
  | .imm c => Const.toValue c

/-- Reading an operand does not consult the predecessor field. -/
theorem evalOperand_setPre (s : State) (p : Option String) (o : Operand) :
    evalOperand (s.setPre p) o = evalOperand s o := by
  cases o <;> rfl

/-- The value a `phi` selects in the state `s`: the incoming operand whose label
is the block the edge came from, read from `s`'s own environment.

`none` is undefined behaviour, and it has two causes that LLVM's verifier
refuses rather than defines: a state with no predecessor — the entry block, or a
hand-built state that never jumped — and an incoming list with no entry for the
predecessor the edge actually came from.  A `phi` whose predecessor *is* listed
and whose selected operand reads is defined; it is valid LLVM, and the value it
selects is the incoming operand's value.

Selection is a pure function of the state it is given.  `denoteCode` gives every
member of a block's leading `phi` run the same state, which is what makes the
run read one snapshot of the environment the edge carried in. -/
def phiSelect (s : State) (inc : List (String × Operand)) : Option Value :=
  match s.pre with
  | none => none
  | some p =>
      match phiIncoming p inc with
      | none => none
      | some op => evalOperand s op

/-- Binary integer operations.  Division and remainder by zero are undefined
behaviour (LLVM: poison).  Shifts follow Lean's `BitVec` saturating behaviour:
a count of at least the width yields all zeroes for `shl`/`lshr` and the sign
bit for `ashr`.  That is defined where LLVM has poison, so it permits fewer
rewrites than LLVM's semantics, never more. -/
def evalBinop (op : BinOp) {w : Nat} (a b : BitVec w) : Option (BitVec w) :=
  match op with
  | .add => some (a + b)
  | .sub => some (a - b)
  | .mul => some (a * b)
  | .udiv => if b = 0 then none else some (BitVec.udiv a b)
  | .sdiv => if b = 0 then none else some (BitVec.sdiv a b)
  | .urem => if b = 0 then none else some (BitVec.umod a b)
  | .srem => if b = 0 then none else some (BitVec.srem a b)
  | .and => some (a &&& b)
  | .or => some (a ||| b)
  | .xor => some (a ^^^ b)
  | .shl => some (BitVec.shiftLeft a b.toNat)
  | .lshr => some (BitVec.ushiftRight a b.toNat)
  | .ashr => some (BitVec.sshiftRight a b.toNat)

/-- Extract an integer of exactly width `w`, as a natural, from a value.
Widths are checked dynamically; a mismatch is undefined behaviour at the use
site.  Working at the `Nat` level keeps the fold proofs free of dependent
casts. -/
def Value.intToNat (w : Nat) : Value → Option Nat
  | .int w' v => if w' = w then some v.toNat else none
  | .ptr _ => none
  | .vec .. => none

/-- `evalBinop` at the `Nat` level: the operands are read as `w`-bit values. -/
def evalBinopNat (op : BinOp) (w : Nat) (a b : Nat) : Option Nat :=
  (evalBinop op (BitVec.ofNat w a) (BitVec.ofNat w b)).map BitVec.toNat

/-- Integer comparison, as a one-bit result. -/
def evalICmp (p : IPred) {w : Nat} (a b : BitVec w) : BitVec 1 :=
  BitVec.ofBool <|
    match p with
    | .eq => a = b
    | .ne => a ≠ b
    | .ult => BitVec.ult a b
    | .ule => BitVec.ule a b
    | .ugt => BitVec.ult b a
    | .uge => BitVec.ule b a
    | .slt => BitVec.slt a b
    | .sle => BitVec.sle a b
    | .sgt => BitVec.slt b a
    | .sge => BitVec.sle b a

/-- `evalICmp` at the `Nat` level. -/
def evalICmpNat (p : IPred) (w : Nat) (a b : Nat) : BitVec 1 :=
  evalICmp p (BitVec.ofNat w a) (BitVec.ofNat w b)

/-- Compare two pointer addresses.

An address is a natural here, so `eq` and `ne` are address equality and
`ult`/`ule`/`ugt`/`uge` are the unsigned order on addresses — the order LLVM
gives those predicates over its pointer value.  LLVM also defines `slt`, `sle`,
`sgt` and `sge` over the signed reading of its 64-bit pointer, but this model's
address is an unbounded `Nat` with no sign, so that reading is not representable
here: those four predicates return `none`.  The parser refuses text that writes
one on a pointer type; this is also the semantics' answer for an
`Instr.icmpPtr` built directly in an AST.

Agreement with LLVM's order holds while addresses stay below `2 ^ 64`, which the
model does not enforce: a `getelementptr i128` can put a `ptr` at `2 ^ 64 + 1`,
where `ugt` against a low address answers 1 while LLVM's wrapped address answers
0 (measured with `lli`).

The same `none` covers an operand that is not a pointer.  Text cannot reach it —
the parser refuses a pointer comparison whose register is not bound at `ptr` —
so it is the hand-built-AST case too, and `step` reads `none` as `ub`. -/
def evalICmpPtr (p : IPred) (a b : Nat) : Option (BitVec 1) :=
  match p with
  | .eq => some (BitVec.ofBool (a = b))
  | .ne => some (BitVec.ofBool (a ≠ b))
  | .ult => some (BitVec.ofBool (a < b))
  | .ule => some (BitVec.ofBool (a ≤ b))
  | .ugt => some (BitVec.ofBool (b < a))
  | .uge => some (BitVec.ofBool (b ≤ a))
  | .slt | .sle | .sgt | .sge => none

/-- Address equality is exact: the accepting case of `evalICmpPtr` is
`BitVec.ofBool` of the equality of the two naturals. -/
@[simp] theorem evalICmpPtr_eq (a b : Nat) :
    evalICmpPtr .eq a b = some (BitVec.ofBool (a = b)) := rfl

/-- The unsigned order compares addresses as naturals, so an address at or above
`2 ^ 63` is greater than a low one.  A signed reading of the same 64-bit pattern
would say the opposite; this model's address has no sign, so the signed
predicates are refused rather than given that reading. -/
theorem evalICmpPtr_high_address_unsigned :
    evalICmpPtr .ugt (2 ^ 63) 0 = some (1 : BitVec 1) ∧
      evalICmpPtr .ult (2 ^ 63) 0 = some (0 : BitVec 1) := by
  decide

/-- A signed predicate is not representable over this model's address, which has
no sign: `evalICmpPtr` returns `none`, which `step` reads as `ub`. -/
theorem evalICmpPtr_signed_none (p : IPred)
    (h : p = .slt ∨ p = .sle ∨ p = .sgt ∨ p = .sge) (a b : Nat) :
    evalICmpPtr p a b = none := by
  rcases h with rfl | rfl | rfl | rfl <;> rfl

/-- The lanes of a vector value at lane width `w` and count `n`, or `none` when
the value is not a vector of exactly that shape.  The width is an argument, so
the caller fixes the lane type and the shape check is a boolean, not a cast. -/
def Value.vecLanes (n w : Nat) : Value → Option (List (BitVec w))
  | .vec n' w' l =>
      if h : w' = w then
        (if l.length = n ∧ n' = n then some (h ▸ l) else none)
      else none
  | _ => none

/-- Lane-wise selection: lane `j` of the result is `a[j]` when the condition's
lane `j` is set and `b[j]` when it is clear.  The three lists are zipped in
lockstep, so the result is as long as the shortest; the instruction's shape
check gives all three the same length. -/
def selectLanes {w : Nat} (cs : List (BitVec 1)) (a b : List (BitVec w)) :
    List (BitVec w) :=
  (cs.zip (a.zip b)).map fun (c, ab) => if c = 1 then ab.1 else ab.2

/-- Little-endian lane packing: lane `k` becomes bit `k` of the natural. -/
def lanesToNat : List (BitVec 1) → Nat
  | [] => 0
  | b :: bs => (if b = 1 then 1 else 0) + 2 * lanesToNat bs

/-- The bit-level reading of `lanesToNat`: bit `k` is set exactly when lane `k`
is.  **No length hypothesis** — past the end the natural's bit is zero and the
lane lookup is `none`, so the two sides agree there too, and the consumer
discharges no bound at each use.  This is the fact the classifier body's mask
proof consumes; the `BitVec` side of that proof reaches the natural through
core's `BitVec.getLsbD_ofNat`, so no separate `BitVec`-width form of this fact
is stated. -/
theorem lanesToNat_testBit (l : List (BitVec 1)) (k : Nat) :
    (lanesToNat l).testBit k = (l[k]? = some (1 : BitVec 1)) := by
  induction l generalizing k with
  | nil => simp [lanesToNat]
  | cons b bs ih =>
      have ha : (if b = 1 then (1 : Nat) else 0) < 2 := by
        split <;> omega
      cases k with
      | zero =>
          rw [lanesToNat, Nat.testBit_zero, Nat.add_mul_mod_self_left,
            Nat.mod_eq_of_lt ha]
          split <;> simp_all
      | succ j =>
          rw [lanesToNat, Nat.testBit_succ,
            Nat.add_mul_div_left (if b = 1 then (1 : Nat) else 0) _ (by decide : (0 : Nat) < 2),
            Nat.div_eq_of_lt ha, Nat.zero_add]
          exact ih j

/-- Little-endian packing of integer lanes: lane `k` becomes bits
`[k * w, (k + 1) * w)` of the natural.  This is the layout `storeValue` writes
and `vecBitcast` reinterprets, so both read one definition rather than a second
packing. -/
def packLanes {w : Nat} : List (BitVec w) → Nat
  | [] => 0
  | x :: xs => x.toNat + 2 ^ w * packLanes xs

/-- The inverse of `packLanes` at another lane width: `n` lanes of width `w`,
lane `k` read from bit `k * w` of the natural.  `BitVec.ofNat` keeps the low `w`
bits of each quotient, so a natural wider than `n * w` is truncated exactly as a
reinterpretation truncates it. -/
def unpackLanes (w n v : Nat) : List (BitVec w) :=
  (List.range n).map fun k => BitVec.ofNat w (v / 2 ^ (k * w))

/-- A vector `bitcast`'s lane reinterpretation at equal total width: the source
lanes packed little-endian and split again at the destination's lane width. -/
def bitcastVecLanes {w : Nat} (wOut nOut : Nat) (lanes : List (BitVec w)) :
    List (BitVec wOut) :=
  unpackLanes wOut nOut (packLanes lanes)

/-- `llvm.x86.avx2.pshuf.b`'s table lookup, one entry per control lane: byte `i`
of the result is zero when bit 7 of control byte `i` is set, and otherwise the
table byte its low four bits select **within its own 16-byte lane** — lane base
`16 * (i / 16)`, bit 4 through bit 6 ignored.  VPSHUFB is lane-local; a linear
32-entry reading of the control is a different function.

The lane count is the control's: the instruction's two operands have one vector
type, and a shorter table leaves the unaddressed lanes zero. -/
def pshufbLanes (table control : List (BitVec 8)) : List (BitVec 8) :=
  (List.range control.length).map fun i =>
    let c := control.getD i 0
    if c.getLsbD 7 then 0
    else table.getD (16 * (i / 16) + (c.toNat % 16)) 0

/-- Load a value of the given type from an address.  A byte that was never
written makes the load undefined.

The `<n x i8>` arm is the byte-vector form the classifier's emitted body reads
with; the integer-lane arm below it is the same layout at another lane width — the
`bitcast <4 x i64> to <32 x i8>` the stage-1 kernel's emission opens with needs
it, and it is `storeValue`'s vector arm read back: `n * w / 8` bytes, lane `k`
from bits `[k * w, (k + 1) * w)`.  A total bit width that is not a whole number
of bytes has no byte layout, exactly as on the store side — a lane width that is
not a whole number of bytes is admitted when the vector's total width is whole. -/
def loadValue (m : Mem) (ty : Ty) (addr : Nat) : Option Value :=
  match ty with
  | .int w =>
      if w = 0 then none
      else
        match readBytes m addr ((w + 7) / 8) with
        | some bs => some (.int w (BitVec.ofNat w (bytesToNat bs)))
        | none => none
  | .ptr =>
      match readBytes m addr 8 with
      | some bs => some (.ptr (bytesToNat bs))
      | none => none
  | .vec n (.int 8) =>
      match readBytes m addr n with
      | some bs => some (.vec n 8 (bs.map fun b => BitVec.ofNat 8 b.toNat))
      | none => none
  | .vec n (.int w) =>
      if n * w % 8 = 0 then
        match readBytes m addr (n * w / 8) with
        | some bs => some (.vec n w (unpackLanes w n (bytesToNat bs)))
        | none => none
      else none
  | .vec _ _ => none
  | .void => none

/-- Store a value at an address.  A vector is stored as its lanes packed
little-endian, one lane after another, so a `<64 x i1>` value occupies eight
bytes and a `<8 x i32>` value thirty-two: the admitted vector widths are exactly
those whose total bit width is whole bytes, at any lane width.  A vector whose
total bit width is not a whole number of bytes has no byte layout, and a shape
or lane width that disagrees with the instruction's type is undefined behaviour;
the parser refuses both — the total-width rule at the store, and a value register
of another type against the function's register table — so this is the
hand-built-AST case. -/
def storeValue (s : State) (ty : Ty) (v : Value) (addr : Nat) : Option State :=
  match ty, v with
  | .int w, .int w' x =>
      if w' = w then
        some { s with mem := writeBytes s.mem addr (natToBytes x.toNat ((w + 7) / 8)) }
      else none
  | .ptr, .ptr a => some { s with mem := writeBytes s.mem addr (natToBytes a 8) }
  | .vec n (.int w), .vec n' w' lanes =>
      if n' = n ∧ w' = w ∧ lanes.length = n ∧ n * w % 8 = 0 then
        some { s with mem := writeBytes s.mem addr (natToBytes (packLanes lanes) (n * w / 8)) }
      else none
  | _, _ => none

/-- Evaluate a call's argument list.  Types are carried by the syntax but not
checked here; a mismatch is the caller's problem, as in the rest of the
useless-width checks in `evalInstr`. -/
def evalOperands (s : State) : List (Ty × Operand) → Option (List Value)
  | [] => some []
  | (_, op) :: rest =>
      match evalOperand s op, evalOperands s rest with
      | some v, some vs => some (v :: vs)
      | _, _ => none

/-- Execute one instruction. -/
def evalInstr (calls : Calls) (s : State) : Instr → Option State
  | .binop d op w a b =>
      match evalOperand s a, evalOperand s b with
      | some va, some vb =>
          match va.intToNat w, vb.intToNat w with
          | some x, some y =>
              match evalBinopNat op w x y with
              | some r => some (s.bind d (.int w (BitVec.ofNat w r)))
              | none => none
          | _, _ => none
      | _, _ => none
  | .icmp d pred w a b =>
      match evalOperand s a, evalOperand s b with
      | some va, some vb =>
          match va.intToNat w, vb.intToNat w with
          | some x, some y => some (s.bind d (.int 1 (evalICmpNat pred w x y)))
          | _, _ => none
      | _, _ => none
  | .icmpPtr d pred a b =>
      -- Both operands must read as pointers.  A mixed pair is `none` here; the
      -- parser refuses that text, so it is reachable only from an AST built
      -- without the parser, where no type table exists to decide it.
      match evalOperand s a, evalOperand s b with
      | some (.ptr x), some (.ptr y) =>
          (evalICmpPtr pred x y).map fun r => s.bind d (.int 1 r)
      | _, _ => none
  | .select d ty c a b =>
      -- Two forms share the constructor and the condition's value decides
      -- between them, so the scalar reading is the one it always was.  A
      -- `<n x i1>` condition selects lane by lane: lane `j` is `a[j]` where the
      -- condition's lane is set and `b[j]` where it is clear.  The result type
      -- fixes the operand shape `<n x iw>`, and a value of any other shape is
      -- `ub` — the parser refuses that text, so it is the hand-built-AST case.
      match evalOperand s c with
      | some (.int 1 bit) =>
          match evalOperand s a, evalOperand s b with
          | some va, some vb =>
              if bit = (1 : BitVec 1) then some (s.bind d va)
              else if bit = (0 : BitVec 1) then some (s.bind d vb)
              else none
          | _, _ => none
      | some (.vec nc 1 cs) =>
          match ty with
          | .vec n (.int w) =>
              if nc = n then
                match evalOperand s a, evalOperand s b with
                | some va, some vb =>
                    match va.vecLanes n w, vb.vecLanes n w with
                    | some la, some lb =>
                        some (s.bind d (.vec n w (selectLanes cs la lb)))
                    | _, _ => none
                | _, _ => none
              else none
          | _ => none
      | _ => none
  | .trunc d wIn wOut v =>
      match evalOperand s v with
      | some (.int w' x) =>
          if w' = wIn then
            some (s.bind d (.int wOut (BitVec.ofNat wOut (x.toNat % 2 ^ wOut))))
          else none
      | _ => none
  | .zext d wIn wOut v =>
      match evalOperand s v with
      | some (.int w' x) =>
          if w' = wIn then
            some (s.bind d (.int wOut (BitVec.ofNat wOut x.toNat)))
          else none
      | _ => none
  | .sext d wIn wOut v =>
      match evalOperand s v with
      | some (.int w' x) =>
          if w' = wIn then
            some (s.bind d (.int wOut (BitVec.ofNat wOut (BitVec.signExtend wOut (BitVec.ofNat wIn x.toNat)).toNat)))
          else none
      | _ => none
  | .alloca d ty _align =>
      some { s with env := (d, .ptr s.next) :: s.env, next := s.next + ty.sizeBytes }
  | .load d ty p =>
      match evalOperand s p with
      | some (.ptr addr) =>
          match loadValue s.mem ty addr with
          | some v => some (s.bind d v)
          | none => none
      | _ => none
  | .store ty v p =>
      match evalOperand s v, evalOperand s p with
      | some vv, some (.ptr addr) => storeValue s ty vv addr
      | _, _ => none
  | .gep d elemTy base off =>
      -- The index is sign-extended to 64 bits and read as signed, so the step has
      -- two accepting cases: a value below `2 ^ 63` is added, and a value at or
      -- above it is subtracted — its magnitude is `2 ^ 64 - v` and its
      -- displacement is that magnitude scaled by the element type's size.  What
      -- is undefined is an address that would leave the address space below zero,
      -- not the index's sign: a displacement larger than the base is refused,
      -- because pointers are bare addresses with no object to bound the walk.
      -- The index's declared width is not part of the instruction, so the value
      -- read supplies it.  The step is scaled by the element type's size, so
      -- `getelementptr i32` adds four bytes per index step and `getelementptr
      -- i8` — the byte count the earlier form expressed — adds one; the type is
      -- an integer for every `gep` the parser produces, and `sizeBytes` is the
      -- model's `sizeof` for the other types as well.
      match evalOperand s base, evalOperand s off with
      | some (.ptr addr), some (.int _ n) =>
          if (n.signExtend 64).toNat < 2 ^ 63 then
            some (s.bind d (.ptr (addr + (n.signExtend 64).toNat * elemTy.sizeBytes)))
          else if (2 ^ 64 - (n.signExtend 64).toNat) * elemTy.sizeBytes ≤ addr then
            some (s.bind d (.ptr (addr - (2 ^ 64 - (n.signExtend 64).toNat) * elemTy.sizeBytes)))
          else none
      | _, _ => none
  | .call d _ callee args =>
      match evalOperands s args with
      | some vs =>
          match calls callee vs s.mem s.next with
          | some r => some { s with env := (d, r.ret) :: s.env, mem := r.mem, next := r.next }
          | none => none
      | none => none
  | .callVoid callee args =>
      -- A void call binds nothing, so the environment is untouched: the value
      -- the callee leaves has no name in the caller and is discarded, and only
      -- its memory and allocator state are adopted.
      match evalOperands s args with
      | some vs =>
          match calls callee vs s.mem s.next with
          | some r => some { s with mem := r.mem, next := r.next }
          | none => none
      | none => none
  | .icmpVec d pred n w a b =>
      match evalOperand s a, evalOperand s b with
      | some va, some vb =>
          match va.vecLanes n w, vb.vecLanes n w with
          | some l₁, some l₂ =>
              some (s.bind d (.vec n 1 ((l₁.zip l₂).map fun (x, y) => evalICmp pred x y)))
          | _, _ => none
      | _, _ => none
  | .binopVec d op n w a b =>
      match evalOperand s a, evalOperand s b with
      | some va, some vb =>
          match va.vecLanes n w, vb.vecLanes n w with
          | some l₁, some l₂ =>
              match (l₁.zip l₂).mapM (fun (x, y) => evalBinop op x y) with
              | some ls => some (s.bind d (.vec n w ls))
              | none => none
          | _, _ => none
      | _, _ => none
  | .bitcastMask d n v =>
      match evalOperand s v with
      | some (.vec n' 1 l) =>
          if n' = n ∧ l.length = n then
            some (s.bind d (.int n (BitVec.ofNat n (lanesToNat l))))
          else none
      | _ => none
  | .extractelement d n w v idx =>
      -- A lane read.  The index is read as an unsigned count — the width it was
      -- written at is not part of the instruction — and one outside the vector's
      -- lane range is `none`.  LLVM calls that poison, and this model has no
      -- poison: `Const.toValue` answers a `poison` or `undef` literal the same
      -- way, so an out-of-range read is undefined behaviour rather than a lane
      -- the compiler may choose.
      match evalOperand s v, evalOperand s idx with
      | some vv, some (.int _ k) =>
          match vv.vecLanes n w with
          | some lanes =>
              match lanes[k.toNat]? with
              | some x => some (s.bind d (.int w x))
              | none => none
          | none => none
      | _, _ => none
  | .insertelement d n w v elt idx =>
      -- A lane write, and the same rule for an index outside the range.  The
      -- vector operand must be a `<n x iw>` value and the element an `iw`
      -- integer; the parser fixes both from the text, so a disagreement here is
      -- the hand-built-AST case and is undefined behaviour rather than a cell
      -- left alone.
      match evalOperand s v, evalOperand s elt, evalOperand s idx with
      | some vv, some ev, some (.int _ k) =>
          match vv.vecLanes n w, ev.intToNat w with
          | some lanes, some x =>
              if k.toNat < lanes.length then
                some (s.bind d (.vec n w (lanes.set k.toNat (BitVec.ofNat w x))))
              else none
          | _, _ => none
      | _, _, _ => none
  | .shuffleVec d n w a b mask =>
      -- A static permutation: mask entry `k` reads lane `k` of the first
      -- operand when `k < n` and lane `k - n` of the second below `2n`.  An
      -- entry outside that range is poison in LLVM and `ub` here; the parser
      -- refuses one, so it is reachable only from a hand-built AST.
      match evalOperand s a, evalOperand s b with
      | some va, some vb =>
          match va.vecLanes n w, vb.vecLanes n w with
          | some l₁, some l₂ =>
              let pick (k : Nat) : Option (BitVec w) :=
                if k < n then l₁[k]? else l₂[k - n]?
              match mask.mapM pick with
              | some ls => some (s.bind d (.vec mask.length w ls))
              | none => none
          | _, _ => none
      | _, _ => none
  | .vecBitcast d n w m jw v =>
      -- A reinterpretation at equal total width.  The element sizes may
      -- differ; a width disagreement is `ub` (the parser refuses the text), and
      -- a value that is not a vector of the instruction's shape is `ub` too.
      match evalOperand s v with
      | some vv =>
          match vv.vecLanes n w with
          | some lanes =>
              if n * w = m * jw then
                some (s.bind d (.vec m jw (bitcastVecLanes jw m lanes)))
              else none
          | none => none
      | none => none
  | .phi d _ty inc =>
      -- Selection reads the predecessor field, which only a jump writes.  With
      -- no predecessor — the entry block — nothing can match, and an incoming
      -- list without an entry for the predecessor the edge actually came from
      -- is undefined behaviour: LLVM's verifier refuses such a module, and a
      -- runtime-only `none` cannot admit a behaviour LLVM forbids.  The
      -- instruction's type is not consulted: the selected operand evaluates to
      -- its own value, and the parser has already refused a mismatch.
      --
      -- This is one member of a leading run read in isolation.  A block's run
      -- is a stronger step than this constructor: `phiGroup` gives every member
      -- the same snapshot state, so no member reads a destination a sibling
      -- bound.  `evalInstr` remains the instruction's meaning for a `phi` that
      -- is not part of such a run — a list the parser refuses — and the
      -- semantics of a well-formed block's run is `denoteCode`'s, below.
      (phiSelect s inc).map fun v => s.bind d v

/-! ### Pointer comparison

The accepting case, and the two facts the rest of the development consumes: the
destination is bound to a one-bit value and the memory is untouched.  An operand
that is not a pointer is `none`, which is the hand-built-AST case; the parser
refuses that text. -/

/-- Two pointer operands compare to the predicate's result on their addresses. -/
theorem evalInstr_icmpPtr {calls : Calls} {s : State} {d : String} {pr : IPred}
    {a b : Operand} {x y : Nat} {r : BitVec 1}
    (ha : evalOperand s a = some (.ptr x)) (hb : evalOperand s b = some (.ptr y))
    (hr : evalICmpPtr pr x y = some r) :
    evalInstr calls s (.icmpPtr d pr a b) = some (s.bind d (.int 1 r)) := by
  simp [evalInstr, ha, hb, hr]

/-- Executing a pointer comparison leaves the memory alone: it binds a one-bit
value and writes nothing. -/
theorem evalInstr_icmpPtr_mem {calls : Calls} {s s' : State} {d : String}
    {pr : IPred} {a b : Operand}
    (h : evalInstr calls s (.icmpPtr d pr a b) = some s') : s'.mem = s.mem := by
  simp only [evalInstr] at h
  split at h
  · simp only [Option.map] at h
    split at h
    all_goals (cases h <;> rfl)
  · cases h

/-! ### The pointer offset

`getelementptr`'s step, as facts a later proof composes with: the forward
accepting case, the backward one, the displacement that would leave the address
space below zero and is refused, the operand shapes it refuses, and the memory it
leaves alone.  A refused offset is `none` here; `none` is read as the `ub`
outcome by `step`, and nothing in this module decides that.

The index is read as **signed**, and the step has two directions: a sign-extended
value below `2 ^ 63` is added, and one at or above it is subtracted.  The
subtraction's **magnitude** is `2 ^ 64 - v` and its **displacement** is that
magnitude scaled by the element type's size, which is the byte count the base is
compared with.  The bound is on the address, not on the index: the subtraction is
defined only while the displacement does not exceed the base, and it is refused
above that, since the result would leave the address space below zero.  Neither
direction touches memory — a `getelementptr` binds a register — so no address
becomes readable that was not readable before.

The index's **width** is not checked by this step — it sign-extends whatever
integer value it reads to 64 bits, and a value wider than 64 bits would be
truncated to 64.  An index type wider than 64 bits is refused by the parser, so a
module that came through it never reaches this step with one.

The step is **scaled** by the element type's size: it adds `off * sizeof(elemTy)`
rather than `off`.  The accepting case below states the scaled form, and
`evalInstr_gep_i8` restates it at the element type the earlier model fixed, where
`sizeof(i8)` is one and the scaled form is the byte count it used to add.
-/

/-- The accepting case: a pointer base and an integer index whose sign-extended
value is below `2 ^ 63` bind the destination to the base plus the index scaled by
the element type's size. -/
theorem evalInstr_gep {calls : Calls} {s : State} {d : String} {elemTy : Ty}
    {base off : Operand} {a w : Nat} {n : BitVec w}
    (hb : evalOperand s base = some (.ptr a))
    (ho : evalOperand s off = some (.int w n)) (hpos : (n.signExtend 64).toNat < 2 ^ 63) :
    evalInstr calls s (.gep d elemTy base off) =
      some (s.bind d (.ptr (a + (n.signExtend 64).toNat * elemTy.sizeBytes))) := by
  simp only [evalInstr, hb, ho]
  rw [ite_eq_left hpos]

/-- The step at an `i8` element type: one byte per index step, which is exactly
the address the byte-offset model computed before the element type was a field.
This is the form every pre-existing `getelementptr i8` statement and pin is
restated at, so their meaning is unchanged. -/
theorem evalInstr_gep_i8 {calls : Calls} {s : State} {d : String}
    {base off : Operand} {a w : Nat} {n : BitVec w}
    (hb : evalOperand s base = some (.ptr a))
    (ho : evalOperand s off = some (.int w n)) (hpos : (n.signExtend 64).toNat < 2 ^ 63) :
    evalInstr calls s (.gep d (.int 8) base off) =
      some (s.bind d (.ptr (a + (n.signExtend 64).toNat))) := by
  rw [evalInstr_gep hb ho hpos]
  simp [Ty.sizeBytes]

/-- The backward accepting case: a sign-extended index at or above `2 ^ 63` whose
displacement `k * sizeof(elemTy)` — `k` being the magnitude `2 ^ 64 - v` — does
not exceed the base binds the destination to the base minus that displacement.
`hk` is the whole of the address arithmetic's definedness: the result is a `Nat`
and `(a - k * sizeof(elemTy)) + k * sizeof(elemTy) = a`, so the address does not
wrap below zero.  The memory is untouched, which `evalInstr_gep_mem` states for
every accepted `getelementptr` and therefore for this branch unchanged. -/
theorem evalInstr_gep_back {calls : Calls} {s : State} {d : String} {elemTy : Ty}
    {base off : Operand} {a w : Nat} {n : BitVec w}
    (hb : evalOperand s base = some (.ptr a))
    (ho : evalOperand s off = some (.int w n))
    (hneg : ¬ (n.signExtend 64).toNat < 2 ^ 63)
    (hk : (2 ^ 64 - (n.signExtend 64).toNat) * elemTy.sizeBytes ≤ a) :
    evalInstr calls s (.gep d elemTy base off) =
      some (s.bind d (.ptr (a - (2 ^ 64 - (n.signExtend 64).toNat) * elemTy.sizeBytes))) := by
  simp only [evalInstr, hb, ho]
  rw [ite_eq_right hneg, ite_eq_left hk]

/-- The refusal that remains: a negative index whose displacement exceeds the
base would take the address below zero, which this model does not define.  The
index's sign alone is no longer the defect — that is the conflation this step
used to make — and the element type enters through the displacement, so one index
can be admitted at one element type and refused at another: `-1` from a base of
`1` is address `0` at `i8` and refused at `i32`, where one step is four bytes. -/
theorem evalInstr_gep_negative {calls : Calls} {s : State} {d : String} {elemTy : Ty}
    {base off : Operand} {a w : Nat} {n : BitVec w}
    (hb : evalOperand s base = some (.ptr a))
    (ho : evalOperand s off = some (.int w n))
    (hneg : ¬ (n.signExtend 64).toNat < 2 ^ 63)
    (hunder : a < (2 ^ 64 - (n.signExtend 64).toNat) * elemTy.sizeBytes) :
    evalInstr calls s (.gep d elemTy base off) = none := by
  simp only [evalInstr, hb, ho]
  rw [ite_eq_right hneg, ite_eq_right (Nat.not_le.mpr hunder)]

/-- A base that is not a pointer is refused, whatever the index is. -/
theorem evalInstr_gep_none_of_base {calls : Calls} {s : State} {d : String}
    {elemTy : Ty} {base off : Operand} {v : Value} (hb : evalOperand s base = some v)
    (hv : ∀ a, v ≠ .ptr a) : evalInstr calls s (.gep d elemTy base off) = none := by
  simp only [evalInstr, hb]
  cases v with
  | ptr a => exact absurd rfl (hv a)
  | int w x => rfl
  | vec n w l => rfl

/-- An index that is not an integer is refused, a pointer base or not: a pointer
offset by a pointer has no meaning here. -/
theorem evalInstr_gep_none_of_off {calls : Calls} {s : State} {d : String}
    {elemTy : Ty} {base off : Operand} {a : Nat} (hb : evalOperand s base = some (.ptr a))
    {v : Value} (ho : evalOperand s off = some v) (hv : ∀ w n, v ≠ .int w n) :
    evalInstr calls s (.gep d elemTy base off) = none := by
  cases v with
  | int w x => exact absurd rfl (hv w x)
  | ptr b => simp only [evalInstr, hb, ho]
  | vec n w l => simp only [evalInstr, hb, ho]

/-- An operand that does not read — an unbound register, an `undef` or `poison`
literal — is refused before either value shape is examined. -/
theorem evalInstr_gep_none_of_unbound {calls : Calls} {s : State} {d : String}
    {elemTy : Ty} {base off : Operand}
    (h : evalOperand s base = none ∨ evalOperand s off = none) :
    evalInstr calls s (.gep d elemTy base off) = none := by
  rcases h with h | h
  · simp only [evalInstr, h]
  · simp only [evalInstr, h]
    cases hb : evalOperand s base with
    | none => rfl
    | some v => cases v <;> rfl

/-- A pointer offset writes nothing: a successful step leaves the memory as it
found it, and only the destination binding changes. -/
theorem evalInstr_gep_mem {calls : Calls} {s s' : State} {d : String} {elemTy : Ty}
    {base off : Operand}
    (h : evalInstr calls s (.gep d elemTy base off) = some s') : s'.mem = s.mem := by
  simp only [evalInstr] at h
  repeat' split at h
  all_goals (cases h <;> rfl)

/-! ### Lane access

The accepting case of each lane instruction and the refusal its out-of-range
index gets.  Together they are the statement that a lane read returns *that*
lane, and that an index the vector does not have is undefined behaviour rather
than a lane the compiler may pick: LLVM calls the latter poison, and this model
has no poison, so it answers `none`, exactly as it does for a `poison` literal.
-/

/-- A lane index at or past the list's length names no lane.  This is the step
from "the index is outside the vector's lane range" to the read's refusal, so the
theorems below can be stated at the range rather than at the lookup. -/
theorem laneList_getElem?_eq_none {α : Type} {l : List α} {i : Nat} (h : l.length ≤ i) :
    l[i]? = none := by
  induction l generalizing i with
  | nil => rfl
  | cons a as ih =>
      cases i with
      | zero => simp at h
      | succ j => simp [ih (by simpa using h)]

/-- A lane read inside the range binds the lane the index names. -/
theorem evalInstr_extractelement {calls : Calls} {s : State} {d : String}
    {n w : Nat} {v idx : Operand} {vv : Value} {lanes : List (BitVec w)}
    {wi : Nat} {k : BitVec wi} {x : BitVec w}
    (hv : evalOperand s v = some vv) (hl : vv.vecLanes n w = some lanes)
    (hi : evalOperand s idx = some (.int wi k)) (hx : lanes[k.toNat]? = some x) :
    evalInstr calls s (.extractelement d n w v idx) = some (s.bind d (.int w x)) := by
  simp [evalInstr, hv, hl, hi, hx]

/-- A lane read at or past the lane count is undefined behaviour.  The hypothesis
is the range condition on the lanes the operand's value yields; `vecLanes` returns
a list of exactly `n` lanes, so it says `n ≤ index`.  The instruction's index
width is irrelevant to it, which is why the width is not a field. -/
theorem evalInstr_extractelement_out_of_range {calls : Calls} {s : State} {d : String}
    {n w : Nat} {v idx : Operand} {vv : Value} {lanes : List (BitVec w)}
    {wi : Nat} {k : BitVec wi}
    (hv : evalOperand s v = some vv) (hl : vv.vecLanes n w = some lanes)
    (hi : evalOperand s idx = some (.int wi k)) (hge : lanes.length ≤ k.toNat) :
    evalInstr calls s (.extractelement d n w v idx) = none := by
  simp [evalInstr, hv, hl, hi, laneList_getElem?_eq_none hge]

/-- A lane write inside the range binds the vector with that lane replaced and
the others as they were. -/
theorem evalInstr_insertelement {calls : Calls} {s : State} {d : String}
    {n w : Nat} {v elt idx : Operand} {vv ev : Value} {lanes : List (BitVec w)}
    {wi x : Nat} {k : BitVec wi}
    (hv : evalOperand s v = some vv) (hl : vv.vecLanes n w = some lanes)
    (he : evalOperand s elt = some ev) (hx : ev.intToNat w = some x)
    (hi : evalOperand s idx = some (.int wi k)) (hk : k.toNat < lanes.length) :
    evalInstr calls s (.insertelement d n w v elt idx) =
      some (s.bind d (.vec n w (lanes.set k.toNat (BitVec.ofNat w x)))) := by
  simp [evalInstr, hv, hl, he, hx, hi, hk]

/-- A lane write at or past the lane count is undefined behaviour, the same rule
as the lane read's. -/
theorem evalInstr_insertelement_out_of_range {calls : Calls} {s : State} {d : String}
    {n w : Nat} {v elt idx : Operand} {vv ev : Value} {lanes : List (BitVec w)}
    {wi x : Nat} {k : BitVec wi}
    (hv : evalOperand s v = some vv) (hl : vv.vecLanes n w = some lanes)
    (he : evalOperand s elt = some ev) (hx : ev.intToNat w = some x)
    (hi : evalOperand s idx = some (.int wi k)) (hge : lanes.length ≤ k.toNat) :
    evalInstr calls s (.insertelement d n w v elt idx) = none := by
  simp [evalInstr, hv, hl, he, hx, hi, Nat.not_lt.mpr hge]

/-- A `phi` of a block's leading run: its destination, result type and incoming
list.  The type is carried so a run's instructions can be named exactly as the
block wrote them; selection does not consult it. -/
structure PhiSpec where
  dst : String
  ty : Ty
  incoming : List (String × Operand)

/-- The instruction a spec describes. -/
def PhiSpec.instr (p : PhiSpec) : Instr := .phi p.dst p.ty p.incoming

/-- Whether a list begins with a `phi`.  A block's leading `phi` run is one step
of `denoteCode`, so the instruction after the run is a step only once the run is
over; this predicate is that fact, in a form `decide` and `rfl` close. -/
def startsWithPhi : List Instr → Bool
  | .phi .. :: _ => true
  | _ => false

/-- The bindings a leading `phi` run selects, one entry per spec in the order the
block writes them, with every operand read from the one state `s`.

This is the run's contract.  A member's operand may name the destination of a
sibling — a swap or a cycle — and that is valid LLVM: the incoming uses happen
on the predecessor edge, where none of the block's new destinations exists yet.
Reading every member at `s` is what makes the run order-independent. -/
inductive PhiSelects (s : State) (p : String) :
    List PhiSpec → List (String × Value) → Prop
  | nil : PhiSelects s p [] []
  | cons {sp : PhiSpec} {specs : List PhiSpec} {vs : List (String × Value)}
      {op : Operand} {v : Value} :
      phiIncoming p sp.incoming = some op →
      evalOperand s op = some v →
      PhiSelects s p specs vs →
      PhiSelects s p (sp :: specs) ((sp.dst, v) :: vs)

/-- Execute a block's instructions from `s`.

The block's leading `phi` run is one step.  `pend` holds the bindings the run
has selected so far, in the order the block writes them, and `s` is untouched
while it is collected: every member reads the environment the edge carried in.
When the run ends — at the first instruction that is not a `phi`, or at the end
of the list — the bindings are installed together and execution continues from
the resulting environment.

A `phi` that does not belong to the leading run is malformed LLVM: the parser
refuses a `phi` that follows a non-`phi`, and SSA gives it no defined meaning.
Such a `phi` is executed by `evalInstr`, exactly as before, so the malformed
input policy is unchanged; what changed is the meaning of the leading run, which
is valid LLVM and now reads one snapshot. -/
def denoteRun (calls : Calls) : List (String × Value) → List Instr → State → Option State
  | pend, [], s => some (s.bindAll pend)
  | pend, .phi d _ty inc :: is, s =>
      match phiSelect s inc with
      | some v => denoteRun calls (pend ++ [(d, v)]) is s
      | none => none
  | pend, i :: is, s =>
      match evalInstr calls (s.bindAll pend) i with
      | some s' => denoteRun calls [] is s'
      | none => none

/-- Execute a straight-line instruction sequence. -/
def denoteCode (calls : Calls) (is : List Instr) (s : State) : Option State :=
  denoteRun calls [] is s

@[simp] theorem denoteCode_nil (calls : Calls) (s : State) :
    denoteCode calls [] s = some s := rfl

/-- `denoteRun` at an instruction that is not a `phi`: the pending run's bindings
are installed, the instruction runs, and the rest of the block follows. -/
theorem denoteRun_cons_of {calls : Calls} {pend : List (String × Value)}
    {i : Instr} {is : List Instr} {s : State} (hi : i.isPhi = false) :
    denoteRun calls pend (i :: is) s =
      match evalInstr calls (s.bindAll pend) i with
      | some s' => denoteRun calls [] is s'
      | none => none := by
  cases i <;> simp_all [denoteRun, Instr.isPhi, State.bindAll]

/-- One instruction, when it is not a `phi`: the block steps through it. -/
theorem denoteCode_cons_of (calls : Calls) (i : Instr) (is : List Instr)
    (s s' : State) (h : evalInstr calls s i = some s')
    (hi : i.isPhi = false := by rfl) :
    denoteCode calls (i :: is) s = denoteCode calls is s' := by
  rw [denoteCode, denoteRun_cons_of hi]
  simp only [State.bindAll, h, denoteCode]

/-- One instruction that is not a `phi` and is undefined makes the block
undefined. -/
theorem denoteCode_cons_none (calls : Calls) (i : Instr) (is : List Instr)
    (s : State) (h : evalInstr calls s i = none)
    (hi : i.isPhi = false := by rfl) :
    denoteCode calls (i :: is) s = none := by
  rw [denoteCode, denoteRun_cons_of hi]
  simp only [State.bindAll, h]

/-- A `phi` whose predecessor is listed and whose selected operand reads selects
its value: the accepting case of one member of a run. -/
theorem phiSelect_eq {s : State} {p : String} {inc : List (String × Operand)}
    {op : Operand} {v : Value} (hpre : s.pre = some p)
    (hinc : phiIncoming p inc = some op) (hop : evalOperand s op = some v) :
    phiSelect s inc = some v := by
  simp [phiSelect, hpre, hinc, hop]

/-- A block's leading `phi` run is one step: one snapshot in, all bindings out. -/
theorem denoteRun_phiRun {calls : Calls} {s : State} {p : String}
    {specs : List PhiSpec} {vs : List (String × Value)} {rest : List Instr}
    {pend : List (String × Value)}
    (hpre : s.pre = some p) (hsel : PhiSelects s p specs vs) :
    denoteRun calls pend (specs.map PhiSpec.instr ++ rest) s =
      denoteRun calls (pend ++ vs) rest s := by
  induction hsel generalizing pend with
  | nil => simp
  | cons hinc hop _ ih =>
      simp only [List.map_cons, List.cons_append, PhiSpec.instr, denoteRun,
        phiSelect_eq hpre hinc hop, Option.some.injEq]
      rw [ih, List.append_assoc, List.singleton_append]

/-- A list that does not begin with a `phi` begins with something `denoteRun`
steps through, so the predicate is the instruction's own. -/
theorem startsWithPhi_cons {i : Instr} {is : List Instr}
    (h : startsWithPhi (i :: is) = false) : i.isPhi = false := by
  cases i <;> simp_all [startsWithPhi, Instr.isPhi]

/-- A completed leading run installs its bindings and execution resumes from
them: the block's snapshot is not visible to anything after the run. -/
theorem denoteRun_nil_pend {calls : Calls} {pend : List (String × Value)}
    {rest : List Instr} {s : State} (h : startsWithPhi rest = false) :
    denoteRun calls pend rest s = denoteRun calls [] rest (s.bindAll pend) := by
  cases rest with
  | nil => rfl
  | cons i is =>
      have hi : i.isPhi = false := startsWithPhi_cons h
      rw [denoteRun_cons_of hi, denoteRun_cons_of hi]
      rfl

/-- A block's leading `phi` run, stated at `denoteCode`: every selected operand
is read from the state the edge delivered, and the bindings land together. -/
theorem denoteCode_phiRun {calls : Calls} {s : State} {p : String}
    {specs : List PhiSpec} {vs : List (String × Value)} {rest : List Instr}
    (hpre : s.pre = some p) (hsel : PhiSelects s p specs vs)
    (hrest : startsWithPhi rest = false) :
    denoteCode calls (specs.map PhiSpec.instr ++ rest) s =
      denoteCode calls rest (s.bindAll vs) := by
  rw [denoteCode, denoteRun_phiRun hpre hsel, List.nil_append]
  rw [denoteRun_nil_pend hrest]
  rfl

/-! ### The `phi` selection

Four facts about one `phi` read in isolation, each a closed statement about
`evalInstr` rather than a restatement of it: the entry whose label is the
predecessor is the one that is read, a `phi` in a block with no predecessor
selects nothing, a `phi` whose list omits the predecessor is undefined, and
neither shape writes memory.  The block's leading run is a stronger step, stated
above: `denoteCode_phiRun`.
-/

/-- A `phi` reached from block `p` whose incoming list names `p` binds the
destination to what that entry's operand evaluates to, whatever the other
entries are. -/
theorem evalInstr_phi {calls : Calls} {s : State} {d : String} {ty : Ty}
    {inc : List (String × Operand)} {p : String} {op : Operand} {v : Value}
    (hpre : s.pre = some p) (hinc : phiIncoming p inc = some op)
    (hop : evalOperand s op = some v) :
    evalInstr calls s (.phi d ty inc) = some (s.bind d v) := by
  simp only [evalInstr, phiSelect_eq hpre hinc hop, Option.map_some]

/-- A `phi` in a block that was not entered from anywhere — the entry block —
selects nothing, because `initState` leaves the predecessor `none` and no
incoming entry can name `none`.  This is undefined behaviour: the module is one
LLVM's verifier refuses, and a program that reached it would be one the model
runs with a meaning LLVM does not give it. -/
theorem evalInstr_phi_no_pred {calls : Calls} {s : State} {d : String} {ty : Ty}
    {inc : List (String × Operand)} (h : s.pre = none) :
    evalInstr calls s (.phi d ty inc) = none := by
  simp [evalInstr, phiSelect, h]

/-- A `phi` whose incoming list has no entry for the block the edge came from is
undefined behaviour: `none`, which `step` reads as `ub`. -/
theorem evalInstr_phi_missing {calls : Calls} {s : State} {d : String} {ty : Ty}
    {inc : List (String × Operand)} {p : String} (hpre : s.pre = some p)
    (hinc : phiIncoming p inc = none) :
    evalInstr calls s (.phi d ty inc) = none := by
  simp only [evalInstr, phiSelect, hpre] at *
  rw [hinc]
  rfl

/-- Selecting an incoming value writes no memory: the step binds one register and
changes nothing else. -/
theorem evalInstr_phi_mem {calls : Calls} {s s' : State} {d : String} {ty : Ty}
    {inc : List (String × Operand)}
    (h : evalInstr calls s (.phi d ty inc) = some s') : s'.mem = s.mem := by
  simp only [evalInstr] at h
  cases hs : phiSelect s inc with
  | none => simp only [hs] at h; cases h
  | some v =>
      simp only [hs, Option.map_some, Option.some.injEq] at h
      subst h
      rfl

/-- A group whose first member has no selection has no selection either: the
run's failure is the whole step's.  Stated for `denoteRun` at the run's head. -/
theorem denoteRun_phi_none {calls : Calls} {pend : List (String × Value)}
    {d : String} {ty : Ty} {inc : List (String × Operand)} {is : List Instr}
    {s : State} (h : phiSelect s inc = none) :
    denoteRun calls pend (.phi d ty inc :: is) s = none := by
  simp only [denoteRun, h]

/-- Installing a group's bindings moves no memory. -/
theorem State.bindAll_mem (s : State) (bs : List (String × Value)) :
    (s.bindAll bs).mem = s.mem := by
  induction bs generalizing s with
  | nil => rfl
  | cons b rest ih =>
      obtain ⟨n, v⟩ := b
      simp only [State.bindAll, State.bind]
      exact ih (s.bind n v)

/-- Installing a group's bindings leaves the program counter where it was:
binding a register rewrites the environment alone. -/
theorem State.bindAll_pc (s : State) (bs : List (String × Value)) :
    (s.bindAll bs).pc = s.pc := by
  induction bs generalizing s with
  | nil => rfl
  | cons b rest ih => exact ih (s.bind b.1 b.2)

/-- A block's leading `phi` run moves no memory: selecting and installing
bindings leaves the memory and the allocator where they were. -/
theorem denoteRun_phi_mem {calls : Calls} :
    ∀ (pend : List (String × Value)) (is : List Instr) (s s' : State),
      (∀ i ∈ is, i.isPhi = true) →
      denoteRun calls pend is s = some s' → s'.mem = s.mem := by
  intro pend is
  induction is generalizing pend with
  | nil =>
      intro s s' _ h
      simp only [denoteRun, Option.some.injEq] at h
      subst h
      exact State.bindAll_mem s pend
  | cons i rest ih =>
      intro s s' hall h
      have hrest : ∀ j ∈ rest, j.isPhi = true :=
        fun j hj => hall j (List.mem_cons_of_mem _ hj)
      cases i with
      | phi dst ty inc =>
          cases hs : phiSelect s inc with
          | none => simp only [denoteRun, hs] at h; cases h
          | some v =>
              simp only [denoteRun, hs] at h
              exact ih _ s s' hrest h
      | _ =>
          have hi : Instr.isPhi _ = true := hall _ (List.mem_cons_self ..)
          simp only [Instr.isPhi] at hi
          cases hi

/-- The effect of a terminator. -/
inductive Ctrl where
  | ub
  | ret (v : Option Value) (s : State)
  | jump (s : State)
  deriving Repr

/-- Carry a state's predecessor field into a control result.  A `ret` keeps the
field: nothing after it overwrites it.  A `jump` does not, and that asymmetry is
the whole reason the non-interference theorem holds: the jump sets the field
from the block the edge came *from*, so whatever the state arrived with is gone
by the time the successor block's `phi` reads it. -/
def Ctrl.setPre (p : Option String) : Ctrl → Ctrl
  | .ub => .ub
  | .ret v s => .ret v (s.setPre p)
  | .jump s => .jump s

/-- Two control results agree outside the predecessor: the same constructor, the
same returned value, and post-states that agree outside the field.  The `ret`
arm keeps the returned value, which is what makes the relation enough for
`Outcome`, where no predecessor is observable. -/
def Ctrl.SameExceptPre : Ctrl → Ctrl → Prop
  | .ub, .ub => True
  | .ret v s, .ret w t => v = w ∧ State.SameExceptPre s t
  | .jump s, .jump t => State.SameExceptPre s t
  | _, _ => False

/-- Replacing a control result's predecessor with any value leaves the result
agreeing outside the field.  A jumped state is untouched — the field it carries
is the one the jump itself set — so it agrees with itself outright. -/
theorem Ctrl.sameExceptPre_setPre (c : Ctrl) (q : Option String) :
    Ctrl.SameExceptPre c (c.setPre q) := by
  cases c with
  | ub => trivial
  | ret v s => exact ⟨rfl, State.sameExceptPre_refl s⟩
  | jump s => exact State.sameExceptPre_refl s

/-- Execute a terminator in a state.

A jump is the only transition that writes the predecessor field, and it writes
the block it came from: `s.pc` is still the block being left, because the
instruction sequence does not change it. -/
def execTerm (s : State) : Term → Ctrl
  | .ret .void none => .ret none s
  | .ret .void (some _) => .ub
  | .ret _ none => .ub
  | .ret _ (some v) =>
      match evalOperand s v with
      | some x => .ret (some x) s
      | none => .ub
  | .br dest => .jump { s with pc := dest, pre := some s.pc }
  | .condbr c t f =>
      match evalOperand s c with
      | some (.int 1 bit) =>
          if bit = (1 : BitVec 1) then .jump { s with pc := t, pre := some s.pc }
          else if bit = (0 : BitVec 1) then .jump { s with pc := f, pre := some s.pc }
          else .ub
      | _ => .ub
  | .unreachable => .ub

/-- One control step of a function. -/
def step (calls : Calls) (f : Function) (s : State) : Ctrl :=
  match f.findBlock s.pc with
  | none => .ub
  | some b =>
      match denoteCode calls b.instrs s with
      | none => .ub
      | some s' => execTerm s' b.term

/-- The observable result of a completed run. -/
inductive Outcome where
  | ub
  | ret (v : Option Value) (mem : Mem)
  deriving DecidableEq, Repr

/-- Run for at most `n` control steps.  `none` means the fuel ran out. -/
def runFuel (calls : Calls) : Nat → Function → State → Option Outcome
  | 0, _, _ => none
  | n + 1, f, s =>
      match step calls f s with
      | .ub => some .ub
      | .ret v s' => some (.ret v s'.mem)
      | .jump s' => runFuel calls n f s'

/-- A completed run keeps its outcome with one more step of fuel: the outcome
was produced by a prefix, and the extra step is never taken. -/
theorem runFuel_succ_some {calls : Calls} {f : Function} {s : State} {o : Outcome} :
    ∀ {n : Nat}, runFuel calls n f s = some o → runFuel calls (n + 1) f s = some o
  | 0, h => by
      simp only [runFuel] at h
      cases h
  | n + 1, h => by
      cases hs : step calls f s with
      | ub =>
          simp only [runFuel, hs] at h ⊢
          exact h
      | ret v s' =>
          simp only [runFuel, hs] at h ⊢
          exact h
      | jump s' =>
          simp only [runFuel, hs] at h ⊢
          exact runFuel_succ_some h

/-- Extra fuel does not change a completed run's outcome. -/
theorem runFuel_mono {calls : Calls} {f : Function} {s : State} {o : Outcome}
    {n : Nat} (h : runFuel calls n f s = some o) :
    ∀ {d : Nat}, runFuel calls (n + d) f s = some o
  | 0 => h
  | d + 1 => by
      rw [← Nat.add_assoc]
      exact runFuel_succ_some (runFuel_mono h)

/-- A completed run is completed with the same outcome at any larger budget. -/
theorem runFuel_mono_le {calls : Calls} {f : Function} {s : State} {o : Outcome}
    {n m : Nat} (hmn : n ≤ m) (h : runFuel calls n f s = some o) :
    runFuel calls m f s = some o := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hmn
  exact runFuel_mono h

/-- Two successful runs from the same state produce the same outcome, so the
fuel budget never selects a different result. -/
theorem runFuel_outcome_unique {calls : Calls} {f : Function} {s : State}
    {n m : Nat} {o o' : Outcome} (hn : runFuel calls n f s = some o)
    (hm : runFuel calls m f s = some o') : o = o' := by
  rcases Nat.le_total n m with hle | hle
  · have h1 := runFuel_mono_le hle hn
    rw [h1] at hm
    exact Option.some.inj hm
  · have h1 := runFuel_mono_le hle hm
    rw [h1] at hn
    exact (Option.some.inj hn).symm

/-- **A run prefix composes.**  `runFuel` carries a continuation as its last
argument, so a segment is stated as the equality `runFuel (n + k) f s =
runFuel k f e`: the segment from `s` reaches `e` in `n` control steps and leaves
whatever follows untouched.  Two such segments compose into one, with the fuel
additive and the continuation's own budget carried unchanged. -/
theorem runFuel_prefix_trans {calls : Calls} {f : Function} {s e e' : State}
    {n m : Nat}
    (h1 : ∀ k, runFuel calls (n + k) f s = runFuel calls k f e)
    (h2 : ∀ k, runFuel calls (m + k) f e = runFuel calls k f e') :
    ∀ k, runFuel calls (n + m + k) f s = runFuel calls k f e' := by
  intro k
  rw [Nat.add_assoc, h1 (m + k), h2 k]

/-- **A prefix composed with a completed continuation.**  The run from `s`
reaches `e` within `n` control steps, and the run from `e` completes at `o`
within `m`; the run from `s` therefore completes at the same outcome within
`n + m`.  This is the form a chain of block steps ends in when the exit block's
trace supplies the `some o`. -/
theorem runFuel_prefix_some {calls : Calls} {f : Function} {s e : State}
    {n m : Nat} {o : Outcome}
    (h : ∀ k, runFuel calls (n + k) f s = runFuel calls k f e)
    (he : runFuel calls m f e = some o) :
    runFuel calls (n + m) f s = some o := by
  rw [h m, he]

/-! ### Non-interference

The `phi` constructor reads the state's predecessor field, and a jump writes it.
A function that contains no `phi` therefore cannot observe the field at all: the
step transition carries it into a `ret` result and drops it at a jump, and the
run's outcome carries no field at all.

These statements are the load-bearing evidence that adding `phi` is additive —
every run of a `phi`-free program is unchanged, and that is proved here rather
than asserted.  They are stated at three levels because the claim is needed at
three: one instruction, one control step, and the whole run.
-/

/-- Reading an operand list does not consult the predecessor field. -/
theorem evalOperands_setPre (s : State) (p : Option String)
    (args : List (Ty × Operand)) :
    evalOperands (s.setPre p) args = evalOperands s args := by
  induction args with
  | nil => rfl
  | cons a rest ih =>
      obtain ⟨ty, op⟩ := a
      simp only [evalOperands, evalOperand_setPre, ih]

/-- A store reaches the same result from two states one `setPre` apart, up to the
field: the bytes it writes are the same and only the state's predecessor differs.
-/
theorem storeValue_setPre (s : State) (p : Option String) (ty : Ty) (v : Value)
    (addr : Nat) :
    storeValue (s.setPre p) ty v addr = (storeValue s ty v addr).map (·.setPre p) := by
  cases ty with
  | vec n elem =>
      cases elem <;> cases v <;> simp [storeValue, State.setPre, Option.map_ite]
  | _ => cases v <;> simp [storeValue, State.setPre, Option.map_ite]

/-- A `phi`-free instruction reaches the same result from two states that are one
`setPre` apart, up to the destination binding.  The `phi` case is excluded by the
hypothesis — it is the only constructor that reads the field. -/
theorem evalInstr_setPre {calls : Calls} (i : Instr) (hi : i.isPhi = false)
    (s : State) (p : Option String) :
    evalInstr calls (s.setPre p) i = (evalInstr calls s i).map (·.setPre p) := by
  cases i with
  | phi d ty inc => simp [Instr.isPhi] at hi
  | binop d op w a b =>
      simp only [evalInstr, evalOperand_setPre, State.bind_setPre]
      cases evalOperand s a with
      | none => rfl
      | some va =>
        try dsimp only
        cases evalOperand s b with
        | none => rfl
        | some vb =>
          try dsimp only
          cases va.intToNat w with
          | none => rfl
          | some x =>
            try dsimp only
            cases vb.intToNat w with
            | none => rfl
            | some y =>
              try dsimp only
              cases evalBinopNat op w x y with
              | none => rfl
              | some r => rfl
  | icmp d pred w a b =>
      simp only [evalInstr, evalOperand_setPre, State.bind_setPre]
      cases evalOperand s a with
      | none => rfl
      | some va =>
        try dsimp only
        cases evalOperand s b with
        | none => rfl
        | some vb =>
          try dsimp only
          cases va.intToNat w with
          | none => rfl
          | some x =>
            try dsimp only
            cases vb.intToNat w with
            | none => rfl
            | some y => rfl
  | icmpPtr d pred a b =>
      simp only [evalInstr, evalOperand_setPre, State.bind_setPre]
      cases evalOperand s a with
      | none => rfl
      | some va =>
        cases va with
        | int w x =>
            cases evalOperand s b <;> dsimp only <;> rfl
        | vec n w l =>
            cases evalOperand s b <;> dsimp only <;> rfl
        | ptr addr =>
            cases evalOperand s b with
            | none => rfl
            | some vb =>
              cases vb with
              | int w y => dsimp only; rfl
              | vec n w l => dsimp only; rfl
              | ptr addr2 =>
                dsimp only
                cases evalICmpPtr pred addr addr2 with
                | none => rfl
                | some r => rfl
  | select d ty c a b =>
      simp only [evalInstr, evalOperand_setPre, State.bind_setPre]
      cases evalOperand s c with
      | none => rfl
      | some vc =>
        cases vc with
        | int w cbit =>
          cases w with
          | zero => rfl
          | succ k =>
            cases k with
            | zero =>
              try dsimp only
              cases evalOperand s a with
              | none => rfl
              | some cva =>
                try dsimp only
                cases evalOperand s b with
                | none => rfl
                | some cvb =>
                  try dsimp only
                  simp only []
                  first
                    | rfl
                    | (by_cases h1 : cbit = (1 : BitVec 1)
                       · rw [ite_eq_left h1, ite_eq_left h1]
                         rfl
                       · by_cases h0 : cbit = (0 : BitVec 1)
                         · rw [ite_eq_right h1, ite_eq_left h0, ite_eq_right h1,
                             ite_eq_left h0]
                           rfl
                         · rw [ite_eq_right h1, ite_eq_right h0, ite_eq_right h1,
                             ite_eq_right h0]
                           rfl)
            | succ j => rfl
        | ptr a => rfl
        | vec n w l =>
          -- A vector condition selects lane by lane only at lane width 1; a
          -- wider or narrower condition value matches no arm and yields `none`,
          -- and every vector-valued arm is independent of the predecessor
          -- field, so both sides agree after the shape checks.
          cases w with
          | zero => rfl
          | succ k =>
            cases k with
            | zero =>
              simp only [Nat.zero_add]
              try dsimp only
              cases ty with
              | vec m elem =>
                cases elem with
                | int ws =>
                  try dsimp only
                  repeat' split
                  all_goals rfl
                | ptr => rfl
                | void => rfl
                | vec _ _ => rfl
              | int _ => rfl
              | ptr => rfl
              | void => rfl
            | succ j => rfl
  | trunc d wIn wOut v =>
      simp only [evalInstr, evalOperand_setPre, State.bind_setPre]
      cases evalOperand s v with
      | none => rfl
      | some vv =>
        try dsimp only
        cases vv with
        | int w' x =>
          try dsimp only
          by_cases hw : w' = wIn
          · rw [ite_eq_left hw, ite_eq_left hw]
            rfl
          · rw [ite_eq_right hw, ite_eq_right hw]
            rfl
        | ptr a => rfl
        | vec n w l => rfl
  | zext d wIn wOut v =>
      simp only [evalInstr, evalOperand_setPre, State.bind_setPre]
      cases evalOperand s v with
      | none => rfl
      | some vv =>
        try dsimp only
        cases vv with
        | int w' x =>
          try dsimp only
          by_cases hw : w' = wIn
          · rw [ite_eq_left hw, ite_eq_left hw]
            rfl
          · rw [ite_eq_right hw, ite_eq_right hw]
            rfl
        | ptr a => rfl
        | vec n w l => rfl
  | sext d wIn wOut v =>
      simp only [evalInstr, evalOperand_setPre, State.bind_setPre]
      cases evalOperand s v with
      | none => rfl
      | some vv =>
        try dsimp only
        cases vv with
        | int w' x =>
          try dsimp only
          by_cases hw : w' = wIn
          · rw [ite_eq_left hw, ite_eq_left hw]
            rfl
          · rw [ite_eq_right hw, ite_eq_right hw]
            rfl
        | ptr a => rfl
        | vec n w l => rfl
  | alloca d ty align =>
      simp only [evalInstr, State.setPre, Option.map_some]
  | load d ty ptr =>
      simp only [evalInstr, evalOperand_setPre, State.bind_setPre, State.setPre_mem]
      cases evalOperand s ptr with
      | none => rfl
      | some pv =>
        try dsimp only
        cases pv with
        | int w x => rfl
        | ptr addr =>
          try dsimp only
          cases loadValue s.mem ty addr with
          | none => rfl
          | some v => rfl
        | vec n w l => rfl
  | store ty val ptr =>
      simp only [evalInstr, evalOperand_setPre, storeValue_setPre]
      cases evalOperand s val with
      | none => rfl
      | some vv =>
        try dsimp only
        cases evalOperand s ptr with
        | none => rfl
        | some pv =>
          try dsimp only
          cases pv with
          | int w x => rfl
          | ptr addr => rfl
          | vec n w l => rfl
  | gep d elemTy base off =>
      simp only [evalInstr, evalOperand_setPre, State.bind_setPre]
      cases evalOperand s base with
      | none => rfl
      | some bv =>
        cases bv with
        | int w x => rfl
        | ptr a =>
          try dsimp only
          cases evalOperand s off with
          | none => rfl
          | some ov =>
            try dsimp only
            cases ov with
            | int w n =>
              try dsimp only
              by_cases hp : (n.signExtend 64).toNat < 2 ^ 63
              · rw [ite_eq_left hp, ite_eq_left hp]
                rfl
              · rw [ite_eq_right hp, ite_eq_right hp]
                by_cases hk : (2 ^ 64 - (n.signExtend 64).toNat) * elemTy.sizeBytes ≤ a
                · rw [ite_eq_left hk, ite_eq_left hk]
                  rfl
                · rw [ite_eq_right hk, ite_eq_right hk]
                  rfl
            | ptr b => rfl
            | vec n w l => rfl
        | vec n w l => rfl
  | icmpVec d pred n w a b =>
      simp only [evalInstr, evalOperand_setPre, State.bind_setPre]
      cases evalOperand s a with
      | none => rfl
      | some va =>
        try dsimp only
        cases evalOperand s b with
        | none => rfl
        | some vb =>
          try dsimp only
          cases va.vecLanes n w with
          | none => rfl
          | some l₁ =>
            try dsimp only
            cases vb.vecLanes n w with
            | none => rfl
            | some l₂ => rfl
  | binopVec d op n w a b =>
      simp only [evalInstr, evalOperand_setPre, State.bind_setPre]
      cases evalOperand s a with
      | none => rfl
      | some va =>
        try dsimp only
        cases evalOperand s b with
        | none => rfl
        | some vb =>
          try dsimp only
          cases va.vecLanes n w with
          | none => rfl
          | some l₁ =>
            try dsimp only
            cases vb.vecLanes n w with
            | none => rfl
            | some l₂ =>
              try dsimp only
              cases (l₁.zip l₂).mapM (fun (x, y) => evalBinop op x y) with
              | none => rfl
              | some ls => rfl
  | shuffleVec d n w a b mask =>
      simp only [evalInstr, evalOperand_setPre, State.bind_setPre]
      cases evalOperand s a with
      | none => rfl
      | some va =>
        try dsimp only
        cases evalOperand s b with
        | none => rfl
        | some vb =>
          try dsimp only
          cases va.vecLanes n w with
          | none => rfl
          | some l₁ =>
            try dsimp only
            cases vb.vecLanes n w with
            | none => rfl
            | some l₂ =>
              try dsimp only
              cases mask.mapM (fun k => if k < n then l₁[k]? else l₂[k - n]?) with
              | none => rfl
              | some ls => rfl
  | vecBitcast d n w m jw v =>
      simp only [evalInstr, evalOperand_setPre, State.bind_setPre]
      cases evalOperand s v with
      | none => rfl
      | some vv =>
        try dsimp only
        cases vv.vecLanes n w with
        | none => rfl
        | some lanes =>
          try dsimp only
          by_cases hw : n * w = m * jw
          · rw [ite_eq_left hw, ite_eq_left hw]
            rfl
          · rw [ite_eq_right hw, ite_eq_right hw]
            rfl
  | bitcastMask d n v =>
      simp only [evalInstr, evalOperand_setPre, State.bind_setPre]
      cases evalOperand s v with
      | none => rfl
      | some vv =>
        try dsimp only
        cases vv with
        | int w x => rfl
        | ptr a => rfl
        | vec bn bw bl =>
          cases bw with
          | zero => rfl
          | succ k =>
            cases k with
            | zero =>
              try dsimp only
              simp only [Option.map_ite]
            | succ j => rfl
  | extractelement d n w v idx =>
      simp only [evalInstr, evalOperand_setPre, State.bind_setPre]
      cases evalOperand s v with
      | none => rfl
      | some vv =>
        try dsimp only
        cases evalOperand s idx with
        | none => rfl
        | some iv =>
          try dsimp only
          cases iv with
          | int wi k =>
            try dsimp only
            cases vv.vecLanes n w with
            | none => rfl
            | some lanes =>
              try dsimp only
              cases lanes[k.toNat]? with
              | none => rfl
              | some x => rfl
          | ptr a => rfl
          | vec n' w' l => rfl
  | insertelement d n w v elt idx =>
      simp only [evalInstr, evalOperand_setPre, State.bind_setPre]
      cases evalOperand s v with
      | none => rfl
      | some vv =>
        try dsimp only
        cases evalOperand s elt with
        | none => rfl
        | some ev =>
          try dsimp only
          cases evalOperand s idx with
          | none => rfl
          | some iv =>
            try dsimp only
            cases iv with
            | int wi k =>
              try dsimp only
              cases vv.vecLanes n w with
              | none => rfl
              | some lanes =>
                try dsimp only
                cases ev.intToNat w with
                | none => rfl
                | some x =>
                  try dsimp only
                  by_cases hk : k.toNat < lanes.length
                  · simp only [ite_eq_left hk]
                    rfl
                  · simp only [ite_eq_right hk]
                    rfl
            | ptr a => rfl
            | vec n' w' l => rfl
  | call d retTy callee args =>
      simp only [evalInstr, evalOperands_setPre, State.setPre_mem, State.setPre_next,
        State.setPre_env, State.setPre_pc]
      cases evalOperands s args with
      | none => rfl
      | some vs =>
        try dsimp only
        cases calls callee vs s.mem s.next with
        | none => rfl
        | some r =>
          try dsimp only
          rfl
  | callVoid callee args =>
      simp only [evalInstr, evalOperands_setPre, State.setPre_mem, State.setPre_next,
        State.setPre_env, State.setPre_pc]
      cases evalOperands s args with
      | none => rfl
      | some vs =>
        try dsimp only
        cases calls callee vs s.mem s.next with
        | none => rfl
        | some r =>
          try dsimp only
          rfl

/-- A void call binds nothing: the register environment after it is the one
before it, whatever the callee left.  The caller has no name for the answer, so
there is no binding to make, and a later instruction cannot read it. -/
theorem evalInstr_callVoid_env {calls : Calls} {s s' : State} {callee : String}
    {args : List (Ty × Operand)}
    (h : evalInstr calls s (.callVoid callee args) = some s') : s'.env = s.env := by
  simp only [evalInstr] at h
  split at h
  · split at h
    · cases h
      rfl
    · cases h
  · cases h

/-- A `phi`-free instruction leaves the predecessor field where it found it: only
a jump writes it. -/
theorem evalInstr_pre_of_not_phi {calls : Calls} {s s' : State} {i : Instr}
    (hi : i.isPhi = false) (h : evalInstr calls s i = some s') : s'.pre = s.pre := by
  have hkey := evalInstr_setPre (calls := calls) i hi s s.pre
  rw [State.setPre_self] at hkey
  rw [h] at hkey
  simp only [Option.map_some] at hkey
  have hEq : s' = s'.setPre s.pre := Option.some.inj hkey
  rw [hEq]
  rfl

/-- A straight-line sequence of `phi`-free instructions reaches the same state up
to the predecessor field.  `pend` is the leading run's pending bindings, which a
`phi`-free list never collects, so it is carried through unchanged; both sides
install it with `bindAll`, which commutes with `setPre`. -/
theorem denoteRun_setPre (calls : Calls) (is : List Instr)
    (h : ∀ i ∈ is, i.isPhi = false) (pend : List (String × Value)) (s : State)
    (p : Option String) :
    denoteRun calls pend is (s.setPre p) =
      (denoteRun calls pend is s).map (·.setPre p) := by
  induction is generalizing pend s with
  | nil => simp only [denoteRun, State.bindAll_setPre, Option.map_some]
  | cons i rest ih =>
      have hi : i.isPhi = false := h i (List.mem_cons_self ..)
      have hrest : ∀ j ∈ rest, j.isPhi = false :=
        fun j hj => h j (List.mem_cons_of_mem _ hj)
      rw [denoteRun_cons_of hi, denoteRun_cons_of hi, State.bindAll_setPre,
        evalInstr_setPre i hi]
      cases he : evalInstr calls (s.bindAll pend) i with
      | none => rfl
      | some s' => simp only [Option.map_some]; exact ih hrest [] s'

/-- A straight-line sequence of `phi`-free instructions reaches the same state up
to the predecessor field. -/
theorem denoteCode_setPre (calls : Calls) (is : List Instr)
    (h : ∀ i ∈ is, i.isPhi = false) (s : State) (p : Option String) :
    denoteCode calls is (s.setPre p) = (denoteCode calls is s).map (·.setPre p) :=
  denoteRun_setPre calls is h [] s p

/-- A terminator reaches the same control result from two states one `setPre`
apart.  A `ret` keeps the field; a jump overwrites it with the block it came
from, which is why the right-hand side's jump is unmoved. -/
theorem execTerm_setPre (s : State) (p : Option String) (t : Term) :
    execTerm (s.setPre p) t = (execTerm s t).setPre p := by
  cases t with
  | ret ty v =>
      cases ty with
      | void => cases v <;> rfl
      | int w =>
          cases v with
          | none => rfl
          | some o =>
              simp only [execTerm, evalOperand_setPre]
              cases ho : evalOperand s o with
              | none => rfl
              | some x => rfl
      | ptr =>
          cases v with
          | none => rfl
          | some o =>
              simp only [execTerm, evalOperand_setPre]
              cases ho : evalOperand s o with
              | none => rfl
              | some x => rfl
      | vec n elem =>
          cases v with
          | none => rfl
          | some o =>
              simp only [execTerm, evalOperand_setPre]
              cases ho : evalOperand s o with
              | none => rfl
              | some x => rfl
  | br dest => rfl
  | condbr c t f =>
      simp only [execTerm, evalOperand_setPre, State.setPre_pc]
      repeat' split
      all_goals rfl
  | unreachable => rfl

/-- One control step of a `phi`-free function is the same whatever predecessor its
starting state carries, as an equation **whose carrier is `Ctrl.setPre`**: that
carrier maps `ub` to itself, carries the field into a `ret` result, and leaves a
`jump` result *unmoved*, because the jump has already set the field from the block
it came from.  The carrier is part of the claim: read with the naive carrier that
maps `.jump s` to `.jump (s.setPre p)`, the equation is false whenever `p` differs
from the block the jump leaves.  `step_sameExceptPre` states the same fact as a
relation, and that form does not name a carrier at all. -/
theorem step_setPre {calls : Calls} {f : Function} (hf : f.phiFree = true)
    (s : State) (p : Option String) :
    step calls f (s.setPre p) = (step calls f s).setPre p := by
  unfold step
  simp only [State.setPre_pc]
  cases hfind : f.findBlock s.pc with
  | none => simp [Ctrl.setPre]
  | some b =>
      have hpi := Function.phiFree_block hf (findBlockList_mem hfind)
      try dsimp only
      rw [denoteCode_setPre calls b.instrs hpi]
      cases hcode : denoteCode calls b.instrs s with
      | none => simp [Ctrl.setPre]
      | some s' => simpa only [hcode, Option.map_some, Ctrl.setPre] using
          execTerm_setPre s' p b.term

/-- One control step preserves agreement outside the predecessor.  This is the
step-level form of non-interference, stated as the relation rather than as an
equation: two states agreeing on every field but the predecessor produce control
results that agree outside it. -/
theorem step_sameExceptPre {calls : Calls} {f : Function} (hf : f.phiFree = true)
    {s t : State} (h : s.SameExceptPre t) :
    Ctrl.SameExceptPre (step calls f s) (step calls f t) := by
  have ht : t = s.setPre t.pre := (State.setPre_eq_of_sameExceptPre h).symm
  rw [ht, step_setPre hf]
  exact Ctrl.sameExceptPre_setPre (step calls f s) t.pre

/-- Non-interference at the fuel semantics: for a `phi`-free function the run from
a state and the run from the same state with any predecessor whatever produce the
same outcome, at every budget.  The jump drops the field before the successor
block could read it, so the induction is not even needed: after one step the two
runs coincide. -/
theorem runFuel_setPre {calls : Calls} {f : Function} (hf : f.phiFree = true) :
    ∀ (n : Nat) (s : State) (q : Option String),
      runFuel calls n f (s.setPre q) = runFuel calls n f s
  | 0, _, _ => rfl
  | n + 1, s, q => by
      simp only [runFuel, step_setPre hf]
      cases hs : step calls f s with
      | ub => rfl
      | ret v s' => rfl
      | jump s' => rfl

/-- Non-interference over a whole run, stated as the relation: a `phi`-free
function produces the same outcome at every fuel budget starting from two states
that agree on every field but the predecessor.  `Outcome` carries the returned
value and the memory, and neither is the field, so the two runs are
indistinguishable. -/
theorem runFuel_sameExceptPre {calls : Calls} {f : Function} (hf : f.phiFree = true)
    {s t : State} (h : s.SameExceptPre t) (n : Nat) :
    runFuel calls n f s = runFuel calls n f t := by
  have ht : t = s.setPre t.pre := (State.setPre_eq_of_sameExceptPre h).symm
  rw [ht, runFuel_setPre hf n s t.pre]


/-- Initial state for a call: parameters bound to the arguments, empty memory,
address `0` reserved for `null`, the entry block loaded, and no predecessor —
the entry block has none, so a `phi` there selects nothing. -/
def initState (f : Function) (args : List Value) : State :=
  { env := (f.params.zip args).map fun (p, v) => (p.1, v)
    mem := [], next := 1, pc := f.entry?.getD "", pre := none }

/-- The set of outcomes a function can produce, as a predicate.  A `ub` outcome
on any prefix admits every outcome; a function that never finishes admits
none.  This is the observable behaviour `Refines` compares. -/
def Beh (calls : Calls) (f : Function) (args : List Value) (o : Outcome) : Prop :=
  (∃ n, runFuel calls n f (initState f args) = some .ub) ∨
    (∃ n, runFuel calls n f (initState f args) = some o)

/-- `target` refines `source`: every outcome the target can produce is one the
source can produce. -/
def Refines (calls : Calls) (target source : Function) : Prop :=
  ∀ args o, Beh calls target args o → Beh calls source args o

/-- Concrete execution with a default fuel budget. -/
def run (calls : Calls) (f : Function) (args : List Value) (fuel : Nat := 10000) :
    Option Outcome :=
  runFuel calls fuel f (initState f args)

/-- Existing runs are unchanged.  A `phi`-free function's canonical run does not
depend on the predecessor its initial state carries, so every result recorded
before `phi` existed is still that result: `initState` sets the field to `none`,
and the field is not observable — at any budget, from that state with any other
predecessor whatever. -/
theorem runFuel_init_setPre {calls : Calls} {f : Function} (hf : f.phiFree = true)
    (n : Nat) (args : List Value) (q : Option String) :
    runFuel calls n f ((initState f args).setPre q) =
      runFuel calls n f (initState f args) :=
  runFuel_setPre hf n (initState f args) q

section Agreement

set_option autoImplicit false

/-! ### Agreement on a read set, and instruction transport

`evalInstr` reads a state only through `lookupName`, the memory, the allocator
base and the predecessor.  Two states that agree on those — the lookups at every
name in a read set, the other three exactly — execute every instruction the same
way, and the results agree in the same way.  That is the lemma a caller uses to
move a block trace stated over one environment to another environment that binds
the registers the block reads; it is stated here, beside `evalInstr`, because the
case analysis is the instruction grammar's and not any one caller's.

* `State.AgreeOn ns s t` is the relation, over a list of register names.
* `Instr.uses` is the read set an instruction can consult — the fragment's own
  computation, so no consumer re-derives one.
* `evalInstr_agree` is the per-instruction transport; `denoteCode_agree` below is
  its straight-line-list form.

Two corners of `evalInstr` need more than splitting the instruction's own shape,
and they are recorded here because every consumer meets them:

* `select`, `store` and `gep` decide a branch on a *value* read from an operand
  (`if bit = 1`, the shape test inside `storeValue`, the sign test inside `gep`).
  Once the operand evaluations are rewritten to the second state, the run's match
  still tests literals: `select`'s condition width and lane width against `1`,
  `storeValue`'s lane shape.  A `split` cannot reduce a match whose scrutinee's
  width is a variable, so the width is enumerated to `0`, `1` and at least `2`
  (`select_of_intBit`, `select_of_lanes`) and the residual shape tests are split
  one at a time.  The instruction's own shape does not determine the branch.
* `call`, `callVoid` and `phi` bind a `Value` whose shape is not syntactically
  an `int` or a `ptr` (`CallOutcome.ret`, the operand `phiIncoming` selects), so
  `s.bind d r.ret` is not a term the relation can be rebuilt from directly.
  Name the outcome's fields first: `State.AgreeOn.call`, `.callVoid` and `.bind`
  are applied to the fields, never to the bare result. -/

/-- Every one-bit value is zero or one: the case split a data-dependent `select`
needs, because the instruction's own test is `bit = 1` and its other arm is
`bit = 0`, so the two values exhaust the condition. -/
private theorem bitVec1_eq_zero_or_one (b : BitVec 1) : b = 0 ∨ b = 1 := by
  have hb : b = BitVec.ofNat 1 b.toNat := by
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  rw [hb]
  have hlt : b.toNat = 0 ∨ b.toNat = 1 := by omega
  rcases hlt with h | h <;> rw [h] <;> decide

/-- **Two states agree on a read set.**  Same memory, allocator base and
predecessor, and the same value for every register name in the set.  The program
counter is not part of it: `denoteCode` does not read it. -/
def State.AgreeOn (ns : List String) (s t : State) : Prop :=
  s.mem = t.mem ∧ s.next = t.next ∧ s.pre = t.pre ∧
    ∀ n ∈ ns, lookupName s.env n = lookupName t.env n

theorem State.AgreeOn.refl (ns : List String) (s : State) : State.AgreeOn ns s s :=
  ⟨rfl, rfl, rfl, fun _ _ => rfl⟩

theorem State.AgreeOn.symm {ns : List String} {s t : State} (h : State.AgreeOn ns s t) :
    State.AgreeOn ns t s :=
  ⟨h.1.symm, h.2.1.symm, h.2.2.1.symm, fun n hn => (h.2.2.2 n hn).symm⟩

theorem State.AgreeOn.mono {ns' ns : List String} {s t : State}
    (hsub : ∀ n ∈ ns', n ∈ ns) (h : State.AgreeOn ns s t) : State.AgreeOn ns' s t :=
  ⟨h.1, h.2.1, h.2.2.1, fun n hn => h.2.2.2 n (hsub n hn)⟩

/-- Binding one cell on both sides preserves agreement. -/
theorem State.AgreeOn.bind {ns : List String} {s t : State} {d : String} {v : Value}
    (h : State.AgreeOn ns s t) : State.AgreeOn ns (s.bind d v) (t.bind d v) := by
  obtain ⟨hm, hn, hp, hl⟩ := h
  refine ⟨hm, hn, hp, fun n hn' => ?_⟩
  simp only [State.bind, lookupName]
  by_cases hdn : d = n
  · rw [ite_eq_left hdn, ite_eq_left hdn]
  · rw [ite_eq_right hdn, ite_eq_right hdn]
    exact hl n hn'

/-- Installing a group's bindings on both sides preserves agreement: the run
selects the same destinations bound to the same values at either state. -/
theorem State.AgreeOn.bindAll {ns : List String} :
    ∀ (bs : List (String × Value)) {s t : State}, State.AgreeOn ns s t →
      State.AgreeOn ns (s.bindAll bs) (t.bindAll bs)
  | [], _, _, h => h
  | (n, v) :: rest, _, _, h => State.AgreeOn.bindAll rest (State.AgreeOn.bind h)

/-- The memory a store writes, at the same address and the same bytes on both
sides: the write's byte list is the value's, so the equality of the memories is
the equality of what was there. -/
theorem State.AgreeOn.withMemBytes {ns : List String} {s t : State} {addr : Nat}
    {bs : List UInt8} (h : State.AgreeOn ns s t) :
    State.AgreeOn ns { s with mem := writeBytes s.mem addr bs }
      { t with mem := writeBytes t.mem addr bs } :=
  ⟨by rw [h.1], h.2.1, h.2.2.1, h.2.2.2⟩

/-- The state a call leaves: a bound result, its memory, its allocator base.  The
result's fields are named by the caller, because `CallOutcome.ret` is not
syntactically a value of the instruction's type. -/
theorem State.AgreeOn.call {ns : List String} {s t : State} {d : String}
    {r : CallOutcome} (h : State.AgreeOn ns s t) :
    State.AgreeOn ns { s with env := (d, r.ret) :: s.env, mem := r.mem, next := r.next }
      { t with env := (d, r.ret) :: t.env, mem := r.mem, next := r.next } := by
  obtain ⟨hm, hn, hp, hl⟩ := h
  refine ⟨rfl, rfl, hp, fun n hn' => ?_⟩
  simp only [lookupName]
  by_cases hdn : d = n
  · rw [ite_eq_left hdn, ite_eq_left hdn]
  · rw [ite_eq_right hdn, ite_eq_right hdn]
    exact hl n hn'

/-- The state a void call leaves: memory and allocator base only. -/
theorem State.AgreeOn.callVoid {ns : List String} {s t : State} {r : CallOutcome}
    (h : State.AgreeOn ns s t) :
    State.AgreeOn ns { s with mem := r.mem, next := r.next }
      { t with mem := r.mem, next := r.next } :=
  ⟨rfl, rfl, h.2.2.1, h.2.2.2⟩

/-- The state an `alloca` leaves: a pointer to the allocator base, and the base
bumped by the size.  The two pointers are equal because the bases are. -/
theorem State.AgreeOn.alloca {ns : List String} {s t : State} {d : String} {ty : Ty}
    (h : State.AgreeOn ns s t) :
    State.AgreeOn ns
      { s with env := (d, .ptr s.next) :: s.env, next := s.next + ty.sizeBytes }
      { t with env := (d, .ptr t.next) :: t.env, next := t.next + ty.sizeBytes } := by
  obtain ⟨hm, hn, hp, hl⟩ := h
  refine ⟨hm, ?_, hp, fun n hn' => ?_⟩
  · rw [hn]
  · simp only [lookupName]
    by_cases hdn : d = n
    · subst hdn
      rw [ite_eq_left rfl, ite_eq_left rfl, hn]
    · rw [ite_eq_right hdn, ite_eq_right hdn]
      exact hl n hn'

/-- **An operand reads the same at two states that agree on its names.** -/
theorem evalOperand_agree {s t : State} {op : Operand}
    (h : ∀ n ∈ Operand.regs op, lookupName s.env n = lookupName t.env n) :
    evalOperand s op = evalOperand t op := by
  cases op with
  | reg n =>
      simpa only [evalOperand] using h n (by simp only [Operand.regs]; exact List.mem_singleton_self n)
  | imm c => rfl

/-- An operand the instruction evaluates reads the same at two states that agree
on the instruction's read set. -/
theorem evalOperand_agree_of_uses {s t : State} {i : Instr} {op : Operand}
    (hl : ∀ n ∈ Instr.uses i, lookupName s.env n = lookupName t.env n)
    (hsub : ∀ n ∈ Operand.regs op, n ∈ Instr.uses i) :
    evalOperand s op = evalOperand t op :=
  evalOperand_agree fun n hn => hl n (hsub n hn)

/-- Arguments read the same at two states that agree on every argument's names. -/
theorem evalOperands_agree {s t : State} :
    ∀ (args : List (Ty × Operand)),
      (∀ op ∈ args.map (·.2), evalOperand s op = evalOperand t op) →
      evalOperands s args = evalOperands t args
  | [], _ => rfl
  | (_, op) :: rest, h => by
      have h1 : evalOperand s op = evalOperand t op := h op (by simp)
      have h2 : evalOperands s rest = evalOperands t rest :=
        evalOperands_agree rest fun q hq => h q (by
          obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hq
          exact List.mem_map.mpr ⟨a, List.mem_cons_of_mem _ ha, rfl⟩)
      simp only [evalOperands, h1, h2]

/-- The predecessor selector's operand is one of the incoming list's. -/
theorem phiIncoming_mem {p : String} {inc : List (String × Operand)} {op : Operand}
    (h : phiIncoming p inc = some op) : op ∈ inc.map (·.2) := by
  induction inc with
  | nil => simp [phiIncoming] at h
  | cons x rest ih =>
      obtain ⟨l, o⟩ := x
      simp only [phiIncoming] at h
      split at h
      · cases h
        simp
      · exact List.mem_cons_of_mem _ (ih h)

/-- The operand a `phi` selects contributes its registers to the instruction's
read set. -/
theorem phi_operand_regs_uses {d : String} {ty : Ty} {inc : List (String × Operand)}
    {p : String} {op : Operand} (hinc : phiIncoming p inc = some op) {n : String}
    (hn : n ∈ Operand.regs op) : n ∈ Instr.uses (.phi d ty inc) := by
  obtain ⟨⟨l, o⟩, hmem, ho⟩ := List.mem_map.mp (phiIncoming_mem hinc)
  rw [← ho] at hn
  exact List.mem_flatten.mpr ⟨o.regs, List.mem_map.mpr ⟨(l, o), hmem, rfl⟩, hn⟩

/-- Selection reads the same at two states that agree on the instruction's read
set: the predecessor field and every incoming operand's registers. -/
theorem phiSelect_agree {ns : List String} {s t : State} {d : String} {ty : Ty}
    {inc : List (String × Operand)}
    (h : State.AgreeOn ns s t)
    (hread : ∀ n ∈ Instr.uses (.phi d ty inc), n ∈ ns) :
    phiSelect s inc = phiSelect t inc := by
  obtain ⟨_, _, hp, hl⟩ := h
  cases hsp : s.pre with
  | none =>
      have htp : t.pre = none := by rw [← hp]; exact hsp
      simp only [phiSelect, hsp, htp]
  | some p =>
      have htp : t.pre = some p := by rw [← hp]; exact hsp
      cases hinc : phiIncoming p inc with
      | none => simp only [phiSelect, hsp, htp, hinc]
      | some op =>
          simp only [phiSelect, hsp, htp, hinc]
          exact evalOperand_agree_of_uses
            (hl := fun n hmem => hl n (hread n hmem))
            (hsub := fun n hn' => phi_operand_regs_uses hinc hn')

/-- **A store's success and its written bytes depend only on the memory.**  The
shape tests `storeValue` performs read the type and the value, never the state,
so two states that agree on their memory both succeed and agree afterwards. -/
theorem storeValue_agree {ns : List String} {s t s' : State} {ty : Ty} {v : Value}
    {addr : Nat} (h : State.AgreeOn ns s t)
    (hs : storeValue s ty v addr = some s') :
    ∃ t', storeValue t ty v addr = some t' ∧ State.AgreeOn ns s' t' := by
  have hm : s.mem = t.mem := h.1
  have hn : s.next = t.next := h.2.1
  have hp : s.pre = t.pre := h.2.2.1
  have hl : ∀ n ∈ ns, lookupName s.env n = lookupName t.env n := h.2.2.2
  cases ty with
  | int w =>
    cases v with
    | int w' x =>
      by_cases hw : w' = w
      · simp only [storeValue, ite_eq_left hw] at hs
        cases hs
        let t' : State := { t with mem := writeBytes t.mem addr (natToBytes x.toNat ((w + 7) / 8)) }
        refine ⟨t', ?_, ⟨by rw [hm], hn, hp, hl⟩⟩
        simp only [storeValue, ite_eq_left hw, t']
      · simp only [storeValue] at hs
        rw [ite_eq_right hw] at hs
        cases hs
    | ptr a => simp only [storeValue] at hs; cases hs
    | vec n' w' lanes => simp only [storeValue] at hs; cases hs
  | ptr =>
    cases v with
    | ptr a =>
      simp only [storeValue] at hs
      cases hs
      let t' : State := { t with mem := writeBytes t.mem addr (natToBytes a 8) }
      refine ⟨t', ?_, ⟨by rw [hm], hn, hp, hl⟩⟩
      simp only [storeValue, t']
    | int w x => simp only [storeValue] at hs; cases hs
    | vec n' w' lanes => simp only [storeValue] at hs; cases hs
  | void => simp only [storeValue] at hs; cases hs
  | vec n elem =>
    cases elem with
    | int w =>
      cases v with
      | vec n' w' lanes =>
        by_cases hc : n' = n ∧ w' = w ∧ lanes.length = n ∧ n * w % 8 = 0
        · simp only [storeValue, ite_eq_left hc] at hs
          cases hs
          let t' : State := { t with mem := writeBytes t.mem addr (natToBytes (packLanes lanes) (n * w / 8)) }
          refine ⟨t', ?_, ⟨by rw [hm], hn, hp, hl⟩⟩
          simp only [storeValue, ite_eq_left hc, t']
        · simp only [storeValue] at hs
          rw [ite_eq_right hc] at hs
          cases hs
      | int w' x => simp only [storeValue] at hs; cases hs
      | ptr a => simp only [storeValue] at hs; cases hs
    | ptr => cases v <;> simp only [storeValue] at hs <;> cases hs
    | void => cases v <;> simp only [storeValue] at hs <;> cases hs
    | vec n2 e2 => cases v <;> simp only [storeValue] at hs <;> cases hs


/-- **A single-width integer condition.**  `select`'s first arm binds the
selected operand and does not consult the result type, so this analysis serves
every `ty`.  The condition's width is split to 0, 1 and at least 2, because the
arm tests it against the literal 1 and the match only computes at a literal:
below 1 and above 1 no arm applies.  The `bit` is a single bit, so a set bit
binds `a` and a clear bit binds `b`; no other bit exists. -/
private theorem select_of_intBit (calls : Calls) {ns : List String} {d : String}
    {ty : Ty} {c a b : Operand} {s t s' : State} {wc : Nat} {x : BitVec wc}
    (h : State.AgreeOn ns s t)
    (hc : evalOperand s c = evalOperand t c)
    (ha : evalOperand s a = evalOperand t a)
    (hb : evalOperand s b = evalOperand t b)
    (hcv : evalOperand t c = some (.int wc x))
    (hs : evalInstr calls s (.select d ty c a b) = some s') :
    ∃ t', evalInstr calls t (.select d ty c a b) = some t' ∧
      State.AgreeOn ns s' t' := by
  simp only [evalInstr, hc, ha, hb, hcv] at hs
  by_cases hw : wc = 1
  · subst hw
    rcases hva : evalOperand t a with _ | va
    · simp [hva] at hs
    · rcases hvb : evalOperand t b with _ | vb
      · simp [hva, hvb] at hs
      · rcases bitVec1_eq_zero_or_one x with hx | hx
        · subst hx
          simp only [hva, hvb] at hs
          cases hs
          exact ⟨_, by simp [evalInstr, *], State.AgreeOn.bind h⟩
        · subst hx
          simp only [hva, hvb] at hs
          cases hs
          exact ⟨_, by simp [evalInstr, *], State.AgreeOn.bind h⟩
  · rcases wc with _ | k
    · simp at hs
    · rcases k with _ | j
      · exact absurd rfl hw
      · simp at hs

/-- **A lane condition.**  At a vector-of-integer result type the second arm
applies: the condition's width must be the literal 1, its lane count must be the
result's, and both operands must carry the result's lane shape; the result then
selects lane by lane.  The condition's width is split as in
`select_of_intBit`. -/
private theorem select_of_lanes (calls : Calls) {ns : List String} {d : String}
    {nv wi : Nat} {c a b : Operand} {s t s' : State} {vn vw : Nat}
    {vs : List (BitVec vw)}
    (h : State.AgreeOn ns s t)
    (hc : evalOperand s c = evalOperand t c)
    (ha : evalOperand s a = evalOperand t a)
    (hb : evalOperand s b = evalOperand t b)
    (hcv : evalOperand t c = some (.vec vn vw vs))
    (hs : evalInstr calls s (.select d (Ty.vec nv (Ty.int wi)) c a b) = some s') :
    ∃ t', evalInstr calls t (.select d (Ty.vec nv (Ty.int wi)) c a b) = some t' ∧
      State.AgreeOn ns s' t' := by
  simp only [evalInstr, hc, ha, hb, hcv] at hs
  rcases vw with _ | k
  · simp at hs
  · rcases k with _ | j
    · by_cases hnc : vn = nv
      · subst vn
        rcases hva : evalOperand t a with _ | va
        · simp [hva] at hs
        · rcases hvb : evalOperand t b with _ | vb
          · simp [hva, hvb] at hs
          · rcases hla : va.vecLanes nv wi with _ | la
            · simp [hva, hvb, hla] at hs
            · rcases hlb : vb.vecLanes nv wi with _ | lb
              · simp [hva, hvb, hla, hlb] at hs
              · simp only [hva, hvb, hla, hlb] at hs
                cases hs
                exact ⟨_, by simp [evalInstr, *], State.AgreeOn.bind h⟩
      · simp [hnc] at hs
    · simp at hs

/-- The `select` transport at a scalar integer result type. -/
theorem select_int (calls : Calls) {ns : List String} {d : String} {wt : Nat}
    {c a b : Operand} {s t s' : State} (h : State.AgreeOn ns s t)
    (hread : ∀ n ∈ Instr.uses (.select d (Ty.int wt) c a b), n ∈ ns)
    (hs : evalInstr calls s (.select d (Ty.int wt) c a b) = some s') :
    ∃ t', evalInstr calls t (.select d (Ty.int wt) c a b) = some t' ∧
      State.AgreeOn ns s' t' := by
  have hl : ∀ n ∈ Instr.uses (.select d (Ty.int wt) c a b),
      lookupName s.env n = lookupName t.env n :=
    fun n hn' => h.2.2.2 n (hread n hn')
  have hc : evalOperand s c = evalOperand t c :=
    evalOperand_agree_of_uses hl (by
      intro n hn'; cases c <;> simp_all [Instr.uses, Operand.regs])
  have ha : evalOperand s a = evalOperand t a :=
    evalOperand_agree_of_uses hl (by
      intro n hn'; cases a <;> simp_all [Instr.uses, Operand.regs])
  have hb : evalOperand s b = evalOperand t b :=
    evalOperand_agree_of_uses hl (by
      intro n hn'; cases b <;> simp_all [Instr.uses, Operand.regs])
  rcases hcv : evalOperand t c with _ | vc
  · simp [evalInstr, hc, hcv] at hs
  · cases vc with
    | int wc x => exact select_of_intBit calls h hc ha hb hcv hs
    | ptr a' => simp [evalInstr, hc, hcv] at hs
    | vec vn vw vs =>
      simp only [evalInstr, hc, ha, hb, hcv] at hs
      rcases vw with _ | k
      · simp at hs
      · rcases k with _ | j
        · simp at hs
        · simp at hs

/-- The `select` transport at a pointer result type. -/
theorem select_ptr (calls : Calls) {ns : List String} {d : String}
    {c a b : Operand} {s t s' : State} (h : State.AgreeOn ns s t)
    (hread : ∀ n ∈ Instr.uses (.select d (Ty.ptr) c a b), n ∈ ns)
    (hs : evalInstr calls s (.select d (Ty.ptr) c a b) = some s') :
    ∃ t', evalInstr calls t (.select d (Ty.ptr) c a b) = some t' ∧
      State.AgreeOn ns s' t' := by
  have hl : ∀ n ∈ Instr.uses (.select d (Ty.ptr) c a b),
      lookupName s.env n = lookupName t.env n :=
    fun n hn' => h.2.2.2 n (hread n hn')
  have hc : evalOperand s c = evalOperand t c :=
    evalOperand_agree_of_uses hl (by
      intro n hn'; cases c <;> simp_all [Instr.uses, Operand.regs])
  have ha : evalOperand s a = evalOperand t a :=
    evalOperand_agree_of_uses hl (by
      intro n hn'; cases a <;> simp_all [Instr.uses, Operand.regs])
  have hb : evalOperand s b = evalOperand t b :=
    evalOperand_agree_of_uses hl (by
      intro n hn'; cases b <;> simp_all [Instr.uses, Operand.regs])
  rcases hcv : evalOperand t c with _ | vc
  · simp [evalInstr, hc, hcv] at hs
  · cases vc with
    | int wc x => exact select_of_intBit calls h hc ha hb hcv hs
    | ptr a' => simp [evalInstr, hc, hcv] at hs
    | vec vn vw vs =>
      simp only [evalInstr, hc, ha, hb, hcv] at hs
      rcases vw with _ | k
      · simp at hs
      · rcases k with _ | j
        · simp at hs
        · simp at hs

/-- The `select` transport at the void result type. -/
theorem select_void (calls : Calls) {ns : List String} {d : String}
    {c a b : Operand} {s t s' : State} (h : State.AgreeOn ns s t)
    (hread : ∀ n ∈ Instr.uses (.select d (Ty.void) c a b), n ∈ ns)
    (hs : evalInstr calls s (.select d (Ty.void) c a b) = some s') :
    ∃ t', evalInstr calls t (.select d (Ty.void) c a b) = some t' ∧
      State.AgreeOn ns s' t' := by
  have hl : ∀ n ∈ Instr.uses (.select d (Ty.void) c a b),
      lookupName s.env n = lookupName t.env n :=
    fun n hn' => h.2.2.2 n (hread n hn')
  have hc : evalOperand s c = evalOperand t c :=
    evalOperand_agree_of_uses hl (by
      intro n hn'; cases c <;> simp_all [Instr.uses, Operand.regs])
  have ha : evalOperand s a = evalOperand t a :=
    evalOperand_agree_of_uses hl (by
      intro n hn'; cases a <;> simp_all [Instr.uses, Operand.regs])
  have hb : evalOperand s b = evalOperand t b :=
    evalOperand_agree_of_uses hl (by
      intro n hn'; cases b <;> simp_all [Instr.uses, Operand.regs])
  rcases hcv : evalOperand t c with _ | vc
  · simp [evalInstr, hc, hcv] at hs
  · cases vc with
    | int wc x => exact select_of_intBit calls h hc ha hb hcv hs
    | ptr a' => simp [evalInstr, hc, hcv] at hs
    | vec vn vw vs =>
      simp only [evalInstr, hc, ha, hb, hcv] at hs
      rcases vw with _ | k
      · simp at hs
      · rcases k with _ | j
        · simp at hs
        · simp at hs

/-- The `select` transport at a vector-of-integer result type. -/
theorem select_vecI (calls : Calls) {ns : List String} {d : String} {nv wi : Nat}
    {c a b : Operand} {s t s' : State} (h : State.AgreeOn ns s t)
    (hread : ∀ n ∈ Instr.uses (.select d (Ty.vec nv (Ty.int wi)) c a b), n ∈ ns)
    (hs : evalInstr calls s (.select d (Ty.vec nv (Ty.int wi)) c a b) = some s') :
    ∃ t', evalInstr calls t (.select d (Ty.vec nv (Ty.int wi)) c a b) = some t' ∧
      State.AgreeOn ns s' t' := by
  have hl : ∀ n ∈ Instr.uses (.select d (Ty.vec nv (Ty.int wi)) c a b),
      lookupName s.env n = lookupName t.env n :=
    fun n hn' => h.2.2.2 n (hread n hn')
  have hc : evalOperand s c = evalOperand t c :=
    evalOperand_agree_of_uses hl (by
      intro n hn'; cases c <;> simp_all [Instr.uses, Operand.regs])
  have ha : evalOperand s a = evalOperand t a :=
    evalOperand_agree_of_uses hl (by
      intro n hn'; cases a <;> simp_all [Instr.uses, Operand.regs])
  have hb : evalOperand s b = evalOperand t b :=
    evalOperand_agree_of_uses hl (by
      intro n hn'; cases b <;> simp_all [Instr.uses, Operand.regs])
  rcases hcv : evalOperand t c with _ | vc
  · simp [evalInstr, hc, hcv] at hs
  · cases vc with
    | int wc x => exact select_of_intBit calls h hc ha hb hcv hs
    | ptr a' => simp [evalInstr, hc, hcv] at hs
    | vec vn vw vs => exact select_of_lanes calls h hc ha hb hcv hs

/-- The `select` transport at a vector-of-pointer result type. -/
theorem select_vecP (calls : Calls) {ns : List String} {d : String} {nv : Nat}
    {c a b : Operand} {s t s' : State} (h : State.AgreeOn ns s t)
    (hread : ∀ n ∈ Instr.uses (.select d (Ty.vec nv Ty.ptr) c a b), n ∈ ns)
    (hs : evalInstr calls s (.select d (Ty.vec nv Ty.ptr) c a b) = some s') :
    ∃ t', evalInstr calls t (.select d (Ty.vec nv Ty.ptr) c a b) = some t' ∧
      State.AgreeOn ns s' t' := by
  have hl : ∀ n ∈ Instr.uses (.select d (Ty.vec nv Ty.ptr) c a b),
      lookupName s.env n = lookupName t.env n :=
    fun n hn' => h.2.2.2 n (hread n hn')
  have hc : evalOperand s c = evalOperand t c :=
    evalOperand_agree_of_uses hl (by
      intro n hn'; cases c <;> simp_all [Instr.uses, Operand.regs])
  have ha : evalOperand s a = evalOperand t a :=
    evalOperand_agree_of_uses hl (by
      intro n hn'; cases a <;> simp_all [Instr.uses, Operand.regs])
  have hb : evalOperand s b = evalOperand t b :=
    evalOperand_agree_of_uses hl (by
      intro n hn'; cases b <;> simp_all [Instr.uses, Operand.regs])
  rcases hcv : evalOperand t c with _ | vc
  · simp [evalInstr, hc, hcv] at hs
  · cases vc with
    | int wc x => exact select_of_intBit calls h hc ha hb hcv hs
    | ptr a' => simp [evalInstr, hc, hcv] at hs
    | vec vn vw vs =>
      simp only [evalInstr, hc, ha, hb, hcv] at hs
      rcases vw with _ | k
      · simp at hs
      · rcases k with _ | j
        · simp at hs
        · simp at hs

/-- The `select` transport at a vector-of-void result type. -/
theorem select_vecV (calls : Calls) {ns : List String} {d : String} {nv : Nat}
    {c a b : Operand} {s t s' : State} (h : State.AgreeOn ns s t)
    (hread : ∀ n ∈ Instr.uses (.select d (Ty.vec nv Ty.void) c a b), n ∈ ns)
    (hs : evalInstr calls s (.select d (Ty.vec nv Ty.void) c a b) = some s') :
    ∃ t', evalInstr calls t (.select d (Ty.vec nv Ty.void) c a b) = some t' ∧
      State.AgreeOn ns s' t' := by
  have hl : ∀ n ∈ Instr.uses (.select d (Ty.vec nv Ty.void) c a b),
      lookupName s.env n = lookupName t.env n :=
    fun n hn' => h.2.2.2 n (hread n hn')
  have hc : evalOperand s c = evalOperand t c :=
    evalOperand_agree_of_uses hl (by
      intro n hn'; cases c <;> simp_all [Instr.uses, Operand.regs])
  have ha : evalOperand s a = evalOperand t a :=
    evalOperand_agree_of_uses hl (by
      intro n hn'; cases a <;> simp_all [Instr.uses, Operand.regs])
  have hb : evalOperand s b = evalOperand t b :=
    evalOperand_agree_of_uses hl (by
      intro n hn'; cases b <;> simp_all [Instr.uses, Operand.regs])
  rcases hcv : evalOperand t c with _ | vc
  · simp [evalInstr, hc, hcv] at hs
  · cases vc with
    | int wc x => exact select_of_intBit calls h hc ha hb hcv hs
    | ptr a' => simp [evalInstr, hc, hcv] at hs
    | vec vn vw vs =>
      simp only [evalInstr, hc, ha, hb, hcv] at hs
      rcases vw with _ | k
      · simp at hs
      · rcases k with _ | j
        · simp at hs
        · simp at hs

/-- The `select` transport at a nested-vector result type. -/
theorem select_vecVv (calls : Calls) {ns : List String} {d : String} {nv n2 : Nat} {e2 : Ty}
    {c a b : Operand} {s t s' : State} (h : State.AgreeOn ns s t)
    (hread : ∀ n ∈ Instr.uses (.select d (Ty.vec nv (Ty.vec n2 e2)) c a b), n ∈ ns)
    (hs : evalInstr calls s (.select d (Ty.vec nv (Ty.vec n2 e2)) c a b) = some s') :
    ∃ t', evalInstr calls t (.select d (Ty.vec nv (Ty.vec n2 e2)) c a b) = some t' ∧
      State.AgreeOn ns s' t' := by
  have hl : ∀ n ∈ Instr.uses (.select d (Ty.vec nv (Ty.vec n2 e2)) c a b),
      lookupName s.env n = lookupName t.env n :=
    fun n hn' => h.2.2.2 n (hread n hn')
  have hc : evalOperand s c = evalOperand t c :=
    evalOperand_agree_of_uses hl (by
      intro n hn'; cases c <;> simp_all [Instr.uses, Operand.regs])
  have ha : evalOperand s a = evalOperand t a :=
    evalOperand_agree_of_uses hl (by
      intro n hn'; cases a <;> simp_all [Instr.uses, Operand.regs])
  have hb : evalOperand s b = evalOperand t b :=
    evalOperand_agree_of_uses hl (by
      intro n hn'; cases b <;> simp_all [Instr.uses, Operand.regs])
  rcases hcv : evalOperand t c with _ | vc
  · simp [evalInstr, hc, hcv] at hs
  · cases vc with
    | int wc x => exact select_of_intBit calls h hc ha hb hcv hs
    | ptr a' => simp [evalInstr, hc, hcv] at hs
    | vec vn vw vs =>
      simp only [evalInstr, hc, ha, hb, hcv] at hs
      rcases vw with _ | k
      · simp at hs
      · rcases k with _ | j
        · simp at hs
        · simp at hs

/-- **The `select` transport.**  The result type fixes which arm can apply, so
each shape is proved at its own type and the `ty` match inside the vector arm
reduces definitionally. -/
theorem select_agree (calls : Calls) {ns : List String} {d : String} {ty : Ty}
    {c a b : Operand} {s t s' : State} (h : State.AgreeOn ns s t)
    (hread : ∀ n ∈ Instr.uses (.select d ty c a b), n ∈ ns)
    (hs : evalInstr calls s (.select d ty c a b) = some s') :
    ∃ t', evalInstr calls t (.select d ty c a b) = some t' ∧ State.AgreeOn ns s' t' := by
  cases ty with
  | int wt => exact select_int calls h hread hs
  | ptr => exact select_ptr calls h hread hs
  | void => exact select_void calls h hread hs
  | vec nv el =>
    cases el with
    | int wi => exact select_vecI calls h hread hs
    | ptr => exact select_vecP calls h hread hs
    | void => exact select_vecV calls h hread hs
    | vec n2 e2 => exact select_vecVv calls h hread hs

/-- **Consecutive-block transport: one instruction.**  If two states agree on the
names an instruction reads, the instruction's run succeeds at the second state
exactly where it does at the first, and the two results agree. -/
theorem evalInstr_agree (calls : Calls) {ns : List String} {i : Instr} {s t : State}
    (h : State.AgreeOn ns s t) (hread : ∀ n ∈ Instr.uses i, n ∈ ns)
    {s' : State} (hs : evalInstr calls s i = some s') :
    ∃ t', evalInstr calls t i = some t' ∧ State.AgreeOn ns s' t' := by
  have hm : s.mem = t.mem := h.1
  have hn : s.next = t.next := h.2.1
  have hp : s.pre = t.pre := h.2.2.1
  have hl : ∀ n ∈ Instr.uses i, lookupName s.env n = lookupName t.env n :=
    fun n hn' => h.2.2.2 n (hread n hn')
  cases i with
  | binop d bop w a b =>
    have ha := evalOperand_agree_of_uses hl (op := a) (by
      intro n hn'; cases a <;> simp_all [Instr.uses, Operand.regs])
    have hb := evalOperand_agree_of_uses hl (op := b) (by
      intro n hn'; cases b <;> simp_all [Instr.uses, Operand.regs])
    simp only [evalInstr, ha, hb] at hs
    repeat (split at hs)
    all_goals
      first
      | (cases hs
         exact ⟨_, by simp [evalInstr, *], State.AgreeOn.bind h⟩)
      | (cases hs)
  | icmp d pred w a b =>
    have ha := evalOperand_agree_of_uses hl (op := a) (by
      intro n hn'; cases a <;> simp_all [Instr.uses, Operand.regs])
    have hb := evalOperand_agree_of_uses hl (op := b) (by
      intro n hn'; cases b <;> simp_all [Instr.uses, Operand.regs])
    simp only [evalInstr, ha, hb] at hs
    repeat (split at hs)
    all_goals
      first
      | (cases hs
         exact ⟨_, by simp [evalInstr, *], State.AgreeOn.bind h⟩)
      | (cases hs)
  | icmpPtr d pred a b =>
    have ha := evalOperand_agree_of_uses hl (op := a) (by
      intro n hn'; cases a <;> simp_all [Instr.uses, Operand.regs])
    have hb := evalOperand_agree_of_uses hl (op := b) (by
      intro n hn'; cases b <;> simp_all [Instr.uses, Operand.regs])
    simp only [evalInstr, ha, hb] at hs
    rcases hva : evalOperand t a with _ | va
    · simp [hva] at hs
    · rcases hvb : evalOperand t b with _ | vb
      · simp [hva, hvb] at hs
      · cases va with
        | ptr x =>
          cases vb with
          | ptr y =>
            cases hr : evalICmpPtr pred x y with
            | none => simp [hva, hvb, hr] at hs
            | some r =>
              simp only [hva, hvb, hr, Option.map_some, Option.some.injEq] at hs
              cases hs
              exact ⟨_, by simp [evalInstr, *], State.AgreeOn.bind h⟩
          | int w z => simp [hva, hvb] at hs
          | vec n w l => simp [hva, hvb] at hs
        | int w z => simp [hva, hvb] at hs
        | vec n w l => simp [hva, hvb] at hs
  | select d ty c a b =>
    exact select_agree calls h hread hs
  | trunc d wIn wOut v =>
    have hv := evalOperand_agree_of_uses hl (op := v) (by
      intro n hn'; cases v <;> simp_all [Instr.uses, Operand.regs])
    simp only [evalInstr, hv] at hs
    repeat (split at hs)
    all_goals
      first
      | (cases hs
         exact ⟨_, by simp [evalInstr, *], State.AgreeOn.bind h⟩)
      | (cases hs)
  | zext d wIn wOut v =>
    have hv := evalOperand_agree_of_uses hl (op := v) (by
      intro n hn'; cases v <;> simp_all [Instr.uses, Operand.regs])
    simp only [evalInstr, hv] at hs
    repeat (split at hs)
    all_goals
      first
      | (cases hs
         exact ⟨_, by simp [evalInstr, *], State.AgreeOn.bind h⟩)
      | (cases hs)
  | sext d wIn wOut v =>
    have hv := evalOperand_agree_of_uses hl (op := v) (by
      intro n hn'; cases v <;> simp_all [Instr.uses, Operand.regs])
    simp only [evalInstr, hv] at hs
    repeat (split at hs)
    all_goals
      first
      | (cases hs
         exact ⟨_, by simp [evalInstr, *], State.AgreeOn.bind h⟩)
      | (cases hs)
  | alloca d ty align =>
    simp only [evalInstr, Option.some.injEq] at hs
    cases hs
    exact ⟨_, by simp only [evalInstr], State.AgreeOn.alloca h⟩
  | load d ty p =>
    have hp' := evalOperand_agree_of_uses hl (op := p) (by
      intro n hn'; cases p <;> simp_all [Instr.uses, Operand.regs])
    simp only [evalInstr, hp', hm] at hs
    repeat (split at hs)
    all_goals
      first
      | (cases hs
         exact ⟨_, by simp [evalInstr, *], State.AgreeOn.bind h⟩)
      | (cases hs)
  | store ty v p =>
    have hv := evalOperand_agree_of_uses hl (op := v) (by
      intro n hn'; cases v <;> simp_all [Instr.uses, Operand.regs])
    have hp' := evalOperand_agree_of_uses hl (op := p) (by
      intro n hn'; cases p <;> simp_all [Instr.uses, Operand.regs])
    simp only [evalInstr, hv, hp'] at hs
    repeat (split at hs)
    all_goals
      first
      | (cases hs)
      | (obtain ⟨t', hst, hag⟩ := storeValue_agree h hs
         exact ⟨t', by simp [evalInstr, *], hag⟩)
  | gep d elemTy base off =>
    have hbase := evalOperand_agree_of_uses hl (op := base) (by
      intro n hn'; cases base <;> simp_all [Instr.uses, Operand.regs])
    have hoff := evalOperand_agree_of_uses hl (op := off) (by
      intro n hn'; cases off <;> simp_all [Instr.uses, Operand.regs])
    simp only [evalInstr, hbase, hoff] at hs
    rcases hbv : evalOperand t base with _ | vb
    · simp [hbv] at hs
    · rcases hov : evalOperand t off with _ | vo
      · simp [hbv, hov] at hs
      · cases vb with
        | int wb y => simp [hbv, hov] at hs
        | vec n w l => simp [hbv, hov] at hs
        | ptr addr =>
          cases vo with
          | ptr z => simp [hbv, hov] at hs
          | vec n w l => simp [hbv, hov] at hs
          | int wi n =>
            by_cases hpos : (BitVec.signExtend 64 n).toNat < 2 ^ 63
            · simp only [hbv, hov, hpos] at hs
              cases hs
              exact ⟨_, by simp [evalInstr, *], State.AgreeOn.bind h⟩
            · by_cases hneg :
                (2 ^ 64 - (BitVec.signExtend 64 n).toNat) * elemTy.sizeBytes ≤ addr
              · simp only [hbv, hov, hpos, hneg] at hs
                cases hs
                exact ⟨_, by simp [evalInstr, *], State.AgreeOn.bind h⟩
              · simp [hbv, hov, hpos, hneg] at hs
  | icmpVec d pred n w a b =>
    have ha := evalOperand_agree_of_uses hl (op := a) (by
      intro n' hn'; cases a <;> simp_all [Instr.uses, Operand.regs])
    have hb := evalOperand_agree_of_uses hl (op := b) (by
      intro n' hn'; cases b <;> simp_all [Instr.uses, Operand.regs])
    simp only [evalInstr, ha, hb] at hs
    repeat (split at hs)
    all_goals
      first
      | (cases hs
         exact ⟨_, by simp [evalInstr, *], State.AgreeOn.bind h⟩)
      | (cases hs)
  | binopVec d bop n w a b =>
    have ha := evalOperand_agree_of_uses hl (op := a) (by
      intro n' hn'; cases a <;> simp_all [Instr.uses, Operand.regs])
    have hb := evalOperand_agree_of_uses hl (op := b) (by
      intro n' hn'; cases b <;> simp_all [Instr.uses, Operand.regs])
    simp only [evalInstr, ha, hb] at hs
    repeat (split at hs)
    all_goals
      first
      | (cases hs
         exact ⟨_, by simp [evalInstr, *], State.AgreeOn.bind h⟩)
      | (cases hs)
  | bitcastMask d n v =>
    have hv := evalOperand_agree_of_uses hl (op := v) (by
      intro n' hn'; cases v <;> simp_all [Instr.uses, Operand.regs])
    simp only [evalInstr, hv] at hs
    repeat (split at hs)
    all_goals
      first
      | (cases hs
         exact ⟨_, by simp [evalInstr, *], State.AgreeOn.bind h⟩)
      | (cases hs)
  | extractelement d n w v idx =>
    have hv := evalOperand_agree_of_uses hl (op := v) (by
      intro n' hn'; cases v <;> simp_all [Instr.uses, Operand.regs])
    have hidx := evalOperand_agree_of_uses hl (op := idx) (by
      intro n' hn'; cases idx <;> simp_all [Instr.uses, Operand.regs])
    simp only [evalInstr, hv, hidx] at hs
    repeat (split at hs)
    all_goals
      first
      | (cases hs
         exact ⟨_, by simp [evalInstr, *], State.AgreeOn.bind h⟩)
      | (cases hs)
  | insertelement d n w v elt idx =>
    have hv := evalOperand_agree_of_uses hl (op := v) (by
      intro n' hn'; cases v <;> simp_all [Instr.uses, Operand.regs])
    have helt := evalOperand_agree_of_uses hl (op := elt) (by
      intro n' hn'; cases elt <;> simp_all [Instr.uses, Operand.regs])
    have hidx := evalOperand_agree_of_uses hl (op := idx) (by
      intro n' hn'; cases idx <;> simp_all [Instr.uses, Operand.regs])
    simp only [evalInstr, hv, helt, hidx] at hs
    repeat (split at hs)
    all_goals
      first
      | (cases hs
         exact ⟨_, by simp [evalInstr, *], State.AgreeOn.bind h⟩)
      | (cases hs)
  | shuffleVec d n w a b mask =>
    have ha := evalOperand_agree_of_uses hl (op := a) (by
      intro n' hn'; cases a <;> simp_all [Instr.uses, Operand.regs])
    have hb := evalOperand_agree_of_uses hl (op := b) (by
      intro n' hn'; cases b <;> simp_all [Instr.uses, Operand.regs])
    simp only [evalInstr, ha, hb] at hs
    repeat (split at hs)
    all_goals
      first
      | (cases hs
         exact ⟨_, by simp [evalInstr, *], State.AgreeOn.bind h⟩)
      | (cases hs)
  | vecBitcast d n w m jw v =>
    have hv := evalOperand_agree_of_uses hl (op := v) (by
      intro n' hn'; cases v <;> simp_all [Instr.uses, Operand.regs])
    simp only [evalInstr, hv] at hs
    repeat (split at hs)
    all_goals
      first
      | (cases hs
         exact ⟨_, by simp [evalInstr, *], State.AgreeOn.bind h⟩)
      | (cases hs)
  | call d ty callee args =>
    have hargs : evalOperands s args = evalOperands t args :=
      evalOperands_agree args fun op hop' => by
        obtain ⟨⟨ty', op'⟩, hmem, rfl⟩ := List.mem_map.mp hop'
        exact evalOperand_agree_of_uses hl fun n hn' =>
          List.mem_flatten.mpr
            ⟨op'.regs, List.mem_map.mpr ⟨(ty', op'), hmem, rfl⟩, hn'⟩
    simp only [evalInstr, hargs, hm, hn] at hs
    repeat (split at hs)
    all_goals
      first
      | (cases hs
         exact ⟨_, by simp only [evalInstr, *], State.AgreeOn.call h⟩)
      | (cases hs)
  | callVoid callee args =>
    have hargs : evalOperands s args = evalOperands t args :=
      evalOperands_agree args fun op hop' => by
        obtain ⟨⟨ty', op'⟩, hmem, rfl⟩ := List.mem_map.mp hop'
        exact evalOperand_agree_of_uses hl fun n hn' =>
          List.mem_flatten.mpr
            ⟨op'.regs, List.mem_map.mpr ⟨(ty', op'), hmem, rfl⟩, hn'⟩
    simp only [evalInstr, hargs, hm, hn] at hs
    repeat (split at hs)
    all_goals
      first
      | (cases hs
         exact ⟨_, by simp only [evalInstr, *], State.AgreeOn.callVoid h⟩)
      | (cases hs)
  | phi d ty inc =>
    have hsel : phiSelect s inc = phiSelect t inc := phiSelect_agree h hread
    cases hsl : phiSelect t inc with
    | none => simp only [evalInstr, hsel, hsl] at hs; cases hs
    | some v =>
        simp only [evalInstr, hsel, hsl, Option.map_some, Option.some.injEq] at hs
        subst hs
        exact ⟨_, by simp only [evalInstr, hsl, Option.map_some],
          State.AgreeOn.bind h⟩

end Agreement

/-- Installing pending `phi` bindings never changes the lookup of a name they do
not bind. -/
theorem lookupName_bindAll_of_ne (s : State) :
    ∀ (pend : List (String × Value)) {n : String}, (∀ b ∈ pend, b.1 ≠ n) →
      lookupName (s.bindAll pend).env n = lookupName s.env n
  | [], _, _ => rfl
  | (m, v) :: rest, n, h => by
      have hm : m ≠ n := h (m, v) (List.mem_cons_self ..)
      have hrest : ∀ b ∈ rest, b.1 ≠ n :=
        fun b hb => h b (List.mem_cons_of_mem _ hb)
      have hstep : lookupName ((s.bind m v).bindAll rest).env n
          = lookupName (s.bind m v).env n := lookupName_bindAll_of_ne (s.bind m v) rest hrest
      have hb : lookupName (s.bind m v).env n = lookupName s.env n := by
        simp only [State.bind, lookupName_cons_ne v s.env hm]
      exact hstep.trans hb

/-- The register names a straight-line instruction list reads. -/
def instrsUses : List Instr → List String
  | [] => []
  | i :: is => i.uses ++ instrsUses is

/-- **Consecutive-block transport: a straight-line list.**  A completed
`denoteRun` at one state transports to any state that agrees on the list's read
set, and the two outcomes agree on that set.  This is `evalInstr_agree` once per
instruction, with the read set unchanged by the step: every instruction only
binds a destination, and a destination is not in the list's read set.  A leading
`phi` run transports as one step: its members select at the same snapshot, so
the bindings it installs are identical on both sides. -/
theorem denoteRun_agree (calls : Calls) :
    ∀ (pend : List (String × Value)) (is : List Instr) {ns : List String}
      {s t s' : State}, State.AgreeOn ns s t →
      (∀ n ∈ instrsUses is, n ∈ ns) →
      denoteRun calls pend is s = some s' →
      ∃ t', denoteRun calls pend is t = some t' ∧ State.AgreeOn ns s' t' := by
  intro pend is
  induction is generalizing pend with
  | nil =>
      intro ns s t s' h _ hs
      simp only [denoteRun, Option.some.injEq] at hs
      subst hs
      exact ⟨t.bindAll pend,
        by simp only [denoteRun], State.AgreeOn.bindAll pend h⟩
  | cons i rest ih =>
      intro ns s t s' h hread hs
      have hread_i : ∀ n ∈ Instr.uses i, n ∈ ns :=
        fun n hn => hread n (List.mem_append_left _ hn)
      have hread_is : ∀ n ∈ instrsUses rest, n ∈ ns :=
        fun n hn => hread n (List.mem_append_right _ hn)
      by_cases hphi : i.isPhi = true
      · obtain ⟨d, ty, inc, rfl⟩ : ∃ d ty inc, i = .phi d ty inc := by
          cases i with
          | phi d ty inc => exact ⟨d, ty, inc, rfl⟩
          | _ => simp_all [Instr.isPhi]
        simp only [denoteRun] at hs
        cases hsl : phiSelect s inc with
        | none => simp only [hsl] at hs; cases hs
        | some v =>
            simp only [hsl, Option.some.injEq] at hs
            have hsl' : phiSelect t inc = some v := by
              rw [← phiSelect_agree h hread_i]; exact hsl
            have h2 := ih (pend := pend ++ [(d, v)]) h hread_is hs
            obtain ⟨t1, ht1, hag⟩ := h2
            exact ⟨t1, by simp only [denoteRun, hsl', ht1], hag⟩
      · have hi : i.isPhi = false := by
          cases i <;> simp_all [Instr.isPhi]
        rw [denoteRun_cons_of hi] at hs
        rw [denoteRun_cons_of hi]
        cases he : evalInstr calls (s.bindAll pend) i with
        | none => simp only [he] at hs; cases hs
        | some s1 =>
            simp only [he, Option.some.injEq] at hs
            obtain ⟨t1, ht1, hag⟩ :=
              evalInstr_agree calls (State.AgreeOn.bindAll pend h) hread_i he
            have h2 := ih (pend := []) hag hread_is hs
            obtain ⟨t2, ht2, hag2⟩ := h2
            exact ⟨t2, by simp only [he, ht1, ht2], hag2⟩

/-- **Consecutive-block transport: a straight-line list.** -/
theorem denoteCode_agree (calls : Calls) (is : List Instr) {ns : List String}
    {s t s' : State} (h : State.AgreeOn ns s t)
    (hread : ∀ n ∈ instrsUses is, n ∈ ns)
    (hs : denoteCode calls is s = some s') :
    ∃ t', denoteCode calls is t = some t' ∧ State.AgreeOn ns s' t' :=
  denoteRun_agree calls [] is h hread hs

end LeanLLVM
