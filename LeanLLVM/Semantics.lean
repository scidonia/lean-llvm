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

/-- Machine state: register environment, memory, next free byte address, and
the block currently being executed. -/
structure State where
  env : Env
  mem : Mem
  next : Nat
  pc : String
  deriving Repr

/-- Bind a register to a value. -/
def State.bind (s : State) (n : String) (v : Value) : State :=
  { s with env := (n, v) :: s.env }

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

/-- The lanes of a vector value at lane width `w` and count `n`, or `none` when
the value is not a vector of exactly that shape.  The width is an argument, so
the caller fixes the lane type and the shape check is a boolean, not a cast. -/
def Value.vecLanes (n w : Nat) : Value → Option (List (BitVec w))
  | .vec n' w' l =>
      if h : w' = w then
        (if l.length = n ∧ n' = n then some (h ▸ l) else none)
      else none
  | _ => none

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

/-- Load a value of the given type from an address.  A byte that was never
written makes the load undefined. -/
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
  | .vec _ _ => none
  | .void => none

/-- Store a value at an address. -/
def storeValue (s : State) (ty : Ty) (v : Value) (addr : Nat) : Option State :=
  match ty, v with
  | .int w, .int w' x =>
      if w' = w then
        some { s with mem := writeBytes s.mem addr (natToBytes x.toNat ((w + 7) / 8)) }
      else none
  | .ptr, .ptr a => some { s with mem := writeBytes s.mem addr (natToBytes a 8) }
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
  | .select d _ty c a b =>
      match evalOperand s c, evalOperand s a, evalOperand s b with
      | some (.int 1 bit), some va, some vb =>
          if bit = (1 : BitVec 1) then some (s.bind d va)
          else if bit = (0 : BitVec 1) then some (s.bind d vb)
          else none
      | _, _, _ => none
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
  | .call d _ callee args =>
      match evalOperands s args with
      | some vs =>
          match calls callee vs s.mem s.next with
          | some r => some { s with env := (d, r.ret) :: s.env, mem := r.mem, next := r.next }
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

/-- Execute a straight-line instruction sequence. -/
def denoteCode (calls : Calls) : List Instr → State → Option State
  | [], s => some s
  | i :: is, s =>
      match evalInstr calls s i with
      | none => none
      | some s' => denoteCode calls is s'

/-- The effect of a terminator. -/
inductive Ctrl where
  | ub
  | ret (v : Option Value) (s : State)
  | jump (s : State)
  deriving Repr

/-- Execute a terminator in a state. -/
def execTerm (s : State) : Term → Ctrl
  | .ret .void none => .ret none s
  | .ret .void (some _) => .ub
  | .ret _ none => .ub
  | .ret _ (some v) =>
      match evalOperand s v with
      | some x => .ret (some x) s
      | none => .ub
  | .br dest => .jump { s with pc := dest }
  | .condbr c t f =>
      match evalOperand s c with
      | some (.int 1 bit) =>
          if bit = (1 : BitVec 1) then .jump { s with pc := t }
          else if bit = (0 : BitVec 1) then .jump { s with pc := f }
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

/-- Initial state for a call: parameters bound to the arguments, empty memory,
address `0` reserved for `null`, and the entry block loaded. -/
def initState (f : Function) (args : List Value) : State :=
  { env := (f.params.zip args).map fun (p, v) => (p.1, v)
    mem := [], next := 1, pc := f.entry?.getD "" }

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

end LeanLLVM
