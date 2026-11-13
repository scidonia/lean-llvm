/-
The six stage-2 helpers' emitted bodies: what the fragment pins, and what it proves.

`JsonStage2Helpers` states each helper's contract at the walk's call boundary and
proves it of `JsonStage2Body`'s model.  This module takes the next step: it
captures each helper's own `define` block — the text the walk's fixture leaves as
a `call` — from the same emission `capture-stage2.sh` derives the walk from, pins
the ones the fragment can express, and proves one of them against the contract
instances.

**The derivation.**  `probes/install/ir/capture-stage2-helpers.sh` applies
`capture-stage2.sh`'s source transform (`noinline` on every helper except
`s2_walk`), its compiler line, its `opt -passes=lower-switch` and its token
strip, then extracts each helper's own `define` block instead of the wrapper's.
`od_scalar_value` additionally takes the walk's own rewrites — its
`alloca double` becomes an appended pointer parameter, its refusal messages
become `null`, and its one `llvm.umin.i64` unfolds — because its conversion slot
is the walk's `%d.i`: the same object, staged the same way.  The script refuses
if a captured body stops being the symbol the walk's fixture declares, and it
writes `stage2.helpers.tsv`, one row per helper with its emitted shape and
whether the fragment has a representation for its body.

**Proved at the body level.**  `s2_init`'s body is one straight-line block and is
proved: `s2InitBody_run` runs it at `s2InitPre`'s staging and leaves exactly
`s2InitPost`'s memory, and `s2InitBody_contract` reads the instance's post and
footprint frame at that outcome.  The call environment is `stage2Calls noCalls`
— the walk's own intrinsic environment with no sub-unit — because the block calls
only `llvm.memset` and the lifetime markers.  No contract is restated: the post
is `s2InitPost` at the model's memory, and the frame is `stage2WriteStores_frame`
at `s2InitFoot`'s region with `s2InitStores_inside`'s membership, the two facts
`s2Init_framed` composes (the instance's `framed` is stated at the model's
literal outcome, and reading its projection across a fifteen-store term is the
cost `JsonStage2Helpers` records).

**Pinned, with the body proof open.**  `s2_value_pos` and `s2_after_value` are
programs of the fragment and are pinned to their parsed ASTs by `#guard`
(`s2ValuePosBody`, `s2AfterValueBody`), but their contracts are not proved of
their bodies here.  What remains is stated rather than implied:

* `s2_value_pos`: the four-arm trace needs the `phi` thread through `return`
  (the state's predecessor field, written by the jumps) and the byte-value
  plumbing (`load i8` binds `BitVec.ofNat 8 b.toNat` while the model reads
  `readByte`'s `UInt8`), plus the `and i8, -3 = 0` equivalence with
  `csv.toNat ∈ {0, 2}` that the model's second arm states.
* `s2_after_value`: the same byte plumbing, plus the 32-bit `sp + (-1)` read as
  `sp.toNat - 1` — the index both the type stack and the state stack are read at.

Both are stated at the same staging the contracts give, so neither is blocked by
a missing representation; the obligation is the trace, not a widening.

**The obstructions, measured.**  One body is expressible but its proof is
obstructed, one was outside the fragment and is now a program whose proof is
open, and one is still outside it:

* `od_scalar_value` is expressible after the walk's three rewrites and is pinned
  by shape (38 blocks, 145 instructions, four parameters).  Its proof is
  obstructed: its accepted path calls `num_fast_el1`, whose body this fragment
  cannot express, and it must match `outTag`'s hash chain and `emitBlobs`'
  reserve byte for byte.
* `s2_string_body` carries `ptrtoint`, which the fragment models as
  `Instr.ptrtoint` at the model's 64-bit pointer width; the step is exact below
  `2 ^ 64` and `ub` at or above it, so a use owes the staging's address bound.
  The body's other construct is its global-symbol operand `@.str.14`, which is an
  `Operand.global` read from the loader's assignment at the run's staging.  The
  body parses; its contents are pinned below.
* `num_fast_el1` carries `alloca [768 x i8]`, `alloca %struct.Stk` and the
  binary64 chain (`uitofp`, `fmul`, `fdiv`, `fneg`, `select double`), all of
  which the fragment models.  Its body is still outside the fragment, and the
  reader of the text names three surfaces the capture leaves in place: the
  extracted block is one `define`, so it carries no `%struct.Stk = type { … }`
  line and the parser takes a struct's extent from its `Layout` argument; its
  one `llvm.umin.i64` call is at `i64` with an immediate operand where the
  model's unsigned minimum is `@llvm.umin.i32` at `i32` with two operands; and
  `ashr exact`'s flag is refused by name.  Its text is not written to the tree:
  a fixture nothing can read is not a pin.  `stage2.helpers.tsv` records its
  shape (1 922 lines, 237 blocks, two aggregate allocas, thirty-eight
  floating-point sites) and those three grounds, and the capture refuses if the
  emission stops carrying the constructs it measures.  The literal spelling the
  reader used to refuse, `-0.000000e+00`, is read now: LLVM prints binary64 with
  the exponent's sign written and a sign in front of the mantissa, and the
  reader takes both (`tests/core-extension.lean` pins the form).

**One finding the body text carries.**  Where the model refuses, it writes the
error record's `ok` word and its offset (`stage2ErrSet`), and the helpers'
footprints name that record as a region sixteen bytes wide.  The emitted refusal
path also stores the record's `message` pointer at offset sixteen — pinned below
for `od_scalar_value` by `storesNullAt` — so the body writes at `e + 16`, which
the region `(e, 16)` does not cover.  A body-level `UnchangedOutside` at that
region would require the byte at `e + 16` unchanged, and the store does not leave
it so (`errorRegion_message_outside` is the arithmetic).  This module records the
gap and does not widen the contract: the region lists are `JsonStage2Helpers`'
and stay as they are.  What it means for a caller is that the error record's
staged extent (`stage2ErrorExtent`, 24 bytes) is the region a walk invariant must
claim, which is what the walk's own staged-writes list already does.
-/
import LeanLLVM.Parser
import LeanLLVM.Semantics
import LeanLLVM.Refinement.JsonStage2Helpers

set_option autoImplicit false

namespace LeanLLVM.Refinement

open LeanLLVM

/-! ### The fixtures -/

/-- `@s2_init`, from `probes/install/ir/stage2.helper.s2_init.ll`. -/
def s2InitSrc : String :=
  include_str "../../probes/install/ir/stage2.helper.s2_init.ll"

/-- `@s2_value_pos`. -/
def s2ValuePosSrc : String :=
  include_str "../../probes/install/ir/stage2.helper.s2_value_pos.ll"

/-- `@s2_after_value`. -/
def s2AfterValueSrc : String :=
  include_str "../../probes/install/ir/stage2.helper.s2_after_value.ll"

/-- `@s2_string_body`. -/
def s2StringBodySrc : String :=
  include_str "../../probes/install/ir/stage2.helper.s2_string_body.ll"

/-- `@od_scalar_value`, after the walk's three rewrites. -/
def odScalarValueSrc : String :=
  include_str "../../probes/install/ir/stage2.helper.od_scalar_value.ll"

/-- Parse a fixture and take its single function. -/
def firstFunction (src : String) : Option Function :=
  match parseModule src with
  | .ok m => m.functions.head?
  | .error _ => none

/-- Whether the parser accepts the text at all. -/
def parses (src : String) : Bool :=
  match parseModule src with
  | .ok _ => true
  | .error _ => false

/-- Whether the text carries a substring.  The marker a pin's control uses. -/
def hasSubstr (s p : String) : Bool := (s.splitOn p).length > 1

/-! ### The three bodies the fragment parses, as ASTs

Each literal below is the parser's own result written out: `capture-stage2-helpers.sh`
produced the text, and the `#guard` beside each definition asserts that parsing
the fixture returns exactly it.  The pin is a `#guard` rather than a `rfl`
proposition because the parser runs on `String` primitives, which the kernel does
not reduce.  The control is `s2InitBody_mutation`: the same text with one
immediate changed still parses, and it is not the pinned body.
-/

/-- `@s2_init`, as `probes/install/ir/stage2.helper.s2_init.ll` parses. -/
def s2InitBody : Function :=
{ name := "s2_init",
  retTy := Ty.void,
  params := [("%s", Ty.ptr),
             ("%b", Ty.ptr),
             ("%n", Ty.int 64),
             ("%nb", Ty.int 64),
             ("%ep", Ty.ptr)],
  blocks := [{ name := "entry",
               instrs := [Instr.store
                            (Ty.ptr)
                            (Operand.reg "%b")
                            (Operand.reg "%s"),
                          Instr.gep
                            "%n2"
                            (Ty.int 8)
                            (Operand.reg "%s")
                            (Operand.imm (Const.int 64 0x0000000000000008#64)),
                          Instr.store
                            (Ty.int 64)
                            (Operand.reg "%n")
                            (Operand.reg "%n2"),
                          Instr.gep
                            "%nb3"
                            (Ty.int 8)
                            (Operand.reg "%s")
                            (Operand.imm (Const.int 64 0x0000000000000010#64)),
                          Instr.store
                            (Ty.int 64)
                            (Operand.reg "%nb")
                            (Operand.reg "%nb3"),
                          Instr.gep
                            "%ix4"
                            (Ty.int 8)
                            (Operand.reg "%s")
                            (Operand.imm (Const.int 64 0x0000000000000018#64)),
                          Instr.gep
                            "%ep7"
                            (Ty.int 8)
                            (Operand.reg "%s")
                            (Operand.imm (Const.int 64 0x0000000000000030#64)),
                          Instr.callVoid
                            "llvm.memset.p0.i64"
                            [(Ty.ptr, Operand.reg "%ix4"),
                             (Ty.int 8, Operand.imm (Const.int 8 0x00#8)),
                             (Ty.int 64, Operand.imm (Const.int 64 0x0000000000000018#64)),
                             (Ty.int 1, Operand.imm (Const.int 1 0x0#1))],
                          Instr.store
                            (Ty.ptr)
                            (Operand.reg "%ep")
                            (Operand.reg "%ep7"),
                          Instr.gep
                            "%nsp"
                            (Ty.int 8)
                            (Operand.reg "%s")
                            (Operand.imm (Const.int 64 0x0000000000000038#64)),
                          Instr.callVoid
                            "llvm.memset.p0.i64"
                            [(Ty.ptr, Operand.reg "%nsp"),
                             (Ty.int 8, Operand.imm (Const.int 8 0x00#8)),
                             (Ty.int 64, Operand.imm (Const.int 64 0x0000000000000040#64)),
                             (Ty.int 1, Operand.imm (Const.int 1 0x0#1))]],
               term := Term.ret (Ty.void) none }] }

/-- `@s2_value_pos`, as `probes/install/ir/stage2.helper.s2_value_pos.ll` parses. -/
def s2ValuePosBody : Function :=
{ name := "s2_value_pos",
  retTy := Ty.int 32,
  params := [("%sp", Ty.int 32),
             ("%root_done", Ty.int 32),
             ("%ct", Ty.ptr),
             ("%cs", Ty.ptr)],
  blocks := [{ name := "entry",
               instrs := [Instr.icmp
                            "%cmp"
                            (IPred.eq)
                            32
                            (Operand.reg "%sp")
                            (Operand.imm (Const.int 32 0x00000000#32))],
               term := Term.condbr (Operand.reg "%cmp") "if.then" "if.end" },
             { name := "if.then",
               instrs := [Instr.icmp
                            "%tobool.not"
                            (IPred.eq)
                            32
                            (Operand.reg "%root_done")
                            (Operand.imm (Const.int 32 0x00000000#32))],
               term := Term.br "return" },
             { name := "if.end",
               instrs := [Instr.binop
                            "%sub"
                            (BinOp.add)
                            32
                            (Operand.reg "%sp")
                            (Operand.imm (Const.int 32 0xffffffff#32)),
                          Instr.zext "%idxprom" 32 64 (Operand.reg "%sub"),
                          Instr.gep
                            "%arrayidx"
                            (Ty.int 8)
                            (Operand.reg "%ct")
                            (Operand.reg "%idxprom"),
                          Instr.load "%0" (Ty.int 8) (Operand.reg "%arrayidx"),
                          Instr.icmp
                            "%cmp1"
                            (IPred.eq)
                            8
                            (Operand.reg "%0")
                            (Operand.imm (Const.int 8 0x01#8)),
                          Instr.gep
                            "%arrayidx5"
                            (Ty.int 8)
                            (Operand.reg "%cs")
                            (Operand.reg "%idxprom"),
                          Instr.load "%1" (Ty.int 8) (Operand.reg "%arrayidx5")],
               term := Term.condbr (Operand.reg "%cmp1") "if.then3" "if.end9" },
             { name := "if.then3",
               instrs := [Instr.icmp
                            "%cmp7"
                            (IPred.eq)
                            8
                            (Operand.reg "%1")
                            (Operand.imm (Const.int 8 0x02#8))],
               term := Term.br "return" },
             { name := "if.end9",
               instrs := [Instr.binop
                            "%2"
                            (BinOp.and)
                            8
                            (Operand.reg "%1")
                            (Operand.imm (Const.int 8 0xfd#8)),
                          Instr.icmp
                            "%narrow"
                            (IPred.eq)
                            8
                            (Operand.reg "%2")
                            (Operand.imm (Const.int 8 0x00#8))],
               term := Term.br "return" },
             { name := "return",
               instrs := [Instr.phi
                            "%retval.1.in"
                            (Ty.int 1)
                            [("if.then", Operand.reg "%tobool.not"),
                             ("if.then3", Operand.reg "%cmp7"),
                             ("if.end9", Operand.reg "%narrow")],
                          Instr.zext "%retval.1" 1 32 (Operand.reg "%retval.1.in")],
               term := Term.ret (Ty.int 32) (some (Operand.reg "%retval.1")) }] }

/-- `@s2_after_value`, as `probes/install/ir/stage2.helper.s2_after_value.ll` parses. -/
def s2AfterValueBody : Function :=
{ name := "s2_after_value",
  retTy := Ty.void,
  params := [("%sp.0.val", Ty.int 32),
             ("%root_done", Ty.ptr),
             ("%ct", Ty.ptr),
             ("%cs", Ty.ptr)],
  blocks := [{ name := "entry",
               instrs := [Instr.icmp
                            "%cmp"
                            (IPred.eq)
                            32
                            (Operand.reg "%sp.0.val")
                            (Operand.imm (Const.int 32 0x00000000#32))],
               term := Term.condbr (Operand.reg "%cmp") "if.then" "if.end" },
             { name := "if.then",
               instrs := [Instr.store
                            (Ty.int 32)
                            (Operand.imm (Const.int 32 0x00000001#32))
                            (Operand.reg "%root_done")],
               term := Term.br "return" },
             { name := "if.end",
               instrs := [Instr.binop
                            "%sub"
                            (BinOp.add)
                            32
                            (Operand.reg "%sp.0.val")
                            (Operand.imm (Const.int 32 0xffffffff#32)),
                          Instr.zext "%idxprom" 32 64 (Operand.reg "%sub"),
                          Instr.gep
                            "%arrayidx"
                            (Ty.int 8)
                            (Operand.reg "%ct")
                            (Operand.reg "%idxprom"),
                          Instr.load "%0" (Ty.int 8) (Operand.reg "%arrayidx"),
                          Instr.icmp
                            "%cmp1"
                            (IPred.eq)
                            8
                            (Operand.reg "%0")
                            (Operand.imm (Const.int 8 0x01#8)),
                          Instr.select
                            "%conv3"
                            (Ty.int 8)
                            (Operand.reg "%cmp1")
                            (Operand.imm (Const.int 8 0x03#8))
                            (Operand.imm (Const.int 8 0x01#8)),
                          Instr.gep
                            "%arrayidx5"
                            (Ty.int 8)
                            (Operand.reg "%cs")
                            (Operand.reg "%idxprom"),
                          Instr.store
                            (Ty.int 8)
                            (Operand.reg "%conv3")
                            (Operand.reg "%arrayidx5")],
               term := Term.br "return" },
             { name := "return", instrs := [], term := Term.ret (Ty.void) none }] }

-- Parsing `stage2.helper.s2_init.ll` returns `s2InitBody`.
#guard decide (firstFunction s2InitSrc = some s2InitBody)

-- Parsing `stage2.helper.s2_value_pos.ll` returns `s2ValuePosBody`.
#guard decide (firstFunction s2ValuePosSrc = some s2ValuePosBody)

-- Parsing `stage2.helper.s2_after_value.ll` returns `s2AfterValueBody`.
#guard decide (firstFunction s2AfterValueSrc = some s2AfterValueBody)

/-! #### The pin's control

`s2InitSrcMutated` is the same fixture with the `%s + 8` offset changed to
`%s + 12`: it parses, and it is not the pinned body, so the equality above is
about the text rather than about a search that would accept anything. -/
def s2InitSrcMutated : String := (s2InitSrc.replace "%s, i64 8" "%s, i64 12")

#guard parses s2InitSrcMutated
#guard decide (firstFunction s2InitSrcMutated ≠ some s2InitBody)

/-! #### `od_scalar_value`, pinned by shape

Its body is expressible and is the text this module pins; it is not proved here
(see the module header).  What the pin establishes is the shape the capture
checks and the refusal path's message store the footprint finding below names. -/
def odScalarValueBody : Option Function := firstFunction odScalarValueSrc

/-- Whether a body stores a null pointer into the register named.  The guard
below and its control are the marker's two readings: it finds the store where it
is, and not in a body that lacks it. -/
def storesNullAt (f : Function) (reg : String) : Bool :=
  f.blocks.any fun b => b.instrs.any fun i =>
    match i with
    | Instr.store .ptr (.imm .null) (.reg r) => r == reg
    | _ => false

-- The body parses, at the shape the capture records (38 blocks, 145 instructions).
#guard decide (odScalarValueBody.map
  (fun f => (f.name, f.blocks.length, (f.blocks.flatMap (·.instrs)).length, f.params.length)) =
    some ("od_scalar_value", 38, 145, 4))

-- The refusal path stores the error record's message pointer at offset sixteen.
#guard (match odScalarValueBody with
  | some f => storesNullAt f "%msg2.i.i"
  | none => false)

-- The control: the message store's marker does not fire on a body without it.
#guard (match firstFunction s2InitSrc with
  | some f => !storesNullAt f "%msg2.i.i"
  | none => false)

/-- **The message slot is outside the contract's error region.**  The helpers'
footprints name the refusal record as the region `(e, 16)`, the half-open range
`[e, e + 16)`; the emitted refusal path's third store is at `e + 16`, the region's
first byte past its end.  This is the gap the module header records: a body-level
`UnchangedOutside` at `(e, 16)` would require that byte unchanged, and the store
does not leave it so.  The lemma is the arithmetic only; the region is
`JsonStage2Helpers`' and this module does not widen it. -/
theorem errorRegion_message_outside (e : Nat) :
    ¬ (e ≤ e + 16 ∧ e + 16 < e + 16) := by omega

/-! #### `s2_string_body`: the conversions and the symbol

The capture writes the body to the tree, so what it parses to is a measurement
rather than a claim.  It carries the conversion pair and the global-symbol
operand; the marker below discriminates, because the sibling body carries
neither. -/
-- The fragment parses this text and the sibling beside it.
#guard parses s2StringBodySrc
#guard parses s2InitSrc
-- The construct the fragment has no term for, and the control that the marker
-- does not find it where the fragment does have terms.
#guard hasSubstr s2StringBodySrc "ptrtoint ptr"
#guard !hasSubstr s2InitSrc "ptrtoint ptr"

/-! ### The call environment and the staged state

The bodies call the two lifetime markers and `llvm.memset.p0.i64`, and nothing
else: `stage2Calls` resolves exactly those and sends anything else to `noCalls`,
where an unresolved call is `ub`.  A body this environment does not describe
therefore fails rather than being read as something it is not. -/
def s2HelperCalls : Calls := JsonStage2IR.stage2Calls noCalls

/-- The contract's staging as a state: the function's parameters bound to the
emitted call's arguments, the caller's memory and allocator state. -/
def stagedState (f : Function) (args : List Value) (mem : Mem) (next : Nat) : State :=
  { initState f args with mem := mem, next := next }

/-- `natToBytes` at zero is a zero run: the model's `wordBytes 8 0` is the eight
zero bytes a `memset` writes. -/
theorem natToBytes_zero (w : Nat) : natToBytes 0 w = List.replicate w (0 : UInt8) := by
  induction w with
  | zero => rfl
  | succ w ih => simp [natToBytes, List.replicate_succ, ih]

/-! ### Written zero bytes, chunked

`s2_init` clears the record's two field runs with `memset(…, 0, 24)` and
`memset(…, 0, 64)`; the model spells the same bytes as eight-byte zero stores.
The lemma below splits a zero run of `n + 8` bytes into `n` bytes and one
eight-byte word, so the two spellings meet at the model's own store list. -/
theorem writeBytes_replicate_zero_chunk (m : Mem) (a n : Nat) :
    writeBytes m a (List.replicate (n + 8) (0 : UInt8)) =
      writeBytes (writeBytes m a (List.replicate n (0 : UInt8))) (a + n)
        (List.replicate 8 (0 : UInt8)) := by
  induction n generalizing m a with
  | zero => simp [writeBytes]
  | succ n ih =>
      rw [show n + 1 + 8 = (n + 8) + 1 by omega, List.replicate_succ]
      simp only [writeBytes]
      rw [ih]
      rw [show a + 1 + n = a + (n + 1) by omega]
      rfl

/-- A zero run of twenty-four bytes is three eight-byte zero words. -/
theorem writeBytes_zero_24 (m : Mem) (a : Nat) :
    writeBytes m a (List.replicate 24 (0 : UInt8)) =
      writeBytes (writeBytes (writeBytes m a (List.replicate 8 (0 : UInt8))) (a + 8)
          (List.replicate 8 (0 : UInt8))) (a + 16) (List.replicate 8 (0 : UInt8)) := by
  rw [show (24 : Nat) = 16 + 8 from rfl, writeBytes_replicate_zero_chunk (n := 16)]
  rw [show (16 : Nat) = 8 + 8 from rfl, writeBytes_replicate_zero_chunk (n := 8)]

/-- A zero run of sixty-four bytes is eight eight-byte zero words. -/
theorem writeBytes_zero_64 (m : Mem) (a : Nat) :
    writeBytes m a (List.replicate 64 (0 : UInt8)) =
      writeBytes
        (writeBytes
          (writeBytes
            (writeBytes
              (writeBytes
                (writeBytes
                  (writeBytes
                    (writeBytes m a (List.replicate 8 (0 : UInt8)))
                    (a + 8) (List.replicate 8 (0 : UInt8)))
                  (a + 16) (List.replicate 8 (0 : UInt8)))
                (a + 24) (List.replicate 8 (0 : UInt8)))
              (a + 32) (List.replicate 8 (0 : UInt8)))
            (a + 40) (List.replicate 8 (0 : UInt8)))
          (a + 48) (List.replicate 8 (0 : UInt8)))
        (a + 56) (List.replicate 8 (0 : UInt8)) := by
  rw [show (64 : Nat) = 56 + 8 from rfl, writeBytes_replicate_zero_chunk (n := 56)]
  rw [show (56 : Nat) = 48 + 8 from rfl, writeBytes_replicate_zero_chunk (n := 48)]
  rw [show (48 : Nat) = 40 + 8 from rfl, writeBytes_replicate_zero_chunk (n := 40)]
  rw [show (40 : Nat) = 32 + 8 from rfl, writeBytes_replicate_zero_chunk (n := 32)]
  rw [show (32 : Nat) = 24 + 8 from rfl, writeBytes_replicate_zero_chunk (n := 24)]
  rw [show (24 : Nat) = 16 + 8 from rfl, writeBytes_replicate_zero_chunk (n := 16)]
  rw [show (16 : Nat) = 8 + 8 from rfl, writeBytes_replicate_zero_chunk (n := 8)]

/-! ### `s2_init`

The body is one straight-line block: the five argument stores, the two clears,
and the escape-plane store between them. -/

/-- **The body's run, at the contract's staging.**  One control step takes
`s2_init` from the emitted call's arguments to its return, and the memory it
leaves is the model's fifteen stores.  The register environment the block built
is not part of the statement: `runFuel`'s `ret` exposes the memory, and the
memory is what the contract's post names. -/
theorem s2InitBody_run (s b ep : Nat) (n nb : BitVec 64) (mem : Mem) (next : Nat) :
    runFuel s2HelperCalls 1 s2InitBody
        (stagedState s2InitBody [.ptr s, .ptr b, .int 64 n, .int 64 nb, .ptr ep]
          mem next) =
      some (.ret none (stage2WriteStores mem (s2InitStores s b n.toNat nb.toNat ep))) := by
  simp [-List.reduceReplicate, runFuel, step, s2InitBody, stagedState, initState,
    Function.findBlock, findBlockList, Function.entry?, List.head?, List.map, List.zip, List.zipWith,
    Option.map, Option.getD, denoteCode, denoteRun, State.bindAll, State.bind,
    evalInstr, evalOperand, evalOperands, execTerm, Const.toValue, storeValue,
    Ty.sizeBytes, s2HelperCalls, JsonStage2IR.stage2Calls, lookupName]
  rw [writeBytes_zero_24, writeBytes_zero_64]
  simp only [s2InitStores, stage2WriteStores, wordBytes, natToBytes_zero,
    Nat.add_assoc, Nat.reduceAdd, Nat.add_zero]

/-- **`s2_init`'s emitted body satisfies its contract.**  The body runs to
completion at `s2InitPre`'s staging, and the outcome built from its memory (the
allocator state is unchanged: the block holds no `alloca`) satisfies
`s2InitPost`, with the contract's own footprint frame.  The frame is
`stage2WriteStores_frame` at `s2InitFoot`'s region and `s2InitStores_inside`'s
membership — the two facts `s2Init_framed` composes — because the instance's
`framed` is stated at the model's literal outcome, and reading its projection
across a fifteen-store term is the cost §`JsonStage2Helpers` records. -/
theorem s2InitBody_contract {args : List Value} {mem : Mem} {next : Nat}
    (hpre : s2InitPre args mem next) :
    ∃ m' : Mem,
      runFuel s2HelperCalls 1 s2InitBody (stagedState s2InitBody args mem next) =
        some (.ret none m') ∧
      s2InitPost args mem next ⟨voidRet, m', next⟩ ∧
      UnchangedOutside mem m' (s2InitFoot args mem next) := by
  obtain ⟨s, b, ep, n, nb, rfl⟩ := hpre
  refine ⟨_, s2InitBody_run s b ep n nb mem next, ?_, ?_⟩
  · simp only [s2InitPost]
    refine ⟨?_, ?_, ?_⟩ <;> trivial
  · simp only [s2InitFoot]
    exact stage2WriteStores_frame (fun p hp =>
      ⟨(s, stage2StateExtent), List.mem_cons_self ..,
        s2InitStores_inside s b n.toNat nb.toNat ep hp⟩)

/-! ### Axiom footprints

The statement and the frame steps it reads, pinned with `#guard_msgs` so the
build checks the footprint rather than printing it.  The control that the
instrument discriminates is `lean --run` on a throwaway declaration proved with
`sorry`: it prints `sorryAx` under the same command, which is the check §7.6
records.  No `sorry` is in this module. -/
/-- info: 'LeanLLVM.Refinement.s2InitBody_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms s2InitBody_run

/-- info: 'LeanLLVM.Refinement.s2InitBody_contract' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms s2InitBody_contract

/-- info: 'LeanLLVM.Refinement.writeBytes_replicate_zero_chunk' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms writeBytes_replicate_zero_chunk

/-- info: 'LeanLLVM.Refinement.stage2WriteStores_frame' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms stage2WriteStores_frame

end LeanLLVM.Refinement
