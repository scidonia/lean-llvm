/-
An emitted-IR bridge for the assembled pipeline.

`probes/install/ir/json-pipeline.candidate.ll` is the emission of
`kernel/json/pipeline.c` — the caller of the five stage-1 units — at the
measured compiler line, normalised.  `probes/install/ir/capture-pipeline.sh`
records the invocation and derives, by diffing its own clang block against what
it emits, every item the normalisation took out (`json-pipeline.strip.tsv`, by
class, and its own reconstruction of the emission from those rows), the fact
that nothing is rewritten (`json-pipeline.rewrites.tsv`), and the fixture's own
construct inventory (`json-pipeline.inventory`, opcodes and call targets).

This module parses the file and pins the parsed AST against the literal below.
The pin is a `#guard` rather than a `rfl` proposition because the parser runs on
`String` primitives, which the kernel does not reduce, so a proposition about a
`parseModule` result cannot be closed by reflexivity.  What the pin buys is that
the hand-written AST and the committed text are the same object: a change to
either that the other does not carry fails elaboration, and no theorem below can
be stated about a body the text does not contain.

## The census, and why four call sites share one symbol

The pipeline's call targets are read out of the pinned AST, not recalled:
`callTargets` enumerates them and the guards below hold the emitted multiset —
`@leanllvm_json_s1_masks` four times, and each of `@leanllvm_json_entry_pos8`,
`@leanllvm_json_entry_b8` and `@leanllvm_json_escape_list` twice, plus
`@leanllvm_json_utf8` and `@leanllvm_json_stage2` once.  The repeats are not a
second call in the source: they are the emission's loop unswitching, which
duplicates the block loop once per value of the `arm` selector's bits 0 and 1
(`arm & 1` selects the entry emitter, `arm & 2` the escape-list gate).  Each
duplicate is a real call site in the body the theorem runs, and the loop
invariant below carries the arm, which is what selects the site that runs.

`callArgs` records each site's argument *types*, and `abiAgrees` checks every
site against the ABI its unit's header declares (`pipeline.h` and the four unit
headers) — callee's return type and argument type list.  That is the executed
form of "the pinning argument lists per call site": a call whose shape drifts
from the ABI fails elaboration here rather than becoming a proof obligation
somewhere else.

## `pipelineCalls`, and the one symbol the tree does not provide

Six of the pipeline's callees are the units whose bodies and records this tree
holds, so `pipelineCalls` resolves them through `envForUnit` at their own
record, their own intrinsic environment and a reservation of `0` — every unit's
ABI takes caller-provided buffers with their capacity in its record's `pre`, so
no unit moves the allocator and the reservation is `Nat.le_refl`.  The
escape-list call is the one whose record and intrinsic environment are
themselves indexed: its budget is `escapePositionsBudget` and its batch call is
resolved at `Γ_xl_batch`.

The seventh callee, `@leanllvm_json_stage2`, has no body in this tree, so its
selection is a **parameter** of the environment: `stage2Sel`.  Its record does
exist — `JsonStage2Contract` defines `Γ_stage2` and builds the bundle at it with
`pipeline_satisfies_at_stage2` — but a record is not a selection.  A caller
supplies the selection with `envForUnit stage2Sym Γ_stage2 stage2Calls
stage2Body` once the body exists, and `pipeline_satisfies_of_units` takes the
corresponding `CallSatisfies` as one of its seven hypotheses.  What is still
absent is the body itself: `stage2Body`, `stage2Calls` and a
`stage2_satisfies` instance.  A body that called
a symbol no slot resolved would be a `ub` at that call rather than a compile
error, which is why the census guards are `#guard`s: a callee outside the six
plus the slot fails elaboration.

## What is proved elsewhere

The bodies and records of the six units live in their own modules; this module
contributes the fixture, the pin, the census and the call environment, and
`JsonPipelineRefine` states and proves the pipeline's loop induction against
them.
-/
import LeanLLVM.Memory
import LeanLLVM.Parser
import LeanLLVM.Refinement.Refinement
import LeanLLVM.Refinement.JsonUnitContracts
import LeanLLVM.Refinement.JsonEscapeListContract

namespace LeanLLVM.Refinement.JsonPipelineIR

open LeanLLVM
open LeanLLVM.Refinement.JsonS1MasksIR (s1Calls s1MasksFunction)
open LeanLLVM.Refinement.JsonEntryIR (entryCalls entryPos8Function entryB8Function)
open LeanLLVM.Refinement.JsonUtf8IR (utf8Calls utf8Function)
open LeanLLVM.Refinement.JsonEscapeIR (escapeListCalls escapeListFunction)

/-! ### The fixture -/

/-- The assembled pipeline as emitted and committed. -/
def pipelineSrc : String :=
  include_str "../../probes/install/ir/json-pipeline.candidate.ll"

/-- Parse a fixture and take its single function. -/
def firstFunction (src : String) : Option Function :=
  match parseModule src with
  | .ok m => m.functions.head?
  | .error _ => none

/-! ### The pinned AST

The body, instruction by instruction, in the order the fixture holds it: twelve
blocks — the entry, the arm-specialised loops, the loop exit and the tail.  An
integer literal is spelled by `lit`, and only by `lit`, so the literal below
carries a width and a signed value rather than the emission's hexadecimal
spelling of the same bits. -/

/-- An integer literal of width `w`, from its signed value. -/
def lit (w : Nat) (v : Int) : Operand := .imm (.int w (BitVec.ofInt w v))

/-- The assembled pipeline's body: the block loop, the loop exit and the tail. -/
def pipelineBody : Function :=
{ name := "leanllvm_json_pipeline",
  retTy := Ty.int 64,
  params := [("%b", Ty.ptr),
             ("%n", Ty.int 64),
             ("%sc", Ty.ptr),
             ("%mk", Ty.ptr),
             ("%entw", Ty.ptr),
             ("%ep", Ty.ptr),
             ("%epcap", Ty.int 64),
             ("%nk", Ty.ptr),
             ("%xp", Ty.ptr),
             ("%xpcap", Ty.int 64),
             ("%nxp", Ty.ptr),
             ("%xcarry", Ty.ptr),
             ("%dst", Ty.ptr),
             ("%dstcap", Ty.int 64),
             ("%ndst", Ty.ptr),
             ("%ev", Ty.ptr),
             ("%evcap", Ty.int 64),
             ("%nev", Ty.ptr),
             ("%err", Ty.ptr),
             ("%arm", Ty.int 64)],
  blocks := [{ name := "entry",
               instrs := [Instr.binop
                            "%add"
                            (BinOp.add)
                            64
                            (Operand.reg "%n")
                            (lit 64 63),
                          Instr.binop
                            "%shr"
                            (BinOp.lshr)
                            64
                            (Operand.reg "%add")
                            (lit 64 6),
                          Instr.load "%0" (Ty.int 64) (Operand.reg "%nk"),
                          Instr.icmp
                            "%cmp79.not"
                            (IPred.ult)
                            64
                            (Operand.reg "%add")
                            (lit 64 64)],
               term := Term.condbr (Operand.reg "%cmp79.not") "for.cond.cleanup" "for.body.lr.ph" },
             { name := "for.body.lr.ph",
               instrs := [Instr.gep
                            "%delim"
                            (Ty.int 8)
                            (Operand.reg "%mk")
                            (lit 64 8),
                          Instr.gep
                            "%in_string"
                            (Ty.int 8)
                            (Operand.reg "%mk")
                            (lit 64 16),
                          Instr.gep
                            "%ws"
                            (Ty.int 8)
                            (Operand.reg "%mk")
                            (lit 64 24),
                          Instr.binop
                            "%and19"
                            (BinOp.and)
                            64
                            (Operand.reg "%arm")
                            (lit 64 1),
                          Instr.icmp
                            "%tobool.not"
                            (IPred.eq)
                            64
                            (Operand.reg "%and19")
                            (lit 64 0),
                          Instr.binop
                            "%and23"
                            (BinOp.and)
                            64
                            (Operand.reg "%arm")
                            (lit 64 2),
                          Instr.icmp
                            "%tobool24.not"
                            (IPred.eq)
                            64
                            (Operand.reg "%and23")
                            (lit 64 0),
                          Instr.gep
                            "%backslash"
                            (Ty.int 8)
                            (Operand.reg "%mk")
                            (lit 64 32),
                          Instr.gep
                            "%ctl"
                            (Ty.int 8)
                            (Operand.reg "%mk")
                            (lit 64 40)],
               term := Term.condbr
                         (Operand.reg "%tobool.not")
                         "for.body.lr.ph.split.us"
                         "for.body.lr.ph.split" },
             { name := "for.body.lr.ph.split.us",
               instrs := [],
               term := Term.condbr (Operand.reg "%tobool24.not") "for.body.us.us" "for.body.us" },
             { name := "for.body.us.us",
               instrs := [Instr.phi
                            "%prevS.082.us.us"
                            (Ty.int 64)
                            [("for.body.us.us", Operand.reg "%shr13.us.us"),
                             ("for.body.lr.ph.split.us",
                              lit 64 0)],
                          Instr.phi
                            "%k.081.us.us"
                            (Ty.int 64)
                            [("for.body.us.us", Operand.reg "%call21.us.us"),
                             ("for.body.lr.ph.split.us", Operand.reg "%0")],
                          Instr.phi
                            "%i.080.us.us"
                            (Ty.int 64)
                            [("for.body.us.us", Operand.reg "%inc.us.us"),
                             ("for.body.lr.ph.split.us",
                              lit 64 0)],
                          Instr.binop
                            "%shl.us.us"
                            (BinOp.shl)
                            64
                            (Operand.reg "%i.080.us.us")
                            (lit 64 6),
                          Instr.gep
                            "%add.ptr.us.us"
                            (Ty.int 8)
                            (Operand.reg "%b")
                            (Operand.reg "%shl.us.us"),
                          Instr.callVoid
                            "leanllvm_json_s1_masks"
                            [(Ty.ptr, Operand.reg "%add.ptr.us.us"),
                             (Ty.ptr, Operand.reg "%sc"),
                             (Ty.ptr, Operand.reg "%mk")],
                          Instr.load "%1" (Ty.int 64) (Operand.reg "%mk"),
                          Instr.load "%2" (Ty.int 64) (Operand.reg "%delim"),
                          Instr.load "%3" (Ty.int 64) (Operand.reg "%in_string"),
                          Instr.load "%4" (Ty.int 64) (Operand.reg "%ws"),
                          Instr.binop
                            "%5"
                            (BinOp.or)
                            64
                            (Operand.reg "%1")
                            (Operand.reg "%4"),
                          Instr.binop
                            "%6"
                            (BinOp.or)
                            64
                            (Operand.reg "%5")
                            (Operand.reg "%2"),
                          Instr.binop
                            "%or2.us.us"
                            (BinOp.or)
                            64
                            (Operand.reg "%6")
                            (Operand.reg "%3"),
                          Instr.binop
                            "%not.us.us"
                            (BinOp.xor)
                            64
                            (Operand.reg "%or2.us.us")
                            (lit 64 (-1)),
                          Instr.binop
                            "%not6.us.us"
                            (BinOp.xor)
                            64
                            (Operand.reg "%3")
                            (lit 64 (-1)),
                          Instr.binop
                            "%and.us.us"
                            (BinOp.and)
                            64
                            (Operand.reg "%2")
                            (Operand.reg "%not6.us.us"),
                          Instr.binop
                            "%shl8.us.us"
                            (BinOp.shl)
                            64
                            (Operand.reg "%not.us.us")
                            (lit 64 1),
                          Instr.binop
                            "%or9.us.us"
                            (BinOp.or)
                            64
                            (Operand.reg "%shl8.us.us")
                            (Operand.reg "%prevS.082.us.us"),
                          Instr.binop
                            "%not10.us.us"
                            (BinOp.xor)
                            64
                            (Operand.reg "%or9.us.us")
                            (lit 64 (-1)),
                          Instr.binop
                            "%and11.us.us"
                            (BinOp.and)
                            64
                            (Operand.reg "%not10.us.us")
                            (Operand.reg "%not.us.us"),
                          Instr.binop
                            "%7"
                            (BinOp.or)
                            64
                            (Operand.reg "%and.us.us")
                            (Operand.reg "%and11.us.us"),
                          Instr.binop
                            "%or12.us.us"
                            (BinOp.or)
                            64
                            (Operand.reg "%7")
                            (Operand.reg "%1"),
                          Instr.binop
                            "%shr13.us.us"
                            (BinOp.lshr)
                            64
                            (Operand.reg "%not.us.us")
                            (lit 64 63),
                          Instr.binop
                            "%sub.us.us"
                            (BinOp.sub)
                            64
                            (Operand.reg "%n")
                            (Operand.reg "%shl.us.us"),
                          Instr.icmp
                            "%cmp15.us.us"
                            (IPred.ult)
                            64
                            (Operand.reg "%sub.us.us")
                            (lit 64 64),
                          Instr.binop
                            "%notmask.us.us"
                            (BinOp.shl)
                            64
                            (lit 64 (-1))
                            (Operand.reg "%sub.us.us"),
                          Instr.binop
                            "%sub17.us.us"
                            (BinOp.xor)
                            64
                            (Operand.reg "%notmask.us.us")
                            (lit 64 (-1)),
                          Instr.select
                            "%and18.us.us"
                            (Ty.int 64)
                            (Operand.reg "%cmp15.us.us")
                            (Operand.reg "%sub17.us.us")
                            (lit 64 (-1)),
                          Instr.binop
                            "%ent.0.us.us"
                            (BinOp.and)
                            64
                            (Operand.reg "%or12.us.us")
                            (Operand.reg "%and18.us.us"),
                          Instr.store
                            (Ty.int 64)
                            (Operand.reg "%ent.0.us.us")
                            (Operand.reg "%entw"),
                          Instr.call
                            "%call21.us.us"
                            (Ty.int 64)
                            "leanllvm_json_entry_pos8"
                            [(Ty.ptr, Operand.reg "%entw"),
                             (Ty.int 64, Operand.reg "%i.080.us.us"),
                             (Ty.int 64, lit 64 1),
                             (Ty.ptr, Operand.reg "%ep"),
                             (Ty.int 64, Operand.reg "%k.081.us.us")],
                          Instr.binop
                            "%inc.us.us"
                            (BinOp.add)
                            64
                            (Operand.reg "%i.080.us.us")
                            (lit 64 1),
                          Instr.icmp
                            "%exitcond116.not"
                            (IPred.eq)
                            64
                            (Operand.reg "%inc.us.us")
                            (Operand.reg "%shr")],
               term := Term.condbr
                         (Operand.reg "%exitcond116.not")
                         "for.cond.cleanup"
                         "for.body.us.us" },
             { name := "for.body.us",
               instrs := [Instr.phi
                            "%prevS.082.us"
                            (Ty.int 64)
                            [("for.body.us", Operand.reg "%shr13.us"),
                             ("for.body.lr.ph.split.us",
                              lit 64 0)],
                          Instr.phi
                            "%k.081.us"
                            (Ty.int 64)
                            [("for.body.us", Operand.reg "%call21.us"),
                             ("for.body.lr.ph.split.us", Operand.reg "%0")],
                          Instr.phi
                            "%i.080.us"
                            (Ty.int 64)
                            [("for.body.us", Operand.reg "%inc.us"),
                             ("for.body.lr.ph.split.us",
                              lit 64 0)],
                          Instr.binop
                            "%shl.us"
                            (BinOp.shl)
                            64
                            (Operand.reg "%i.080.us")
                            (lit 64 6),
                          Instr.gep
                            "%add.ptr.us"
                            (Ty.int 8)
                            (Operand.reg "%b")
                            (Operand.reg "%shl.us"),
                          Instr.callVoid
                            "leanllvm_json_s1_masks"
                            [(Ty.ptr, Operand.reg "%add.ptr.us"),
                             (Ty.ptr, Operand.reg "%sc"),
                             (Ty.ptr, Operand.reg "%mk")],
                          Instr.load "%8" (Ty.int 64) (Operand.reg "%mk"),
                          Instr.load "%9" (Ty.int 64) (Operand.reg "%delim"),
                          Instr.load "%10" (Ty.int 64) (Operand.reg "%in_string"),
                          Instr.load "%11" (Ty.int 64) (Operand.reg "%ws"),
                          Instr.binop
                            "%12"
                            (BinOp.or)
                            64
                            (Operand.reg "%8")
                            (Operand.reg "%11"),
                          Instr.binop
                            "%13"
                            (BinOp.or)
                            64
                            (Operand.reg "%12")
                            (Operand.reg "%9"),
                          Instr.binop
                            "%or2.us"
                            (BinOp.or)
                            64
                            (Operand.reg "%13")
                            (Operand.reg "%10"),
                          Instr.binop
                            "%not.us"
                            (BinOp.xor)
                            64
                            (Operand.reg "%or2.us")
                            (lit 64 (-1)),
                          Instr.binop
                            "%not6.us"
                            (BinOp.xor)
                            64
                            (Operand.reg "%10")
                            (lit 64 (-1)),
                          Instr.binop
                            "%and.us"
                            (BinOp.and)
                            64
                            (Operand.reg "%9")
                            (Operand.reg "%not6.us"),
                          Instr.binop
                            "%shl8.us"
                            (BinOp.shl)
                            64
                            (Operand.reg "%not.us")
                            (lit 64 1),
                          Instr.binop
                            "%or9.us"
                            (BinOp.or)
                            64
                            (Operand.reg "%shl8.us")
                            (Operand.reg "%prevS.082.us"),
                          Instr.binop
                            "%not10.us"
                            (BinOp.xor)
                            64
                            (Operand.reg "%or9.us")
                            (lit 64 (-1)),
                          Instr.binop
                            "%and11.us"
                            (BinOp.and)
                            64
                            (Operand.reg "%not10.us")
                            (Operand.reg "%not.us"),
                          Instr.binop
                            "%14"
                            (BinOp.or)
                            64
                            (Operand.reg "%and.us")
                            (Operand.reg "%and11.us"),
                          Instr.binop
                            "%or12.us"
                            (BinOp.or)
                            64
                            (Operand.reg "%14")
                            (Operand.reg "%8"),
                          Instr.binop
                            "%shr13.us"
                            (BinOp.lshr)
                            64
                            (Operand.reg "%not.us")
                            (lit 64 63),
                          Instr.binop
                            "%sub.us"
                            (BinOp.sub)
                            64
                            (Operand.reg "%n")
                            (Operand.reg "%shl.us"),
                          Instr.icmp
                            "%cmp15.us"
                            (IPred.ult)
                            64
                            (Operand.reg "%sub.us")
                            (lit 64 64),
                          Instr.binop
                            "%notmask.us"
                            (BinOp.shl)
                            64
                            (lit 64 (-1))
                            (Operand.reg "%sub.us"),
                          Instr.binop
                            "%sub17.us"
                            (BinOp.xor)
                            64
                            (Operand.reg "%notmask.us")
                            (lit 64 (-1)),
                          Instr.select
                            "%and18.us"
                            (Ty.int 64)
                            (Operand.reg "%cmp15.us")
                            (Operand.reg "%sub17.us")
                            (lit 64 (-1)),
                          Instr.binop
                            "%ent.0.us"
                            (BinOp.and)
                            64
                            (Operand.reg "%or12.us")
                            (Operand.reg "%and18.us"),
                          Instr.store
                            (Ty.int 64)
                            (Operand.reg "%ent.0.us")
                            (Operand.reg "%entw"),
                          Instr.call
                            "%call21.us"
                            (Ty.int 64)
                            "leanllvm_json_entry_pos8"
                            [(Ty.ptr, Operand.reg "%entw"),
                             (Ty.int 64, Operand.reg "%i.080.us"),
                             (Ty.int 64, lit 64 1),
                             (Ty.ptr, Operand.reg "%ep"),
                             (Ty.int 64, Operand.reg "%k.081.us")],
                          Instr.load "%15" (Ty.int 64) (Operand.reg "%backslash"),
                          Instr.load "%16" (Ty.int 64) (Operand.reg "%ctl"),
                          Instr.load "%17" (Ty.int 64) (Operand.reg "%in_string"),
                          Instr.callVoid
                            "leanllvm_json_escape_list"
                            [(Ty.int 64, Operand.reg "%15"),
                             (Ty.int 64, Operand.reg "%16"),
                             (Ty.int 64, Operand.reg "%17"),
                             (Ty.int 64, Operand.reg "%i.080.us"),
                             (Ty.ptr, Operand.reg "%xp"),
                             (Ty.ptr, Operand.reg "%nxp"),
                             (Ty.ptr, Operand.reg "%xcarry")],
                          Instr.binop
                            "%inc.us"
                            (BinOp.add)
                            64
                            (Operand.reg "%i.080.us")
                            (lit 64 1),
                          Instr.icmp
                            "%exitcond115.not"
                            (IPred.eq)
                            64
                            (Operand.reg "%inc.us")
                            (Operand.reg "%shr")],
               term := Term.condbr
                         (Operand.reg "%exitcond115.not")
                         "for.cond.cleanup"
                         "for.body.us" },
             { name := "for.body.lr.ph.split",
               instrs := [],
               term := Term.condbr (Operand.reg "%tobool24.not") "for.body.us83" "for.body" },
             { name := "for.body.us83",
               instrs := [Instr.phi
                            "%prevS.082.us84"
                            (Ty.int 64)
                            [("for.body.us83", Operand.reg "%shr13.us98"),
                             ("for.body.lr.ph.split",
                              lit 64 0)],
                          Instr.phi
                            "%k.081.us85"
                            (Ty.int 64)
                            [("for.body.us83", Operand.reg "%call.us"),
                             ("for.body.lr.ph.split", Operand.reg "%0")],
                          Instr.phi
                            "%i.080.us86"
                            (Ty.int 64)
                            [("for.body.us83", Operand.reg "%inc.us106"),
                             ("for.body.lr.ph.split",
                              lit 64 0)],
                          Instr.binop
                            "%shl.us87"
                            (BinOp.shl)
                            64
                            (Operand.reg "%i.080.us86")
                            (lit 64 6),
                          Instr.gep
                            "%add.ptr.us88"
                            (Ty.int 8)
                            (Operand.reg "%b")
                            (Operand.reg "%shl.us87"),
                          Instr.callVoid
                            "leanllvm_json_s1_masks"
                            [(Ty.ptr, Operand.reg "%add.ptr.us88"),
                             (Ty.ptr, Operand.reg "%sc"),
                             (Ty.ptr, Operand.reg "%mk")],
                          Instr.load "%18" (Ty.int 64) (Operand.reg "%mk"),
                          Instr.load "%19" (Ty.int 64) (Operand.reg "%delim"),
                          Instr.load "%20" (Ty.int 64) (Operand.reg "%in_string"),
                          Instr.load "%21" (Ty.int 64) (Operand.reg "%ws"),
                          Instr.binop
                            "%22"
                            (BinOp.or)
                            64
                            (Operand.reg "%18")
                            (Operand.reg "%21"),
                          Instr.binop
                            "%23"
                            (BinOp.or)
                            64
                            (Operand.reg "%22")
                            (Operand.reg "%19"),
                          Instr.binop
                            "%or2.us89"
                            (BinOp.or)
                            64
                            (Operand.reg "%23")
                            (Operand.reg "%20"),
                          Instr.binop
                            "%not.us90"
                            (BinOp.xor)
                            64
                            (Operand.reg "%or2.us89")
                            (lit 64 (-1)),
                          Instr.binop
                            "%not6.us91"
                            (BinOp.xor)
                            64
                            (Operand.reg "%20")
                            (lit 64 (-1)),
                          Instr.binop
                            "%and.us92"
                            (BinOp.and)
                            64
                            (Operand.reg "%19")
                            (Operand.reg "%not6.us91"),
                          Instr.binop
                            "%shl8.us93"
                            (BinOp.shl)
                            64
                            (Operand.reg "%not.us90")
                            (lit 64 1),
                          Instr.binop
                            "%or9.us94"
                            (BinOp.or)
                            64
                            (Operand.reg "%shl8.us93")
                            (Operand.reg "%prevS.082.us84"),
                          Instr.binop
                            "%not10.us95"
                            (BinOp.xor)
                            64
                            (Operand.reg "%or9.us94")
                            (lit 64 (-1)),
                          Instr.binop
                            "%and11.us96"
                            (BinOp.and)
                            64
                            (Operand.reg "%not10.us95")
                            (Operand.reg "%not.us90"),
                          Instr.binop
                            "%24"
                            (BinOp.or)
                            64
                            (Operand.reg "%and.us92")
                            (Operand.reg "%and11.us96"),
                          Instr.binop
                            "%or12.us97"
                            (BinOp.or)
                            64
                            (Operand.reg "%24")
                            (Operand.reg "%18"),
                          Instr.binop
                            "%shr13.us98"
                            (BinOp.lshr)
                            64
                            (Operand.reg "%not.us90")
                            (lit 64 63),
                          Instr.binop
                            "%sub.us99"
                            (BinOp.sub)
                            64
                            (Operand.reg "%n")
                            (Operand.reg "%shl.us87"),
                          Instr.icmp
                            "%cmp15.us100"
                            (IPred.ult)
                            64
                            (Operand.reg "%sub.us99")
                            (lit 64 64),
                          Instr.binop
                            "%notmask.us101"
                            (BinOp.shl)
                            64
                            (lit 64 (-1))
                            (Operand.reg "%sub.us99"),
                          Instr.binop
                            "%sub17.us102"
                            (BinOp.xor)
                            64
                            (Operand.reg "%notmask.us101")
                            (lit 64 (-1)),
                          Instr.select
                            "%and18.us103"
                            (Ty.int 64)
                            (Operand.reg "%cmp15.us100")
                            (Operand.reg "%sub17.us102")
                            (lit 64 (-1)),
                          Instr.binop
                            "%ent.0.us104"
                            (BinOp.and)
                            64
                            (Operand.reg "%or12.us97")
                            (Operand.reg "%and18.us103"),
                          Instr.store
                            (Ty.int 64)
                            (Operand.reg "%ent.0.us104")
                            (Operand.reg "%entw"),
                          Instr.call
                            "%call.us"
                            (Ty.int 64)
                            "leanllvm_json_entry_b8"
                            [(Ty.ptr, Operand.reg "%entw"),
                             (Ty.int 64, Operand.reg "%i.080.us86"),
                             (Ty.int 64, lit 64 1),
                             (Ty.ptr, Operand.reg "%ep"),
                             (Ty.int 64, Operand.reg "%k.081.us85")],
                          Instr.binop
                            "%inc.us106"
                            (BinOp.add)
                            64
                            (Operand.reg "%i.080.us86")
                            (lit 64 1),
                          Instr.icmp
                            "%exitcond114.not"
                            (IPred.eq)
                            64
                            (Operand.reg "%inc.us106")
                            (Operand.reg "%shr")],
               term := Term.condbr
                         (Operand.reg "%exitcond114.not")
                         "for.cond.cleanup"
                         "for.body.us83" },
             { name := "for.cond.cleanup",
               instrs := [Instr.phi
                            "%k.0.lcssa"
                            (Ty.int 64)
                            [("entry", Operand.reg "%0"),
                             ("for.body.us.us", Operand.reg "%call21.us.us"),
                             ("for.body.us", Operand.reg "%call21.us"),
                             ("for.body.us83", Operand.reg "%call.us"),
                             ("for.body", Operand.reg "%call")],
                          Instr.store
                            (Ty.int 64)
                            (Operand.reg "%k.0.lcssa")
                            (Operand.reg "%nk"),
                          Instr.trunc "%25" 64 32 (Operand.reg "%arm"),
                          Instr.binop
                            "%26"
                            (BinOp.lshr)
                            32
                            (Operand.reg "%25")
                            (lit 32 2),
                          Instr.binop
                            "%conv"
                            (BinOp.and)
                            32
                            (Operand.reg "%26")
                            (lit 32 1),
                          Instr.call
                            "%call30"
                            (Ty.int 64)
                            "leanllvm_json_utf8"
                            [(Ty.ptr, Operand.reg "%b"),
                             (Ty.int 64, Operand.reg "%n"),
                             (Ty.int 32, Operand.reg "%conv")],
                          Instr.icmp
                            "%cmp31.not"
                            (IPred.eq)
                            64
                            (Operand.reg "%call30")
                            (lit 64 0)],
               term := Term.condbr (Operand.reg "%cmp31.not") "if.end34" "if.then33" },
             { name := "for.body",
               instrs := [Instr.phi
                            "%prevS.082"
                            (Ty.int 64)
                            [("for.body", Operand.reg "%shr13"),
                             ("for.body.lr.ph.split",
                              lit 64 0)],
                          Instr.phi
                            "%k.081"
                            (Ty.int 64)
                            [("for.body", Operand.reg "%call"),
                             ("for.body.lr.ph.split", Operand.reg "%0")],
                          Instr.phi
                            "%i.080"
                            (Ty.int 64)
                            [("for.body", Operand.reg "%inc"),
                             ("for.body.lr.ph.split",
                              lit 64 0)],
                          Instr.binop
                            "%shl"
                            (BinOp.shl)
                            64
                            (Operand.reg "%i.080")
                            (lit 64 6),
                          Instr.gep
                            "%add.ptr"
                            (Ty.int 8)
                            (Operand.reg "%b")
                            (Operand.reg "%shl"),
                          Instr.callVoid
                            "leanllvm_json_s1_masks"
                            [(Ty.ptr, Operand.reg "%add.ptr"),
                             (Ty.ptr, Operand.reg "%sc"),
                             (Ty.ptr, Operand.reg "%mk")],
                          Instr.load "%27" (Ty.int 64) (Operand.reg "%mk"),
                          Instr.load "%28" (Ty.int 64) (Operand.reg "%delim"),
                          Instr.load "%29" (Ty.int 64) (Operand.reg "%in_string"),
                          Instr.load "%30" (Ty.int 64) (Operand.reg "%ws"),
                          Instr.binop
                            "%31"
                            (BinOp.or)
                            64
                            (Operand.reg "%27")
                            (Operand.reg "%30"),
                          Instr.binop
                            "%32"
                            (BinOp.or)
                            64
                            (Operand.reg "%31")
                            (Operand.reg "%28"),
                          Instr.binop
                            "%or2"
                            (BinOp.or)
                            64
                            (Operand.reg "%32")
                            (Operand.reg "%29"),
                          Instr.binop
                            "%not"
                            (BinOp.xor)
                            64
                            (Operand.reg "%or2")
                            (lit 64 (-1)),
                          Instr.binop
                            "%not6"
                            (BinOp.xor)
                            64
                            (Operand.reg "%29")
                            (lit 64 (-1)),
                          Instr.binop
                            "%and"
                            (BinOp.and)
                            64
                            (Operand.reg "%28")
                            (Operand.reg "%not6"),
                          Instr.binop
                            "%shl8"
                            (BinOp.shl)
                            64
                            (Operand.reg "%not")
                            (lit 64 1),
                          Instr.binop
                            "%or9"
                            (BinOp.or)
                            64
                            (Operand.reg "%shl8")
                            (Operand.reg "%prevS.082"),
                          Instr.binop
                            "%not10"
                            (BinOp.xor)
                            64
                            (Operand.reg "%or9")
                            (lit 64 (-1)),
                          Instr.binop
                            "%and11"
                            (BinOp.and)
                            64
                            (Operand.reg "%not10")
                            (Operand.reg "%not"),
                          Instr.binop
                            "%33"
                            (BinOp.or)
                            64
                            (Operand.reg "%and")
                            (Operand.reg "%and11"),
                          Instr.binop
                            "%or12"
                            (BinOp.or)
                            64
                            (Operand.reg "%33")
                            (Operand.reg "%27"),
                          Instr.binop
                            "%shr13"
                            (BinOp.lshr)
                            64
                            (Operand.reg "%not")
                            (lit 64 63),
                          Instr.binop
                            "%sub"
                            (BinOp.sub)
                            64
                            (Operand.reg "%n")
                            (Operand.reg "%shl"),
                          Instr.icmp
                            "%cmp15"
                            (IPred.ult)
                            64
                            (Operand.reg "%sub")
                            (lit 64 64),
                          Instr.binop
                            "%notmask"
                            (BinOp.shl)
                            64
                            (lit 64 (-1))
                            (Operand.reg "%sub"),
                          Instr.binop
                            "%sub17"
                            (BinOp.xor)
                            64
                            (Operand.reg "%notmask")
                            (lit 64 (-1)),
                          Instr.select
                            "%and18"
                            (Ty.int 64)
                            (Operand.reg "%cmp15")
                            (Operand.reg "%sub17")
                            (lit 64 (-1)),
                          Instr.binop
                            "%ent.0"
                            (BinOp.and)
                            64
                            (Operand.reg "%or12")
                            (Operand.reg "%and18"),
                          Instr.store
                            (Ty.int 64)
                            (Operand.reg "%ent.0")
                            (Operand.reg "%entw"),
                          Instr.call
                            "%call"
                            (Ty.int 64)
                            "leanllvm_json_entry_b8"
                            [(Ty.ptr, Operand.reg "%entw"),
                             (Ty.int 64, Operand.reg "%i.080"),
                             (Ty.int 64, lit 64 1),
                             (Ty.ptr, Operand.reg "%ep"),
                             (Ty.int 64, Operand.reg "%k.081")],
                          Instr.load "%34" (Ty.int 64) (Operand.reg "%backslash"),
                          Instr.load "%35" (Ty.int 64) (Operand.reg "%ctl"),
                          Instr.load "%36" (Ty.int 64) (Operand.reg "%in_string"),
                          Instr.callVoid
                            "leanllvm_json_escape_list"
                            [(Ty.int 64, Operand.reg "%34"),
                             (Ty.int 64, Operand.reg "%35"),
                             (Ty.int 64, Operand.reg "%36"),
                             (Ty.int 64, Operand.reg "%i.080"),
                             (Ty.ptr, Operand.reg "%xp"),
                             (Ty.ptr, Operand.reg "%nxp"),
                             (Ty.ptr, Operand.reg "%xcarry")],
                          Instr.binop
                            "%inc"
                            (BinOp.add)
                            64
                            (Operand.reg "%i.080")
                            (lit 64 1),
                          Instr.icmp
                            "%exitcond.not"
                            (IPred.eq)
                            64
                            (Operand.reg "%inc")
                            (Operand.reg "%shr")],
               term := Term.condbr (Operand.reg "%exitcond.not") "for.cond.cleanup" "for.body" },
             { name := "if.then33",
               instrs := [Instr.store
                            (Ty.int 64)
                            (Operand.reg "%n")
                            (Operand.reg "%err")],
               term := Term.br "cleanup" },
             { name := "if.end34",
               instrs := [Instr.load "%37" (Ty.int 64) (Operand.reg "%nxp"),
                          Instr.call
                            "%call35"
                            (Ty.int 64)
                            "leanllvm_json_stage2"
                            [(Ty.ptr, Operand.reg "%b"),
                             (Ty.int 64, Operand.reg "%n"),
                             (Ty.ptr, Operand.reg "%ep"),
                             (Ty.int 64, Operand.reg "%k.0.lcssa"),
                             (Ty.ptr, Operand.reg "%xp"),
                             (Ty.int 64, Operand.reg "%37"),
                             (Ty.ptr, Operand.reg "%dst"),
                             (Ty.int 64, Operand.reg "%dstcap"),
                             (Ty.ptr, Operand.reg "%ndst"),
                             (Ty.ptr, Operand.reg "%ev"),
                             (Ty.int 64, Operand.reg "%evcap"),
                             (Ty.ptr, Operand.reg "%nev"),
                             (Ty.ptr, Operand.reg "%err")]],
               term := Term.br "cleanup" },
             { name := "cleanup",
               instrs := [Instr.phi
                            "%retval.0"
                            (Ty.int 64)
                            [("if.then33", lit 64 0),
                             ("if.end34", Operand.reg "%call35")]],
               term := Term.ret (Ty.int 64) (some (Operand.reg "%retval.0")) }] }
/-! ### The pin -/

/-- The parsed fixture's whole function list, for the pin below. -/
def parsedFunctions (src : String) : Option (List Function) :=
  match parseModule src with
  | .ok m => some m.functions
  | .error _ => none

/-- The parsed fixture's declaration count. -/
def parsedDeclCount (src : String) : Option Nat :=
  match parseModule src with
  | .ok m => some m.decls.length
  | .error _ => none

-- The literal above is the parsed fixture, and the fixture is the parsed literal.
#guard decide (firstFunction pipelineSrc = some pipelineBody)
#guard decide (parsedFunctions pipelineSrc = some [pipelineBody])
#guard decide (parsedDeclCount pipelineSrc = some 6)

/-! ### The census -/

/-- The call targets the pinned body names, in text order: a `call` that binds a
result and a `call void` are both calls, because the census is the callee and
not the shape the instruction has. -/
def callTargets (f : Function) : List String :=
  (f.blocks.flatMap (·.instrs)).filterMap fun i =>
    match i with
    | .call _ _ callee _ => some callee
    | .callVoid callee _ => some callee
    | _ => none

/-- Each call site's callee and argument types, in text order. -/
def callArgs (f : Function) : List (String × List Ty) :=
  (f.blocks.flatMap (·.instrs)).filterMap fun i =>
    match i with
    | .call _ _ callee args => some (callee, args.map (·.1))
    | .callVoid callee args => some (callee, args.map (·.1))
    | _ => none

/-- Every allocation instruction's destination type, in text order.  The
pipeline's own text has none: its scratch is the caller's, which is the fact the
run's allocator base rests on. -/
def allocaTypes (f : Function) : List Ty :=
  (f.blocks.flatMap (·.instrs)).filterMap fun i =>
    match i with
    | .alloca _ ty _ => some ty
    | _ => none

/-- The ABI each unit's header declares for the pipeline's call: the callee's
return type and its argument types, in order.  This is `pipeline.h`'s and the
four unit headers' text, and `abiAgrees` checks the pinned body against it. -/
def pipelineAbi : String → Option (Ty × List Ty)
  | "leanllvm_json_s1_masks" =>
      some (.void, [.ptr, .ptr, .ptr])
  | "leanllvm_json_entry_pos8" =>
      some (.int 64, [.ptr, .int 64, .int 64, .ptr, .int 64])
  | "leanllvm_json_entry_b8" =>
      some (.int 64, [.ptr, .int 64, .int 64, .ptr, .int 64])
  | "leanllvm_json_escape_list" =>
      some (.void, [.int 64, .int 64, .int 64, .int 64, .ptr, .ptr, .ptr])
  | "leanllvm_json_utf8" =>
      some (.int 64, [.ptr, .int 64, .int 32])
  | "leanllvm_json_stage2" =>
      some (.int 64, [.ptr, .int 64, .ptr, .int 64, .ptr, .int 64, .ptr, .int 64,
                      .ptr, .ptr, .int 64, .ptr, .ptr])
  | _ => none

/-- Every call site's shape is the ABI its callee's header declares.  A site
whose callee is not one of the six fails, so the census is closed: there is no
seventh callee and no `llvm.*` intrinsic in the body. -/
def abiAgrees (f : Function) : Bool :=
  (f.blocks.flatMap (·.instrs)).all fun i =>
    match i with
    | .call _ rt callee args =>
        match pipelineAbi callee with
        | some (rt', ts) => (rt == rt') && (args.map (·.1) == ts)
        | none => false
    | .callVoid callee args =>
        match pipelineAbi callee with
        | some (rt', ts) => (rt' == .void) && (args.map (·.1) == ts)
        | none => false
    | _ => true

/-- The six symbols the pinned body calls, sorted and de-duplicated. -/
def censusSymbols : List String :=
  ["leanllvm_json_entry_b8", "leanllvm_json_entry_pos8",
   "leanllvm_json_escape_list", "leanllvm_json_s1_masks",
   "leanllvm_json_stage2", "leanllvm_json_utf8"]

-- The census, enumerated from the pinned AST: the symbol set is exactly the six
-- units, and the emitted multiset is the four mask sites, two of each entry
-- emitter, two escape-list sites, and one each of UTF-8 and stage 2.
#guard
  decide (((callTargets pipelineBody).mergeSort (fun a b => a ≤ b)).eraseDups =
    censusSymbols)
#guard
  decide ((callTargets pipelineBody).mergeSort (fun a b => a ≤ b) =
    ["leanllvm_json_entry_b8", "leanllvm_json_entry_b8",
     "leanllvm_json_entry_pos8", "leanllvm_json_entry_pos8",
     "leanllvm_json_escape_list", "leanllvm_json_escape_list",
     "leanllvm_json_s1_masks", "leanllvm_json_s1_masks",
     "leanllvm_json_s1_masks", "leanllvm_json_s1_masks",
     "leanllvm_json_stage2", "leanllvm_json_utf8"])

-- Every site's return type and argument type list is its unit header's ABI.
#guard abiAgrees pipelineBody

-- The pinned body allocates nothing, and every `ret` carries an `i64`: the two
-- facts the run's allocator base and the completion's shape rest on.  The
-- second is the guard a value-returning call site's bridge needs, recorded here
-- because the pipeline is itself the caller of every one of them.
#guard decide (allocaTypes pipelineBody = [])
#guard retsValued pipelineBody

/-! ### The call environment -/

/-- The mask unit's symbol. -/
def masksSym : String := "leanllvm_json_s1_masks"

/-- The POS8 entry emitter's symbol. -/
def entryPos8Sym : String := "leanllvm_json_entry_pos8"

/-- The B8 entry emitter's symbol. -/
def entryB8Sym : String := "leanllvm_json_entry_b8"

/-- The escape-position list's symbol. -/
def escapeListSym : String := "leanllvm_json_escape_list"

/-- The UTF-8 stage's symbol. -/
def utf8Sym : String := "leanllvm_json_utf8"

/-- The stage-2 walk's symbol. -/
def stage2Sym : String := "leanllvm_json_stage2"

/-- The POS8 record at a caller that passes five values.

The capture rewrote the emitter's static table into a parameter, so the record's
`pre`, `post` and `budget` speak **six** arguments while `entry.h` speaks five.
Read at the five-argument list with the staged table base appended, this is the
same record: no clause is added, dropped or weakened, and the record's own
theorem is what proves it. -/
def Γ_entry_pos8at (tab : Nat) : MemContract where
  budget := fun args mem => Γ_entry_pos8.budget (args ++ [.ptr tab]) mem
  pre    := fun args mem next => Γ_entry_pos8.pre (args ++ [.ptr tab]) mem next
  post   := fun args mem next o => Γ_entry_pos8.post (args ++ [.ptr tab]) mem next o

/-- The POS8 selection at a five-argument call site: the base is appended before
the body runs, at the record's budget for the six arguments it actually receives.

This is a re-indexing, not a second body: the selection is `envForUnit` at the
appended arguments, so a call site that passes five values reaches the pinned
six-argument body with the table the caller staged.  The C body reads a static
table where the model reads `%tab`; the caller's memory image of that table is
the representation the unit's own record already encodes, and the harness that
stages it is the one whose identity arm compares the table by digest. -/
def envForPos8 (tab : Nat) (calls : Calls) : Calls := fun callee args mem next =>
  envForUnit entryPos8Sym Γ_entry_pos8 calls entryPos8Function callee
    (args ++ [.ptr tab]) mem next

/-- The POS8 bundle member at the pipeline's five-argument call site.

This is `satisfies_calls` applied at the appended arguments — a lifting, not a
second bridge: the record's pre, post and budget are read at `args ++ [.ptr tab]`
on both sides, so the two cannot drift. -/
theorem satisfies_calls_pos8 (tab : Nat) {calls : Calls}
    (hsub : Satisfies calls entryPos8Function Γ_entry_pos8)
    (hv : retsValued entryPos8Function = true) :
    CallSatisfies (envForPos8 tab calls) (Γ_entry_pos8at tab) entryPos8Sym := by
  intro args mem next hpre
  exact satisfies_calls (calls := calls) (body := entryPos8Function)
    (Γ := Γ_entry_pos8) (sym := entryPos8Sym) hsub hv
    (args ++ [.ptr tab]) mem next (by simpa only [Γ_entry_pos8at] using hpre)

/-- The pipeline's call environment: each of the six units this tree holds,
resolved by `envForUnit` at its own body, its own intrinsic environment, its own
record's `(args, mem)`-indexed budget and a reservation of `0`.

The escape list's record is `Γ_escape_positions base escapePositionsBudget` — its
block clause reads the document at `base + blockAddr blk0`, so the record is
indexed by the document's base, and its budget is the run's own fuel term, named
by the list's theorem — and its intrinsic environment resolves the batch at
`Γ_xl_batch`.

`base` is a parameter rather than a reading of the arguments because `Satisfies`
fixes the call environment before it quantifies over arguments: the record a call
site is judged by must be chosen outside the argument list.  The pipeline's own
staging then ties `base` to the ABI's first slot, which is where `pipeline.h`
puts the document (`b .. b + n - 1`).

`stage2Sel` is the stage-2 slot: that unit's body is not in this tree, so a
caller supplies its selection, and `pipelineCalls` is parametric in it.  Its
record is `JsonStage2Contract`'s `Γ_stage2`, and `pipeline_satisfies_at_stage2`
builds the pipeline's bundle at it from that selection; the theorem states the
stage-2 fact as one hypothesis.

`tab` is the staged table base the POS8 record reads, appended by the adapter
because the capture made the emitter's static table a parameter (see
`Γ_entry_pos8at`).  The other five selections take the caller's arguments
unchanged: `Γ_entry_b8` reads no table, and the mask, UTF-8 and escape-list
records' argument clauses are the ABIs their headers declare.

Every branch is `envForUnit`'s own answer for its symbol, so a callee outside
these seven is `none` — the census above is what makes that unreachable in the
pinned body. -/
def pipelineCalls (tab base : Nat) (stage2Sel : Calls) : Calls :=
  fun callee args mem next =>
  if callee = masksSym then
    envForUnit masksSym Γ_masks s1Calls s1MasksFunction callee args mem next
  else if callee = entryPos8Sym then
    envForPos8 tab entryCalls callee args mem next
  else if callee = entryB8Sym then
    envForUnit entryB8Sym Γ_entry_b8 entryCalls entryB8Function callee args mem next
  else if callee = escapeListSym then
    envForUnit escapeListSym (Γ_escape_positions base escapePositionsBudget)
      (escapeListCalls Γ_xl_batch) escapeListFunction callee args mem next
  else if callee = utf8Sym then
    envForUnit utf8Sym Γ_utf8 utf8Calls utf8Function callee args mem next
  else if callee = stage2Sym then
    stage2Sel callee args mem next
  else
    none

/-- The mask branch is the selection `envForUnit` builds for the mask unit: the
environment names the units the body calls, and the first of them resolves at
its own record rather than falling through. -/
theorem pipelineCalls_masks (tab base : Nat) (stage2Sel : Calls) :
    pipelineCalls tab base stage2Sel masksSym =
      envForUnit masksSym Γ_masks s1Calls s1MasksFunction masksSym := by
  funext args mem next
  simp only [pipelineCalls, masksSym, entryPos8Sym, entryB8Sym, escapeListSym,
    utf8Sym, stage2Sym, ite_true]

end LeanLLVM.Refinement.JsonPipelineIR
