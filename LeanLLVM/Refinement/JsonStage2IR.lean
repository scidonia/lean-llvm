/-
The stage-2 walk's emitted body, pinned, and the call environment and call-site
mapping the record needs.

`probes/install/ir/stage2.candidate.ll` is the body this module proves things
about.  `capture-stage2.sh` records how it is derived; the summary is:

* `kernel/json/stage2.c` at the measured compiler line
  (`-O3 -march=x86-64-v3 -mpclmul -std=gnu11 -falign-loops=64
  -falign-functions=64 -fno-discard-value-names`), with `__attribute__((noinline))`
  on every helper except `s2_walk`, so the walk inlines into the ABI wrapper with
  the mode `S2_VAL | S2_STR | S2_EV` constant and its helpers leave the body as
  calls;
* `opt -passes=lower-switch`, since the fragment has no `switch`;
* the wrapper's `define` block, with the argument surface stripped (recorded in
  `stage2.strip.tsv`) and four rewrites (recorded in `stage2.rewrites.tsv`):
  array reads become byte reads, the three refusal-message operands become
  `null`, `llvm.umin.i64` unfolds to `icmp`+`select`, and the eight local objects
  the fragment cannot allocate become appended `ptr` parameters
  (`stage2.staging.tsv`).

## What the pinned body is, and what it is not

It is the walk's text with its intra-unit helper boundaries preserved and the
mode constant.  It is **not** the measured object's text: the object inlines the
helpers, and the difference is the call composition.  The measurement that makes
that a measurement rather than a preference is in `stage2.inventory`: the fused
emission of the same source is 1754 lines in 233 blocks and carries binary64
(`alloca double`, `uitofp`, `fmul`, `fdiv`, `fneg`, `select double`,
`phi double`), because `od_scalar_value` and `num_fast_el1` are
`__attribute__((always_inline))`; the same source with the twelve helpers
`noinline` is 944 lines in 165 blocks with no binary64 and no vector operation.
`Ty` and `Semantics` have no floating point, so the inlined text has no
representation here at all.  Out of line, the number path is a call, and its
contract is the one this tree already proves: `numFastEmitted_strtodSpec` in
`JsonStage2Body`, the composition of the three tier theorems, states the
conversion's observable.

The distance from the pinned body to the shipped object is therefore two named
things and nothing else: the **FP call composition** (this body calls the helpers
whose contracts are the tier theorems) and the **re-indexing adapter**
`Γ_stage2at`/`envForStage2` below, which maps `stage2.h`'s thirteen-argument ABI
to the fixture's twenty-one-argument form.  Neither is implied: the first is a
callee's record, the second is a definition with its own lemmas.

## The pin

`stage2Body` is the parsed fixture written out, and the `#guard`s below assert
that the parser returns exactly it, that the module's declaration count is the
fixture's, that the ABI prefix and the staging suffix are the ones the derivation
claims, that the census is closed, and that `retsValued` holds.  The pin is a
`#guard` rather than a `rfl` proposition because the parser runs on `String`
primitives, which the kernel does not reduce, so a proposition about a
`parseModule` result cannot be closed by reflexivity.

`stage2SrcMutated` is the mutation that shows the pin bites: the same text with
one instruction's immediate changed.  It parses, and it is not `stage2Body`, so
the equality above is about the text and not about a search that would accept
anything.  Without that control a pin that compared two terms the parser never
produces would read the same as a pin that compared the fixture.

## What the body keeps

The walk's own guards are body text and are pinned with it: the two reserve
checks (the arena's slack add and the event stream's thirteen-byte add), their
four `__builtin_trap` arms (`@llvm.trap`), the thirteen-byte record's stores, and
the number dispatch's counters.  The number conversion's two caps
(`idig < 19`, `exp10 < 100000`) are in `od_scalar_value`, which is a callee in
this body; they are stated at that callee's contract, and the call census below
is what says so.

## What is discharged here, and what is not

Discharged: the pin; the ABI prefix and the staging suffix; the census; the
structural facts `Satisfies` consumes (`retsValued`, no aggregate alloca, one
`ret`, 165 blocks); the call environment `stage2Calls`, which resolves the
lifetime markers and the walk's two `memset`s and leaves the unit's own sub-units
to the parameter `sub`; and `satisfies_calls_stage2`, which turns a `Satisfies`
obligation on the pinned body at the adapter's record into the `CallSatisfies`
the pipeline's stage-2 slot needs.

Not discharged, and named with the obligation:

* **`Satisfies (stage2Calls sub) stage2Body (Γ_stage2at st)`**, the walk's own
  obligation.  Its first conjunct is the **completion budget**: a step count at
  which a 165-block loop returns.  Every later clause is downstream of it,
  because `Satisfies` states the post only of an outcome the run reaches, so the
  loop induction is the first obligation that resists and the six `Stage2Run`
  clauses (both cursors and their growth bounds, the arena's reserve slack,
  `Owns` over the two extents, the refusal bit, and `eoff ≤ n`) are what it owes
  once it is reached.  The budget is stated on its own at this ABI in
  `JsonStage2Body` — `Stage2WalkCompletes`, with
  `stage2WalkObligation_iff_completion` proving it is exactly this conjunct —
  and the clauses are reduced there to the loop's trace.
* **the two walk facts `JsonStage2Body` names**: at most one event record per
  entry (`Stage2OneRecordPerEntry`, the count `emitBlobs_len_le` needs stated at
  the entry stream) and the escaped bodies' lengths summing inside the document
  (`Stage2SpansInside`, the extents whose sum `Stage2Run.arenaLe_of_spans` reads
  the arena's bound off).  Both are properties of the loop's per-entry dispatch,
  so they are part of the same induction; what each buys once the loop supplies
  it — and what the six clauses above reduce to — is proved in `JsonStage2Body`.
* **the FP call composition's own side**: the body calls `num_fast_el1` and
  `od_scalar_value`; what those compute is the tier theorems' subject, and this
  module neither adds to nor weakens them.
-/
import LeanLLVM.Memory
import LeanLLVM.Parser
import LeanLLVM.Refinement.Relation
import LeanLLVM.Refinement.JsonStage2Contract

set_option autoImplicit false

namespace LeanLLVM.Refinement.JsonStage2IR

open LeanLLVM
open LeanLLVM.Refinement

/-! ### The fixture, parsed -/

/-- The stage-2 walk as emitted and committed. -/
def stage2Src : String :=
  include_str "../../probes/install/ir/stage2.candidate.ll"

/-- Parse a fixture and take its single function. -/
def firstFunction (src : String) : Option Function :=
  match parseModule src with
  | .ok m => m.functions.head?
  | .error _ => none

/-- The parsed fixture's functions. -/
def parsedFunctions (src : String) : Option (List Function) :=
  match parseModule src with
  | .ok m => some m.functions
  | .error _ => none

/-- The parsed fixture's declaration count. -/
def parsedDeclCount (src : String) : Option Nat :=
  match parseModule src with
  | .ok m => some m.decls.length
  | .error _ => none

def stage2Body : Function :=
{ name := "leanllvm_json_stage2",
  retTy := (Ty.int 64),
  params := [    ("%b", Ty.ptr),
    ("%n", (Ty.int 64)),
    ("%ep", Ty.ptr),
    ("%nep", (Ty.int 64)),
    ("%xp", Ty.ptr),
    ("%nxp", (Ty.int 64)),
    ("%dst", Ty.ptr),
    ("%dstcap", (Ty.int 64)),
    ("%ndst", Ty.ptr),
    ("%ev", Ty.ptr),
    ("%evcap", (Ty.int 64)),
    ("%nev", Ty.ptr),
    ("%err", Ty.ptr),
    ("%d.i", Ty.ptr),
    ("%c.i", Ty.ptr),
    ("%ctype.i", Ty.ptr),
    ("%cst.i", Ty.ptr),
    ("%t352.i", Ty.ptr),
    ("%s", Ty.ptr),
    ("%z", Ty.ptr),
    ("%e", Ty.ptr)],
  blocks := [
{ name := "entry",
    instrs := [
      Instr.alloca "%ei.i" (Ty.int 64) 0,
      Instr.alloca "%root_done.i" (Ty.int 32) 0,
      Instr.alloca "%xj.i" (Ty.int 64) 0,
      Instr.alloca "%outn.i" (Ty.int 64) 0,
      Instr.callVoid "llvm.lifetime.start.p0" [((Ty.int 64), (Operand.imm (.int 64 (BitVec.ofNat 64 120)))), (Ty.ptr, (Operand.reg "%s"))],
      Instr.callVoid "llvm.lifetime.start.p0" [((Ty.int 64), (Operand.imm (.int 64 (BitVec.ofNat 64 64)))), (Ty.ptr, (Operand.reg "%z"))],
      Instr.callVoid "llvm.lifetime.start.p0" [((Ty.int 64), (Operand.imm (.int 64 (BitVec.ofNat 64 24)))), (Ty.ptr, (Operand.reg "%e"))],
      Instr.binop "%add" BinOp.add 64 (Operand.reg "%n") (Operand.imm (.int 64 (BitVec.ofNat 64 63))),
      Instr.binop "%shr" BinOp.lshr 64 (Operand.reg "%add") (Operand.imm (.int 64 (BitVec.ofNat 64 6))),
      Instr.callVoid "s2_init" [(Ty.ptr, (Operand.reg "%s")), (Ty.ptr, (Operand.reg "%b")), ((Ty.int 64), (Operand.reg "%n")), ((Ty.int 64), (Operand.reg "%shr")), (Ty.ptr, (Operand.reg "%ep"))],
      Instr.gep "%nsp" (Ty.int 8) (Operand.reg "%s") (Operand.imm (.int 64 (BitVec.ofNat 64 56))),
      Instr.store (Ty.int 64) (Operand.reg "%nep") (Operand.reg "%nsp"),
      Instr.gep "%xp1" (Ty.int 8) (Operand.reg "%s") (Operand.imm (.int 64 (BitVec.ofNat 64 72))),
      Instr.store Ty.ptr (Operand.reg "%xp") (Operand.reg "%xp1"),
      Instr.gep "%nxp2" (Ty.int 8) (Operand.reg "%s") (Operand.imm (.int 64 (BitVec.ofNat 64 80))),
      Instr.store (Ty.int 64) (Operand.reg "%nxp") (Operand.reg "%nxp2"),
      Instr.gep "%hash1.i.i" (Ty.int 8) (Operand.reg "%z") (Operand.imm (.int 64 (BitVec.ofNat 64 32))),
      Instr.gep "%ar" (Ty.int 8) (Operand.reg "%z") (Operand.imm (.int 64 (BitVec.ofNat 64 40))),
      Instr.gep "%0" (Ty.int 8) (Operand.reg "%z") (Operand.imm (.int 64 (BitVec.ofNat 64 24))),
      Instr.callVoid "llvm.memset.p0.i64" [(Ty.ptr, (Operand.reg "%0")), ((Ty.int 8), (Operand.imm (.int 8 (BitVec.ofNat 8 0)))), ((Ty.int 64), (Operand.imm (.int 64 (BitVec.ofNat 64 16)))), ((Ty.int 1), (Operand.imm (.int 1 (BitVec.ofNat 1 0))))],
      Instr.store Ty.ptr (Operand.reg "%dst") (Operand.reg "%ar"),
      Instr.load "%1" (Ty.int 64) (Operand.reg "%ndst"),
      Instr.gep "%alen" (Ty.int 8) (Operand.reg "%z") (Operand.imm (.int 64 (BitVec.ofNat 64 48))),
      Instr.store (Ty.int 64) (Operand.reg "%1") (Operand.reg "%alen"),
      Instr.gep "%acap" (Ty.int 8) (Operand.reg "%z") (Operand.imm (.int 64 (BitVec.ofNat 64 56))),
      Instr.store (Ty.int 64) (Operand.reg "%dstcap") (Operand.reg "%acap"),
      Instr.store Ty.ptr (Operand.reg "%ev") (Operand.reg "%z"),
      Instr.load "%2" (Ty.int 64) (Operand.reg "%nev"),
      Instr.gep "%len" (Ty.int 8) (Operand.reg "%z") (Operand.imm (.int 64 (BitVec.ofNat 64 8))),
      Instr.store (Ty.int 64) (Operand.reg "%2") (Operand.reg "%len"),
      Instr.gep "%cap" (Ty.int 8) (Operand.reg "%z") (Operand.imm (.int 64 (BitVec.ofNat 64 16))),
      Instr.store (Ty.int 64) (Operand.reg "%evcap") (Operand.reg "%cap"),
      Instr.load "%3" Ty.ptr (Operand.reg "%s"),
      Instr.gep "%n2.i" (Ty.int 8) (Operand.reg "%s") (Operand.imm (.int 64 (BitVec.ofNat 64 8))),
      Instr.load "%4" (Ty.int 64) (Operand.reg "%n2.i"),
      Instr.gep "%ep3.i" (Ty.int 8) (Operand.reg "%s") (Operand.imm (.int 64 (BitVec.ofNat 64 48))),
      Instr.load "%5" Ty.ptr (Operand.reg "%ep3.i"),
      Instr.callVoid "llvm.lifetime.start.p0" [((Ty.int 64), (Operand.imm (.int 64 (BitVec.ofNat 64 1192)))), (Ty.ptr, (Operand.reg "%c.i"))],
      Instr.gep "%6" (Ty.int 8) (Operand.reg "%c.i") (Operand.imm (.int 64 (BitVec.ofNat 64 40))),
      Instr.callVoid "llvm.memset.p0.i64" [(Ty.ptr, (Operand.reg "%6")), ((Ty.int 8), (Operand.imm (.int 8 (BitVec.ofNat 8 0)))), ((Ty.int 64), (Operand.imm (.int 64 (BitVec.ofNat 64 1152)))), ((Ty.int 1), (Operand.imm (.int 1 (BitVec.ofNat 1 0))))],
      Instr.store Ty.ptr (Operand.reg "%3") (Operand.reg "%c.i"),
      Instr.gep "%n6.i" (Ty.int 8) (Operand.reg "%c.i") (Operand.imm (.int 64 (BitVec.ofNat 64 8))),
      Instr.store (Ty.int 64) (Operand.reg "%4") (Operand.reg "%n6.i"),
      Instr.gep "%ix.i" (Ty.int 8) (Operand.reg "%c.i") (Operand.imm (.int 64 (BitVec.ofNat 64 16))),
      Instr.store Ty.ptr (Operand.reg "%5") (Operand.reg "%ix.i"),
      Instr.gep "%nix.i" (Ty.int 8) (Operand.reg "%c.i") (Operand.imm (.int 64 (BitVec.ofNat 64 24))),
      Instr.store (Ty.int 64) (Operand.reg "%nep") (Operand.reg "%nix.i"),
      Instr.gep "%e7.i" (Ty.int 8) (Operand.reg "%c.i") (Operand.imm (.int 64 (BitVec.ofNat 64 1112))),
      Instr.store Ty.ptr (Operand.reg "%e") (Operand.reg "%e7.i"),
      Instr.callVoid "llvm.lifetime.start.p0" [((Ty.int 64), (Operand.imm (.int 64 (BitVec.ofNat 64 520)))), (Ty.ptr, (Operand.reg "%ctype.i"))],
      Instr.callVoid "llvm.lifetime.start.p0" [((Ty.int 64), (Operand.imm (.int 64 (BitVec.ofNat 64 520)))), (Ty.ptr, (Operand.reg "%cst.i"))],
      Instr.callVoid "llvm.lifetime.start.p0" [((Ty.int 64), (Operand.imm (.int 64 (BitVec.ofNat 64 4)))), (Ty.ptr, (Operand.reg "%root_done.i"))],
      Instr.store (Ty.int 32) (Operand.imm (.int 32 (BitVec.ofNat 32 0))) (Operand.reg "%root_done.i"),
      Instr.callVoid "llvm.lifetime.start.p0" [((Ty.int 64), (Operand.imm (.int 64 (BitVec.ofNat 64 8)))), (Ty.ptr, (Operand.reg "%xj.i"))],
      Instr.store (Ty.int 64) (Operand.imm (.int 64 (BitVec.ofNat 64 0))) (Operand.reg "%xj.i"),
      Instr.gep "%invariant.gep" (Ty.int 8) (Operand.reg "%3") (Operand.imm (.int 64 (BitVec.ofNat 64 18446744073709551615))),
      Instr.icmp "%cmp.i247.not" IPred.eq 64 (Operand.reg "%nep") (Operand.imm (.int 64 (BitVec.ofNat 64 0)))
    ],
    term := Term.condbr (Operand.reg "%cmp.i247.not") "if.then492.i" "while.body.i.lr.ph" },
{ name := "while.body.i.lr.ph",
    instrs := [
      Instr.gep "%k11.i" (Ty.int 8) (Operand.reg "%c.i") (Operand.imm (.int 64 (BitVec.ofNat 64 32))),
      Instr.gep "%h1.i.i.i51" (Ty.int 8) (Operand.reg "%z") (Operand.imm (.int 64 (BitVec.ofNat 64 24))),
      Instr.gep "%gap.i" (Ty.int 8) (Operand.reg "%t352.i") (Operand.imm (.int 64 (BitVec.ofNat 64 20))),
      Instr.gep "%end.i" (Ty.int 8) (Operand.reg "%t352.i") (Operand.imm (.int 64 (BitVec.ofNat 64 8))),
      Instr.gep "%kind404.i" (Ty.int 8) (Operand.reg "%t352.i") (Operand.imm (.int 64 (BitVec.ofNat 64 16)))
    ],
    term := Term.br "while.body.i" },
{ name := "while.body.i",
    instrs := [
      Instr.phi "%k.0.i249" (Ty.int 64) [("while.body.i.lr.ph", (Operand.imm (.int 64 (BitVec.ofNat 64 0)))), ("cleanup478.i", (Operand.reg "%k.2.i"))],
      Instr.phi "%sp.i.0248" (Ty.int 32) [("while.body.i.lr.ph", (Operand.imm (.int 32 (BitVec.ofNat 32 0)))), ("cleanup478.i", (Operand.reg "%sp.i.1"))],
      Instr.binop "%inc.i" BinOp.add 64 (Operand.reg "%k.0.i249") (Operand.imm (.int 64 (BitVec.ofNat 64 1))),
      Instr.gep "%arrayidx.i" (Ty.int 32) (Operand.reg "%5") (Operand.reg "%k.0.i249"),
      Instr.load "%7" (Ty.int 32) (Operand.reg "%arrayidx.i"),
      Instr.zext "%idxprom.i" 32 64 (Operand.reg "%7"),
      Instr.gep "%arrayidx10.i" (Ty.int 8) (Operand.reg "%3") (Operand.reg "%idxprom.i"),
      Instr.load "%8" (Ty.int 8) (Operand.reg "%arrayidx10.i"),
      Instr.store (Ty.int 64) (Operand.reg "%inc.i") (Operand.reg "%k11.i")
    ],
    term := Term.br "NodeBlock21" },
{ name := "NodeBlock21",
    instrs := [
      Instr.icmp "%Pivot22" IPred.slt 8 (Operand.reg "%8") (Operand.imm (.int 8 (BitVec.ofNat 8 91)))
    ],
    term := Term.condbr (Operand.reg "%Pivot22") "NodeBlock5" "NodeBlock19" },
{ name := "NodeBlock19",
    instrs := [
      Instr.icmp "%Pivot20" IPred.slt 8 (Operand.reg "%8") (Operand.imm (.int 8 (BitVec.ofNat 8 123)))
    ],
    term := Term.condbr (Operand.reg "%Pivot20") "NodeBlock11" "NodeBlock17" },
{ name := "NodeBlock17",
    instrs := [
      Instr.icmp "%Pivot18" IPred.slt 8 (Operand.reg "%8") (Operand.imm (.int 8 (BitVec.ofNat 8 125)))
    ],
    term := Term.condbr (Operand.reg "%Pivot18") "LeafBlock13" "LeafBlock15" },
{ name := "LeafBlock15",
    instrs := [
      Instr.icmp "%SwitchLeaf16" IPred.eq 8 (Operand.reg "%8") (Operand.imm (.int 8 (BitVec.ofNat 8 125)))
    ],
    term := Term.condbr (Operand.reg "%SwitchLeaf16") "if.then53.i" "sw.default.i" },
{ name := "LeafBlock13",
    instrs := [
      Instr.icmp "%SwitchLeaf14" IPred.eq 8 (Operand.reg "%8") (Operand.imm (.int 8 (BitVec.ofNat 8 123)))
    ],
    term := Term.condbr (Operand.reg "%SwitchLeaf14") "if.then.i" "sw.default.i" },
{ name := "NodeBlock11",
    instrs := [
      Instr.icmp "%Pivot12" IPred.slt 8 (Operand.reg "%8") (Operand.imm (.int 8 (BitVec.ofNat 8 93)))
    ],
    term := Term.condbr (Operand.reg "%Pivot12") "LeafBlock7" "LeafBlock9" },
{ name := "LeafBlock9",
    instrs := [
      Instr.icmp "%SwitchLeaf10" IPred.eq 8 (Operand.reg "%8") (Operand.imm (.int 8 (BitVec.ofNat 8 93)))
    ],
    term := Term.condbr (Operand.reg "%SwitchLeaf10") "if.then53.i" "sw.default.i" },
{ name := "LeafBlock7",
    instrs := [
      Instr.icmp "%SwitchLeaf8" IPred.eq 8 (Operand.reg "%8") (Operand.imm (.int 8 (BitVec.ofNat 8 91)))
    ],
    term := Term.condbr (Operand.reg "%SwitchLeaf8") "if.then.i" "sw.default.i" },
{ name := "NodeBlock5",
    instrs := [
      Instr.icmp "%Pivot6" IPred.slt 8 (Operand.reg "%8") (Operand.imm (.int 8 (BitVec.ofNat 8 44)))
    ],
    term := Term.condbr (Operand.reg "%Pivot6") "LeafBlock" "NodeBlock" },
{ name := "NodeBlock",
    instrs := [
      Instr.icmp "%Pivot" IPred.slt 8 (Operand.reg "%8") (Operand.imm (.int 8 (BitVec.ofNat 8 58)))
    ],
    term := Term.condbr (Operand.reg "%Pivot") "LeafBlock1" "LeafBlock3" },
{ name := "LeafBlock3",
    instrs := [
      Instr.icmp "%SwitchLeaf4" IPred.eq 8 (Operand.reg "%8") (Operand.imm (.int 8 (BitVec.ofNat 8 58)))
    ],
    term := Term.condbr (Operand.reg "%SwitchLeaf4") "if.then173.i" "sw.default.i" },
{ name := "LeafBlock1",
    instrs := [
      Instr.icmp "%SwitchLeaf2" IPred.eq 8 (Operand.reg "%8") (Operand.imm (.int 8 (BitVec.ofNat 8 44)))
    ],
    term := Term.condbr (Operand.reg "%SwitchLeaf2") "if.then127.i" "sw.default.i" },
{ name := "LeafBlock",
    instrs := [
      Instr.icmp "%SwitchLeaf" IPred.eq 8 (Operand.reg "%8") (Operand.imm (.int 8 (BitVec.ofNat 8 34)))
    ],
    term := Term.condbr (Operand.reg "%SwitchLeaf") "sw.bb202.i" "sw.default.i" },
{ name := "if.then.i",
    instrs := [
      Instr.load "%9" (Ty.int 32) (Operand.reg "%root_done.i"),
      Instr.call "%call14.i" (Ty.int 32) "s2_value_pos" [((Ty.int 32), (Operand.reg "%sp.i.0248")), ((Ty.int 32), (Operand.reg "%9")), (Ty.ptr, (Operand.reg "%ctype.i")), (Ty.ptr, (Operand.reg "%cst.i"))],
      Instr.icmp "%tobool15.not.i" IPred.eq 32 (Operand.reg "%call14.i") (Operand.imm (.int 32 (BitVec.ofNat 32 0)))
    ],
    term := Term.condbr (Operand.reg "%tobool15.not.i") "if.then16.i" "if.end.i" },
{ name := "if.then16.i",
    instrs := [
      Instr.gep "%off1.i.i" (Ty.int 8) (Operand.reg "%e") (Operand.imm (.int 64 (BitVec.ofNat 64 8))),
      Instr.store (Ty.int 64) (Operand.reg "%idxprom.i") (Operand.reg "%off1.i.i")
    ],
    term := Term.br "if.then" },
{ name := "if.end.i",
    instrs := [
      Instr.icmp "%cmp19.i" IPred.ugt 32 (Operand.reg "%sp.i.0248") (Operand.imm (.int 32 (BitVec.ofNat 32 519)))
    ],
    term := Term.condbr (Operand.reg "%cmp19.i") "if.then21.i" "if.end24.i" },
{ name := "if.then21.i",
    instrs := [
      Instr.gep "%off1.i.i38" (Ty.int 8) (Operand.reg "%e") (Operand.imm (.int 64 (BitVec.ofNat 64 8))),
      Instr.store (Ty.int 64) (Operand.reg "%idxprom.i") (Operand.reg "%off1.i.i38")
    ],
    term := Term.br "if.then" },
{ name := "if.end24.i",
    instrs := [
      Instr.icmp "%cmp26.i" IPred.eq 8 (Operand.reg "%8") (Operand.imm (.int 8 (BitVec.ofNat 8 123))),
      Instr.select "%conv28.i" (Ty.int 8) (Operand.reg "%cmp26.i") (Operand.imm (.int 8 (BitVec.ofNat 8 1))) (Operand.imm (.int 8 (BitVec.ofNat 8 2))),
      Instr.zext "%idxprom29.i" 32 64 (Operand.reg "%sp.i.0248"),
      Instr.gep "%arrayidx30.i" (Ty.int 8) (Operand.reg "%ctype.i") (Operand.reg "%idxprom29.i"),
      Instr.store (Ty.int 8) (Operand.reg "%conv28.i") (Operand.reg "%arrayidx30.i"),
      Instr.gep "%arrayidx32.i" (Ty.int 8) (Operand.reg "%cst.i") (Operand.reg "%idxprom29.i"),
      Instr.store (Ty.int 8) (Operand.imm (.int 8 (BitVec.ofNat 8 0))) (Operand.reg "%arrayidx32.i"),
      Instr.binop "%inc33.i" BinOp.add 32 (Operand.reg "%sp.i.0248") (Operand.imm (.int 32 (BitVec.ofNat 32 1))),
      Instr.select "%conv42.i" (Ty.int 8) (Operand.reg "%cmp26.i") (Operand.imm (.int 8 (BitVec.ofNat 8 1))) (Operand.imm (.int 8 (BitVec.ofNat 8 3))),
      Instr.load "%10" (Ty.int 32) (Operand.reg "%hash1.i.i"),
      Instr.icmp "%tobool.not.i.i" IPred.eq 32 (Operand.reg "%10") (Operand.imm (.int 32 (BitVec.ofNat 32 0)))
    ],
    term := Term.condbr (Operand.reg "%tobool.not.i.i") "if.end.i.i" "if.then.i.i" },
{ name := "if.then.i.i",
    instrs := [
      Instr.load "%11" (Ty.int 64) (Operand.reg "%h1.i.i.i51"),
      Instr.zext "%conv.i.i.i" 8 64 (Operand.reg "%conv42.i"),
      Instr.binop "%xor.us.i.i.i" BinOp.xor 64 (Operand.reg "%11") (Operand.reg "%conv.i.i.i"),
      Instr.binop "%12" BinOp.mul 64 (Operand.reg "%xor.us.i.i.i") (Operand.imm (.int 64 (BitVec.ofNat 64 16088033396387240377))),
      Instr.binop "%mul11.i.i.i" BinOp.add 64 (Operand.reg "%12") (Operand.imm (.int 64 (BitVec.ofNat 64 11400714819323198485))),
      Instr.store (Ty.int 64) (Operand.reg "%mul11.i.i.i") (Operand.reg "%h1.i.i.i51")
    ],
    term := Term.br "cleanup478.i" },
{ name := "if.end.i.i",
    instrs := [
      Instr.load "%o.val.i.i" (Ty.int 64) (Operand.reg "%len"),
      Instr.load "%o.val11.i.i" (Ty.int 64) (Operand.reg "%cap"),
      Instr.binop "%add.i.i.i" BinOp.add 64 (Operand.reg "%o.val.i.i") (Operand.imm (.int 64 (BitVec.ofNat 64 1))),
      Instr.icmp "%cmp.not.i.i.i" IPred.ugt 64 (Operand.reg "%add.i.i.i") (Operand.reg "%o.val11.i.i")
    ],
    term := Term.condbr (Operand.reg "%cmp.not.i.i.i") "if.end.i.i.i" "out_reserve.exit.i.i" },
{ name := "if.end.i.i.i",
    instrs := [
      Instr.callVoid "llvm.trap" []
    ],
    term := Term.unreachable },
{ name := "out_reserve.exit.i.i",
    instrs := [
      Instr.load "%13" Ty.ptr (Operand.reg "%z"),
      Instr.gep "%add.ptr.i.i" (Ty.int 8) (Operand.reg "%13") (Operand.reg "%o.val.i.i"),
      Instr.store (Ty.int 8) (Operand.reg "%conv42.i") (Operand.reg "%add.ptr.i.i"),
      Instr.store (Ty.int 64) (Operand.reg "%add.i.i.i") (Operand.reg "%len")
    ],
    term := Term.br "cleanup478.i" },
{ name := "if.then53.i",
    instrs := [
      Instr.icmp "%cmp54.i" IPred.eq 32 (Operand.reg "%sp.i.0248") (Operand.imm (.int 32 (BitVec.ofNat 32 0)))
    ],
    term := Term.condbr (Operand.reg "%cmp54.i") "if.then56.i" "if.end59.i" },
{ name := "if.then56.i",
    instrs := [
      Instr.gep "%off1.i.i41" (Ty.int 8) (Operand.reg "%e") (Operand.imm (.int 64 (BitVec.ofNat 64 8))),
      Instr.store (Ty.int 64) (Operand.reg "%idxprom.i") (Operand.reg "%off1.i.i41")
    ],
    term := Term.br "if.then" },
{ name := "if.end59.i",
    instrs := [
      Instr.binop "%sub.i" BinOp.add 32 (Operand.reg "%sp.i.0248") (Operand.imm (.int 32 (BitVec.ofNat 32 4294967295))),
      Instr.icmp "%cmp61.i" IPred.eq 8 (Operand.reg "%8") (Operand.imm (.int 8 (BitVec.ofNat 8 125))),
      Instr.select "%conv64.i" (Ty.int 32) (Operand.reg "%cmp61.i") (Operand.imm (.int 32 (BitVec.ofNat 32 1))) (Operand.imm (.int 32 (BitVec.ofNat 32 2))),
      Instr.zext "%idxprom65.i" 32 64 (Operand.reg "%sub.i"),
      Instr.gep "%arrayidx66.i" (Ty.int 8) (Operand.reg "%ctype.i") (Operand.reg "%idxprom65.i"),
      Instr.load "%14" (Ty.int 8) (Operand.reg "%arrayidx66.i"),
      Instr.zext "%conv67.i" 8 32 (Operand.reg "%14"),
      Instr.icmp "%cmp69.not.i" IPred.eq 32 (Operand.reg "%conv64.i") (Operand.reg "%conv67.i")
    ],
    term := Term.condbr (Operand.reg "%cmp69.not.i") "if.end74.i" "if.then71.i" },
{ name := "if.then71.i",
    instrs := [
      Instr.gep "%off1.i.i43" (Ty.int 8) (Operand.reg "%e") (Operand.imm (.int 64 (BitVec.ofNat 64 8))),
      Instr.store (Ty.int 64) (Operand.reg "%idxprom.i") (Operand.reg "%off1.i.i43")
    ],
    term := Term.br "if.then" },
{ name := "if.end74.i",
    instrs := [
      Instr.gep "%arrayidx76.i" (Ty.int 8) (Operand.reg "%cst.i") (Operand.reg "%idxprom65.i"),
      Instr.load "%15" (Ty.int 8) (Operand.reg "%arrayidx76.i")
    ],
    term := Term.condbr (Operand.reg "%cmp61.i") "cond.true.i" "cond.end.i" },
{ name := "cond.true.i",
    instrs := [

    ],
    term := Term.br "NodeBlock27" },
{ name := "NodeBlock27",
    instrs := [
      Instr.icmp "%Pivot28" IPred.slt 8 (Operand.reg "%15") (Operand.imm (.int 8 (BitVec.ofNat 8 3)))
    ],
    term := Term.condbr (Operand.reg "%Pivot28") "LeafBlock23" "LeafBlock25" },
{ name := "LeafBlock25",
    instrs := [
      Instr.icmp "%SwitchLeaf26" IPred.eq 8 (Operand.reg "%15") (Operand.imm (.int 8 (BitVec.ofNat 8 3)))
    ],
    term := Term.condbr (Operand.reg "%SwitchLeaf26") "if.then109.i" "cleanup104.i" },
{ name := "LeafBlock23",
    instrs := [
      Instr.icmp "%SwitchLeaf24" IPred.eq 8 (Operand.reg "%15") (Operand.imm (.int 8 (BitVec.ofNat 8 0)))
    ],
    term := Term.condbr (Operand.reg "%SwitchLeaf24") "if.then109.i" "cleanup104.i" },
{ name := "cond.end.i",
    instrs := [
      Instr.icmp "%16" IPred.ult 8 (Operand.reg "%15") (Operand.imm (.int 8 (BitVec.ofNat 8 2)))
    ],
    term := Term.condbr (Operand.reg "%16") "if.then109.i" "cleanup104.i" },
{ name := "cleanup104.i",
    instrs := [
      Instr.gep "%off1.i.i45" (Ty.int 8) (Operand.reg "%e") (Operand.imm (.int 64 (BitVec.ofNat 64 8))),
      Instr.store (Ty.int 64) (Operand.reg "%idxprom.i") (Operand.reg "%off1.i.i45")
    ],
    term := Term.br "if.then" },
{ name := "if.then109.i",
    instrs := [
      Instr.phi "%conv115.i" (Ty.int 8) [("LeafBlock23", (Operand.imm (.int 8 (BitVec.ofNat 8 2)))), ("LeafBlock25", (Operand.imm (.int 8 (BitVec.ofNat 8 2)))), ("cond.end.i", (Operand.imm (.int 8 (BitVec.ofNat 8 4))))],
      Instr.callVoid "s2_after_value" [((Ty.int 32), (Operand.reg "%sub.i")), (Ty.ptr, (Operand.reg "%root_done.i")), (Ty.ptr, (Operand.reg "%ctype.i")), (Ty.ptr, (Operand.reg "%cst.i"))],
      Instr.load "%17" (Ty.int 32) (Operand.reg "%hash1.i.i"),
      Instr.icmp "%tobool.not.i.i49" IPred.eq 32 (Operand.reg "%17") (Operand.imm (.int 32 (BitVec.ofNat 32 0)))
    ],
    term := Term.condbr (Operand.reg "%tobool.not.i.i49") "if.end.i.i55" "if.then.i.i50" },
{ name := "if.then.i.i50",
    instrs := [
      Instr.load "%18" (Ty.int 64) (Operand.reg "%h1.i.i.i51"),
      Instr.zext "%conv.i.i.i52" 8 64 (Operand.reg "%conv115.i"),
      Instr.binop "%xor.us.i.i.i53" BinOp.xor 64 (Operand.reg "%18") (Operand.reg "%conv.i.i.i52"),
      Instr.binop "%19" BinOp.mul 64 (Operand.reg "%xor.us.i.i.i53") (Operand.imm (.int 64 (BitVec.ofNat 64 16088033396387240377))),
      Instr.binop "%mul11.i.i.i54" BinOp.add 64 (Operand.reg "%19") (Operand.imm (.int 64 (BitVec.ofNat 64 11400714819323198485))),
      Instr.store (Ty.int 64) (Operand.reg "%mul11.i.i.i54") (Operand.reg "%h1.i.i.i51")
    ],
    term := Term.br "cleanup478.i" },
{ name := "if.end.i.i55",
    instrs := [
      Instr.load "%o.val.i.i56" (Ty.int 64) (Operand.reg "%len"),
      Instr.load "%o.val11.i.i57" (Ty.int 64) (Operand.reg "%cap"),
      Instr.binop "%add.i.i.i58" BinOp.add 64 (Operand.reg "%o.val.i.i56") (Operand.imm (.int 64 (BitVec.ofNat 64 1))),
      Instr.icmp "%cmp.not.i.i.i59" IPred.ugt 64 (Operand.reg "%add.i.i.i58") (Operand.reg "%o.val11.i.i57")
    ],
    term := Term.condbr (Operand.reg "%cmp.not.i.i.i59") "if.end.i.i.i64" "out_reserve.exit.i.i60" },
{ name := "if.end.i.i.i64",
    instrs := [
      Instr.callVoid "llvm.trap" []
    ],
    term := Term.unreachable },
{ name := "out_reserve.exit.i.i60",
    instrs := [
      Instr.load "%20" Ty.ptr (Operand.reg "%z"),
      Instr.gep "%add.ptr.i.i61" (Ty.int 8) (Operand.reg "%20") (Operand.reg "%o.val.i.i56"),
      Instr.store (Ty.int 8) (Operand.reg "%conv115.i") (Operand.reg "%add.ptr.i.i61"),
      Instr.store (Ty.int 64) (Operand.reg "%add.i.i.i58") (Operand.reg "%len")
    ],
    term := Term.br "cleanup478.i" },
{ name := "if.then127.i",
    instrs := [
      Instr.icmp "%cmp128.i" IPred.eq 32 (Operand.reg "%sp.i.0248") (Operand.imm (.int 32 (BitVec.ofNat 32 0)))
    ],
    term := Term.condbr (Operand.reg "%cmp128.i") "if.then130.i" "if.end133.i" },
{ name := "if.then130.i",
    instrs := [
      Instr.gep "%off1.i.i66" (Ty.int 8) (Operand.reg "%e") (Operand.imm (.int 64 (BitVec.ofNat 64 8))),
      Instr.store (Ty.int 64) (Operand.reg "%idxprom.i") (Operand.reg "%off1.i.i66")
    ],
    term := Term.br "if.then" },
{ name := "if.end133.i",
    instrs := [
      Instr.binop "%sub135.i" BinOp.add 32 (Operand.reg "%sp.i.0248") (Operand.imm (.int 32 (BitVec.ofNat 32 4294967295))),
      Instr.zext "%idxprom136.i" 32 64 (Operand.reg "%sub135.i"),
      Instr.gep "%arrayidx137.i" (Ty.int 8) (Operand.reg "%ctype.i") (Operand.reg "%idxprom136.i"),
      Instr.load "%21" (Ty.int 8) (Operand.reg "%arrayidx137.i"),
      Instr.icmp "%cmp139.i" IPred.eq 8 (Operand.reg "%21") (Operand.imm (.int 8 (BitVec.ofNat 8 1))),
      Instr.gep "%arrayidx143.i" (Ty.int 8) (Operand.reg "%cst.i") (Operand.reg "%idxprom136.i"),
      Instr.load "%22" (Ty.int 8) (Operand.reg "%arrayidx143.i")
    ],
    term := Term.condbr (Operand.reg "%cmp139.i") "if.then141.i" "if.else153.i" },
{ name := "if.then141.i",
    instrs := [
      Instr.icmp "%cmp145.not.i" IPred.eq 8 (Operand.reg "%22") (Operand.imm (.int 8 (BitVec.ofNat 8 3)))
    ],
    term := Term.condbr (Operand.reg "%cmp145.not.i") "if.end150.i" "if.then147.i" },
{ name := "if.then147.i",
    instrs := [
      Instr.gep "%off1.i.i68" (Ty.int 8) (Operand.reg "%e") (Operand.imm (.int 64 (BitVec.ofNat 64 8))),
      Instr.store (Ty.int 64) (Operand.reg "%idxprom.i") (Operand.reg "%off1.i.i68")
    ],
    term := Term.br "if.then" },
{ name := "if.end150.i",
    instrs := [
      Instr.store (Ty.int 8) (Operand.imm (.int 8 (BitVec.ofNat 8 4))) (Operand.reg "%arrayidx143.i")
    ],
    term := Term.br "cleanup478.i" },
{ name := "if.else153.i",
    instrs := [
      Instr.icmp "%cmp157.not.i" IPred.eq 8 (Operand.reg "%22") (Operand.imm (.int 8 (BitVec.ofNat 8 1)))
    ],
    term := Term.condbr (Operand.reg "%cmp157.not.i") "if.end162.i" "if.then159.i" },
{ name := "if.then159.i",
    instrs := [
      Instr.gep "%off1.i.i70" (Ty.int 8) (Operand.reg "%e") (Operand.imm (.int 64 (BitVec.ofNat 64 8))),
      Instr.store (Ty.int 64) (Operand.reg "%idxprom.i") (Operand.reg "%off1.i.i70")
    ],
    term := Term.br "if.then" },
{ name := "if.end162.i",
    instrs := [
      Instr.store (Ty.int 8) (Operand.imm (.int 8 (BitVec.ofNat 8 2))) (Operand.reg "%arrayidx143.i")
    ],
    term := Term.br "cleanup478.i" },
{ name := "if.then173.i",
    instrs := [
      Instr.icmp "%cmp174.i" IPred.eq 32 (Operand.reg "%sp.i.0248") (Operand.imm (.int 32 (BitVec.ofNat 32 0)))
    ],
    term := Term.condbr (Operand.reg "%cmp174.i") "if.then176.i" "if.end179.i" },
{ name := "if.then176.i",
    instrs := [
      Instr.gep "%off1.i.i72" (Ty.int 8) (Operand.reg "%e") (Operand.imm (.int 64 (BitVec.ofNat 64 8))),
      Instr.store (Ty.int 64) (Operand.reg "%idxprom.i") (Operand.reg "%off1.i.i72")
    ],
    term := Term.br "if.then" },
{ name := "if.end179.i",
    instrs := [
      Instr.binop "%sub181.i" BinOp.add 32 (Operand.reg "%sp.i.0248") (Operand.imm (.int 32 (BitVec.ofNat 32 4294967295))),
      Instr.zext "%idxprom182.i" 32 64 (Operand.reg "%sub181.i"),
      Instr.gep "%arrayidx183.i" (Ty.int 8) (Operand.reg "%ctype.i") (Operand.reg "%idxprom182.i"),
      Instr.load "%23" (Ty.int 8) (Operand.reg "%arrayidx183.i"),
      Instr.icmp "%cmp185.not.i" IPred.eq 8 (Operand.reg "%23") (Operand.imm (.int 8 (BitVec.ofNat 8 1)))
    ],
    term := Term.condbr (Operand.reg "%cmp185.not.i") "lor.lhs.false.i" "if.then192.i" },
{ name := "lor.lhs.false.i",
    instrs := [
      Instr.gep "%arrayidx188.i" (Ty.int 8) (Operand.reg "%cst.i") (Operand.reg "%idxprom182.i"),
      Instr.load "%24" (Ty.int 8) (Operand.reg "%arrayidx188.i"),
      Instr.icmp "%cmp190.not.i" IPred.eq 8 (Operand.reg "%24") (Operand.imm (.int 8 (BitVec.ofNat 8 1)))
    ],
    term := Term.condbr (Operand.reg "%cmp190.not.i") "if.end195.i" "if.then192.i" },
{ name := "if.then192.i",
    instrs := [
      Instr.gep "%off1.i.i74" (Ty.int 8) (Operand.reg "%e") (Operand.imm (.int 64 (BitVec.ofNat 64 8))),
      Instr.store (Ty.int 64) (Operand.reg "%idxprom.i") (Operand.reg "%off1.i.i74")
    ],
    term := Term.br "if.then" },
{ name := "if.end195.i",
    instrs := [
      Instr.store (Ty.int 8) (Operand.imm (.int 8 (BitVec.ofNat 8 2))) (Operand.reg "%arrayidx188.i")
    ],
    term := Term.br "cleanup478.i" },
{ name := "sw.bb202.i",
    instrs := [
      Instr.icmp "%cmp203.not.i" IPred.ult 64 (Operand.reg "%inc.i") (Operand.reg "%nep")
    ],
    term := Term.condbr (Operand.reg "%cmp203.not.i") "if.end207.i" "if.then205.i" },
{ name := "if.then205.i",
    instrs := [
      Instr.gep "%off1.i.i76" (Ty.int 8) (Operand.reg "%e") (Operand.imm (.int 64 (BitVec.ofNat 64 8))),
      Instr.store (Ty.int 64) (Operand.reg "%4") (Operand.reg "%off1.i.i76")
    ],
    term := Term.br "if.then" },
{ name := "if.end207.i",
    instrs := [
      Instr.binop "%inc208.i" BinOp.add 64 (Operand.reg "%k.0.i249") (Operand.imm (.int 64 (BitVec.ofNat 64 2))),
      Instr.gep "%arrayidx209.i" (Ty.int 32) (Operand.reg "%5") (Operand.reg "%inc.i"),
      Instr.load "%25" (Ty.int 32) (Operand.reg "%arrayidx209.i"),
      Instr.store (Ty.int 64) (Operand.reg "%inc208.i") (Operand.reg "%k11.i"),
      Instr.zext "%conv211.i" 32 64 (Operand.reg "%25"),
      Instr.icmp "%cmp212.not.i" IPred.ugt 64 (Operand.reg "%4") (Operand.reg "%conv211.i")
    ],
    term := Term.condbr (Operand.reg "%cmp212.not.i") "if.then219.i" "if.then214.i" },
{ name := "if.then214.i",
    instrs := [
      Instr.gep "%off1.i.i78" (Ty.int 8) (Operand.reg "%e") (Operand.imm (.int 64 (BitVec.ofNat 64 8))),
      Instr.store (Ty.int 64) (Operand.reg "%4") (Operand.reg "%off1.i.i78")
    ],
    term := Term.br "if.then" },
{ name := "if.then219.i",
    instrs := [
      Instr.load "%26" (Ty.int 32) (Operand.reg "%root_done.i"),
      Instr.call "%call222.i" (Ty.int 32) "s2_value_pos" [((Ty.int 32), (Operand.reg "%sp.i.0248")), ((Ty.int 32), (Operand.reg "%26")), (Ty.ptr, (Operand.reg "%ctype.i")), (Ty.ptr, (Operand.reg "%cst.i"))],
      Instr.icmp "%cmp223.not.i" IPred.eq 32 (Operand.reg "%sp.i.0248") (Operand.imm (.int 32 (BitVec.ofNat 32 0)))
    ],
    term := Term.condbr (Operand.reg "%cmp223.not.i") "if.end245.i" "land.lhs.true.i" },
{ name := "land.lhs.true.i",
    instrs := [
      Instr.binop "%sub225.i" BinOp.add 32 (Operand.reg "%sp.i.0248") (Operand.imm (.int 32 (BitVec.ofNat 32 4294967295))),
      Instr.zext "%idxprom226.i" 32 64 (Operand.reg "%sub225.i"),
      Instr.gep "%arrayidx227.i" (Ty.int 8) (Operand.reg "%ctype.i") (Operand.reg "%idxprom226.i"),
      Instr.load "%27" (Ty.int 8) (Operand.reg "%arrayidx227.i"),
      Instr.icmp "%cmp229.i" IPred.eq 8 (Operand.reg "%27") (Operand.imm (.int 8 (BitVec.ofNat 8 1)))
    ],
    term := Term.condbr (Operand.reg "%cmp229.i") "if.then231.i" "if.end245.i" },
{ name := "if.then231.i",
    instrs := [
      Instr.gep "%arrayidx235.i" (Ty.int 8) (Operand.reg "%cst.i") (Operand.reg "%idxprom226.i"),
      Instr.load "%28" (Ty.int 8) (Operand.reg "%arrayidx235.i"),
      Instr.binop "%29" BinOp.and 8 (Operand.reg "%28") (Operand.imm (.int 8 (BitVec.ofNat 8 251))),
      Instr.icmp "%or.cond.i" IPred.eq 8 (Operand.reg "%29") (Operand.imm (.int 8 (BitVec.ofNat 8 0)))
    ],
    term := Term.br "if.end245.i" },
{ name := "if.end245.i",
    instrs := [
      Instr.phi "%key.1.i" (Ty.int 1) [("if.then231.i", (Operand.reg "%or.cond.i")), ("land.lhs.true.i", (Operand.imm (.int 1 (BitVec.ofNat 1 0)))), ("if.then219.i", (Operand.imm (.int 1 (BitVec.ofNat 1 0))))],
      Instr.icmp "%tobool248.i" IPred.ne 32 (Operand.reg "%call222.i") (Operand.imm (.int 32 (BitVec.ofNat 32 0))),
      Instr.select "%or.cond523.i" (Ty.int 1) (Operand.reg "%key.1.i") (Operand.imm (.int 1 (BitVec.ofNat 1 1))) (Operand.reg "%tobool248.i")
    ],
    term := Term.condbr (Operand.reg "%or.cond523.i") "if.end256.i" "if.then249.i" },
{ name := "if.then249.i",
    instrs := [
      Instr.gep "%off1.i.i80" (Ty.int 8) (Operand.reg "%e") (Operand.imm (.int 64 (BitVec.ofNat 64 8))),
      Instr.store (Ty.int 64) (Operand.reg "%idxprom.i") (Operand.reg "%off1.i.i80")
    ],
    term := Term.br "if.then" },
{ name := "if.end256.i",
    instrs := [
      Instr.binop "%30" BinOp.xor 64 (Operand.reg "%idxprom.i") (Operand.imm (.int 64 (BitVec.ofNat 64 18446744073709551615))),
      Instr.binop "%sub260.i" BinOp.add 64 (Operand.reg "%conv211.i") (Operand.reg "%30"),
      Instr.callVoid "llvm.lifetime.start.p0" [((Ty.int 64), (Operand.imm (.int 64 (BitVec.ofNat 64 8)))), (Ty.ptr, (Operand.reg "%outn.i"))],
      Instr.store (Ty.int 64) (Operand.imm (.int 64 (BitVec.ofNat 64 0))) (Operand.reg "%outn.i"),
      Instr.binop "%add.i" BinOp.add 64 (Operand.reg "%sub260.i") (Operand.imm (.int 64 (BitVec.ofNat 64 64))),
      Instr.load "%z.val36" (Ty.int 64) (Operand.reg "%alen"),
      Instr.load "%z.val37" (Ty.int 64) (Operand.reg "%acap"),
      Instr.binop "%add.i82" BinOp.add 64 (Operand.reg "%add.i") (Operand.reg "%z.val36"),
      Instr.icmp "%cmp.not.i" IPred.ugt 64 (Operand.reg "%add.i82") (Operand.reg "%z.val37")
    ],
    term := Term.condbr (Operand.reg "%cmp.not.i") "if.end.i83" "z_arena_reserve.exit" },
{ name := "if.end.i83",
    instrs := [
      Instr.callVoid "llvm.trap" []
    ],
    term := Term.unreachable },
{ name := "z_arena_reserve.exit",
    instrs := [
      Instr.load "%31" Ty.ptr (Operand.reg "%ar"),
      Instr.gep "%add.ptr.i" (Ty.int 8) (Operand.reg "%31") (Operand.reg "%z.val36"),
      Instr.gep "%add.ptr271.i" (Ty.int 8) (Operand.reg "%arrayidx10.i") (Operand.imm (.int 64 (BitVec.ofNat 64 1))),
      Instr.call "%call272.i" (Ty.int 32) "s2_string_body" [(Ty.ptr, (Operand.reg "%c.i")), (Ty.ptr, (Operand.reg "%add.ptr271.i")), ((Ty.int 64), (Operand.reg "%sub260.i")), (Ty.ptr, (Operand.reg "%add.ptr.i")), (Ty.ptr, (Operand.reg "%outn.i")), (Ty.ptr, (Operand.reg "%xp")), (Ty.ptr, (Operand.reg "%xj.i")), ((Ty.int 64), (Operand.reg "%nxp"))]
    ],
    term := Term.br "NodeBlock31" },
{ name := "NodeBlock31",
    instrs := [
      Instr.icmp "%Pivot32" IPred.slt 32 (Operand.reg "%call272.i") (Operand.imm (.int 32 (BitVec.ofNat 32 1)))
    ],
    term := Term.condbr (Operand.reg "%Pivot32") "cleanup339.critedge.i" "LeafBlock29" },
{ name := "LeafBlock29",
    instrs := [
      Instr.icmp "%SwitchLeaf30" IPred.eq 32 (Operand.reg "%call272.i") (Operand.imm (.int 32 (BitVec.ofNat 32 1)))
    ],
    term := Term.condbr (Operand.reg "%SwitchLeaf30") "if.then281.i" "if.else285.i" },
{ name := "if.then281.i",
    instrs := [
      Instr.binop "%add283.i" BinOp.add 32 (Operand.reg "%7") (Operand.imm (.int 32 (BitVec.ofNat 32 1))),
      Instr.zext "%conv284.i" 32 64 (Operand.reg "%add283.i"),
      Instr.binop "%or.i" BinOp.or 64 (Operand.reg "%conv284.i") (Operand.imm (.int 64 (BitVec.ofNat 64 9223372036854775808)))
    ],
    term := Term.br "if.end290.i" },
{ name := "if.else285.i",
    instrs := [
      Instr.load "%32" (Ty.int 64) (Operand.reg "%outn.i"),
      Instr.binop "%add289.i" BinOp.add 64 (Operand.reg "%z.val36") (Operand.reg "%32"),
      Instr.store (Ty.int 64) (Operand.reg "%add289.i") (Operand.reg "%alen")
    ],
    term := Term.br "if.end290.i" },
{ name := "if.end290.i",
    instrs := [
      Instr.phi "%conv286.i.sink.in" (Ty.int 64) [("if.then281.i", (Operand.reg "%sub260.i")), ("if.else285.i", (Operand.reg "%32"))],
      Instr.phi "%.sink" (Ty.int 64) [("if.then281.i", (Operand.reg "%or.i")), ("if.else285.i", (Operand.reg "%z.val36"))],
      Instr.load "%z.val" (Ty.int 64) (Operand.reg "%len"),
      Instr.load "%z.val33" (Ty.int 64) (Operand.reg "%cap"),
      Instr.binop "%add.i84" BinOp.add 64 (Operand.reg "%z.val") (Operand.imm (.int 64 (BitVec.ofNat 64 13))),
      Instr.icmp "%cmp.not.i85" IPred.ugt 64 (Operand.reg "%add.i84") (Operand.reg "%z.val33")
    ],
    term := Term.condbr (Operand.reg "%cmp.not.i85") "if.end.i86" "if.then328.i" },
{ name := "if.end.i86",
    instrs := [
      Instr.callVoid "llvm.trap" []
    ],
    term := Term.unreachable },
{ name := "if.then328.i",
    instrs := [
      Instr.trunc "%conv286.i.sink" 64 32 (Operand.reg "%conv286.i.sink.in"),
      Instr.load "%33" Ty.ptr (Operand.reg "%z"),
      Instr.gep "%add.ptr297.i" (Ty.int 8) (Operand.reg "%33") (Operand.reg "%z.val"),
      Instr.select "%conv300.i" (Ty.int 8) (Operand.reg "%key.1.i") (Operand.imm (.int 8 (BitVec.ofNat 8 5))) (Operand.imm (.int 8 (BitVec.ofNat 8 6))),
      Instr.store (Ty.int 8) (Operand.reg "%conv300.i") (Operand.reg "%add.ptr297.i"),
      Instr.gep "%add.ptr302.i" (Ty.int 8) (Operand.reg "%add.ptr297.i") (Operand.imm (.int 64 (BitVec.ofNat 64 1))),
      Instr.store (Ty.int 32) (Operand.reg "%conv286.i.sink") (Operand.reg "%add.ptr302.i"),
      Instr.gep "%add.ptr304.i" (Ty.int 8) (Operand.reg "%add.ptr297.i") (Operand.imm (.int 64 (BitVec.ofNat 64 5))),
      Instr.store (Ty.int 64) (Operand.reg "%.sink") (Operand.reg "%add.ptr304.i"),
      Instr.store (Ty.int 64) (Operand.reg "%add.i84") (Operand.reg "%len"),
      Instr.callVoid "llvm.lifetime.end.p0" [((Ty.int 64), (Operand.imm (.int 64 (BitVec.ofNat 64 8)))), (Ty.ptr, (Operand.reg "%outn.i"))]
    ],
    term := Term.condbr (Operand.reg "%key.1.i") "if.then330.i" "if.else334.i" },
{ name := "if.then330.i",
    instrs := [
      Instr.binop "%sub331.i" BinOp.add 32 (Operand.reg "%sp.i.0248") (Operand.imm (.int 32 (BitVec.ofNat 32 4294967295))),
      Instr.zext "%idxprom332.i" 32 64 (Operand.reg "%sub331.i"),
      Instr.gep "%arrayidx333.i" (Ty.int 8) (Operand.reg "%cst.i") (Operand.reg "%idxprom332.i"),
      Instr.store (Ty.int 8) (Operand.imm (.int 8 (BitVec.ofNat 8 1))) (Operand.reg "%arrayidx333.i")
    ],
    term := Term.br "cleanup478.i" },
{ name := "if.else334.i",
    instrs := [
      Instr.callVoid "s2_after_value" [((Ty.int 32), (Operand.reg "%sp.i.0248")), (Ty.ptr, (Operand.reg "%root_done.i")), (Ty.ptr, (Operand.reg "%ctype.i")), (Ty.ptr, (Operand.reg "%cst.i"))]
    ],
    term := Term.br "cleanup478.i" },
{ name := "cleanup339.critedge.i",
    instrs := [
      Instr.callVoid "llvm.lifetime.end.p0" [((Ty.int 64), (Operand.imm (.int 64 (BitVec.ofNat 64 8)))), (Ty.ptr, (Operand.reg "%outn.i"))]
    ],
    term := Term.br "if.then" },
{ name := "sw.default.i",
    instrs := [
      Instr.icmp "%cmp343.i" IPred.ult 64 (Operand.reg "%inc.i") (Operand.reg "%nep")
    ],
    term := Term.condbr (Operand.reg "%cmp343.i") "cond.true345.i" "cond.end349.i" },
{ name := "cond.true345.i",
    instrs := [
      Instr.gep "%arrayidx346.i" (Ty.int 32) (Operand.reg "%5") (Operand.reg "%inc.i"),
      Instr.load "%34" (Ty.int 32) (Operand.reg "%arrayidx346.i"),
      Instr.zext "%conv347.i" 32 64 (Operand.reg "%34")
    ],
    term := Term.br "cond.end349.i" },
{ name := "cond.end349.i",
    instrs := [
      Instr.phi "%cond350.i" (Ty.int 64) [("cond.true345.i", (Operand.reg "%conv347.i")), ("sw.default.i", (Operand.reg "%4"))],
      Instr.callVoid "llvm.lifetime.start.p0" [((Ty.int 64), (Operand.imm (.int 64 (BitVec.ofNat 64 24)))), (Ty.ptr, (Operand.reg "%t352.i"))],
      Instr.store (Ty.int 64) (Operand.reg "%idxprom.i") (Operand.reg "%t352.i"),
      Instr.store (Ty.int 32) (Operand.imm (.int 32 (BitVec.ofNat 32 1))) (Operand.reg "%gap.i"),
      Instr.icmp "%cmp355.i" IPred.ugt 64 (Operand.reg "%cond350.i") (Operand.reg "%idxprom.i")
    ],
    term := Term.condbr (Operand.reg "%cmp355.i") "land.lhs.true357.i" "if.end372.i" },
{ name := "land.lhs.true357.i",
    instrs := [
      Instr.gep "%gep" (Ty.int 8) (Operand.reg "%invariant.gep") (Operand.reg "%cond350.i"),
      Instr.load "%35" (Ty.int 8) (Operand.reg "%gep")
    ],
    term := Term.br "NodeBlock41" },
{ name := "NodeBlock41",
    instrs := [
      Instr.icmp "%Pivot42" IPred.slt 8 (Operand.reg "%35") (Operand.imm (.int 8 (BitVec.ofNat 8 13)))
    ],
    term := Term.condbr (Operand.reg "%Pivot42") "LeafBlock33" "NodeBlock39" },
{ name := "NodeBlock39",
    instrs := [
      Instr.icmp "%Pivot40" IPred.slt 8 (Operand.reg "%35") (Operand.imm (.int 8 (BitVec.ofNat 8 32)))
    ],
    term := Term.condbr (Operand.reg "%Pivot40") "LeafBlock35" "LeafBlock37" },
{ name := "LeafBlock37",
    instrs := [
      Instr.icmp "%SwitchLeaf38" IPred.eq 8 (Operand.reg "%35") (Operand.imm (.int 8 (BitVec.ofNat 8 32)))
    ],
    term := Term.condbr (Operand.reg "%SwitchLeaf38") "land.rhs.i.preheader" "if.end372.i" },
{ name := "LeafBlock35",
    instrs := [
      Instr.icmp "%SwitchLeaf36" IPred.eq 8 (Operand.reg "%35") (Operand.imm (.int 8 (BitVec.ofNat 8 13)))
    ],
    term := Term.condbr (Operand.reg "%SwitchLeaf36") "land.rhs.i.preheader" "if.end372.i" },
{ name := "LeafBlock33",
    instrs := [
      Instr.binop "%.off" BinOp.add 8 (Operand.reg "%35") (Operand.imm (.int 8 (BitVec.ofNat 8 247))),
      Instr.icmp "%SwitchLeaf34" IPred.ule 8 (Operand.reg "%.off") (Operand.imm (.int 8 (BitVec.ofNat 8 1)))
    ],
    term := Term.condbr (Operand.reg "%SwitchLeaf34") "land.rhs.i.preheader" "if.end372.i" },
{ name := "land.rhs.i.preheader",
    instrs := [

    ],
    term := Term.br "land.rhs.i" },
{ name := "land.rhs.i",
    instrs := [
      Instr.phi "%ee.0.i238" (Ty.int 64) [("while.body370.i", (Operand.reg "%inc371.i")), ("land.rhs.i.preheader", (Operand.reg "%idxprom.i"))],
      Instr.gep "%arrayidx367.i" (Ty.int 8) (Operand.reg "%3") (Operand.reg "%ee.0.i238"),
      Instr.load "%36" (Ty.int 8) (Operand.reg "%arrayidx367.i")
    ],
    term := Term.br "NodeBlock52" },
{ name := "NodeBlock52",
    instrs := [
      Instr.icmp "%Pivot53" IPred.slt 8 (Operand.reg "%36") (Operand.imm (.int 8 (BitVec.ofNat 8 13)))
    ],
    term := Term.condbr (Operand.reg "%Pivot53") "LeafBlock43" "NodeBlock50" },
{ name := "NodeBlock50",
    instrs := [
      Instr.icmp "%Pivot51" IPred.slt 8 (Operand.reg "%36") (Operand.imm (.int 8 (BitVec.ofNat 8 32)))
    ],
    term := Term.condbr (Operand.reg "%Pivot51") "LeafBlock46" "LeafBlock48" },
{ name := "LeafBlock48",
    instrs := [
      Instr.icmp "%SwitchLeaf49" IPred.eq 8 (Operand.reg "%36") (Operand.imm (.int 8 (BitVec.ofNat 8 32)))
    ],
    term := Term.condbr (Operand.reg "%SwitchLeaf49") "if.end372.i" "while.body370.i" },
{ name := "LeafBlock46",
    instrs := [
      Instr.icmp "%SwitchLeaf47" IPred.eq 8 (Operand.reg "%36") (Operand.imm (.int 8 (BitVec.ofNat 8 13)))
    ],
    term := Term.condbr (Operand.reg "%SwitchLeaf47") "if.end372.i" "while.body370.i" },
{ name := "LeafBlock43",
    instrs := [
      Instr.binop "%.off44" BinOp.add 8 (Operand.reg "%36") (Operand.imm (.int 8 (BitVec.ofNat 8 247))),
      Instr.icmp "%SwitchLeaf45" IPred.ule 8 (Operand.reg "%.off44") (Operand.imm (.int 8 (BitVec.ofNat 8 1)))
    ],
    term := Term.condbr (Operand.reg "%SwitchLeaf45") "if.end372.i" "while.body370.i" },
{ name := "while.body370.i",
    instrs := [
      Instr.binop "%inc371.i" BinOp.add 64 (Operand.reg "%ee.0.i238") (Operand.imm (.int 64 (BitVec.ofNat 64 1))),
      Instr.icmp "%exitcond.not" IPred.eq 64 (Operand.reg "%inc371.i") (Operand.reg "%cond350.i")
    ],
    term := Term.condbr (Operand.reg "%exitcond.not") "if.end372.i" "land.rhs.i" },
{ name := "if.end372.i",
    instrs := [
      Instr.phi "%ee.1.i" (Ty.int 64) [("cond.end349.i", (Operand.reg "%idxprom.i")), ("while.body370.i", (Operand.reg "%cond350.i")), ("LeafBlock43", (Operand.reg "%ee.0.i238")), ("LeafBlock46", (Operand.reg "%ee.0.i238")), ("LeafBlock48", (Operand.reg "%ee.0.i238")), ("LeafBlock33", (Operand.reg "%cond350.i")), ("LeafBlock35", (Operand.reg "%cond350.i")), ("LeafBlock37", (Operand.reg "%cond350.i"))],
      Instr.store (Ty.int 64) (Operand.reg "%ee.1.i") (Operand.reg "%end.i"),
      Instr.icmp "%cmp376.i" IPred.eq 8 (Operand.reg "%8") (Operand.imm (.int 8 (BitVec.ofNat 8 45))),
      Instr.binop "%37" BinOp.add 8 (Operand.reg "%8") (Operand.imm (.int 8 (BitVec.ofNat 8 208))),
      Instr.icmp "%or.cond524.i" IPred.ult 8 (Operand.reg "%37") (Operand.imm (.int 8 (BitVec.ofNat 8 10))),
      Instr.binop "%or.cond677.i" BinOp.or 1 (Operand.reg "%cmp376.i") (Operand.reg "%or.cond524.i")
    ],
    term := Term.condbr (Operand.reg "%or.cond677.i") "if.then413.i" "if.else387.i" },
{ name := "if.else387.i",
    instrs := [

    ],
    term := Term.br "NodeBlock62" },
{ name := "NodeBlock62",
    instrs := [
      Instr.icmp "%Pivot63" IPred.slt 8 (Operand.reg "%8") (Operand.imm (.int 8 (BitVec.ofNat 8 110)))
    ],
    term := Term.condbr (Operand.reg "%Pivot63") "LeafBlock54" "NodeBlock60" },
{ name := "NodeBlock60",
    instrs := [
      Instr.icmp "%Pivot61" IPred.slt 8 (Operand.reg "%8") (Operand.imm (.int 8 (BitVec.ofNat 8 116)))
    ],
    term := Term.condbr (Operand.reg "%Pivot61") "LeafBlock56" "LeafBlock58" },
{ name := "LeafBlock58",
    instrs := [
      Instr.icmp "%SwitchLeaf59" IPred.eq 8 (Operand.reg "%8") (Operand.imm (.int 8 (BitVec.ofNat 8 116)))
    ],
    term := Term.condbr (Operand.reg "%SwitchLeaf59") "if.then413.i" "if.else405.i" },
{ name := "LeafBlock56",
    instrs := [
      Instr.icmp "%SwitchLeaf57" IPred.eq 8 (Operand.reg "%8") (Operand.imm (.int 8 (BitVec.ofNat 8 110)))
    ],
    term := Term.condbr (Operand.reg "%SwitchLeaf57") "if.then403.i" "if.else405.i" },
{ name := "LeafBlock54",
    instrs := [
      Instr.icmp "%SwitchLeaf55" IPred.eq 8 (Operand.reg "%8") (Operand.imm (.int 8 (BitVec.ofNat 8 102)))
    ],
    term := Term.condbr (Operand.reg "%SwitchLeaf55") "if.then397.i" "if.else405.i" },
{ name := "if.then397.i",
    instrs := [

    ],
    term := Term.br "if.then413.i" },
{ name := "if.then403.i",
    instrs := [

    ],
    term := Term.br "if.then413.i" },
{ name := "if.else405.i",
    instrs := [

    ],
    term := Term.br "if.then413.i" },
{ name := "if.then413.i",
    instrs := [
      Instr.phi "%.sink372" (Ty.int 32) [("if.else405.i", (Operand.imm (.int 32 (BitVec.ofNat 32 0)))), ("if.then403.i", (Operand.imm (.int 32 (BitVec.ofNat 32 10)))), ("if.then397.i", (Operand.imm (.int 32 (BitVec.ofNat 32 9)))), ("if.end372.i", (Operand.imm (.int 32 (BitVec.ofNat 32 7)))), ("LeafBlock58", (Operand.imm (.int 32 (BitVec.ofNat 32 8))))],
      Instr.store (Ty.int 32) (Operand.reg "%.sink372") (Operand.reg "%kind404.i"),
      Instr.load "%38" (Ty.int 32) (Operand.reg "%root_done.i"),
      Instr.call "%call416.i" (Ty.int 32) "s2_value_pos" [((Ty.int 32), (Operand.reg "%sp.i.0248")), ((Ty.int 32), (Operand.reg "%38")), (Ty.ptr, (Operand.reg "%ctype.i")), (Ty.ptr, (Operand.reg "%cst.i"))],
      Instr.icmp "%tobool417.not.i" IPred.eq 32 (Operand.reg "%call416.i") (Operand.imm (.int 32 (BitVec.ofNat 32 0)))
    ],
    term := Term.condbr (Operand.reg "%tobool417.not.i") "if.then418.i" "if.then425.i" },
{ name := "if.then418.i",
    instrs := [
      Instr.gep "%off1.i.i91" (Ty.int 8) (Operand.reg "%e") (Operand.imm (.int 64 (BitVec.ofNat 64 8))),
      Instr.store (Ty.int 64) (Operand.reg "%idxprom.i") (Operand.reg "%off1.i.i91")
    ],
    term := Term.br "cleanup474.i" },
{ name := "if.then425.i",
    instrs := [
      Instr.call "%call427.i" (Ty.int 32) "od_scalar_value" [(Ty.ptr, (Operand.reg "%c.i")), (Ty.ptr, (Operand.reg "%t352.i")), (Ty.ptr, (Operand.reg "%z"))],
      Instr.icmp "%tobool428.not.i" IPred.eq 32 (Operand.reg "%call427.i") (Operand.imm (.int 32 (BitVec.ofNat 32 0)))
    ],
    term := Term.condbr (Operand.reg "%tobool428.not.i") "if.then432.i" "if.then447.i" },
{ name := "if.then432.i",
    instrs := [

    ],
    term := Term.condbr (Operand.reg "%cmp343.i") "cond.true.i106" "cond.end.i96" },
{ name := "cond.true.i106",
    instrs := [
      Instr.gep "%arrayidx.i108" (Ty.int 32) (Operand.reg "%5") (Operand.reg "%inc.i"),
      Instr.load "%39" (Ty.int 32) (Operand.reg "%arrayidx.i108"),
      Instr.zext "%conv.i" 32 64 (Operand.reg "%39")
    ],
    term := Term.br "cond.end.i96" },
{ name := "cond.end.i96",
    instrs := [
      Instr.phi "%cond.i" (Ty.int 64) [("cond.true.i106", (Operand.reg "%conv.i")), ("if.then432.i", (Operand.reg "%4"))],
      Instr.icmp "%cmp310.i" IPred.ugt 64 (Operand.reg "%cond.i") (Operand.reg "%idxprom.i")
    ],
    term := Term.condbr (Operand.reg "%cmp310.i") "land.rhs.i103" "while.end.i" },
{ name := "land.rhs.i103",
    instrs := [
      Instr.phi "%ee.011.i" (Ty.int 64) [("while.body.i104", (Operand.reg "%inc.i105")), ("cond.end.i96", (Operand.reg "%idxprom.i"))],
      Instr.gep "%arrayidx5.i" (Ty.int 8) (Operand.reg "%3") (Operand.reg "%ee.011.i"),
      Instr.load "%40" (Ty.int 8) (Operand.reg "%arrayidx5.i")
    ],
    term := Term.br "NodeBlock73" },
{ name := "NodeBlock73",
    instrs := [
      Instr.icmp "%Pivot74" IPred.slt 8 (Operand.reg "%40") (Operand.imm (.int 8 (BitVec.ofNat 8 13)))
    ],
    term := Term.condbr (Operand.reg "%Pivot74") "LeafBlock64" "NodeBlock71" },
{ name := "NodeBlock71",
    instrs := [
      Instr.icmp "%Pivot72" IPred.slt 8 (Operand.reg "%40") (Operand.imm (.int 8 (BitVec.ofNat 8 32)))
    ],
    term := Term.condbr (Operand.reg "%Pivot72") "LeafBlock67" "LeafBlock69" },
{ name := "LeafBlock69",
    instrs := [
      Instr.icmp "%SwitchLeaf70" IPred.eq 8 (Operand.reg "%40") (Operand.imm (.int 8 (BitVec.ofNat 8 32)))
    ],
    term := Term.condbr (Operand.reg "%SwitchLeaf70") "while.end.i" "while.body.i104" },
{ name := "LeafBlock67",
    instrs := [
      Instr.icmp "%SwitchLeaf68" IPred.eq 8 (Operand.reg "%40") (Operand.imm (.int 8 (BitVec.ofNat 8 13)))
    ],
    term := Term.condbr (Operand.reg "%SwitchLeaf68") "while.end.i" "while.body.i104" },
{ name := "LeafBlock64",
    instrs := [
      Instr.binop "%.off65" BinOp.add 8 (Operand.reg "%40") (Operand.imm (.int 8 (BitVec.ofNat 8 247))),
      Instr.icmp "%SwitchLeaf66" IPred.ule 8 (Operand.reg "%.off65") (Operand.imm (.int 8 (BitVec.ofNat 8 1)))
    ],
    term := Term.condbr (Operand.reg "%SwitchLeaf66") "while.end.i" "while.body.i104" },
{ name := "while.body.i104",
    instrs := [
      Instr.binop "%inc.i105" BinOp.add 64 (Operand.reg "%ee.011.i") (Operand.imm (.int 64 (BitVec.ofNat 64 1))),
      Instr.icmp "%exitcond.not.i" IPred.eq 64 (Operand.reg "%inc.i105") (Operand.reg "%cond.i")
    ],
    term := Term.condbr (Operand.reg "%exitcond.not.i") "cleanup474.i" "land.rhs.i103" },
{ name := "while.end.i",
    instrs := [
      Instr.phi "%ee.0.lcssa.i" (Ty.int 64) [("cond.end.i96", (Operand.reg "%idxprom.i")), ("LeafBlock64", (Operand.reg "%ee.011.i")), ("LeafBlock67", (Operand.reg "%ee.011.i")), ("LeafBlock69", (Operand.reg "%ee.011.i"))],
      Instr.icmp "%cmp6.i" IPred.eq 64 (Operand.reg "%ee.0.lcssa.i") (Operand.reg "%cond.i")
    ],
    term := Term.condbr (Operand.reg "%cmp6.i") "cleanup474.i" "if.end.i97" },
{ name := "if.end.i97",
    instrs := [
      Instr.load "%41" (Ty.int 8) (Operand.reg "%arrayidx10.i"),
      Instr.icmp "%cmp11.i" IPred.eq 8 (Operand.reg "%41") (Operand.imm (.int 8 (BitVec.ofNat 8 45))),
      Instr.binop "%42" BinOp.add 8 (Operand.reg "%41") (Operand.imm (.int 8 (BitVec.ofNat 8 208))),
      Instr.icmp "%or.cond.i98" IPred.ult 8 (Operand.reg "%42") (Operand.imm (.int 8 (BitVec.ofNat 8 10))),
      Instr.binop "%or.cond127.i" BinOp.or 1 (Operand.reg "%cmp11.i") (Operand.reg "%or.cond.i98")
    ],
    term := Term.condbr (Operand.reg "%or.cond127.i") "if.then19.i" "if.else.i" },
{ name := "if.then19.i",
    instrs := [
      Instr.callVoid "llvm.lifetime.start.p0" [((Ty.int 64), (Operand.imm (.int 64 (BitVec.ofNat 64 8)))), (Ty.ptr, (Operand.reg "%d.i"))],
      Instr.callVoid "llvm.lifetime.start.p0" [((Ty.int 64), (Operand.imm (.int 64 (BitVec.ofNat 64 8)))), (Ty.ptr, (Operand.reg "%ei.i"))],
      Instr.binop "%sub.i99" BinOp.sub 64 (Operand.reg "%ee.0.lcssa.i") (Operand.reg "%idxprom.i"),
      Instr.call "%call23.i" (Ty.int 32) "num_fast_el1" [(Ty.ptr, (Operand.reg "%arrayidx10.i")), ((Ty.int 64), (Operand.reg "%sub.i99")), (Ty.ptr, (Operand.reg "%d.i")), (Ty.ptr, (Operand.reg "%ei.i"))],
      Instr.icmp "%tobool24.not.not.i" IPred.eq 32 (Operand.reg "%call23.i") (Operand.imm (.int 32 (BitVec.ofNat 32 0)))
    ],
    term := Term.condbr (Operand.reg "%tobool24.not.not.i") "if.then25.i" "if.end67.critedge.i" },
{ name := "if.then25.i",
    instrs := [
      Instr.load "%43" (Ty.int 64) (Operand.reg "%ei.i"),
      Instr.binop "%add.i100" BinOp.add 64 (Operand.reg "%43") (Operand.reg "%idxprom.i"),
      Instr.gep "%off1.i.i101" (Ty.int 8) (Operand.reg "%e") (Operand.imm (.int 64 (BitVec.ofNat 64 8))),
      Instr.store (Ty.int 64) (Operand.reg "%add.i100") (Operand.reg "%off1.i.i101"),
      Instr.callVoid "llvm.lifetime.end.p0" [((Ty.int 64), (Operand.imm (.int 64 (BitVec.ofNat 64 8)))), (Ty.ptr, (Operand.reg "%ei.i"))],
      Instr.callVoid "llvm.lifetime.end.p0" [((Ty.int 64), (Operand.imm (.int 64 (BitVec.ofNat 64 8)))), (Ty.ptr, (Operand.reg "%d.i"))]
    ],
    term := Term.br "cleanup474.i" },
{ name := "if.else.i",
    instrs := [

    ],
    term := Term.br "NodeBlock83" },
{ name := "NodeBlock83",
    instrs := [
      Instr.icmp "%Pivot84" IPred.slt 8 (Operand.reg "%41") (Operand.imm (.int 8 (BitVec.ofNat 8 110)))
    ],
    term := Term.condbr (Operand.reg "%Pivot84") "LeafBlock75" "NodeBlock81" },
{ name := "NodeBlock81",
    instrs := [
      Instr.icmp "%Pivot82" IPred.slt 8 (Operand.reg "%41") (Operand.imm (.int 8 (BitVec.ofNat 8 116)))
    ],
    term := Term.condbr (Operand.reg "%Pivot82") "LeafBlock77" "LeafBlock79" },
{ name := "LeafBlock79",
    instrs := [
      Instr.icmp "%SwitchLeaf80" IPred.eq 8 (Operand.reg "%41") (Operand.imm (.int 8 (BitVec.ofNat 8 116)))
    ],
    term := Term.condbr (Operand.reg "%SwitchLeaf80") "if.end48.i" "if.else43.i" },
{ name := "LeafBlock77",
    instrs := [
      Instr.icmp "%SwitchLeaf78" IPred.eq 8 (Operand.reg "%41") (Operand.imm (.int 8 (BitVec.ofNat 8 110)))
    ],
    term := Term.condbr (Operand.reg "%SwitchLeaf78") "if.then42.i" "if.else43.i" },
{ name := "LeafBlock75",
    instrs := [
      Instr.icmp "%SwitchLeaf76" IPred.eq 8 (Operand.reg "%41") (Operand.imm (.int 8 (BitVec.ofNat 8 102)))
    ],
    term := Term.condbr (Operand.reg "%SwitchLeaf76") "if.then37.i" "if.else43.i" },
{ name := "if.then37.i",
    instrs := [

    ],
    term := Term.br "if.end48.i" },
{ name := "if.then42.i",
    instrs := [

    ],
    term := Term.br "if.end48.i" },
{ name := "if.else43.i",
    instrs := [
      Instr.gep "%off1.i129.i" (Ty.int 8) (Operand.reg "%e") (Operand.imm (.int 64 (BitVec.ofNat 64 8))),
      Instr.store (Ty.int 64) (Operand.reg "%idxprom.i") (Operand.reg "%off1.i129.i")
    ],
    term := Term.br "cleanup474.i" },
{ name := "if.end48.i",
    instrs := [
      Instr.phi "%lit.0.i" Ty.ptr [("if.then37.i", (Operand.imm .null)), ("if.then42.i", (Operand.imm .null)), ("LeafBlock79", (Operand.imm .null))],
      Instr.phi "%ln.0.i" (Ty.int 64) [("if.then37.i", (Operand.imm (.int 64 (BitVec.ofNat 64 5)))), ("if.then42.i", (Operand.imm (.int 64 (BitVec.ofNat 64 4)))), ("LeafBlock79", (Operand.imm (.int 64 (BitVec.ofNat 64 4))))],
      Instr.binop "%sub54.i" BinOp.sub 64 (Operand.reg "%ee.0.lcssa.i") (Operand.reg "%idxprom.i"),
      Instr.icmp "%cond.i.i.min" IPred.ult 64 (Operand.reg "%sub54.i") (Operand.reg "%ln.0.i"),
      Instr.select "%cond.i.i" (Ty.int 64) (Operand.reg "%cond.i.i.min") (Operand.reg "%sub54.i") (Operand.reg "%ln.0.i"),
      Instr.icmp "%cmp3.not28.not.i.i" IPred.eq 64 (Operand.reg "%ee.0.lcssa.i") (Operand.reg "%idxprom.i")
    ],
    term := Term.condbr (Operand.reg "%cmp3.not28.not.i.i") "for.end.i.i" "for.body.i.i" },
{ name := "for.body.i.i",
    instrs := [
      Instr.phi "%i.029.i.i" (Ty.int 64) [("for.inc.i.i", (Operand.reg "%inc.i.i")), ("if.end48.i", (Operand.imm (.int 64 (BitVec.ofNat 64 0))))],
      Instr.gep "%arrayidx.i.i" (Ty.int 8) (Operand.reg "%arrayidx10.i") (Operand.reg "%i.029.i.i"),
      Instr.load "%44" (Ty.int 8) (Operand.reg "%arrayidx.i.i"),
      Instr.gep "%arrayidx6.i.i" (Ty.int 8) (Operand.reg "%lit.0.i") (Operand.reg "%i.029.i.i"),
      Instr.load "%45" (Ty.int 8) (Operand.reg "%arrayidx6.i.i"),
      Instr.icmp "%cmp8.not.i.i" IPred.eq 8 (Operand.reg "%44") (Operand.reg "%45")
    ],
    term := Term.condbr (Operand.reg "%cmp8.not.i.i") "for.inc.i.i" "if.then57.i" },
{ name := "for.inc.i.i",
    instrs := [
      Instr.binop "%inc.i.i" BinOp.add 64 (Operand.reg "%i.029.i.i") (Operand.imm (.int 64 (BitVec.ofNat 64 1))),
      Instr.icmp "%exitcond.not.i.i" IPred.eq 64 (Operand.reg "%inc.i.i") (Operand.reg "%cond.i.i")
    ],
    term := Term.condbr (Operand.reg "%exitcond.not.i.i") "for.end.i.i" "for.body.i.i" },
{ name := "for.end.i.i",
    instrs := [
      Instr.icmp "%cmp11.not.i.i" IPred.eq 64 (Operand.reg "%sub54.i") (Operand.reg "%ln.0.i")
    ],
    term := Term.condbr (Operand.reg "%cmp11.not.i.i") "if.end67.i" "if.then57.i" },
{ name := "if.then57.i",
    instrs := [
      Instr.phi "%ei49.0.ph.i" (Ty.int 64) [("for.end.i.i", (Operand.reg "%cond.i.i")), ("for.body.i.i", (Operand.reg "%i.029.i.i"))],
      Instr.binop "%add60.i" BinOp.add 64 (Operand.reg "%ei49.0.ph.i") (Operand.reg "%idxprom.i"),
      Instr.gep "%off1.i131.i" (Ty.int 8) (Operand.reg "%e") (Operand.imm (.int 64 (BitVec.ofNat 64 8))),
      Instr.store (Ty.int 64) (Operand.reg "%add60.i") (Operand.reg "%off1.i131.i")
    ],
    term := Term.br "cleanup474.i" },
{ name := "if.end67.critedge.i",
    instrs := [
      Instr.callVoid "llvm.lifetime.end.p0" [((Ty.int 64), (Operand.imm (.int 64 (BitVec.ofNat 64 8)))), (Ty.ptr, (Operand.reg "%ei.i"))],
      Instr.callVoid "llvm.lifetime.end.p0" [((Ty.int 64), (Operand.imm (.int 64 (BitVec.ofNat 64 8)))), (Ty.ptr, (Operand.reg "%d.i"))]
    ],
    term := Term.br "if.end67.i" },
{ name := "if.end67.i",
    instrs := [
      Instr.icmp "%cmp6919.i" IPred.ult 64 (Operand.reg "%ee.0.lcssa.i") (Operand.reg "%cond.i")
    ],
    term := Term.condbr (Operand.reg "%cmp6919.i") "land.rhs71.i" "while.end78.i" },
{ name := "land.rhs71.i",
    instrs := [
      Instr.phi "%s2.020.i" (Ty.int 64) [("while.body76.i", (Operand.reg "%inc77.i")), ("if.end67.i", (Operand.reg "%ee.0.lcssa.i"))],
      Instr.gep "%arrayidx72.i" (Ty.int 8) (Operand.reg "%3") (Operand.reg "%s2.020.i"),
      Instr.load "%46" (Ty.int 8) (Operand.reg "%arrayidx72.i")
    ],
    term := Term.br "NodeBlock94" },
{ name := "NodeBlock94",
    instrs := [
      Instr.icmp "%Pivot95" IPred.slt 8 (Operand.reg "%46") (Operand.imm (.int 8 (BitVec.ofNat 8 13)))
    ],
    term := Term.condbr (Operand.reg "%Pivot95") "LeafBlock85" "NodeBlock92" },
{ name := "NodeBlock92",
    instrs := [
      Instr.icmp "%Pivot93" IPred.slt 8 (Operand.reg "%46") (Operand.imm (.int 8 (BitVec.ofNat 8 32)))
    ],
    term := Term.condbr (Operand.reg "%Pivot93") "LeafBlock88" "LeafBlock90" },
{ name := "LeafBlock90",
    instrs := [
      Instr.icmp "%SwitchLeaf91" IPred.eq 8 (Operand.reg "%46") (Operand.imm (.int 8 (BitVec.ofNat 8 32)))
    ],
    term := Term.condbr (Operand.reg "%SwitchLeaf91") "while.body76.i" "while.end78.i" },
{ name := "LeafBlock88",
    instrs := [
      Instr.icmp "%SwitchLeaf89" IPred.eq 8 (Operand.reg "%46") (Operand.imm (.int 8 (BitVec.ofNat 8 13)))
    ],
    term := Term.condbr (Operand.reg "%SwitchLeaf89") "while.body76.i" "while.end78.i" },
{ name := "LeafBlock85",
    instrs := [
      Instr.binop "%.off86" BinOp.add 8 (Operand.reg "%46") (Operand.imm (.int 8 (BitVec.ofNat 8 247))),
      Instr.icmp "%SwitchLeaf87" IPred.ule 8 (Operand.reg "%.off86") (Operand.imm (.int 8 (BitVec.ofNat 8 1)))
    ],
    term := Term.condbr (Operand.reg "%SwitchLeaf87") "while.body76.i" "while.end78.i" },
{ name := "while.body76.i",
    instrs := [
      Instr.binop "%inc77.i" BinOp.add 64 (Operand.reg "%s2.020.i") (Operand.imm (.int 64 (BitVec.ofNat 64 1))),
      Instr.icmp "%exitcond24.not.i" IPred.eq 64 (Operand.reg "%inc77.i") (Operand.reg "%cond.i")
    ],
    term := Term.condbr (Operand.reg "%exitcond24.not.i") "while.end78.i" "land.rhs71.i" },
{ name := "while.end78.i",
    instrs := [
      Instr.phi "%s2.0.lcssa.i" (Ty.int 64) [("if.end67.i", (Operand.reg "%ee.0.lcssa.i")), ("while.body76.i", (Operand.reg "%cond.i")), ("LeafBlock85", (Operand.reg "%s2.020.i")), ("LeafBlock88", (Operand.reg "%s2.020.i")), ("LeafBlock90", (Operand.reg "%s2.020.i"))],
      Instr.gep "%off1.i137.i" (Ty.int 8) (Operand.reg "%e") (Operand.imm (.int 64 (BitVec.ofNat 64 8))),
      Instr.store (Ty.int 64) (Operand.reg "%s2.0.lcssa.i") (Operand.reg "%off1.i137.i")
    ],
    term := Term.br "cleanup474.i" },
{ name := "if.then447.i",
    instrs := [
      Instr.callVoid "s2_after_value" [((Ty.int 32), (Operand.reg "%sp.i.0248")), (Ty.ptr, (Operand.reg "%root_done.i")), (Ty.ptr, (Operand.reg "%ctype.i")), (Ty.ptr, (Operand.reg "%cst.i"))],
      Instr.icmp "%cmp451.i" IPred.ult 64 (Operand.reg "%ee.1.i") (Operand.reg "%cond350.i")
    ],
    term := Term.condbr (Operand.reg "%cmp451.i") "land.rhs457.i" "if.end473.i" },
{ name := "land.rhs457.i",
    instrs := [
      Instr.phi "%q.0.i246" (Ty.int 64) [("while.body462.i", (Operand.reg "%inc463.i")), ("if.then447.i", (Operand.reg "%ee.1.i"))],
      Instr.gep "%arrayidx458.i" (Ty.int 8) (Operand.reg "%3") (Operand.reg "%q.0.i246"),
      Instr.load "%47" (Ty.int 8) (Operand.reg "%arrayidx458.i")
    ],
    term := Term.br "NodeBlock105" },
{ name := "NodeBlock105",
    instrs := [
      Instr.icmp "%Pivot106" IPred.slt 8 (Operand.reg "%47") (Operand.imm (.int 8 (BitVec.ofNat 8 13)))
    ],
    term := Term.condbr (Operand.reg "%Pivot106") "LeafBlock96" "NodeBlock103" },
{ name := "NodeBlock103",
    instrs := [
      Instr.icmp "%Pivot104" IPred.slt 8 (Operand.reg "%47") (Operand.imm (.int 8 (BitVec.ofNat 8 32)))
    ],
    term := Term.condbr (Operand.reg "%Pivot104") "LeafBlock99" "LeafBlock101" },
{ name := "LeafBlock101",
    instrs := [
      Instr.icmp "%SwitchLeaf102" IPred.eq 8 (Operand.reg "%47") (Operand.imm (.int 8 (BitVec.ofNat 8 32)))
    ],
    term := Term.condbr (Operand.reg "%SwitchLeaf102") "while.body462.i" "if.then467.i" },
{ name := "LeafBlock99",
    instrs := [
      Instr.icmp "%SwitchLeaf100" IPred.eq 8 (Operand.reg "%47") (Operand.imm (.int 8 (BitVec.ofNat 8 13)))
    ],
    term := Term.condbr (Operand.reg "%SwitchLeaf100") "while.body462.i" "if.then467.i" },
{ name := "LeafBlock96",
    instrs := [
      Instr.binop "%.off97" BinOp.add 8 (Operand.reg "%47") (Operand.imm (.int 8 (BitVec.ofNat 8 247))),
      Instr.icmp "%SwitchLeaf98" IPred.ule 8 (Operand.reg "%.off97") (Operand.imm (.int 8 (BitVec.ofNat 8 1)))
    ],
    term := Term.condbr (Operand.reg "%SwitchLeaf98") "while.body462.i" "if.then467.i" },
{ name := "while.body462.i",
    instrs := [
      Instr.binop "%inc463.i" BinOp.add 64 (Operand.reg "%q.0.i246") (Operand.imm (.int 64 (BitVec.ofNat 64 1))),
      Instr.icmp "%exitcond298.not" IPred.eq 64 (Operand.reg "%inc463.i") (Operand.reg "%cond350.i")
    ],
    term := Term.condbr (Operand.reg "%exitcond298.not") "if.end473.i" "land.rhs457.i" },
{ name := "if.then467.i",
    instrs := [
      Instr.gep "%off1.i.i113" (Ty.int 8) (Operand.reg "%e") (Operand.imm (.int 64 (BitVec.ofNat 64 8))),
      Instr.store (Ty.int 64) (Operand.reg "%q.0.i246") (Operand.reg "%off1.i.i113")
    ],
    term := Term.br "cleanup474.i" },
{ name := "if.end473.i",
    instrs := [
      Instr.callVoid "llvm.lifetime.end.p0" [((Ty.int 64), (Operand.imm (.int 64 (BitVec.ofNat 64 24)))), (Ty.ptr, (Operand.reg "%t352.i"))]
    ],
    term := Term.br "cleanup478.i" },
{ name := "cleanup474.i",
    instrs := [
      Instr.callVoid "llvm.lifetime.end.p0" [((Ty.int 64), (Operand.imm (.int 64 (BitVec.ofNat 64 24)))), (Ty.ptr, (Operand.reg "%t352.i"))]
    ],
    term := Term.br "if.then" },
{ name := "cleanup478.i",
    instrs := [
      Instr.phi "%sp.i.1" (Ty.int 32) [("if.end473.i", (Operand.reg "%sp.i.0248")), ("if.end150.i", (Operand.reg "%sp.i.0248")), ("if.end162.i", (Operand.reg "%sp.i.0248")), ("if.end195.i", (Operand.reg "%sp.i.0248")), ("if.else334.i", (Operand.reg "%sp.i.0248")), ("if.then330.i", (Operand.reg "%sp.i.0248")), ("if.then.i.i", (Operand.reg "%inc33.i")), ("out_reserve.exit.i.i", (Operand.reg "%inc33.i")), ("if.then.i.i50", (Operand.reg "%sub.i")), ("out_reserve.exit.i.i60", (Operand.reg "%sub.i"))],
      Instr.phi "%k.2.i" (Ty.int 64) [("if.end473.i", (Operand.reg "%inc.i")), ("if.end150.i", (Operand.reg "%inc.i")), ("if.end162.i", (Operand.reg "%inc.i")), ("if.end195.i", (Operand.reg "%inc.i")), ("if.else334.i", (Operand.reg "%inc208.i")), ("if.then330.i", (Operand.reg "%inc208.i")), ("if.then.i.i", (Operand.reg "%inc.i")), ("out_reserve.exit.i.i", (Operand.reg "%inc.i")), ("if.then.i.i50", (Operand.reg "%inc.i")), ("out_reserve.exit.i.i60", (Operand.reg "%inc.i"))],
      Instr.icmp "%cmp.i" IPred.ult 64 (Operand.reg "%k.2.i") (Operand.reg "%nep")
    ],
    term := Term.condbr (Operand.reg "%cmp.i") "while.body.i" "if.then485.i" },
{ name := "if.then485.i",
    instrs := [
      Instr.icmp "%48" IPred.eq 32 (Operand.reg "%sp.i.1") (Operand.imm (.int 32 (BitVec.ofNat 32 0)))
    ],
    term := Term.condbr (Operand.reg "%48") "if.end490.i" "if.then488.i" },
{ name := "if.then488.i",
    instrs := [
      Instr.gep "%off1.i.i115" (Ty.int 8) (Operand.reg "%e") (Operand.imm (.int 64 (BitVec.ofNat 64 8))),
      Instr.store (Ty.int 64) (Operand.reg "%4") (Operand.reg "%off1.i.i115")
    ],
    term := Term.br "if.then" },
{ name := "if.end490.i",
    instrs := [
      Instr.load "%.pr" (Ty.int 32) (Operand.reg "%root_done.i"),
      Instr.icmp "%tobool491.not.i" IPred.eq 32 (Operand.reg "%.pr") (Operand.imm (.int 32 (BitVec.ofNat 32 0)))
    ],
    term := Term.condbr (Operand.reg "%tobool491.not.i") "if.then492.i" "s2_walk.exit" },
{ name := "if.then492.i",
    instrs := [
      Instr.gep "%off1.i.i117" (Ty.int 8) (Operand.reg "%e") (Operand.imm (.int 64 (BitVec.ofNat 64 8))),
      Instr.store (Ty.int 64) (Operand.reg "%4") (Operand.reg "%off1.i.i117")
    ],
    term := Term.br "if.then" },
{ name := "s2_walk.exit",
    instrs := [
      Instr.callVoid "llvm.lifetime.end.p0" [((Ty.int 64), (Operand.imm (.int 64 (BitVec.ofNat 64 8)))), (Ty.ptr, (Operand.reg "%xj.i"))],
      Instr.callVoid "llvm.lifetime.end.p0" [((Ty.int 64), (Operand.imm (.int 64 (BitVec.ofNat 64 4)))), (Ty.ptr, (Operand.reg "%root_done.i"))],
      Instr.callVoid "llvm.lifetime.end.p0" [((Ty.int 64), (Operand.imm (.int 64 (BitVec.ofNat 64 520)))), (Ty.ptr, (Operand.reg "%cst.i"))],
      Instr.callVoid "llvm.lifetime.end.p0" [((Ty.int 64), (Operand.imm (.int 64 (BitVec.ofNat 64 520)))), (Ty.ptr, (Operand.reg "%ctype.i"))],
      Instr.callVoid "llvm.lifetime.end.p0" [((Ty.int 64), (Operand.imm (.int 64 (BitVec.ofNat 64 1192)))), (Ty.ptr, (Operand.reg "%c.i"))],
      Instr.load "%49" (Ty.int 64) (Operand.reg "%alen"),
      Instr.store (Ty.int 64) (Operand.reg "%49") (Operand.reg "%ndst"),
      Instr.load "%50" (Ty.int 64) (Operand.reg "%len"),
      Instr.store (Ty.int 64) (Operand.reg "%50") (Operand.reg "%nev")
    ],
    term := Term.br "if.end" },
{ name := "if.then",
    instrs := [
      Instr.callVoid "llvm.lifetime.end.p0" [((Ty.int 64), (Operand.imm (.int 64 (BitVec.ofNat 64 8)))), (Ty.ptr, (Operand.reg "%xj.i"))],
      Instr.callVoid "llvm.lifetime.end.p0" [((Ty.int 64), (Operand.imm (.int 64 (BitVec.ofNat 64 4)))), (Ty.ptr, (Operand.reg "%root_done.i"))],
      Instr.callVoid "llvm.lifetime.end.p0" [((Ty.int 64), (Operand.imm (.int 64 (BitVec.ofNat 64 520)))), (Ty.ptr, (Operand.reg "%cst.i"))],
      Instr.callVoid "llvm.lifetime.end.p0" [((Ty.int 64), (Operand.imm (.int 64 (BitVec.ofNat 64 520)))), (Ty.ptr, (Operand.reg "%ctype.i"))],
      Instr.callVoid "llvm.lifetime.end.p0" [((Ty.int 64), (Operand.imm (.int 64 (BitVec.ofNat 64 1192)))), (Ty.ptr, (Operand.reg "%c.i"))],
      Instr.load "%51" (Ty.int 64) (Operand.reg "%alen"),
      Instr.store (Ty.int 64) (Operand.reg "%51") (Operand.reg "%ndst"),
      Instr.load "%52" (Ty.int 64) (Operand.reg "%len"),
      Instr.store (Ty.int 64) (Operand.reg "%52") (Operand.reg "%nev"),
      Instr.gep "%off" (Ty.int 8) (Operand.reg "%e") (Operand.imm (.int 64 (BitVec.ofNat 64 8))),
      Instr.load "%53" (Ty.int 64) (Operand.reg "%off"),
      Instr.store (Ty.int 64) (Operand.reg "%53") (Operand.reg "%err")
    ],
    term := Term.br "if.end" },
{ name := "if.end",
    instrs := [
      Instr.phi "%tobool.not151" (Ty.int 64) [("if.then", (Operand.imm (.int 64 (BitVec.ofNat 64 0)))), ("s2_walk.exit", (Operand.imm (.int 64 (BitVec.ofNat 64 1))))],
      Instr.callVoid "llvm.lifetime.end.p0" [((Ty.int 64), (Operand.imm (.int 64 (BitVec.ofNat 64 24)))), (Ty.ptr, (Operand.reg "%e"))],
      Instr.callVoid "llvm.lifetime.end.p0" [((Ty.int 64), (Operand.imm (.int 64 (BitVec.ofNat 64 64)))), (Ty.ptr, (Operand.reg "%z"))],
      Instr.callVoid "llvm.lifetime.end.p0" [((Ty.int 64), (Operand.imm (.int 64 (BitVec.ofNat 64 120)))), (Ty.ptr, (Operand.reg "%s"))]
    ],
    term := Term.ret (Ty.int 64) (some (Operand.reg "%tobool.not151")) }] }

/-! ### The pin's guards -/

-- The literal above is the parsed fixture, and the fixture is the parsed literal.
#guard decide (firstFunction stage2Src = some stage2Body)
#guard decide (parsedFunctions stage2Src = some [stage2Body])
#guard decide (parsedDeclCount stage2Src = some 10)

-- The pin bites: the same text with one immediate changed still parses, and it is
-- not the pinned body.
/-- `s` with the first occurrence of `pat` replaced by `rep`; `s` unchanged when
there is none. -/
def replaceFirst (s pat rep : String) : String :=
  match s.splitOn pat with
  | a :: b :: rest => a ++ rep ++ String.intercalate pat (b :: rest)
  | _ => s

/-- The immediate the mutation writes: the walk's `(n + 63) >> 6` sizes the entry
stream's block count, so a body carrying `64` is a different body. -/
def stage2Mutant : String := "%add = add i64 %n, 64"

/-- The pinned text with that one immediate changed. -/
def stage2SrcMutated : String :=
  replaceFirst stage2Src "%add = add i64 %n, 63" stage2Mutant

-- The needle occurs exactly once, so the mutation is one instruction.
#guard (stage2Src.splitOn "%add = add i64 %n, 63").length = 2
#guard stage2SrcMutated ≠ stage2Src
#guard (match parseModule stage2SrcMutated with | .ok _ => true | .error _ => false)
#guard decide (firstFunction stage2SrcMutated ≠ some stage2Body)

/-! ### The ABI prefix and the staging suffix

`stage2.h`'s thirteen slots are the body's first thirteen parameters, in the ABI's
order; the eight objects the flattening moved out of the body follow them.  The
pin records both lists, because a change to either is a change to the interface
`Γ_stage2at` maps. -/

/-- `stage2.h`'s thirteen slots, name and type, in order. -/
def stage2Abi13 : List (String × Ty) :=
  [("%b", .ptr), ("%n", .int 64), ("%ep", .ptr), ("%nep", .int 64),
   ("%xp", .ptr), ("%nxp", .int 64), ("%dst", .ptr), ("%dstcap", .int 64),
   ("%ndst", .ptr), ("%ev", .ptr), ("%evcap", .int 64), ("%nev", .ptr),
   ("%err", .ptr)]

/-- The eight staging objects the flattening appends, in the emission's order
(`stage2.staging.tsv`): the number path's output slot, the cursor record, the two
container stacks, the scalar token, and the walk's own three records. -/
def stage2Staging8 : List (String × Ty) :=
  [("%d.i", .ptr), ("%c.i", .ptr), ("%ctype.i", .ptr), ("%cst.i", .ptr),
   ("%t352.i", .ptr), ("%s", .ptr), ("%z", .ptr), ("%e", .ptr)]

#guard decide (stage2Body.params = stage2Abi13 ++ stage2Staging8)
#guard decide (stage2Body.retTy = Ty.int 64)
#guard decide (stage2Body.name = "leanllvm_json_stage2")

/-! ### The census -/

/-- The call targets the pinned body names, in text order. -/
def callTargets (f : Function) : List String :=
  (f.blocks.flatMap (·.instrs)).filterMap fun i =>
    match i with
    | .call _ _ callee _ => some callee
    | .callVoid callee _ => some callee
    | _ => none

/-- How often the body calls `sym`. -/
def callCount (f : Function) (sym : String) : Nat := (callTargets f).count sym

/-- The unit's own sub-units: the symbols whose bodies are outside this fixture and
whose contracts are `stage2Calls`'s parameter. -/
def stage2SubUnits : List String :=
  ["num_fast_el1", "od_scalar_value", "s2_after_value", "s2_init",
   "s2_string_body", "s2_value_pos"]

/-- The symbols `stage2Calls` resolves itself: the two lifetime markers and the
walk's two `memset`s, plus the trap, which has no defined outcome. -/
def stage2Resolved : List String :=
  ["llvm.lifetime.end.p0", "llvm.lifetime.start.p0", "llvm.memset.p0.i64",
   "llvm.trap"]

-- The census is closed: the body calls exactly these ten symbols, and no other.
#guard
  decide (((callTargets stage2Body).mergeSort (fun a b => a ≤ b)).eraseDups =
    ["llvm.lifetime.end.p0", "llvm.lifetime.start.p0", "llvm.memset.p0.i64",
     "llvm.trap", "num_fast_el1", "od_scalar_value", "s2_after_value",
     "s2_init", "s2_string_body", "s2_value_pos"])

-- And the multiset is the emission's: the walk's zeroing and its live-range
-- markers are what the counts say, and each sub-unit is called once per entry
-- or once per body.
#guard callCount stage2Body "llvm.lifetime.end.p0" = 21
#guard callCount stage2Body "llvm.lifetime.start.p0" = 12
#guard callCount stage2Body "llvm.memset.p0.i64" = 2
#guard callCount stage2Body "llvm.trap" = 4
#guard callCount stage2Body "num_fast_el1" = 1
#guard callCount stage2Body "od_scalar_value" = 1
#guard callCount stage2Body "s2_after_value" = 3
#guard callCount stage2Body "s2_init" = 1
#guard callCount stage2Body "s2_string_body" = 1
#guard callCount stage2Body "s2_value_pos" = 3

/-! ### The structural facts `Satisfies` consumes

A body whose `ret` carries no value cannot be related to a call outcome, so
`retsValued` is a precondition of the bridge below; the aggregate-alloca and
`ret`-count facts are what the run's shape rests on. -/

/-- Every instruction's `alloca` type, in text order. -/
def allocaTypes (f : Function) : List Ty :=
  (f.blocks.flatMap (·.instrs)).filterMap fun i =>
    match i with
    | .alloca _ ty _ => some ty
    | _ => none

/-- The number of blocks that end in a `ret`. -/
def retCount (f : Function) : Nat :=
  (f.blocks.filter fun b => match b.term with
    | .ret _ _ => true
    | _ => false).length

/-- The `llvm.lifetime.start` extents a body declares, as the register and the
byte count it allocates.  The stage-2 record names the seven appended objects at
these extents (`stage2StagedWrites`), so this is the instrument that keeps the
record's numbers the body's: a fixture that resized an object fails the
`#guard`s below at elaboration. -/
def lifetimeExtents (f : Function) : List (String × Nat) :=
  (f.blocks.flatMap (·.instrs)).filterMap fun i =>
    match i with
    | .callVoid "llvm.lifetime.start.p0"
        [(Ty.int 64, Operand.imm (.int 64 s)), (Ty.ptr, Operand.reg r)] =>
        some (r, s.toNat)
    | _ => none

#guard decide (stage2Body.blocks.length = 165)
#guard decide ((stage2Body.blocks.flatMap (·.instrs)).length = 441)
#guard decide (allocaTypes stage2Body = [Ty.int 64, Ty.int 32, Ty.int 64, Ty.int 64])
#guard retCount stage2Body = 1
#guard retsValued stage2Body

-- The seven appended objects the walk writes are allocated for exactly the
-- extents `stage2StagedWrites` names.  Each is the body's own `lifetime.start`,
-- so a fixture that resized one of them fails here rather than leaving the
-- record describing an object the body no longer has.
#guard (lifetimeExtents stage2Body).lookup "%c.i" == some stage2CursorExtent
#guard (lifetimeExtents stage2Body).lookup "%ctype.i" == some stage2StackExtent
#guard (lifetimeExtents stage2Body).lookup "%cst.i" == some stage2StackExtent
#guard (lifetimeExtents stage2Body).lookup "%t352.i" == some stage2TokenExtent
#guard (lifetimeExtents stage2Body).lookup "%s" == some stage2StateExtent
#guard (lifetimeExtents stage2Body).lookup "%z" == some stage2LogExtent
#guard (lifetimeExtents stage2Body).lookup "%e" == some stage2ErrorExtent

/-- **The pinned body returns a value at every `ret`.**  The bridge to a call site
needs it, and reading it off the pinned AST rather than asserting it is the
point of pinning the AST. -/
theorem stage2Body_retsValued : retsValued stage2Body = true := by decide

/-- **The pinned body allocates only scalars.**  The flattening removed every
aggregate `alloca`, so no allocation in the fixture moves the cursor by a
computed size. -/
theorem stage2Body_allocaTypes :
    allocaTypes stage2Body = [Ty.int 64, Ty.int 32, Ty.int 64, Ty.int 64] := by
  decide

/-! ### The guards the body keeps

The walk's own guards are body text.  A fixture that had removed one would pin a
different program, so the pin asserts they are there: the arena reserve's slack
add and the event stream's thirteen-byte add, and the four trap arms. -/

/-- Whether the body adds the immediate `v` at width `w` somewhere. -/
def hasAddImm (f : Function) (w v : Nat) : Bool :=
  (f.blocks.flatMap (·.instrs)).any fun i =>
    match i with
    | .binop _ .add w' _ (.imm (.int w'' v')) => w' == w && w'' == w && v'.toNat == v
    | _ => false

#guard hasAddImm stage2Body 64 64     -- `US_SLACK`, the arena's reserve slack
#guard hasAddImm stage2Body 64 13     -- the event record's thirteen bytes
#guard callCount stage2Body "llvm.trap" = 4
#guard (callTargets stage2Body).count "llvm.memset.p0.i64" = 2

-- The six symbols that fall through to the sub-unit selection, in the body's own
-- first-call order.  `stage2Calls` resolves the lifetime markers, the two
-- `memset`s and the trap; everything else is the parameter `sub`.  So the body's
-- completion depends on `sub` at exactly these six and no others — which is why
-- `Stage2WalkObligation` is not a statement about the pinned text alone.
#guard (callTargets stage2Body).eraseDups.filter (fun s =>
    s != "llvm.lifetime.start.p0" && s != "llvm.lifetime.end.p0" &&
    s != "llvm.memset.p0.i64" && s != "llvm.trap") =
  ["s2_init", "s2_value_pos", "s2_after_value", "s2_string_body",
   "od_scalar_value", "num_fast_el1"]

/-! ### The call environment

The body calls ten symbols.  Four are resolved here — the lifetime markers, the
two `memset`s and the trap — and six are the unit's own sub-units, whose bodies
the fixture does not hold and whose contracts are the parameter `sub`.  The
census guards above are what make "the body calls nothing else" true of the
pinned AST rather than of a reading of the source.

`llvm.trap` answers `none`, which the semantics reads as `ub`: the trap arms are
the reserve checks' fault exits, and `Γ_stage2.pre` is what puts them out of
reach.  A selection that answered a value there would claim the reserves can
fail. -/

/-- The stage-2 walk's call environment at the sub-unit selection `sub`. -/
def stage2Calls (sub : Calls) : Calls :=
  fun callee args mem next =>
    match callee with
    | "llvm.lifetime.start.p0" | "llvm.lifetime.end.p0" =>
        -- a live-range marker: no value read, no byte written, no allocation
        some { ret := .int 1 0, mem := mem, next := next }
    | "llvm.memset.p0.i64" =>
        -- `memset(p, 0, n)`: the bytes, and nothing else
        match args with
        | [.ptr p, .int 8 _, .int 64 n, .int 1 _] =>
            some { ret := .int 1 0,
                   mem := writeBytes mem p (List.replicate n.toNat (0 : UInt8)),
                   next := next }
        | _ => none
    | "llvm.trap" => none
    | _ => sub callee args mem next

/-- A lifetime marker writes nothing and allocates nothing. -/
theorem stage2Calls_lifetime {sub : Calls} {mem : Mem} {next : Nat} {sym : String}
    (h : sym = "llvm.lifetime.start.p0" ∨ sym = "llvm.lifetime.end.p0") :
    ∃ out, stage2Calls sub sym [] mem next = some out ∧ out.mem = mem ∧
      out.next = next := by
  rcases h with rfl | rfl
  · exact ⟨_, rfl, rfl, rfl⟩
  · exact ⟨_, rfl, rfl, rfl⟩

/-- The trap's selection is the semantics' `ub`, not a value: the reserve checks'
fault arms are the only calls of it. -/
theorem stage2Calls_trap {sub : Calls} {args : List Value} {mem : Mem} {next : Nat} :
    stage2Calls sub "llvm.trap" args mem next = none := rfl

/-! ### The re-indexing adapter

`stage2.h` declares thirteen slots; the pinned body takes twenty-one.  The adapter
is a definition, not a step: `stage2Args` appends the eight staging objects, and
`Γ_stage2at` reads the record's budget and post at the thirteen-slot prefix.  The
eight objects' staging **is** a clause of the adapter (`stage2StagedPre`), because
seven of them are written by the body: `%c.i`'s `k` field is the loop's first
store (`while.body.i`), so a record that left them unstaged would contradict its
own ownership claim one step in.  The thirteen-argument ABI cannot name them, so
the adapter is the only place the staging can say it. -/

/-- The eight staging objects, as the addresses the body receives. -/
def stage2StagingArgs (d c ctype cst tok s z e : Nat) : List Value :=
  [.ptr d, .ptr c, .ptr ctype, .ptr cst, .ptr tok, .ptr s, .ptr z, .ptr e]

/-- `stage2.h`'s thirteen arguments followed by the eight the flattening appends. -/
def stage2Args (a13 : List Value) (d c ctype cst tok s z e : Nat) : List Value :=
  a13 ++ stage2StagingArgs d c ctype cst tok s z e

/-- The record at the flattened body: the budget and the post read at the
thirteen-slot prefix, and the precondition holds when the arguments are the ABI's
followed by the eight staging objects **and those objects are staged**.  Seven of
the eight are written by the body — `%c.i`'s `k` field is the loop's first store —
so the adapter cannot leave their staging unstated: `stage2StagedPre` gives
presence at each of the seven extents and the separation of every staged object
from every other, which is what the loop's region claim needs and what
`Γ_stage2.pre`, at thirteen arguments, has no way to name.

The two count slots are parameters for the same reason the eight are: the ABI
does not carry them and both sides of their separation have to be nameable
somewhere.  They are not presence clauses — the pipeline's own staging reads both
words — but the two entries that put them in the staged list, so that the walk's
seven write extents are separated from the caller's `%nk` and `%nxp` rather than
only from the thirteen ABI objects. -/
def Γ_stage2at (d c ctype cst tok s z e nkSlot nxpSlot : Nat) : MemContract where
  budget := fun args mem => Γ_stage2.budget (args.take 13) mem
  pre := fun args mem next =>
    ∃ a13, args = stage2Args a13 d c ctype cst tok s z e ∧
      Γ_stage2.pre a13 mem next ∧
      stage2StagedPre a13 mem c ctype cst tok s z e nkSlot nxpSlot
  post := fun args mem next o => Γ_stage2.post (args.take 13) mem next o

/-- The adapter's prefix is the ABI's argument list. -/
theorem stage2Args_take13 (a13 : List Value) (h : a13.length = 13)
    (d c ctype cst tok s z e : Nat) :
    (stage2Args a13 d c ctype cst tok s z e).take 13 = a13 := by
  simp [stage2Args, stage2StagingArgs, h]

/-- **The record's precondition is the adapter's, and it constrains the eight
appended objects.**  A caller whose thirteen arguments are in `Γ_stage2.pre` is in
`Γ_stage2at.pre` at the appended form once the seven the walk writes are staged at
their extents and every staged object is separate from every other.  That second
hypothesis is not optional: `Γ_stage2.pre` names thirteen objects and the body
writes seven more, so the adapter is the only place the staging can say it. -/
theorem Γ_stage2at_pre {a13 : List Value} {mem : Mem} {next : Nat}
    {d c ctype cst tok s z e nkSlot nxpSlot : Nat} (h : Γ_stage2.pre a13 mem next)
    (hstaged : stage2StagedPre a13 mem c ctype cst tok s z e nkSlot nxpSlot) :
    (Γ_stage2at d c ctype cst tok s z e nkSlot nxpSlot).pre
      (stage2Args a13 d c ctype cst tok s z e) mem next :=
  ⟨a13, rfl, h, hstaged⟩

/-! ### The bridge to a call site

This is the shape `JsonPipelineIR`'s stage-2 slot takes: a selection over the
thirteen-argument ABI, which runs the pinned body with the eight staging objects
appended, at the adapter's record and the walk's own call environment. -/

/-- The stage-2 selection at a staging: `envForUnit` at the pinned body, with the
adapter's arguments appended. -/
def envForStage2 (d c ctype cst tok s z e nkSlot nxpSlot : Nat) (sub : Calls) : Calls :=
  fun callee args mem next =>
    envForUnit "leanllvm_json_stage2" (Γ_stage2at d c ctype cst tok s z e nkSlot nxpSlot)
      (stage2Calls sub) stage2Body callee
      (stage2Args args d c ctype cst tok s z e) mem next

/-- The record's precondition fixes the argument list: `stage2Pre`'s first clause
is the thirteen values, so any admissible caller has thirteen of them. -/
theorem stage2Pre_length {args : List Value} {mem : Mem} {next : Nat}
    (h : Γ_stage2.pre args mem next) : args.length = 13 := by
  obtain ⟨b, n, ep, nep, xp, nxp, dst, dstcap, ndst, ev, evcap, nev, err, bs, ent,
    ndst0, nev0, hargs, -⟩ := h
  subst hargs
  rfl

/-- **The walk resolves at the record, given its obligation, its pin, and the
appended objects' staging.**  The `Satisfies` hypothesis is the walk's own
obligation at the adapter's record — the thing this slice names and does not
discharge; `retsValued` is read off the pinned AST by `stage2Body_retsValued`; and
the staging hypothesis is the caller's: at thirteen arguments the ABI cannot name
the seven objects the body writes, so the promise that they are staged is theirs'
to make and is stated once here rather than per call; it now carries the caller's
two count slots as well, which are the objects whose separation from the seven is
what lets a caller read them back after the run. -/
theorem satisfies_calls_stage2 (d c ctype cst tok s z e nkSlot nxpSlot : Nat) {sub : Calls}
    (hwalk : Satisfies (stage2Calls sub) stage2Body
      (Γ_stage2at d c ctype cst tok s z e nkSlot nxpSlot))
    (hstaged : ∀ {args : List Value} {mem : Mem} {next : Nat},
      Γ_stage2.pre args mem next →
        stage2StagedPre args mem c ctype cst tok s z e nkSlot nxpSlot) :
    CallSatisfies (envForStage2 d c ctype cst tok s z e nkSlot nxpSlot sub) Γ_stage2
      "leanllvm_json_stage2" := by
  intro args mem next hpre
  obtain ⟨r, hsome, hpost, hnext⟩ :=
    satisfies_calls (calls := stage2Calls sub) (body := stage2Body)
      (Γ := Γ_stage2at d c ctype cst tok s z e nkSlot nxpSlot) (sym := "leanllvm_json_stage2")
      hwalk stage2Body_retsValued (stage2Args args d c ctype cst tok s z e) mem next
      (Γ_stage2at_pre hpre (hstaged hpre))
  have htake : (stage2Args args d c ctype cst tok s z e).take 13 = args :=
    stage2Args_take13 args (stage2Pre_length hpre) d c ctype cst tok s z e
  exact ⟨r, by simpa [envForStage2] using hsome, by simpa [Γ_stage2at, htake] using hpost,
    hnext⟩

/-! ### The named remainder

The walk's obligation, as a proposition at the pinned body.  It is not proved
here, and the first thing that resists is its completion conjunct: a step count
at which a 165-block loop returns.  The six `Stage2Run` clauses — both cursors and
their growth bounds, the arena's reserve slack, `Owns` over the two extents, the
refusal bit, and `eoff ≤ n` — are what it owes once the run is reached, and the
two walk facts `JsonStage2Body` names (one event record per entry, and the escaped
bodies' lengths summing inside the document) are part of the same induction. -/

/-- The stage-2 walk's obligation at a staging and a sub-unit selection. -/
def Stage2WalkObligation (d c ctype cst tok s z e nkSlot nxpSlot : Nat) (sub : Calls) : Prop :=
  Satisfies (stage2Calls sub) stage2Body (Γ_stage2at d c ctype cst tok s z e nkSlot nxpSlot)

/-- **The walk's obligation yields the record's post.**  At an argument list in
`Γ_stage2.pre` whose seven appended objects are staged, the obligation at the
adapter's arguments completes the pinned body, and the outcome it reaches
satisfies `Γ_stage2`'s post at the ABI's own thirteen values: the two are one
proposition, related by `stage2Args_take13`, so a proof of the walk needs no
second statement of what it owes. -/
theorem stage2_walk_yields_record {d c ctype cst tok s z e nkSlot nxpSlot : Nat} {sub : Calls}
    (hwalk : Stage2WalkObligation d c ctype cst tok s z e nkSlot nxpSlot sub)
    {a13 : List Value} {mem : Mem} {next : Nat} (hpre : Γ_stage2.pre a13 mem next)
    (hstaged : stage2StagedPre a13 mem c ctype cst tok s z e nkSlot nxpSlot) :
    ∃ v m,
      runFuel (stage2Calls sub)
          ((Γ_stage2at d c ctype cst tok s z e nkSlot nxpSlot).budget
            (stage2Args a13 d c ctype cst tok s z e) mem)
          stage2Body
          (EntryState stage2Body (stage2Args a13 d c ctype cst tok s z e) mem next) =
        some (.ret v m) ∧
      Γ_stage2.post a13 mem next (.ret v m) := by
  obtain ⟨hcom, hpost⟩ := hwalk _ _ _ (Γ_stage2at_pre hpre hstaged)
  obtain ⟨v, m, hrun⟩ := hcom
  refine ⟨v, m, hrun, ?_⟩
  have htake : (stage2Args a13 d c ctype cst tok s z e).take 13 = a13 :=
    stage2Args_take13 a13 (stage2Pre_length hpre) d c ctype cst tok s z e
  simpa [Γ_stage2at, htake] using hpost (.ret v m) (Or.inr ⟨_, hrun⟩)

/-- The obligation's own vocabulary: a body's `Satisfies` is a completion at the
record's budget and the post of the outcome it reaches. -/
theorem Stage2WalkObligation.summary {d c ctype cst tok s z e nkSlot nxpSlot : Nat} {sub : Calls}
    (h : Stage2WalkObligation d c ctype cst tok s z e nkSlot nxpSlot sub) :
    ∀ args mem next,
      (Γ_stage2at d c ctype cst tok s z e nkSlot nxpSlot).pre args mem next →
      (∃ v m, runFuel (stage2Calls sub)
          ((Γ_stage2at d c ctype cst tok s z e nkSlot nxpSlot).budget args mem) stage2Body
          (EntryState stage2Body args mem next) = some (.ret v m)) ∧
      ∀ o, BehFromState (stage2Calls sub) stage2Body
          (EntryState stage2Body args mem next) o →
        (Γ_stage2at d c ctype cst tok s z e nkSlot nxpSlot).post args mem next o := h

end LeanLLVM.Refinement.JsonStage2IR

/-! ### Axiom footprints -/

/-- info: 'LeanLLVM.Refinement.JsonStage2IR.stage2Body_retsValued' depends on axioms: [propext] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.JsonStage2IR.stage2Body_retsValued

/-- info: 'LeanLLVM.Refinement.JsonStage2IR.stage2Body_allocaTypes' depends on axioms: [propext] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.JsonStage2IR.stage2Body_allocaTypes

/-- info: 'LeanLLVM.Refinement.JsonStage2IR.stage2Calls_trap' depends on axioms: [propext] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.JsonStage2IR.stage2Calls_trap

/-- info: 'LeanLLVM.Refinement.JsonStage2IR.stage2Calls_lifetime' depends on axioms: [propext] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.JsonStage2IR.stage2Calls_lifetime

/-- info: 'LeanLLVM.Refinement.JsonStage2IR.Γ_stage2at_pre' depends on axioms: [propext] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.JsonStage2IR.Γ_stage2at_pre

/-- info: 'LeanLLVM.Refinement.JsonStage2IR.stage2Args_take13' depends on axioms: [propext] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.JsonStage2IR.stage2Args_take13

/-- info: 'LeanLLVM.Refinement.JsonStage2IR.satisfies_calls_stage2' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.JsonStage2IR.satisfies_calls_stage2

/-- info: 'LeanLLVM.Refinement.JsonStage2IR.Stage2WalkObligation.summary' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.JsonStage2IR.Stage2WalkObligation.summary

/-- info: 'LeanLLVM.Refinement.JsonStage2IR.stage2_walk_yields_record' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.JsonStage2IR.stage2_walk_yields_record

/-- info: 'LeanLLVM.Refinement.JsonStage2IR.stage2Pre_length' depends on axioms: [propext] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.JsonStage2IR.stage2Pre_length
