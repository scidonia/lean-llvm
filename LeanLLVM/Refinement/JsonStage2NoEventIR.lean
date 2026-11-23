/-
The no-event stage-2 entry's emitted body, pinned, with the staging and call
censuses the boundary record consumes.

`probes/install/ir/stage2-noevent.candidate.ll` is the body this module pins.
`capture-stage2-noevent.sh` records how it is derived; the summary is:

* `kernel/json/stage2_noevent.c` with `kernel/json/stage2.c` included under its
  entry rename, at the measured compiler line
  (`-O3 -march=x86-64-v3 -mpclmul -std=gnu11 -falign-loops=64
  -falign-functions=64`), with `__attribute__((noinline))` on every helper and
  two derivation flags:
  * `-fno-discard-value-names`, a naming flag whose neutrality the capture
    checks by normalising both emissions;
  * `-fno-slp-vectorize`, NOT the measured line: at the measured line clang SLP
    packs the entry's two independent 64-bit counters into `<2 x i64>`, which
    changes no value but puts vector types in the body.  With the flag the body
    carries none, which the capture's residual check enforces;
* `opt -passes=lower-switch`, since the entry's byte dispatch is emitted as
  switches;
* the entry's `define` block, with the argument surface stripped (recorded in
  `stage2-noevent.strip.tsv`) and the derivation's rewrites (recorded in
  `stage2-noevent.rewrites.tsv`): array reads become byte reads, the refusal
  record's message word becomes `null`, `llvm.umax.i32` unfolds to
  `icmp`+`select`, and the four local objects the fragment could not allocate
  become appended `ptr` parameters (`stage2-noevent.staging.tsv`).

## What the pin is, and what it is not

It is the entry's body with its intra-unit helper boundaries preserved.  The
entry calls the certified unit's helpers out of line -- `s2_string_body`,
`num_fast_el1`, `od_gap_recover`, and the lifetime, `memset` and `trap`
intrinsics -- so their text is not in this block; the four scalar `alloca i64`
locals the entry keeps (`%xj`, `%outn`, `%outn205`, `%ei`) are its own body
text.

The scalar literal compare is also body text: the entry's `ne_lit` packs the
literal into an integer rather than passing the certified `lit_check` a
`const char *`, because the fragment has no module-global representation.
`ne_lit` returns `lit_check`'s verdict and its offset; that equality is the
boundary record's obligation, not this module's claim.  The capture's call
census below shows no literal-helper call.

## The pin

`stage2NoEventBody` is the parsed fixture written out, and the `#guard`s below
assert that the parser returns exactly it, that the module's declaration count
is the fixture's, that the ABI prefix and the staging suffix are the ones the
derivation claims, that the census is closed, and that `retsValued` holds.
The pin is a `#guard` rather than a `rfl` proposition because the parser runs
on `String` primitives, which the kernel does not reduce.

`stage2NoEventSrcMutated` is the mutation that shows the pin bites: the same
text with one immediate changed.  It parses, and it is not
`stage2NoEventBody`, so the equality above is about the text and not about a
search that would accept anything.
-/
import LeanLLVM.Memory
import LeanLLVM.Parser
import LeanLLVM.Refinement.Relation

set_option autoImplicit false
set_option maxRecDepth 8192

namespace LeanLLVM.Refinement.JsonStage2NoEventIR

open LeanLLVM
open LeanLLVM.Refinement

/-! ### The fixture, parsed -/

/-- The no-event stage-2 entry as emitted and committed. -/
def stage2NoEventSrc : String :=
  include_str "../../probes/install/ir/stage2-noevent.candidate.ll"

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

def stage2NoEventBody : Function :=
{ name := "leanllvm_json_stage2_noevent",
  retTy := (Ty.int 64),
  params := [
    ("%b", Ty.ptr),
    ("%n", (Ty.int 64)),
    ("%ep", Ty.ptr),
    ("%nep", (Ty.int 64)),
    ("%xp", Ty.ptr),
    ("%nxp", (Ty.int 64)),
    ("%scratch", Ty.ptr),
    ("%scratchcap", (Ty.int 64)),
    ("%tokens_out", Ty.ptr),
    ("%values_out", Ty.ptr),
    ("%sum_out", Ty.ptr),
    ("%err", Ty.ptr),
    ("%stk", Ty.ptr),
    ("%e", Ty.ptr),
    ("%c", Ty.ptr),
    ("%d", Ty.ptr)
  ],
  blocks := [
    { name := "entry",
      instrs := [
      Instr.alloca "%xj" (Ty.int 64) 0,
      Instr.alloca "%outn" (Ty.int 64) 0,
      Instr.alloca "%outn205" (Ty.int 64) 0,
      Instr.alloca "%ei" (Ty.int 64) 0,
      Instr.callVoid "llvm.lifetime.start.p0" [((Ty.int 64), (Operand.imm (.int 64 (BitVec.ofNat 64 8)))), (Ty.ptr, (Operand.reg "%xj"))],
      Instr.store (Ty.int 64) (Operand.imm (.int 64 (BitVec.ofNat 64 0))) (Operand.reg "%xj"),
      Instr.callVoid "llvm.lifetime.start.p0" [((Ty.int 64), (Operand.imm (.int 64 (BitVec.ofNat 64 520)))), (Ty.ptr, (Operand.reg "%stk"))],
      Instr.callVoid "llvm.lifetime.start.p0" [((Ty.int 64), (Operand.imm (.int 64 (BitVec.ofNat 64 24)))), (Ty.ptr, (Operand.reg "%e"))],
      Instr.callVoid "llvm.lifetime.start.p0" [((Ty.int 64), (Operand.imm (.int 64 (BitVec.ofNat 64 1192)))), (Ty.ptr, (Operand.reg "%c"))],
      Instr.store (Ty.int 32) (Operand.imm (.int 32 (BitVec.ofNat 32 1))) (Operand.reg "%e"),
      Instr.gep "%off" (Ty.int 8) (Operand.reg "%e") (Operand.imm (.int 64 (BitVec.ofNat 64 8))),
      Instr.store (Ty.int 64) (Operand.imm (.int 64 (BitVec.ofNat 64 0))) (Operand.reg "%off"),
      Instr.gep "%msg" (Ty.int 8) (Operand.reg "%e") (Operand.imm (.int 64 (BitVec.ofNat 64 16))),
      Instr.store Ty.ptr (Operand.imm .null) (Operand.reg "%msg"),
      Instr.gep "%0" (Ty.int 8) (Operand.reg "%c") (Operand.imm (.int 64 (BitVec.ofNat 64 32))),
      Instr.callVoid "llvm.memset.p0.i64" [(Ty.ptr, (Operand.reg "%0")), ((Ty.int 8), (Operand.imm (.int 8 (BitVec.ofNat 8 0)))), ((Ty.int 64), (Operand.imm (.int 64 (BitVec.ofNat 64 1160)))), ((Ty.int 1), (Operand.imm (.int 1 (BitVec.ofNat 1 0))))],
      Instr.store Ty.ptr (Operand.reg "%b") (Operand.reg "%c"),
      Instr.gep "%n2" (Ty.int 8) (Operand.reg "%c") (Operand.imm (.int 64 (BitVec.ofNat 64 8))),
      Instr.store (Ty.int 64) (Operand.reg "%n") (Operand.reg "%n2"),
      Instr.gep "%ix" (Ty.int 8) (Operand.reg "%c") (Operand.imm (.int 64 (BitVec.ofNat 64 16))),
      Instr.store Ty.ptr (Operand.reg "%ep") (Operand.reg "%ix"),
      Instr.gep "%nix" (Ty.int 8) (Operand.reg "%c") (Operand.imm (.int 64 (BitVec.ofNat 64 24))),
      Instr.store (Ty.int 64) (Operand.reg "%nep") (Operand.reg "%nix"),
      Instr.gep "%e3" (Ty.int 8) (Operand.reg "%c") (Operand.imm (.int 64 (BitVec.ofNat 64 1112))),
      Instr.store Ty.ptr (Operand.reg "%e") (Operand.reg "%e3"),
      Instr.gep "%invariant.gep" (Ty.int 8) (Operand.reg "%b") (Operand.imm (.int 64 (BitVec.ofNat 64 1))),
      Instr.gep "%invariant.gep1068" (Ty.int 8) (Operand.reg "%b") (Operand.imm (.int 64 (BitVec.ofNat 64 18446744073709551615))),
      Instr.gep "%k219" (Ty.int 8) (Operand.reg "%c") (Operand.imm (.int 64 (BitVec.ofNat 64 32))),
      Instr.icmp "%cmp.not.peel1401.not" IPred.eq 64 (Operand.reg "%nep") (Operand.imm (.int 64 (BitVec.ofNat 64 0)))
      ],
      term := Term.condbr (Operand.reg "%cmp.not.peel1401.not") "if.then" "if.end.peel.preheader" },
    { name := "if.end.peel.preheader",
      instrs := [
      Instr.gep "%invariant.gep1650" (Ty.int 8) (Operand.reg "%scratch") (Operand.imm (.int 64 (BitVec.ofNat 64 1))),
      Instr.gep "%invariant.gep1652" (Ty.int 8) (Operand.reg "%scratch") (Operand.imm (.int 64 (BitVec.ofNat 64 2))),
      Instr.gep "%invariant.gep1654" (Ty.int 8) (Operand.reg "%scratch") (Operand.imm (.int 64 (BitVec.ofNat 64 3))),
      Instr.gep "%invariant.gep1656" (Ty.int 8) (Operand.reg "%scratch") (Operand.imm (.int 64 (BitVec.ofNat 64 4))),
      Instr.gep "%invariant.gep1658" (Ty.int 8) (Operand.reg "%scratch") (Operand.imm (.int 64 (BitVec.ofNat 64 5))),
      Instr.gep "%invariant.gep1660" (Ty.int 8) (Operand.reg "%scratch") (Operand.imm (.int 64 (BitVec.ofNat 64 6))),
      Instr.gep "%invariant.gep1662" (Ty.int 8) (Operand.reg "%scratch") (Operand.imm (.int 64 (BitVec.ofNat 64 7))),
      Instr.gep "%invariant.gep1664" (Ty.int 8) (Operand.reg "%scratch") (Operand.imm (.int 64 (BitVec.ofNat 64 1))),
      Instr.gep "%invariant.gep1666" (Ty.int 8) (Operand.reg "%scratch") (Operand.imm (.int 64 (BitVec.ofNat 64 2))),
      Instr.gep "%invariant.gep1668" (Ty.int 8) (Operand.reg "%scratch") (Operand.imm (.int 64 (BitVec.ofNat 64 3))),
      Instr.gep "%invariant.gep1670" (Ty.int 8) (Operand.reg "%scratch") (Operand.imm (.int 64 (BitVec.ofNat 64 4))),
      Instr.gep "%invariant.gep1672" (Ty.int 8) (Operand.reg "%scratch") (Operand.imm (.int 64 (BitVec.ofNat 64 5))),
      Instr.gep "%invariant.gep1674" (Ty.int 8) (Operand.reg "%scratch") (Operand.imm (.int 64 (BitVec.ofNat 64 6))),
      Instr.gep "%invariant.gep1676" (Ty.int 8) (Operand.reg "%scratch") (Operand.imm (.int 64 (BitVec.ofNat 64 7)))
      ],
      term := Term.br "if.end.peel" },
    { name := "if.end.peel",
      instrs := [
      Instr.phi "%wide.trip.count1409" (Ty.int 64) [("value.outer.backedge", (Operand.reg "%wide.trip.count")), ("if.end.peel.preheader", (Operand.imm (.int 64 (BitVec.ofNat 64 520))))],
      Instr.phi "%1" (Ty.int 64) [("value.outer.backedge", (Operand.reg "%45")), ("if.end.peel.preheader", (Operand.imm (.int 64 (BitVec.ofNat 64 0))))],
      Instr.phi "%tokens.0.ph1408" (Ty.int 64) [("value.outer.backedge", (Operand.reg "%tokens.0.ph.be")), ("if.end.peel.preheader", (Operand.imm (.int 64 (BitVec.ofNat 64 0))))],
      Instr.phi "%terms.0.ph1407" (Ty.int 64) [("value.outer.backedge", (Operand.reg "%terms.0.ph.be")), ("if.end.peel.preheader", (Operand.imm (.int 64 (BitVec.ofNat 64 0))))],
      Instr.phi "%arena.0.ph1406" (Ty.int 64) [("value.outer.backedge", (Operand.reg "%arena.0.ph.be")), ("if.end.peel.preheader", (Operand.imm (.int 64 (BitVec.ofNat 64 0))))],
      Instr.phi "%alen.0.ph1405" (Ty.int 64) [("value.outer.backedge", (Operand.reg "%alen.0.ph.be")), ("if.end.peel.preheader", (Operand.imm (.int 64 (BitVec.ofNat 64 0))))],
      Instr.phi "%k.0.ph1404" (Ty.int 64) [("value.outer.backedge", (Operand.reg "%k.0.ph.be")), ("if.end.peel.preheader", (Operand.imm (.int 64 (BitVec.ofNat 64 0))))],
      Instr.phi "%sp.0.ph1403" (Ty.int 32) [("value.outer.backedge", (Operand.reg "%sp.0.ph.be")), ("if.end.peel.preheader", (Operand.imm (.int 32 (BitVec.ofNat 32 0))))],
      Instr.phi "%frame.0.ph1402" (Ty.int 8) [("value.outer.backedge", (Operand.reg "%frame.0.ph.be")), ("if.end.peel.preheader", (Operand.imm (.int 8 (BitVec.ofNat 8 0))))],
      Instr.binop "%inc.peel" BinOp.add 64 (Operand.reg "%k.0.ph1404") (Operand.imm (.int 64 (BitVec.ofNat 64 1))),
      Instr.gep "%arrayidx.peel" (Ty.int 32) (Operand.reg "%ep") (Operand.reg "%k.0.ph1404"),
      Instr.load "%2" (Ty.int 32) (Operand.reg "%arrayidx.peel"),
      Instr.zext "%idxprom.peel" 32 64 (Operand.reg "%2"),
      Instr.gep "%arrayidx6.peel" (Ty.int 8) (Operand.reg "%b") (Operand.reg "%idxprom.peel"),
      Instr.load "%3" (Ty.int 8) (Operand.reg "%arrayidx6.peel")
      ],
      term := Term.br "NodeBlock5" },
    { name := "NodeBlock5",
      instrs := [
      Instr.icmp "%Pivot6" IPred.slt 8 (Operand.reg "%3") (Operand.imm (.int 8 (BitVec.ofNat 8 91)))
      ],
      term := Term.condbr (Operand.reg "%Pivot6") "LeafBlock" "NodeBlock" },
    { name := "NodeBlock",
      instrs := [
      Instr.icmp "%Pivot" IPred.slt 8 (Operand.reg "%3") (Operand.imm (.int 8 (BitVec.ofNat 8 123)))
      ],
      term := Term.condbr (Operand.reg "%Pivot") "LeafBlock1" "LeafBlock3" },
    { name := "LeafBlock3",
      instrs := [
      Instr.icmp "%SwitchLeaf4" IPred.eq 8 (Operand.reg "%3") (Operand.imm (.int 8 (BitVec.ofNat 8 123)))
      ],
      term := Term.condbr (Operand.reg "%SwitchLeaf4") "if.then9" "scalar" },
    { name := "LeafBlock1",
      instrs := [
      Instr.icmp "%SwitchLeaf2" IPred.eq 8 (Operand.reg "%3") (Operand.imm (.int 8 (BitVec.ofNat 8 91)))
      ],
      term := Term.condbr (Operand.reg "%SwitchLeaf2") "if.then35.peel" "scalar" },
    { name := "LeafBlock",
      instrs := [
      Instr.icmp "%SwitchLeaf" IPred.eq 8 (Operand.reg "%3") (Operand.imm (.int 8 (BitVec.ofNat 8 34)))
      ],
      term := Term.condbr (Operand.reg "%SwitchLeaf") "string_value" "scalar" },
    { name := "if.then35.peel",
      instrs := [
      Instr.icmp "%exitcond.peel" IPred.ugt 32 (Operand.reg "%sp.0.ph1403") (Operand.imm (.int 32 (BitVec.ofNat 32 519)))
      ],
      term := Term.condbr (Operand.reg "%exitcond.peel") "if.then38" "if.end45.peel" },
    { name := "if.end45.peel",
      instrs := [
      Instr.icmp "%tobool46.not.peel" IPred.eq 32 (Operand.reg "%sp.0.ph1403") (Operand.imm (.int 32 (BitVec.ofNat 32 0)))
      ],
      term := Term.condbr (Operand.reg "%tobool46.not.peel") "if.end51.peel" "if.then47.peel" },
    { name := "if.then47.peel",
      instrs := [
      Instr.binop "%4" BinOp.add 64 (Operand.reg "%1") (Operand.imm (.int 64 (BitVec.ofNat 64 18446744073709551615))),
      Instr.gep "%arrayidx50.peel" (Ty.int 8) (Operand.reg "%stk") (Operand.reg "%4"),
      Instr.store (Ty.int 8) (Operand.reg "%frame.0.ph1402") (Operand.reg "%arrayidx50.peel")
      ],
      term := Term.br "if.end51.peel" },
    { name := "if.end51.peel",
      instrs := [
      Instr.icmp "%cmp319.not.peel" IPred.ult 64 (Operand.reg "%inc.peel") (Operand.reg "%nep")
      ],
      term := Term.condbr (Operand.reg "%cmp319.not.peel") "if.end327.peel" "if.then321" },
    { name := "if.end327.peel",
      instrs := [
      Instr.gep "%arrayidx328.peel" (Ty.int 32) (Operand.reg "%ep") (Operand.reg "%inc.peel"),
      Instr.load "%5" (Ty.int 32) (Operand.reg "%arrayidx328.peel"),
      Instr.zext "%idxprom329.peel" 32 64 (Operand.reg "%5"),
      Instr.gep "%arrayidx330.peel" (Ty.int 8) (Operand.reg "%b") (Operand.reg "%idxprom329.peel"),
      Instr.load "%6" (Ty.int 8) (Operand.reg "%arrayidx330.peel"),
      Instr.icmp "%cmp332.peel" IPred.eq 8 (Operand.reg "%6") (Operand.imm (.int 8 (BitVec.ofNat 8 93)))
      ],
      term := Term.condbr (Operand.reg "%cmp332.peel") "if.then334" "if.end" },
    { name := "if.then",
      instrs := [
      Instr.store (Ty.int 64) (Operand.imm (.int 64 (BitVec.ofNat 64 0))) (Operand.reg "%tokens_out"),
      Instr.store (Ty.int 64) (Operand.imm (.int 64 (BitVec.ofNat 64 0))) (Operand.reg "%values_out"),
      Instr.store (Ty.int 64) (Operand.imm (.int 64 (BitVec.ofNat 64 0))) (Operand.reg "%sum_out"),
      Instr.store (Ty.int 64) (Operand.reg "%n") (Operand.reg "%err")
      ],
      term := Term.br "cleanup580" },
    { name := "if.end",
      instrs := [
      Instr.phi "%7" (Ty.int 8) [("if.end327", (Operand.reg "%47")), ("if.end327.peel", (Operand.reg "%6"))],
      Instr.phi "%8" (Ty.int 32) [("if.end327", (Operand.reg "%46")), ("if.end327.peel", (Operand.reg "%5"))],
      Instr.phi "%indvars.iv.in" (Ty.int 64) [("if.end327", (Operand.reg "%indvars.iv")), ("if.end327.peel", (Operand.reg "%1"))],
      Instr.phi "%k.0" (Ty.int 64) [("if.end327", (Operand.reg "%inc")), ("if.end327.peel", (Operand.reg "%inc.peel"))],
      Instr.phi "%terms.0.in" (Ty.int 64) [("if.end327", (Operand.reg "%terms.0")), ("if.end327.peel", (Operand.reg "%terms.0.ph1407"))],
      Instr.phi "%tokens.0.in" (Ty.int 64) [("if.end327", (Operand.reg "%tokens.0")), ("if.end327.peel", (Operand.reg "%tokens.0.ph1408"))],
      Instr.binop "%tokens.0" BinOp.add 64 (Operand.reg "%tokens.0.in") (Operand.imm (.int 64 (BitVec.ofNat 64 1))),
      Instr.binop "%terms.0" BinOp.add 64 (Operand.reg "%terms.0.in") (Operand.imm (.int 64 (BitVec.ofNat 64 3))),
      Instr.binop "%indvars.iv" BinOp.add 64 (Operand.reg "%indvars.iv.in") (Operand.imm (.int 64 (BitVec.ofNat 64 1))),
      Instr.binop "%inc" BinOp.add 64 (Operand.reg "%k.0") (Operand.imm (.int 64 (BitVec.ofNat 64 1)))
      ],
      term := Term.br "NodeBlock15" },
    { name := "NodeBlock15",
      instrs := [
      Instr.icmp "%Pivot16" IPred.slt 8 (Operand.reg "%7") (Operand.imm (.int 8 (BitVec.ofNat 8 91)))
      ],
      term := Term.condbr (Operand.reg "%Pivot16") "LeafBlock7" "NodeBlock13" },
    { name := "NodeBlock13",
      instrs := [
      Instr.icmp "%Pivot14" IPred.slt 8 (Operand.reg "%7") (Operand.imm (.int 8 (BitVec.ofNat 8 123)))
      ],
      term := Term.condbr (Operand.reg "%Pivot14") "LeafBlock9" "LeafBlock11" },
    { name := "LeafBlock11",
      instrs := [
      Instr.icmp "%SwitchLeaf12" IPred.eq 8 (Operand.reg "%7") (Operand.imm (.int 8 (BitVec.ofNat 8 123)))
      ],
      term := Term.condbr (Operand.reg "%SwitchLeaf12") "if.then9.loopexit" "scalar.loopexit" },
    { name := "LeafBlock9",
      instrs := [
      Instr.icmp "%SwitchLeaf10" IPred.eq 8 (Operand.reg "%7") (Operand.imm (.int 8 (BitVec.ofNat 8 91)))
      ],
      term := Term.condbr (Operand.reg "%SwitchLeaf10") "if.then35" "scalar.loopexit" },
    { name := "LeafBlock7",
      instrs := [
      Instr.icmp "%SwitchLeaf8" IPred.eq 8 (Operand.reg "%7") (Operand.imm (.int 8 (BitVec.ofNat 8 34)))
      ],
      term := Term.condbr (Operand.reg "%SwitchLeaf8") "string_value.loopexit" "scalar.loopexit" },
    { name := "if.then9.loopexit",
      instrs := [
      Instr.zext "%idxprom.le1289" 32 64 (Operand.reg "%8"),
      Instr.trunc "%9" 64 32 (Operand.reg "%indvars.iv")
      ],
      term := Term.br "if.then9" },
    { name := "if.then9",
      instrs := [
      Instr.phi "%inc.lcssa1129" (Ty.int 64) [("LeafBlock3", (Operand.reg "%inc.peel")), ("if.then9.loopexit", (Operand.reg "%inc"))],
      Instr.phi "%idxprom.lcssa1108" (Ty.int 64) [("LeafBlock3", (Operand.reg "%idxprom.peel")), ("if.then9.loopexit", (Operand.reg "%idxprom.le1289"))],
      Instr.phi "%frame.0.lcssa1098" (Ty.int 8) [("LeafBlock3", (Operand.reg "%frame.0.ph1402")), ("if.then9.loopexit", (Operand.imm (.int 8 (BitVec.ofNat 8 1))))],
      Instr.phi "%sp.0.lcssa1092.wide" (Ty.int 32) [("LeafBlock3", (Operand.reg "%sp.0.ph1403")), ("if.then9.loopexit", (Operand.reg "%9"))],
      Instr.phi "%k.0.lcssa1086" (Ty.int 64) [("LeafBlock3", (Operand.reg "%k.0.ph1404")), ("if.then9.loopexit", (Operand.reg "%k.0"))],
      Instr.phi "%terms.0.lcssa1080" (Ty.int 64) [("LeafBlock3", (Operand.reg "%terms.0.ph1407")), ("if.then9.loopexit", (Operand.reg "%terms.0"))],
      Instr.phi "%tokens.0.lcssa1074" (Ty.int 64) [("LeafBlock3", (Operand.reg "%tokens.0.ph1408")), ("if.then9.loopexit", (Operand.reg "%tokens.0"))],
      Instr.icmp "%cmp10" IPred.ugt 32 (Operand.reg "%sp.0.lcssa1092.wide") (Operand.imm (.int 32 (BitVec.ofNat 32 519)))
      ],
      term := Term.condbr (Operand.reg "%cmp10") "if.then12" "if.end19" },
    { name := "if.then12",
      instrs := [
      Instr.store (Ty.int 64) (Operand.imm (.int 64 (BitVec.ofNat 64 0))) (Operand.reg "%tokens_out"),
      Instr.store (Ty.int 64) (Operand.imm (.int 64 (BitVec.ofNat 64 0))) (Operand.reg "%values_out"),
      Instr.store (Ty.int 64) (Operand.imm (.int 64 (BitVec.ofNat 64 0))) (Operand.reg "%sum_out"),
      Instr.store (Ty.int 64) (Operand.reg "%idxprom.lcssa1108") (Operand.reg "%err")
      ],
      term := Term.br "cleanup580" },
    { name := "if.end19",
      instrs := [
      Instr.icmp "%tobool.not" IPred.eq 32 (Operand.reg "%sp.0.lcssa1092.wide") (Operand.imm (.int 32 (BitVec.ofNat 32 0)))
      ],
      term := Term.condbr (Operand.reg "%tobool.not") "if.end23" "if.then20" },
    { name := "if.then20",
      instrs := [
      Instr.binop "%sub" BinOp.add 32 (Operand.reg "%sp.0.lcssa1092.wide") (Operand.imm (.int 32 (BitVec.ofNat 32 4294967295))),
      Instr.zext "%idxprom21" 32 64 (Operand.reg "%sub"),
      Instr.gep "%arrayidx22" (Ty.int 8) (Operand.reg "%stk") (Operand.reg "%idxprom21"),
      Instr.store (Ty.int 8) (Operand.reg "%frame.0.lcssa1098") (Operand.reg "%arrayidx22")
      ],
      term := Term.br "if.end23" },
    { name := "if.end23",
      instrs := [
      Instr.binop "%inc24" BinOp.add 32 (Operand.reg "%sp.0.lcssa1092.wide") (Operand.imm (.int 32 (BitVec.ofNat 32 1))),
      Instr.icmp "%cmp66.not" IPred.ult 64 (Operand.reg "%inc.lcssa1129") (Operand.reg "%nep")
      ],
      term := Term.condbr (Operand.reg "%cmp66.not") "if.end74" "if.then68" },
    { name := "if.then35",
      instrs := [
      Instr.icmp "%exitcond" IPred.eq 64 (Operand.reg "%indvars.iv") (Operand.reg "%wide.trip.count1409")
      ],
      term := Term.condbr (Operand.reg "%exitcond") "if.then38.loopexit" "if.end51" },
    { name := "if.then38.loopexit",
      instrs := [
      Instr.zext "%idxprom.le" 32 64 (Operand.reg "%8")
      ],
      term := Term.br "if.then38" },
    { name := "if.then38",
      instrs := [
      Instr.phi "%idxprom.lcssa1110" (Ty.int 64) [("if.then38.loopexit", (Operand.reg "%idxprom.le")), ("if.then35.peel", (Operand.reg "%idxprom.peel"))],
      Instr.store (Ty.int 64) (Operand.imm (.int 64 (BitVec.ofNat 64 0))) (Operand.reg "%tokens_out"),
      Instr.store (Ty.int 64) (Operand.imm (.int 64 (BitVec.ofNat 64 0))) (Operand.reg "%values_out"),
      Instr.store (Ty.int 64) (Operand.imm (.int 64 (BitVec.ofNat 64 0))) (Operand.reg "%sum_out"),
      Instr.store (Ty.int 64) (Operand.reg "%idxprom.lcssa1110") (Operand.reg "%err")
      ],
      term := Term.br "cleanup580" },
    { name := "if.end51",
      instrs := [
      Instr.gep "%arrayidx50" (Ty.int 8) (Operand.reg "%stk") (Operand.reg "%indvars.iv.in"),
      Instr.store (Ty.int 8) (Operand.imm (.int 8 (BitVec.ofNat 8 1))) (Operand.reg "%arrayidx50"),
      Instr.icmp "%cmp319.not" IPred.ult 64 (Operand.reg "%inc") (Operand.reg "%nep")
      ],
      term := Term.condbr (Operand.reg "%cmp319.not") "if.end327" "if.then321" },
    { name := "if.then68",
      instrs := [
      Instr.store (Ty.int 64) (Operand.imm (.int 64 (BitVec.ofNat 64 0))) (Operand.reg "%tokens_out"),
      Instr.store (Ty.int 64) (Operand.imm (.int 64 (BitVec.ofNat 64 0))) (Operand.reg "%values_out"),
      Instr.store (Ty.int 64) (Operand.imm (.int 64 (BitVec.ofNat 64 0))) (Operand.reg "%sum_out"),
      Instr.store (Ty.int 64) (Operand.reg "%n") (Operand.reg "%err")
      ],
      term := Term.br "cleanup580" },
    { name := "if.end74",
      instrs := [
      Instr.binop "%add" BinOp.add 64 (Operand.reg "%terms.0.lcssa1080") (Operand.imm (.int 64 (BitVec.ofNat 64 1))),
      Instr.binop "%inc26" BinOp.add 64 (Operand.reg "%tokens.0.lcssa1074") (Operand.imm (.int 64 (BitVec.ofNat 64 1))),
      Instr.gep "%arrayidx75" (Ty.int 32) (Operand.reg "%ep") (Operand.reg "%inc.lcssa1129"),
      Instr.load "%10" (Ty.int 32) (Operand.reg "%arrayidx75"),
      Instr.zext "%idxprom76" 32 64 (Operand.reg "%10"),
      Instr.gep "%arrayidx77" (Ty.int 8) (Operand.reg "%b") (Operand.reg "%idxprom76"),
      Instr.load "%11" (Ty.int 8) (Operand.reg "%arrayidx77")
      ],
      term := Term.br "NodeBlock21" },
    { name := "NodeBlock21",
      instrs := [
      Instr.icmp "%Pivot22" IPred.slt 8 (Operand.reg "%11") (Operand.imm (.int 8 (BitVec.ofNat 8 125)))
      ],
      term := Term.condbr (Operand.reg "%Pivot22") "LeafBlock17" "LeafBlock19" },
    { name := "LeafBlock19",
      instrs := [
      Instr.icmp "%SwitchLeaf20" IPred.eq 8 (Operand.reg "%11") (Operand.imm (.int 8 (BitVec.ofNat 8 125)))
      ],
      term := Term.condbr (Operand.reg "%SwitchLeaf20") "if.then81" "if.then94" },
    { name := "LeafBlock17",
      instrs := [
      Instr.icmp "%SwitchLeaf18" IPred.eq 8 (Operand.reg "%11") (Operand.imm (.int 8 (BitVec.ofNat 8 34)))
      ],
      term := Term.condbr (Operand.reg "%SwitchLeaf18") "key_body" "if.then94" },
    { name := "if.then81",
      instrs := [
      Instr.binop "%inc82" BinOp.add 64 (Operand.reg "%k.0.lcssa1086") (Operand.imm (.int 64 (BitVec.ofNat 64 2))),
      Instr.binop "%inc84" BinOp.add 64 (Operand.reg "%tokens.0.lcssa1074") (Operand.imm (.int 64 (BitVec.ofNat 64 2))),
      Instr.binop "%add85" BinOp.add 64 (Operand.reg "%terms.0.lcssa1080") (Operand.imm (.int 64 (BitVec.ofNat 64 3)))
      ],
      term := Term.br "close_obj" },
    { name := "if.then94",
      instrs := [
      Instr.store (Ty.int 64) (Operand.imm (.int 64 (BitVec.ofNat 64 0))) (Operand.reg "%tokens_out"),
      Instr.store (Ty.int 64) (Operand.imm (.int 64 (BitVec.ofNat 64 0))) (Operand.reg "%values_out"),
      Instr.store (Ty.int 64) (Operand.imm (.int 64 (BitVec.ofNat 64 0))) (Operand.reg "%sum_out"),
      Instr.store (Ty.int 64) (Operand.reg "%idxprom76") (Operand.reg "%err")
      ],
      term := Term.br "cleanup580" },
    { name := "if.then105",
      instrs := [
      Instr.store (Ty.int 64) (Operand.imm (.int 64 (BitVec.ofNat 64 0))) (Operand.reg "%tokens_out"),
      Instr.store (Ty.int 64) (Operand.imm (.int 64 (BitVec.ofNat 64 0))) (Operand.reg "%values_out"),
      Instr.store (Ty.int 64) (Operand.imm (.int 64 (BitVec.ofNat 64 0))) (Operand.reg "%sum_out"),
      Instr.store (Ty.int 64) (Operand.reg "%n") (Operand.reg "%err")
      ],
      term := Term.br "cleanup580" },
    { name := "if.end111",
      instrs := [
      Instr.gep "%arrayidx112" (Ty.int 32) (Operand.reg "%ep") (Operand.reg "%inc379"),
      Instr.load "%12" (Ty.int 32) (Operand.reg "%arrayidx112"),
      Instr.zext "%idxprom113" 32 64 (Operand.reg "%12"),
      Instr.gep "%arrayidx114" (Ty.int 8) (Operand.reg "%b") (Operand.reg "%idxprom113"),
      Instr.load "%13" (Ty.int 8) (Operand.reg "%arrayidx114"),
      Instr.icmp "%cmp116.not" IPred.eq 8 (Operand.reg "%13") (Operand.imm (.int 8 (BitVec.ofNat 8 34)))
      ],
      term := Term.condbr (Operand.reg "%cmp116.not") "key_body" "if.then118" },
    { name := "if.then118",
      instrs := [
      Instr.store (Ty.int 64) (Operand.imm (.int 64 (BitVec.ofNat 64 0))) (Operand.reg "%tokens_out"),
      Instr.store (Ty.int 64) (Operand.imm (.int 64 (BitVec.ofNat 64 0))) (Operand.reg "%values_out"),
      Instr.store (Ty.int 64) (Operand.imm (.int 64 (BitVec.ofNat 64 0))) (Operand.reg "%sum_out"),
      Instr.store (Ty.int 64) (Operand.reg "%idxprom113") (Operand.reg "%err")
      ],
      term := Term.br "cleanup580" },
    { name := "key_body",
      instrs := [
      Instr.phi "%p.0" (Ty.int 32) [("LeafBlock17", (Operand.reg "%10")), ("if.end111", (Operand.reg "%12"))],
      Instr.phi "%sp.1" (Ty.int 32) [("LeafBlock17", (Operand.reg "%inc24")), ("if.end111", (Operand.reg "%sp.4"))],
      Instr.phi "%k.1.in" (Ty.int 64) [("LeafBlock17", (Operand.reg "%k.0.lcssa1086")), ("if.end111", (Operand.reg "%k.6"))],
      Instr.phi "%alen.1" (Ty.int 64) [("LeafBlock17", (Operand.reg "%alen.0.ph1405")), ("if.end111", (Operand.reg "%alen.8"))],
      Instr.phi "%arena.1" (Ty.int 64) [("LeafBlock17", (Operand.reg "%arena.0.ph1406")), ("if.end111", (Operand.reg "%arena.10"))],
      Instr.phi "%terms.1" (Ty.int 64) [("LeafBlock17", (Operand.reg "%add")), ("if.end111", (Operand.reg "%terms.8"))],
      Instr.phi "%tokens.1" (Ty.int 64) [("LeafBlock17", (Operand.reg "%inc26")), ("if.end111", (Operand.reg "%tokens.8"))],
      Instr.binop "%k.1" BinOp.add 64 (Operand.reg "%k.1.in") (Operand.imm (.int 64 (BitVec.ofNat 64 2))),
      Instr.callVoid "llvm.lifetime.start.p0" [((Ty.int 64), (Operand.imm (.int 64 (BitVec.ofNat 64 8)))), (Ty.ptr, (Operand.reg "%outn"))],
      Instr.icmp "%cmp127.not" IPred.ult 64 (Operand.reg "%k.1") (Operand.reg "%nep")
      ],
      term := Term.condbr (Operand.reg "%cmp127.not") "if.end136" "if.then129" },
    { name := "if.then129",
      instrs := [
      Instr.zext "%conv130" 32 64 (Operand.reg "%p.0"),
      Instr.store (Ty.int 64) (Operand.imm (.int 64 (BitVec.ofNat 64 0))) (Operand.reg "%tokens_out"),
      Instr.store (Ty.int 64) (Operand.imm (.int 64 (BitVec.ofNat 64 0))) (Operand.reg "%values_out"),
      Instr.store (Ty.int 64) (Operand.imm (.int 64 (BitVec.ofNat 64 0))) (Operand.reg "%sum_out")
      ],
      term := Term.br "cleanup.thread" },
    { name := "if.end136",
      instrs := [
      Instr.binop "%inc137" BinOp.add 64 (Operand.reg "%k.1.in") (Operand.imm (.int 64 (BitVec.ofNat 64 3))),
      Instr.gep "%arrayidx138" (Ty.int 32) (Operand.reg "%ep") (Operand.reg "%k.1"),
      Instr.load "%14" (Ty.int 32) (Operand.reg "%arrayidx138"),
      Instr.store (Ty.int 64) (Operand.reg "%inc137") (Operand.reg "%k219"),
      Instr.zext "%conv140" 32 64 (Operand.reg "%14"),
      Instr.icmp "%cmp141.not" IPred.ugt 64 (Operand.reg "%n") (Operand.reg "%conv140"),
      Instr.zext "%conv152" 32 64 (Operand.reg "%p.0")
      ],
      term := Term.condbr (Operand.reg "%cmp141.not") "if.end150" "if.then143" },
    { name := "if.then143",
      instrs := [
      Instr.store (Ty.int 64) (Operand.imm (.int 64 (BitVec.ofNat 64 0))) (Operand.reg "%tokens_out"),
      Instr.store (Ty.int 64) (Operand.imm (.int 64 (BitVec.ofNat 64 0))) (Operand.reg "%values_out"),
      Instr.store (Ty.int 64) (Operand.imm (.int 64 (BitVec.ofNat 64 0))) (Operand.reg "%sum_out")
      ],
      term := Term.br "cleanup.thread" },
    { name := "if.end150",
      instrs := [
      Instr.binop "%15" BinOp.xor 64 (Operand.reg "%conv152") (Operand.imm (.int 64 (BitVec.ofNat 64 18446744073709551615))),
      Instr.binop "%sub154" BinOp.add 64 (Operand.reg "%conv140") (Operand.reg "%15"),
      Instr.binop "%add155" BinOp.add 64 (Operand.reg "%sub154") (Operand.imm (.int 64 (BitVec.ofNat 64 64))),
      Instr.icmp "%cmp156" IPred.ugt 64 (Operand.reg "%add155") (Operand.reg "%scratchcap")
      ],
      term := Term.condbr (Operand.reg "%cmp156") "if.then158" "if.end159" },
    { name := "if.then158",
      instrs := [
      Instr.callVoid "llvm.trap" []
      ],
      term := Term.unreachable },
    { name := "if.end159",
      instrs := [
      Instr.store (Ty.int 64) (Operand.imm (.int 64 (BitVec.ofNat 64 0))) (Operand.reg "%outn"),
      Instr.gep "%gep1071" (Ty.int 8) (Operand.reg "%invariant.gep") (Operand.reg "%conv152"),
      Instr.call "%call161" (Ty.int 32) "s2_string_body" [(Ty.ptr, (Operand.reg "%c")), (Ty.ptr, (Operand.reg "%gep1071")), ((Ty.int 64), (Operand.reg "%sub154")), (Ty.ptr, (Operand.reg "%scratch")), (Ty.ptr, (Operand.reg "%outn")), (Ty.ptr, (Operand.reg "%xp")), (Ty.ptr, (Operand.reg "%xj")), ((Ty.int 64), (Operand.reg "%nxp"))]
      ],
      term := Term.br "NodeBlock25" },
    { name := "NodeBlock25",
      instrs := [
      Instr.icmp "%Pivot26" IPred.slt 32 (Operand.reg "%call161") (Operand.imm (.int 32 (BitVec.ofNat 32 1)))
      ],
      term := Term.condbr (Operand.reg "%Pivot26") "do.body164" "LeafBlock23" },
    { name := "LeafBlock23",
      instrs := [
      Instr.icmp "%SwitchLeaf24" IPred.eq 32 (Operand.reg "%call161") (Operand.imm (.int 32 (BitVec.ofNat 32 1)))
      ],
      term := Term.condbr (Operand.reg "%SwitchLeaf24") "do.body172" "for.cond.preheader" },
    { name := "for.cond.preheader",
      instrs := [
      Instr.load "%16" (Ty.int 64) (Operand.reg "%outn"),
      Instr.icmp "%cmp1811063.not" IPred.eq 64 (Operand.reg "%16") (Operand.imm (.int 64 (BitVec.ofNat 64 0)))
      ],
      term := Term.condbr (Operand.reg "%cmp1811063.not") "for.cond.cleanup" "for.body.preheader" },
    { name := "for.body.preheader",
      instrs := [
      Instr.binop "%xtraiter1529" BinOp.and 64 (Operand.reg "%16") (Operand.imm (.int 64 (BitVec.ofNat 64 7))),
      Instr.icmp "%17" IPred.ult 64 (Operand.reg "%16") (Operand.imm (.int 64 (BitVec.ofNat 64 8)))
      ],
      term := Term.condbr (Operand.reg "%17") "for.cond.cleanup.loopexit.unr-lcssa" "for.body.preheader.new" },
    { name := "for.body.preheader.new",
      instrs := [
      Instr.binop "%unroll_iter1533" BinOp.and 64 (Operand.reg "%16") (Operand.imm (.int 64 (BitVec.ofNat 64 18446744073709551608)))
      ],
      term := Term.br "for.body" },
    { name := "do.body164",
      instrs := [
      Instr.store (Ty.int 64) (Operand.imm (.int 64 (BitVec.ofNat 64 0))) (Operand.reg "%tokens_out"),
      Instr.store (Ty.int 64) (Operand.imm (.int 64 (BitVec.ofNat 64 0))) (Operand.reg "%values_out"),
      Instr.store (Ty.int 64) (Operand.imm (.int 64 (BitVec.ofNat 64 0))) (Operand.reg "%sum_out"),
      Instr.load "%18" (Ty.int 64) (Operand.reg "%off")
      ],
      term := Term.br "cleanup.thread" },
    { name := "do.body172",
      instrs := [
      Instr.binop "%add175" BinOp.add 32 (Operand.reg "%p.0") (Operand.imm (.int 32 (BitVec.ofNat 32 1))),
      Instr.zext "%conv176" 32 64 (Operand.reg "%add175"),
      Instr.binop "%or" BinOp.add 64 (Operand.reg "%conv176") (Operand.imm (.int 64 (BitVec.ofNat 64 9223372036854775813))),
      Instr.binop "%add177" BinOp.add 64 (Operand.reg "%or") (Operand.reg "%sub154")
      ],
      term := Term.br "expect_colon" },
    { name := "for.cond.cleanup.loopexit.unr-lcssa",
      instrs := [
      Instr.phi "%add185.lcssa.ph" (Ty.int 64) [("for.body.preheader", (Operand.imm .poison)), ("for.body", (Operand.reg "%add185.7"))],
      Instr.phi "%arena.21065.unr" (Ty.int 64) [("for.body.preheader", (Operand.reg "%arena.1")), ("for.body", (Operand.reg "%add185.7"))],
      Instr.phi "%i.01064.unr" (Ty.int 64) [("for.body.preheader", (Operand.imm (.int 64 (BitVec.ofNat 64 0)))), ("for.body", (Operand.reg "%inc186.7"))],
      Instr.icmp "%lcmp.mod1531.not" IPred.eq 64 (Operand.reg "%xtraiter1529") (Operand.imm (.int 64 (BitVec.ofNat 64 0)))
      ],
      term := Term.condbr (Operand.reg "%lcmp.mod1531.not") "for.cond.cleanup" "for.body.epil" },
    { name := "for.body.epil",
      instrs := [
      Instr.phi "%arena.21065.epil" (Ty.int 64) [("for.body.epil", (Operand.reg "%add185.epil")), ("for.cond.cleanup.loopexit.unr-lcssa", (Operand.reg "%arena.21065.unr"))],
      Instr.phi "%i.01064.epil" (Ty.int 64) [("for.body.epil", (Operand.reg "%inc186.epil")), ("for.cond.cleanup.loopexit.unr-lcssa", (Operand.reg "%i.01064.unr"))],
      Instr.phi "%epil.iter1530" (Ty.int 64) [("for.body.epil", (Operand.reg "%epil.iter1530.next")), ("for.cond.cleanup.loopexit.unr-lcssa", (Operand.imm (.int 64 (BitVec.ofNat 64 0))))],
      Instr.gep "%arrayidx183.epil" (Ty.int 8) (Operand.reg "%scratch") (Operand.reg "%i.01064.epil"),
      Instr.load "%19" (Ty.int 8) (Operand.reg "%arrayidx183.epil"),
      Instr.zext "%conv184.epil" 8 64 (Operand.reg "%19"),
      Instr.binop "%add185.epil" BinOp.add 64 (Operand.reg "%arena.21065.epil") (Operand.reg "%conv184.epil"),
      Instr.binop "%inc186.epil" BinOp.add 64 (Operand.reg "%i.01064.epil") (Operand.imm (.int 64 (BitVec.ofNat 64 1))),
      Instr.binop "%epil.iter1530.next" BinOp.add 64 (Operand.reg "%epil.iter1530") (Operand.imm (.int 64 (BitVec.ofNat 64 1))),
      Instr.icmp "%epil.iter1530.cmp.not" IPred.eq 64 (Operand.reg "%epil.iter1530.next") (Operand.reg "%xtraiter1529")
      ],
      term := Term.condbr (Operand.reg "%epil.iter1530.cmp.not") "for.cond.cleanup" "for.body.epil" },
    { name := "for.cond.cleanup",
      instrs := [
      Instr.phi "%arena.2.lcssa" (Ty.int 64) [("for.cond.preheader", (Operand.reg "%arena.1")), ("for.cond.cleanup.loopexit.unr-lcssa", (Operand.reg "%add185.lcssa.ph")), ("for.body.epil", (Operand.reg "%add185.epil"))],
      Instr.binop "%add187" BinOp.add 64 (Operand.reg "%16") (Operand.reg "%alen.1"),
      Instr.binop "%add190" BinOp.add 64 (Operand.reg "%alen.1") (Operand.imm (.int 64 (BitVec.ofNat 64 5))),
      Instr.binop "%add191" BinOp.add 64 (Operand.reg "%add190") (Operand.reg "%16")
      ],
      term := Term.br "expect_colon" },
    { name := "for.body",
      instrs := [
      Instr.phi "%arena.21065" (Ty.int 64) [("for.body.preheader.new", (Operand.reg "%arena.1")), ("for.body", (Operand.reg "%add185.7"))],
      Instr.phi "%i.01064" (Ty.int 64) [("for.body.preheader.new", (Operand.imm (.int 64 (BitVec.ofNat 64 0)))), ("for.body", (Operand.reg "%inc186.7"))],
      Instr.phi "%niter1534" (Ty.int 64) [("for.body.preheader.new", (Operand.imm (.int 64 (BitVec.ofNat 64 0)))), ("for.body", (Operand.reg "%niter1534.next.7"))],
      Instr.gep "%arrayidx183" (Ty.int 8) (Operand.reg "%scratch") (Operand.reg "%i.01064"),
      Instr.load "%20" (Ty.int 8) (Operand.reg "%arrayidx183"),
      Instr.zext "%conv184" 8 64 (Operand.reg "%20"),
      Instr.binop "%add185" BinOp.add 64 (Operand.reg "%arena.21065") (Operand.reg "%conv184"),
      Instr.gep "%gep1665" (Ty.int 8) (Operand.reg "%invariant.gep1664") (Operand.reg "%i.01064"),
      Instr.load "%21" (Ty.int 8) (Operand.reg "%gep1665"),
      Instr.zext "%conv184.1" 8 64 (Operand.reg "%21"),
      Instr.binop "%add185.1" BinOp.add 64 (Operand.reg "%add185") (Operand.reg "%conv184.1"),
      Instr.gep "%gep1667" (Ty.int 8) (Operand.reg "%invariant.gep1666") (Operand.reg "%i.01064"),
      Instr.load "%22" (Ty.int 8) (Operand.reg "%gep1667"),
      Instr.zext "%conv184.2" 8 64 (Operand.reg "%22"),
      Instr.binop "%add185.2" BinOp.add 64 (Operand.reg "%add185.1") (Operand.reg "%conv184.2"),
      Instr.gep "%gep1669" (Ty.int 8) (Operand.reg "%invariant.gep1668") (Operand.reg "%i.01064"),
      Instr.load "%23" (Ty.int 8) (Operand.reg "%gep1669"),
      Instr.zext "%conv184.3" 8 64 (Operand.reg "%23"),
      Instr.binop "%add185.3" BinOp.add 64 (Operand.reg "%add185.2") (Operand.reg "%conv184.3"),
      Instr.gep "%gep1671" (Ty.int 8) (Operand.reg "%invariant.gep1670") (Operand.reg "%i.01064"),
      Instr.load "%24" (Ty.int 8) (Operand.reg "%gep1671"),
      Instr.zext "%conv184.4" 8 64 (Operand.reg "%24"),
      Instr.binop "%add185.4" BinOp.add 64 (Operand.reg "%add185.3") (Operand.reg "%conv184.4"),
      Instr.gep "%gep1673" (Ty.int 8) (Operand.reg "%invariant.gep1672") (Operand.reg "%i.01064"),
      Instr.load "%25" (Ty.int 8) (Operand.reg "%gep1673"),
      Instr.zext "%conv184.5" 8 64 (Operand.reg "%25"),
      Instr.binop "%add185.5" BinOp.add 64 (Operand.reg "%add185.4") (Operand.reg "%conv184.5"),
      Instr.gep "%gep1675" (Ty.int 8) (Operand.reg "%invariant.gep1674") (Operand.reg "%i.01064"),
      Instr.load "%26" (Ty.int 8) (Operand.reg "%gep1675"),
      Instr.zext "%conv184.6" 8 64 (Operand.reg "%26"),
      Instr.binop "%add185.6" BinOp.add 64 (Operand.reg "%add185.5") (Operand.reg "%conv184.6"),
      Instr.gep "%gep1677" (Ty.int 8) (Operand.reg "%invariant.gep1676") (Operand.reg "%i.01064"),
      Instr.load "%27" (Ty.int 8) (Operand.reg "%gep1677"),
      Instr.zext "%conv184.7" 8 64 (Operand.reg "%27"),
      Instr.binop "%add185.7" BinOp.add 64 (Operand.reg "%add185.6") (Operand.reg "%conv184.7"),
      Instr.binop "%inc186.7" BinOp.add 64 (Operand.reg "%i.01064") (Operand.imm (.int 64 (BitVec.ofNat 64 8))),
      Instr.binop "%niter1534.next.7" BinOp.add 64 (Operand.reg "%niter1534") (Operand.imm (.int 64 (BitVec.ofNat 64 8))),
      Instr.icmp "%niter1534.ncmp.7" IPred.eq 64 (Operand.reg "%niter1534.next.7") (Operand.reg "%unroll_iter1533")
      ],
      term := Term.condbr (Operand.reg "%niter1534.ncmp.7") "for.cond.cleanup.loopexit.unr-lcssa" "for.body" },
    { name := "cleanup.thread",
      instrs := [
      Instr.phi "%conv130.sink" (Ty.int 64) [("if.then129", (Operand.reg "%conv130")), ("if.then143", (Operand.reg "%conv152")), ("do.body164", (Operand.reg "%18"))],
      Instr.store (Ty.int 64) (Operand.reg "%conv130.sink") (Operand.reg "%err"),
      Instr.callVoid "llvm.lifetime.end.p0" [((Ty.int 64), (Operand.imm (.int 64 (BitVec.ofNat 64 8)))), (Ty.ptr, (Operand.reg "%outn"))]
      ],
      term := Term.br "cleanup580" },
    { name := "string_value.loopexit",
      instrs := [
      Instr.zext "%idxprom.le1287" 32 64 (Operand.reg "%8"),
      Instr.trunc "%28" 64 32 (Operand.reg "%indvars.iv")
      ],
      term := Term.br "string_value" },
    { name := "string_value",
      instrs := [
      Instr.phi "%inc.lcssa1130" (Ty.int 64) [("LeafBlock", (Operand.reg "%inc.peel")), ("string_value.loopexit", (Operand.reg "%inc"))],
      Instr.phi "%.lcssa1125" (Ty.int 32) [("LeafBlock", (Operand.reg "%2")), ("string_value.loopexit", (Operand.reg "%8"))],
      Instr.phi "%idxprom.lcssa1109" (Ty.int 64) [("LeafBlock", (Operand.reg "%idxprom.peel")), ("string_value.loopexit", (Operand.reg "%idxprom.le1287"))],
      Instr.phi "%frame.0.lcssa1099" (Ty.int 8) [("LeafBlock", (Operand.reg "%frame.0.ph1402")), ("string_value.loopexit", (Operand.imm (.int 8 (BitVec.ofNat 8 1))))],
      Instr.phi "%sp.0.lcssa1093.wide" (Ty.int 32) [("LeafBlock", (Operand.reg "%sp.0.ph1403")), ("string_value.loopexit", (Operand.reg "%28"))],
      Instr.phi "%k.0.lcssa1087" (Ty.int 64) [("LeafBlock", (Operand.reg "%k.0.ph1404")), ("string_value.loopexit", (Operand.reg "%k.0"))],
      Instr.phi "%terms.0.lcssa1081" (Ty.int 64) [("LeafBlock", (Operand.reg "%terms.0.ph1407")), ("string_value.loopexit", (Operand.reg "%terms.0"))],
      Instr.phi "%tokens.0.lcssa1075" (Ty.int 64) [("LeafBlock", (Operand.reg "%tokens.0.ph1408")), ("string_value.loopexit", (Operand.reg "%tokens.0"))],
      Instr.callVoid "llvm.lifetime.start.p0" [((Ty.int 64), (Operand.imm (.int 64 (BitVec.ofNat 64 8)))), (Ty.ptr, (Operand.reg "%outn205"))],
      Instr.icmp "%cmp207.not" IPred.ult 64 (Operand.reg "%inc.lcssa1130") (Operand.reg "%nep")
      ],
      term := Term.condbr (Operand.reg "%cmp207.not") "if.end216" "if.then209" },
    { name := "if.then209",
      instrs := [
      Instr.store (Ty.int 64) (Operand.imm (.int 64 (BitVec.ofNat 64 0))) (Operand.reg "%tokens_out"),
      Instr.store (Ty.int 64) (Operand.imm (.int 64 (BitVec.ofNat 64 0))) (Operand.reg "%values_out"),
      Instr.store (Ty.int 64) (Operand.imm (.int 64 (BitVec.ofNat 64 0))) (Operand.reg "%sum_out")
      ],
      term := Term.br "cleanup287.thread" },
    { name := "if.end216",
      instrs := [
      Instr.binop "%inc217" BinOp.add 64 (Operand.reg "%k.0.lcssa1087") (Operand.imm (.int 64 (BitVec.ofNat 64 2))),
      Instr.gep "%arrayidx218" (Ty.int 32) (Operand.reg "%ep") (Operand.reg "%inc.lcssa1130"),
      Instr.load "%29" (Ty.int 32) (Operand.reg "%arrayidx218"),
      Instr.store (Ty.int 64) (Operand.reg "%inc217") (Operand.reg "%k219"),
      Instr.zext "%conv220" 32 64 (Operand.reg "%29"),
      Instr.icmp "%cmp221.not" IPred.ugt 64 (Operand.reg "%n") (Operand.reg "%conv220")
      ],
      term := Term.condbr (Operand.reg "%cmp221.not") "if.end230" "if.then223" },
    { name := "if.then223",
      instrs := [
      Instr.store (Ty.int 64) (Operand.imm (.int 64 (BitVec.ofNat 64 0))) (Operand.reg "%tokens_out"),
      Instr.store (Ty.int 64) (Operand.imm (.int 64 (BitVec.ofNat 64 0))) (Operand.reg "%values_out"),
      Instr.store (Ty.int 64) (Operand.imm (.int 64 (BitVec.ofNat 64 0))) (Operand.reg "%sum_out")
      ],
      term := Term.br "cleanup287.thread" },
    { name := "if.end230",
      instrs := [
      Instr.binop "%30" BinOp.xor 64 (Operand.reg "%idxprom.lcssa1109") (Operand.imm (.int 64 (BitVec.ofNat 64 18446744073709551615))),
      Instr.binop "%sub234" BinOp.add 64 (Operand.reg "%conv220") (Operand.reg "%30"),
      Instr.binop "%add235" BinOp.add 64 (Operand.reg "%sub234") (Operand.imm (.int 64 (BitVec.ofNat 64 64))),
      Instr.icmp "%cmp236" IPred.ugt 64 (Operand.reg "%add235") (Operand.reg "%scratchcap")
      ],
      term := Term.condbr (Operand.reg "%cmp236") "if.then238" "if.end239" },
    { name := "if.then238",
      instrs := [
      Instr.callVoid "llvm.trap" []
      ],
      term := Term.unreachable },
    { name := "if.end239",
      instrs := [
      Instr.store (Ty.int 64) (Operand.imm (.int 64 (BitVec.ofNat 64 0))) (Operand.reg "%outn205"),
      Instr.gep "%gep" (Ty.int 8) (Operand.reg "%invariant.gep") (Operand.reg "%idxprom.lcssa1109"),
      Instr.call "%call243" (Ty.int 32) "s2_string_body" [(Ty.ptr, (Operand.reg "%c")), (Ty.ptr, (Operand.reg "%gep")), ((Ty.int 64), (Operand.reg "%sub234")), (Ty.ptr, (Operand.reg "%scratch")), (Ty.ptr, (Operand.reg "%outn205")), (Ty.ptr, (Operand.reg "%xp")), (Ty.ptr, (Operand.reg "%xj")), ((Ty.int 64), (Operand.reg "%nxp"))]
      ],
      term := Term.br "NodeBlock29" },
    { name := "NodeBlock29",
      instrs := [
      Instr.icmp "%Pivot30" IPred.slt 32 (Operand.reg "%call243") (Operand.imm (.int 32 (BitVec.ofNat 32 1)))
      ],
      term := Term.condbr (Operand.reg "%Pivot30") "do.body246" "LeafBlock27" },
    { name := "LeafBlock27",
      instrs := [
      Instr.icmp "%SwitchLeaf28" IPred.eq 32 (Operand.reg "%call243") (Operand.imm (.int 32 (BitVec.ofNat 32 1)))
      ],
      term := Term.condbr (Operand.reg "%SwitchLeaf28") "do.body254" "for.cond266.preheader" },
    { name := "for.cond266.preheader",
      instrs := [
      Instr.load "%31" (Ty.int 64) (Operand.reg "%outn205"),
      Instr.icmp "%cmp2671048.not" IPred.eq 64 (Operand.reg "%31") (Operand.imm (.int 64 (BitVec.ofNat 64 0)))
      ],
      term := Term.condbr (Operand.reg "%cmp2671048.not") "for.cond.cleanup269" "for.body270.preheader" },
    { name := "for.body270.preheader",
      instrs := [
      Instr.binop "%xtraiter" BinOp.and 64 (Operand.reg "%31") (Operand.imm (.int 64 (BitVec.ofNat 64 7))),
      Instr.icmp "%32" IPred.ult 64 (Operand.reg "%31") (Operand.imm (.int 64 (BitVec.ofNat 64 8)))
      ],
      term := Term.condbr (Operand.reg "%32") "for.cond.cleanup269.loopexit.unr-lcssa" "for.body270.preheader.new" },
    { name := "for.body270.preheader.new",
      instrs := [
      Instr.binop "%unroll_iter" BinOp.and 64 (Operand.reg "%31") (Operand.imm (.int 64 (BitVec.ofNat 64 18446744073709551608)))
      ],
      term := Term.br "for.body270" },
    { name := "do.body246",
      instrs := [
      Instr.store (Ty.int 64) (Operand.imm (.int 64 (BitVec.ofNat 64 0))) (Operand.reg "%tokens_out"),
      Instr.store (Ty.int 64) (Operand.imm (.int 64 (BitVec.ofNat 64 0))) (Operand.reg "%values_out"),
      Instr.store (Ty.int 64) (Operand.imm (.int 64 (BitVec.ofNat 64 0))) (Operand.reg "%sum_out"),
      Instr.load "%33" (Ty.int 64) (Operand.reg "%off")
      ],
      term := Term.br "cleanup287.thread" },
    { name := "do.body254",
      instrs := [
      Instr.binop "%add257" BinOp.add 32 (Operand.reg "%.lcssa1125") (Operand.imm (.int 32 (BitVec.ofNat 32 1))),
      Instr.zext "%conv258" 32 64 (Operand.reg "%add257"),
      Instr.binop "%or259" BinOp.add 64 (Operand.reg "%conv258") (Operand.imm (.int 64 (BitVec.ofNat 64 9223372036854775814))),
      Instr.binop "%add260" BinOp.add 64 (Operand.reg "%or259") (Operand.reg "%sub234")
      ],
      term := Term.br "cleanup287" },
    { name := "for.cond.cleanup269.loopexit.unr-lcssa",
      instrs := [
      Instr.phi "%add273.lcssa.ph" (Ty.int 64) [("for.body270.preheader", (Operand.imm .poison)), ("for.body270", (Operand.reg "%add273.7"))],
      Instr.phi "%i265.01050.unr" (Ty.int 64) [("for.body270.preheader", (Operand.imm (.int 64 (BitVec.ofNat 64 0)))), ("for.body270", (Operand.reg "%inc275.7"))],
      Instr.phi "%arena.51049.unr" (Ty.int 64) [("for.body270.preheader", (Operand.reg "%arena.0.ph1406")), ("for.body270", (Operand.reg "%add273.7"))],
      Instr.icmp "%lcmp.mod.not" IPred.eq 64 (Operand.reg "%xtraiter") (Operand.imm (.int 64 (BitVec.ofNat 64 0)))
      ],
      term := Term.condbr (Operand.reg "%lcmp.mod.not") "for.cond.cleanup269" "for.body270.epil" },
    { name := "for.body270.epil",
      instrs := [
      Instr.phi "%i265.01050.epil" (Ty.int 64) [("for.body270.epil", (Operand.reg "%inc275.epil")), ("for.cond.cleanup269.loopexit.unr-lcssa", (Operand.reg "%i265.01050.unr"))],
      Instr.phi "%arena.51049.epil" (Ty.int 64) [("for.body270.epil", (Operand.reg "%add273.epil")), ("for.cond.cleanup269.loopexit.unr-lcssa", (Operand.reg "%arena.51049.unr"))],
      Instr.phi "%epil.iter" (Ty.int 64) [("for.body270.epil", (Operand.reg "%epil.iter.next")), ("for.cond.cleanup269.loopexit.unr-lcssa", (Operand.imm (.int 64 (BitVec.ofNat 64 0))))],
      Instr.gep "%arrayidx271.epil" (Ty.int 8) (Operand.reg "%scratch") (Operand.reg "%i265.01050.epil"),
      Instr.load "%34" (Ty.int 8) (Operand.reg "%arrayidx271.epil"),
      Instr.zext "%conv272.epil" 8 64 (Operand.reg "%34"),
      Instr.binop "%add273.epil" BinOp.add 64 (Operand.reg "%arena.51049.epil") (Operand.reg "%conv272.epil"),
      Instr.binop "%inc275.epil" BinOp.add 64 (Operand.reg "%i265.01050.epil") (Operand.imm (.int 64 (BitVec.ofNat 64 1))),
      Instr.binop "%epil.iter.next" BinOp.add 64 (Operand.reg "%epil.iter") (Operand.imm (.int 64 (BitVec.ofNat 64 1))),
      Instr.icmp "%epil.iter.cmp.not" IPred.eq 64 (Operand.reg "%epil.iter.next") (Operand.reg "%xtraiter")
      ],
      term := Term.condbr (Operand.reg "%epil.iter.cmp.not") "for.cond.cleanup269" "for.body270.epil" },
    { name := "for.cond.cleanup269",
      instrs := [
      Instr.phi "%arena.5.lcssa" (Ty.int 64) [("for.cond266.preheader", (Operand.reg "%arena.0.ph1406")), ("for.cond.cleanup269.loopexit.unr-lcssa", (Operand.reg "%add273.lcssa.ph")), ("for.body270.epil", (Operand.reg "%add273.epil"))],
      Instr.binop "%add278" BinOp.add 64 (Operand.reg "%31") (Operand.reg "%alen.0.ph1405"),
      Instr.binop "%add281" BinOp.add 64 (Operand.reg "%alen.0.ph1405") (Operand.imm (.int 64 (BitVec.ofNat 64 6))),
      Instr.binop "%add282" BinOp.add 64 (Operand.reg "%add281") (Operand.reg "%31")
      ],
      term := Term.br "cleanup287" },
    { name := "for.body270",
      instrs := [
      Instr.phi "%i265.01050" (Ty.int 64) [("for.body270.preheader.new", (Operand.imm (.int 64 (BitVec.ofNat 64 0)))), ("for.body270", (Operand.reg "%inc275.7"))],
      Instr.phi "%arena.51049" (Ty.int 64) [("for.body270.preheader.new", (Operand.reg "%arena.0.ph1406")), ("for.body270", (Operand.reg "%add273.7"))],
      Instr.phi "%niter" (Ty.int 64) [("for.body270.preheader.new", (Operand.imm (.int 64 (BitVec.ofNat 64 0)))), ("for.body270", (Operand.reg "%niter.next.7"))],
      Instr.gep "%arrayidx271" (Ty.int 8) (Operand.reg "%scratch") (Operand.reg "%i265.01050"),
      Instr.load "%35" (Ty.int 8) (Operand.reg "%arrayidx271"),
      Instr.zext "%conv272" 8 64 (Operand.reg "%35"),
      Instr.binop "%add273" BinOp.add 64 (Operand.reg "%arena.51049") (Operand.reg "%conv272"),
      Instr.gep "%gep1651" (Ty.int 8) (Operand.reg "%invariant.gep1650") (Operand.reg "%i265.01050"),
      Instr.load "%36" (Ty.int 8) (Operand.reg "%gep1651"),
      Instr.zext "%conv272.1" 8 64 (Operand.reg "%36"),
      Instr.binop "%add273.1" BinOp.add 64 (Operand.reg "%add273") (Operand.reg "%conv272.1"),
      Instr.gep "%gep1653" (Ty.int 8) (Operand.reg "%invariant.gep1652") (Operand.reg "%i265.01050"),
      Instr.load "%37" (Ty.int 8) (Operand.reg "%gep1653"),
      Instr.zext "%conv272.2" 8 64 (Operand.reg "%37"),
      Instr.binop "%add273.2" BinOp.add 64 (Operand.reg "%add273.1") (Operand.reg "%conv272.2"),
      Instr.gep "%gep1655" (Ty.int 8) (Operand.reg "%invariant.gep1654") (Operand.reg "%i265.01050"),
      Instr.load "%38" (Ty.int 8) (Operand.reg "%gep1655"),
      Instr.zext "%conv272.3" 8 64 (Operand.reg "%38"),
      Instr.binop "%add273.3" BinOp.add 64 (Operand.reg "%add273.2") (Operand.reg "%conv272.3"),
      Instr.gep "%gep1657" (Ty.int 8) (Operand.reg "%invariant.gep1656") (Operand.reg "%i265.01050"),
      Instr.load "%39" (Ty.int 8) (Operand.reg "%gep1657"),
      Instr.zext "%conv272.4" 8 64 (Operand.reg "%39"),
      Instr.binop "%add273.4" BinOp.add 64 (Operand.reg "%add273.3") (Operand.reg "%conv272.4"),
      Instr.gep "%gep1659" (Ty.int 8) (Operand.reg "%invariant.gep1658") (Operand.reg "%i265.01050"),
      Instr.load "%40" (Ty.int 8) (Operand.reg "%gep1659"),
      Instr.zext "%conv272.5" 8 64 (Operand.reg "%40"),
      Instr.binop "%add273.5" BinOp.add 64 (Operand.reg "%add273.4") (Operand.reg "%conv272.5"),
      Instr.gep "%gep1661" (Ty.int 8) (Operand.reg "%invariant.gep1660") (Operand.reg "%i265.01050"),
      Instr.load "%41" (Ty.int 8) (Operand.reg "%gep1661"),
      Instr.zext "%conv272.6" 8 64 (Operand.reg "%41"),
      Instr.binop "%add273.6" BinOp.add 64 (Operand.reg "%add273.5") (Operand.reg "%conv272.6"),
      Instr.gep "%gep1663" (Ty.int 8) (Operand.reg "%invariant.gep1662") (Operand.reg "%i265.01050"),
      Instr.load "%42" (Ty.int 8) (Operand.reg "%gep1663"),
      Instr.zext "%conv272.7" 8 64 (Operand.reg "%42"),
      Instr.binop "%add273.7" BinOp.add 64 (Operand.reg "%add273.6") (Operand.reg "%conv272.7"),
      Instr.binop "%inc275.7" BinOp.add 64 (Operand.reg "%i265.01050") (Operand.imm (.int 64 (BitVec.ofNat 64 8))),
      Instr.binop "%niter.next.7" BinOp.add 64 (Operand.reg "%niter") (Operand.imm (.int 64 (BitVec.ofNat 64 8))),
      Instr.icmp "%niter.ncmp.7" IPred.eq 64 (Operand.reg "%niter.next.7") (Operand.reg "%unroll_iter")
      ],
      term := Term.condbr (Operand.reg "%niter.ncmp.7") "for.cond.cleanup269.loopexit.unr-lcssa" "for.body270" },
    { name := "cleanup287.thread",
      instrs := [
      Instr.phi "%idxprom.lcssa1109.lcssa.sink" (Ty.int 64) [("if.then209", (Operand.reg "%idxprom.lcssa1109")), ("if.then223", (Operand.reg "%idxprom.lcssa1109")), ("do.body246", (Operand.reg "%33"))],
      Instr.store (Ty.int 64) (Operand.reg "%idxprom.lcssa1109.lcssa.sink") (Operand.reg "%err"),
      Instr.callVoid "llvm.lifetime.end.p0" [((Ty.int 64), (Operand.imm (.int 64 (BitVec.ofNat 64 8)))), (Ty.ptr, (Operand.reg "%outn205"))]
      ],
      term := Term.br "cleanup580" },
    { name := "cleanup287",
      instrs := [
      Instr.phi "%alen.4" (Ty.int 64) [("do.body254", (Operand.reg "%alen.0.ph1405")), ("for.cond.cleanup269", (Operand.reg "%add278"))],
      Instr.phi "%arena.6" (Ty.int 64) [("do.body254", (Operand.reg "%arena.0.ph1406")), ("for.cond.cleanup269", (Operand.reg "%arena.5.lcssa"))],
      Instr.phi "%add260.pn" (Ty.int 64) [("do.body254", (Operand.reg "%add260")), ("for.cond.cleanup269", (Operand.reg "%add282"))],
      Instr.binop "%tokens.4" BinOp.add 64 (Operand.reg "%tokens.0.lcssa1075") (Operand.imm (.int 64 (BitVec.ofNat 64 1))),
      Instr.binop "%terms.4" BinOp.add 64 (Operand.reg "%add260.pn") (Operand.reg "%terms.0.lcssa1081"),
      Instr.callVoid "llvm.lifetime.end.p0" [((Ty.int 64), (Operand.imm (.int 64 (BitVec.ofNat 64 8)))), (Ty.ptr, (Operand.reg "%outn205"))]
      ],
      term := Term.br "after_value" },
    { name := "expect_colon",
      instrs := [
      Instr.phi "%alen.2" (Ty.int 64) [("do.body172", (Operand.reg "%alen.1")), ("for.cond.cleanup", (Operand.reg "%add187"))],
      Instr.phi "%arena.3" (Ty.int 64) [("do.body172", (Operand.reg "%arena.1")), ("for.cond.cleanup", (Operand.reg "%arena.2.lcssa"))],
      Instr.phi "%add177.pn" (Ty.int 64) [("do.body172", (Operand.reg "%add177")), ("for.cond.cleanup", (Operand.reg "%add191"))],
      Instr.callVoid "llvm.lifetime.end.p0" [((Ty.int 64), (Operand.imm (.int 64 (BitVec.ofNat 64 8)))), (Ty.ptr, (Operand.reg "%outn"))],
      Instr.icmp "%cmp295.not" IPred.ult 64 (Operand.reg "%inc137") (Operand.reg "%nep")
      ],
      term := Term.condbr (Operand.reg "%cmp295.not") "if.end303" "if.then297" },
    { name := "if.then297",
      instrs := [
      Instr.store (Ty.int 64) (Operand.imm (.int 64 (BitVec.ofNat 64 0))) (Operand.reg "%tokens_out"),
      Instr.store (Ty.int 64) (Operand.imm (.int 64 (BitVec.ofNat 64 0))) (Operand.reg "%values_out"),
      Instr.store (Ty.int 64) (Operand.imm (.int 64 (BitVec.ofNat 64 0))) (Operand.reg "%sum_out"),
      Instr.store (Ty.int 64) (Operand.reg "%n") (Operand.reg "%err")
      ],
      term := Term.br "cleanup580" },
    { name := "if.end303",
      instrs := [
      Instr.binop "%terms.2" BinOp.add 64 (Operand.reg "%add177.pn") (Operand.reg "%terms.1"),
      Instr.binop "%tokens.2" BinOp.add 64 (Operand.reg "%tokens.1") (Operand.imm (.int 64 (BitVec.ofNat 64 1))),
      Instr.binop "%inc304" BinOp.add 64 (Operand.reg "%k.1.in") (Operand.imm (.int 64 (BitVec.ofNat 64 4))),
      Instr.gep "%arrayidx305" (Ty.int 32) (Operand.reg "%ep") (Operand.reg "%inc137"),
      Instr.load "%43" (Ty.int 32) (Operand.reg "%arrayidx305"),
      Instr.zext "%idxprom306" 32 64 (Operand.reg "%43"),
      Instr.gep "%arrayidx307" (Ty.int 8) (Operand.reg "%b") (Operand.reg "%idxprom306"),
      Instr.load "%44" (Ty.int 8) (Operand.reg "%arrayidx307"),
      Instr.icmp "%cmp309.not" IPred.eq 8 (Operand.reg "%44") (Operand.imm (.int 8 (BitVec.ofNat 8 58)))
      ],
      term := Term.condbr (Operand.reg "%cmp309.not") "value.outer.backedge" "if.then311" },
    { name := "value.outer.backedge",
      instrs := [
      Instr.phi "%frame.0.ph.be" (Ty.int 8) [("LeafBlock37", (Operand.reg "%frame.6")), ("if.end303", (Operand.imm (.int 8 (BitVec.ofNat 8 0))))],
      Instr.phi "%sp.0.ph.be" (Ty.int 32) [("LeafBlock37", (Operand.reg "%sp.4")), ("if.end303", (Operand.reg "%sp.1"))],
      Instr.phi "%k.0.ph.be" (Ty.int 64) [("LeafBlock37", (Operand.reg "%inc379")), ("if.end303", (Operand.reg "%inc304"))],
      Instr.phi "%alen.0.ph.be" (Ty.int 64) [("LeafBlock37", (Operand.reg "%alen.8")), ("if.end303", (Operand.reg "%alen.2"))],
      Instr.phi "%arena.0.ph.be" (Ty.int 64) [("LeafBlock37", (Operand.reg "%arena.10")), ("if.end303", (Operand.reg "%arena.3"))],
      Instr.phi "%terms.0.ph.be" (Ty.int 64) [("LeafBlock37", (Operand.reg "%terms.8")), ("if.end303", (Operand.reg "%terms.2"))],
      Instr.phi "%tokens.0.ph.be" (Ty.int 64) [("LeafBlock37", (Operand.reg "%tokens.8")), ("if.end303", (Operand.reg "%tokens.2"))],
      Instr.zext "%45" 32 64 (Operand.reg "%sp.0.ph.be"),
      Instr.icmp "%umax.max" IPred.ugt 32 (Operand.reg "%sp.0.ph.be") (Operand.imm (.int 32 (BitVec.ofNat 32 520))),
      Instr.select "%umax" (Ty.int 32) (Operand.reg "%umax.max") (Operand.reg "%sp.0.ph.be") (Operand.imm (.int 32 (BitVec.ofNat 32 520))),
      Instr.zext "%wide.trip.count" 32 64 (Operand.reg "%umax"),
      Instr.icmp "%cmp.not.peel" IPred.ult 64 (Operand.reg "%k.0.ph.be") (Operand.reg "%nep")
      ],
      term := Term.condbr (Operand.reg "%cmp.not.peel") "if.end.peel" "if.then" },
    { name := "if.then311",
      instrs := [
      Instr.store (Ty.int 64) (Operand.imm (.int 64 (BitVec.ofNat 64 0))) (Operand.reg "%tokens_out"),
      Instr.store (Ty.int 64) (Operand.imm (.int 64 (BitVec.ofNat 64 0))) (Operand.reg "%values_out"),
      Instr.store (Ty.int 64) (Operand.imm (.int 64 (BitVec.ofNat 64 0))) (Operand.reg "%sum_out"),
      Instr.store (Ty.int 64) (Operand.reg "%idxprom306") (Operand.reg "%err")
      ],
      term := Term.br "cleanup580" },
    { name := "if.then321",
      instrs := [
      Instr.store (Ty.int 64) (Operand.imm (.int 64 (BitVec.ofNat 64 0))) (Operand.reg "%tokens_out"),
      Instr.store (Ty.int 64) (Operand.imm (.int 64 (BitVec.ofNat 64 0))) (Operand.reg "%values_out"),
      Instr.store (Ty.int 64) (Operand.imm (.int 64 (BitVec.ofNat 64 0))) (Operand.reg "%sum_out"),
      Instr.store (Ty.int 64) (Operand.reg "%n") (Operand.reg "%err")
      ],
      term := Term.br "cleanup580" },
    { name := "if.end327",
      instrs := [
      Instr.gep "%arrayidx328" (Ty.int 32) (Operand.reg "%ep") (Operand.reg "%inc"),
      Instr.load "%46" (Ty.int 32) (Operand.reg "%arrayidx328"),
      Instr.zext "%idxprom329" 32 64 (Operand.reg "%46"),
      Instr.gep "%arrayidx330" (Ty.int 8) (Operand.reg "%b") (Operand.reg "%idxprom329"),
      Instr.load "%47" (Ty.int 8) (Operand.reg "%arrayidx330"),
      Instr.icmp "%cmp332" IPred.eq 8 (Operand.reg "%47") (Operand.imm (.int 8 (BitVec.ofNat 8 93)))
      ],
      term := Term.condbr (Operand.reg "%cmp332") "if.then334.loopexit" "if.end" },
    { name := "if.then334.loopexit",
      instrs := [
      Instr.trunc "%48" 64 32 (Operand.reg "%indvars.iv")
      ],
      term := Term.br "if.then334" },
    { name := "if.then334",
      instrs := [
      Instr.phi "%sp.0.lcssa1096.wide" (Ty.int 32) [("if.end327.peel", (Operand.reg "%sp.0.ph1403")), ("if.then334.loopexit", (Operand.reg "%48"))],
      Instr.phi "%k.0.lcssa1090" (Ty.int 64) [("if.end327.peel", (Operand.reg "%k.0.ph1404")), ("if.then334.loopexit", (Operand.reg "%k.0"))],
      Instr.phi "%terms.0.lcssa1084" (Ty.int 64) [("if.end327.peel", (Operand.reg "%terms.0.ph1407")), ("if.then334.loopexit", (Operand.reg "%terms.0"))],
      Instr.phi "%tokens.0.lcssa1078" (Ty.int 64) [("if.end327.peel", (Operand.reg "%tokens.0.ph1408")), ("if.then334.loopexit", (Operand.reg "%tokens.0"))],
      Instr.binop "%inc335" BinOp.add 64 (Operand.reg "%k.0.lcssa1090") (Operand.imm (.int 64 (BitVec.ofNat 64 2))),
      Instr.binop "%inc337" BinOp.add 64 (Operand.reg "%tokens.0.lcssa1078") (Operand.imm (.int 64 (BitVec.ofNat 64 2))),
      Instr.binop "%add338" BinOp.add 64 (Operand.reg "%terms.0.lcssa1084") (Operand.imm (.int 64 (BitVec.ofNat 64 7)))
      ],
      term := Term.br "close_arr" },
    { name := "close_obj",
      instrs := [
      Instr.phi "%sp.2" (Ty.int 32) [("if.then81", (Operand.reg "%inc24")), ("do.body391", (Operand.reg "%sp.4"))],
      Instr.phi "%k.4" (Ty.int 64) [("if.then81", (Operand.reg "%inc82")), ("do.body391", (Operand.reg "%inc379"))],
      Instr.phi "%alen.6" (Ty.int 64) [("if.then81", (Operand.reg "%alen.0.ph1405")), ("do.body391", (Operand.reg "%alen.8"))],
      Instr.phi "%arena.8" (Ty.int 64) [("if.then81", (Operand.reg "%arena.0.ph1406")), ("do.body391", (Operand.reg "%arena.10"))],
      Instr.phi "%terms.6" (Ty.int 64) [("if.then81", (Operand.reg "%add85")), ("do.body391", (Operand.reg "%add393"))],
      Instr.phi "%tokens.6" (Ty.int 64) [("if.then81", (Operand.reg "%inc84")), ("do.body391", (Operand.reg "%inc392"))],
      Instr.binop "%dec" BinOp.add 32 (Operand.reg "%sp.2") (Operand.imm (.int 32 (BitVec.ofNat 32 4294967295))),
      Instr.icmp "%tobool342.not" IPred.eq 32 (Operand.reg "%dec") (Operand.imm (.int 32 (BitVec.ofNat 32 0)))
      ],
      term := Term.condbr (Operand.reg "%tobool342.not") "after_value" "if.then343" },
    { name := "if.then343",
      instrs := [
      Instr.binop "%sub344" BinOp.add 32 (Operand.reg "%sp.2") (Operand.imm (.int 32 (BitVec.ofNat 32 4294967294))),
      Instr.zext "%idxprom345" 32 64 (Operand.reg "%sub344"),
      Instr.gep "%arrayidx346" (Ty.int 8) (Operand.reg "%stk") (Operand.reg "%idxprom345"),
      Instr.load "%49" (Ty.int 8) (Operand.reg "%arrayidx346")
      ],
      term := Term.br "after_value" },
    { name := "close_arr",
      instrs := [
      Instr.phi "%frame.4" (Ty.int 8) [("do.body417", (Operand.reg "%frame.6")), ("if.then334", (Operand.imm (.int 8 (BitVec.ofNat 8 1))))],
      Instr.phi "%sp.3" (Ty.int 32) [("do.body417", (Operand.reg "%54")), ("if.then334", (Operand.reg "%sp.0.lcssa1096.wide"))],
      Instr.phi "%k.5" (Ty.int 64) [("do.body417", (Operand.reg "%inc379")), ("if.then334", (Operand.reg "%inc335"))],
      Instr.phi "%alen.7" (Ty.int 64) [("do.body417", (Operand.reg "%alen.8")), ("if.then334", (Operand.reg "%alen.0.ph1405"))],
      Instr.phi "%arena.9" (Ty.int 64) [("do.body417", (Operand.reg "%arena.10")), ("if.then334", (Operand.reg "%arena.0.ph1406"))],
      Instr.phi "%terms.7" (Ty.int 64) [("do.body417", (Operand.reg "%add419")), ("if.then334", (Operand.reg "%add338"))],
      Instr.phi "%tokens.7" (Ty.int 64) [("do.body417", (Operand.reg "%inc418")), ("if.then334", (Operand.reg "%inc337"))],
      Instr.icmp "%tobool349.not" IPred.eq 32 (Operand.reg "%sp.3") (Operand.imm (.int 32 (BitVec.ofNat 32 0)))
      ],
      term := Term.condbr (Operand.reg "%tobool349.not") "after_value" "if.then350" },
    { name := "if.then350",
      instrs := [
      Instr.binop "%sub351" BinOp.add 32 (Operand.reg "%sp.3") (Operand.imm (.int 32 (BitVec.ofNat 32 4294967295))),
      Instr.zext "%idxprom352" 32 64 (Operand.reg "%sub351"),
      Instr.gep "%arrayidx353" (Ty.int 8) (Operand.reg "%stk") (Operand.reg "%idxprom352"),
      Instr.load "%50" (Ty.int 8) (Operand.reg "%arrayidx353")
      ],
      term := Term.br "after_value" },
    { name := "after_value",
      instrs := [
      Instr.phi "%frame.6" (Ty.int 8) [("cleanup287", (Operand.reg "%frame.0.lcssa1099")), ("if.then343", (Operand.reg "%49")), ("close_obj", (Operand.imm (.int 8 (BitVec.ofNat 8 0)))), ("if.then350", (Operand.reg "%50")), ("close_arr", (Operand.reg "%frame.4")), ("if.end545", (Operand.reg "%frame.0.lcssa1097")), ("while.body557", (Operand.reg "%frame.0.lcssa1097"))],
      Instr.phi "%sp.4" (Ty.int 32) [("cleanup287", (Operand.reg "%sp.0.lcssa1093.wide")), ("if.then343", (Operand.reg "%dec")), ("close_obj", (Operand.reg "%dec")), ("if.then350", (Operand.reg "%sp.3")), ("close_arr", (Operand.reg "%sp.3")), ("if.end545", (Operand.reg "%sp.0.lcssa1091.wide")), ("while.body557", (Operand.reg "%sp.0.lcssa1091.wide"))],
      Instr.phi "%k.6" (Ty.int 64) [("cleanup287", (Operand.reg "%inc217")), ("if.then343", (Operand.reg "%k.4")), ("close_obj", (Operand.reg "%k.4")), ("if.then350", (Operand.reg "%k.5")), ("close_arr", (Operand.reg "%k.5")), ("if.end545", (Operand.reg "%inc.lcssa")), ("while.body557", (Operand.reg "%inc.lcssa"))],
      Instr.phi "%alen.8" (Ty.int 64) [("cleanup287", (Operand.reg "%alen.4")), ("if.then343", (Operand.reg "%alen.6")), ("close_obj", (Operand.reg "%alen.6")), ("if.then350", (Operand.reg "%alen.7")), ("close_arr", (Operand.reg "%alen.7")), ("if.end545", (Operand.reg "%alen.0.ph1405")), ("while.body557", (Operand.reg "%alen.0.ph1405"))],
      Instr.phi "%arena.10" (Ty.int 64) [("cleanup287", (Operand.reg "%arena.6")), ("if.then343", (Operand.reg "%arena.8")), ("close_obj", (Operand.reg "%arena.8")), ("if.then350", (Operand.reg "%arena.9")), ("close_arr", (Operand.reg "%arena.9")), ("if.end545", (Operand.reg "%arena.0.ph1406")), ("while.body557", (Operand.reg "%arena.0.ph1406"))],
      Instr.phi "%terms.8" (Ty.int 64) [("cleanup287", (Operand.reg "%terms.4")), ("if.then343", (Operand.reg "%terms.6")), ("close_obj", (Operand.reg "%terms.6")), ("if.then350", (Operand.reg "%terms.7")), ("close_arr", (Operand.reg "%terms.7")), ("if.end545", (Operand.reg "%terms.12")), ("while.body557", (Operand.reg "%terms.12"))],
      Instr.phi "%tokens.8" (Ty.int 64) [("cleanup287", (Operand.reg "%tokens.4")), ("if.then343", (Operand.reg "%tokens.6")), ("close_obj", (Operand.reg "%tokens.6")), ("if.then350", (Operand.reg "%tokens.7")), ("close_arr", (Operand.reg "%tokens.7")), ("if.end545", (Operand.reg "%tokens.12")), ("while.body557", (Operand.reg "%tokens.12"))],
      Instr.icmp "%cmp355" IPred.eq 32 (Operand.reg "%sp.4") (Operand.imm (.int 32 (BitVec.ofNat 32 0))),
      Instr.icmp "%cmp358" IPred.ult 64 (Operand.reg "%k.6") (Operand.reg "%nep")
      ],
      term := Term.condbr (Operand.reg "%cmp355") "if.then357" "if.end369" },
    { name := "if.then357",
      instrs := [
      
      ],
      term := Term.condbr (Operand.reg "%cmp358") "if.then360" "accept" },
    { name := "if.then360",
      instrs := [
      Instr.gep "%arrayidx361" (Ty.int 32) (Operand.reg "%ep") (Operand.reg "%k.6"),
      Instr.load "%51" (Ty.int 32) (Operand.reg "%arrayidx361"),
      Instr.zext "%conv362" 32 64 (Operand.reg "%51"),
      Instr.store (Ty.int 64) (Operand.imm (.int 64 (BitVec.ofNat 64 0))) (Operand.reg "%tokens_out"),
      Instr.store (Ty.int 64) (Operand.imm (.int 64 (BitVec.ofNat 64 0))) (Operand.reg "%values_out"),
      Instr.store (Ty.int 64) (Operand.imm (.int 64 (BitVec.ofNat 64 0))) (Operand.reg "%sum_out"),
      Instr.store (Ty.int 64) (Operand.reg "%conv362") (Operand.reg "%err")
      ],
      term := Term.br "cleanup580" },
    { name := "if.end369",
      instrs := [
      
      ],
      term := Term.condbr (Operand.reg "%cmp358") "if.end378" "if.then372" },
    { name := "if.then372",
      instrs := [
      Instr.store (Ty.int 64) (Operand.imm (.int 64 (BitVec.ofNat 64 0))) (Operand.reg "%tokens_out"),
      Instr.store (Ty.int 64) (Operand.imm (.int 64 (BitVec.ofNat 64 0))) (Operand.reg "%values_out"),
      Instr.store (Ty.int 64) (Operand.imm (.int 64 (BitVec.ofNat 64 0))) (Operand.reg "%sum_out"),
      Instr.store (Ty.int 64) (Operand.reg "%n") (Operand.reg "%err")
      ],
      term := Term.br "cleanup580" },
    { name := "if.end378",
      instrs := [
      Instr.binop "%inc379" BinOp.add 64 (Operand.reg "%k.6") (Operand.imm (.int 64 (BitVec.ofNat 64 1))),
      Instr.gep "%arrayidx380" (Ty.int 32) (Operand.reg "%ep") (Operand.reg "%k.6"),
      Instr.load "%52" (Ty.int 32) (Operand.reg "%arrayidx380"),
      Instr.icmp "%cmp382" IPred.eq 8 (Operand.reg "%frame.6") (Operand.imm (.int 8 (BitVec.ofNat 8 0))),
      Instr.zext "%idxprom385" 32 64 (Operand.reg "%52"),
      Instr.gep "%arrayidx386" (Ty.int 8) (Operand.reg "%b") (Operand.reg "%idxprom385"),
      Instr.load "%53" (Ty.int 8) (Operand.reg "%arrayidx386")
      ],
      term := Term.condbr (Operand.reg "%cmp382") "if.then384" "if.end410" },
    { name := "if.then384",
      instrs := [
      
      ],
      term := Term.br "NodeBlock35" },
    { name := "NodeBlock35",
      instrs := [
      Instr.icmp "%Pivot36" IPred.slt 8 (Operand.reg "%53") (Operand.imm (.int 8 (BitVec.ofNat 8 125)))
      ],
      term := Term.condbr (Operand.reg "%Pivot36") "LeafBlock31" "LeafBlock33" },
    { name := "LeafBlock33",
      instrs := [
      Instr.icmp "%SwitchLeaf34" IPred.eq 8 (Operand.reg "%53") (Operand.imm (.int 8 (BitVec.ofNat 8 125)))
      ],
      term := Term.condbr (Operand.reg "%SwitchLeaf34") "do.body391" "if.then402" },
    { name := "LeafBlock31",
      instrs := [
      Instr.icmp "%SwitchLeaf32" IPred.eq 8 (Operand.reg "%53") (Operand.imm (.int 8 (BitVec.ofNat 8 44)))
      ],
      term := Term.condbr (Operand.reg "%SwitchLeaf32") "if.end409" "if.then402" },
    { name := "do.body391",
      instrs := [
      Instr.binop "%inc392" BinOp.add 64 (Operand.reg "%tokens.8") (Operand.imm (.int 64 (BitVec.ofNat 64 1))),
      Instr.binop "%add393" BinOp.add 64 (Operand.reg "%terms.8") (Operand.imm (.int 64 (BitVec.ofNat 64 2)))
      ],
      term := Term.br "close_obj" },
    { name := "if.then402",
      instrs := [
      Instr.store (Ty.int 64) (Operand.imm (.int 64 (BitVec.ofNat 64 0))) (Operand.reg "%tokens_out"),
      Instr.store (Ty.int 64) (Operand.imm (.int 64 (BitVec.ofNat 64 0))) (Operand.reg "%values_out"),
      Instr.store (Ty.int 64) (Operand.imm (.int 64 (BitVec.ofNat 64 0))) (Operand.reg "%sum_out"),
      Instr.store (Ty.int 64) (Operand.reg "%idxprom385") (Operand.reg "%err")
      ],
      term := Term.br "cleanup580" },
    { name := "if.end409",
      instrs := [
      Instr.icmp "%cmp103.not" IPred.ult 64 (Operand.reg "%inc379") (Operand.reg "%nep")
      ],
      term := Term.condbr (Operand.reg "%cmp103.not") "if.end111" "if.then105" },
    { name := "if.end410",
      instrs := [
      
      ],
      term := Term.br "NodeBlock41" },
    { name := "NodeBlock41",
      instrs := [
      Instr.icmp "%Pivot42" IPred.slt 8 (Operand.reg "%53") (Operand.imm (.int 8 (BitVec.ofNat 8 93)))
      ],
      term := Term.condbr (Operand.reg "%Pivot42") "LeafBlock37" "LeafBlock39" },
    { name := "LeafBlock39",
      instrs := [
      Instr.icmp "%SwitchLeaf40" IPred.eq 8 (Operand.reg "%53") (Operand.imm (.int 8 (BitVec.ofNat 8 93)))
      ],
      term := Term.condbr (Operand.reg "%SwitchLeaf40") "do.body417" "if.then428" },
    { name := "LeafBlock37",
      instrs := [
      Instr.icmp "%SwitchLeaf38" IPred.eq 8 (Operand.reg "%53") (Operand.imm (.int 8 (BitVec.ofNat 8 44)))
      ],
      term := Term.condbr (Operand.reg "%SwitchLeaf38") "value.outer.backedge" "if.then428" },
    { name := "do.body417",
      instrs := [
      Instr.binop "%inc418" BinOp.add 64 (Operand.reg "%tokens.8") (Operand.imm (.int 64 (BitVec.ofNat 64 1))),
      Instr.binop "%add419" BinOp.add 64 (Operand.reg "%terms.8") (Operand.imm (.int 64 (BitVec.ofNat 64 4))),
      Instr.binop "%54" BinOp.add 32 (Operand.reg "%sp.4") (Operand.imm (.int 32 (BitVec.ofNat 32 4294967295)))
      ],
      term := Term.br "close_arr" },
    { name := "if.then428",
      instrs := [
      Instr.store (Ty.int 64) (Operand.imm (.int 64 (BitVec.ofNat 64 0))) (Operand.reg "%tokens_out"),
      Instr.store (Ty.int 64) (Operand.imm (.int 64 (BitVec.ofNat 64 0))) (Operand.reg "%values_out"),
      Instr.store (Ty.int 64) (Operand.imm (.int 64 (BitVec.ofNat 64 0))) (Operand.reg "%sum_out"),
      Instr.store (Ty.int 64) (Operand.reg "%idxprom385") (Operand.reg "%err")
      ],
      term := Term.br "cleanup580" },
    { name := "scalar.loopexit",
      instrs := [
      Instr.zext "%idxprom.le1291" 32 64 (Operand.reg "%8"),
      Instr.trunc "%55" 64 32 (Operand.reg "%indvars.iv")
      ],
      term := Term.br "scalar" },
    { name := "scalar",
      instrs := [
      Instr.phi "%inc.lcssa" (Ty.int 64) [("scalar.loopexit", (Operand.reg "%inc")), ("LeafBlock", (Operand.reg "%inc.peel")), ("LeafBlock1", (Operand.reg "%inc.peel")), ("LeafBlock3", (Operand.reg "%inc.peel"))],
      Instr.phi "%idxprom.lcssa" (Ty.int 64) [("scalar.loopexit", (Operand.reg "%idxprom.le1291")), ("LeafBlock", (Operand.reg "%idxprom.peel")), ("LeafBlock1", (Operand.reg "%idxprom.peel")), ("LeafBlock3", (Operand.reg "%idxprom.peel"))],
      Instr.phi "%.lcssa" (Ty.int 8) [("scalar.loopexit", (Operand.reg "%7")), ("LeafBlock", (Operand.reg "%3")), ("LeafBlock1", (Operand.reg "%3")), ("LeafBlock3", (Operand.reg "%3"))],
      Instr.phi "%frame.0.lcssa1097" (Ty.int 8) [("scalar.loopexit", (Operand.imm (.int 8 (BitVec.ofNat 8 1)))), ("LeafBlock", (Operand.reg "%frame.0.ph1402")), ("LeafBlock1", (Operand.reg "%frame.0.ph1402")), ("LeafBlock3", (Operand.reg "%frame.0.ph1402"))],
      Instr.phi "%sp.0.lcssa1091.wide" (Ty.int 32) [("scalar.loopexit", (Operand.reg "%55")), ("LeafBlock", (Operand.reg "%sp.0.ph1403")), ("LeafBlock1", (Operand.reg "%sp.0.ph1403")), ("LeafBlock3", (Operand.reg "%sp.0.ph1403"))],
      Instr.phi "%terms.0.lcssa1079" (Ty.int 64) [("scalar.loopexit", (Operand.reg "%terms.0")), ("LeafBlock", (Operand.reg "%terms.0.ph1407")), ("LeafBlock1", (Operand.reg "%terms.0.ph1407")), ("LeafBlock3", (Operand.reg "%terms.0.ph1407"))],
      Instr.phi "%tokens.0.lcssa1073" (Ty.int 64) [("scalar.loopexit", (Operand.reg "%tokens.0")), ("LeafBlock", (Operand.reg "%tokens.0.ph1408")), ("LeafBlock1", (Operand.reg "%tokens.0.ph1408")), ("LeafBlock3", (Operand.reg "%tokens.0.ph1408"))],
      Instr.gep "%arrayidx6.le1046" (Ty.int 8) (Operand.reg "%b") (Operand.reg "%idxprom.lcssa"),
      Instr.icmp "%cmp436" IPred.ult 64 (Operand.reg "%inc.lcssa") (Operand.reg "%nep")
      ],
      term := Term.condbr (Operand.reg "%cmp436") "cond.true" "cond.end" },
    { name := "cond.true",
      instrs := [
      Instr.gep "%arrayidx438" (Ty.int 32) (Operand.reg "%ep") (Operand.reg "%inc.lcssa"),
      Instr.load "%56" (Ty.int 32) (Operand.reg "%arrayidx438"),
      Instr.zext "%conv439" 32 64 (Operand.reg "%56")
      ],
      term := Term.br "cond.end" },
    { name := "cond.end",
      instrs := [
      Instr.phi "%cond" (Ty.int 64) [("cond.true", (Operand.reg "%conv439")), ("scalar", (Operand.reg "%n"))],
      Instr.icmp "%cmp443" IPred.ugt 64 (Operand.reg "%cond") (Operand.reg "%idxprom.lcssa")
      ],
      term := Term.condbr (Operand.reg "%cmp443") "land.lhs.true" "if.end457" },
    { name := "land.lhs.true",
      instrs := [
      Instr.gep "%gep1069" (Ty.int 8) (Operand.reg "%invariant.gep1068") (Operand.reg "%cond"),
      Instr.load "%57" (Ty.int 8) (Operand.reg "%gep1069")
      ],
      term := Term.br "NodeBlock51" },
    { name := "NodeBlock51",
      instrs := [
      Instr.icmp "%Pivot52" IPred.slt 8 (Operand.reg "%57") (Operand.imm (.int 8 (BitVec.ofNat 8 13)))
      ],
      term := Term.condbr (Operand.reg "%Pivot52") "LeafBlock43" "NodeBlock49" },
    { name := "NodeBlock49",
      instrs := [
      Instr.icmp "%Pivot50" IPred.slt 8 (Operand.reg "%57") (Operand.imm (.int 8 (BitVec.ofNat 8 32)))
      ],
      term := Term.condbr (Operand.reg "%Pivot50") "LeafBlock45" "LeafBlock47" },
    { name := "LeafBlock47",
      instrs := [
      Instr.icmp "%SwitchLeaf48" IPred.eq 8 (Operand.reg "%57") (Operand.imm (.int 8 (BitVec.ofNat 8 32)))
      ],
      term := Term.condbr (Operand.reg "%SwitchLeaf48") "land.rhs.preheader" "if.end457" },
    { name := "LeafBlock45",
      instrs := [
      Instr.icmp "%SwitchLeaf46" IPred.eq 8 (Operand.reg "%57") (Operand.imm (.int 8 (BitVec.ofNat 8 13)))
      ],
      term := Term.condbr (Operand.reg "%SwitchLeaf46") "land.rhs.preheader" "if.end457" },
    { name := "LeafBlock43",
      instrs := [
      Instr.binop "%.off" BinOp.add 8 (Operand.reg "%57") (Operand.imm (.int 8 (BitVec.ofNat 8 247))),
      Instr.icmp "%SwitchLeaf44" IPred.ule 8 (Operand.reg "%.off") (Operand.imm (.int 8 (BitVec.ofNat 8 1)))
      ],
      term := Term.condbr (Operand.reg "%SwitchLeaf44") "land.rhs.preheader" "if.end457" },
    { name := "land.rhs.preheader",
      instrs := [
      
      ],
      term := Term.br "land.rhs" },
    { name := "land.rhs",
      instrs := [
      Instr.phi "%ee.01053" (Ty.int 64) [("while.body", (Operand.reg "%inc456")), ("land.rhs.preheader", (Operand.reg "%idxprom.lcssa"))],
      Instr.gep "%arrayidx453" (Ty.int 8) (Operand.reg "%b") (Operand.reg "%ee.01053"),
      Instr.load "%58" (Ty.int 8) (Operand.reg "%arrayidx453")
      ],
      term := Term.br "NodeBlock62" },
    { name := "NodeBlock62",
      instrs := [
      Instr.icmp "%Pivot63" IPred.slt 8 (Operand.reg "%58") (Operand.imm (.int 8 (BitVec.ofNat 8 13)))
      ],
      term := Term.condbr (Operand.reg "%Pivot63") "LeafBlock53" "NodeBlock60" },
    { name := "NodeBlock60",
      instrs := [
      Instr.icmp "%Pivot61" IPred.slt 8 (Operand.reg "%58") (Operand.imm (.int 8 (BitVec.ofNat 8 32)))
      ],
      term := Term.condbr (Operand.reg "%Pivot61") "LeafBlock56" "LeafBlock58" },
    { name := "LeafBlock58",
      instrs := [
      Instr.icmp "%SwitchLeaf59" IPred.eq 8 (Operand.reg "%58") (Operand.imm (.int 8 (BitVec.ofNat 8 32)))
      ],
      term := Term.condbr (Operand.reg "%SwitchLeaf59") "if.end457" "while.body" },
    { name := "LeafBlock56",
      instrs := [
      Instr.icmp "%SwitchLeaf57" IPred.eq 8 (Operand.reg "%58") (Operand.imm (.int 8 (BitVec.ofNat 8 13)))
      ],
      term := Term.condbr (Operand.reg "%SwitchLeaf57") "if.end457" "while.body" },
    { name := "LeafBlock53",
      instrs := [
      Instr.binop "%.off54" BinOp.add 8 (Operand.reg "%58") (Operand.imm (.int 8 (BitVec.ofNat 8 247))),
      Instr.icmp "%SwitchLeaf55" IPred.ule 8 (Operand.reg "%.off54") (Operand.imm (.int 8 (BitVec.ofNat 8 1)))
      ],
      term := Term.condbr (Operand.reg "%SwitchLeaf55") "if.end457" "while.body" },
    { name := "while.body",
      instrs := [
      Instr.binop "%inc456" BinOp.add 64 (Operand.reg "%ee.01053") (Operand.imm (.int 64 (BitVec.ofNat 64 1))),
      Instr.icmp "%exitcond1170.not" IPred.eq 64 (Operand.reg "%inc456") (Operand.reg "%cond")
      ],
      term := Term.condbr (Operand.reg "%exitcond1170.not") "if.end457" "land.rhs" },
    { name := "if.end457",
      instrs := [
      Instr.phi "%ee.1" (Ty.int 64) [("cond.end", (Operand.reg "%idxprom.lcssa")), ("while.body", (Operand.reg "%cond")), ("LeafBlock53", (Operand.reg "%ee.01053")), ("LeafBlock56", (Operand.reg "%ee.01053")), ("LeafBlock58", (Operand.reg "%ee.01053")), ("LeafBlock43", (Operand.reg "%cond")), ("LeafBlock45", (Operand.reg "%cond")), ("LeafBlock47", (Operand.reg "%cond"))],
      Instr.store (Ty.int 64) (Operand.reg "%inc.lcssa") (Operand.reg "%k219"),
      Instr.icmp "%cmp462" IPred.eq 8 (Operand.reg "%.lcssa") (Operand.imm (.int 8 (BitVec.ofNat 8 45))),
      Instr.binop "%59" BinOp.add 8 (Operand.reg "%.lcssa") (Operand.imm (.int 8 (BitVec.ofNat 8 208))),
      Instr.icmp "%or.cond" IPred.ult 8 (Operand.reg "%59") (Operand.imm (.int 8 (BitVec.ofNat 8 10))),
      Instr.binop "%or.cond901" BinOp.or 1 (Operand.reg "%cmp462") (Operand.reg "%or.cond")
      ],
      term := Term.condbr (Operand.reg "%or.cond901") "if.then471" "if.else495" },
    { name := "if.then471",
      instrs := [
      Instr.callVoid "llvm.lifetime.start.p0" [((Ty.int 64), (Operand.imm (.int 64 (BitVec.ofNat 64 8)))), (Ty.ptr, (Operand.reg "%d"))],
      Instr.callVoid "llvm.lifetime.start.p0" [((Ty.int 64), (Operand.imm (.int 64 (BitVec.ofNat 64 8)))), (Ty.ptr, (Operand.reg "%ei"))],
      Instr.store (Ty.int 64) (Operand.imm (.int 64 (BitVec.ofNat 64 0))) (Operand.reg "%ei"),
      Instr.binop "%sub475" BinOp.sub 64 (Operand.reg "%ee.1") (Operand.reg "%idxprom.lcssa"),
      Instr.call "%call476" (Ty.int 32) "num_fast_el1" [(Ty.ptr, (Operand.reg "%arrayidx6.le1046")), ((Ty.int 64), (Operand.reg "%sub475")), (Ty.ptr, (Operand.reg "%d")), (Ty.ptr, (Operand.reg "%ei"))],
      Instr.icmp "%tobool477.not.not" IPred.eq 32 (Operand.reg "%call476") (Operand.imm (.int 32 (BitVec.ofNat 32 0)))
      ],
      term := Term.condbr (Operand.reg "%tobool477.not.not") "cleanup491.thread" "cleanup491" },
    { name := "cleanup491.thread",
      instrs := [
      Instr.load "%60" (Ty.int 64) (Operand.reg "%ei"),
      Instr.binop "%add480" BinOp.add 64 (Operand.reg "%60") (Operand.reg "%idxprom.lcssa"),
      Instr.store (Ty.int 64) (Operand.reg "%add480") (Operand.reg "%off"),
      Instr.callVoid "od_gap_recover" [(Ty.ptr, (Operand.reg "%c")), ((Ty.int 64), (Operand.reg "%idxprom.lcssa"))],
      Instr.store (Ty.int 64) (Operand.imm (.int 64 (BitVec.ofNat 64 0))) (Operand.reg "%tokens_out"),
      Instr.store (Ty.int 64) (Operand.imm (.int 64 (BitVec.ofNat 64 0))) (Operand.reg "%values_out"),
      Instr.store (Ty.int 64) (Operand.imm (.int 64 (BitVec.ofNat 64 0))) (Operand.reg "%sum_out"),
      Instr.load "%61" (Ty.int 64) (Operand.reg "%off"),
      Instr.store (Ty.int 64) (Operand.reg "%61") (Operand.reg "%err"),
      Instr.callVoid "llvm.lifetime.end.p0" [((Ty.int 64), (Operand.imm (.int 64 (BitVec.ofNat 64 8)))), (Ty.ptr, (Operand.reg "%ei"))],
      Instr.callVoid "llvm.lifetime.end.p0" [((Ty.int 64), (Operand.imm (.int 64 (BitVec.ofNat 64 8)))), (Ty.ptr, (Operand.reg "%d"))]
      ],
      term := Term.br "cleanup580" },
    { name := "cleanup491",
      instrs := [
      Instr.load "%62" (Ty.int 64) (Operand.reg "%d"),
      Instr.binop "%add489" BinOp.add 64 (Operand.reg "%62") (Operand.imm (.int 64 (BitVec.ofNat 64 7))),
      Instr.callVoid "llvm.lifetime.end.p0" [((Ty.int 64), (Operand.imm (.int 64 (BitVec.ofNat 64 8)))), (Ty.ptr, (Operand.reg "%ei"))],
      Instr.callVoid "llvm.lifetime.end.p0" [((Ty.int 64), (Operand.imm (.int 64 (BitVec.ofNat 64 8)))), (Ty.ptr, (Operand.reg "%d"))]
      ],
      term := Term.br "if.end545" },
    { name := "if.else495",
      instrs := [
      
      ],
      term := Term.br "NodeBlock72" },
    { name := "NodeBlock72",
      instrs := [
      Instr.icmp "%Pivot73" IPred.slt 8 (Operand.reg "%.lcssa") (Operand.imm (.int 8 (BitVec.ofNat 8 110)))
      ],
      term := Term.condbr (Operand.reg "%Pivot73") "LeafBlock64" "NodeBlock70" },
    { name := "NodeBlock70",
      instrs := [
      Instr.icmp "%Pivot71" IPred.slt 8 (Operand.reg "%.lcssa") (Operand.imm (.int 8 (BitVec.ofNat 8 116)))
      ],
      term := Term.condbr (Operand.reg "%Pivot71") "LeafBlock66" "LeafBlock68" },
    { name := "LeafBlock68",
      instrs := [
      Instr.icmp "%SwitchLeaf69" IPred.eq 8 (Operand.reg "%.lcssa") (Operand.imm (.int 8 (BitVec.ofNat 8 116)))
      ],
      term := Term.condbr (Operand.reg "%SwitchLeaf69") "if.end519" "if.else510" },
    { name := "LeafBlock66",
      instrs := [
      Instr.icmp "%SwitchLeaf67" IPred.eq 8 (Operand.reg "%.lcssa") (Operand.imm (.int 8 (BitVec.ofNat 8 110)))
      ],
      term := Term.condbr (Operand.reg "%SwitchLeaf67") "if.then509" "if.else510" },
    { name := "LeafBlock64",
      instrs := [
      Instr.icmp "%SwitchLeaf65" IPred.eq 8 (Operand.reg "%.lcssa") (Operand.imm (.int 8 (BitVec.ofNat 8 102)))
      ],
      term := Term.condbr (Operand.reg "%SwitchLeaf65") "if.then504" "if.else510" },
    { name := "if.then504",
      instrs := [
      
      ],
      term := Term.br "if.end519" },
    { name := "if.then509",
      instrs := [
      
      ],
      term := Term.br "if.end519" },
    { name := "if.else510",
      instrs := [
      Instr.store (Ty.int 64) (Operand.reg "%idxprom.lcssa") (Operand.reg "%off"),
      Instr.callVoid "od_gap_recover" [(Ty.ptr, (Operand.reg "%c")), ((Ty.int 64), (Operand.reg "%idxprom.lcssa"))],
      Instr.store (Ty.int 64) (Operand.imm (.int 64 (BitVec.ofNat 64 0))) (Operand.reg "%tokens_out"),
      Instr.store (Ty.int 64) (Operand.imm (.int 64 (BitVec.ofNat 64 0))) (Operand.reg "%values_out"),
      Instr.store (Ty.int 64) (Operand.imm (.int 64 (BitVec.ofNat 64 0))) (Operand.reg "%sum_out"),
      Instr.load "%63" (Ty.int 64) (Operand.reg "%off"),
      Instr.store (Ty.int 64) (Operand.reg "%63") (Operand.reg "%err")
      ],
      term := Term.br "cleanup580" },
    { name := "if.end519",
      instrs := [
      Instr.phi "%lit.0" (Ty.int 64) [("if.then504", (Operand.imm (.int 64 (BitVec.ofNat 64 435728179558)))), ("if.then509", (Operand.imm (.int 64 (BitVec.ofNat 64 1819047278)))), ("LeafBlock68", (Operand.imm (.int 64 (BitVec.ofNat 64 1702195828))))],
      Instr.phi "%exitcond38.not.i.3" (Ty.int 1) [("if.then504", (Operand.imm (.int 1 (BitVec.ofNat 1 0)))), ("if.then509", (Operand.imm (.int 1 (BitVec.ofNat 1 1)))), ("LeafBlock68", (Operand.imm (.int 1 (BitVec.ofNat 1 1))))],
      Instr.phi "%ln.0" (Ty.int 64) [("if.then504", (Operand.imm (.int 64 (BitVec.ofNat 64 5)))), ("if.then509", (Operand.imm (.int 64 (BitVec.ofNat 64 4)))), ("LeafBlock68", (Operand.imm (.int 64 (BitVec.ofNat 64 4))))],
      Instr.phi "%tag.0" (Ty.int 64) [("if.then504", (Operand.imm (.int 64 (BitVec.ofNat 64 9)))), ("if.then509", (Operand.imm (.int 64 (BitVec.ofNat 64 10)))), ("LeafBlock68", (Operand.imm (.int 64 (BitVec.ofNat 64 8))))],
      Instr.binop "%sub524" BinOp.sub 64 (Operand.reg "%ee.1") (Operand.reg "%idxprom.lcssa"),
      Instr.icmp "%exitcond.not.i" IPred.eq 64 (Operand.reg "%sub524") (Operand.imm (.int 64 (BitVec.ofNat 64 0)))
      ],
      term := Term.condbr (Operand.reg "%exitcond.not.i") "if.then527" "if.end.i" },
    { name := "for.body.i.1",
      instrs := [
      Instr.icmp "%exitcond.not.i.1" IPred.eq 64 (Operand.reg "%sub524") (Operand.imm (.int 64 (BitVec.ofNat 64 1)))
      ],
      term := Term.condbr (Operand.reg "%exitcond.not.i.1") "if.then527" "if.end.i.1" },
    { name := "if.end.i.1",
      instrs := [
      Instr.gep "%arrayidx.i.1" (Ty.int 8) (Operand.reg "%arrayidx6.le1046") (Operand.imm (.int 64 (BitVec.ofNat 64 1))),
      Instr.load "%64" (Ty.int 8) (Operand.reg "%arrayidx.i.1"),
      Instr.binop "%shr.i.1" BinOp.lshr 64 (Operand.reg "%lit.0") (Operand.imm (.int 64 (BitVec.ofNat 64 8))),
      Instr.trunc "%65" 64 8 (Operand.reg "%shr.i.1"),
      Instr.icmp "%cmp7.not.i.1" IPred.eq 8 (Operand.reg "%64") (Operand.reg "%65")
      ],
      term := Term.condbr (Operand.reg "%cmp7.not.i.1") "for.body.i.2" "if.then527" },
    { name := "for.body.i.2",
      instrs := [
      Instr.icmp "%exitcond.not.i.2" IPred.eq 64 (Operand.reg "%sub524") (Operand.imm (.int 64 (BitVec.ofNat 64 2)))
      ],
      term := Term.condbr (Operand.reg "%exitcond.not.i.2") "if.then527" "if.end.i.2" },
    { name := "if.end.i.2",
      instrs := [
      Instr.gep "%arrayidx.i.2" (Ty.int 8) (Operand.reg "%arrayidx6.le1046") (Operand.imm (.int 64 (BitVec.ofNat 64 2))),
      Instr.load "%66" (Ty.int 8) (Operand.reg "%arrayidx.i.2"),
      Instr.binop "%shr.i.2" BinOp.lshr 64 (Operand.reg "%lit.0") (Operand.imm (.int 64 (BitVec.ofNat 64 16))),
      Instr.trunc "%67" 64 8 (Operand.reg "%shr.i.2"),
      Instr.icmp "%cmp7.not.i.2" IPred.eq 8 (Operand.reg "%66") (Operand.reg "%67")
      ],
      term := Term.condbr (Operand.reg "%cmp7.not.i.2") "for.body.i.3" "if.then527" },
    { name := "for.body.i.3",
      instrs := [
      Instr.icmp "%exitcond.not.i.3" IPred.eq 64 (Operand.reg "%sub524") (Operand.imm (.int 64 (BitVec.ofNat 64 3)))
      ],
      term := Term.condbr (Operand.reg "%exitcond.not.i.3") "if.then527" "if.end.i.3" },
    { name := "if.end.i.3",
      instrs := [
      Instr.gep "%arrayidx.i.3" (Ty.int 8) (Operand.reg "%arrayidx6.le1046") (Operand.imm (.int 64 (BitVec.ofNat 64 3))),
      Instr.load "%68" (Ty.int 8) (Operand.reg "%arrayidx.i.3"),
      Instr.binop "%shr.i.3" BinOp.lshr 64 (Operand.reg "%lit.0") (Operand.imm (.int 64 (BitVec.ofNat 64 24))),
      Instr.trunc "%69" 64 8 (Operand.reg "%shr.i.3"),
      Instr.icmp "%cmp7.not.i.3" IPred.eq 8 (Operand.reg "%68") (Operand.reg "%69")
      ],
      term := Term.condbr (Operand.reg "%cmp7.not.i.3") "for.cond.i.3" "if.then527" },
    { name := "for.cond.i.3",
      instrs := [
      
      ],
      term := Term.condbr (Operand.reg "%exitcond38.not.i.3") "for.end.i" "for.body.i.4" },
    { name := "for.body.i.4",
      instrs := [
      Instr.icmp "%exitcond.not.i.4" IPred.eq 64 (Operand.reg "%sub524") (Operand.imm (.int 64 (BitVec.ofNat 64 4)))
      ],
      term := Term.condbr (Operand.reg "%exitcond.not.i.4") "if.then527" "if.end.i.4" },
    { name := "if.end.i.4",
      instrs := [
      Instr.gep "%arrayidx.i.4" (Ty.int 8) (Operand.reg "%arrayidx6.le1046") (Operand.imm (.int 64 (BitVec.ofNat 64 4))),
      Instr.load "%70" (Ty.int 8) (Operand.reg "%arrayidx.i.4"),
      Instr.binop "%shr.i.4" BinOp.lshr 64 (Operand.reg "%lit.0") (Operand.imm (.int 64 (BitVec.ofNat 64 32))),
      Instr.trunc "%71" 64 8 (Operand.reg "%shr.i.4"),
      Instr.icmp "%cmp7.not.i.4" IPred.eq 8 (Operand.reg "%70") (Operand.reg "%71")
      ],
      term := Term.condbr (Operand.reg "%cmp7.not.i.4") "for.end.i" "if.then527" },
    { name := "if.end.i",
      instrs := [
      Instr.load "%72" (Ty.int 8) (Operand.reg "%arrayidx6.le1046"),
      Instr.trunc "%73" 64 8 (Operand.reg "%lit.0"),
      Instr.icmp "%cmp7.not.i" IPred.eq 8 (Operand.reg "%72") (Operand.reg "%73")
      ],
      term := Term.condbr (Operand.reg "%cmp7.not.i") "for.body.i.1" "if.then527" },
    { name := "for.end.i",
      instrs := [
      Instr.icmp "%cmp13.not.i" IPred.eq 64 (Operand.reg "%sub524") (Operand.reg "%ln.0")
      ],
      term := Term.condbr (Operand.reg "%cmp13.not.i") "if.end545" "if.then527" },
    { name := "if.then527",
      instrs := [
      Instr.phi "%ei520.0.ph" (Ty.int 64) [("if.end519", (Operand.reg "%sub524")), ("if.end.i", (Operand.imm (.int 64 (BitVec.ofNat 64 0)))), ("for.body.i.1", (Operand.reg "%sub524")), ("if.end.i.1", (Operand.imm (.int 64 (BitVec.ofNat 64 1)))), ("for.body.i.2", (Operand.reg "%sub524")), ("if.end.i.2", (Operand.imm (.int 64 (BitVec.ofNat 64 2)))), ("for.body.i.3", (Operand.reg "%sub524")), ("if.end.i.3", (Operand.imm (.int 64 (BitVec.ofNat 64 3)))), ("for.body.i.4", (Operand.reg "%sub524")), ("if.end.i.4", (Operand.imm (.int 64 (BitVec.ofNat 64 4)))), ("for.end.i", (Operand.reg "%ln.0"))],
      Instr.binop "%add529" BinOp.add 64 (Operand.reg "%ei520.0.ph") (Operand.reg "%idxprom.lcssa"),
      Instr.store (Ty.int 64) (Operand.reg "%add529") (Operand.reg "%off"),
      Instr.callVoid "od_gap_recover" [(Ty.ptr, (Operand.reg "%c")), ((Ty.int 64), (Operand.reg "%idxprom.lcssa"))],
      Instr.store (Ty.int 64) (Operand.imm (.int 64 (BitVec.ofNat 64 0))) (Operand.reg "%tokens_out"),
      Instr.store (Ty.int 64) (Operand.imm (.int 64 (BitVec.ofNat 64 0))) (Operand.reg "%values_out"),
      Instr.store (Ty.int 64) (Operand.imm (.int 64 (BitVec.ofNat 64 0))) (Operand.reg "%sum_out"),
      Instr.load "%74" (Ty.int 64) (Operand.reg "%off"),
      Instr.store (Ty.int 64) (Operand.reg "%74") (Operand.reg "%err")
      ],
      term := Term.br "cleanup580" },
    { name := "if.end545",
      instrs := [
      Instr.phi "%add489.pn" (Ty.int 64) [("cleanup491", (Operand.reg "%add489")), ("for.end.i", (Operand.reg "%tag.0"))],
      Instr.binop "%tokens.12" BinOp.add 64 (Operand.reg "%tokens.0.lcssa1073") (Operand.imm (.int 64 (BitVec.ofNat 64 1))),
      Instr.binop "%terms.12" BinOp.add 64 (Operand.reg "%add489.pn") (Operand.reg "%terms.0.lcssa1079"),
      Instr.icmp "%cmp546" IPred.ult 64 (Operand.reg "%ee.1") (Operand.reg "%cond")
      ],
      term := Term.condbr (Operand.reg "%cmp546") "land.rhs552" "after_value" },
    { name := "land.rhs552",
      instrs := [
      Instr.phi "%q.01062" (Ty.int 64) [("while.body557", (Operand.reg "%inc558")), ("if.end545", (Operand.reg "%ee.1"))],
      Instr.gep "%arrayidx553" (Ty.int 8) (Operand.reg "%b") (Operand.reg "%q.01062"),
      Instr.load "%75" (Ty.int 8) (Operand.reg "%arrayidx553")
      ],
      term := Term.br "NodeBlock83" },
    { name := "NodeBlock83",
      instrs := [
      Instr.icmp "%Pivot84" IPred.slt 8 (Operand.reg "%75") (Operand.imm (.int 8 (BitVec.ofNat 8 13)))
      ],
      term := Term.condbr (Operand.reg "%Pivot84") "LeafBlock74" "NodeBlock81" },
    { name := "NodeBlock81",
      instrs := [
      Instr.icmp "%Pivot82" IPred.slt 8 (Operand.reg "%75") (Operand.imm (.int 8 (BitVec.ofNat 8 32)))
      ],
      term := Term.condbr (Operand.reg "%Pivot82") "LeafBlock77" "LeafBlock79" },
    { name := "LeafBlock79",
      instrs := [
      Instr.icmp "%SwitchLeaf80" IPred.eq 8 (Operand.reg "%75") (Operand.imm (.int 8 (BitVec.ofNat 8 32)))
      ],
      term := Term.condbr (Operand.reg "%SwitchLeaf80") "while.body557" "if.then562" },
    { name := "LeafBlock77",
      instrs := [
      Instr.icmp "%SwitchLeaf78" IPred.eq 8 (Operand.reg "%75") (Operand.imm (.int 8 (BitVec.ofNat 8 13)))
      ],
      term := Term.condbr (Operand.reg "%SwitchLeaf78") "while.body557" "if.then562" },
    { name := "LeafBlock74",
      instrs := [
      Instr.binop "%.off75" BinOp.add 8 (Operand.reg "%75") (Operand.imm (.int 8 (BitVec.ofNat 8 247))),
      Instr.icmp "%SwitchLeaf76" IPred.ule 8 (Operand.reg "%.off75") (Operand.imm (.int 8 (BitVec.ofNat 8 1)))
      ],
      term := Term.condbr (Operand.reg "%SwitchLeaf76") "while.body557" "if.then562" },
    { name := "while.body557",
      instrs := [
      Instr.binop "%inc558" BinOp.add 64 (Operand.reg "%q.01062") (Operand.imm (.int 64 (BitVec.ofNat 64 1))),
      Instr.icmp "%exitcond1171.not" IPred.eq 64 (Operand.reg "%inc558") (Operand.reg "%cond")
      ],
      term := Term.condbr (Operand.reg "%exitcond1171.not") "after_value" "land.rhs552" },
    { name := "if.then562",
      instrs := [
      Instr.store (Ty.int 64) (Operand.imm (.int 64 (BitVec.ofNat 64 0))) (Operand.reg "%tokens_out"),
      Instr.store (Ty.int 64) (Operand.imm (.int 64 (BitVec.ofNat 64 0))) (Operand.reg "%values_out"),
      Instr.store (Ty.int 64) (Operand.imm (.int 64 (BitVec.ofNat 64 0))) (Operand.reg "%sum_out"),
      Instr.store (Ty.int 64) (Operand.reg "%q.01062") (Operand.reg "%err")
      ],
      term := Term.br "cleanup580" },
    { name := "accept",
      instrs := [
      Instr.store (Ty.int 64) (Operand.reg "%tokens.8") (Operand.reg "%tokens_out"),
      Instr.store (Ty.int 64) (Operand.reg "%tokens.8") (Operand.reg "%values_out"),
      Instr.binop "%add579" BinOp.add 64 (Operand.reg "%terms.8") (Operand.reg "%arena.10"),
      Instr.store (Ty.int 64) (Operand.reg "%add579") (Operand.reg "%sum_out")
      ],
      term := Term.br "cleanup580" },
    { name := "cleanup580",
      instrs := [
      Instr.phi "%retval.14" (Ty.int 64) [("if.then", (Operand.imm (.int 64 (BitVec.ofNat 64 0)))), ("if.then12", (Operand.imm (.int 64 (BitVec.ofNat 64 0)))), ("if.then68", (Operand.imm (.int 64 (BitVec.ofNat 64 0)))), ("if.then360", (Operand.imm (.int 64 (BitVec.ofNat 64 0)))), ("accept", (Operand.imm (.int 64 (BitVec.ofNat 64 1)))), ("if.then372", (Operand.imm (.int 64 (BitVec.ofNat 64 0)))), ("if.then402", (Operand.imm (.int 64 (BitVec.ofNat 64 0)))), ("if.then105", (Operand.imm (.int 64 (BitVec.ofNat 64 0)))), ("if.then118", (Operand.imm (.int 64 (BitVec.ofNat 64 0)))), ("if.then297", (Operand.imm (.int 64 (BitVec.ofNat 64 0)))), ("if.then311", (Operand.imm (.int 64 (BitVec.ofNat 64 0)))), ("if.then428", (Operand.imm (.int 64 (BitVec.ofNat 64 0)))), ("if.then94", (Operand.imm (.int 64 (BitVec.ofNat 64 0)))), ("if.then38", (Operand.imm (.int 64 (BitVec.ofNat 64 0)))), ("if.then321", (Operand.imm (.int 64 (BitVec.ofNat 64 0)))), ("cleanup.thread", (Operand.imm (.int 64 (BitVec.ofNat 64 0)))), ("cleanup287.thread", (Operand.imm (.int 64 (BitVec.ofNat 64 0)))), ("if.then562", (Operand.imm (.int 64 (BitVec.ofNat 64 0)))), ("cleanup491.thread", (Operand.imm (.int 64 (BitVec.ofNat 64 0)))), ("if.else510", (Operand.imm (.int 64 (BitVec.ofNat 64 0)))), ("if.then527", (Operand.imm (.int 64 (BitVec.ofNat 64 0))))],
      Instr.callVoid "llvm.lifetime.end.p0" [((Ty.int 64), (Operand.imm (.int 64 (BitVec.ofNat 64 1192)))), (Ty.ptr, (Operand.reg "%c"))],
      Instr.callVoid "llvm.lifetime.end.p0" [((Ty.int 64), (Operand.imm (.int 64 (BitVec.ofNat 64 24)))), (Ty.ptr, (Operand.reg "%e"))],
      Instr.callVoid "llvm.lifetime.end.p0" [((Ty.int 64), (Operand.imm (.int 64 (BitVec.ofNat 64 520)))), (Ty.ptr, (Operand.reg "%stk"))],
      Instr.callVoid "llvm.lifetime.end.p0" [((Ty.int 64), (Operand.imm (.int 64 (BitVec.ofNat 64 8)))), (Ty.ptr, (Operand.reg "%xj"))]
      ],
      term := Term.ret (Ty.int 64) (some (Operand.reg "%retval.14")) }] }

/-! ### The pin's guards -/

#guard decide (firstFunction stage2NoEventSrc = some stage2NoEventBody)
#guard decide (parsedFunctions stage2NoEventSrc = some [stage2NoEventBody])
#guard decide (parsedDeclCount stage2NoEventSrc = some 7)

-- The pin bites: the same text with one immediate changed still parses, and it
-- is not the pinned body.
/-- `s` with the first occurrence of `pat` replaced by `rep`; `s` unchanged
when there is none. -/
def replaceFirst (s pat rep : String) : String :=
  match s.splitOn pat with
  | a :: b :: rest => a ++ rep ++ String.intercalate pat (b :: rest)
  | _ => s

/-- The immediate the mutation writes: the first body's capacity check adds
`US_SLACK` to its length, so a body carrying `65` is a different body. -/
def stage2NoEventMutant : String := "add i64 %sub154, 65"

/-- The pinned text with that one immediate changed. -/
def stage2NoEventSrcMutated : String :=
  replaceFirst stage2NoEventSrc "add i64 %sub154, 64" stage2NoEventMutant

-- The needle occurs exactly once, so the mutation is one instruction.
#guard (stage2NoEventSrc.splitOn "add i64 %sub154, 64").length = 2
#guard stage2NoEventSrcMutated ≠ stage2NoEventSrc
#guard (match parseModule stage2NoEventSrcMutated with | .ok _ => true | .error _ => false)
#guard decide (firstFunction stage2NoEventSrcMutated ≠ some stage2NoEventBody)

/-! ### The ABI prefix and the staging suffix

`stage2_noevent.h`'s twelve slots are the body's first twelve parameters, in the
ABI's order; the four objects the flattening moved out of the body follow them.
The pin records both lists, because a change to either is a change to the
interface the boundary record maps. -/

/-- `stage2_noevent.h`'s twelve slots, name and type, in order. -/
def stage2NoEventAbi12 : List (String × Ty) :=
  [("%b", .ptr), ("%n", .int 64), ("%ep", .ptr), ("%nep", .int 64),
   ("%xp", .ptr), ("%nxp", .int 64), ("%scratch", .ptr),
   ("%scratchcap", .int 64), ("%tokens_out", .ptr), ("%values_out", .ptr),
   ("%sum_out", .ptr), ("%err", .ptr)]

/-- The four staging objects the flattening appends, in the emission's order
(`stage2-noevent.staging.tsv`): the container stack, the refusal record, the
cursor record and the number path's output slot. -/
def stage2NoEventStaging4 : List (String × Ty) :=
  [("%stk", .ptr), ("%e", .ptr), ("%c", .ptr), ("%d", .ptr)]

#guard decide (stage2NoEventBody.params = stage2NoEventAbi12 ++ stage2NoEventStaging4)
#guard decide (stage2NoEventBody.retTy = Ty.int 64)
#guard decide (stage2NoEventBody.name = "leanllvm_json_stage2_noevent")

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

-- The census is closed: the body calls exactly these seven symbols, and no
-- other -- in particular no literal helper, because the compare is body text.
#guard
  decide (((callTargets stage2NoEventBody).mergeSort (fun a b => a ≤ b)).eraseDups =
    ["llvm.lifetime.end.p0", "llvm.lifetime.start.p0", "llvm.memset.p0.i64",
     "llvm.trap", "num_fast_el1", "od_gap_recover", "s2_string_body"])

-- And the multiset is the emission's: the two string arms, the scalar gap's
-- recovery call, the entry's zeroing and its live-range markers.
#guard callCount stage2NoEventBody "llvm.lifetime.end.p0" = 12
#guard callCount stage2NoEventBody "llvm.lifetime.start.p0" = 8
#guard callCount stage2NoEventBody "llvm.memset.p0.i64" = 1
#guard callCount stage2NoEventBody "llvm.trap" = 2
#guard callCount stage2NoEventBody "num_fast_el1" = 1
#guard callCount stage2NoEventBody "od_gap_recover" = 3
#guard callCount stage2NoEventBody "s2_string_body" = 2
#guard callCount stage2NoEventBody "lit_check" = 0
#guard callCount stage2NoEventBody "ne_lit" = 0

/-! ### The structural facts the record consumes -/

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
byte count it allocates.  The record names the four mapped objects at these
extents, so this is the instrument that keeps the record's numbers the body's:
a fixture that resized an object fails the `#guard`s below at elaboration. -/
def lifetimeExtents (f : Function) : List (String × Nat) :=
  (f.blocks.flatMap (·.instrs)).filterMap fun i =>
    match i with
    | .callVoid "llvm.lifetime.start.p0"
        [(Ty.int 64, Operand.imm (.int 64 s)), (Ty.ptr, Operand.reg r)] =>
        some (r, s.toNat)
    | _ => none

#guard decide (stage2NoEventBody.blocks.length = 167)
#guard decide ((stage2NoEventBody.blocks.flatMap (·.instrs)).length = 646)
#guard decide (allocaTypes stage2NoEventBody =
  [Ty.int 64, Ty.int 64, Ty.int 64, Ty.int 64])
#guard retCount stage2NoEventBody = 1
#guard retsValued stage2NoEventBody

-- The four mapped objects are allocated for exactly the extents the record
-- names.  Each is the entry's own `lifetime.start`, so a fixture that resized
-- one fails here rather than leaving the record describing an object the body
-- no longer has.
#guard (lifetimeExtents stage2NoEventBody).lookup "%stk" == some 520
#guard (lifetimeExtents stage2NoEventBody).lookup "%e" == some 24
#guard (lifetimeExtents stage2NoEventBody).lookup "%c" == some 1192
#guard (lifetimeExtents stage2NoEventBody).lookup "%d" == some 8

/-- **The pinned body returns a value at every `ret`.**  The bridge to a call
site needs it, and reading it off the pinned AST rather than asserting it is the
point of pinning the AST.

The body is larger than the certified walk's, so the module raises the kernel
evaluation's recursion bound. -/
theorem stage2NoEventBody_retsValued : retsValued stage2NoEventBody = true := by
  decide

/-- **The pinned body allocates only scalars.**  The flattening removed every
aggregate `alloca`, so no allocation in the fixture moves the cursor by a
computed size. -/
theorem stage2NoEventBody_allocaTypes :
    allocaTypes stage2NoEventBody =
      [Ty.int 64, Ty.int 64, Ty.int 64, Ty.int 64] := by
  decide

/-! ### The guards the body keeps

The entry's own checks are body text and are pinned with it: both
scratch-capacity checks (the `len + US_SLACK` add compared against
`%scratchcap`), their two `__builtin_trap` arms, the refusal arms' three zero
stores, and the three acceptance stores.  A stub that dropped one is a
different body, and these `#guard`s refuse it. -/

/-- How often the body names a call to `sym`. -/
def hasTrapArm (f : Function) : Bool :=
  callCount f "llvm.trap" = 2

/-- The number of `icmp eq i8` instructions: the scalar literal compare's byte
comparisons, which are body text. -/
def icmpEq8Count (f : Function) : Nat :=
  ((f.blocks.flatMap (·.instrs)).filter fun i =>
    match i with
    | .icmp _ .eq 8 _ _ => true
    | _ => false).length

#guard hasTrapArm stage2NoEventBody
#guard icmpEq8Count stage2NoEventBody = 32

end LeanLLVM.Refinement.JsonStage2NoEventIR
