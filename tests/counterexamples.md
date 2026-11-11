# Counterexamples to the three source findings

Three executable checks, one per finding of
`docs/lean-llvm-correctness-critique-and-repair-plan-b40bbe4.md`.  F2/F3 are
failing-then-passing regression inputs and change nothing themselves.  F1 is the
proof side: two negative lemmas pin the premises the parser composition retired,
and one instantiation check shows the replacement premise holds at two actual
runs.

    nix develop -c bash tests/counterexamples/check.sh

The driver builds `LeanLLVMTest` for F1's negative lemmas, elaborates the F1
instantiation, and runs the other two scripts.  F2 and F3 exit nonzero while the
defect they name is present; the driver then exits nonzero and prints one
summary line per finding.  The driver's `index`/`HEAD` lines and each script's
`HEAD`/mtime lines belong to the invocation, so a transcript says which revision
produced it.

| finding | subject | check | path |
|---|---|---|---|
| F1 | the proof | the retired universal `hsem` implies `False`, and the replacement holds at two runs | `LeanLLVMTest/Counterexamples.lean`, `tests/counterexamples/parser-half-outcome.lean` |
| F2 | the semantics | the swap program, model against clang | `tests/counterexamples/phi-swap.sh` |
| F3 | parser and printer | the GEP round trip, assembled by `llvm-as` | `tests/counterexamples/gep-roundtrip.sh` |

## F1 — the final parser premise was unsatisfiable

`pipeline_satisfies_of_parser` and `pipeline_units_finalisation` took

```lean
hsem : ∀ (mem : Mem) (bs : List UInt8) (verdict : BitVec 64) (m : Mem)
    (dst ev err ndst' nev' : Nat),
  readBytes mem base bs.length = some bs →
  ParserHalf eventRel bs verdict m dst ev err ndst' nev'
```

The last two binders are the arena's and the event stream's extents, which
`ParserHalf` takes as arguments (the extent repair below); they carry no verdict,
which is what the refutation uses.  `ParserHalf`'s first conjunct is

```lean
verdict = 1 ↔ ∃ t : Tape, parseBytes Limits.default (ByteString.literal bs) = .ok t
```

The quantifier ranges over `verdict`, so the same input supplies the acceptance
equivalence at `1` and at `0`: the first instance says the parser accepts, the
second says it refuses.  Nothing in the premise connects the verdict, the
returned memory or the slots to an execution.

Both declarations now take

```lean
hsem : ∀ (ndst' nev' : Nat), pipelineOutputExtents args o ndst' nev' →
  ParserHalfForOutcome eventRel base args mem ndst' nev' o
```

`ParserHalfForOutcome` reads the verdict, the returned memory and the caller's
three slots out of `o` and the document out of `args` and `mem`; a run that
returned `1` supplies the half at `1` and says nothing at `0`.

**The extents are the record's, and that is the finding's second half.**
`ParserHalf` used to quantify its arena and event extents, so the event/arena
relation had to hold at *every* readable prefix of the two buffers, the empty one
included, and a relation that distinguished prefixes made the accepting case
unsatisfiable.  The extents are arguments now, and the units' post names them:
`pipelineOutputExtents` (`JsonPipelineContract`) reads each from its cursor slot
and bounds it below `2 ^ 64`.  The bound is load-bearing rather than defensive —
a slot's eight bytes identify a value modulo `2 ^ 64`, so without it the record
would still name every readable prefix; with it the pair is unique
(`pipelineOutputExtents_unique`, choice-free), so the premise above is satisfiable
at the run's own pair.  `pipeline_units_finalisation` applies it at the pair its
post carries, and no `∀ ndst' nev'` over arbitrary extents remains on the path
from the units' post to `Sigma_pipeline`.

**The retired shape implies `False`.**  `LeanLLVMTest/Counterexamples.lean`
states and proves both negations, at an arbitrary `eventRel` (and, for the
finalisation's, an arbitrary staging memory and `base`):

```lean
theorem pipeline_parser_hsem_false (eventRel : EventStreamRel) (base : Nat) :
    ¬ (∀ (mem : Mem) (bs : List UInt8) (verdict : BitVec 64) (m : Mem)
        (dst ev err ndst' nev' : Nat),
        readBytes mem base bs.length = some bs →
        ParserHalf eventRel bs verdict m dst ev err ndst' nev')

theorem pipeline_units_finalisation_hsem_false (eventRel : EventStreamRel)
    (mem : Mem) (base : Nat) :
    ¬ (∀ (bs : List UInt8) (verdict : BitVec 64) (m : Mem)
        (dst ev err ndst' nev' : Nat),
        readBytes mem base bs.length = some bs →
        ParserHalf eventRel bs verdict m dst ev err ndst' nev')
```

Each proof instantiates its hypothesis on the empty document, reads the
equivalence at `verdict = 1` and at `verdict = 0`, and derives the
contradiction.  The extents it supplies are arbitrary, and immaterial: the
contradiction is the free verdict's, in the first conjunct.

**The input read.**  The hypothesis's own `readBytes` premise supplies it; the
empty document satisfies it in every memory and at every base, because
`readBytes m a 0 = some []` is `readBytes`'s first branch.  No concrete `Mem`,
no concrete `base`, and no evaluation of the parser's answer is needed.  The
lemmas hold at every `eventRel`, so they apply at whatever instance the
composition uses.

The modules pin both axiom footprints at `[propext, Quot.sound]`, the
development's ceiling.  They live in `LeanLLVMTest/` rather than in the library
because `LeanLLVM.lean` is the library's root module and is not edited;
`LeanLLVMTest` imports `LeanLLVM` from outside, and `lake build LeanLLVMTest`
elaborates the module and its pins.

The property is about the premise, not about the parser: it says the hypothesis
cannot be discharged, not that the parser gives a wrong answer.

**The replacement is instantiated at two actual runs.**
`tests/counterexamples/parser-half-outcome.lean` proves
`∃ o, runFuel noCalls 1 f (EntryState f args mem 1) = some o ∧
ParserHalfForOutcome … 1 1 o` twice, at a one-block function whose entry returns
the verdict:

* accepting — `1` over the document `null`; the tape, its decode, its span
  discipline and its validity come from `parseRef_complete`, `decodeTape_correct`
  and `tape_valid`, so the acceptance equivalence is proved rather than assumed;
* refusing — `0` over a byte-order mark, which `parseBytes` refuses at its own
  branch (`bom_refused`, decided).

The outcome in each theorem is the run's result, not a chosen one, and the half is
stated at the extents those runs report — `1` and `1`, the value both cursor words
hold.  With the relation stated at one extent instead of at every prefix, it can
distinguish prefixes: a shorter prefix of either buffer fails it, which is the
relation the earlier shape could not use.

    nix develop -c probes/install/mem-capped.sh --cap 6G -- \
      lake env lean tests/counterexamples/parser-half-outcome.lean

whose dev-shell banner and `Git tree … is dirty` warning belong to the
invocation.  The file's `#print axioms` pins are its recorded values — the two
instantiations, `accept_half` and `refuse_half`, at `[propext, Quot.sound]` — so
a run that elaborates the file with no diagnostic from it leaves them matching.
The driver reports F1 as

```text
F1 proved: the retired premise implies False, and the replacement holds at both runs
```

## F2 — the two-register `phi` swap

`tests/counterexamples/phi-swap.ll`:

```llvm
define i32 @main() {
entry:
  br label %loop
loop:
  %a = phi i32 [ 1, %entry ], [ %b, %loop ]
  %b = phi i32 [ 2, %entry ], [ %a, %loop ]
  %i = phi i32 [ 0, %entry ], [ %j, %loop ]
  %j = add i32 %i, 1
  %again = icmp ult i32 %j, 2
  br i1 %again, label %loop, label %done
done:
  ret i32 %b
}
```

LLVM uses both incoming operands on the back edge, so the second iteration
installs `(a, b) = (2, 1)` from the first iteration's `(1, 2)`, and the program
returns `1`.  The model's `evalInstr` binds `%a` immediately and `denoteCode`
passes the updated environment to the next instruction, so `%b`'s incoming `%a`
reads the value just bound and the model returns `2`.

`tests/counterexamples/phi-swap.lean` prints the model's answer, and the script
compiles and runs the same file with clang.  Observed on this revision:

```text
model 2
native 1
```

The existing `tests/phi-fragment.lean` P1 uses a loop whose single leading `phi`
reads `%j`, a register bound *after* the `phi` in the same block on the previous
iteration; no leading `phi` reads another leading `phi` there, so that fixture
cannot see the defect.  The swap adds the second leading `phi` that reads the
first one's destination.

The script is the regression input: it exits nonzero while `model` and `native`
disagree, and `RESULT: F2 REFUTED` with exit zero once they agree.  The native
answer is a single clang 21.1.8 on this host, and the exit status carries the
low eight bits of the `i32`; both possible answers are below 256.

## F3 — the `getelementptr` round trip

**Refuted.**  The finding's live clause was that the printer adds `inbounds` to
every `getelementptr`, so a round trip gave the printed program a definedness the
source did not have.  The printer writes an ordinary `getelementptr` now —
`LeanLLVM/Printer.lean`'s header states that rule, and the check below observes
the text — so the round trip adds no flag.

The parser still accepts `inbounds` and drops it, because the instruction has no
field for it.  That direction loses a promise instead of adding one, and the
text LLVM consumes is the printed one.

`tests/counterexamples/gep-roundtrip.ll`:

```llvm
define i8 @roundtrip_gep() {
entry:
  %p = alloca i8
  store i8 7, ptr %p
  %q = getelementptr i8, ptr %p, i64 2
  %r = getelementptr i8, ptr %q, i64 -2
  %v = load i8, ptr %r
  ret i8 %v
}
```

Parsing this file and printing it gives, verbatim:

```llvm
define i8 @roundtrip_gep() {
entry:
  %p = alloca i8
  store i8 7, ptr %p, align 1
  %q = getelementptr i8, ptr %p, i64 2
  %r = getelementptr i8, ptr %q, i64 18446744073709551614
  %v = load i8, ptr %r, align 1
  ret i8 %v
}
```

Neither GEP carries `inbounds`, so the round trip preserves the absence this
fixture is about.  The text differs elsewhere, in two ways that add no promise:
`-2` prints as its `i64` bit pattern `18446744073709551614`, the same value, and
each `load` and `store` names `align 1` rather than leaving the modifier to the
type's ABI alignment, which the AST does not carry.  The re-parsed module equals
the parsed one, so neither difference is visible to the AST-level round trip.

**Definedness is the criterion.**  `%p` names a one-byte allocation, so the
first GEP's index `2` leaves the object; under LLVM's `inbounds` rule that result
is poison, and a printed `inbounds` would give the program a definedness the
source does not have.  The observed return cannot see that, and the check records
why both forms assemble and both optimise to the same constant:

```text
llvm-as source 0
llvm-as printed 0
opt-source-return ret i8 7
opt-printed-return ret i8 7
```

So the flag would be a semantic change, not a syntax error, and a test that only
runs the program cannot distinguish the two texts.  The regression input is
therefore the text: the printed form must not carry an `inbounds` the source did
not write.  Its detector runs on a positive control in the same run
(`getelementptr inbounds …` is found), on the source (absent), and on the printed
text (absent); a printed `inbounds` turns the verdict into `RESULT: F3
CONFIRMED` and exits nonzero.

The run reports `source-has-inbounds false`, `printed-has-inbounds false`,
`reparse-same true`, the model's observation `model 7`, and `RESULT: F3 REFUTED`
with exit zero.

This check covers the `inbounds` clause of the finding.  The index-width and
alignment losses it also names are settled in the printer rather than by this
check: an index written as a register is printed at the width that register's
own definition binds, and the alignment the AST does not carry is named `align 1`
rather than left to the type's ABI alignment.  Neither is exercised here.
