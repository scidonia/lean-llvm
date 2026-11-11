# Counterexamples to the three source findings

Three executable checks, one per finding of
`docs/lean-llvm-correctness-critique-and-repair-plan-b40bbe4.md`.  Nothing here
repairs a definition, states a new semantics, or changes a theorem: F1 adds one
negative lemma and F2/F3 add failing-then-passing regression inputs.

    nix develop -c bash tests/counterexamples/check.sh

The driver builds `LeanLLVMTest` for F1 and runs the other two scripts.  F2 and
F3 exit nonzero while the defect they name is present; the driver then exits
nonzero and prints one summary line per finding.  The driver's
`index`/`HEAD` lines and each script's `HEAD`/mtime lines belong to the
invocation, so a transcript says which revision produced it.

| finding | subject | check | path |
|---|---|---|---|
| F1 | the proof | the universal `hsem` implies `False` | `LeanLLVMTest/Counterexamples.lean` |
| F2 | the semantics | the swap program, model against clang | `tests/counterexamples/phi-swap.sh` |
| F3 | parser and printer | the GEP round trip, assembled by `llvm-as` | `tests/counterexamples/gep-roundtrip.sh` |

## F1 — the final parser premise is unsatisfiable

`pipeline_satisfies_of_parser` takes

```lean
hsem : ∀ (mem : Mem) (bs : List UInt8) (verdict : BitVec 64) (m : Mem)
    (dst ev err : Nat),
  readBytes mem base bs.length = some bs →
  ParserHalf eventRel bs verdict m dst ev err
```

and `ParserHalf`'s first conjunct is

```lean
verdict = 1 ↔ ∃ t : Tape, parseBytes Limits.default (ByteString.literal bs) = .ok t
```

The quantifier ranges over `verdict`, so the same input supplies the acceptance
equivalence at `1` and at `0`: the first instance says the parser accepts, the
second says it refuses.

`LeanLLVMTest/Counterexamples.lean` states and proves the negation at an
arbitrary `eventRel` and `base`:

```lean
theorem pipeline_parser_hsem_false (eventRel : EventStreamRel) (base : Nat) :
    ¬ (∀ (mem : Mem) (bs : List UInt8) (verdict : BitVec 64) (m : Mem)
        (dst ev err : Nat),
        readBytes mem base bs.length = some bs →
        ParserHalf eventRel bs verdict m dst ev err)
```

The proof instantiates `hsem` on the empty document and the empty memory, reads
the equivalence at `verdict = 1` and at `verdict = 0`, and derives the
contradiction.

**The input read.** `hsem`'s own `readBytes` hypothesis supplies it; the empty
document satisfies it in every memory and at every base, because
`readBytes m a 0 = some []` is `readBytes`'s first branch.  No concrete `Mem`,
no concrete `base`, and no evaluation of the parser's answer is needed.  The
lemma is stated at every `eventRel` and `base`, so it applies at whatever
instance the composition uses.

The module pins the declaration's axiom footprint:
`[propext, Quot.sound]`, the development's ceiling.  It lives in
`LeanLLVMTest/` rather than in the library because `LeanLLVM.lean` is the
library's root module and is not edited; `LeanLLVMTest` imports `LeanLLVM` from
outside, and `lake build LeanLLVMTest` elaborates the module and its pin.

The property is about the premise, not about the parser: it says the hypothesis
cannot be discharged, not that the parser gives a wrong answer.

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

The parser accepts and drops `inbounds`; the printer emits it again on every
GEP.  Parsing this file and printing it gives, verbatim:

```llvm
define i8 @roundtrip_gep() {
entry:
  %p = alloca i8
  store i8 7, ptr %p
  %q = getelementptr inbounds i8, ptr %p, i64 2
  %r = getelementptr inbounds i8, ptr %q, i64 18446744073709551614
  %v = load i8, ptr %r
  ret i8 %v
}
```

Both GEPs acquire `inbounds`, where the source wrote none.  (`-2` prints as its
`i64` bit pattern `18446744073709551614`; the value is the same.)  The
re-parsed module equals the parsed one, so the addition is invisible to the
AST-level round trip.

**Definedness is the criterion.**  `%p` names a one-byte allocation, so the
first GEP's index `2` leaves the object; under LLVM's `inbounds` rule that
result is poison, and the printed program has a definedness the source does not
have.  The observed return does not show this, and the check records why both
forms assemble and both optimise to the same constant:

```text
llvm-as source 0
llvm-as printed 0
opt-source-return ret i8 7
opt-printed-return ret i8 7
```

So the added flag is a semantic change, not a syntax error, and a test that only
runs the program cannot distinguish the two texts.  The regression input is
therefore the text: the printed form must not carry an `inbounds` the source did
not write.  Its detector runs on a positive control in the same run
(`getelementptr inbounds …` is found), on the source (absent), and on the printed
text (present); the script exits nonzero while the last disagrees with the
source.

The run reports `source-has-inbounds false`, `printed-has-inbounds true`,
`reparse-same true`, and the model's observation `model 7`.

This check covers the `inbounds` clause of the finding.  The index-width and
alignment losses the finding also names are not exercised here.
