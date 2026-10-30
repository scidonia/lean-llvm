# Emitted loop fixture and driver header refusal

`probes/install/ir/capture.sh` regenerates `baseline.ll` from Lean's emitted C
and `candidate.ll` from the lane-by-lane C transcription in `candidate_lanes.c`,
and records the exact `clang` and `opt` invocations.  The loop fixture is
emitted, not handwritten: `lake exe leanllvm-loop-emit` renders
`LeanLLVM.Vellum.CommaMaskLoop.loopFunction` — the AST in
`LeanLLVM/Vellum/CommaMaskLoopBody.lean` that
`LeanLLVM/Vellum/CommaMaskLoop.lean` parses `ir/loop.ll` back to and proves its
correctness and framed-memory statements about — with
`LeanLLVM.Function.render`, the framework's printer.  That is
framework-printer output from the same function the proofs parse, explicitly
not the output of Lean's native compiler: no `lean -c` C emission and no
`clang` lowering produces this text.  What the proofs pin is the emitted
textual IR, and the object is rebuilt from that text.  No theorem here
certifies LLVM's lowering of that text or the object built from it, and
nothing in this route establishes native `lean -c` provenance.  The capture
route is one shared command that writes all three fixtures, but the proofs
that pin them have separate owners: `LeanLLVM/Vellum/CommaMaskIR.lean` parses
and pins `baseline.ll` and `candidate.ll`, while
`LeanLLVM/Vellum/CommaMaskLoop.lean` separately parses and pins `ir/loop.ll`.

E1 pins that: the documented capture command must write the loop fixture from a
Lean emission of the loop body instead of leaving the fixture the tree starts
with in place.

The check drives a copy of `probes/install/ir/capture.sh` inside a private,
temporary tree shaped like the repository, with local shims for the only tools
the route invokes — `lake`, `clang` and `opt` — in a private `PATH`, and
`TMPDIR` inside that tree.  The `lake` shim answers the two questions the route
asks of it: the Lean prefix, and the loop emission.  The emission it answers
with is the tree's loop body carrying the delimiter pattern the tree's Lean body
fixture binds, which is the pattern of the fixture the tree starts with, with
each byte raised by one (`0x2C` becomes `0x2D`).  The pattern is computed from
that fixture's constant rather than typed, so the pair cannot silently agree.
The `clang` and `opt` shims answer with one minimal module, a pass-through copy
and a successful `verify`, so the rest of the capture run — the baseline and
candidate fixtures — completes.  No compiler, linker, network or clock is
reached, and nothing outside the temporary tree is written.

The check first runs the emission shim on its own and requires that answer to
carry the relations E1 asserts, so a capture result that lacks them is a
statement about the capture route rather than about an inert shim.  It then
applies one relation-breaking edit at a time to that body — a counter store
moved into the fall-through block, an accumulator load removed from the loop
body, a back-edge removed, the conditional branch's targets exchanged, a false
branch naming a block the function does not define, and a comparison that no
longer reads the slot's load — and requires the structural check to name each,
so passing it is a statement about the relations rather than about the
instruction tokens.

`leanllvm` reads textual IR, runs the pipeline on every function and writes
textual IR back.  For function definitions, an unmodelled header attribute is
refused rather than parsed past, with a message naming the attribute as
`AGENTS.md`, "What a change must satisfy", requires.  An unmodelled return
attribute before the return type and an unmodelled function attribute after the
parameter list are both declined.  The refusal covers function-definition
headers, not declarations: attributes in a `declare` parameter list or after its
closing `)` are outside what this file proves and may still be accepted.  The
promise here is the function-definition header and return attributes E2 and E3
pin, not general attribute rejection.
A diagnostic that only echoes the header line back does not satisfy E2 or E3:
the accepted form is a single diagnostic line that both names the attribute and
says that attribute is unsupported or unmodelled — `unsupported`, `unmodelled`,
`unmodeled`, or the parser's own `is not modelled yet` idiom.
A header attribute that constrains the returned value, or one that changes what
the function promises its caller, is part of the function's contract; a driver
that parses past it and writes the function back without it has accepted a
contract the pipeline proved nothing about.  E2 and E3 pin that at the driver's
command line.  Both place the attribute where LLVM's own emission puts it, as
`probes/install/ir/baseline.o1.ll` shows for a return attribute, and each input
carries its attribute only in the header line.

E2 and E3 run against a binary the repository builds outside the check's
temporary tree: `nix develop -c lake build leanllvm` produces
`.lake/build/bin/leanllvm`, and the check copies that binary into a private
temporary directory and invokes the copy there, so the rule is observed at the
command the driver exposes.  The same copied driver first rewrites an input
that carries no attribute and leaves an output file, so the output the refusal
asserts is absent is shown to be observable when a run does write it.  The
check itself reaches no compiler, linker, network, clock or other service once
it runs inside the prepared dev shell; `nix develop` may provision that shell
before the check starts.

    bash tests/m4-loop-emission.sh --capture
    nix develop -c lake build leanllvm
    nix develop -c bash tests/m4-loop-emission.sh --return-attr
    nix develop -c bash tests/m4-loop-emission.sh --function-attr

### E1 — the capture route regenerates the loop fixture from a Lean emission

- **Actor:** the probe maintainer.
- **Given:** a private, temporary tree shaped like the repository, holding a
  copy of `probes/install/ir/capture.sh`, the `ir/loop.ll` fixture the tree
  starts with, the C inputs the route compiles, and a Lean body fixture for the
  loop whose XOR delimiter pattern is that fixture's pattern with each byte
  raised by one; a private `PATH` whose `lake` answers `env lean --print-prefix`
  with a temporary Lean prefix and `exe leanllvm-loop-emit` with the loop
  emission — the tree's loop body with its `xor` constant taken from the
  pattern the Lean body fixture binds — and whose `clang` and `opt` answer with
  one minimal module, a pass-through copy, and success for `-passes=verify`;
  and `TMPDIR` inside the temporary tree.
- **When:** the maintainer runs the copied `capture.sh` once, as
  `probes/install/ir/capture.sh` documents it.
- **Then:** the copied command exits zero.  Within the parsed
  `define i64 @leanllvm_comma_mask8(i64 %arg)` function of the tree's
  regenerated `ir/loop.ll`, the instruction `xor i64 %arg, <constant>` takes
  its constant from the Lean body fixture's pattern — the decimal value that
  fixture binds, and not the tree fixture's constant — and the value it
  produces is the value operand of the body's `lshr i64`.  That shift's amount
  is the SSA result of a `mul i64 <counter-load>, 8` in the loop body, where
  `<counter-load>` is the conditional block's load of the same allocated
  counter slot its `icmp` tests, the `icmp` whose result the conditional
  branch sends on true to that body.  The function's blocks bind as a
  memory-backed loop: the entry block allocates two distinct `i64` slots; a
  conditional block loads the counter slot, compares that load, and branches on
  the comparison to a true target that is the loop body and a false target that
  is a distinct `done` block the function defines; the loop body stores the
  counter slot after the conditional block loads it, loads the accumulator slot
  and stores that slot after the load, and branches back to the conditional
  block.  A body that keeps the counter only in `done`, one that loads the
  accumulator only in `done`, one whose branch does not return to the
  conditional block, one whose false branch names a block the function does not
  define, and one whose comparison reads anything but the counter slot's load
  all fail this, however many of the expected instructions remain present.  A
  body whose `lshr` amount is a fixed constant rather than the lane offset's
  SSA result, one whose lane offset multiplies a constant rather than the
  counter load, and one whose lane offset multiplies by a value other than 8
  each fail a separate near-miss control derived from the valid shim body, even
  when the expected tokens remain elsewhere, and a capture command that fails
  while leaving an expected fixture fails the exit-status clause.
- **Why:** the documented capture route must produce the loop fixture from a
  Lean emission rather than carry the body as a file nothing regenerates, so
  the text that is parsed and proved is the program Lean emits.

### E2 — the driver refuses an unmodelled return attribute

- **Actor:** the IR transformation integrator.
- **Given:** the already built `leanllvm` driver copied into a private temporary
  directory; a single-function input in that directory carrying no attribute,
  which the same copied driver rewrites and leaves an output file for; and a
  second single-function input whose header is
  `define range(i64 0, 1) i64 @f(i64 %x)`, the return attribute before the
  return type and nowhere else in the input.
- **When:** the integrator invokes the copied driver once, as
  `--passes none <input.ll> -o <output.ll>`.
- **Then:** it exits nonzero, one diagnostic line names `range` and says that
  return attribute is unsupported or unmodelled, and it creates no output file.
- **Why:** a return attribute constrains the value the function returns, so a
  driver that drops it and writes the function back has accepted a wider
  contract than the one it was given.

### E3 — the driver refuses an unmodelled function attribute

- **Actor:** the IR transformation integrator.
- **Given:** the same driver copy and the same clean-input control; and a
  single-function input whose header is
  `define i64 @f(i64 %x) noreturn`, the function attribute after the parameter
  list and nowhere else in the input.
- **When:** the integrator invokes the copied driver once, as
  `--passes none <input.ll> -o <output.ll>`.
- **Then:** it exits nonzero, one diagnostic line names `noreturn` and says
  that function attribute is unsupported or unmodelled, and it creates no
  output file.
- **Why:** `noreturn` changes what the function promises its caller, so a driver
  that drops it and writes the function back has accepted a contract the
  pipeline proved nothing about.
