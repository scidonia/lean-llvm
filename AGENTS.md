# lean-llvm

Lean 4 development of a certified LLVM transformation and refinement framework.
`DESIGN.md` states the refinement relation and the modelling choices; this file
records how to build and what a change must prove.

## Toolchain

Lean `v4.35.0-rc3` and LLVM tools come from the flake.  Run every toolchain
command through the dev shell so the environment belongs to this checkout:

```bash
nix develop -c lake build
nix develop -c lake build LeanLLVMTest
nix develop -c lake exe leanllvm tests/constfold.ll
```

`llvm-as`, `llvm-dis`, `opt`, `llc` and `clang` are provided by the shell.

## Layout

- `LeanLLVM/` is the library: syntax, semantics, parser, printer, refinement,
  the pass framework, and the passes.
- `LeanLLVM/Vellum/` is the refinement layer: `Contract`, `Refines` /
  `SemRefines`, `Correct`, the contextual theorems, the comma-mask instance,
  the emitted-IR bridge (`CommaMaskIR`) and the IR-level caller
  (`SeamContext`).
- `LeanLLVMTest/` is the check library.  It imports `LeanLLVM` from outside, so
  it sees exactly the public interface, and holds `#guard` checks,
  `#guard_msgs` pins, and small theorems.
- `reference/vellvm/` is vendored VeLLVM source for study.  It is not built,
  linted or edited.
- `tests/` holds textual IR exercised by the driver, and executable scenarios of
  a user-facing route: `m4-loop-gate.sh` drives the installer selector and
  asserts that a loop request without a covering theorem is refused and that the
  baseline is installed instead.

## What a change must satisfy

- No `sorry`, no `admit`, no `native_decide`.
- A transformation is not done until it has a `Pass.Sound` theorem.  The build
  enforces that the theorem typechecks; a test is not a substitute.
- Every theorem that claims soundness should have its axiom footprint pinned in
  `LeanLLVMTest/` with `#guard_msgs in #print axioms ...` once it is stable.
- The parser and printer are part of the contract: round-trip checks in
  `LeanLLVMTest/Core.lean` must pass, and emitted IR must assemble with
  `llvm-as`.
- Anything the semantics does not model is refused by the parser with a message
  naming the construct.  Do not silently approximate an unmodelled construct.
- The 64-bit seam identities are kernel-checked in
  `LeanLLVM/Vellum/CommaMaskKernel.lean` by a byte-lane argument.  Do not
  reintroduce `bv_decide`, `native_decide`, `sorry` or `admit`; the pins in
  `LeanLLVMTest/Vellum.lean` must stay at the standard axiom footprint.
- Checks are behavioural where behaviour is observable: parse a program, run it,
  run the pass, compare.  Avoid tests that merely restate a definition.
- A mathematical obligation — a refinement, a framing law, a loop rule — is
  discharged by a theorem, its axiom pin, and an adversarial example that fails
  (`LeanLLVMTest/Vellum.lean` has both the loop's framed statement and a write
  outside the frame that it refuses).  A user-facing route gets an executable
  scenario instead: `tests/m4-loop-gate.sh` drives `probes/install/select.sh`
  and asserts refusal and fallback.

## Adding a pass

1. Write `Function → Function` in `LeanLLVM/Transform/`.
2. Prove the local effect lemma for each rewritten instruction/terminator.
3. Lift to `runFuel` by induction, then state the `Beh` result and derive
   `Refines`.
4. Package it as a `Pass` with a `Sound` theorem; add it to
   `LeanLLVM/Pipeline.lean` only if it is ready.
5. Add a `#guard` check showing the pass fires on a concrete program and that
   observable behaviour is unchanged.

## Style

- Keep passes block-local until dominance is modelled; cross-block rewrites
  need an explicit statement of what makes a substitution valid.
- Document a modelling simplification where it is made, not only in this file.
- The driver's output is a toolchain artifact: canonical syntax, one instruction
  per line, block labels preserved.
