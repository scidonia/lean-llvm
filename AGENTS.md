# lean-llvm

Lean 4 development of a certified LLVM transformation and refinement framework.
`DESIGN.md` states the refinement relation and the modelling choices; this file
records how to build and what a change must prove.

## Toolchain

Lean `v4.36.0-rc1` and LLVM tools come from the flake.  Run every toolchain
command through the dev shell so the environment belongs to this checkout:

```bash
nix develop -c lake build
nix develop -c lake build LeanLLVMTest
nix develop -c lake exe leanllvm tests/constfold.ll
```

`llvm-as`, `llvm-dis`, `opt`, `llc` and `clang` are provided by the shell.

The default build covers the `LeanLLVM.ITree` library as well as `LeanLLVM`.
That library depends on `leanprover-community/mathlib4` at the revision pinned
in `lakefile.toml`, resolved into `.lake/packages`; mathlib's oleans must be
present before the tree modules elaborate, so a cold checkout pays for a mathlib
build unless its prebuilt cache is already in place.  The mathlib revision,
`lean-toolchain` and the flake's Lean source are one unit: moving one needs the
other two to match.

## Layout

- `LeanLLVM/` is the library: syntax, semantics, parser, printer, refinement,
  the pass framework, and the passes.
- `LeanLLVM/Vellum/` is the refinement layer: `Contract`, `Refines` /
  `SemRefines`, `Correct`, the contextual theorems, the comma-mask instance,
  the emitted-IR bridge (`CommaMaskIR`) and the IR-level caller
  (`SeamContext`).
- `LeanLLVM/ITree/` is a second Lake library, `LeanLLVM.ITree`: the
  interaction-tree layer.  `Core` is the public tree API, `Interpret` the
  interpretation of the fuel semantics as trees, `Eutt` the
  postcondition-indexed directed relation, and `LoopInstance` the
  comma-mask loop/candidate instance.  Only
  `LeanLLVM/ITree/Internal/PFunctor.lean` imports mathlib; every other module
  reaches it through that adapter.  `LeanLLVM.lean` imports the library after
  the loop module, so `LeanLLVMTest/` reaches the tree API through the same
  entrypoint as the rest of `LeanLLVM`.  `LeanLLVM/ITree/README.md` records the
  public surface, the dependency and the upstream provenance.
- `LeanLLVMTest/` is the check library.  It imports `LeanLLVM` from outside, so
  it sees exactly the public interface, and holds `#guard` checks,
  `#guard_msgs` pins, and small theorems.
- `reference/vellvm/` is vendored VeLLVM source for study.  It is not built,
  linted or edited.
- `tests/` holds textual IR exercised by the driver, and executable scenarios of
  user-facing routes: `m4-loop-gate.sh` drives the installer selector and
  asserts that a loop request without a covering theorem is refused and that the
  baseline is installed instead; `m4-loop-emission.sh` drives the fixture-capture
  route and the driver's command line, and asserts that the loop fixture is
  regenerated from the Lean emission and that a function header carrying an
  unmodelled attribute is refused.

## What a change must satisfy

- No `sorry`, no `admit`, no `native_decide`.
- A transformation is not done until it has a `Pass.Sound` theorem.  The build
  enforces that the theorem typechecks; a test is not a substitute.
- Every theorem that claims soundness should have its axiom footprint pinned in
  `LeanLLVMTest/` with `#guard_msgs in #print axioms ...` once it is stable.
- The parser and printer are part of the contract: round-trip checks in
  `LeanLLVMTest/Core.lean` must pass, and emitted IR must assemble with
  `llvm-as`.  A fixture read through `include_str` is not a `lake build` input,
  so elaborate its proof module from source after changing it; keep the mutation
  that shows the pin bites (`probes/install/check.sh` does this for the candidate
  and loop fixtures).
- The parser refuses the surfaces it checks, with a message naming the
  construct: unmodelled instructions, block structure, and a function
  definition's header -- a return attribute before the return type and a
  function attribute after the parameter list are refused
  (`tests/m4-loop-emission.sh --return-attr`, `--function-attr`).  Do not
  silently approximate an unmodelled construct on those surfaces.  A `declare`
  header is not checked: its parameter list is read up to the closing `)` and
  the rest of the line is ignored, so unmodelled declaration tokens can be
  accepted and dropped.  Do not claim total attribute rejection.
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
- The tree relation (`LeanLLVM/ITree/Eutt.lean`) is a second, finer statement
  beside `Refines` and `RefinesWithin`, not a replacement for them.  Those
  keep their definitions and their proofs, and no pass or route reasons
  through the tree layer yet; do not describe it as the semantics' refinement
  relation.  Its own statements follow the same discipline: a positive
  theorem, a negative example the same detector rejects, and an axiom pin no
  wider than `[propext, Classical.choice, Quot.sound]` in
  `LeanLLVMTest/Vellum.lean`.  The loop instance is one fixture at fixed
  budgets and one allocator-derived frame; a wider frame, a bigger budget or a
  general rule is new work, not a variation on that theorem.
- Keep mathlib behind its adapter.  A new module in `LeanLLVM/` or
  `LeanLLVM/ITree/` imports `LeanLLVM.ITree.Internal.PFunctor` (or a module
  above it), never `Mathlib.*`, and clients name trees through
  `LeanLLVM.ITree.Core` rather than `PFunctor.M`, `MIntl` or `CofixA`.  Only
  `LeanLLVM/ITree/Internal/PFunctor.lean` may import mathlib directly.

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
