# Vendored reference: VeLLVM

The Lean development is written from scratch; this directory is study material
only.  It is not part of the Lake build.

## Provenance

- Upstream: <https://github.com/vellvm/vellvm>
- Revision: `de5b324922afa34c18e0401b74c431ae93d422fb` (2026-07-31)
- Licence: MIT (see `vellvm/LICENSE.md`, retained here)

## What was copied

- `vellvm/src/rocq/**/*.v` — the Coq syntax, semantics, numeric libraries,
  memory model and refinement theory.
- `vellvm/src/ml/libvellvm/**` — the OCaml lexer, parser and printer, used as a
  reference for textual LLVM IR grammar.
- `vellvm/Makefile`, `vellvm/src/rocq/_CoqProject` — build organisation for
  orientation.
- `vellvm/README.md`, `vellvm/CITATION.cff` — attribution.

Build products (`.vo`, `.glob`, `.aux`), documentation, and the test corpus were
excluded.

## How it is used

Design decisions are recorded in `DESIGN.md`.  Where a development choice differs
from VeLLVM — for example, modelling `poison` as immediate undefined behaviour
in this slice rather than threading a poison value — the difference is stated in
the Lean module that makes it.
