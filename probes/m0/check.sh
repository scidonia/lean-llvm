#!/usr/bin/env bash
# M0 boundary probes for the LeanVellum programme.
#
# Run from the repository root:
#   nix develop -c bash probes/m0/check.sh
#
# The assertions are the observations recorded in
# docs/m0-runtime-noise-report.md: definition/declaration counts, the
# inlining of the exported body, the survival of the opaque extern call,
# and the SWAR mask guards.
set -euo pipefail

here=$(cd "$(dirname "$0")" && pwd)
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT

cp "$here/Probe.lean" "$here/Probe3.lean" "$here/Chunk2.lean" "$here/Swar.lean" "$tmp"/
cd "$tmp"

lean -c Probe.c Probe.lean
lean -c Probe3.c Probe3.lean
lean -c Chunk2.c Chunk2.lean
lean Swar.lean

clang -O1 -S -emit-llvm -I"$(lean --print-prefix)/include" Probe.c  -o ProbeO1.ll
clang -O1 -S -emit-llvm -I"$(lean --print-prefix)/include" Probe3.c -o Probe3O1.ll
clang -O3 -S -emit-llvm -I"$(lean --print-prefix)/include" Chunk2.c -o Chunk2O3.ll

defines() { grep -c '^define' "$1"; }
declares() { grep -c '^declare' "$1"; }

[ "$(defines ProbeO1.ll)" = 13 ]
[ "$(declares ProbeO1.ll)" = 9 ]
[ "$(defines Probe3O1.ll)" = 11 ]
[ "$(declares Probe3O1.ll)" = 7 ]

# The opaque extern call survives at -O3.
grep -q 'tail call i64 @leanllvm_comma_mask8_ext' Chunk2O3.ll

# The exported body is inlined into its same-unit caller.
awk '/^define.*l_useIt\(/{f=1} f{print} f&&/^}/{exit}' Chunk2O3.ll > useit.ir
grep -q 'shl' useit.ir
if grep -q 'call.*comma_mask8' useit.ir; then
  echo "unexpected call in l_useIt: the exported body was not inlined" >&2
  exit 1
fi

echo "m0 probes: ok"
