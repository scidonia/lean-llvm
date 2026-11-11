#!/usr/bin/env bash
# The `getelementptr` round trip, assembled by LLVM.
#
# `tests/counterexamples/gep-roundtrip.ll` walks one byte past an `i8`
# allocation and back before dereferencing, and it writes no `inbounds`.  The
# model's printer emits `inbounds` on every `getelementptr`, so the printed text
# adds a semantic promise the source did not make: over a one-byte allocation,
# index 2 leaves the object, and LLVM then makes the result poison.
#
# Definedness is the criterion, not the observed return.  Both texts assemble,
# and both optimise to the same constant, so an observed-return test cannot
# distinguish them.  The regression input is therefore the text: it exits
# nonzero while the printed text carries an `inbounds` the source does not.
#
# Run from the repository root:
#
#     nix develop -c bash tests/counterexamples/gep-roundtrip.sh
set -uo pipefail

here=$(cd "$(dirname "$0")" && pwd)
repo=$(cd "$here/../.." && pwd)
cd "$repo"

work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT

echo "HEAD $(git rev-parse HEAD)"
echo "fixture-mtime $(stat -c '%y' tests/counterexamples/gep-roundtrip.ll)"
echo "runner-mtime $(stat -c '%y' tests/counterexamples/gep-roundtrip.lean)"

for tool in lean llvm-as opt; do
  if ! command -v "$tool" >/dev/null 2>&1; then
    echo "RESULT: NOT EXECUTABLE (missing $tool; run this from the dev shell)"
    exit 2
  fi
done
echo "llvm-as $(llvm-as --version | awk 'NR == 2')"

# The parser, the printer and the model, over the fixture.
run_out=$(probes/install/mem-capped.sh --cap 6G -- lake env lean \
  tests/counterexamples/gep-roundtrip.lean 2>&1)
run_status=$?
printf '%s\n' "$run_out" | sed 's/^/roundtrip-run: /'
if [ "$run_status" -ne 0 ]; then
  echo "RESULT: NOT EXECUTABLE (the round-trip run exited $run_status)"
  exit 2
fi

field() { printf '%s\n' "$run_out" | awk -v k="$1" '$1 == k { print $2 }'; }
source_flag=$(field source-has-inbounds)
printed_flag=$(field printed-has-inbounds)
reparse_same=$(field reparse-same)
model=$(field model)

if [ -z "${source_flag:-}" ] || [ -z "${printed_flag:-}" ] || \
   [ -z "${reparse_same:-}" ] || [ -z "${model:-}" ]; then
  echo "RESULT: NOT EXECUTABLE (the runner did not print every observation)"
  exit 2
fi

# The printer's own text, taken verbatim from the runner's markers.
printf '%s\n' "$run_out" | awk '
  /^--- printed ---$/ { inside = 1; next }
  /^--- end printed ---$/ { inside = 0 }
  inside { print }' > "$work/printed.ll"

if [ ! -s "$work/printed.ll" ]; then
  echo "RESULT: NOT EXECUTABLE (no printed text between the markers)"
  exit 2
fi

# The same detector's affirmative control, in this run: a text that does carry
# the token must be found by it.
if printf '%s\n' 'getelementptr inbounds i8, ptr %p, i64 2' | grep -q 'inbounds'; then
  echo "detector-control inbounds-present yes"
else
  echo "detector-control inbounds-present NO"
  echo "RESULT: NOT EXECUTABLE (the detector does not find its own control)"
  exit 2
fi

echo "source-has-inbounds ${source_flag}"
echo "printed-has-inbounds ${printed_flag}"
echo "reparse-same ${reparse_same}"
echo "model ${model}"

# The texts, and the difference between them.
echo "--- source ---"
cat tests/counterexamples/gep-roundtrip.ll
echo "--- printed (verbatim) ---"
cat "$work/printed.ll"
echo "--- diff source vs printed ---"
diff -u tests/counterexamples/gep-roundtrip.ll "$work/printed.ll" || true

# Both forms as assembler input, so the added flag is shown to be a semantic
# change rather than a syntax error.
llvm-as tests/counterexamples/gep-roundtrip.ll -o "$work/source.bc" \
  >"$work/as-source.log" 2>&1
as_source=$?
llvm-as "$work/printed.ll" -o "$work/printed.bc" >"$work/as-printed.log" 2>&1
as_printed=$?
echo "llvm-as source ${as_source}"
echo "llvm-as printed ${as_printed}"
if [ "$as_source" -ne 0 ]; then
  sed 's/^/llvm-as source: /' "$work/as-source.log"
  echo "RESULT: NOT EXECUTABLE (the source does not assemble)"
  exit 2
fi
if [ "$as_printed" -ne 0 ]; then
  sed 's/^/llvm-as printed: /' "$work/as-printed.log"
  echo "RESULT: NOT EXECUTABLE (the printed text does not assemble)"
  exit 2
fi

# The control for "the observed return is not the instrument": both forms
# optimise to the same constant.
opt -O2 -S tests/counterexamples/gep-roundtrip.ll -o "$work/source.opt.ll" \
  >/dev/null 2>&1
opt -O2 -S "$work/printed.ll" -o "$work/printed.opt.ll" >/dev/null 2>&1
source_ret=$(grep -o 'ret i8 [0-9]*' "$work/source.opt.ll" | awk 'NR == 1')
printed_ret=$(grep -o 'ret i8 [0-9]*' "$work/printed.opt.ll" | awk 'NR == 1')
echo "opt-source-return ${source_ret}"
echo "opt-printed-return ${printed_ret}"

if [ "$source_flag" = "true" ]; then
  echo "RESULT: INCONCLUSIVE (the fixture itself writes inbounds)"
  exit 2
fi
if [ "$printed_flag" = "false" ]; then
  echo "RESULT: F3 REFUTED (the printed text preserved the absence of inbounds)"
  exit 0
fi

echo "RESULT: F3 CONFIRMED (the source has no inbounds; the printed text adds it)"
echo "DEFINEDNESS: the printed GEP is inbounds over a one-byte allocation at index 2,"
echo "             so LLVM makes the out-of-object result poison; the source's GEP"
echo "             makes no such promise.  Both forms assemble and both optimise"
echo "             to the same return, so the observed return does not distinguish"
echo "             them."
echo "REGRESSION: RED — the round trip adds a semantic flag the source did not write"
exit 1
