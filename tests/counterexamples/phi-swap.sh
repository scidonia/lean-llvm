#!/usr/bin/env bash
# The two-register `phi` swap, executed by the model and by LLVM.
#
# `tests/counterexamples/phi-swap.ll` swaps `%a` and `%b` on the loop's back
# edge and returns `%b`.  Both incoming operands are read on that edge, so the
# second iteration installs `(a, b) = (2, 1)` and the program returns `1`.  A
# model that installs `%a`'s new binding before evaluating `%b`'s operand reads
# the new `%a` and returns `2`.
#
# This is the regression input: it compares the model's answer with the
# compiler's over the same text, and it exits nonzero while they disagree.  It
# is meant to pass once the block's leading `phi`s read one snapshot of the
# incoming environment.
#
# Run from the repository root:
#
#     nix develop -c bash tests/counterexamples/phi-swap.sh
set -uo pipefail

here=$(cd "$(dirname "$0")" && pwd)
repo=$(cd "$here/../.." && pwd)
cd "$repo"

work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT

echo "HEAD $(git rev-parse HEAD)"
echo "fixture-mtime $(stat -c '%y' tests/counterexamples/phi-swap.ll)"
echo "runner-mtime $(stat -c '%y' tests/counterexamples/phi-swap.lean)"

for tool in clang lean; do
  if ! command -v "$tool" >/dev/null 2>&1; then
    echo "RESULT: NOT EXECUTABLE (missing $tool; run this from the dev shell)"
    exit 2
  fi
done
echo "clang $(clang --version | awk 'NR == 1')"

# The model's answer, read off the same file the compiler is given.
model_out=$(probes/install/mem-capped.sh --cap 6G -- lake env lean \
  tests/counterexamples/phi-swap.lean 2>&1)
model_status=$?
printf '%s\n' "$model_out" | sed 's/^/model-run: /'
if [ "$model_status" -ne 0 ]; then
  echo "RESULT: NOT EXECUTABLE (the model run exited $model_status)"
  exit 2
fi

model=$(printf '%s\n' "$model_out" | awk '$1 == "model" { print $2 }')
if [ -z "${model:-}" ]; then
  echo "RESULT: NOT EXECUTABLE (the model runner printed no answer)"
  exit 2
fi

# The compiler's answer from the same text.
if ! clang -O0 tests/counterexamples/phi-swap.ll -o "$work/swap" \
    >"$work/clang.log" 2>&1; then
  sed 's/^/clang: /' "$work/clang.log"
  echo "RESULT: NOT EXECUTABLE (clang refused the fixture)"
  exit 2
fi
"$work/swap"
native=$?

echo "model ${model}"
echo "native ${native}"
echo "llvm-expected 1"
echo "finding-prediction 2"

if [ "$native" -ne 1 ]; then
  echo "RESULT: INCONCLUSIVE (native answered ${native}, not the LangRef reading 1)"
  exit 2
fi

if [ "$model" = "$native" ]; then
  echo "RESULT: F2 REFUTED (model ${model} agrees with native ${native})"
  exit 0
fi

if [ "$model" = "2" ]; then
  echo "RESULT: F2 CONFIRMED (model ${model} is the finding's prediction; native ${native} is LLVM's)"
else
  echo "RESULT: F2 CONFIRMED (model ${model} disagrees with native ${native}, but is not the predicted 2)"
fi
echo "REGRESSION: RED — the model's answer for this input differs from LLVM's"
exit 1
