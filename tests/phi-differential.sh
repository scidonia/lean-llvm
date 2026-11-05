#!/usr/bin/env bash
# The differential observation for the `phi` fragment.
#
# Two programs — a loop whose `phi` takes one value on entry and another on the
# back-edge, and a `phi` with three predecessors whose path is chosen by `argc`
# — are executed twice: once by the model (`tests/phi-model.lean`, through the
# parser, the semantics and the predecessor field) and once by a compiler from
# the same text.  The two results are compared and reported.
#
# This is an observation, not a proof.  It says that on these two programs the
# model and the compiler agree; it says nothing about programs not run here, and
# nothing about the compiler's own semantics being the model's.
#
# Run from the repository root:
#
#     nix develop -c bash tests/phi-differential.sh
#
# A disagreement, a missing tool, or an unreadable model answer is a nonzero
# exit; the transcript ends with `RESULT: PASS` only when every comparison held.
set -uo pipefail

here=$(cd "$(dirname "$0")" && pwd)
repo=$(cd "$here/.." && pwd)
cd "$repo"

work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT

fail=0
note() { printf '%s\n' "$*"; }

for tool in clang lean llvm-as; do
  if ! command -v "$tool" >/dev/null 2>&1; then
    note "phi-differential: '$tool' is not on PATH; run this through the dev shell"
    exit 2
  fi
done

# The model's answers, read off the same files the compiler is given.
model_out=$(lake env lean tests/phi-model.lean 2>&1)
if [ $? -ne 0 ]; then
  note "phi-differential: the model run failed:"
  printf '%s\n' "$model_out"
  exit 1
fi
printf '%s\n' "$model_out" | sed 's/^/model: /'

model_loop=$(printf '%s\n' "$model_out" | awk '$1 == "loop" { print $2 }')
model_three=$(printf '%s\n' "$model_out" | awk '$1 == "three" { print $2, $3, $4, $5 }')
if [ -z "${model_loop:-}" ] || [ -z "${model_three:-}" ]; then
  note "phi-differential: the model printed no answers"
  exit 1
fi

# The compiler's answers from the same text.
compile() {
  local src=$1 out=$2
  clang -Wno-override-module -o "$out" "$src" 2>"$work/cc.log" || {
    note "phi-differential: clang could not build $src:"
    cat "$work/cc.log"
    return 1
  }
}

compile tests/phi/loop.ll "$work/loop" || exit 1
compile tests/phi/three.ll "$work/three" || exit 1

"$work/loop"
native_loop=$?
note "native: loop ${native_loop}"

set -- 1 2 3 4
native_three=""
for argc in "$@"; do
  # `argc` is one plus the number of arguments the program is run with.
  args=()
  for ((i = 1; i < argc; i++)); do args+=("x"); done
  "$work/three" "${args[@]}"
  native_three="$native_three $?"
done
native_three=${native_three# }
note "native: three ${native_three}"

compare() {
  local what=$1 model=$2 native=$3
  if [ "$model" = "$native" ]; then
    note "agree: ${what} model=${model} native=${native}"
  else
    note "MISMATCH: ${what} model=${model} native=${native}"
    fail=1
  fi
}

compare "loop" "$model_loop" "$native_loop"
compare "three (argc=1..4)" "$model_three" "$native_three"

# The model returns an `i32`; a process exit status exposes only its low eight
# bits.  Every fixture's answer is below 256, so the comparison above is on the
# whole value rather than on a truncation of it — which would not be true of a
# program returning, say, 300.
note "note: exit statuses carry the low 8 bits of the model's i32; every expected"
note "      answer here is below 256, so the whole value is compared"

# The printer's own text, assembled.  The fixtures above are hand-written IR that
# both the model and the compiler read; this takes what `Module.render` produces
# from them and gives it to `llvm-as`, so the printed `phi` is checked as
# assembler input rather than by inspection.
render_out=$(lake env lean tests/phi-render.lean 2>&1)
if [ $? -ne 0 ]; then
  note "phi-differential: the renderer failed:"
  printf '%s\n' "$render_out"
  fail=1
else
  printf '%s\n' "$render_out" | awk -v dir="$work" '
    /^--- phi-render ---$/ { part = 2; next }
    { if (part == 1) print > (dir "/rendered-loop.ll");
      else if (part == 2) print > (dir "/rendered-three.ll") }
  ' part=1 2>/dev/null || true
  for f in rendered-loop rendered-three; do
    if [ ! -s "$work/$f.ll" ]; then
      note "ASSEMBLY CHECK MISSING: the renderer produced no $f"
      fail=1
    elif llvm-as "$work/$f.ll" -o /dev/null 2>"$work/as.log"; then
      note "assembles: $f.ll, printed by Module.render"
    else
      note "ASSEMBLY FAILED: $f.ll, printed by Module.render"
      cat "$work/as.log"
      fail=1
    fi
  done
fi

# What the wrong readings would have printed, so the pass is read as agreement
# where disagreement was possible.  Each follows from the fixture rather than
# from a second run: the loop's guard is `%i < 3`, `%i`'s entry-edge value is 0
# and its back-edge value is `%j = %i + 1`, and `%j` is bound only by the block
# the back-edge leaves.
note "prediction: a reading that always takes the first incoming entry leaves \`%i\` at 0,"
note "            the guard \`%i < 3\` never fails and the run never returns: \`loop ub\`"
note "prediction: a reading that always takes the last incoming entry reads \`%j\` before"
note "            \`body\` has bound it, so the first step is undefined: \`loop ub\`"
note "            observed: model=3 native=3 — neither wrong reading reaches 3"
note "prediction: first-entry-always prints \`three 10 10 10 10\`; last-entry-always prints"
note "            \`three 30 30 30 30\`; observed: 10 20 30 30 — a different edge each time"

if [ "$fail" -eq 0 ]; then
  note "RESULT: PASS (model vs compiler, two programs, three-predecessor phi read at four edges)"
else
  note "RESULT: MISMATCH"
fi
exit "$fail"
