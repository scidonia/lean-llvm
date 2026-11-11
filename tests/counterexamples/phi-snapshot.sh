#!/usr/bin/env bash
# The leading-`phi` snapshot fixtures, executed by the model and by LLVM.
#
# A block's leading `phi` run is one step of the semantics: every member reads
# the environment the edge carried in, and the bindings land together once the
# run ends.  Five fixtures cover the shapes that rule has to get right, and each
# is run twice over the same text — by the model and by `clang -O0`.
#
#   cycle      three-register cycle on the back edge (`phi-cycle.ll`);
#   self       a `phi` whose back-edge operand is its own destination
#              (`phi-self.ll`);
#   backedge   a `phi` reached from two different predecessor blocks, with an
#              incoming entry keyed to each (`phi-backedge.ll`);
#   perm-a     the permutation pair's first half (`phi-perm-a.ll`);
#   perm-b     the same function with its independent leading `phi`s reordered
#              (`phi-perm-b.ll`).
#
# The pair criterion is symmetric: each case's model answer must equal the
# compiler's answer for that case, and `perm-a`'s answer must equal `perm-b`'s
# model answer *and* its native answer, because reordering independent leading
# `phi`s cannot change the result.
#
# The case's expected value is the number the fixture's header derives from the
# LangRef reading.  A native run that answers something else means the fixture is
# not measuring what it says, and this driver reports that rather than
# comparing against it.
#
# `tests/counterexamples/phi-swap.sh` is the original regression input for the
# same rule and is left as it is; this driver covers the shapes it does not.
#
# Run from the repository root:
#
#     nix develop -c bash tests/counterexamples/phi-snapshot.sh
set -uo pipefail

here=$(cd "$(dirname "$0")" && pwd)
repo=$(cd "$here/../.." && pwd)
cd "$repo"

work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT

echo "HEAD $(git rev-parse HEAD)"
echo "index $(git write-tree)"
for f in phi-cycle phi-self phi-backedge phi-perm-a phi-perm-b; do
  echo "fixture-mtime $f $(stat -c '%y' "tests/counterexamples/$f.ll")"
done
echo "runner-mtime $(stat -c '%y' tests/counterexamples/phi-snapshot.lean)"

for tool in clang lean; do
  if ! command -v "$tool" >/dev/null 2>&1; then
    echo "RESULT: NOT EXECUTABLE (missing $tool; run this from the dev shell)"
    exit 2
  fi
done
echo "clang $(clang --version | awk 'NR == 1')"

# The model's answers, read off the same files the compiler is given.
model_out=$(probes/install/mem-capped.sh --cap 6G -- lake env lean \
  tests/counterexamples/phi-snapshot.lean 2>&1)
model_status=$?
printf '%s\n' "$model_out" | sed 's/^/model-run: /'
if [ "$model_status" -ne 0 ]; then
  echo "RESULT: NOT EXECUTABLE (the model run exited $model_status)"
  exit 2
fi

model_value() {
  printf '%s\n' "$model_out" | awk -v c="$1" '$1 == "model" && $2 == c { print $3 }'
}

# The LangRef reading each fixture's header derives.
langref() {
  case "$1" in
    cycle) echo 2 ;;
    self) echo 7 ;;
    backedge) echo 111 ;;
    perm-a) echo 13 ;;
    perm-b) echo 13 ;;
    *) echo "" ;;
  esac
}

red=0
for c in cycle self backedge perm-a perm-b; do
  m=$(model_value "$c")
  if [ -z "${m:-}" ]; then
    echo "RESULT: NOT EXECUTABLE (the model runner printed no answer for $c)"
    exit 2
  fi
  if ! clang -O0 "tests/counterexamples/phi-$c.ll" -o "$work/$c" \
      >"$work/$c.clang.log" 2>&1; then
    sed "s/^/$c clang: /" "$work/$c.clang.log"
    echo "case $c model $m native NOT-COMPILED"
    echo "RESULT[$c]: NOT EXECUTABLE (clang refused the fixture)"
    exit 2
  fi
  "$work/$c"
  n=$?
  echo "$n" > "$work/$c.native"
  expected=$(langref "$c")
  echo "case $c model $m native $n expected $expected"
  if [ "$n" -ne "$expected" ]; then
    echo "RESULT[$c]: INCONCLUSIVE (native answered $n, not the LangRef reading $expected)"
    exit 2
  fi
  if [ "$m" = "$n" ]; then
    echo "RESULT[$c]: AGREE (model $m, native $n)"
  else
    echo "RESULT[$c]: DISAGREE (model $m, native $n)"
    red=1
  fi
done

# The permutation pair: the two texts are one function, so their answers agree.
ma=$(model_value perm-a)
mb=$(model_value perm-b)
na=$(cat "$work/perm-a.native")
nb=$(cat "$work/perm-b.native")
if [ "$ma" = "$mb" ] && [ "$na" -eq "$nb" ]; then
  echo "RESULT[pair]: AGREE (perm-a model $ma native $na, perm-b model $mb native $nb)"
else
  echo "RESULT[pair]: DISAGREE (perm-a model $ma native $na, perm-b model $mb native $nb)"
  red=1
fi

echo "== SUMMARY =="
if [ "$red" -ne 0 ]; then
  echo "RESULT: RED — a model answer differs from the compiler's for the same text"
  exit 1
fi
echo "RESULT: GREEN — every case's model answer equals the compiler's, and the pair agrees"
exit 0
