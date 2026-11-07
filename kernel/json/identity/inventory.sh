#!/usr/bin/env bash
# The fixture's inventory gate: the construct-capability check of the emitted
# stage-1 body.
#
#   nix develop -c bash kernel/json/identity/inventory.sh
#
# It exits a verdict and holds no admitted set.  The capture derives the
# fixture and three inventories from `kernel/json/s1_block.c` at the pinned
# flags; this gate checks that the committed artefacts are that derivation, that
# the fixture is a text the repository's parser reads, and that its own
# inventory detector is not blind.  The comparison of the inventory against a list of
# forms the proof covers is a review step over the generated file, never a
# literal list here: a list kept by hand is a list that falls behind the
# emission, and one that silently admits what the emission contains is worse
# than none.
#
# The four conditions, all required for exit 0:
#   (a) the committed fixture regenerates byte-identically from the committed C
#       at the pinned flags;
#   (b) the regenerated inventory byte-equals the committed `.inventory`, which
#       lists opcodes *and* call targets — an intrinsic is a callee symbol, not
#       an opcode — so a form entering the emission shows as a diff; and the two
#       records of the normalisation byte-equal the committed `.strip.tsv`
#       (what was removed, by class) and `.rewrites.tsv` (what was rewritten,
#       with its reason);
#   (c) the fixture parses under the repository's parser (`leanllvm`, exit 0);
#   (d) both controls fire: a text carrying `llvm.vector.reduce.*` is reported
#       by the same detector and is outside the fixture's inventory, and the
#       measured two-argument `pshuf.b` call is reported inside it, named in the
#       committed inventory and carrying exactly two operands in the fixture.
#
# Exit status: 0 when all four hold; 3 otherwise, naming the missing or
# differing item.  There is no 1: a fixture that does not regenerate, does not
# parse or is not the inventory's source is an unusable input, not an assertion
# result, and the route's other scripts use 3 for the same class of fault.
set -uo pipefail

here=$(cd "$(dirname "$0")" && pwd)
repo=$(cd "$here/../../.." && pwd)
ir=$repo/probes/install/ir
capture=$ir/capture-s1-masks.sh
fixture=$ir/json-s1-masks.candidate.ll
strip=$ir/json-s1-masks.strip.tsv
inventory=$ir/json-s1-masks.inventory
rewrites=$ir/json-s1-masks.rewrites.tsv
kernel=$repo/kernel/json/s1_block.c

fail() { printf 'SETUP: %s\n' "$*" >&2; exit 3; }

for path in "$kernel" "$capture" "$fixture" "$strip" "$rewrites" "$inventory"; do
  [ -f "$path" ] || fail "absent: $path"
done

driver=$repo/.lake/build/bin/leanllvm
if [ -x "$driver" ]; then
  parser_desc=$driver
  parse() { "$driver" --passes none --no-check -o /dev/null "$1"; }
elif command -v lake >/dev/null 2>&1; then
  parser_desc='lake exe leanllvm'
  parse() { lake exe leanllvm --passes none --no-check -o /dev/null "$1"; }
else
  fail "no parser: build one with 'lake build leanllvm', or put lake on PATH"
fi

mkdir -p "$repo/.lake" || { printf 'SETUP: cannot create %s/.lake\n' "$repo" >&2; exit 3; }
work=$(mktemp -d "$repo/.lake/tmp-s1-inventory.XXXXXX" 2>/dev/null) ||
  fail "cannot create a work directory under $repo/.lake"
restore() {
  for f in "$fixture" "$strip" "$rewrites" "$inventory"; do
    if [ -f "$work/committed.$(basename "$f")" ]; then
      cp "$work/committed.$(basename "$f")" "$f"
    fi
  done
}
trap 'restore; rm -rf "$work"' EXIT

# --- (a) and (b): the committed artefacts are the capture's derivation ------

cp "$fixture" "$work/committed.json-s1-masks.candidate.ll"
cp "$strip" "$work/committed.json-s1-masks.strip.tsv"
cp "$rewrites" "$work/committed.json-s1-masks.rewrites.tsv"
cp "$inventory" "$work/committed.json-s1-masks.inventory"

if ! bash "$capture" > "$work/capture.out" 2> "$work/capture.err"; then
  sed -n '1,40p' "$work/capture.err" >&2
  fail "the capture exited nonzero; the fixture did not regenerate"
fi

[ -f "$fixture" ] || fail "the capture wrote no fixture at $fixture"
[ -f "$strip" ] || fail "the capture wrote no strip inventory at $strip"
[ -f "$rewrites" ] || fail "the capture wrote no rewrite inventory at $rewrites"
[ -f "$inventory" ] || fail "the capture wrote no inventory at $inventory"

if ! cmp -s "$work/committed.json-s1-masks.candidate.ll" "$fixture"; then
  diff -u "$work/committed.json-s1-masks.candidate.ll" "$fixture" | awk 'NR <= 40' >&2
  fail "(a) the committed fixture is not the kernel source's emission at the pinned flags"
fi
printf 'ok: (a) the fixture regenerates byte-identically from %s\n' "${kernel#"$repo"/}"

if ! cmp -s "$work/committed.json-s1-masks.inventory" "$inventory"; then
  diff -u "$work/committed.json-s1-masks.inventory" "$inventory" | awk 'NR <= 40' >&2
  fail "(b) the committed inventory is not the fixture's inventory"
fi
printf 'ok: (b) the fixture inventory regenerates: %s line(s)\n' \
  "$(wc -l < "$inventory")"

if ! cmp -s "$work/committed.json-s1-masks.strip.tsv" "$strip"; then
  diff -u "$work/committed.json-s1-masks.strip.tsv" "$strip" | awk 'NR <= 40' >&2
  fail "the committed normalisation inventory is not the capture's"
fi
printf 'ok: the normalisation inventory regenerates: %s line(s)\n' \
  "$(wc -l < "$strip")"

if ! cmp -s "$work/committed.json-s1-masks.rewrites.tsv" "$rewrites"; then
  diff -u "$work/committed.json-s1-masks.rewrites.tsv" "$rewrites" | awk 'NR <= 40' >&2
  fail "(b) the committed rewrite inventory is not the capture's"
fi
printf 'ok: the rewrite inventory regenerates: %s row(s)\n' \
  "$(awk -F'\t' '!/^#/ && $1 != "class"' "$rewrites" | wc -l)"

# --- (c): the fixture is a text the parser reads ----------------------------

if ! parse "$fixture" > "$work/parse.out" 2> "$work/parse.err"; then
  sed -n '1,10p' "$work/parse.err" >&2
  fail "(c) the fixture does not parse"
fi
printf 'ok: (c) the fixture parses (%s)\n' "$parser_desc"

# --- the detector, which the controls test ---------------------------------

# Emits one `opcode <name>` or `call <target>` line per construct in a module
# text, sorted and unique.  Nothing here decides what is admitted: it reports
# what the text holds.
detect() {
  awk '
    /^[ \t]*;/ { next }
    /^[ \t]*!/ { next }
    /^[ \t]*#/ { next }
    /^[ \t]*[}{]/ { next }
    /^[ \t]*\[/ { next }
    {
      line = $0
      sub(/^[ \t]+/, "", line)
      if (substr(line, 1, 1) == "%") {
        eq = index(line, " = ")
        if (eq == 0) next
        line = substr(line, eq + 3)
      }
      split(line, w, /[ \t]+/)
      op = w[1]
      if (op ~ /^[a-z]+$/) print "opcode " op
      if (line ~ /^declare / || line ~ /^call / || line ~ /^tail call / ||
          line ~ /^invoke / || line ~ /^musttail call / || line ~ /^notail call /) {
        rest = line
        while (match(rest, /@[A-Za-z0-9_.$-]+/)) {
          print "call " substr(rest, RSTART, RLENGTH)
          rest = substr(rest, RSTART + RLENGTH)
        }
      }
    }
  ' "$1" | LC_ALL=C sort -u
}

# --- (d) both controls fire ------------------------------------------------

cat > "$work/reduce.ll" <<'EOF'
define i64 @probe(ptr %p) {
entry:
  %0 = call i64 @llvm.vector.reduce.add.v4i64(<4 x i64> zeroinitializer)
  ret i64 %0
}

declare i64 @llvm.vector.reduce.add.v4i64(<4 x i64>)
EOF

reduce_seen=$(detect "$work/reduce.ll" | grep -c '@llvm\.vector\.reduce\.add' || true)
[ "$reduce_seen" -gt 0 ] || fail "(d) the detector did not report llvm.vector.reduce.* in a text that contains it"
if grep -q 'llvm\.vector\.reduce' "$inventory"; then
  fail "(d) the fixture's inventory names llvm.vector.reduce.*; the control text is not outside it"
fi
printf 'ok: (d) control 1: the detector reports llvm.vector.reduce.add.* in a text carrying it,\n'
printf '          and the fixture inventory does not name it\n'

if ! grep -q '@llvm\.x86\.avx2\.pshuf\.b' "$inventory"; then
  fail "(d) control 2: the fixture's inventory does not name @llvm.x86.avx2.pshuf.b"
fi
pshuf_calls=$(awk '
  {
    key = "@llvm.x86.avx2.pshuf.b("
    i = index($0, key)
    if (i == 0) next
    rest = substr($0, i + length(key))
    depth = 1; args = 1; closed = 0
    for (j = 1; j <= length(rest); j++) {
      c = substr(rest, j, 1)
      if (c == "(" || c == "<") depth++
      else if (c == ")" || c == ">") { depth--; if (depth == 0) { closed = 1; break } }
      else if (c == "," && depth == 1) args++
    }
    if (!closed) next
    print args
  }
' "$fixture")
[ -n "$pshuf_calls" ] || fail "(d) control 2: the fixture carries no pshuf.b call"
bad=$(printf '%s\n' "$pshuf_calls" | grep -cv '^2$' || true)
[ "$bad" -eq 0 ] || fail "(d) control 2: a pshuf.b call in the fixture is not two-argument"
printf 'ok: (d) control 2: the fixture inventory names @llvm.x86.avx2.pshuf.b and every\n'
printf '          call to it carries exactly two operands (%s call(s))\n' "$(echo "$pshuf_calls" | wc -l)"

printf '\nok: the fixture is the kernel emission, its inventories are its own, it parses,\n'
printf '    and the inventory detector reports both what is present and what is absent\n'
