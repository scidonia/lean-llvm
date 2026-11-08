#!/usr/bin/env bash
# The fixture's inventory gate: the construct-capability check of an emitted
# stage-1 body.
#
#   nix develop -c bash kernel/json/identity/inventory.sh
#   nix develop -c bash kernel/json/identity/inventory.sh --unit s1
#   nix develop -c bash kernel/json/identity/inventory.sh --unit entry
#
# The unit (`--unit s1` is the default, so an invocation with no arguments keeps
# its meaning and its exit codes).  Three units are gated:
#
#   s1     the classification mask unit.  Its capture is
#          probes/install/ir/capture-s1-masks.sh and its artefacts are the
#          fixture `json-s1-masks.candidate.ll` and the three inventories
#          `json-s1-masks.strip.tsv`, `…rewrites.tsv` and `….inventory`.
#   entry  the entry positions unit.  Its capture is
#          probes/install/ir/capture-entry.sh and its artefacts are the fixture
#          `json-entry.candidate.ll` and the four inventories
#          `json-entry.strip.tsv`, `….rewrites.tsv`, `….table.tsv` and
#          `….inventory`.  The table inventory records the one rewrite this unit
#          adds: the unit's table cannot be a module global, so each of the
#          eight `getelementptr` reads through it becomes a read through the
#          `%tab` parameter.
#   utf8   the UTF-8 validity unit.  Its capture is
#          probes/install/ir/capture-utf8.sh and its artefacts are the fixture
#          `json-utf8.candidate.ll` and the three inventories
#          `json-utf8.strip.tsv`, `….rewrites.tsv` and `….inventory`.  This unit
#          has no table rewrite and no parameter rename: its tables fold to
#          literal vector operands and its emission carries the unit's own
#          parameter names, so the capture refuses rather than rewrites if
#          either appears.
#
# This gate holds no class list of its own, because the classes are the capture's
# formats and a list kept here would be the hand-kept list this gate exists to
# avoid: it regenerates the artefacts by running the unit's own capture, and a
# capture whose classification falls behind the emission refuses there.
#
# It exits a verdict and holds no admitted set.  The comparison of the inventory
# against a list of forms the proof covers is a review step over the generated
# file, never a literal list here: a list kept by hand is a list that falls
# behind the emission, and one that silently admits what the emission contains is
# worse than none.
#
# The four conditions, all required for exit 0:
#   (a) the committed fixture regenerates byte-identically from the committed C
#       at the pinned flags;
#   (b) each regenerated inventory byte-equals its committed file, which lists
#       opcodes *and* call targets — an intrinsic is a callee symbol, not an
#       opcode — so a form entering the emission shows as a diff; the strip
#       inventory records what the normalisation removed (by class), the rewrite
#       inventory what it rewrote (with its reason), and, for `entry`, the table
#       inventory the GEP each read was emitted as and the one it became;
#   (c) the fixture parses under the repository's parser (`leanllvm`, exit 0);
#   (d) the unit's controls fire:
#       s1     a text carrying `llvm.vector.reduce.*` is reported by the same
#              detector and is outside the fixture's inventory, and the measured
#              two-argument `pshuf.b` call is reported inside it, named in the
#              committed inventory and carrying exactly two operands in the
#              fixture;
#       entry  a text carrying `llvm.xor.reduce.*` is reported by the same
#              detector and is outside the fixture's inventory; a text carrying
#              `llvm.cttz.i64(…, i1 false)` is reported inside it as the
#              accepted-flag spelling, named by the same detector and named in
#              the committed inventory; and the capture's table attributor
#              accepts a pair that differs only in the table read and refuses a
#              pair whose differing GEP is not the table read — the refusal
#              naming the line as unattributed.
#       utf8   a text carrying the refused neighbour spelling
#              `llvm.usub.sat.v16i8` is reported by the same detector and is
#              outside the fixture's inventory, and the two spellings the stage
#              calls — `@llvm.usub.sat.v32i8` and `@llvm.x86.avx.ptestz.256` —
#              are named by the same detector and named in the committed
#              inventory.  A unit whose control arm is missing passes zero
#              controls silently, because this file's controls switch has no
#              default.
#
# Exit status: 0 when all four hold; 3 otherwise, naming the missing or
# differing item.  There is no 1: a fixture that does not regenerate, does not
# parse or is not the inventory's source is an unusable input, not an assertion
# result, and the route's other scripts use 3 for the same class of fault.
set -uo pipefail

here=$(cd "$(dirname "$0")" && pwd)
repo=$(cd "$here/../../.." && pwd)
ir=$repo/probes/install/ir

fail() { printf 'SETUP: %s\n' "$*" >&2; exit 3; }

usage() {
  awk 'NR > 1 && /^set -/ { exit } NR > 1 { print }' "$0" | sed 's/^# \{0,1\}//'
}

unit=s1
while [ "$#" -gt 0 ]; do
  case "$1" in
    --unit) shift; [ -n "${1:-}" ] || fail '--unit needs a value'; unit=$1 ;;
    --unit=*) unit=${1#--unit=} ;;
    -h|--help) usage; exit 0 ;;
    *) printf 'inventory: unknown argument %s\n' "$1" >&2; exit 3 ;;
  esac
  shift
done

# Per unit: the capture that derives the artefacts, the fixture, the kernel it
# is emitted from, and the inventories that stand beside it.
case "$unit" in
  s1)
    capture=$ir/capture-s1-masks.sh
    fixture=$ir/json-s1-masks.candidate.ll
    kernel=$repo/kernel/json/s1_block.c
    inventories=("$ir/json-s1-masks.strip.tsv" "$ir/json-s1-masks.rewrites.tsv" \
                 "$ir/json-s1-masks.inventory")
    ;;
  entry)
    capture=$ir/capture-entry.sh
    fixture=$ir/json-entry.candidate.ll
    kernel=$repo/kernel/json/entry.c
    inventories=("$ir/json-entry.strip.tsv" "$ir/json-entry.rewrites.tsv" \
                 "$ir/json-entry.table.tsv" "$ir/json-entry.inventory")
    ;;
  utf8)
    capture=$ir/capture-utf8.sh
    fixture=$ir/json-utf8.candidate.ll
    kernel=$repo/kernel/json/utf8.c
    inventories=("$ir/json-utf8.strip.tsv" "$ir/json-utf8.rewrites.tsv" \
                 "$ir/json-utf8.inventory")
    ;;
  *)
    printf 'SETUP: unit %s has no inventory gate; implemented: s1, entry, utf8\n' "$unit" >&2
    exit 3
    ;;
esac

for path in "$kernel" "$capture" "$fixture" "${inventories[@]}"; do
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
work=$(mktemp -d "$repo/.lake/tmp-$unit-inventory.XXXXXX" 2>/dev/null) ||
  fail "cannot create a work directory under $repo/.lake"
restore() {
  for f in "$fixture" "${inventories[@]}"; do
    if [ -f "$work/committed.$(basename "$f")" ]; then
      cp "$work/committed.$(basename "$f")" "$f"
    fi
  done
}
trap 'restore; rm -rf "$work"' EXIT

# --- (a) and (b): the committed artefacts are the capture's derivation ------

for f in "$fixture" "${inventories[@]}"; do
  cp "$f" "$work/committed.$(basename "$f")"
done

if ! bash "$capture" > "$work/capture.out" 2> "$work/capture.err"; then
  sed -n '1,20p' "$work/capture.err" >&2
  fail "the capture did not run; the artefacts are not derived"
fi

[ -f "$fixture" ] || fail "the capture wrote no fixture at $fixture"
for f in "${inventories[@]}"; do
  [ -f "$f" ] || fail "the capture wrote no inventory at $f"
done

if ! cmp -s "$work/committed.$(basename "$fixture")" "$fixture"; then
  diff -u "$work/committed.$(basename "$fixture")" "$fixture" | awk 'NR <= 60' >&2
  fail "(a) the committed fixture is not the capture's; ${kernel#"$repo"/} does not emit it at the pinned flags"
fi
printf 'ok: (a) the fixture regenerates byte-identically from %s\n' "${kernel#"$repo"/}"

for f in "${inventories[@]}"; do
  if ! cmp -s "$work/committed.$(basename "$f")" "$f"; then
    diff -u "$work/committed.$(basename "$f")" "$f" | awk 'NR <= 40' >&2
    fail "(b) the committed $(basename "$f") is not the capture's"
  fi
  printf 'ok: (b) %s regenerates: %s row(s)\n' "$(basename "$f")" \
    "$(awk '!/^#/ && $1 != "class" && $1 != "kind"' "$f" | wc -l)"
done

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

# --- (d) the unit's controls fire ------------------------------------------

controls_s1() {
  cat > "$work/reduce.ll" <<'EOF'
define i64 @probe(ptr %p) {
entry:
  %0 = call i64 @llvm.vector.reduce.add.v4i64(<4 x i64> zeroinitializer)
  ret i64 %0
}

declare i64 @llvm.vector.reduce.add.v4i64(<4 x i64>)
EOF

  local reduce_seen pshuf_calls bad
  reduce_seen=$(detect "$work/reduce.ll" | grep -c '@llvm\.vector\.reduce\.add' || true)
  [ "$reduce_seen" -gt 0 ] || fail "(d) the detector did not report llvm.vector.reduce.* in a text that contains it"
  if grep -q 'llvm\.vector\.reduce' "${inventories[2]}"; then
    fail "(d) the fixture's inventory names llvm.vector.reduce.*; the control text is not outside it"
  fi
  printf 'ok: (d) control 1: the detector reports llvm.vector.reduce.add.* in a text carrying it,\n'
  printf '          and the fixture inventory does not name it\n'

  if ! grep -q '@llvm\.x86\.avx2\.pshuf\.b' "${inventories[2]}"; then
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
}

controls_entry() {
  local seen ngep ninv rows tamperlineno bad

  # Control 1: a construct the fragment does not model is reported by the same
  # detector and is outside the fixture's inventory.
  cat > "$work/xor.ll" <<'EOF'
define i64 @probe(i64 %x) {
entry:
  %0 = call i64 @llvm.xor.reduce.i64(i64 %x)
  ret i64 %0
}
EOF
  seen=$(detect "$work/xor.ll" | grep -c '@llvm\.xor\.reduce\.i64' || true)
  [ "$seen" -gt 0 ] || fail "(d) control 1: the detector did not report llvm.xor.reduce.* in a text that contains it"
  if grep -q 'llvm\.xor\.reduce' "${inventories[3]}"; then
    fail "(d) control 1: the fixture's inventory names llvm.xor.reduce.*; the control text is not outside it"
  fi
  printf 'ok: (d) control 1: the detector reports llvm.xor.reduce.i64 in a text carrying it,\n'
  printf '          and the fixture inventory does not name it\n'

  # Control 2: the flag spelling the parser admits at both values is reported
  # inside — by this detector, and by the committed inventory the fixture's own
  # calls produce.
  cat > "$work/cttz.ll" <<'EOF'
define i64 @probe(i64 %x) {
entry:
  %0 = call i64 @llvm.cttz.i64(i64 %x, i1 false)
  ret i64 %0
}
EOF
  seen=$(detect "$work/cttz.ll" | grep -c '@llvm\.cttz\.i64' || true)
  [ "$seen" -gt 0 ] ||
    fail "(d) control 2: the detector did not report llvm.cttz.i64 in a text carrying the i1 false flag"
  grep -qx 'call @llvm.cttz.i64' "${inventories[3]}" ||
    fail "(d) control 2: the fixture's inventory does not name @llvm.cttz.i64, so the accepted flag spelling is not inside it"
  printf 'ok: (d) control 2: the detector reports llvm.cttz.i64 in a text carrying `i1 false`,\n'
  printf '          and the fixture inventory names it\n'

  # Control 3: the table attributor's two outcomes, on texts derived from the
  # committed fixture.  The first pair is the fixture with the rewrite inverted —
  # exactly the table read and the parameter list differ — and the attributor
  # must account for every one of those lines.  The second pair tampers with a
  # GEP that is not the table read, and the attributor must refuse it, naming
  # the line.
  awk 'f && $0 == "}" { print; exit } /^define / { f = 1 } f' "$fixture" > "$work/pos8.ll"
  [ -s "$work/pos8.ll" ] || fail "(d) control 3: the fixture holds no first function"
  ngep=$(grep -c 'getelementptr inbounds <8 x i32>, ptr %tab, i64 ' "$work/pos8.ll" || true)
  [ "$ngep" -gt 0 ] || fail "(d) control 3: the fixture's first function reads no table"

  awk '
    {
      line = $0
      if (NR == 1) sub(/, ptr %tab\)[ \t]*\{[ \t]*$/, ") {", line)
      key = "getelementptr inbounds <8 x i32>, ptr %tab, i64 "
      i = index(line, key)
      if (i > 0) {
        pre = substr(line, 1, i - 1)
        idx = substr(line, i + length(key))
        line = pre "getelementptr inbounds [256 x [8 x i32]], ptr @xl_pos8, i64 0, i64 " idx
      }
      print line
    }
  ' "$work/pos8.ll" > "$work/pos8.emitted.ll"
  ninv=$(grep -c 'getelementptr inbounds \[256 x \[8 x i32\]\], ptr @xl_pos8, i64 0, i64 ' "$work/pos8.emitted.ll" || true)
  [ "$ninv" -eq "$ngep" ] ||
    fail "(d) control 3: the inverted text has $ninv table read(s) and the fixture $ngep"

  if ! bash "$capture" --attribute "$work/pos8.emitted.ll" "$work/pos8.ll" > "$work/attr.rows" 2> "$work/attr.err"; then
    sed -n '1,10p' "$work/attr.err" >&2
    fail "(d) control 3: the attributor refused a pair that differs only in the table read and the parameter list"
  fi
  rows=$(grep -c '^gep	' "$work/attr.rows" || true)
  [ "$rows" -eq "$ngep" ] ||
    fail "(d) control 3: the attributor accounted for $rows table read(s); the pair differs in $ngep"

  tamperlineno=$(awk '
    NR > 1 && index($0, "getelementptr") > 0 && index($0, "ptr %tab") == 0 { print NR; exit }
  ' "$work/pos8.ll")
  [ -n "$tamperlineno" ] ||
    fail "(d) control 3: the fixture's first function has a GEP that is not the table read"
  awk -v n="$tamperlineno" 'NR == n { $0 = $0 " " } { print }' \
    "$work/pos8.ll" > "$work/pos8.tampered.ll"
  if bash "$capture" --attribute "$work/pos8.emitted.ll" "$work/pos8.tampered.ll" \
      > "$work/attr.tampered.rows" 2> "$work/attr.tampered.err"; then
    fail "(d) control 3: the attributor accepted a pair whose differing GEP is not the table read"
  fi
  if ! grep -q 'unattributed' "$work/attr.tampered.err"; then
    sed -n '1,10p' "$work/attr.tampered.err" >&2
    fail "(d) control 3: the attributor refused the tampered pair without reporting the line as unattributed"
  fi
  if ! grep -q "line $tamperlineno" "$work/attr.tampered.err"; then
    sed -n '1,10p' "$work/attr.tampered.err" >&2
    fail "(d) control 3: the attributor's refusal does not name line $tamperlineno"
  fi
  bad=$(grep -c '^gep	' "$work/attr.tampered.rows" || true)
  printf 'ok: (d) control 3: the attributor accounts for all %s table read(s) of a pair\n' "$rows"
  printf '          that differs only there, and refuses a pair whose differing GEP is\n'
  printf '          not the table read, naming line %s as unattributed\n' "$tamperlineno"
}

controls_utf8() {
  local seen usub ptestz
  local inventory=${inventories[2]}

  # Control 1: the refused neighbour of the saturating-subtract spelling.  It is
  # a call the fragment does not model at that width, so the same detector must
  # report it and the fixture's inventory must not name it.
  cat > "$work/usub16.ll" <<'EOF'
define void @probe(<16 x i8> %a, <16 x i8> %b) {
entry:
  %0 = call <16 x i8> @llvm.usub.sat.v16i8(<16 x i8> %a, <16 x i8> %b)
  ret void
}

declare <16 x i8> @llvm.usub.sat.v16i8(<16 x i8>, <16 x i8>)
EOF
  seen=$(detect "$work/usub16.ll" | grep -c '@llvm\.usub\.sat\.v16i8' || true)
  [ "$seen" -gt 0 ] || fail "(d) control 1: the detector did not report llvm.usub.sat.v16i8 in a text that contains it"
  if grep -q 'llvm\.usub\.sat\.v16i8' "$inventory"; then
    fail "(d) control 1: the fixture's inventory names the refused spelling; the control text is not outside it"
  fi
  printf 'ok: (d) control 1: the detector reports llvm.usub.sat.v16i8 in a text carrying it,\n'
  printf '          and the fixture inventory does not name it\n'

  # Control 2: the two spellings the stage calls are inside, by the same
  # detector and by the committed inventory the fixture's own calls produce.
  cat > "$work/stage-spellings.ll" <<'EOF'
define void @probe(<32 x i8> %a, <32 x i8> %b, <4 x i64> %c, <4 x i64> %d) {
entry:
  %0 = call <32 x i8> @llvm.usub.sat.v32i8(<32 x i8> %a, <32 x i8> %b)
  %1 = call i32 @llvm.x86.avx.ptestz.256(<4 x i64> %c, <4 x i64> %d)
  ret void
}

declare <32 x i8> @llvm.usub.sat.v32i8(<32 x i8>, <32 x i8>)
declare i32 @llvm.x86.avx.ptestz.256(<4 x i64>, <4 x i64>)
EOF
  usub=$(detect "$work/stage-spellings.ll" | grep -c '@llvm\.usub\.sat\.v32i8' || true)
  ptestz=$(detect "$work/stage-spellings.ll" | grep -c '@llvm\.x86\.avx\.ptestz\.256' || true)
  [ "$usub" -gt 0 ] || fail "(d) control 2: the detector did not report llvm.usub.sat.v32i8"
  [ "$ptestz" -gt 0 ] || fail "(d) control 2: the detector did not report llvm.x86.avx.ptestz.256"
  grep -qx 'call @llvm.usub.sat.v32i8' "$inventory" ||
    fail "(d) control 2: the fixture's inventory does not name @llvm.usub.sat.v32i8"
  grep -qx 'call @llvm.x86.avx.ptestz.256' "$inventory" ||
    fail "(d) control 2: the fixture's inventory does not name @llvm.x86.avx.ptestz.256"
  printf 'ok: (d) control 2: the detector reports both stage spellings in a text carrying them,\n'
  printf '          and the fixture inventory names them\n'
}

case "$unit" in
  s1) controls_s1 ;;
  entry) controls_entry ;;
  utf8) controls_utf8 ;;
esac

printf '\nok: the fixture is the kernel emission, its inventories are its own, it parses,\n'
printf '    and the inventory detector reports both what is present and what is absent\n'
