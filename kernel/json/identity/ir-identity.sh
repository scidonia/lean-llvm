#!/usr/bin/env bash
# Arm B: the extracted kernel and the measured header are the same code at the
# mask unit's boundary.
#
#   nix develop -c bash kernel/json/identity/ir-identity.sh
#   nix develop -c bash kernel/json/identity/ir-identity.sh --tree-only
#
# Two translation units define the same probe symbol over a 64-byte block and a
# three-word carry: `oracle.c` includes the vendored measured header and calls
# the measured `s1f_masks`; `kernel_probe.c` includes `s1_block.c` and calls the
# extracted one.  Both are compiled with the measured compiler line
# (`build49.sh:17`) and the P2 `-D` set (`build49.sh:21`); the probe is lifted
# out of each module with `llvm-extract`, and `llvm-diff` compares the two
# single-function modules.  Identity is an empty `llvm-diff`: both sides are
# compiled, inlined and optimised by the same compiler, so this compares emitted
# code and not source text.  The flags carry no `-g`, so there is no debug info
# to strip; the module's own file name (`ModuleID`, `source_filename`) is removed
# from both sides, leaving the comparison about code.
#
# "Identical IR" means the instruction text — every opcode, operand, type,
# constant and branch edge.  Analysis metadata is excluded only where that text
# is identical *and* the metadata difference has a cause named in the output:
# here, the TBAA struct-path node's field count, which follows the enumerated
# deletion of the carry type's `prevS`/`bs_prevb`/`bs_prevs`.  A difference with
# no nameable cause is reported as a finding and fails the arm.
#
# Controls, run every time, because an arm that cannot see a change is not
# evidence:
#   --mutate-table  one byte of `s1f_lo_tab` changed in a copy of the kernel
#   --mutate-op     one operand in `s1f_escaped` changed in a copy
# Each must be reported by the same comparison.
#
# Modes: default `--identity --controls`; `--identity` alone compares only.
#   --tree-only  refuse any input path outside the repository (exit 3).
#
# Exit status: 0 when the identity and the requested controls hold, 1 when one
# fails, 3 on a setup fault (an absent input or tool, a control that could not
# be applied), so an absent tool is never read as a difference or as identity.
set -uo pipefail

here=$(cd "$(dirname "$0")" && pwd)
repo=$(cd "$here/../../.." && pwd)
kernel=$repo/kernel/json/s1_block.c
readme=$repo/kernel/json/README.md
oracle=$here/oracle.c
probe_src=$here/kernel_probe.c
probe=stage1_block_probe
cc=clang
cflags=(-O3 -march=x86-64-v3 -mpclmul -std=gnu11 -falign-loops=64 -falign-functions=64)
# `build49.sh:21`'s P2 set, the measured configuration's remaining switches.
defs=(-DPSTAGE=32 -DPMODE=2 -DS1F_XS=5 -DS2_XP=1 -DS2_DEC_GATE=2 -DS1F_XS_DYN=1)

run_identity=0
run_controls=0
tree_only=0
any_mode=0

while [ "$#" -gt 0 ]; do
  case "$1" in
    --identity) run_identity=1; any_mode=1 ;;
    --controls) run_controls=1; any_mode=1 ;;
    --tree-only) tree_only=1 ;;
    -h|--help) sed -n '2,29p' "$0" | sed 's/^# \{0,1\}//'; exit 0 ;;
    *) printf 'ir-identity: unknown argument %s\n' "$1" >&2; exit 3 ;;
  esac
  shift
done
if [ "$any_mode" -eq 0 ]; then run_identity=1; run_controls=1; fi

for path in "$kernel" "$oracle" "$probe_src" "$readme"; do
  [ -e "$path" ] || { printf 'SETUP: absent: %s\n' "$path" >&2; exit 3; }
done
for tool in "$cc" llvm-extract llvm-diff; do
  command -v "$tool" >/dev/null 2>&1 || {
    printf 'SETUP: no %s on PATH; Arm B needs the flake'"'"'s LLVM tools\n' "$tool" >&2
    exit 3
  }
done

require_in_tree() {
  case "$1" in
    "$repo"/*) return 0 ;;
    *) printf 'REFUSED: %s is outside %s and --tree-only was given\n' "$1" "$repo" >&2; exit 3 ;;
  esac
}
[ "$tree_only" -eq 1 ] && for path in "$kernel" "$oracle" "$probe_src" "$readme"; do require_in_tree "$path"; done

mkdir -p "$repo/.lake" || { printf 'SETUP: cannot create %s/.lake\n' "$repo" >&2; exit 3; }
work=$(mktemp -d "$repo/.lake/tmp-s1-ir.XXXXXX" 2>/dev/null) || {
  printf 'SETUP: cannot create a work directory under %s/.lake\n' "$repo" >&2
  exit 3
}
trap 'rm -rf "$work"' EXIT

# compile_probe <name> <source> <extra include dir> [extra args...]
# Leaves $work/<name>.ll holding the module with the probe lifted out.
compile_probe() {
  local name=$1 src=$2 inc=$3
  shift 3
  local ll=$work/$name.ll lifted=$work/$name.probe.ll
  if ! "$cc" "${cflags[@]}" "${defs[@]}" "$@" -I "$inc" -S -emit-llvm \
      -o "$ll" "$src"; then
    printf 'SETUP: %s did not compile\n' "$src" >&2
    return 3
  fi
  if ! llvm-extract -func="$probe" -S "$ll" -o "$lifted"; then
    printf 'SETUP: llvm-extract could not lift @%s out of %s\n' "$probe" "$ll" >&2
    return 3
  fi
  # No debug info is emitted (the flags carry no -g), so there is nothing to
  # strip; this LLVM 21.1.8 has no `strip-debug` pass to strip it with either.
  # The absence is asserted rather than assumed, so a later `-g` fails loudly
  # instead of making the comparison a comparison of debug metadata.
  if grep -qE '!llvm\.dbg|"Debug Info Version"' "$lifted"; then
    printf 'SETUP: %s carries debug info and this LLVM has no strip-debug pass\n' "$lifted" >&2
    printf 'SETUP: compile without -g, or add the strip step the toolchain provides\n' >&2
    return 3
  fi
  # The module's own file name (`ModuleID`, `source_filename`) is the input
  # path, not code; removing it from both sides leaves the comparison about the
  # emitted code and makes the two digests comparable.
  sed -i -e '/^; ModuleID = /d' -e '/^source_filename = /d' "$lifted"
  printf '%s' "$lifted"
}

# compare <expected:identical|different> <a.ll> <b.ll> <label>
compare() {
  local want=$1 a=$2 b=$3
  local label=$4
  local out="$work/diff.$label"
  local status
  llvm-diff "$a" "$b" > "$out" 2>&1
  status=$?
  if [ "$want" = identical ]; then
    if [ "$status" -eq 0 ] && [ ! -s "$out" ]; then
      printf 'ok: %s: llvm-diff reports no difference\n' "$label"
      return 0
    fi
    printf 'FAIL: %s: llvm-diff reports a difference\n' "$label" >&2
    awk 'NR <= 40' "$out" >&2
    return 1
  fi
  if [ "$status" -ne 0 ] || [ -s "$out" ]; then
    printf 'ok: %s: reported as a difference\n' "$label"
    awk 'NR <= 6 { printf "      %s\n", $0 }' "$out"
    return 0
  fi
  printf 'FAIL: %s: the comparison did not see the mutation\n' "$label" >&2
  return 1
}

# --- the metadata exclusion and its named cause ---------------------------

# The identity is the instruction text: every opcode, operand, type, constant
# and branch edge.  Analysis metadata is excluded only where (i) the instruction
# text is identical and (ii) the metadata difference has a cause named here.
# This arm's one such difference is the TBAA struct-path node of the carry type:
# the enumerated deletion of `prevS`, `bs_prevb` and `bs_prevs` leaves the
# kernel's carry with three fields where the measured `S1F` has six, and the
# node lists one `i64` offset per field.  Anything else is a finding, not an
# exclusion.
metadata_cause() { # <measured.ll> <kernel.ll>
  local a=$1 b=$2
  local am=$work/meta.measured bm=$work/meta.kernel
  local an= bn= deleted= k=
  awk '/^!/' "$a" > "$am"
  awk '/^!/' "$b" > "$bm"
  if cmp -s "$am" "$bm"; then
    printf 'metadata: identical\n'
    return 0
  fi
  if ! grep -qE '^![0-9]+ = !\{!"",' "$am" || ! grep -qE '^![0-9]+ = !\{!"",' "$bm"; then
    printf 'FINDING: the metadata sections differ and neither side names an unnamed-struct node\n' >&2
    diff -u "$am" "$bm" | awk 'NR <= 20 { printf "      %s\n", $0 }' >&2
    return 1
  fi
  an=$(grep -m1 -E '^![0-9]+ = !\{!"",' "$am" | grep -o 'i64' | wc -l | tr -d ' ')
  bn=$(grep -m1 -E '^![0-9]+ = !\{!"",' "$bm" | grep -o 'i64' | wc -l | tr -d ' ')
  awk '{ if ($0 ~ /^![0-9]+ = !\{!"",/) sub(/\{!"",.*\}$/, "{!\"\", <fields>}"); print }' \
    "$am" > "$work/meta.measured.norm"
  awk '{ if ($0 ~ /^![0-9]+ = !\{!"",/) sub(/\{!"",.*\}$/, "{!\"\", <fields>}"); print }' \
    "$bm" > "$work/meta.kernel.norm"
  if ! cmp -s "$work/meta.measured.norm" "$work/meta.kernel.norm"; then
    printf 'FINDING: the metadata sections differ beyond the carry type'"'"'s field count\n' >&2
    diff -u "$work/meta.measured.norm" "$work/meta.kernel.norm" \
      | awk 'NR <= 20 { printf "      %s\n", $0 }' >&2
    return 1
  fi
  deleted=$(sed -n '/<!-- identity-list:begin -->/,/<!-- identity-list:end -->/p' "$readme" \
    | sed -n 's/^carry-fields-deleted:[[:space:]]*//p')
  if [ -z "$deleted" ]; then
    printf 'FINDING: metadata differs (struct-path %s -> %s) and no deleted carry field is recorded\n' \
      "$an" "$bn" >&2
    return 1
  fi
  k=$(printf '%s\n' $deleted | wc -l | tr -d ' ')
  if [ "$((an - bn))" -ne "$k" ]; then
    printf 'FINDING: metadata differs (struct-path %s -> %s) but %s carry field(s) are recorded as deleted\n' \
      "$an" "$bn" "$k" >&2
    return 1
  fi
  printf 'metadata: struct-path field count %s -> %s, from the enumerated deletion of %s\n' \
    "$an" "$bn" "$deleted"
  printf '          the identity is the instruction text; this difference has the cause named above\n'
  return 0
}

# --- the identity ---------------------------------------------------------

arm_identity() {
  local a b ca cb
  printf '\n== Arm B: emitted-code identity of @%s\n' "$probe"
  a=$(compile_probe oracle "$oracle" "$here") || return 3
  b=$(compile_probe kernel "$probe_src" "$repo/kernel/json") || return 3
  ca=$(awk '/^!/{exit} {print}' "$a" | sha256sum | cut -d' ' -f1)
  cb=$(awk '/^!/{exit} {print}' "$b" | sha256sum | cut -d' ' -f1)
  printf '   code text digest (the module before its metadata section)\n'
  printf '     measured  %s\n' "$ca"
  printf '     extracted %s\n' "$cb"
  compare identical "$a" "$b" identity || return 1
  if [ "$ca" = "$cb" ]; then
    printf 'ok: the code text is byte-identical\n'
  else
    printf 'FAIL: the code text differs outside the metadata section\n' >&2
    diff -u <(awk '/^!/{exit} {print}' "$a") <(awk '/^!/{exit} {print}' "$b") \
      | awk 'NR <= 40' >&2
    return 1
  fi
  metadata_cause "$a" "$b"
}

# --- the controls ---------------------------------------------------------

# mutate_probe <name> <mutated kernel file>
# Builds a probe TU over the mutated copy in $work and echoes its module.
mutate_probe() {
  local name=$1 src=$2
  cat > "$work/$name.c" <<EOF
#include "$src"
void $probe(const uint8_t *p, void *st, uint64_t *out) {
    __m256i v0 = _mm256_loadu_si256((const __m256i *)(const void *)p);
    __m256i v1 = _mm256_loadu_si256((const __m256i *)(const void *)(p + 32));
    s1f_masks(v0, v1, (S1F *)st, &out[0], &out[1], &out[2], &out[3], &out[4],
              &out[5]);
}
EOF
  compile_probe "$name" "$work/$name.c" "$repo/kernel/json"
}

arm_controls() {
  local base mut module rc=0
  base=$(compile_probe kernel "$probe_src" "$repo/kernel/json") || return 3

  # --mutate-table: bit 0 of the first byte of `s1f_lo_tab`.
  mut=$work/s1_block.table.c
  awk '
    { if (!done && index($0, "s1f_lo_tab[32]") > 0) in_tab = 1
      if (in_tab && !done && index($0, "0x40,") > 0) { sub(/0x40,/, "0x41,"); done = 1 }
      print }
  ' "$kernel" > "$mut"
  if cmp -s "$kernel" "$mut"; then
    printf 'SETUP: the table control did not apply to %s\n' "$kernel" >&2
    return 3
  fi
  printf '\n== Control: one byte of s1f_lo_tab changed\n'
  module=$(mutate_probe kernel_table "$mut") || return 3
  compare different "$base" "$module" table || rc=1

  # --mutate-op: the left operand of `s1f_escaped`'s `alt = even_slots ^ …`.
  mut=$work/s1_block.op.c
  awk '
    { if (!done && index($0, "0x5555555555555555ULL") > 0) {
        sub(/0x5555555555555555ULL/, "0x5555555555555554ULL"); done = 1 }
      print }
  ' "$kernel" > "$mut"
  if cmp -s "$kernel" "$mut"; then
    printf 'SETUP: the operand control did not apply to %s\n' "$kernel" >&2
    return 3
  fi
  printf '\n== Control: one operand in s1f_escaped changed\n'
  module=$(mutate_probe kernel_op "$mut") || return 3
  compare different "$base" "$module" operand || rc=1

  return "$rc"
}

if [ "$run_identity" -eq 1 ]; then arm_identity || exit $?; fi
if [ "$run_controls" -eq 1 ]; then arm_controls || exit $?; fi
printf '\nok: IR identity holds\n'
