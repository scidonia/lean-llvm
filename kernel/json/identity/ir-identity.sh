#!/usr/bin/env bash
# Arm B: the extracted unit and the measured header are the same code at the
# unit's boundary.
#
#   nix develop -c bash kernel/json/identity/ir-identity.sh              # s1
#   nix develop -c bash kernel/json/identity/ir-identity.sh --tree-only
#   nix develop -c bash kernel/json/identity/ir-identity.sh --unit entry # the entry unit
#
# Units (`--unit s1` is the default, so every existing invocation keeps its
# meaning and its exit codes):
#
#   s1     the mask unit.  Two translation units define the same probe symbol
#          over a 64-byte block and a three-word carry: `oracle.c` includes the
#          vendored measured header and calls the measured `s1f_masks`;
#          `kernel_probe.c` includes `s1_block.c` and calls the extracted one.
#          The probe is lifted out of each module with `llvm-extract` and
#          `llvm-diff` compares the two single-function modules.
#   entry  the entry unit.  `entry_oracle.c` includes the vendored headers and
#          calls the measured `s1f_k_pos8` and `s1f_k_b8`; `entry_probe.c`
#          includes `entry.c` and calls the same two names.  Both are lifted
#          **by name**, together with the table's global, and the arm asserts
#          each lifted module holds exactly those two functions and no other,
#          so a probe that dragged a third function in, or a lift that dropped
#          one of the two, is a setup fault rather than identity.
#
# Both units: both sides are compiled with the measured compiler line
# (`build49.sh:17`); `s1` adds the P2 `-D` set (`build49.sh:21`) and `entry` the
# measured one (`build49.sh:19-21`) with `S1F_UTF8` left at the header's default
# because `u8kl.h` is not vendored and no claim here reaches the UTF-8 probe.
# Identity is an empty `llvm-diff`: both sides are compiled, inlined and
# optimised by the same compiler, so this compares emitted code and not source
# text.  The flags carry no `-g`, so there is no debug info to strip; the
# module's own file name (`ModuleID`, `source_filename`) is removed from both
# sides, leaving the comparison about code.
#
# "Identical IR" means the instruction text -- every opcode, operand, type,
# constant and branch edge.  Analysis metadata is excluded only where that text
# is identical *and* the metadata difference has a cause named in the output.
# The two units differ here, and the difference is stated rather than shared:
#
#   s1     the TBAA struct-path node's field count follows the enumerated
#          deletion of the carry type's `prevS`/`bs_prevb`/`bs_prevs`.
#   entry  no exclusion.  The two lifted modules are the same node graph --
#          their node *numbers* differ because each side was serialised from a
#          different source module -- so the metadata sections are compared as
#          a canonical graph: every node's text with its references replaced by
#          the referenced node's canonical text (a cycle is the `distinct` loop
#          node's self-reference), and the two multisets must be equal.  That
#          sees a changed node kind, string or integer, and is blind only to a
#          rewiring between nodes whose canonical texts are identical, which is
#          why the node count is printed beside it.
#
# The entry unit's table is computed by `xl_pos8_init`, so the only place a
# table byte exists in the lifted module is the global's own initialiser, and
# that definition is part of the comparison.  `llvm-diff` compares code and not
# global initialisers, so the arm compares `@xl_pos8`'s definition itself: the
# table's content is a definition, and the instrument needs it, so this is the
# comparison rather than an exclusion.
# `--mutate-table` demonstrates that this half bites, and the route (not this
# arm) is what compares the table's *content*.
#
# Controls, run every time, because an arm that cannot see a change is not
# evidence:
#   s1     --mutate-table  one byte of `s1f_lo_tab` changed in a copy of the kernel
#          --mutate-op     one operand in `s1f_escaped` changed in a copy
#   entry  --mutate-table  row 0x2C of the table's initialiser changed (entry 0 -> 1)
#          --mutate-slot   one slot index in `s1f_ke_b8`'s chain changed
# Each must be reported by the instrument that can see it, and both verdicts are
# printed for each control.
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
readme=$repo/kernel/json/README.md
cc=clang
cflags=(-O3 -march=x86-64-v3 -mpclmul -std=gnu11 -falign-loops=64 -falign-functions=64)

unit=s1
run_identity=0
run_controls=0
tree_only=0
any_mode=0

usage() {
  awk 'NR > 1 && /^set -/ { exit } NR > 1 { print }' "$0" | sed 's/^# \{0,1\}//' 
}

while [ "$#" -gt 0 ]; do
  case "$1" in
    --unit) shift; unit=${1:-}; [ -n "$unit" ] || { printf 'ir-identity: --unit needs a value\n' >&2; exit 3; } ;;
    --unit=*) unit=${1#--unit=} ;;
    --identity) run_identity=1; any_mode=1 ;;
    --controls) run_controls=1; any_mode=1 ;;
    --tree-only) tree_only=1 ;;
    -h|--help) usage; exit 0 ;;
    *) printf 'ir-identity: unknown argument %s\n' "$1" >&2; exit 3 ;;
  esac
  shift
done
if [ "$any_mode" -eq 0 ]; then run_identity=1; run_controls=1; fi

# The unit's own data: its kernel file, its two probe TUs, the symbol(s) the
# lift names, the `-D` set, and whether the lifted module's functions are the
# probe or the two kernels by name.
case "$unit" in
  s1)
    kernel=$repo/kernel/json/s1_block.c
    oracle=$here/oracle.c
    probe_src=$here/kernel_probe.c
    probe=stage1_block_probe
    defs=(-DPSTAGE=32 -DPMODE=2 -DS1F_XS=5 -DS2_XP=1 -DS2_DEC_GATE=2 -DS1F_XS_DYN=1)
    lift=(-func="$probe")
    lift_functions=""
    by_name=0
    ;;
  entry)
    kernel=$repo/kernel/json/entry.c
    oracle=$here/entry_oracle.c
    probe_src=$here/entry_probe.c
    probe=entry_stream_probe
    # `build49.sh:19-21`'s measured set, with the UTF-8 switch at its default
    # 0: `u8kl.h` is not vendored and this unit is not the UTF-8 probe.
    defs=(-DSTAGE_PROBE -DS1F_ENT_PROBE=1 -DS1F_DENS=1 -DS1F_TWOPHASE=1
          -DS1F_EXP2=11 -DS1F_DISPATCH=1 -DS1F_UTF8=0 -DS1F_KL_DOC=0 -DPSTAGE=32
          -DPMODE=2 -DS1F_XS=5 -DS2_XP=1 -DS2_DEC_GATE=2 -DS1F_XS_DYN=1)
    lift=(-func=s1f_k_pos8 -func=s1f_k_b8 -glob=xl_pos8)
    lift_functions="s1f_k_b8 s1f_k_pos8"
    by_name=1
    ;;
  *)
    printf 'SETUP: unit %s has no IR identity arm; implemented units: s1 entry\n' "$unit" >&2
    exit 3
    ;;
esac

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
work=$(mktemp -d "$repo/.lake/tmp-$unit-ir.XXXXXX" 2>/dev/null) || {
  printf 'SETUP: cannot create a work directory under %s/.lake\n' "$repo" >&2
  exit 3
}
trap 'rm -rf "$work"' EXIT

# compile_probe <name> <source> <extra include dir> [extra args...]
# Leaves $work/<name>.ll holding the module with the unit's symbols lifted out.
compile_probe() {
  local name=$1 src=$2 inc=$3
  shift 3
  local ll=$work/$name.ll lifted=$work/$name.probe.ll
  if ! "$cc" "${cflags[@]}" "${defs[@]}" "$@" -I "$inc" -S -emit-llvm \
      -o "$ll" "$src"; then
    printf 'SETUP: %s did not compile\n' "$src" >&2
    return 3
  fi
  if ! llvm-extract "${lift[@]}" -S "$ll" -o "$lifted"; then
    printf 'SETUP: llvm-extract could not lift %s out of %s\n' "${lift[*]}" "$ll" >&2
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

# compare <expected:identical|different|report> <a.ll> <b.ll> <label>
# `report` prints which way `llvm-diff` went and asserts nothing: it is how a
# control shows what the instruction comparison can and cannot see.
compare() {
  local want=$1 a=$2 b=$3
  local label=$4
  local out="$work/diff.$label"
  local status
  llvm-diff "$a" "$b" > "$out" 2>&1
  status=$?
  if [ "$want" = report ]; then
    if [ "$status" -eq 0 ] && [ ! -s "$out" ]; then
      printf '   %s: llvm-diff reports no difference\n' "$label"
    else
      printf '   %s: llvm-diff reports a difference\n' "$label"
      awk 'NR <= 6 { printf "      %s\n", $0 }' "$out"
    fi
    return 0
  fi
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

# --- the lifted module's shape, for the by-name unit ----------------------

# defined_functions <file> -- the sorted names of the functions it defines.
defined_functions() {
  awk '/^define / {
         name = $0
         sub(/.*@/, "", name); sub(/\(.*/, "", name)
         print name
       }' "$1" | LC_ALL=C sort
}

# global_definition <file> <name> -- the one line that defines the global.
global_definition() {
  awk -v name="$2" '
    $1 == "@" name && $2 == "=" {
      line = $0
      sub(/^[^ ]+ [^ ]+ /, "", line)
      if (line !~ /^external /) print $0
      found = 1
      exit
    }
    END { if (!found) printf "" }
  ' "$1"
}

assert_lifted_shape() { # <file> <side>
  local file=$1 side=$2 got
  got=$(defined_functions "$file")
  if [ "$got" != "$(printf '%s\n' $lift_functions | LC_ALL=C sort)" ]; then
    printf 'SETUP: the %s module defines {%s}, not {%s}\n' \
      "$side" "$(echo $got)" "$(echo $lift_functions)" >&2
    return 3
  fi
  printf 'ok: the %s module defines exactly %s\n' "$side" "$(echo $got | tr ' ' ',')"
}

# The table's definition, carried on both sides rather than excused from the
# comparison: `llvm-diff` compares code and not global initialisers, so this
# line is compared here.
compare_global() { # <expected:identical|different> <a.ll> <b.ll> <label>
  local want=$1 a=$2 b=$3 label=$4
  local la lb
  la=$(global_definition "$a" xl_pos8)
  lb=$(global_definition "$b" xl_pos8)
  if [ -z "$la" ] || [ -z "$lb" ]; then
    printf 'SETUP: %s: a side does not define @xl_pos8\n' "$label" >&2
    return 3
  fi
  if [ "$want" = identical ]; then
    if [ "$la" = "$lb" ]; then
      printf 'ok: %s: @xl_pos8'"'"'s definition is identical\n     %s\n' "$label" "$la"
      return 0
    fi
    printf 'FAIL: %s: @xl_pos8'"'"'s definition differs\n     measured  %s\n     extracted %s\n' \
      "$label" "$la" "$lb" >&2
    return 1
  fi
  if [ "$la" != "$lb" ]; then
    printf 'ok: %s: @xl_pos8'"'"'s definition moved\n     measured  %s\n     mutated   %s\n' \
      "$label" "$la" "$lb"
    return 0
  fi
  printf 'FAIL: %s: the global comparison did not see the mutation\n' "$label" >&2
  return 1
}

# --- the metadata comparison ----------------------------------------------

# The s1 unit's one named cause: the TBAA struct-path node of the carry type.
# The enumerated deletion of `prevS`, `bs_prevb` and `bs_prevs` leaves the
# kernel's carry with three fields where the measured `S1F` has six, and the
# node lists one `i64` offset per field.  Anything else is a finding.
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

# canon_metadata <file> -- one line per metadata node, sorted: the node's text
# with every reference replaced by the referenced node's canonical text, so the
# numbering a module happens to assign cancels out.
canon_metadata() { # <file>
  awk '
    /^![0-9]+ = / {
      id = $1
      text = $0
      sub(/^[^ ]+ = /, "", text)
      txt[id] = text
      ids[++n] = id
    }
    END { for (i = 1; i <= n; i++) print label(ids[i]) }
    function label(id,   t, out) {
      if (id in memo) return memo[id]
      if (id in busy) return "SELF"
      if (!(id in txt)) return "UNRESOLVED"
      busy[id] = 1
      t = txt[id]
      out = ""
      while (match(t, /![0-9]+/)) {
        out = out substr(t, 1, RSTART - 1) "!" label(substr(t, RSTART + 1, RLENGTH - 1))
        t = substr(t, RSTART + RLENGTH)
      }
      out = out t
      delete busy[id]
      memo[id] = out
      return out
    }
  ' "$1" | LC_ALL=C sort
}

# metadata_graph <a.ll> <b.ll> -- the entry unit's no-exclusion comparison.
metadata_graph() { # <measured.ll> <extracted.ll>
  local a=$1 b=$2 count
  canon_metadata "$a" > "$work/meta.graph.measured"
  canon_metadata "$b" > "$work/meta.graph.extracted"
  count=$(wc -l < "$work/meta.graph.measured" | tr -d ' ')
  if cmp -s "$work/meta.graph.measured" "$work/meta.graph.extracted"; then
    printf 'ok: metadata: %s nodes, equal as a graph (node numbering is per-module)\n' "$count"
    return 0
  fi
  printf 'FINDING: the metadata graphs differ\n' >&2
  diff -u "$work/meta.graph.measured" "$work/meta.graph.extracted" \
    | awk 'NR <= 20 { printf "      %s\n", $0 }' >&2
  return 1
}

# --- the identity ---------------------------------------------------------

arm_identity() {
  local a b ca cb
  printf '\n== Arm B (%s): emitted-code identity\n' "$unit"
  a=$(compile_probe oracle "$oracle" "$here") || return 3
  b=$(compile_probe kernel "$probe_src" "$repo/kernel/json") || return 3
  if [ "$by_name" -eq 1 ]; then
    assert_lifted_shape "$a" measured || return $?
    assert_lifted_shape "$b" extracted || return $?
  fi
  if [ "$by_name" -eq 0 ]; then
    ca=$(awk '/^!/{exit} {print}' "$a" | sha256sum | cut -d' ' -f1)
    cb=$(awk '/^!/{exit} {print}' "$b" | sha256sum | cut -d' ' -f1)
    printf '   code text digest (the module before its metadata section)\n'
    printf '     measured  %s\n' "$ca"
    printf '     extracted %s\n' "$cb"
  fi
  compare identical "$a" "$b" identity || return 1
  if [ "$by_name" -eq 0 ]; then
    if [ "$ca" = "$cb" ]; then
      printf 'ok: the code text is byte-identical\n'
    else
      printf 'FAIL: the code text differs outside the metadata section\n' >&2
      diff -u <(awk '/^!/{exit} {print}' "$a") <(awk '/^!/{exit} {print}' "$b") \
        | awk 'NR <= 40' >&2
      return 1
    fi
    metadata_cause "$a" "$b"
  else
    compare_global identical "$a" "$b" identity || return 1
    metadata_graph "$a" "$b"
  fi
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

# mutate_entry_probe <name> <mutated kernel file> -- the entry unit's shape.
mutate_entry_probe() {
  local name=$1 src=$2
  cat > "$work/$name.c" <<EOF
#include "$src"
uint64_t $probe(uint64_t *ent, uint64_t blk0, uint64_t nblk,
                uint32_t *out, uint64_t k, int kern) {
    return kern ? s1f_k_b8(ent, blk0, nblk, out, k)
                : s1f_k_pos8(ent, blk0, nblk, out, k);
}
EOF
  compile_probe "$name" "$work/$name.c" "$repo/kernel/json"
}

arm_controls() {
  if [ "$by_name" -eq 1 ]; then
    arm_controls_entry
    return $?
  fi

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

# The entry unit's two controls.  The table's rows are written at run time, so
# the only place a table byte reaches the module is the global's initialiser:
# the table control changes it there, and the global comparison is the
# instrument that reports it.  The slot control changes instruction text, which
# is what `llvm-diff` compares.
arm_controls_entry() {
  local base mut module rc=0 st=0
  base=$(compile_probe kernel "$probe_src" "$repo/kernel/json") || return 3

  # --mutate-table: row 0x2C's first entry, 2 -> 1, carried as the global's
  # initialiser (row 0x2C's set lanes are 2, 3 and 5, so the measured row opens
  # with 2).
  mut=$work/entry.table.c
  awk '
    { if (!done && index($0, "static uint32_t xl_pos8[256][8]") > 0) {
        sub(/;[ \t]*$/, " = {[0x2C] = {1}};")
        done = 1 }
      print }
  ' "$kernel" > "$mut"
  if cmp -s "$kernel" "$mut"; then
    printf 'SETUP: the table control did not apply to %s\n' "$kernel" >&2
    return 3
  fi
  printf '\n== Control: table row 0x2C changed, as the global'"'"'s initialiser\n'
  module=$(mutate_entry_probe kernel_table "$mut") || return 3
  compare report "$base" "$module" table-instruction
  compare_global different "$base" "$module" table-global
  st=$?
  [ "$st" -ne 0 ] && rc=$st
  if [ "$rc" -eq 0 ]; then
    printf '   the instruction comparison does not see an initialiser (it compares code);\n'
    printf '   the global comparison is what reports this control, which is why it is here\n'
  fi

  # --mutate-slot: the fifth slot's index in `s1f_ke_b8`'s chain.
  mut=$work/entry.slot.c
  awk '
    { if (!done && index($0, "o[5] = base +") > 0) {
        sub(/o\[5\] = base \+/, "o[6] = base +"); done = 1 }
      print }
  ' "$kernel" > "$mut"
  if cmp -s "$kernel" "$mut"; then
    printf 'SETUP: the slot control did not apply to %s\n' "$kernel" >&2
    return 3
  fi
  printf '\n== Control: one slot index in s1f_ke_b8 changed\n'
  module=$(mutate_entry_probe kernel_slot "$mut") || return 3
  compare different "$base" "$module" slot-instruction
  st=$?
  [ "$st" -ne 0 ] && rc=$st
  compare_global identical "$base" "$module" slot-global
  st=$?
  [ "$st" -ne 0 ] && rc=$st

  return "$rc"
}

if [ "$run_identity" -eq 1 ]; then arm_identity || exit $?; fi
if [ "$run_controls" -eq 1 ]; then arm_controls || exit $?; fi
printf '\nok: IR identity holds (%s)\n' "$unit"
