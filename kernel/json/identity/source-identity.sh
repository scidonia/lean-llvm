#!/usr/bin/env bash
# Arm A: the extracted unit's text is the measured text, modulo the deletion
# list — plus the one preprocessor check that makes Arm B's oracle faithful.
#
#   nix develop -c bash kernel/json/identity/source-identity.sh             # A + its control
#   nix develop -c bash kernel/json/identity/source-identity.sh --arms-only # C1
#   nix develop -c bash kernel/json/identity/source-identity.sh --vendor    # C4
#   nix develop -c bash kernel/json/identity/source-identity.sh --preprocess # the macro-set arm
#   nix develop -c bash kernel/json/identity/source-identity.sh --all
#   nix develop -c bash kernel/json/identity/source-identity.sh --unit entry
#
# Units (`--unit s1` is the default, so every existing invocation keeps its
# meaning and its exit codes):
#
#   s1     the mask unit, `kernel/json/s1_block.c`, against the seven entities
#          `README.md`'s `entities:` line names in `measured/s1fuse.h`.
#   entry  the entry unit, `kernel/json/entry.c`, against the seven entities
#          `README.md`'s `entry-entities:` line names across `measured/s1fuse.h`
#          and `measured/xlist.h`, with that unit's own deletion list.
#
# Modes (default: --identity --mutate):
#   --identity    extract the entities `kernel/json/README.md` lists from the
#                 vendored headers, drop the lines the same block lists,
#                 normalise comments and whitespace, and require the tokens to
#                 equal the same entities' tokens in the unit's C file.
#   --mutate      the control: rewrite one numeral in a copy of the kernel and
#                 require the same comparison to report a difference.  A
#                 comparison that cannot see a numeral changed is not evidence.
#                 The entry unit runs a second control, a changed slot index in
#                 the `ctz` chain, because its second kernel is a different
#                 shape from the first and one control does not exercise both.
#   --arms-only   C1: compile the unit as a standalone translation unit with
#                 the pinned flags, then preprocess it and require the arm
#                 detector to name nothing; run the same detector on the
#                 measured header's translation unit and require it to name at
#                 least one thing, so the detector is not vacuous.  For the
#                 entry unit the detector is the measurement vocabulary without
#                 `xl_`, whose names are checked separately against the
#                 exemption the README records, and the unit's public symbols
#                 are asserted to be exactly its three ABI functions.
#   --vendor      C4: `sha256sum -c` over `measured/SHA256SUMS`, the anchored
#                 line ranges of `measured/s1fuse.h`, and — while it survives —
#                 a live `diff -u` against the scratch tree the set was copied
#                 from.  The scratch tree is corroboration, not a dependency.
#                 This arm is about the vendored set, not about a unit.
#   --preprocess  the mask region is invariant to the macro set.  It is the
#                 s1 unit's claim only: the entry unit's entities exist only at
#                 `S1F_EXP2=11`, so asking for this mode with `--unit entry` is
#                 a setup fault rather than a silent vacuous pass.
#   --tree-only   refuse any input path outside the repository (exit 3).  Under
#                 it, --vendor refuses while the scratch tree exists, because
#                 the live diff asks to read a path outside the repository.
#
# Exit status: 0 when every requested arm holds, 1 when one fails, 3 on a setup
# fault (an absent input or tool, a malformed identity list, a divergence in
# --preprocess that is a setup fault rather than an assertion, a fourth `xl_`
# name in the entry unit), so a missing dependency is never read as a passing or
# a failing claim.
set -uo pipefail

here=$(cd "$(dirname "$0")" && pwd)
repo=$(cd "$here/../../.." && pwd)
measured=$repo/kernel/json/measured
header_src=$measured/s1fuse.h
readme=$repo/kernel/json/README.md
scratch=/tmp/scidonia-spike45/src
cc=clang

unit=s1

# The measured compiler line (`build49.sh:17`).
cflags=(-O3 -march=x86-64-v3 -mpclmul -std=gnu11 -falign-loops=64 -falign-functions=64)

# The measured translation unit's `-D` set (`build49.sh:19-21`): $S1 $U8 $P2.
measured_defs=(
  -DSTAGE_PROBE -DS1F_ENT_PROBE=1 -DS1F_DENS=1 -DS1F_TWOPHASE=1 -DS1F_EXP2=11
  -DS1F_DISPATCH=1 -DS1F_UTF8=7 -DS1F_KL_DOC=1 -DPSTAGE=32 -DPMODE=2 -DS1F_XS=5
  -DS2_XP=1 -DS2_DEC_GATE=2 -DS1F_XS_DYN=1
)
# The oracle's reduced set: the two macros `s1f_masks` reads, and nothing else
# (the macro-set arm).  The remaining switches stay at the header's defaults,
# which is what `--preprocess` compares against the measured set.
oracle_defs=(-DS1F_XS=5 -DS1F_CTAB=1)

# The arm detector of C1: an identifier in the measured build's vocabulary.
detector='\b(dens_|xl_|kl_|S1F_|SP_|sp_)[A-Za-z0-9_]*'
# The same vocabulary without `xl_`, for the entry unit, whose table is named by
# three exempt `xl_` identifiers the README records.
detector_no_xl='\b(dens_|kl_|S1F_|SP_|sp_)[A-Za-z0-9_]*'
detector_xl='\bxl_[A-Za-z0-9_]*'

run_identity=0
run_mutate=0
run_arms=0
run_vendor=0
run_preprocess=0
tree_only=0
any_mode=0

usage() {
  awk 'NR > 1 && /^set -/ { exit } NR > 1 { print }' "$0" | sed 's/^# \{0,1\}//' 
}

while [ "$#" -gt 0 ]; do
  case "$1" in
    --unit) shift; unit=${1:-}; [ -n "$unit" ] || { printf 'source-identity: --unit needs a value\n' >&2; exit 3; } ;;
    --unit=*) unit=${1#--unit=} ;;
    --identity) run_identity=1; any_mode=1 ;;
    --mutate) run_mutate=1; any_mode=1 ;;
    --arms-only) run_arms=1; any_mode=1 ;;
    --vendor) run_vendor=1; any_mode=1 ;;
    --preprocess) run_preprocess=1; any_mode=1 ;;
    --all) run_identity=1; run_mutate=1; run_arms=1; run_vendor=1; run_preprocess=1; any_mode=1 ;;
    --tree-only) tree_only=1 ;;
    -h|--help) usage; exit 0 ;;
    *) printf 'source-identity: unknown argument %s\n' "$1" >&2; exit 3 ;;
  esac
  shift
done

if [ "$any_mode" -eq 0 ]; then
  run_identity=1
  run_mutate=1
fi

case "$unit" in
  s1)
    kernel=$repo/kernel/json/s1_block.c
    oracle=$here/oracle.c
    input_paths=("$kernel" "$repo/kernel/json/s1_block.h" "$header_src" "$readme" "$oracle")
    ;;
  entry)
    kernel=$repo/kernel/json/entry.c
    oracle=""
    input_paths=("$kernel" "$repo/kernel/json/entry.h" "$header_src" "$measured/xlist.h" "$readme")
    ;;
  *)
    printf 'SETUP: unit %s has no source identity arm; implemented units: s1 entry\n' "$unit" >&2
    exit 3
    ;;
esac

for path in "${input_paths[@]}"; do
  [ -e "$path" ] || { printf 'SETUP: absent: %s\n' "$path" >&2; exit 3; }
done
command -v "$cc" >/dev/null 2>&1 || {
  printf 'SETUP: no %s on PATH\n' "$cc" >&2
  exit 3
}

require_in_tree() {
  case "$1" in
    "$repo"/*) return 0 ;;
    *) printf 'REFUSED: %s is outside %s and --tree-only was given\n' "$1" "$repo" >&2; exit 3 ;;
  esac
}
[ "$tree_only" -eq 1 ] && for path in "${input_paths[@]}"; do require_in_tree "$path"; done

if [ "$run_preprocess" -eq 1 ] && [ "$unit" != s1 ]; then
  printf 'SETUP: --preprocess is the s1 unit'"'"'s claim; the entry entities exist only at\n' >&2
  printf 'SETUP: S1F_EXP2=11, so no macro-set invariance is claimed for them (exit 3)\n' >&2
  exit 3
fi

# A private work directory inside the checkout, so a --tree-only run touches
# nothing outside it.  `.lake` is a build directory and is not tracked.
mkdir -p "$repo/.lake" || { printf 'SETUP: cannot create %s/.lake\n' "$repo" >&2; exit 3; }
work=$(mktemp -d "$repo/.lake/tmp-$unit-identity.XXXXXX" 2>/dev/null) || {
  printf 'SETUP: cannot create a work directory under %s/.lake\n' "$repo" >&2
  exit 3
}
trap 'rm -rf "$work"' EXIT

# --- the identity list, read from the README -------------------------------

list_block=$(sed -n '/<!-- identity-list:begin -->/,/<!-- identity-list:end -->/p' "$readme")
if [ -z "$list_block" ]; then
  printf 'SETUP: %s carries no <!-- identity-list:begin --> block\n' "$readme" >&2
  exit 3
fi

# list_field <key> -- the whitespace-separated values of every `<key>:` line.
list_field() {
  printf '%s\n' "$list_block" | sed -n "s/^$1:[[:space:]]*//p" | tr '\n' ' ' \
    | sed -e 's/^ //' -e 's/ $//'
}

# entity_specs: `<source>:<entity>` pairs; deletion_specs: `<source>:<ranges>`.
# The s1 unit has one source header, so its bare lists are prefixed here and
# both units are read by one code path below.
case "$unit" in
  s1)
    entity_specs=$(list_field entities | tr ' ' '\n' | sed 's/^/s1fuse:/' | tr '\n' ' ')
    entity_specs=${entity_specs% }
    deletion_specs=$(printf '%s\n' "$list_block" | sed -n 's/^delete:[[:space:]]*//p' \
      | sed 's/^/s1fuse:/' | tr '\n' ' ')
    deletion_specs=${deletion_specs% }
    extra_specs="s1fuse:leanllvm_json_s1_masks"
    defs_re="s1f_[a-z0-9_]+|leanllvm_json_s1_masks"
    xl_exempt=""
    ;;
  entry)
    entity_specs=$(list_field entry-entities)
    deletion_specs=$(list_field entry-delete)
    extra_specs=$(list_field entry-extra)
    defs_re="s1f_[a-z0-9_]+|xl_[a-z0-9_]+|S1F_[A-Za-z0-9_]+|leanllvm_json_entry_[a-z0-9_]+"
    xl_exempt=$(list_field entry-xl-exempt)
    ;;
esac

if [ -z "$entity_specs" ]; then
  printf 'SETUP: the %s identity list names no entities\n' "$unit" >&2
  exit 3
fi
printf 'unit:          %s\n' "$unit"
printf 'identity list: %s\n' "$entity_specs"
printf 'delete list:   %s\n' "$deletion_specs"

# source_file <source> -- the vendored file an entity or a deletion row came from.
source_file() { # <source>
  case "$1" in
    s1fuse) printf '%s' "$header_src" ;;
    xlist) printf '%s' "$measured/xlist.h" ;;
    *) printf 'SETUP: the identity list names an unknown source %s\n' "$1" >&2; return 3 ;;
  esac
}

# deletions_for <source> -- that source's ranges, space-separated.
deletions_for() { # <source>
  local s
  for s in $deletion_specs; do
    case "$s" in
      "$1":*) printf '%s ' "${s#"$1":}" ;;
    esac
  done
}

# Extract one top-level definition: it starts on a column-0 line naming the
# entity and ends where the entity's own text ends.  Lines in `skip` are
# dropped.  This is the only place a name is turned into text, so an entity or
# a deletion the README does not list cannot be excused.
#
# The end is one of four shapes, and the measured sources use all four:
#   - a preprocessor definition (`#define NAME(...)`): through the last line
#     whose trailing backslash continues it;
#   - a braced definition (`static inline uint64_t f(...) {`): through the line
#     that closes the brace it opened;
#   - a declaration ending in `;` (a table, a flag): that line;
#   - a macro invocation (`S1F_DEFINE_KERNEL(s1f_k_pos8, s1f_ke_pos8)`): that
#     line.
extract_entity() { # <file> <entity> <skip-list>
  awk -v name="$2" -v skip="$3" '
    { line[NR] = $0 }
    END {
      n = split(skip, parts, " ")
      for (i = 1; i <= n; i++) {
        if (parts[i] ~ /^[0-9]+-[0-9]+$/) {
          split(parts[i], r, "-")
          for (l = r[1] + 0; l <= r[2] + 0; l++) drop[l] = 1
        } else if (parts[i] != "") drop[parts[i] + 0] = 1
      }
      start = 0
      for (l = 1; l <= NR; l++) {
        if (line[l] ~ /^#define[ \t]/ && index(line[l], name) > 0) { start = l; break }
        if (line[l] ~ /^[^ \t#\/]/ && index(line[l], name) > 0 &&
            (index(line[l], "(") > 0 || index(line[l], "[") > 0)) { start = l; break }
      }
      if (!start) { printf "no definition of %s in %s\n", name, FILENAME > "/dev/stderr"; exit 1 }
      define = (line[start] ~ /^#define[ \t]/)
      depth = 0; opened = 0
      for (l = start; l <= NR; l++) {
        if (!(l in drop)) print line[l]
        if (define) {
          if (line[l] !~ /\\[ \t]*$/) break
          continue
        }
        probe = line[l]
        o = gsub(/\{/, "{", probe); c = gsub(/\}/, "}", probe)
        depth += o - c
        if (o > 0) opened = 1
        if (opened && depth == 0) break
        if (!opened && (line[l] ~ /;[ \t]*$/ || line[l] ~ /)[ \t]*$/)) break
      }
    }
  ' "$1"
}

# Comments and whitespace are representation; the tokens are the content.
normalise() {
  "$cc" -E -P -x c - 2>/dev/null | tr '\n\t' '  ' | tr -s ' ' | sed -e 's/^ //' -e 's/ $//'
}

# A preprocessor definition has no preprocessed text of its own: `-E` prints
# nothing for a `#define` that is never used.  So its normal form is its
# expansion, forced by one invocation appended to the definition — the same
# invocation on both sides, so it adds no difference and the comparison is of
# what the macro means.
normalise_entity() { # <entity>
  local entity=$1 text
  text=$(cat)
  case "$text" in
    '#define'*)
      { printf '%s\n' "$text"; printf '%s(PROBE_NAME, PROBE_BLOCK)\n' "$entity"; } \
        | normalise
      ;;
    *) printf '%s\n' "$text" | normalise ;;
  esac
}

# compare_entities <kernel-file> <label>
# Prints one line per entity and returns 0 iff every entity's tokens match.
compare_entities() {
  local kfile=$1 label=$2 spec name src entity meas kern rc=0
  for spec in $entity_specs; do
    src=${spec%%:*}
    entity=${spec#*:}
    if ! meas=$(extract_entity "$(source_file "$src")" "$entity" "$(deletions_for "$src")" \
        | normalise_entity "$entity"); then
      printf 'SETUP: cannot extract %s from %s\n' "$entity" "$(source_file "$src")" >&2
      return 3
    fi
    if ! kern=$(extract_entity "$kfile" "$entity" "" | normalise_entity "$entity"); then
      printf 'SETUP: cannot extract %s from %s\n' "$entity" "$kfile" >&2
      return 3
    fi
    if [ "$meas" = "$kern" ]; then
      printf 'ok: %-8s %-18s identical (%s token bytes)\n' "$label" "$entity" "${#meas}"
    else
      rc=1
      printf 'DIFF: %-8s %-18s differs\n' "$label" "$entity" >&2
      diff -u <(printf '%s\n' "$meas" | tr ' ' '\n') \
              <(printf '%s\n' "$kern" | tr ' ' '\n') \
        | sed -e '1,2d' -e 's/^/      /' | awk 'NR <= 20' >&2
    fi
  done
  return "$rc"
}

# --- Arm A and its control -------------------------------------------------

# The list is bilateral: a definition in the kernel that it does not name is a
# copy the diff above never looked at.  The exceptions are the unit's new text,
# which README.md and the unit's header declare, and they are data.
arm_identity() {
  local rc defs extra re
  printf '\n== Arm A (%s): token identity, against %s\n' "$unit" "$kernel"
  compare_entities "$kernel" identity
  rc=$?

  re="($defs_re)[[:space:]]*[([]"
  defs=$(awk -v re="$re" -v dre="($defs_re)" '
    BEGIN { in_def = 0 }
    # A `#define` and its continuation lines are one entity, and the names in
    # the body are its formals, not definitions of the unit.
    in_def { if ($0 !~ /\\[ \t]*$/) in_def = 0; next }
    /^#define[ \t]/ { if ($0 ~ /\\[ \t]*$/) in_def = 1; next }
    /^[A-Za-z_#]/ {
      line = $0
      while (match(line, re)) {
        s = substr(line, RSTART, RLENGTH)
        sub(/[ \t]*[([]$/, "", s)
        print s
        line = substr(line, RSTART + RLENGTH)
      }
    }
    # A definition can also be a macro invocation at column 0, whose arguments
    # name what it defines: `S1F_DEFINE_KERNEL(s1f_k_pos8, s1f_ke_pos8)` defines
    # the first.  Every identifier of the unit'"'"'s naming shapes on such a line
    # is reported, because the comparison is bilateral and an over-report is a
    # diff the list has to explain.
    /^[A-Za-z_][A-Za-z0-9_]*[ \t]*\(/ {
      rest = $0
      while (match(rest, dre)) {
        print substr(rest, RSTART, RLENGTH)
        rest = substr(rest, RSTART + RLENGTH)
      }
    }
  ' "$kernel" | LC_ALL=C sort -u)
  extra=$(printf '%s\n' $entity_specs $extra_specs \
    | sed 's/^[^:]*://' | LC_ALL=C sort -u \
    | comm -13 - <(printf '%s\n' "$defs"))
  if [ -n "$extra" ]; then
    printf 'DIFF: the unit defines %s, which the identity list does not name\n' \
      "$(echo $extra)" >&2
    rc=1
  else
    printf 'ok: every definition in the unit is listed or is its declared new text\n'
  fi
  return "$rc"
}

arm_mutate() {
  local rc=0 status st
  printf '\n== Control: text rewritten in a copy of the unit (%s)\n' "$kernel"
  printf '   the comparison must report a difference; its diff follows\n'

  # One numeral: `0xFFu` masks the group byte in `s1f_ke_pos8` / `s1f_masks`.
  case "$unit" in
    s1) local needle='0x1F' replacement='0x1E' subject=s1_masks ;;
    entry) local needle='0xFFu' replacement='0xFEu' subject=s1f_ke_pos8 ;;
  esac
  local mut=$work/unit.numeral.c
  awk -v needle="$needle" -v replacement="$replacement" '
    { if (!done && index($0, needle) > 0) {
        n = gsub(needle, replacement); done = 1 }
      print }
    END { if (!done) exit 1 }
  ' "$kernel" > "$mut" || { printf 'SETUP: the numeral control did not apply\n' >&2; return 3; }
  if cmp -s "$kernel" "$mut"; then
    printf 'SETUP: the control could not rewrite a numeral in %s\n' "$kernel" >&2
    return 3
  fi
  if [ "$(grep -c "$replacement" "$mut")" -ne 1 ]; then
    printf 'SETUP: the control rewrote more than one numeral\n' >&2
    return 3
  fi
  printf '   (%s: one numeral, in %s)\n' "$needle -> $replacement" "$subject"
  compare_entities "$mut" control
  status=$?
  case "$status" in
    0) printf 'FAIL: the token comparison did not see a changed numeral\n' >&2; rc=1 ;;
    1) printf 'ok: the control is reported as a difference\n' ;;
    *) return "$status" ;;
  esac

  # The entry unit's second kernel is a different shape — `ctz` slots rather
  # than a table lookup — so a second control changes one slot index there.
  if [ "$unit" = entry ]; then
    printf '\n== Control: one slot index in the second kernel changed\n'
    mut=$work/unit.slot.c
    awk '
      { if (!done && index($0, "o[5] = base +") > 0) {
          sub(/o\[5\] = base \+/, "o[6] = base +"); done = 1 }
        print }
      END { if (!done) exit 1 }
    ' "$kernel" > "$mut" || { printf 'SETUP: the slot control did not apply\n' >&2; return 3; }
    if cmp -s "$kernel" "$mut"; then
      printf 'SETUP: the slot control could not rewrite a slot index\n' >&2
      return 3
    fi
    compare_entities "$mut" control
    status=$?
    case "$status" in
      0) printf 'FAIL: the token comparison did not see a changed slot index\n' >&2; rc=1 ;;
      1) printf 'ok: the slot control is reported as a difference\n' ;;
      *) return "$status" ;;
    esac
  fi
  return "$rc"
}

# --- C1: the translation unit and the arm detector -------------------------

arm_arms_only() {
  local i k hits count
  printf '\n== C1 (%s): the unit compiles standalone and carries no measurement arm\n' "$unit"
  if ! "$cc" "${cflags[@]}" -I "$repo/kernel/json" -c "$kernel" -o "$work/kernel.o"; then
    printf 'FAIL: %s did not compile with the pinned flags\n' "$kernel" >&2
    return 1
  fi
  printf 'ok: compiled %s with %s\n' "$kernel" "${cflags[*]}"

  "$cc" "${cflags[@]}" -I "$repo/kernel/json" -E -P "$kernel" > "$work/kernel.i" || {
    printf 'SETUP: cannot preprocess %s\n' "$kernel" >&2
    return 3
  }

  # The measured side of the detector: a TU including the vendored header, at
  # the measured `-D` set, with a generated `u8kl.h` for the include the
  # UTF-8 switch takes.  It is the control in both units.
  mkdir -p "$work/stub"
  cat > "$work/stub/u8kl.h" <<'EOF'
/* Generated for this arm only: `s1fuse.h:124` includes "u8kl.h" at
   S1F_UTF8=7.  Neither unit's text names a u8kl symbol, so this arm's text
   cannot depend on this file; the detector's verdict on the vendored header is
   what the control below reads.  It is never committed. */
EOF
  printf '#include <stdio.h>\n#include <stdlib.h>\n#include <stdint.h>\n#include "s1fuse.h"\n' \
    > "$work/pre.control.c"
  "$cc" "${cflags[@]}" "${measured_defs[@]}" -I "$work/stub" -I "$measured" \
    -E -P "$work/pre.control.c" > "$work/control.i" || {
    printf 'SETUP: the measured header did not preprocess\n' >&2
    return 3
  }

  if [ "$unit" = s1 ]; then
    hits=$(grep -oE "$detector" "$work/kernel.i" | sort -u || true)
    if [ -n "$hits" ]; then
      printf 'FAIL: the preprocessed kernel names a measurement arm:\n%s\n' "$hits" >&2
      return 1
    fi
    printf 'ok: the preprocessed kernel names none of dens_/xl_/kl_/S1F_/SP_/sp_\n'
  else
    hits=$(grep -oE "$detector_no_xl" "$work/kernel.i" | sort -u || true)
    if [ -n "$hits" ]; then
      printf 'FAIL: the preprocessed unit names a measurement arm:\n%s\n' "$hits" >&2
      return 1
    fi
    printf 'ok: the preprocessed unit names none of dens_/kl_/S1F_/SP_/sp_\n'
    hits=$(grep -oE "$detector_xl" "$work/kernel.i" | sort -u | tr '\n' ' ')
    hits=${hits% }
    if [ "$hits" != "$xl_exempt" ]; then
      printf 'SETUP: the unit'"'"'s xl_ names are {%s}, and the identity list exempts {%s}\n' \
        "$hits" "$xl_exempt" >&2
      printf 'SETUP: a name outside the exemption is a setup fault, not a passing unit\n' >&2
      return 3
    fi
    count=$(printf '%s\n' $hits | grep -c . || true)
    printf 'ok: the unit'"'"'s xl_ names are exactly its %s exempt table names (%s)\n' \
      "$count" "$hits"
    if ! command -v nm >/dev/null 2>&1; then
      printf 'SETUP: no nm on PATH; the public-symbol assertion needs it\n' >&2
      return 3
    fi
    hits=$(nm -g --defined-only "$work/kernel.o" | awk '{ print $3 }' | LC_ALL=C sort | tr '\n' ' ')
    hits=${hits% }
    if [ "$hits" != "leanllvm_json_entry_b8 leanllvm_json_entry_pos8 leanllvm_json_entry_table" ]; then
      printf 'FAIL: the unit defines the public symbols {%s}\n' "$hits" >&2
      printf 'FAIL: expected exactly leanllvm_json_entry_b8/pos8/table\n' >&2
      return 1
    fi
    printf 'ok: the unit defines exactly its three public symbols\n'
  fi

  hits=$(grep -oE "$detector" "$work/control.i" | sort -u || true)
  count=$(printf '%s\n' "$hits" | grep -c . || true)
  if [ "$count" -eq 0 ]; then
    printf 'FAIL: the same detector names nothing in the measured header; it is vacuous\n' >&2
    return 1
  fi
  printf 'ok: the same detector names %s distinct measurement identifiers in the measured TU, e.g.\n' "$count"
  i=0
  for k in $hits; do
    printf '    %s\n' "$k"
    i=$((i + 1))
    [ "$i" -ge 5 ] && break
  done
  if [ "$unit" = entry ]; then
    hits=$(grep -oE "$detector_xl" "$work/control.i" | sort -u | tr '\n' ' ')
    hits=${hits% }
    count=$(printf '%s\n' $hits | grep -c . || true)
    if [ "$count" -le 3 ]; then
      printf 'FAIL: the measured TU names %s xl_ identifiers; the exemption cannot be seen\n' \
        "$count" >&2
      return 1
    fi
    printf 'ok: the measured TU names %s xl_ identifiers, so the exemption is not vacuous\n' "$count"
  fi
}

# --- C4: the vendored set is the measured set ------------------------------

anchor() { # <line> <text>
  local got
  got=$(sed -n "${1}p" "$header_src")
  case "$got" in
    *"$2"*) printf 'ok: s1fuse.h:%-5s %s\n' "$1" "$2" ;;
    *)
      printf 'FAIL: s1fuse.h:%s is not "%s"\n     got: %s\n' "$1" "$2" "$got" >&2
      return 1
      ;;
  esac
}

arm_vendor() {
  local f rc=0
  printf '\n== C4: the vendored set and its digests\n'
  ( cd "$measured" && sha256sum -c SHA256SUMS ) || return 1
  anchor 272 'typedef struct { uint64_t esc_open, esc_ppar, im_carry, prevS,' || rc=1
  anchor 345 'static inline uint64_t s1f_prefix_xor(uint64_t x) {' || rc=1
  anchor 351 'static inline uint64_t s1f_escaped(uint64_t bs, uint64_t *open, uint64_t *ppar) {' || rc=1
  anchor 384 '#ifndef S1F_CTAB' || rc=1
  anchor 388 'static const uint8_t s1f_lo_tab[32]' || rc=1
  anchor 394 'static const uint8_t s1f_hi_tab[32]' || rc=1
  anchor 401 'static inline void s1f_sw32(__m256i v, uint32_t *sm, uint32_t *ws) {' || rc=1
  anchor 414 'static inline uint64_t s1f_sm_ws(__m256i v0, __m256i v1, uint64_t *ws_o) {' || rc=1
  anchor 425 'static inline void s1f_masks(__m256i v0, __m256i v1, S1F *st,' || rc=1
  anchor 1670 'uint64_t nb = (n + 63) / 64;' || rc=1
  anchor 1702 '__m256i v0 = _mm256_loadu_si256((const __m256i *)p);' || rc=1
  anchor 1703 '__m256i v1 = _mm256_loadu_si256((const __m256i *)(p + 32));' || rc=1
  anchor 1705 's1f_masks(v0, v1, &st, &qm, &sm, &im, &wsm, &bm, &ctl);' || rc=1
  [ "$rc" -eq 0 ] || return 1

  if [ -d "$scratch" ]; then
    if [ "$tree_only" -eq 1 ]; then
      require_in_tree "$scratch"
    fi
    for f in s1fuse.h xlist.h dens.h; do
      if diff -u "$scratch/$f" "$measured/$f" > "$work/vendor.$f.diff"; then
        printf 'ok: %s is byte-identical to %s/%s\n' "$measured/$f" "$scratch" "$f"
      else
        printf 'FAIL: %s differs from %s/%s\n' "$measured/$f" "$scratch" "$f" >&2
        awk 'NR <= 40' "$work/vendor.$f.diff" >&2
        rc=1
      fi
    done
    [ "$rc" -eq 0 ] || return 1
  else
    printf 'note: %s is absent; the digests are the corroboration and the live diff is skipped\n' "$scratch"
  fi
}

# --- the mask region is invariant to the macro set --------------------------

# build_preprocessed <label> <include-stub:0|1> <defs...>
# Writes $work/preprocessed.<label> and echoes the macro set that produced it.
build_preprocessed() {
  local label=$1 stub=$2
  shift 2
  {
    printf '#include <stdio.h>\n#include <stdlib.h>\n#include <stdint.h>\n#include "s1fuse.h"\n'
  } > "$work/pre.$label.c"
  local -a inc=(-I "$measured")
  [ "$stub" -eq 1 ] && inc=(-I "$work/stub" "${inc[@]}")
  if ! "$cc" "${cflags[@]}" "$@" "${inc[@]}" -E -P "$work/pre.$label.c" \
      > "$work/preprocessed.$label"; then
    printf 'SETUP: the %s arm did not preprocess\n' "$label" >&2
    return 3
  fi
  printf '   arm %-10s %s\n' "$label" "$*"
}

preprocess_entities() { # <label>
  local label=$1 spec src entity text
  for spec in $entity_specs; do
    src=${spec%%:*}
    entity=${spec#*:}
    if ! text=$(extract_entity "$work/preprocessed.$label" "$entity" "" | normalise_entity "$entity"); then
      printf 'SETUP: cannot extract %s from the %s arm\n' "$entity" "$label" >&2
      return 3
    fi
    printf '%s\n' "$text" > "$work/entity.$label.$entity"
  done
}

arm_preprocess() {
  local spec entity rc=0
  printf '\n== --preprocess: the mask region is invariant to the macro set\n'
  printf '   claim: the seven entities are the same text under each macro set;\n'
  printf '   this is not a claim that a full measured build was compiled here.\n'

  mkdir -p "$work/stub"
  cat > "$work/stub/u8kl.h" <<'EOF'
/* Generated for this arm only: `s1fuse.h:124` includes "u8kl.h" at
   S1F_UTF8=7.  The mask region names no u8kl symbol, so this arm's text for
   the seven entities cannot depend on this file; the checks below compare
   against an arm without it.  It is never committed. */
EOF

  build_preprocessed full 1 "${measured_defs[@]}" || return $?
  build_preprocessed noutf8 0 -DSTAGE_PROBE -DS1F_ENT_PROBE=1 -DS1F_DENS=1 \
    -DS1F_TWOPHASE=1 -DS1F_EXP2=11 -DS1F_DISPATCH=1 -DS1F_UTF8=0 -DS1F_KL_DOC=0 \
    -DPSTAGE=32 -DPMODE=2 -DS1F_XS=5 -DS2_XP=1 -DS2_DEC_GATE=2 -DS1F_XS_DYN=1 || return $?
  build_preprocessed oracle 0 "${oracle_defs[@]}" || return $?

  preprocess_entities full || return $?
  preprocess_entities noutf8 || return $?
  preprocess_entities oracle || return $?
  # The control: the same instrument, on a macro change that *does* move the
  # mask region.  `-DS1F_CTAB=0` selects the `cmpeq` chain inside `s1f_masks`
  # instead of the table path, so `s1f_masks` must differ from the full arm.
  build_preprocessed ctab0 0 -DS1F_XS=5 -DS1F_CTAB=0 || return $?
  preprocess_entities ctab0 || return $?

  for spec in $entity_specs; do
    entity=${spec#*:}
    if cmp -s "$work/entity.full.$entity" "$work/entity.noutf8.$entity" &&
       cmp -s "$work/entity.full.$entity" "$work/entity.oracle.$entity"; then
      printf 'ok: %-18s identical under full/noutf8/oracle\n' "$entity"
    else
      rc=1
      printf 'DIFF: %-18s differs between arms\n' "$entity" >&2
      for arm in full noutf8 oracle; do
        printf '      %s: %s\n' "$arm" "$(cat "$work/entity.$arm.$entity")" >&2
      done
    fi
  done
  [ "$rc" -eq 0 ] || return 1
  moved=0
  for spec in $entity_specs; do
    entity=${spec#*:}
    cmp -s "$work/entity.full.$entity" "$work/entity.ctab0.$entity" || {
      printf 'ok: control arm ctab0 moves %s\n' "$entity"; moved=$((moved + 1)); }
  done
  [ "$moved" -gt 0 ] || {
    printf 'FAIL: control arm ctab0 moved no entity; the instrument cannot see a macro change\n' >&2
    return 1; }
  printf 'ok: the instrument sees a macro change (%s entit(ies) moved by ctab0)\n' "$moved"
}

# --- run -------------------------------------------------------------------

if [ "$run_identity" -eq 1 ]; then arm_identity || exit $?; fi
if [ "$run_mutate" -eq 1 ]; then arm_mutate || exit $?; fi
if [ "$run_arms" -eq 1 ]; then arm_arms_only || exit $?; fi
if [ "$run_vendor" -eq 1 ]; then arm_vendor || exit $?; fi
if [ "$run_preprocess" -eq 1 ]; then arm_preprocess || exit $?; fi
printf '\nok: source identity holds (%s)\n' "$unit"
