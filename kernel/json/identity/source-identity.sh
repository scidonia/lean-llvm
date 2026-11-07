#!/usr/bin/env bash
# Arm A: the extracted kernel's text is the measured text, modulo the deletion
# list — plus the one preprocessor check that makes Arm B's oracle faithful.
#
#   nix develop -c bash kernel/json/identity/source-identity.sh             # A + its control
#   nix develop -c bash kernel/json/identity/source-identity.sh --arms-only # C1
#   nix develop -c bash kernel/json/identity/source-identity.sh --vendor    # C4
#   nix develop -c bash kernel/json/identity/source-identity.sh --preprocess # §5
#   nix develop -c bash kernel/json/identity/source-identity.sh --all
#
# Modes (default: --identity --mutate):
#   --identity    extract the entities `kernel/json/README.md` lists from
#                 `measured/s1fuse.h`, drop the lines the same block lists,
#                 normalise comments and whitespace, and require the tokens to
#                 equal the same entities' tokens in `kernel/json/s1_block.c`.
#   --mutate      the control: rewrite one numeral in a copy of the kernel and
#                 require the same comparison to report a difference.  A
#                 comparison that cannot see a numeral changed is not evidence.
#   --arms-only   C1: compile the kernel as a standalone translation unit with
#                 the pinned flags, then preprocess it and require the arm
#                 detector to name nothing; run the same detector on the
#                 measured header's translation unit and require it to name at
#                 least one thing, so the detector is not vacuous.
#   --vendor      C4: `sha256sum -c` over `measured/SHA256SUMS`, the anchored
#                 line ranges of `measured/s1fuse.h`, and — while it survives —
#                 a live `diff -u` against the scratch tree the set was copied
#                 from.  The scratch tree is corroboration, not a dependency.
#   --preprocess  §5: the mask region is invariant to the macro set.  It is
#                 preprocessed three ways — the measured `-D` set of
#                 `build49.sh:19-21` (with a generated `u8kl.h` for the include
#                 at `s1fuse.h:124`, which the mask region never references),
#                 the same set with `-DS1F_UTF8=0` and no stub, and the
#                 oracle's reduced set — and the seven entities must agree
#                 across all three.  The claim is invariance, not that a full
#                 measured build was compiled; each arm's text is labelled.
#   --tree-only   refuse any input path outside the repository (exit 3).  Under
#                 it, --vendor refuses while the scratch tree exists, because
#                 the live diff asks to read a path outside the repository.
#
# Exit status: 0 when every requested arm holds, 1 when one fails, 3 on a setup
# fault (an absent input or tool, a malformed identity list, a divergence in
# --preprocess that is a setup fault rather than an assertion), so a missing
# dependency is never read as a passing or a failing claim.
set -uo pipefail

here=$(cd "$(dirname "$0")" && pwd)
repo=$(cd "$here/../../.." && pwd)
kernel=$repo/kernel/json/s1_block.c
header=$repo/kernel/json/s1_block.h
measured=$repo/kernel/json/measured
header_src=$measured/s1fuse.h
readme=$repo/kernel/json/README.md
oracle=$here/oracle.c
scratch=/tmp/scidonia-spike45/src
cc=clang

# The measured compiler line (`build49.sh:17`).
cflags=(-O3 -march=x86-64-v3 -mpclmul -std=gnu11 -falign-loops=64 -falign-functions=64)

# The measured translation unit's `-D` set (`build49.sh:19-21`): $S1 $U8 $P2.
measured_defs=(
  -DSTAGE_PROBE -DS1F_ENT_PROBE=1 -DS1F_DENS=1 -DS1F_TWOPHASE=1 -DS1F_EXP2=11
  -DS1F_DISPATCH=1 -DS1F_UTF8=7 -DS1F_KL_DOC=1 -DPSTAGE=32 -DPMODE=2 -DS1F_XS=5
  -DS2_XP=1 -DS2_DEC_GATE=2 -DS1F_XS_DYN=1
)
# The oracle's reduced set: the two macros `s1f_masks` reads, and nothing else
# (§5).  The remaining switches are left at the header's defaults, which is what
# `--preprocess` compares against the measured set.
oracle_defs=(-DS1F_XS=5 -DS1F_CTAB=1)

# The arm detector of C1: an identifier in the measured build's vocabulary.
detector='\b(dens_|xl_|kl_|S1F_|SP_|sp_)[A-Za-z0-9_]*'

run_identity=0
run_mutate=0
run_arms=0
run_vendor=0
run_preprocess=0
tree_only=0
any_mode=0

usage() {
  sed -n '2,40p' "$0" | sed 's/^# \{0,1\}//'
}

while [ "$#" -gt 0 ]; do
  case "$1" in
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

for path in "$kernel" "$header" "$header_src" "$readme" "$oracle"; do
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

# A private work directory inside the checkout, so a --tree-only run touches
# nothing outside it.  `.lake` is a build directory and is not tracked.
mkdir -p "$repo/.lake" || { printf 'SETUP: cannot create %s/.lake\n' "$repo" >&2; exit 3; }
work=$(mktemp -d "$repo/.lake/tmp-s1-identity.XXXXXX" 2>/dev/null) || {
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
entities=$(printf '%s\n' "$list_block" | sed -n 's/^entities:[[:space:]]*//p')
deletions=$(printf '%s\n' "$list_block" | sed -n 's/^delete:[[:space:]]*//p' | tr '\n' ' ')
if [ -z "$entities" ]; then
  printf 'SETUP: the identity list names no entities\n' >&2
  exit 3
fi
printf 'identity list: %s\n' "$entities"
printf 'delete list:   %s\n' "${deletions% }"

# Extract one top-level definition: it starts on a column-0 line naming the
# entity and is emitted up to the brace that closes it.  Lines in `skip` are
# dropped.  This is the only place a name is turned into text, so an entity or
# a deletion the README does not list cannot be excused.
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
        if (line[l] ~ /^[^ \t#\/]/ && index(line[l], name) > 0 &&
            (index(line[l], "(") > 0 || index(line[l], "[") > 0)) { start = l; break }
      }
      if (!start) { printf "no definition of %s in %s\n", name, FILENAME > "/dev/stderr"; exit 1 }
      depth = 0; opened = 0
      for (l = start; l <= NR; l++) {
        if (!(l in drop)) print line[l]
        probe = line[l]
        o = gsub(/\{/, "{", probe); c = gsub(/\}/, "}", probe)
        depth += o - c
        if (o > 0) opened = 1
        if (opened && depth == 0) break
      }
    }
  ' "$1"
}

# Comments and whitespace are representation; the tokens are the content.
normalise() {
  "$cc" -E -P -x c - 2>/dev/null | tr '\n\t' '  ' | tr -s ' ' | sed -e 's/^ //' -e 's/ $//'
}

# compare_entities <kernel-file> <label>
# Prints one line per entity and returns 0 iff every entity's tokens match.
compare_entities() {
  local kfile=$1 label=$2 entity meas kern rc=0
  for entity in $entities; do
    if ! meas=$(extract_entity "$header_src" "$entity" "${deletions% }" | normalise); then
      printf 'SETUP: cannot extract %s from %s\n' "$entity" "$header_src" >&2
      return 3
    fi
    if ! kern=$(extract_entity "$kfile" "$entity" "" | normalise); then
      printf 'SETUP: cannot extract %s from %s\n' "$entity" "$kfile" >&2
      return 3
    fi
    if [ "$meas" = "$kern" ]; then
      printf 'ok: %-8s %-16s identical (%s token bytes)\n' "$label" "$entity" "${#meas}"
    else
      rc=1
      printf 'DIFF: %-8s %-16s differs\n' "$label" "$entity" >&2
      diff -u <(printf '%s\n' "$meas" | tr ' ' '\n') \
              <(printf '%s\n' "$kern" | tr ' ' '\n') \
        | sed -e '1,2d' -e 's/^/      /' | awk 'NR <= 20' >&2
    fi
  done
  return "$rc"
}

# --- Arm A and its control -------------------------------------------------

arm_identity() {
  local defs extra rc
  printf '\n== Arm A: token identity, %s against %s\n' "$header_src" "$kernel"
  compare_entities "$kernel" identity
  rc=$?

  # The list is bilateral: a definition in the kernel that it does not name is
  # a copy the diff above never looked at.  The one exception is the public
  # wrapper, which README.md and §4.2 declare is new code and not measured text.
  defs=$(awk '
    /^[A-Za-z_]/ {
      line = $0
      while (match(line, /(s1f_[a-z0-9_]+|leanllvm_json_s1_masks)[ \t]*[\(\[]/)) {
        s = substr(line, RSTART, RLENGTH)
        sub(/[ \t]*[\(\[]$/, "", s)
        print s
        line = substr(line, RSTART + RLENGTH)
      }
    }
  ' "$kernel" | LC_ALL=C sort -u)
  extra=$(printf '%s\n' $entities leanllvm_json_s1_masks | LC_ALL=C sort -u \
    | comm -13 - <(printf '%s\n' "$defs"))
  if [ -n "$extra" ]; then
    printf 'DIFF: the kernel defines %s, which the identity list does not name\n' \
      "$(echo $extra)" >&2
    rc=1
  else
    printf 'ok: every definition in the kernel is listed or is the new wrapper\n'
  fi
  return "$rc"
}

arm_mutate() {
  local mut=$work/s1_block.mutated.c status
  # One numeral, and the first one that occurs in an extracted entity: the
  # control threshold `0x1F` in `s1f_masks`.
  awk '{ if (!done && index($0, "0x1F") > 0) { sub(/0x1F/, "0x1E"); done = 1 } print }' \
    "$kernel" > "$mut"
  if cmp -s "$kernel" "$mut"; then
    printf 'SETUP: the control could not rewrite a numeral in %s\n' "$kernel" >&2
    exit 3
  fi
  if [ "$(grep -c '0x1E' "$mut")" -ne 1 ]; then
    printf 'SETUP: the control rewrote more than one numeral\n' >&2
    exit 3
  fi
  printf '\n== Control: one numeral rewritten in a copy of the kernel (%s)\n' "$mut"
  printf '   the comparison must report a difference; its diff follows\n'
  compare_entities "$mut" control
  status=$?
  case "$status" in
    0) printf 'FAIL: the token comparison did not see a changed numeral\n' >&2; return 1 ;;
    1) printf 'ok: the control is reported as a difference\n'; return 0 ;;
    *) return "$status" ;;
  esac
}

# --- C1: the translation unit and the arm detector -------------------------

arm_arms_only() {
  local i k hits count
  printf '\n== C1: the kernel compiles standalone and carries no measurement arm\n'
  if ! "$cc" "${cflags[@]}" -I "$repo/kernel/json" -c "$kernel" -o "$work/kernel.o"; then
    printf 'FAIL: %s did not compile with the pinned flags\n' "$kernel" >&2
    return 1
  fi
  printf 'ok: compiled %s with %s\n' "$kernel" "${cflags[*]}"

  "$cc" "${cflags[@]}" -I "$repo/kernel/json" -E -P "$kernel" > "$work/kernel.i" || {
    printf 'SETUP: cannot preprocess %s\n' "$kernel" >&2
    return 3
  }
  hits=$(grep -oE "$detector" "$work/kernel.i" | sort -u || true)
  if [ -n "$hits" ]; then
    printf 'FAIL: the preprocessed kernel names a measurement arm:\n%s\n' "$hits" >&2
    return 1
  fi
  printf 'ok: the preprocessed kernel names none of dens_/xl_/kl_/S1F_/SP_/sp_\n'

  "$cc" "${cflags[@]}" "${oracle_defs[@]}" -I "$here" -E -P "$oracle" > "$work/oracle.i" || {
    printf 'SETUP: cannot preprocess %s\n' "$oracle" >&2
    return 3
  }
  hits=$(grep -oE "$detector" "$work/oracle.i" | sort -u || true)
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

# --- §5: the mask region is invariant to the macro set ----------------------

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
  local label=$1 entity text
  for entity in $entities; do
    if ! text=$(extract_entity "$work/preprocessed.$label" "$entity" "" | normalise); then
      printf 'SETUP: cannot extract %s from the %s arm\n' "$entity" "$label" >&2
      return 3
    fi
    printf '%s\n' "$text" > "$work/entity.$label.$entity"
  done
}

arm_preprocess() {
  local entity rc=0
  printf '\n== §5: the mask region is invariant to the macro set\n'
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

  for entity in $entities; do
    if cmp -s "$work/entity.full.$entity" "$work/entity.noutf8.$entity" &&
       cmp -s "$work/entity.full.$entity" "$work/entity.oracle.$entity"; then
      printf 'ok: %-16s identical under full/noutf8/oracle\n' "$entity"
    else
      rc=1
      printf 'DIFF: %-16s differs between arms\n' "$entity" >&2
      for arm in full noutf8 oracle; do
        printf '      %s: %s\n' "$arm" "$(cat "$work/entity.$arm.$entity")" >&2
      done
    fi
  done
  [ "$rc" -eq 0 ] || return 1
  moved=0
  for entity in $entities; do
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
printf '\nok: source identity holds\n'
