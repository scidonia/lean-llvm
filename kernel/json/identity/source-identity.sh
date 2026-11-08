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
#   utf8   the UTF-8 unit, `kernel/json/utf8.c`, against the six definitions
#          `README.md`'s `utf8-entities:` line names in `measured/u8kl.h` and
#          against the stage the `utf8-stage:` line names by line range in
#          `measured/s1fuse.h`.  The stage has no name to locate it by, so each
#          side gets the locator it can hold: a line range on the measured side
#          (safe because that file is pinned by digest) and a marker-delimited
#          region inside the unit (`utf8-stage-begin`/`utf8-stage-end`, safe
#          because the unit is this repository's own file).  The ranges are
#          concatenated in the key order `stage_text` fixes (`utf8-stage:` then
#          `utf8-stage-tail:`, and within one row in the order written), the
#          `utf8-rename:`
#          row is applied to the measured side, and **both** sides must have a
#          nonzero token count and a non-empty normalisation: an empty
#          extraction is a setup fault, not an equality.  This unit's arm
#          detector is its own (`--arms-only`): it keeps `dens_`, `S1F_`, `SP_`
#          and `sp_` refused and accepts `kl_`, which is this unit's subject.
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
#   --stage-tu    print the measured side of the stage's emitted-code
#                 comparison: a translation unit whose function is the measured
#                 declarations and the extracted stage text.  It is the one
#                 definition of that text, so the IR arm and the timing arm both
#                 build their measured side from this and not from copies.  The
#                 function is named by `UTF8_STAGE_NAME` (default:
#                 `leanllvm_json_utf8`), so a caller that links it beside the
#                 unit can rename it.  This mode reads the vendored files and
#                 the identity list, not the unit.
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
# The UTF-8 unit's own detector.  For the two units above, `kl_` is a
# measurement arm to be refused; for this unit the KL machinery is the subject,
# so its detector keeps the rest of the measured vocabulary and accepts `kl_`.
# A detector loosened for all three units would stop refusing the arm these two
# exist to exclude, which is why the calibration is per unit and not shared.
detector_utf8='\b(dens_|S1F_|SP_|sp_)[A-Za-z0-9_]*'
# The vendored header's own name shape, for the completeness check: every
# definition `u8kl.h` carries, whichever list accounts for it.
detector_kl='\b(kl_[A-Za-z0-9_]*|KLCARRY)'

run_identity=0
run_mutate=0
run_arms=0
run_vendor=0
run_preprocess=0
run_stage_tu=0
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
    --stage-tu) run_stage_tu=1; any_mode=1 ;;
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
  utf8)
    kernel=$repo/kernel/json/utf8.c
    oracle=""
    input_paths=("$kernel" "$repo/kernel/json/utf8.h" "$header_src" "$measured/u8kl.h" "$readme")
    ;;
  *)
    printf 'SETUP: unit %s has no source identity arm; implemented units: s1 entry utf8\n' "$unit" >&2
    exit 3
    ;;
esac

# The unit's own files are what the token and detector arms read; --vendor is
# about the vendored set and --stage-tu prints the measured side, so neither
# needs the unit to exist, and each names its own inputs.
needs_unit=0
[ "$run_identity" -eq 1 ] && needs_unit=1
[ "$run_mutate" -eq 1 ] && needs_unit=1
[ "$run_arms" -eq 1 ] && needs_unit=1
[ "$run_preprocess" -eq 1 ] && needs_unit=1

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
require_paths() {
  local path
  for path in "$@"; do [ -e "$path" ] || { printf 'SETUP: absent: %s\n' "$path" >&2; exit 3; }; done
}

[ "$needs_unit" -eq 1 ] && require_paths "${input_paths[@]}"
[ "$tree_only" -eq 1 ] && [ "$needs_unit" -eq 1 ] && \
  for path in "${input_paths[@]}"; do require_in_tree "$path"; done

if [ "$run_preprocess" -eq 1 ] && [ "$unit" != s1 ]; then
  printf 'SETUP: --preprocess is the s1 unit'"'"'s claim; the %s entities exist under one\n' "$unit" >&2
  printf 'SETUP: macro set only, so no macro-set invariance is claimed for them (exit 3)\n' >&2
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

# list_rows <key> -- every `<key>:` line's text, one line per row.  Used where a
# row holds two fields (`<measured> <unit>`) and splitting it would lose which
# is which.
list_rows() {
  printf '%s\n' "$list_block" | sed -n "s/^$1:[[:space:]]*//p"
}

# list_line <key> -- the first `<key>:` line's text.  A marker is a line of its
# own, spaces included, so it is read whole and not as a field.
list_line() {
  printf '%s\n' "$list_block" | sed -n "s/^$1:[[:space:]]*//p" | sed -n '1p'
}

# entity_specs: `<source>:<entity>` pairs; deletion_specs: `<source>:<ranges>`.
# The s1 unit has one source header, so its bare lists are prefixed here and
# all three units are read by one code path below.  The stage variables are empty
# for the units that have no stage range; only `utf8` sets them.
stage_specs=""
stage_tail_specs=""
stage_copy_specs=""
stage_unit=""
stage_begin=""
stage_end=""
rename_specs=""
perm_specs=""
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
    detector_unit=$detector
    ;;
  entry)
    entity_specs=$(list_field entry-entities)
    deletion_specs=$(list_field entry-delete)
    extra_specs=$(list_field entry-extra)
    defs_re="s1f_[a-z0-9_]+|xl_[a-z0-9_]+|S1F_[A-Za-z0-9_]+|leanllvm_json_entry_[a-z0-9_]+"
    xl_exempt=$(list_field entry-xl-exempt)
    detector_unit=$detector_no_xl
    ;;
  utf8)
    entity_specs=$(list_field utf8-entities)
    deletion_specs=$(list_field utf8-delete)
    extra_specs=$(list_field utf8-extra)
    defs_re="kl_[a-z0-9_]+|leanllvm_json_utf8"
    xl_exempt=""
    detector_unit=$detector_utf8
    stage_specs=$(list_field utf8-stage)
    stage_tail_specs=$(list_field utf8-stage-tail)
    stage_copy_specs=$(list_field utf8-stage-copy)
    stage_unit=$(list_field utf8-stage-unit)
    stage_begin=$(list_line utf8-stage-begin)
    stage_end=$(list_line utf8-stage-end)
    rename_specs=$(list_rows utf8-rename)
    perm_specs=$(list_field utf8-permutation)
    ;;
esac

if [ -z "$entity_specs" ]; then
  printf 'SETUP: the %s identity list names no entities\n' "$unit" >&2
  exit 3
fi
# The summary is for a reader of an arm's log; --stage-tu's stdout is a
# translation unit and must hold nothing else.
if [ "$run_stage_tu" -eq 0 ]; then
  printf 'unit:          %s\n' "$unit"
  printf 'identity list: %s\n' "$entity_specs"
  printf 'delete list:   %s\n' "$deletion_specs"
fi

# source_file <source> -- the vendored file an entity or a deletion row came from.
source_file() { # <source>
  case "$1" in
    s1fuse) printf '%s' "$header_src" ;;
    xlist) printf '%s' "$measured/xlist.h" ;;
    u8kl) printf '%s' "$measured/u8kl.h" ;;
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

# --- the stage form: line ranges on the measured side, a marked region in the
# --- unit, and a comparison that cannot call two empties equal -------------

# range_lines <file> <first>-<last> -- that file's lines, inclusive.  A range is
# pinned safely only because its file is pinned by digest, so the bounds are
# checked against the file's own length: a span that runs past the end is a
# setup fault and never a short extraction that a comparison then reads.
range_lines() { # <file> <first>-<last>
  local file=$1 span=$2 first last total
  case "$span" in
    *-*) : ;;
    *) printf 'SETUP: %s is not a <first>-<last> range\n' "$span" >&2; return 3 ;;
  esac
  first=${span%%-*}
  last=${span#*-}
  case "$first:$last" in
    *[!0-9:]*) printf 'SETUP: %s is not a <first>-<last> range\n' "$span" >&2; return 3 ;;
  esac
  total=$(wc -l < "$file" 2>/dev/null) || {
    printf 'SETUP: cannot read %s\n' "$file" >&2
    return 3
  }
  total=${total// /}
  if [ "$first" -lt 1 ] || [ "$last" -lt "$first" ] || [ "$last" -gt "$total" ]; then
    printf 'SETUP: range %s is outside %s (%s lines)\n' "$span" "$file" "$total" >&2
    return 3
  fi
  sed -n "${first},${last}p" "$file"
}

# extract_stage <source>:<first>-<last> ... -- the measured stage text, its
# ranges concatenated in the order given.  `stage_text` fixes that order by key
# (`utf8-stage:` before `utf8-stage-tail:`), so the order of the list is not
# load-bearing; the order of the spans within one row is, because swapping them
# changes the concatenation.
extract_stage() { # <source>:<span> ...
  local spec src span file
  for spec in "$@"; do
    src=${spec%%:*}
    span=${spec#*:}
    file=$(source_file "$src") || return 3
    range_lines "$file" "$span" || return 3
  done
}

# stage_text -- the stage as one token run: `utf8-stage:`'s statements, then
# `utf8-stage-tail:`'s reduce and tail after it.  The order is the keys', not the
# list's, so it cannot be changed by reordering the rows.
stage_text() {
  extract_stage $stage_specs || return 3
  extract_stage $stage_tail_specs || return 3
}

# apply_renames <text> -- the `utf8-rename:` rows, `<measured> <unit>`, on the
# measured side.  A row whose measured name no longer occurs is a setup fault:
# a rename that does not apply is a claim the text stopped making, and applying
# it silently to nothing would hide that.
apply_renames() { # <text>
  local text=$1 row from to
  while IFS= read -r row; do
    [ -n "$row" ] || continue
    from=${row%% *}
    to=${row#* }
    if [ "$from" = "$row" ] || [ -z "$to" ]; then
      printf 'SETUP: the rename row "%s" is not "<measured> <unit>"\n' "$row" >&2
      return 3
    fi
    case "$text" in
      *"$from"*) text=$(printf '%s\n' "$text" | sed "s/\\b$from\\b/$to/g") ;;
      *)
        printf 'SETUP: the rename row "%s -> %s" does not occur in the measured stage text\n' \
          "$from" "$to" >&2
        return 3
        ;;
    esac
  done <<<"$rename_specs"
  printf '%s\n' "$text"
}

# extract_region <file> <begin marker> <end marker> -- the lines strictly
# between the first line carrying <begin> and the next line carrying <end>.
# Either marker missing, or the end marker first, is a setup fault.
extract_region() { # <file> <begin> <end>
  awk -v begin="$2" -v end="$3" '
    !seen { if (index($0, begin) > 0) seen = 1; next }
    index($0, end) > 0 { done = 1; exit }
    { print }
    END { if (!seen || !done) exit 1 }
  ' "$1"
}

# compare_token_text <label> <measured> <unit>
# The comparison the stage form and its control share.  Both sides must have a
# nonzero token count and a non-empty normalisation: the comparison prints
# `identical (0 token bytes)` for two empty extractions, and an empty extraction
# is what a bound that clipped a statement produces -- `normalise` pipes through
# `cc -E`, which emits nothing for a preprocessor directive it never uses.  So
# an empty side is a setup fault and never an equality.
compare_token_text() { # <label> <measured-text> <unit-text>
  local label=$1 measured_text unit_text mtok utok
  measured_text=$(printf '%s\n' "$2" | normalise)
  unit_text=$(printf '%s\n' "$3" | normalise)
  mtok=$(printf '%s\n' "$measured_text" | wc -w | tr -d ' ')
  utok=$(printf '%s\n' "$unit_text" | wc -w | tr -d ' ')
  if [ "$mtok" -eq 0 ] || [ "$utok" -eq 0 ] || [ -z "$measured_text" ] || [ -z "$unit_text" ]; then
    printf 'SETUP: %s: an empty side (measured %s token(s), unit %s token(s));\n' \
      "$label" "$mtok" "$utok" >&2
    printf 'SETUP: an empty extraction is not an equality\n' >&2
    return 3
  fi
  if [ "$measured_text" = "$unit_text" ]; then
    printf 'ok: %-8s %-18s identical (%s token bytes, %s tokens)\n' \
      "$label" stage "${#measured_text}" "$mtok"
    return 0
  fi
  printf 'DIFF: %-8s %-18s differs (measured %s token(s), unit %s token(s))\n' \
    "$label" stage "$mtok" "$utok" >&2
  diff -u <(printf '%s\n' "$measured_text" | tr ' ' '\n') \
          <(printf '%s\n' "$unit_text" | tr ' ' '\n') \
    | sed -e '1,2d' -e 's/^/      /' | awk 'NR <= 20' >&2
  return 1
}

# compare_stage <unit-file> -- the measured stage text against the unit's marked
# region, with the rename row applied to the measured side only: a unit that
# kept the measured static's name would then be a difference, which is what the
# rename records.
compare_stage() { # <unit-file>
  local kfile=$1 measured_text unit_text
  [ -n "$stage_specs" ] || {
    printf 'SETUP: unit %s has no stage range list\n' "$unit" >&2
    return 3
  }
  if [ "$(basename "$kfile")" != "$stage_unit" ]; then
    printf 'SETUP: the stage unit row names %s and the arm reads %s\n' "$stage_unit" "$kfile" >&2
    return 3
  fi
  measured_text=$(stage_text) || return 3
  measured_text=$(apply_renames "$measured_text") || return 3
  unit_text=$(extract_region "$kfile" "$stage_begin" "$stage_end") || {
    printf 'SETUP: %s carries no region between "%s" and "%s"\n' \
      "$kfile" "$stage_begin" "$stage_end" >&2
    return 3
  }
  compare_token_text identity "$measured_text" "$unit_text"
}

# compare_stage_copies -- the stage exists twice in the measured header, and the
# two copies are one text.  No rename is applied: both sides carry the measured
# name, so identity is the comparison and a rename on one side only would be
# wrong rather than helpful.
compare_stage_copies() {
  local measured_text copy_text
  measured_text=$(stage_text) || return 3
  copy_text=$(extract_stage $stage_copy_specs) || return 3
  compare_token_text copy "$measured_text" "$copy_text"
}

# stage_control -- the stage comparison's own controls, in the same run.
stage_control() {
  local first span src clipped copy_text status rc=0
  first=${stage_specs%% *}
  src=${first%%:*}
  span=${first#*:}
  span=${span%%-*}
  printf '\n== Control: a bound clipped one line above the stage range (%s:%s-%s)\n' \
    "$src" "$((span - 1))" "$((span - 1))"
  clipped=$(range_lines "$(source_file "$src")" "$((span - 1))-$((span - 1))") || return 3
  printf '/* CLIPPED-CONTROL begin */\n%s\n/* CLIPPED-CONTROL end */\n' "$clipped" > "$work/clipped.c"
  printf '   the clipped line is: %s\n' "$clipped"
  compare_token_text clipped "$clipped" \
    "$(extract_region "$work/clipped.c" '/* CLIPPED-CONTROL begin */' '/* CLIPPED-CONTROL end */')" \
    > "$work/clipped.out" 2>&1
  status=$?
  case "$status" in
    3)
      printf 'ok: the empty comparison is refused as a setup fault, not reported as identity\n'
      printf '   %s\n' "$(sed -n '1p' "$work/clipped.out")"
      ;;
    0) printf 'FAIL: two empty extractions were reported as identical\n' >&2; rc=1 ;;
    *) printf 'FAIL: the clipped comparison did not fail as a setup fault\n' >&2; rc=1 ;;
  esac

  printf '\n== Control: one statement dropped from the second copy of the stage\n'
  copy_text=$(extract_stage $stage_copy_specs) || return 3
  copy_text=$(printf '%s\n' "$copy_text" | sed '$d')
  compare_token_text dropped "$(stage_text)" "$copy_text"
  status=$?
  case "$status" in
    1) printf 'ok: a dropped statement is reported as a difference\n' ;;
    *) printf 'FAIL: a dropped statement was not reported (status %s)\n' "$status" >&2; rc=1 ;;
  esac
  return "$rc"
}

# strip_comments -- a C source with its comments removed and nothing else
# changed.  Comments are representation, so a name a comment mentions is not a
# name the header defines; without this the vendored header's own prose about
# `kl_tail()` would read as a seventh definition.
strip_comments() {
  awk '
    {
      line = ""
      i = 1
      n = length($0)
      while (i <= n) {
        c = substr($0, i, 1)
        d = substr($0, i, 2)
        if (inblock) {
          if (d == "*/") { inblock = 0; i += 2 } else { i += 1 }
        } else if (d == "/*") {
          inblock = 1; i += 2
        } else if (d == "//") {
          i = n + 1
        } else {
          line = line c; i += 1
        }
      }
      print line
    }
  '
}

# kl_name_set -- the vendored header's `kl_` names are exactly the entities the
# unit copies plus the permutation form the measured build does not select.  A
# seventh name is a setup fault: it would be a definition the entity list and
# the deletion list both miss, so the arm would be diffing a header it has not
# accounted for.
kl_name_set() {
  local got expected unlisted absent
  got=$(strip_comments < "$(source_file u8kl)" | grep -oE "$detector_kl" | LC_ALL=C sort -u)
  expected=$(printf '%s\n' $entity_specs $perm_specs | sed 's/^[^:]*://' | LC_ALL=C sort -u)
  if [ -z "$got" ] || [ -z "$expected" ]; then
    printf 'SETUP: the kl_ name set is empty on one side\n' >&2
    return 3
  fi
  unlisted=$(comm -13 <(printf '%s\n' "$expected") <(printf '%s\n' "$got"))
  absent=$(comm -23 <(printf '%s\n' "$expected") <(printf '%s\n' "$got"))
  if [ -n "$unlisted" ] || [ -n "$absent" ]; then
    [ -n "$unlisted" ] && printf 'SETUP: u8kl.h names, unlisted: %s\n' "$(echo $unlisted)" >&2
    [ -n "$absent" ] && printf 'SETUP: the identity list names, absent: %s\n' "$(echo $absent)" >&2
    return 3
  fi
  printf 'ok: u8kl.h'"'"'s kl_ names are exactly its %s entities and %s permutation-form names\n' \
    "$(printf '%s\n' $entity_specs | wc -l | tr -d ' ')" \
    "$(printf '%s\n' $perm_specs | wc -l | tr -d ' ')"
}

# stage_tu -- the measured side of the stage's emitted-code comparison: the
# measured declarations and the extracted stage text.  This is the one
# definition of that text, so the IR arm and the timing arm build the same
# translation unit instead of two copies that could drift.  The function's name
# is `UTF8_STAGE_NAME`, so a caller that links it beside the unit can rename it.
stage_tu() {
  local name=${UTF8_STAGE_NAME:-leanllvm_json_utf8} loop_text tail_text whole loop_lines
  [ -n "$stage_specs" ] || {
    printf 'SETUP: unit %s has no stage range list\n' "$unit" >&2
    return 3
  }
  loop_text=$(extract_stage $stage_specs) || return 3
  tail_text=$(extract_stage $stage_tail_specs) || return 3
  loop_lines=$(printf '%s\n' "$loop_text" | wc -l | tr -d ' ')
  # The rename is applied to the stage as one text, exactly as the token arm
  # applies it, and the text is then split again by its line count: a rename
  # substitutes within a line and never adds or removes one.
  whole=$(apply_renames "$(printf '%s\n' "$loop_text"; printf '%s\n' "$tail_text")") || return 3
  loop_text=$(printf '%s\n' "$whole" | sed -n "1,${loop_lines}p")
  tail_text=$(printf '%s\n' "$whole" | sed -n "$((loop_lines + 1)),\$p")
  cat <<EOF
/* The measured side of the UTF-8 stage's emitted-code and timing comparisons:
   the measured declarations and the stage text the identity list names in
   measured/s1fuse.h, with its rename row applied.  Generated by
   source-identity.sh --stage-tu; not committed. */
#include <immintrin.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include "s1fuse.h"

uint64_t $name(const uint8_t *b, uint64_t n, int ungated)
{
    uint64_t nb = (n + 63) / 64;
    uint64_t err = 0;
    int prev_ascii = 1;
    const __m256i high = _mm256_set1_epi8((char)0x80);
    __m256i u8k = _mm256_setzero_si256();
    for (uint64_t bi = 0; bi < nb; bi++) {
        const uint8_t *p = b + (bi << 6);
        __m256i v0 = _mm256_loadu_si256((const __m256i *)p);
        __m256i v1 = _mm256_loadu_si256((const __m256i *)(p + 32));
$loop_text
    }
$tail_text
    return err;
}
EOF
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
  [ "$rc" -eq 3 ] && return 3

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

  if [ -n "$stage_specs" ]; then
    kl_name_set || return 3
    compare_stage "$kernel"
    fold_status $? || return 3
    compare_stage_copies
    fold_status $? || return 3
    stage_control
    fold_status $? || return 3
  fi
  return "$rc"
}

# fold_status <status> -- a stage result folded into the arm's own: 3 is a setup
# fault and stops the arm, any other nonzero failure is remembered in `rc`.
fold_status() {
  local st=$1
  [ "$st" -eq 3 ] && return 3
  [ "$st" -ne 0 ] && rc=1
  return 0
}

arm_mutate() {
  local rc=0 status st
  printf '\n== Control: text rewritten in a copy of the unit (%s)\n' "$kernel"
  printf '   the comparison must report a difference; its diff follows\n'

  # One numeral: `0xFFu` masks the group byte in `s1f_ke_pos8` / `s1f_masks`;
  # `0xe7,` is `kl_t1`'s first lane, which appears once in the header.
  case "$unit" in
    s1) local needle='0x1F' replacement='0x1E' subject=s1_masks ;;
    entry) local needle='0xFFu' replacement='0xFEu' subject=s1f_ke_pos8 ;;
    utf8) local needle='0xe7,' replacement='0xe5,' subject=kl_t1 ;;
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
  # UTF-8 switch takes.  It is the control in all three units.
  mkdir -p "$work/stub"
  cat > "$work/stub/u8kl.h" <<'EOF'
/* Generated for this arm only: `s1fuse.h:124` includes "u8kl.h" at
   S1F_UTF8=7.  The vendored copy of that header is in `measured/`, and this
   stub shadows it so the arm's text does not depend on the UTF-8 unit's text:
   what the control below reads is the measurement vocabulary in the measured
   header, not this unit's own names.  It is never committed. */
EOF
  printf '#include <stdio.h>\n#include <stdlib.h>\n#include <stdint.h>\n#include "s1fuse.h"\n' \
    > "$work/pre.control.c"
  "$cc" "${cflags[@]}" "${measured_defs[@]}" -I "$work/stub" -I "$measured" \
    -E -P "$work/pre.control.c" > "$work/control.i" || {
    printf 'SETUP: the measured header did not preprocess\n' >&2
    return 3
  }

  hits=$(grep -oE "$detector_unit" "$work/kernel.i" | sort -u || true)
  if [ -n "$hits" ]; then
    printf 'FAIL: the preprocessed unit names a measurement arm:\n%s\n' "$hits" >&2
    return 1
  fi
  case "$unit" in
    s1) printf 'ok: the preprocessed kernel names none of dens_/xl_/kl_/S1F_/SP_/sp_\n' ;;
    entry) printf 'ok: the preprocessed unit names none of dens_/kl_/S1F_/SP_/sp_\n' ;;
    utf8)
      printf 'ok: the preprocessed unit names none of dens_/S1F_/SP_/sp_\n'
      printf '    (kl_ is this unit'"'"'s subject, so its detector accepts it by design)\n'
      ;;
  esac

  if [ "$unit" = entry ]; then
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

  if [ "$unit" = utf8 ]; then
    # The calibrated detector's positive control: the same detector, on a copy
    # of the unit with one measurement identifier inserted, must name it.  A
    # detector that accepts `kl_` is only evidence if it still refuses what it
    # was widened away from.
    { cat "$kernel"; printf '\nint dens_u8_control;\n'; } > "$work/kernel.dens.c"
    "$cc" "${cflags[@]}" -I "$repo/kernel/json" -E -P "$work/kernel.dens.c" \
      > "$work/kernel.dens.i" || {
      printf 'SETUP: the detector control did not preprocess\n' >&2
      return 3
    }
    hits=$(grep -oE "$detector_unit" "$work/kernel.dens.i" | sort -u || true)
    if [ -z "$hits" ]; then
      printf 'FAIL: the detector names nothing in a copy that inserts a dens_ name\n' >&2
      return 1
    fi
    printf 'ok: control: the same detector names %s in a copy that inserts one\n' \
      "$(echo $hits)"
    # The ABI is one function, so the object's public symbols are exactly it.
    if ! command -v nm >/dev/null 2>&1; then
      printf 'SETUP: no nm on PATH; the public-symbol assertion needs it\n' >&2
      return 3
    fi
    hits=$(nm -g --defined-only "$work/kernel.o" | awk '{ print $3 }' | LC_ALL=C sort | tr '\n' ' ')
    hits=${hits% }
    if [ "$hits" != "leanllvm_json_utf8" ]; then
      printf 'FAIL: the unit defines the public symbols {%s}\n' "$hits" >&2
      printf 'FAIL: expected exactly leanllvm_json_utf8\n' >&2
      return 1
    fi
    printf 'ok: the unit defines exactly its one ABI symbol\n'
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

# The same anchored check against the fourth vendored file, for the six
# definitions the UTF-8 unit copies.
anchor_u8kl() { # <line> <text>
  local got
  got=$(sed -n "${1}p" "$measured/u8kl.h")
  case "$got" in
    *"$2"*) printf 'ok: u8kl.h:%-7s %s\n' "$1" "$2" ;;
    *)
      printf 'FAIL: u8kl.h:%s is not "%s"\n     got: %s\n' "$1" "$2" "$got" >&2
      return 1
      ;;
  esac
}

arm_vendor() {
  local f rc=0
  printf '\n== C4: the vendored set and its digests\n'
  for f in SHA256SUMS s1fuse.h xlist.h dens.h u8kl.h; do
    [ -f "$measured/$f" ] || { printf 'SETUP: absent: %s\n' "$measured/$f" >&2; return 3; }
    [ "$tree_only" -eq 1 ] && require_in_tree "$measured/$f"
  done
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
  anchor_u8kl 38 'static const uint8_t kl_t1[32]' || rc=1
  anchor_u8kl 44 'static const uint8_t kl_t2[32]' || rc=1
  anchor_u8kl 50 'static const uint8_t kl_t3[32]' || rc=1
  anchor_u8kl 114 'static inline __m256i kl_err32_ld(__m256i v, const uint8_t *p) {' || rc=1
  anchor_u8kl 139 'static inline __m256i kl_err_vec_ld(__m256i v0, __m256i v1, const uint8_t *p) {' || rc=1
  anchor_u8kl 152 'static inline int kl_tail_byte(uint8_t b) {' || rc=1
  [ "$rc" -eq 0 ] || return 1

  if [ -d "$scratch" ]; then
    if [ "$tree_only" -eq 1 ]; then
      require_in_tree "$scratch"
    fi
    for f in s1fuse.h xlist.h dens.h u8kl.h; do
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
   S1F_UTF8=7.  The vendored copy is in `measured/`, and this stub shadows it
   because the mask region must not depend on the UTF-8 unit's text; the checks
   below compare against an arm without it.  It is never committed. */
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

# The stage's measured side is printed and nothing else runs: this mode reads
# the vendored files and the identity list, not a unit, so its inputs are
# checked here rather than with the unit's.
if [ "$run_stage_tu" -eq 1 ]; then
  [ -n "$stage_specs" ] || {
    printf 'SETUP: unit %s has no stage range list\n' "$unit" >&2
    exit 3
  }
  for spec in $stage_specs $stage_tail_specs; do
    f=$(source_file "${spec%%:*}") || exit 3
    require_paths "$f"
    [ "$tree_only" -eq 1 ] && require_in_tree "$f"
  done
  stage_tu || exit $?
  exit 0
fi

if [ "$run_identity" -eq 1 ]; then arm_identity || exit $?; fi
if [ "$run_mutate" -eq 1 ]; then arm_mutate || exit $?; fi
if [ "$run_arms" -eq 1 ]; then arm_arms_only || exit $?; fi
if [ "$run_vendor" -eq 1 ]; then arm_vendor || exit $?; fi
if [ "$run_preprocess" -eq 1 ]; then arm_preprocess || exit $?; fi
printf '\nok: source identity holds (%s)\n' "$unit"
