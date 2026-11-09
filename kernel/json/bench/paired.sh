#!/usr/bin/env bash
# Arm C: the extracted unit costs what the measured one costs.
#
#   nix develop -c bash kernel/json/bench/paired.sh                        # the mask unit
#   nix develop -c bash kernel/json/bench/paired.sh --core 3 --rounds 15
#   nix develop -c bash kernel/json/bench/paired.sh --self-control
#   nix develop -c bash kernel/json/bench/paired.sh --unit entry           # the entry unit
#
# Units (`--unit s1` is the default, so every existing invocation keeps its
# meaning and its exit codes):
#
#   s1     one binary holds the measured and the extracted `s1f_masks` under
#          distinct symbols, selected per process; both acts run in the same
#          round, in rotated order, on the same data, and the reported number is
#          the median of (extracted - measured) ns per block over the rounds.
#          The bound is +/-0.5 ns/block on every input: each committed corpus
#          file and the three generated arms (every byte value in every lane,
#          every 4-byte sequence of the 16-symbol class alphabet, and a
#          fixed-seed random arm), each under the eight carry states.
#   entry  one binary holds the measured and the extracted `s1f_k_pos8` and
#          `s1f_k_b8`, again selected per process; the four acts are the two
#          kernels on each side, run in the same round over the same mask stream
#          and twice per round in both orders (so a drift inside the round
#          cancels in the difference), and the report is one median difference
#          per input and kernel against the same +/-0.5 ns/block bound.  The
#          unit's own table is initialised by a constructor in each probe TU,
#          outside the timed region.
#   utf8   the UTF-8 unit, whose two sides are two texts rather than two include
#          paths: the measured side is the translation unit
#          `source-identity.sh --unit utf8 --stage-tu` generates, with its
#          function renamed to `probe_utf8_measured`, and the extracted side is
#          `kernel/json/utf8.c` behind `probe_utf8_extracted`.  `paired-utf8.c`
#          is the binary's main and its two probes; the inputs are the curated
#          corpus `tests/json-utf8/corpus.tsv` and the arms the probes
#          generate, and the report is the per-input median difference against
#          the same +/-0.5 ns/block bound.
#   escape the escape unit.  The measured side is
#          `kernel/json/identity/escape_oracle.c` — the unit's two ABI entry
#          points over the vendored `xl_lanes`/`xl_emit` and `us_dec_x` — and
#          the extracted side is `kernel/json/escape.c`, both renamed so one
#          binary holds them.  `paired-escape.c` is the harness: one act walks
#          the block masks through the list and then expands the document from
#          the list it built, and the inputs are generated from the harness's
#          own rules.  The list the harness derives is checked against the
#          measured list before the clock starts.
#   pipeline the assembled pipeline, staged against the same source compiled as
#          one translation unit.  The staged side is `kernel/json/pipeline.c`
#          and each of the five units as its own translation unit, every call
#          crossing the external ABI the unit's header declares; it is the
#          form the model's records are stated at.  The one-TU side is the same
#          six files compiled as one translation unit, the form the recorded
#          ratios were measured on.  `paired-pipeline.c` is the harness; the
#          inputs are the documents under `probes/bench/json/`; both sides run
#          every document once and must agree byte for byte before either is
#          timed, and the entry table is the caller's — a constructor fills
#          both sides' 8 KiB before the first pipeline call.  The shell prints
#          the call census each form keeps, so the difference measured is the
#          one the compiler left.  A document under one full 4 KiB block is
#          reported as an observation, because one block divides the fixed
#          per-document term by its block count.  The claim is one-sided
#          (staged - one-TU <= +0.5 ns/block) and needs at least 301 rounds;
#          this unit's default round count is 301.
#
# `--self-control` runs the measured unit against itself.  It must report
# exactly 0.0, which tests the harness's dispatch and subtraction — the two
# acts are the same recorded sample — not the clock.
#
# The core class is read from CPUID.1Ah.EAX[31:24] by the binary and printed
# with the result.  `--core N` pins the run with `taskset -c N`; without it the
# process is unpinned and the class printed is the one it observed.  Repeat
# `--core` to run the same binary on more than one core class.
#
# All three units place their probes on 4 KiB boundaries (see each source file
# for why), and the entry and UTF-8 units additionally align every function to
# 4 KiB so the kernels or the stage they time have the same geometry on both
# sides; this script asserts the placement with `nm`.  For the entry unit it
# also prints the preprocessed text of the timed entry point and refuses to
# report a time unless that text names the extracted unit and calls both
# kernels -- a staged pipeline is not measured until its timed source is shown
# to reach the new code (`docs/json-pipeline-performance.md` §7.1); the same
# check runs for the UTF-8 unit and requires its timed source to name and call
# `leanllvm_json_utf8`.
#
# Exit status: 0 when every input holds, 1 when one is outside the bound,
# 3 on a setup fault (an absent input, tool or corpus, a build failure, a
# misaligned probe, a timed source that does not reach the extracted unit), so a
# missing dependency is never read as a measurement.
set -uo pipefail

here=$(cd "$(dirname "$0")" && pwd)
repo=$(cd "$here/../../.." && pwd)
measured=$repo/kernel/json/measured
kernel_dir=$repo/kernel/json
corpus=$repo/tests/json-s1-masks/corpus
cc=clang

# The measured compiler line (`build49.sh:17`) and P2 set (`build49.sh:21`).
cflags=(-O3 -march=x86-64-v3 -mpclmul -std=gnu11 -falign-loops=64 -falign-functions=64)
defs=(-DPSTAGE=32 -DPMODE=2 -DS1F_XS=5 -DS2_XP=1 -DS2_DEC_GATE=2 -DS1F_XS_DYN=1)
# The entry unit's measured set (`build49.sh:19-21`), with the UTF-8 switch at
# the header's default: the entry unit is not the UTF-8 unit, and no act here
# reaches that stage.
entry_defs=(-DSTAGE_PROBE -DS1F_ENT_PROBE=1 -DS1F_DENS=1 -DS1F_TWOPHASE=1
            -DS1F_EXP2=11 -DS1F_DISPATCH=1 -DS1F_UTF8=0 -DS1F_KL_DOC=0 -DPSTAGE=32
            -DPMODE=2 -DS1F_XS=5 -DS2_XP=1 -DS2_DEC_GATE=2 -DS1F_XS_DYN=1)
# The UTF-8 unit's: the same measured set with the stage selected.
utf8_defs=(-DSTAGE_PROBE -DS1F_ENT_PROBE=1 -DS1F_DENS=1 -DS1F_TWOPHASE=1
           -DS1F_EXP2=11 -DS1F_DISPATCH=1 -DS1F_UTF8=7 -DS1F_KL_DOC=1 -DPSTAGE=32
           -DPMODE=2 -DS1F_XS=5 -DS2_XP=1 -DS2_DEC_GATE=2 -DS1F_XS_DYN=1)
# The escape unit's: the measured set with the decoder's escape step enabled
# (`build49.sh:28`'s `-DUS_EMIT4=1`).
escape_defs=(-DSTAGE_PROBE -DS1F_ENT_PROBE=1 -DS1F_DENS=1 -DS1F_TWOPHASE=1
             -DS1F_EXP2=11 -DS1F_DISPATCH=1 -DS1F_UTF8=7 -DS1F_KL_DOC=1
             -DPSTAGE=32 -DPMODE=2 -DS1F_XS=5 -DS2_XP=1 -DS2_DEC_GATE=2
             -DS1F_XS_DYN=1 -DUS_EMIT4=1)

unit=s1
rounds=""
self_control=0
cores=()

usage() {
  awk 'NR > 1 && /^set -/ { exit } NR > 1 { print }' "$0" | sed 's/^# \{0,1\}//' 
}

while [ "$#" -gt 0 ]; do
  case "$1" in
    --unit) shift; unit=${1:-}; [ -n "$unit" ] || { printf 'paired: --unit needs a value\n' >&2; exit 3; } ;;
    --unit=*) unit=${1#--unit=} ;;
    --rounds) shift; rounds=${1:-}; [ -n "$rounds" ] || { printf 'paired: --rounds needs a value\n' >&2; exit 3; } ;;
    --core) shift; cores+=("${1:-}"); [ -n "${1:-}" ] || { printf 'paired: --core needs a value\n' >&2; exit 3; } ;;
    --self-control) self_control=1 ;;
    -h|--help) usage; exit 0 ;;
    *) printf 'paired: unknown argument %s\n' "$1" >&2; exit 3 ;;
  esac
  shift
done

case "$unit" in
  s1)
    src=$here/paired.c
    inputs=("$src" "$measured/s1fuse.h" "$kernel_dir/s1_block.c" "$corpus")
    ;;
  entry)
    src=$here/paired-entry.c
    inputs=("$src" "$measured/s1fuse.h" "$measured/xlist.h" "$kernel_dir/entry.c")
    ;;
  utf8)
    src=$here/paired-utf8.c
    inputs=("$src" "$measured/s1fuse.h" "$measured/u8kl.h" "$kernel_dir/utf8.c" \
            "$repo/kernel/json/identity/source-identity.sh" \
            "$repo/tests/json-utf8/corpus.tsv")
    ;;
  escape)
    src=$here/paired-escape.c
    inputs=("$src" "$kernel_dir/escape.c" "$kernel_dir/escape.h" \
            "$repo/kernel/json/identity/escape_oracle.c" \
            "$measured/s1fuse.h" "$measured/xlist.h" "$measured/usdec.h" \
            "$measured/uj.c")
    ;;
  pipeline)
    # The two forms are built from the same source: the six translation units
    # the staged form keeps apart, and the one translation unit that includes
    # them.  The documents are `probes/bench/json/`, the directory the record's
    # in-tree comparison names.
    src=$here/paired-pipeline.c
    inputs=("$src" "$kernel_dir/pipeline.c" "$kernel_dir/pipeline.h" \
            "$kernel_dir/s1_block.c" "$kernel_dir/s1_block.h" \
            "$kernel_dir/entry.c" "$kernel_dir/entry.h" \
            "$kernel_dir/utf8.c" "$kernel_dir/utf8.h" \
            "$kernel_dir/escape.c" "$kernel_dir/escape.h" \
            "$kernel_dir/stage2.c" "$kernel_dir/stage2.h" \
            "$repo/probes/bench/json")
    ;;
  *)
    printf 'SETUP: unit %s has no paired timing arm; implemented units: s1 entry utf8 escape pipeline\n' "$unit" >&2
    exit 3
    ;;
esac

# The pipeline arm's claim is stated at 301 interleaved rounds (the record's
# round count for a high-noise row); every other unit keeps the default it has
# always had.
if [ -z "$rounds" ]; then
  if [ "$unit" = pipeline ]; then rounds=301; else rounds=11; fi
fi

for path in "${inputs[@]}"; do
  [ -e "$path" ] || { printf 'SETUP: absent: %s\n' "$path" >&2; exit 3; }
done
command -v "$cc" >/dev/null 2>&1 || { printf 'SETUP: no %s on PATH\n' "$cc" >&2; exit 3; }
if [ "${#cores[@]}" -gt 0 ] && ! command -v taskset >/dev/null 2>&1; then
  printf 'SETUP: --core needs taskset on PATH\n' >&2
  exit 3
fi

mkdir -p "$repo/.lake" || { printf 'SETUP: cannot create %s/.lake\n' "$repo" >&2; exit 3; }
work=$(mktemp -d "$repo/.lake/tmp-$unit-bench.XXXXXX" 2>/dev/null) || {
  printf 'SETUP: cannot create a work directory under %s/.lake\n' "$repo" >&2
  exit 3
}
trap 'rm -rf "$work"' EXIT

build() { # <output> <args...>
  local out=$1
  shift
  if ! "$cc" "$@" -o "$out" 2>"$work/build.err"; then
    printf 'SETUP: %s did not build\n' "$out" >&2
    awk 'NR <= 40' "$work/build.err" >&2
    exit 3
  fi
}

# call_census <object> <function> -- the calls one function makes, as
# `<name> <count>` lines.  A relocatable object has not resolved a call across
# sections, so the target is the symbol `objdump -dr` writes on the line after
# the call; a call already resolved prints its own `<name>`; and a call into the
# function itself is the trap idiom and is not a callee.
call_census() { # <object> <function>
  objdump -dr --no-show-raw-insn "$1" | awk -v target="$2" '
    /^[0-9a-f]+ <.*>:/ {
      fn = $0
      sub(/^[0-9a-f]+ </, "", fn)
      sub(/>:.*/, "", fn)
      pending = 0
      next
    }
    fn != target { next }
    /R_X86_64_PLT32/ {
      if (pending) {
        name = $0
        sub(/.*R_X86_64_PLT32[ \t]+/, "", name)
        sub(/[-+].*$/, "", name)
        if (name != "") c[name]++
        pending = 0
      }
      next
    }
    /^[ \t]*[0-9a-f]+:/ {
      if (pending) pending = 0
      if ($0 ~ /[ \t]call[ \t]/) {
        if ($0 ~ /<[^>]*>/) {
          name = $0
          sub(/.*</, "", name)
          sub(/>.*/, "", name)
          if (name ~ /\+/) {
            # An unresolved call prints the enclosing function symbol plus the
            # addend; its target is on the following relocation line.  A call
            # into the function itself (the trap idiom) has no relocation and
            # is dropped when the next instruction clears `pending`.
            pending = 1
          } else {
            c[name]++
          }
        } else {
          pending = 1
        }
      }
    }
    END { for (n in c) print n, c[n] }
  ' | LC_ALL=C sort
}

# fixture_census <fixture> -- the call targets the pinned emission names, as
# `<name> <count>` lines.
fixture_census() { # <fixture.ll>
  awk '
    /call .*@leanllvm_json_/ {
      line = $0
      while (match(line, /@leanllvm_json_[a-z0-9_]+/)) {
        n = substr(line, RSTART + 1, RLENGTH - 1)
        c[n]++
        line = substr(line, RSTART + RLENGTH)
      }
    }
    END { for (n in c) print n, c[n] }
  ' "$1" | LC_ALL=C sort
}

if [ "$unit" = s1 ]; then
  build "$work/measured.o" "${cflags[@]}" "${defs[@]}" -DPAIRED_PROBE=measured \
    -DPAIRED_MEASURED -DPROBE_NAME=probe_measured -I "$measured" -c "$src"
  build "$work/kernel.o" "${cflags[@]}" "${defs[@]}" -DPAIRED_PROBE=kernel \
    -DPROBE_NAME=probe_kernel -I "$kernel_dir" -c "$src"
  build "$work/main.o" -O2 -DPAIRED_MAIN -c "$src"
  build "$work/paired" -O2 "$work/main.o" "$work/measured.o" "$work/kernel.o"
elif [ "$unit" = escape ]; then
  # The measured side includes the vendored text; the extracted side is the
  # unit.  Both are renamed so the two copies of each ABI function share one
  # binary, and both get the same function alignment.
  build "$work/measured.o" "${cflags[@]}" "${escape_defs[@]}" \
    -falign-functions=4096 \
    -Dleanllvm_json_escape_list=probe_escape_list_measured \
    -Dleanllvm_json_escape_expand=probe_escape_expand_measured \
    -I "$measured" -c "$repo/kernel/json/identity/escape_oracle.c"
  build "$work/kernel.o" "${cflags[@]}" -falign-functions=4096 \
    -Dleanllvm_json_escape_list=probe_escape_list_extracted \
    -Dleanllvm_json_escape_expand=probe_escape_expand_extracted \
    -I "$kernel_dir" -c "$kernel_dir/escape.c"
  build "$work/main.o" -O2 -c "$src"
  build "$work/paired" -O2 "$work/main.o" "$work/measured.o" "$work/kernel.o"
elif [ "$unit" = utf8 ]; then
  # The measured side is generated, not included: the stage is a region of the
  # measured header, so the token arm's helper pastes it into the measured
  # declarations and the function is renamed here so the two sides can share one
  # binary.  4 KiB alignment on both sides, as for the entry unit.
  UTF8_STAGE_NAME=probe_utf8_measured \
    bash "$repo/kernel/json/identity/source-identity.sh" --unit utf8 --stage-tu \
    > "$work/stage-a.c" || {
    printf 'SETUP: the measured side could not be generated\n' >&2
    exit 3
  }
  if [ ! -s "$work/stage-a.c" ]; then
    printf 'SETUP: the generated measured side is empty\n' >&2
    exit 3
  fi
  build "$work/measured.o" "${cflags[@]}" "${utf8_defs[@]}" -falign-functions=4096 \
    -I "$measured" -c "$work/stage-a.c"
  build "$work/kernel.o" "${cflags[@]}" "${utf8_defs[@]}" -falign-functions=4096 \
    -DPAIRED_PROBE=extracted -DPROBE_NAME=probe_utf8_extracted \
    -I "$kernel_dir" -c "$src"
  build "$work/main.o" -O2 -DPAIRED_MAIN -c "$src"
  build "$work/paired" -O2 "$work/main.o" "$work/measured.o" "$work/kernel.o"
elif [ "$unit" = pipeline ]; then
  # The staged form: each of the six files is its own translation unit, and
  # the pipeline reaches the units through the ABI their headers declare.
  # Every function is 4 KiB aligned on both sides, as the entry, UTF-8 and
  # escape arms do; the two pipeline symbols' page placement is asserted below.
  for u in s1_block entry utf8 escape stage2; do
    build "$work/$u.o" "${cflags[@]}" -falign-functions=4096 \
      -I "$kernel_dir" -c "$kernel_dir/$u.c"
  done
  build "$work/staged.o" "${cflags[@]}" -falign-functions=4096 \
    -Dleanllvm_json_pipeline=probe_pipeline_staged \
    -I "$kernel_dir" -c "$kernel_dir/pipeline.c"
  # The one-TU form: the same six files compiled as one translation unit.  The
  # renames are the whole adaptation, so no unit's text is edited and the two
  # forms are the same source.  The ABI names are renamed on the one-TU side
  # only, so one binary holds both.
  {
    for n in s1_masks entry_pos8 entry_b8 entry_table utf8 escape_list \
             escape_expand stage2; do
      printf '#define leanllvm_json_%s probe_inl_%s\n' "$n" "$n"
    done
    printf '#define leanllvm_json_pipeline probe_pipeline_inlined\n'
    for u in s1_block entry utf8 escape stage2 pipeline; do
      printf '#include "%s"\n' "$kernel_dir/$u.c"
    done
  } > "$work/inlined.c"
  build "$work/inlined.o" "${cflags[@]}" -falign-functions=4096 \
    -I "$kernel_dir" -c "$work/inlined.c"
  build "$work/main.o" -O2 -c "$src"
  build "$work/paired" -O2 "$work/main.o" "$work/staged.o" "$work/inlined.o" \
    "$work/s1_block.o" "$work/entry.o" "$work/utf8.o" "$work/escape.o" \
    "$work/stage2.o"
else
  # 4 KiB function alignment on both probe TUs: the kernels are measured text
  # and cannot carry an attribute, so the geometry is set by the flag, equally
  # for both sides, and asserted below.
  build "$work/measured.o" "${cflags[@]}" "${defs[@]}" "${entry_defs[@]}" \
    -falign-functions=4096 -DPAIRED_PROBE=measured -DPAIRED_MEASURED \
    -DPROBE_NAME=probe_entry_measured -I "$measured" -c "$src"
  build "$work/kernel.o" "${cflags[@]}" "${defs[@]}" "${entry_defs[@]}" \
    -falign-functions=4096 -DPAIRED_PROBE=extracted \
    -DPROBE_NAME=probe_entry_extracted -I "$kernel_dir" -c "$src"
  build "$work/main.o" -O2 -DPAIRED_MAIN -c "$src"
  build "$work/paired" -O2 "$work/main.o" "$work/measured.o" "$work/kernel.o"
fi

# The two probes must sit at page boundaries, or the comparison measures their
# addresses' uop-cache and I-cache sets as well as their code (the source says
# why).  `nm` is not required; when it is present the placement is asserted.
if command -v nm >/dev/null 2>&1; then
  if [ "$unit" = s1 ]; then
    probe_addrs=$(nm "$work/paired" | awk '$3 ~ /^probe_(measured|kernel)$/ { print $1 }')
    bad=$(printf '%s\n' "$probe_addrs" | grep -cv '000$' || true)
    if [ "$(printf '%s\n' "$probe_addrs" | grep -c . || true)" -ne 2 ] || [ "$bad" -ne 0 ]; then
      printf 'SETUP: the probes are not page-aligned: %s\n' "$(echo $probe_addrs)" >&2
      exit 3
    fi
    printf 'probe addresses %s (page-aligned)\n' "$(echo $probe_addrs)"
  elif [ "$unit" = escape ]; then
    probe_addrs=$(nm "$work/paired" | awk '$3 ~ /^probe_escape_(list|expand)_(measured|extracted)$/ { print $1, $3 }')
    if [ "$(printf '%s\n' "$probe_addrs" | grep -c . || true)" -ne 4 ]; then
      printf 'SETUP: expected four probe symbols, found: %s\n' "$(echo $probe_addrs)" >&2
      exit 3
    fi
    bad=$(printf '%s\n' "$probe_addrs" | awk '$1 !~ /000$/ { print $1, $2 }')
    if [ -n "$bad" ]; then
      printf 'SETUP: a probe is not page-aligned: %s\n' "$(echo $bad)" >&2
      exit 3
    fi
    printf 'probe addresses (page-aligned):\n'
    printf '%s\n' "$probe_addrs" | awk '{ printf "  %s %s\n", $1, $2 }'
  elif [ "$unit" = utf8 ]; then
    probe_addrs=$(nm "$work/paired" | awk '$3 ~ /^probe_utf8_(measured|extracted)$/ { print $1, $3 }')
    if [ "$(printf '%s\n' "$probe_addrs" | grep -c . || true)" -ne 2 ]; then
      printf 'SETUP: expected two probe symbols, found: %s\n' "$(echo $probe_addrs)" >&2
      exit 3
    fi
    bad=$(printf '%s\n' "$probe_addrs" | awk '$1 !~ /000$/ { print $1, $2 }')
    if [ -n "$bad" ]; then
      printf 'SETUP: a probe is not page-aligned: %s\n' "$(echo $bad)" >&2
      exit 3
    fi
    printf 'probe addresses (page-aligned):\n'
    printf '%s\n' "$probe_addrs" | awk '{ printf "  %s %s\n", $1, $2 }'
  elif [ "$unit" = pipeline ]; then
    # The two forms are two symbols; each must start a page, as every other
    # arm's probes do.
    probe_addrs=$(nm "$work/paired" | awk '$3 ~ /^probe_pipeline_(staged|inlined)$/ { print $1, $3 }')
    if [ "$(printf '%s\n' "$probe_addrs" | grep -c . || true)" -ne 2 ]; then
      printf 'SETUP: expected two pipeline symbols, found: %s\n' "$(echo $probe_addrs)" >&2
      exit 3
    fi
    bad=$(printf '%s\n' "$probe_addrs" | awk '$1 !~ /000$/ { print $1, $2 }')
    if [ -n "$bad" ]; then
      printf 'SETUP: a pipeline does not start a page: %s\n' "$(echo $bad)" >&2
      exit 3
    fi
    printf 'pipeline addresses (page-aligned):\n'
    printf '%s\n' "$probe_addrs" | awk '{ printf "  %s %s\n", $1, $2 }'

    # The staged object is built from `pipeline.c` alone, so its undefined set
    # is the ABI it calls; the one-TU object is the same source with those
    # names resolved inside it.
    staged_undef=$(nm -u "$work/staged.o" | awk '{ print $NF }' | LC_ALL=C sort)
    want_undef=$(printf '%s\n' leanllvm_json_entry_b8 leanllvm_json_entry_pos8 \
      leanllvm_json_escape_list leanllvm_json_s1_masks leanllvm_json_stage2 \
      leanllvm_json_utf8 | LC_ALL=C sort)
    if [ "$staged_undef" != "$want_undef" ]; then
      printf 'SETUP: the staged pipeline leaves undefined {%s}\n' "$(echo $staged_undef)" >&2
      printf 'SETUP: expected exactly the six unit ABIs\n' >&2
      exit 3
    fi
    printf 'staged pipeline leaves undefined exactly the six unit ABIs\n'
    if nm -u "$work/inlined.o" | awk '{ print $NF }' | grep -qE '^(leanllvm_json_|probe_inl_)'; then
      printf 'SETUP: the one-TU object leaves a unit symbol unresolved\n' >&2
      exit 3
    fi
    printf 'one-TU object resolves every unit symbol inside itself\n'

    # The calls each form keeps.  The staged form must match the pinned
    # emission exactly; the one-TU form must have dropped at least one unit
    # boundary, or the comparison would measure placement alone.
    staged_census=$(call_census "$work/staged.o" probe_pipeline_staged)
    inlined_census=$(call_census "$work/inlined.o" probe_pipeline_inlined)
    pinned_census=$(fixture_census "$repo/probes/install/ir/json-pipeline.candidate.ll")
    if [ "$staged_census" != "$pinned_census" ]; then
      printf 'SETUP: the staged pipeline'"'"'s call census is not the pinned emission'"'"'s\n' >&2
      diff -u <(printf '%s\n' "$pinned_census") <(printf '%s\n' "$staged_census") \
        | awk 'NR <= 20' >&2
      exit 3
    fi
    printf 'staged call census (the pinned emission'"'"'s):\n'
    printf '%s\n' "$staged_census" | awk '{ printf "  %-32s %s\n", $1, $2 }'
    if [ -z "$inlined_census" ]; then
      printf 'SETUP: the one-TU pipeline makes no calls; it is not the one-TU form\n' >&2
      exit 3
    fi
    printf 'one-TU call census (the calls the compiler kept):\n'
    printf '%s\n' "$inlined_census" | awk '{ printf "  %-32s %s\n", $1, $2 }'
    inlined_abi=$(printf '%s\n' "$inlined_census" | awk '$1 ~ /^probe_inl_/ { print $1 }')
    dropped=0
    for n in leanllvm_json_s1_masks leanllvm_json_entry_pos8 leanllvm_json_entry_b8 \
             leanllvm_json_escape_list leanllvm_json_utf8 leanllvm_json_stage2; do
      inl=${n/leanllvm_json_/probe_inl_}
      printf '%s\n' "$inlined_abi" | grep -qxF "$inl" || dropped=$((dropped + 1))
    done
    if [ "$dropped" -eq 0 ]; then
      printf 'SETUP: the one-TU form inlined no unit boundary; the comparison would\n' >&2
      printf 'SETUP: measure placement alone\n' >&2
      exit 3
    fi
    printf 'ok: the one-TU form inlined %s of the six unit boundaries\n' "$dropped"
  else
    probe_addrs=$(nm "$work/paired" | awk '$3 ~ /^probe_entry_(measured|extracted)_(pos8|b8)$/ { print $1, $3 }')
    if [ "$(printf '%s\n' "$probe_addrs" | grep -c . || true)" -ne 4 ]; then
      printf 'SETUP: expected four probe symbols, found: %s\n' "$(echo $probe_addrs)" >&2
      exit 3
    fi
    bad=$(printf '%s\n' "$probe_addrs" | awk '$1 !~ /000$/ { print $1, $2 }')
    if [ -n "$bad" ]; then
      printf 'SETUP: a probe is not page-aligned: %s\n' "$(echo $bad)" >&2
      exit 3
    fi
    printf 'probe addresses (page-aligned):\n'
    printf '%s\n' "$probe_addrs" | awk '{ printf "  %s %s\n", $1, $2 }'
    # The kernels cannot carry the attribute, so their geometry is asserted as
    # congruence: the measured and the extracted copy of a kernel must have the
    # same offset inside its page, which is what the caches map by.
    for kname in s1f_k_pos8 s1f_k_b8; do
      low=$(nm "$work/paired" | awk -v n="^$kname$" '$3 ~ n { print substr($1, length($1) - 2) }' | LC_ALL=C sort -u)
      count=$(nm "$work/paired" | awk -v n="^$kname$" '$3 ~ n' | wc -l | tr -d ' ')
      if [ "$count" -ne 2 ] || [ "$(printf '%s\n' "$low" | grep -c .)" -ne 1 ]; then
        printf 'SETUP: %s: %s copies at page offsets {%s}; the geometry is not shared\n' \
          "$kname" "$count" "$(echo $low)" >&2
        exit 3
      fi
      printf 'kernel %s: 2 copies, both at page offset 0x%s\n' "$kname" "$(echo $low)"
    done
  fi
else
  printf 'note: nm is absent, so the probes'"'"' page alignment is not asserted\n'
fi

# §7.1: the timed entry point's preprocessed text must name the new code.
if [ "$unit" = entry ]; then
  "$cc" "${cflags[@]}" "${defs[@]}" "${entry_defs[@]}" -falign-functions=4096 \
    -DPAIRED_PROBE=extracted -DPROBE_NAME=probe_entry_extracted -I "$kernel_dir" \
    -E -P "$src" > "$work/timed.i" 2>"$work/timed.err" || {
    printf 'SETUP: the timed source did not preprocess\n' >&2
    awk 'NR <= 20' "$work/timed.err" >&2
    exit 3
  }
  if ! grep -q 'leanllvm_json_entry_pos8' "$work/timed.i"; then
    printf 'SETUP: the timed source does not name the extracted unit\n' >&2
    printf 'SETUP: docs/json-pipeline-performance.md 7.1: the timed path must reach the new code\n' >&2
    exit 3
  fi
  for pair in pos8:s1f_k_pos8 b8:s1f_k_b8; do
    suffix=${pair%%:*}
    kernel=${pair#*:}
    body=$(awk -v name="probe_entry_extracted_$suffix" '
      !infn && index($0, name "(") > 0 &&
        ($0 ~ /\([ \t]*$/ || $0 ~ /\{[ \t]*$/) { infn = 1 }
      infn {
        print
        probe = $0
        o = gsub(/\{/, "", probe); c = gsub(/\}/, "", probe)
        depth += o - c
        if (o > 0) opened = 1
        if (opened && depth == 0) exit
      }
    ' "$work/timed.i")
    if [ -z "$body" ] || ! printf '%s\n' "$body" | grep -qF "$kernel("; then
      printf 'SETUP: the timed probe %s does not call %s in its preprocessed text\n' \
        "probe_entry_extracted_$suffix" "$kernel" >&2
      printf 'SETUP: docs/json-pipeline-performance.md 7.1: the timed path must reach the new code\n' >&2
      exit 3
    fi
  done
  printf 'timed entry point reaches the extracted unit (docs/json-pipeline-performance.md 7.1):\n'
  printf '  the preprocessed TU names leanllvm_json_entry_pos8, and both probes call\n'
  printf '  their own kernel (s1f_k_pos8, s1f_k_b8)\n'
elif [ "$unit" = utf8 ]; then
  "$cc" "${cflags[@]}" "${utf8_defs[@]}" -falign-functions=4096 \
    -DPAIRED_PROBE=extracted -DPROBE_NAME=probe_utf8_extracted -I "$kernel_dir" \
    -E -P "$src" > "$work/timed.i" 2>"$work/timed.err" || {
    printf 'SETUP: the timed source did not preprocess\n' >&2
    awk 'NR <= 20' "$work/timed.err" >&2
    exit 3
  }
  if ! grep -q 'leanllvm_json_utf8' "$work/timed.i"; then
    printf 'SETUP: the timed source does not name the extracted unit\n' >&2
    printf 'SETUP: docs/json-pipeline-performance.md 7.1: the timed path must reach the new code\n' >&2
    exit 3
  fi
  body=$(awk -v name="probe_utf8_extracted" '
    !infn && index($0, name "(") > 0 &&
      ($0 ~ /\([ \t]*$/ || $0 ~ /\{[ \t]*$/) { infn = 1 }
    infn {
      print
      probe = $0
      o = gsub(/\{/, "", probe); c = gsub(/\}/, "", probe)
      depth += o - c
      if (o > 0) opened = 1
      if (opened && depth == 0) exit
    }
  ' "$work/timed.i")
  if [ -z "$body" ] || ! printf '%s\n' "$body" | grep -qF 'leanllvm_json_utf8('; then
    printf 'SETUP: the timed probe probe_utf8_extracted does not call the unit in its\n' >&2
    printf 'SETUP: preprocessed text; docs/json-pipeline-performance.md 7.1\n' >&2
    exit 3
  fi
  printf 'timed entry point reaches the extracted unit (docs/json-pipeline-performance.md 7.1):\n'
  printf '  the preprocessed TU names leanllvm_json_utf8, and probe_utf8_extracted calls it\n'
elif [ "$unit" = pipeline ]; then
  # The staged pipeline's timed body must reach the six units through their
  # ABI calls, and the one-TU form must be the same source with those
  # definitions inside its own translation unit.  A build whose timed body did
  # not reach the units would time the wrong binary, which is the §7.1 defect.
  "$cc" "${cflags[@]}" -falign-functions=4096 \
    -Dleanllvm_json_pipeline=probe_pipeline_staged -I "$kernel_dir" \
    -E -P "$kernel_dir/pipeline.c" > "$work/timed.i" 2>"$work/timed.err" || {
    printf 'SETUP: the staged pipeline did not preprocess\n' >&2
    awk 'NR <= 20' "$work/timed.err" >&2
    exit 3
  }
  body=$(awk -v name="probe_pipeline_staged" '
    state == 0 && index($0, name "(") > 0 { state = 1; next }
    state == 1 && $0 !~ /\{/ && $0 ~ /;[ \t]*$/ { state = 0; next }
    state == 1 && $0 ~ /\{/ { state = 2 }
    state == 2 {
      print
      probe = $0
      o = gsub(/\{/, "", probe); c = gsub(/\}/, "", probe)
      depth += o - c
      if (o > 0) opened = 1
      if (opened && depth == 0) exit
    }
  ' "$work/timed.i")
  if [ -z "$body" ]; then
    printf 'SETUP: the timed staged body was not found in its preprocessed text\n' >&2
    exit 3
  fi
  for callee in leanllvm_json_s1_masks leanllvm_json_entry_pos8 \
                leanllvm_json_entry_b8 leanllvm_json_escape_list \
                leanllvm_json_utf8 leanllvm_json_stage2; do
    if ! printf '%s\n' "$body" | grep -qF "$callee("; then
      printf 'SETUP: the timed staged body does not call %s\n' "$callee" >&2
      printf 'SETUP: docs/json-pipeline-performance.md 7.1: the timed path must reach the new code\n' >&2
      exit 3
    fi
  done
  "$cc" "${cflags[@]}" -falign-functions=4096 -I "$kernel_dir" \
    -E -P "$work/inlined.c" > "$work/inlined.i" 2>"$work/timed.err" || {
    printf 'SETUP: the one-TU source did not preprocess\n' >&2
    awk 'NR <= 20' "$work/timed.err" >&2
    exit 3
  }
  for def in probe_inl_s1_masks probe_inl_entry_pos8 probe_inl_entry_b8 \
             probe_inl_utf8 probe_inl_escape_list probe_inl_escape_expand \
             probe_inl_stage2 probe_pipeline_inlined; do
    if ! grep -qE "^[A-Za-z_][A-Za-z0-9_ *]*\b${def}\(" "$work/inlined.i"; then
      printf 'SETUP: the one-TU source does not define %s\n' "$def" >&2
      exit 3
    fi
  done
  printf 'timed pipeline reaches the units (docs/json-pipeline-performance.md 7.1):\n'
  printf '  the staged body calls all six unit ABIs; the one-TU source holds all six\n'
  printf '  definitions and the pipeline in one translation unit\n'
fi

printf 'unit        %s\n' "$unit"
printf 'binary      %s\n' "$work/paired"
printf 'binary sha256 %s\n' "$(sha256sum "$work/paired" | cut -d' ' -f1)"
if [ "$unit" = pipeline ]; then
  printf 'staged obj sha256   %s\n' "$(sha256sum "$work/staged.o" | cut -d' ' -f1)"
  printf 'one-TU obj sha256   %s\n' "$(sha256sum "$work/inlined.o" | cut -d' ' -f1)"
  cc_version=$("$cc" -dumpversion 2>/dev/null || printf 'unknown')
  cc_target=$("$cc" -dumpmachine 2>/dev/null || printf 'unknown')
  printf 'compiler    %s %s\n' "$cc" "$cc_version"
  printf 'compiler-line %s %s -falign-functions=4096\n' "$cc" "${cflags[*]}"
  printf 'target      %s\n' "$cc_target"
  build_id="$cc-$cc_version/$cc_target/measured-line+falign4096"
else
  printf 'measured obj sha256 %s\n' "$(sha256sum "$work/measured.o" | cut -d' ' -f1)"
  printf 'extracted obj sha256 %s\n' "$(sha256sum "$work/kernel.o" | cut -d' ' -f1)"
fi

args=()
if [ "$unit" = s1 ]; then
  mapfile -t corpus_files < <(find "$corpus" -mindepth 1 -maxdepth 1 -type f | LC_ALL=C sort)
  [ "${#corpus_files[@]}" -gt 0 ] || { printf 'SETUP: no corpus files under %s\n' "$corpus" >&2; exit 3; }
  for f in "${corpus_files[@]}"; do args+=(--corpus "$f"); done
elif [ "$unit" = utf8 ]; then
  # One file, not a directory: the curated rows are the committed corpus and the
  # probe generates the counted arms around them.
  args+=(--corpus "$repo/tests/json-utf8/corpus.tsv")
elif [ "$unit" = pipeline ]; then
  # The documents the record's in-tree comparison names.  A directory with no
  # document is a setup fault, not an empty measurement.
  mapfile -t documents < <(find "$repo/probes/bench/json" -mindepth 1 -maxdepth 1 \
                             -type f -name '*.json' | LC_ALL=C sort)
  [ "${#documents[@]}" -gt 0 ] || {
    printf 'SETUP: no documents under %s/probes/bench/json\n' "$repo" >&2
    exit 3
  }
  for f in "${documents[@]}"; do args+=(--document "$f"); done
  args+=(--build "$build_id")
fi
args+=(--arms --rounds "$rounds")
[ "$self_control" -eq 1 ] && args+=(--self-control)

# A snapshot of the window's edges: the load average, the running processes and
# the build tools.  It cannot prove the window was quiet, so a run whose edge
# snapshots name a build process is labelled rather than reported as clean.
process_ancestors() { # the pids from this shell up to init, space-delimited
  local p=$$ out=" "
  while :; do
    [ -n "$p" ] && [ "$p" -gt 1 ] || break
    out="$out$p "
    p=$(ps -o ppid= -p "$p" 2>/dev/null | tr -d ' ')
  done
  printf '%s' "$out"
}

snapshot() { # <label>
  local label=$1 load running mine names
  load=$(cut -d' ' -f1-3 /proc/loadavg 2>/dev/null || printf 'unknown')
  running=$(ps -eo stat= 2>/dev/null | grep -c '^R' || true)
  # A build process that is this command's own ancestor (the `nix develop -c`
  # wrapper and the shell it started) is not a concurrent workload, so it is
  # excluded by pid; a sibling build is not an ancestor and is reported.
  mine=$(process_ancestors)
  names=$(ps -eo pid=,comm= 2>/dev/null \
    | awk -v mine="$mine" '
        $2 ~ /^(clang[^ ]*|cc1|cc1plus|ld|ld\.lld|lld|lake|lean|nix|nix-store|cargo|rustc|make|ninja)$/ &&
        index(mine, " " $1 " ") == 0 { print $2 }' \
    | LC_ALL=C sort | uniq -c \
    | awk '{ printf "%s:%s ", $2, $1 }' | sed 's/ $//')
  printf 'quiet %-12s load=%s running=%s builds=%s\n' "$label" "$load" "$running" "${names:-none}"
  [ -z "$names" ]
}

interference=0
status=0
if [ "${#cores[@]}" -eq 0 ]; then
  if [ "$unit" = pipeline ] && ! snapshot before; then interference=1; fi
  "$work/paired" "${args[@]}" || status=$?
  if [ "$unit" = pipeline ] && ! snapshot after; then interference=1; fi
else
  for core in "${cores[@]}"; do
    printf '\n== pinned to CPU %s\n' "$core"
    if [ "$unit" = pipeline ] && ! snapshot "cpu$core-before"; then interference=1; fi
    taskset -c "$core" "$work/paired" "${args[@]}" || status=$?
    if [ "$unit" = pipeline ] && ! snapshot "cpu$core-after"; then interference=1; fi
  done
fi

if [ "$unit" = pipeline ]; then
  if [ "$interference" -eq 1 ]; then
    printf 'interference: a build process was present at a window edge; these rows are\n'
    printf '              labelled, not presented as clean\n'
  else
    printf 'interference: none named by the edge snapshots (a snapshot cannot prove the\n'
    printf '              window was quiet between them)\n'
  fi
fi

if [ "$status" -eq 0 ]; then
  if [ "$self_control" -eq 1 ]; then
    printf '\nok: the harness reports 0.0 against itself\n'
  elif [ "$unit" = escape ]; then
    printf '\nok: every bounded input is within +/-0.5 ns/block of the measured one\n'
    printf '    (arm:escapes-64 is reported as an observation with no delta claim)\n'
  elif [ "$unit" = pipeline ]; then
    printf '\nok: every claimed document is within the one-sided +0.5 ns/block bound\n'
    printf '    (a document under one full 4 KiB block is an observation with no claim)\n'
  else
    printf '\nok: the extracted unit is within +/-0.5 ns/block of the measured one\n'
  fi
fi
exit "$status"
