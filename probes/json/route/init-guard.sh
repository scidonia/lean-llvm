#!/usr/bin/env bash
# The POS8 entry table's initialisation guard.
#
#   nix develop -c bash probes/json/route/init-guard.sh
#
# `leanllvm_json_entry_pos8` reads the entry unit's file-static `xl_pos8`
# table, and only `leanllvm_json_entry_table` fills it.  `pipeline.h` makes the
# fill a precondition of any run whose arm word has bit 0 clear, and the
# emitter enforces it: a pos8 call before the fill traps rather than writing a
# position stream from the zero-initialised table.  Without that, the caller
# gets a well-formed stream of wrong positions and a plausible verdict -- the
# silent wrong answer this scenario exists to rule out.
#
# The probe (`init_guard_check.c`) runs the pipeline on one small document in
# three separate processes:
#
#   1. initialised: the table is filled, then the pipeline is called at arm 0
#      (pos8) and at arm 1 (b8) and the two entry streams must be identical.
#      That is the initialised path still correct, and it is a relation rather
#      than a remembered count: b8 reads no table, so pos8's stream must equal
#      a stream produced without it.
#   2. bare: the table is not filled and the pipeline is called at arm 0.  The
#      process must die by SIGILL (status 132) with no result printed.  A
#      returned result, whatever its verdict, is the defect: it is the
#      silent-wrong-answer failure mode stated as a red.
#   3. b8-bare: the table is not filled and the pipeline is called at arm 1.
#      B8 reads no table, so it must accept.  This is the control that the
#      SIGILL in (2) is the pos8 table's check and not an unrelated fault:
#      the same process setup without the table succeeds on the arm that does
#      not read it.
#
# A guard that always fired, or a check on arm 1 as well, would fail (1) and
# (3); a guard that never fired would fail (2).  Exit status: 0 when all three
# hold, 1 when one fails, 3 on a setup fault (no clang, an absent source, a
# build that failed).
set -uo pipefail

here=$(cd "$(dirname "$0")" && pwd)
repo=$(cd "$here/../../.." && pwd)
kernel=$repo/kernel/json
cc=clang

command -v "$cc" >/dev/null 2>&1 || { printf 'SETUP: no clang on PATH\n' >&2; exit 3; }
for path in "$kernel/pipeline.c" "$kernel/entry.c" "$kernel/s1_block.c" \
            "$kernel/escape.c" "$kernel/utf8.c" "$kernel/stage2.c" \
            "$here/init_guard_check.c" "$kernel/pipeline.h" "$kernel/entry.h"; do
  [ -e "$path" ] || { printf 'SETUP: absent: %s\n' "$path" >&2; exit 3; }
done

ulimit -c 0 2>/dev/null || true

work=$(mktemp -d "${TMPDIR:-/tmp}/json-init-guard.XXXXXX") || {
  printf 'SETUP: cannot create a work directory\n' >&2; exit 3; }
trap 'rm -rf "$work"' EXIT

# The route's kernel line (`build.sh`'s `kflags`, `OPT` defaulting to -O2).
kflags=(-O2 -march=x86-64-v3 -mpclmul -std=gnu11 -falign-loops=64
        -falign-functions=64 -I "$kernel")
for u in pipeline s1_block entry escape utf8 stage2; do
  if ! "$cc" "${kflags[@]}" -c "$kernel/$u.c" -o "$work/$u.o" \
       2>"$work/build.err"; then
    printf 'SETUP: %s did not compile\n' "$kernel/$u.c" >&2
    awk 'NR <= 40' "$work/build.err" >&2
    exit 3
  fi
done
if ! "$cc" "${kflags[@]}" "$here/init_guard_check.c" \
      "$work/pipeline.o" "$work/s1_block.o" "$work/entry.o" \
      "$work/escape.o" "$work/utf8.o" "$work/stage2.o" \
      -o "$work/init_guard_check" 2>"$work/build.err"; then
  printf 'SETUP: the probe did not build\n' >&2
  awk 'NR <= 40' "$work/build.err" >&2
  exit 3
fi

probe=$work/init_guard_check

"$probe" initialised >"$work/initialised.out" 2>"$work/initialised.err"
initialised_status=$?
"$probe" b8-bare >"$work/b8-bare.out" 2>"$work/b8-bare.err"
b8_bare_status=$?
# Bash prints a job-status line naming the signal ("Illegal instruction") when
# the child traps; that line is the expected SIGILL, and the status captured
# here is the observation.  No core is written (`ulimit -c 0` above).
"$probe" bare >"$work/bare.out" 2>"$work/bare.err"
bare_status=$?

if [ "$initialised_status" -eq 3 ] || [ "$b8_bare_status" -eq 3 ] || \
   [ "$bare_status" -eq 3 ]; then
  printf 'SETUP: the probe reported an allocation failure (status 3):\n' >&2
  cat "$work/initialised.err" "$work/b8-bare.err" "$work/bare.err" >&2
  exit 3
fi

failed=0

# 1. The initialised path: pos8 accepts and writes b8's stream.
if [ "$initialised_status" -ne 0 ]; then
  printf 'FAIL: the initialised pos8 run exited %s:\n' "$initialised_status" >&2
  cat "$work/initialised.out" "$work/initialised.err" >&2
  failed=$((failed + 1))
elif ! grep -Eq '^pos8 verdict=1 nk=[1-9][0-9]* b8 verdict=1 nk=[1-9][0-9]* streams=identical$' \
      "$work/initialised.out"; then
  printf 'FAIL: the initialised pos8 and b8 runs did not agree:\n' >&2
  cat "$work/initialised.out" >&2
  failed=$((failed + 1))
else
  printf 'ok: initialised pos8 and b8 accept and write the same stream: %s\n' \
    "$(cat "$work/initialised.out")"
fi

# 3. The control: b8 needs no table and accepts without one.
if [ "$b8_bare_status" -ne 0 ]; then
  printf 'FAIL: the uninitialised b8 run exited %s:\n' "$b8_bare_status" >&2
  cat "$work/b8-bare.out" "$work/b8-bare.err" >&2
  failed=$((failed + 1))
elif ! grep -Eq '^b8 verdict=1 nk=[1-9][0-9]* err=[0-9]+$' \
      "$work/b8-bare.out"; then
  printf 'FAIL: uninitialised b8 did not accept:\n' >&2
  cat "$work/b8-bare.out" >&2
  failed=$((failed + 1))
else
  printf 'ok: uninitialised b8 accepts (the table is pos8-only): %s\n' \
    "$(cat "$work/b8-bare.out")"
fi

# 2. The red: uninitialised pos8 must not return.  SIGILL (128 + 4) is
#    `__builtin_trap`'s ud2; SIGSEGV (139) would be a different, unexplained
#    fault, and exit 0/1 is the silent wrong answer.
if [ "$bare_status" -eq 132 ]; then
  printf 'ok: uninitialised pos8 trapped (status %s, SIGILL)\n' "$bare_status"
elif [ "$bare_status" -ge 128 ]; then
  printf 'FAIL: uninitialised pos8 died by signal %s, not the trap (status %s):\n' \
    "$((bare_status - 128))" "$bare_status" >&2
  cat "$work/bare.out" "$work/bare.err" >&2
  failed=$((failed + 1))
else
  printf 'FAIL: uninitialised pos8 returned (status %s) instead of trapping:\n' \
    "$bare_status" >&2
  cat "$work/bare.out" "$work/bare.err" >&2
  failed=$((failed + 1))
fi

if [ "$failed" -ne 0 ]; then
  printf 'FAIL: %s assertion(s) failed\n' "$failed" >&2
  exit 1
fi
printf 'ok: the pos8 table must be initialised; without it the emitter traps,\n'
printf '    and the initialised pos8 stream is b8'"'"'s\n'
exit 0
