#!/usr/bin/env bash
# Checks for the loop installation gate.
#
#   bash tests/m4-loop-gate.sh --strict
#   bash tests/m4-loop-gate.sh --fallback
#   bash tests/m4-loop-gate.sh --strict-conflict
#   bash tests/m4-loop-gate.sh --fallback-conflict
#
# Each mode drives the selector CLI (probes/install/select.sh) against an
# isolated manifest built in a temporary directory.  Only the compiler, linker
# and inspection tools the selector invokes — clang, ld, file, nm and leanc —
# are local shims in a private PATH; the remaining utilities (sha256sum, cut,
# sed and the rest) are the real core utilities, operating on temporary inputs.
# No compiler, linker or service is reached, and nothing outside the temporary
# directory is written.
#
# --strict is G1: a strict loop request must be refused when the manifest's
# theorem covers the candidate only.  --fallback is G2: the same request
# without strict mode must install the recorded baseline.  --strict-conflict is
# G3 and --fallback-conflict is G4: the manifest given to the selector ends
# with assignments that name the caller's own `unit` and `strict` variables,
# and must not change which unit the caller asked for.
#
# Exit status: 0 when the scenario's assertions hold, 1 when one fails,
# 2 on bad usage, 3 when the fixture itself is not usable.
set -uo pipefail

usage() {
  echo "usage: bash tests/m4-loop-gate.sh --strict|--fallback|--strict-conflict|--fallback-conflict" >&2
  exit 2
}

mode=${1:-}
case "$mode" in
  --strict|--fallback|--strict-conflict|--fallback-conflict) ;;
  *) usage ;;
esac
[ "$#" -eq 1 ] || usage

repo=$(cd "$(dirname "$0")/.." && pwd)
selector_source=$repo/probes/install/select.sh
ir=$repo/probes/install/ir

work=$(mktemp -d) || { echo "SETUP: cannot create a temporary directory" >&2; exit 3; }
trap 'rm -rf "$work"' EXIT

fakebin=$work/bin
fixtures=$work/fixtures
units=$work/units
outdir=$work/out
rebuild=$work/rebuild
link_log=$work/link.log
manifest=$work/manifest.env
selector=$work/select.sh
# Exit before the scenario's own assertions if the fixture cannot be built, so
# a construction failure is never read as an assertion result.
trap 'printf "SETUP: fixture construction failed: %s\n" "$BASH_COMMAND" >&2; exit 3' ERR
set -e

mkdir -p "$fakebin" "$fixtures/ir" "$units" "$outdir" "$rebuild" "$work/build"
: > "$link_log"

target=x86_64-unknown-linux-gnu
datalayout='e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128'

{
  printf 'FAKE_TARGET=%q\n' "$target"
  printf 'FAKE_DATALAYOUT=%q\n' "$datalayout"
  printf 'FAKE_LINK_LOG=%q\n' "$link_log"
} > "$fakebin/fake.env"

# --- fake toolchain -------------------------------------------------------
# clang: constant target and data layout, and object bytes fixed by the output
# basename and the bytes of the fixture it compiles.  The object records the
# symbols the unit exports, so nm and the selector's symbol checks observe a
# fixed per-object answer.
cat > "$fakebin/clang" <<'SHIM'
#!/usr/bin/env bash
set -euo pipefail
. "$(dirname "$0")/fake.env"
if [ "${1:-}" = "-print-target-triple" ]; then
  printf '%s\n' "$FAKE_TARGET"
  exit 0
fi
out=
src=
emit_llvm=0
args=("$@")
i=0
while [ "$i" -lt "${#args[@]}" ]; do
  case "${args[i]}" in
    -o) i=$((i + 1)); out=${args[i]} ;;
    -emit-llvm) emit_llvm=1 ;;
    -*) ;;
    *) src=${args[i]} ;;
  esac
  i=$((i + 1))
done
if [ "$emit_llvm" -eq 1 ]; then
  printf 'target datalayout = "%s"\n' "$FAKE_DATALAYOUT"
  exit 0
fi
[ -n "$out" ] || { echo "clang: no output file" >&2; exit 1; }
[ -n "$src" ] && [ -f "$src" ] || { echo "clang: no source file" >&2; exit 1; }
name=$(basename "$out" .o)
digest=$(sha256sum "$src" | cut -d' ' -f1)
{
  printf 'OBJ %s %s\n' "$name" "$digest"
  case "$name" in
    marker_*) printf 'T leanllvm_impl_id\n' ;;
    *) printf 'T leanllvm_comma_mask8\n' ;;
  esac
} > "$out"
SHIM

# ld -r: deterministic combination of the input objects.
cat > "$fakebin/ld" <<'SHIM'
#!/usr/bin/env bash
set -euo pipefail
out=
inputs=()
args=("$@")
i=0
while [ "$i" -lt "${#args[@]}" ]; do
  case "${args[i]}" in
    -o) i=$((i + 1)); out=${args[i]} ;;
    -*) ;;
    *) inputs+=("${args[i]}") ;;
  esac
  i=$((i + 1))
done
[ -n "$out" ] && [ "${#inputs[@]}" -gt 0 ] || { echo "ld: bad invocation" >&2; exit 1; }
{
  printf 'OBJ %s\n' "$(basename "$out" .o)"
  for f in "${inputs[@]}"; do
    sed -n 's/^\([TU] .*\)$/\1/p' "$f"
    sed -n 's/^\(OBJ .*\)$/\1/p' "$f"
  done | LC_ALL=C sort -u
} > "$out"
SHIM

# file: ELF classification for the fake unit objects only.  The answer is one
# line derived from the object's first recorded line, and an early-closed pipe
# is tolerated, so the answer is the same however much the reader consumes.
cat > "$fakebin/file" <<'SHIM'
#!/usr/bin/env bash
set -uo pipefail
trap '' PIPE
path=
for a in "$@"; do
  case "$a" in
    -*) ;;
    *) path=$a ;;
  esac
done
if [ -z "$path" ] || [ ! -f "$path" ]; then
  echo "cannot open $path" >&2
  exit 1
fi
first=
IFS= read -r first < "$path" || true
case "$first" in
  'OBJ '*) answer='ELF 64-bit LSB relocatable, x86-64, version 1 (SYSV)' ;;
  *) answer='ASCII text' ;;
esac
printf '%s\n' "$answer" || true
exit 0
SHIM

# nm: fixed per-object exports and caller imports.  The lines are derived from
# the symbols the object holds, and an early-closed pipe is tolerated, so the
# symbol answer is the same however much the reader consumes.
cat > "$fakebin/nm" <<'SHIM'
#!/usr/bin/env bash
set -uo pipefail
trap '' PIPE
mode=
path=
for a in "$@"; do
  case "$a" in
    -u) mode=u ;;
    -g) mode=g ;;
    -*) ;;
    *) path=$a ;;
  esac
done
if [ -z "$path" ] || [ ! -f "$path" ]; then
  echo "nm: no file" >&2
  exit 1
fi
addr=0
while IFS= read -r line; do
  case "$line" in
    'OBJ '*) ;;
    'T '*) [ "$mode" = u ] || printf '%016x T %s\n' "$addr" "${line#T }" ;;
    'U '*) [ "$mode" = g ] || printf '%016x U %s\n' "$addr" "${line#U }" ;;
  esac
  addr=$((addr + 16))
done < "$path" || true
exit 0
SHIM

# leanc: records the exact objects it was asked to link and writes the output.
cat > "$fakebin/leanc" <<'SHIM'
#!/usr/bin/env bash
set -euo pipefail
. "$(dirname "$0")/fake.env"
out=
expect_out=0
args=()
for a in "$@"; do
  if [ "$expect_out" -eq 1 ]; then
    out=$a
    expect_out=0
    continue
  fi
  case "$a" in
    -o) expect_out=1 ;;
    -*) ;;
    *) args+=("$a") ;;
  esac
done
[ -n "$out" ] || { echo "leanc: no output file" >&2; exit 1; }
{
  printf '%s' "$out"
  printf '\t%s' "${args[@]}"
  printf '\n'
} >> "$FAKE_LINK_LOG"
{
  printf '#!/bin/sh\n'
  printf 'LINKED_OBJECTS=%s\n' "${args[*]}"
} > "$out"
chmod +x "$out"
SHIM

chmod +x "$fakebin/clang" "$fakebin/ld" "$fakebin/file" "$fakebin/nm" \
  "$fakebin/leanc"
PATH="$fakebin:$PATH"
export PATH

# --- fixtures -------------------------------------------------------------
# The unit IR is the repository's fixture, copied; each object is built with
# the same basenames and command sequence `build.sh` uses, so the manifest
# values are computed from the fixture bytes and from what the selector will
# rebuild, never typed by hand.
for unit in baseline candidate loop; do
  cp "$ir/$unit.ll" "$fixtures/ir/$unit.ll"
  cp "$ir/marker_$unit.ll" "$fixtures/ir/marker_$unit.ll"
  mkdir -p "$units/$unit"
  cp "$fixtures/ir/$unit.ll" "$units/$unit/$unit.ll"
  cp "$fixtures/ir/marker_$unit.ll" "$units/$unit/marker_$unit.ll"
  (cd "$units/$unit" &&
    clang -c "$unit.ll" -o "$unit.o" &&
    clang -c "marker_$unit.ll" -o "marker_$unit.o" &&
    ld -r "$unit.o" "marker_$unit.o" -o unit.o)
  cp "$units/$unit/unit.o" "$fixtures/$unit.o"
done

printf 'OBJ caller\nU leanllvm_comma_mask8\n' > "$fixtures/caller.o"

cat > "$fixtures/differential.txt" <<'CERT'
kind: differential
symbol: leanllvm_comma_mask8
bodies: proved-baseline proved-candidate proved-loop lean-baseline lean-candidate
theorem: LeanLLVM.Vellum.CommaMaskIR.IR_refines
covers: candidate-vs-baseline
RESULT: PASS
CERT

# The loop object must be exactly what a rebuild from its own fixture produces
# with the same tools: otherwise the selector's own rebuild check would reject
# the loop and the scenario would observe a fixture failure instead of the
# selection rule under test.
cp "$fixtures/ir/loop.ll" "$rebuild/loop.ll"
cp "$fixtures/ir/marker_loop.ll" "$rebuild/marker_loop.ll"
(cd "$rebuild" &&
  clang -c loop.ll -o loop.o &&
  clang -c marker_loop.ll -o marker_loop.o &&
  ld -r loop.o marker_loop.o -o unit.o)
if ! cmp -s "$rebuild/unit.o" "$fixtures/loop.o"; then
  echo "SETUP: the installed loop object is not the rebuild of its fixture" >&2
  exit 3
fi

sha() { sha256sum "$1" | cut -d' ' -f1; }

cat > "$manifest" <<EOF
kind=proof-bound
target=$target
triple=$target
symbol=leanllvm_comma_mask8
marker=leanllvm_impl_id
contract=LeanLLVM.Vellum.commaContract
theorem=LeanLLVM.Vellum.CommaMaskIR.IR_refines
attributes=reject
datalayout=$datalayout
target_features=none
baseline_fixture=$fixtures/ir/baseline.ll
candidate_fixture=$fixtures/ir/candidate.ll
loop_fixture=$fixtures/ir/loop.ll
baseline_marker=$fixtures/ir/marker_baseline.ll
candidate_marker=$fixtures/ir/marker_candidate.ll
loop_marker=$fixtures/ir/marker_loop.ll
baseline_fixture_sha256=$(sha "$fixtures/ir/baseline.ll")
candidate_fixture_sha256=$(sha "$fixtures/ir/candidate.ll")
loop_fixture_sha256=$(sha "$fixtures/ir/loop.ll")
baseline_marker_sha256=$(sha "$fixtures/ir/marker_baseline.ll")
candidate_marker_sha256=$(sha "$fixtures/ir/marker_candidate.ll")
loop_marker_sha256=$(sha "$fixtures/ir/marker_loop.ll")
caller=$fixtures/caller.o
baseline=$fixtures/baseline.o
candidate=$fixtures/candidate.o
loop=$fixtures/loop.o
certificate=$fixtures/differential.txt
caller_sha256=$(sha "$fixtures/caller.o")
baseline_sha256=$(sha "$fixtures/baseline.o")
candidate_sha256=$(sha "$fixtures/candidate.o")
loop_sha256=$(sha "$fixtures/loop.o")
certificate_sha256=$(sha "$fixtures/differential.txt")
EOF

# The conflict manifest repeats the clean manifest and ends with assignments
# that name the caller's own `unit` and `strict` variables.  The selector reads
# the request before it sources a manifest, so these lines must not reach the
# selection.
conflict_manifest=$work/manifest-conflict.env
cp "$manifest" "$conflict_manifest"
cat >> "$conflict_manifest" <<'CONFLICT'
unit=candidate
strict=0
CONFLICT

# The selector is run as the build integrator runs it: its copy lives beside
# an empty build directory so its relative link log stays inside the fixture.
cp "$selector_source" "$selector"
chmod +x "$selector"

set +e
trap - ERR

# --- assertions -----------------------------------------------------------
fails=0
ok() { printf 'ok: %s\n' "$*"; }
bad() { printf 'FAIL: %s\n' "$*" >&2; fails=$((fails + 1)); }

# The object the leanc shim was given for a particular output, empty when no
# link was attempted for it.
link_target() { # out
  local want=$1 lout larg1 larg2 found=
  if [ -f "$link_log" ]; then
    while IFS=$'\t' read -r lout larg1 larg2; do
      if [ "$lout" = "$want" ]; then
        found=$larg2
      fi
    done < "$link_log"
  fi
  printf '%s' "$found"
}

# --- affirmative control --------------------------------------------------
# A baseline selection from the same input must link the baseline object and
# leave an output at the requested path, so the fake link and output detection
# is known to work before the same detector is used to judge the loop.
control_out=$outdir/control
control_record=$work/control.env
control_status=0
UNIT=baseline STRICT=1 MANIFEST="$manifest" OUT="$control_out" \
  RECORD="$control_record" "$selector" \
  >"$work/control.stdout" 2>"$work/control.stderr" || control_status=$?
control_selected=$(sed -n 's/^selected=//p' "$control_record" 2>/dev/null || true)
control_linked=$(link_target "$control_out")

if [ "$control_status" -eq 0 ] &&
   [ "$control_selected" = baseline ] &&
   [ -e "$control_out" ] &&
   [ "$control_linked" = "$fixtures/baseline.o" ]; then
  ok "control: a strict baseline selection exited 0, linked the baseline object and emitted an output file"
else
  echo "SETUP: baseline control failed (status $control_status, selected '$control_selected', linked '$control_linked')" >&2
  sed 's/^/  selector stderr: /' "$work/control.stderr" >&2
  exit 3
fi

if [ "$mode" = --strict ]; then
  # --- G1 ----------------------------------------------------------------
  strict_out=$outdir/strict
  strict_record=$work/strict.env
  rm -f "$strict_out" "$strict_record"
  strict_status=0
  UNIT=loop STRICT=1 MANIFEST="$manifest" OUT="$strict_out" \
    RECORD="$strict_record" "$selector" \
    >"$work/strict.stdout" 2>"$work/strict.stderr" || strict_status=$?

  if [ "$strict_status" -ne 0 ]; then
    ok "G1: the strict loop request was refused with status $strict_status"
  else
    bad "G1: the strict loop request exited 0, so a unit with no loop theorem was accepted"
  fi

  if [ ! -e "$strict_out" ]; then
    ok "G1: no loop executable was emitted"
  else
    bad "G1: a loop executable was emitted at $strict_out"
  fi

  if [ -f "$strict_record" ] && grep -qx 'selected=loop' "$strict_record"; then
    bad "G1: the selection record names the loop"
  else
    ok "G1: the selection record does not name the loop"
  fi

  printf 'selector stdout: %s\n' "$(cat "$work/strict.stdout")"
  sed 's/^/selector stderr: /' "$work/strict.stderr"
  if [ -f "$strict_record" ]; then
    printf 'selection record: %s\n' "$(tr '\n' ';' < "$strict_record")"
  fi
elif [ "$mode" = --fallback ]; then
  # --- G2 ----------------------------------------------------------------
  fallback_out=$outdir/fallback
  fallback_record=$work/fallback.env
  rm -f "$fallback_out" "$fallback_record"
  fallback_status=0
  UNIT=loop STRICT=0 MANIFEST="$manifest" OUT="$fallback_out" \
    RECORD="$fallback_record" "$selector" \
    >"$work/fallback.stdout" 2>"$work/fallback.stderr" || fallback_status=$?

  if [ "$fallback_status" -eq 0 ]; then
    ok "G2: the non-strict loop request exited 0"
  else
    bad "G2: the non-strict loop request exited $fallback_status"
  fi

  selected=$(sed -n 's/^selected=//p' "$fallback_record" 2>/dev/null || true)
  case "$selected" in
    baseline) expected=$fixtures/baseline.o ;;
    candidate) expected=$fixtures/candidate.o ;;
    loop) expected=$fixtures/loop.o ;;
    *) expected= ;;
  esac
  linked=$(link_target "$fallback_out")

  if [ "$selected" = baseline ]; then
    ok "G2: the selection record names the baseline"
  else
    bad "G2: the selection record names '${selected:-nothing}'"
  fi

  if [ -n "$expected" ] && [ "$linked" = "$expected" ]; then
    ok "G2: the linker was given the object of the recorded unit ($selected)"
  else
    bad "G2: the record names '${selected:-nothing}' but the linker was given '${linked:-nothing}'"
  fi

  if [ "$linked" != "$fixtures/loop.o" ]; then
    ok "G2: the linked object is not the loop"
  else
    bad "G2: the linked object is the loop"
  fi

  printf 'selector stdout: %s\n' "$(cat "$work/fallback.stdout")"
  sed 's/^/selector stderr: /' "$work/fallback.stderr"
  if [ -f "$fallback_record" ]; then
    printf 'selection record: %s\n' "$(tr '\n' ';' < "$fallback_record")"
  fi
elif [ "$mode" = --strict-conflict ]; then
  # --- G3 ----------------------------------------------------------------
  # The caller asks for the loop in strict mode.  The manifest ends with
  # assignments that name the caller's own variables and would substitute the
  # candidate were they to reach the selection.
  conflict_out=$outdir/strict-conflict
  conflict_record=$work/strict-conflict.env
  rm -f "$conflict_out" "$conflict_record"
  conflict_status=0
  UNIT=loop STRICT=1 MANIFEST="$conflict_manifest" OUT="$conflict_out" \
    RECORD="$conflict_record" "$selector" \
    >"$work/strict-conflict.stdout" 2>"$work/strict-conflict.stderr" || conflict_status=$?

  if [ "$conflict_status" -ne 0 ]; then
    ok "G3: the conflicting strict loop request was refused with status $conflict_status"
  else
    bad "G3: the conflicting strict loop request exited 0, so the manifest chose the unit"
  fi

  if [ ! -e "$conflict_out" ]; then
    ok "G3: no executable was emitted"
  else
    bad "G3: an executable was emitted at $conflict_out"
  fi

  conflict_selected=$(sed -n 's/^selected=//p' "$conflict_record" 2>/dev/null || true)
  case "$conflict_selected" in
    candidate) bad "G3: the selection record names the candidate the manifest substituted" ;;
    loop) bad "G3: the selection record names the loop" ;;
    *) ok "G3: no selection record names the candidate or the loop" ;;
  esac

  printf 'selector stdout: %s\n' "$(cat "$work/strict-conflict.stdout")"
  sed 's/^/selector stderr: /' "$work/strict-conflict.stderr"
  if [ -f "$conflict_record" ]; then
    printf 'selection record: %s\n' "$(tr '\n' ';' < "$conflict_record")"
  fi
else
  # --- G4 ----------------------------------------------------------------
  # The same conflicting manifest, with the caller asking for the loop without
  # strict mode: the loop has no covering theorem, so the selection must fall
  # back to the baseline rather than to the substituted candidate.
  conflict_out=$outdir/fallback-conflict
  conflict_record=$work/fallback-conflict.env
  rm -f "$conflict_out" "$conflict_record"
  conflict_status=0
  UNIT=loop STRICT=0 MANIFEST="$conflict_manifest" OUT="$conflict_out" \
    RECORD="$conflict_record" "$selector" \
    >"$work/fallback-conflict.stdout" 2>"$work/fallback-conflict.stderr" || conflict_status=$?

  if [ "$conflict_status" -eq 0 ]; then
    ok "G4: the conflicting non-strict loop request exited 0"
  else
    bad "G4: the conflicting non-strict loop request exited $conflict_status"
  fi

  conflict_selected=$(sed -n 's/^selected=//p' "$conflict_record" 2>/dev/null || true)
  case "$conflict_selected" in
    baseline) expected=$fixtures/baseline.o ;;
    candidate) expected=$fixtures/candidate.o ;;
    loop) expected=$fixtures/loop.o ;;
    *) expected= ;;
  esac
  linked=$(link_target "$conflict_out")

  if [ "$conflict_selected" = baseline ]; then
    ok "G4: the selection record names the baseline"
  else
    bad "G4: the selection record names '${conflict_selected:-nothing}'"
  fi

  if [ -n "$expected" ] && [ "$linked" = "$expected" ]; then
    ok "G4: the linker was given the object of the recorded unit ($conflict_selected)"
  else
    bad "G4: the record names '${conflict_selected:-nothing}' but the linker was given '${linked:-nothing}'"
  fi

  if [ "$linked" = "$fixtures/baseline.o" ]; then
    ok "G4: the linked object is the baseline fixture"
  else
    bad "G4: the linked object is '${linked:-nothing}', not the baseline fixture"
  fi

  printf 'selector stdout: %s\n' "$(cat "$work/fallback-conflict.stdout")"
  sed 's/^/selector stderr: /' "$work/fallback-conflict.stderr"
  if [ -f "$conflict_record" ]; then
    printf 'selection record: %s\n' "$(tr '\n' ';' < "$conflict_record")"
  fi
fi

if [ "$fails" -ne 0 ]; then
  printf '%d assertion(s) failed\n' "$fails" >&2
  exit 1
fi
printf 'all assertions held\n'
