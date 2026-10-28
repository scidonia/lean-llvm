#!/usr/bin/env bash
# Verify a replacement unit against its manifest and link one body.
#
#   MANIFEST=... OUT=... RECORD=... STRICT=1 ./select.sh
#
# A unit is accepted only when
#   * the manifest names the contract and theorem that cover its fixtures;
#   * every recorded hash matches: caller, unit objects, certificate, and the
#     four fixture inputs (baseline/candidate body and marker);
#   * each unit object is rebuilt from its fixtures and the rebuild matches the
#     installed bytes, so the object is the one the parser pinned;
#   * the target matches, the certificate reports PASS, the objects are ELF64
#     and export the seam and marker symbols, and the caller imports the seam.
#
# STRICT=1 fails instead of falling back to the baseline.
set -euo pipefail

here=$(cd "$(dirname "$0")" && pwd)
manifest=${MANIFEST:-"$here/build/manifest.env"}
out=${OUT:-"$here/build/app"}
record=${RECORD:-"$here/build/selection.env"}
strict=${STRICT:-0}
unit=${UNIT:-}

[ -f "$manifest" ] || { echo "select: no manifest at $manifest" >&2; exit 1; }
# shellcheck disable=SC1090
source "$manifest"

sha() { sha256sum "$1" | cut -d' ' -f1; }
ok=1
reasons=()

check_hash() { # path expected label
  if [ ! -f "$1" ] || [ "$(sha "$1")" != "$2" ]; then
    ok=0
    reasons+=("$3 mismatch")
  fi
}

# Rebuild a unit from its two fixtures under the same basenames `build.sh`
# used.  clang records the module name in the object, so the names are part of
# the input; a different name is a different object even for the same IR.
verify_rebuild() { # unit fixture marker expected
  local unit=$1 fixture=$2 marker=$3 expected=$4 dir got
  command -v clang >/dev/null 2>&1 || return 1
  command -v ld >/dev/null 2>&1 || return 1
  dir=$(mktemp -d) || return 1
  if ! cp "$fixture" "$dir/$unit.ll" ||
     ! cp "$marker" "$dir/marker_$unit.ll"; then
    rm -rf "$dir"
    return 1
  fi
  if ! (cd "$dir" &&
        clang -c "$unit.ll" -o "$unit.o" 2>/dev/null &&
        clang -c "marker_$unit.ll" -o "marker_$unit.o" 2>/dev/null &&
        ld -r "$unit.o" "marker_$unit.o" -o unit.o); then
    rm -rf "$dir"
    return 1
  fi
  got=$(sha "$dir/unit.o")
  rm -rf "$dir"
  [ "$got" = "$expected" ]
}

check_hash "$caller" "$caller_sha256" "caller hash"
check_hash "$baseline" "$baseline_sha256" "baseline hash"
check_hash "$candidate" "$candidate_sha256" "candidate hash"
check_hash "$certificate" "$certificate_sha256" "certificate hash"

check_hash "$baseline_fixture" "$baseline_fixture_sha256" "baseline fixture"
check_hash "$candidate_fixture" "$candidate_fixture_sha256" "candidate fixture"
check_hash "$baseline_marker" "$baseline_marker_sha256" "baseline marker"
check_hash "$candidate_marker" "$candidate_marker_sha256" "candidate marker"

if [ -n "${loop:-}" ]; then
  check_hash "$loop" "$loop_sha256" "loop hash"
  check_hash "$loop_fixture" "$loop_fixture_sha256" "loop fixture"
  check_hash "$loop_marker" "$loop_marker_sha256" "loop marker"
fi

if [ "$kind" != "proof-bound" ]; then
  ok=0; reasons+=("manifest kind $kind")
fi
if [ -z "${contract:-}" ] || [ -z "${theorem:-}" ]; then
  ok=0; reasons+=("manifest does not name a contract and theorem")
fi
if [ "${attributes:-}" != "reject" ]; then
  ok=0; reasons+=("attribute policy ${attributes:-missing}")
fi

if [ "$ok" -eq 1 ]; then
  if ! verify_rebuild baseline "$baseline_fixture" "$baseline_marker" "$baseline_sha256"; then
    ok=0; reasons+=("baseline unit not rebuilt from its fixture")
  fi
  if ! verify_rebuild candidate "$candidate_fixture" "$candidate_marker" "$candidate_sha256"; then
    ok=0; reasons+=("candidate unit not rebuilt from its fixture")
  fi
  if [ -n "${loop:-}" ]; then
    if ! verify_rebuild loop "$loop_fixture" "$loop_marker" "$loop_sha256"; then
      ok=0; reasons+=("loop unit not rebuilt from its fixture")
    fi
  fi
fi

if [ "$(uname -m)-unknown-linux-gnu" != "$target" ]; then
  ok=0; reasons+=("target $target")
fi
if ! grep -q '^RESULT: PASS$' "$certificate" 2>/dev/null; then
  ok=0; reasons+=("certificate result")
fi
if ! file -b "$baseline" 2>/dev/null | grep -q 'ELF 64-bit'; then
  ok=0; reasons+=("baseline is not ELF64")
fi
if ! nm -g "$baseline" 2>/dev/null | grep -q ' T leanllvm_comma_mask8'; then
  ok=0; reasons+=("baseline symbol")
fi
if ! nm -g "$candidate" 2>/dev/null | grep -q ' T leanllvm_comma_mask8'; then
  ok=0; reasons+=("candidate symbol")
fi
if ! nm -g "$candidate" 2>/dev/null | grep -q ' T leanllvm_impl_id'; then
  ok=0; reasons+=("candidate marker")
fi
if [ -n "${loop:-}" ]; then
  if ! file -b "$loop" 2>/dev/null | grep -q 'ELF 64-bit'; then
    ok=0; reasons+=("loop is not ELF64")
  fi
  if ! nm -g "$loop" 2>/dev/null | grep -q ' T leanllvm_comma_mask8'; then
    ok=0; reasons+=("loop symbol")
  fi
  if ! nm -g "$loop" 2>/dev/null | grep -q ' T leanllvm_impl_id'; then
    ok=0; reasons+=("loop marker")
  fi
fi
if ! nm -u "$caller" 2>/dev/null | grep -q 'leanllvm_comma_mask8'; then
  ok=0; reasons+=("caller import")
fi

if [ "$ok" -eq 1 ]; then
  case "$unit" in
    ""|candidate) selected=$candidate; kind=candidate ;;
    baseline) selected=$baseline; kind=baseline ;;
    loop) selected=$loop; kind=loop ;;
    *) ok=0; reasons+=("unknown unit $unit") ;;
  esac
fi
if [ "$ok" -eq 1 ]; then
  reason="hashes, fixtures, rebuild and certificate match"
else
  selected=$baseline
  kind=baseline
  reason=$(IFS='; '; echo "${reasons[*]}")
fi

if [ "$strict" = 1 ] && [ "$ok" -ne 1 ]; then
  printf 'select: strict failure\n' >&2
  printf '  - %s\n' "${reasons[@]}" >&2
  exit 1
fi

leanc "$caller" "$selected" -o "$out" 2>>"$here/build/link.log"

{
  echo "selected=$kind"
  echo "output=$out"
  echo "target=$target"
  echo "contract=$contract"
  echo "theorem=$theorem"
  echo "reason=$reason"
  echo "baseline_fixture_sha256=$baseline_fixture_sha256"
  echo "candidate_fixture_sha256=$candidate_fixture_sha256"
  echo "baseline_sha256=$baseline_sha256"
  echo "candidate_sha256=$candidate_sha256"
  echo "loop_sha256=${loop_sha256:-}"
  echo "certificate_sha256=$certificate_sha256"
} > "$record"

echo "$kind -> $out"
