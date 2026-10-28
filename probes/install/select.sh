#!/usr/bin/env bash
# Verify a replacement unit against its manifest and link one body.
#
#   MANIFEST=... OUT=... RECORD=... STRICT=1 ./select.sh
#
# STRICT=1 fails instead of falling back to the baseline.
set -euo pipefail

here=$(cd "$(dirname "$0")" && pwd)
manifest=${MANIFEST:-"$here/build/manifest.env"}
out=${OUT:-"$here/build/app"}
record=${RECORD:-"$here/build/selection.env"}
strict=${STRICT:-0}

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

check_hash "$caller" "$caller_sha256" "caller hash"
check_hash "$baseline" "$baseline_sha256" "baseline hash"
check_hash "$candidate" "$candidate_sha256" "candidate hash"
check_hash "$certificate" "$certificate_sha256" "certificate hash"

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
if ! nm -u "$caller" 2>/dev/null | grep -q 'leanllvm_comma_mask8'; then
  ok=0; reasons+=("caller import")
fi

if [ "$ok" -eq 1 ]; then
  selected=$candidate
  kind=candidate
  reason="candidate hashes and certificate match"
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
  echo "reason=$reason"
  echo "baseline_sha256=$baseline_sha256"
  echo "candidate_sha256=$candidate_sha256"
  echo "certificate_sha256=$certificate_sha256"
} > "$record"

echo "$kind -> $out"
