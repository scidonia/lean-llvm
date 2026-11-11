#!/usr/bin/env bash
# Checks for the json_scan selection route.
#
#   bash tests/json-scan-select-gate.sh --strict
#   bash tests/json-scan-select-gate.sh --fallback
#
# Each mode drives the selector CLI (probes/install/select.sh) against an
# isolated manifest built in a temporary directory.  The tools the selector
# invokes are local shims in a private PATH: clang, ld, file, nm and leanc;
# lean, which answers `--version` only; and lake, which accepts the proof-module
# rebuild and the certificate producer, and nothing else.  The remaining
# utilities (sha256sum, cut, sed and the rest) are the real core utilities,
# operating on temporary inputs.  The temporary tree mirrors the repository root
# the selector resolves the revision-bearing pin files from.  No compiler,
# linker, proof checker or service is reached, and nothing outside the temporary
# directory is written.
#
# Every mode first makes a strict baseline selection from the same input and
# asserts that it exits 0, links the baseline object and emits an app, so a
# working link and a detectable output are known before the same detectors are
# used to judge the JSON unit.
#
# --strict is JS1 and JS2.  JS1 is a strict `json_scan` request whose certificate
# names the unit's own theorem and contract, its own hashes and the observed
# toolchain: it must install the unit, record the certificate's own digest, and
# hand the linker the unit's object.  JS2 then changes the certificate's
# `theorem` field to `IR_refines`, the candidate-to-baseline statement, rewrites
# the manifest's digest of the certificate to the changed bytes, and requires
# the request to be refused with the certificate reason.
#
# --fallback is JS3: the JS2 certificate with `STRICT=0` must install the
# baseline and record the rejection as the invalid-certificate fallback.
#
# The value the unit's body computes is deliberately not asserted here: a number
# written by this test's own fixture and echoed by its own linker shim would be
# the fixture's claim, not the body's.  The emitted body's agreement with the
# model is checked by the separate body-vs-model route over real windows.
#
# Exit status: 0 when the scenario's assertions hold, 1 when one fails, 2 on bad
# usage, 3 when the fixture itself is not usable.
set -uo pipefail

usage() {
  cat >&2 <<'USAGE'
usage: bash tests/json-scan-select-gate.sh --strict
       bash tests/json-scan-select-gate.sh --fallback
USAGE
  exit 2
}

mode=${1:-}
case "$mode" in
  --strict|--fallback) ;;
  *) usage ;;
esac
[ "$#" -eq 1 ] || usage

repo=$(cd "$(dirname "$0")/.." && pwd)
selector_source=$repo/probes/install/select.sh
ir=$repo/probes/install/ir
for path in "$selector_source" "$ir/baseline.ll" "$ir/candidate.ll" \
  "$ir/marker_baseline.ll" "$ir/marker_candidate.ll" \
  "$repo/probes/install/InstallCertificate.lean" \
  "$repo/probes/install/toolchain-id.sh" \
  "$repo/lean-toolchain" "$repo/flake.nix" "$repo/flake.lock" \
  "$repo/lakefile.toml" "$repo/lake-manifest.json"; do
  [ -e "$path" ] || { printf 'SETUP: absent: %s\n' "$path" >&2; exit 3; }
done

work=$(mktemp -d) || { echo "SETUP: cannot create a temporary directory" >&2; exit 3; }
trap 'rm -rf "$work"' EXIT

fakebin=$work/bin
fixtures=$work/fixtures
units=$work/units
outdir=$work/out
rebuild=$work/rebuild
proofs=$work/proofs
canonical=$work/canonical
mirror=$work
link_log=$work/link.log
manifest=$work/manifest.env
selector=$mirror/probes/install/select.sh
# Exit before the scenario's own assertions if the fixture cannot be built, so a
# construction failure is never read as an assertion result.
trap 'printf "SETUP: fixture construction failed: %s\n" "$BASH_COMMAND" >&2; exit 3' ERR
set -e

mkdir -p "$fakebin" "$fixtures/ir" "$units" "$outdir" "$rebuild" "$proofs" \
  "$canonical" "$mirror/probes/install/build" \
  "$mirror/.lake/build/lib/lean/LeanLLVM/Refinement"
: > "$link_log"

target=x86_64-unknown-linux-gnu
datalayout='e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128'

{
  printf 'FAKE_TARGET=%q\n' "$target"
  printf 'FAKE_DATALAYOUT=%q\n' "$datalayout"
  printf 'FAKE_LINK_LOG=%q\n' "$link_log"
  printf 'FAKE_CANONICAL_DIR=%q\n' "$canonical"
} > "$fakebin/fake.env"

# --- fake toolchain -------------------------------------------------------
# clang: constant target and data layout, and object bytes fixed by the output
# basename and the bytes of the fixture it compiles.  The object records the
# symbol the fixture defines, so nm and the selector's symbol checks observe a
# fixed per-fixture answer.  Nothing about the body's value is recorded: the
# body's result is not this route's observable.
cat > "$fakebin/clang" <<'SHIM'
#!/usr/bin/env bash
set -euo pipefail
. "$(dirname "$0")/fake.env"
if [ "${1:-}" = "-print-target-triple" ]; then
  printf '%s\n' "$FAKE_TARGET"
  exit 0
fi
if [ "${1:-}" = "--version" ]; then
  printf 'clang version 18.1.8\n'
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
symbol=$(sed -n 's/^define [^@]*@\([A-Za-z0-9_]*\)(.*/\1/p' "$src" | sed -n '1p')
[ -n "$symbol" ] || { echo "clang: no function definition in $src" >&2; exit 1; }
{
  printf 'OBJ %s %s\n' "$name" "$(sha256sum "$src" | cut -d' ' -f1)"
  printf 'T %s\n' "$symbol"
} > "$out"
SHIM

# ld -r: deterministic combination of the input objects, and a version answer
# for the toolchain revision.
cat > "$fakebin/ld" <<'SHIM'
#!/usr/bin/env bash
set -euo pipefail
if [ "${1:-}" = "--version" ]; then
  printf 'GNU ld (GNU Binutils) 2.42\n'
  exit 0
fi
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
    sed -n -e 's/^\([TU] .*\)$/\1/p' -e 's/^\(OBJ .*\)$/\1/p' "$f"
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

# nm: the symbols the object records, as exports or imports.  The lines are
# derived from the object, and an early-closed pipe is tolerated, so the symbol
# answer is the same however much the reader consumes.
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

# leanc: records the exact objects it was asked to link and writes an app at the
# requested path.  What the app computes is not this route's observable; the
# route asserts which object the linker was handed and that the selection's
# output was emitted.
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
  printf 'exit 0\n'
} > "$out"
chmod +x "$out"
SHIM

# lean: a version answer only, for the toolchain revision record.
cat > "$fakebin/lean" <<'SHIM'
#!/usr/bin/env bash
set -euo pipefail
if [ "$#" -eq 1 ] && [ "${1:-}" = "--version" ]; then
  printf 'Lean (version 4.36.0-rc1, Release)\n'
  exit 0
fi
echo "lean: unexpected invocation: $*" >&2
exit 1
SHIM

# lake: the proof checker the selector drives.  Two command forms are accepted:
# the rebuild of the proof module the route re-elaborates after removing its
# olean, whichever module that is; and the certificate producer, which publishes
# the canonical certificate of the requested unit derived from the manifest
# inputs.  The rebuild is accepted unconditionally, so the gate is observed
# through the certificate and not through a stale import.  Any other invocation
# is refused.
cat > "$fakebin/lake" <<'SHIM'
#!/usr/bin/env bash
set -euo pipefail
. "$(dirname "$0")/fake.env"
if [ "${1:-}" = build ]; then
  [ "$#" -eq 2 ] ||
    { echo "lake: unexpected build arguments: $*" >&2; exit 1; }
  case "$2" in
    LeanLLVM.*) exit 0 ;;
    *) echo "lake: unexpected build target: $2" >&2; exit 1 ;;
  esac
fi
[ "${1:-}" = env ] && [ "${2:-}" = lean ] ||
  { echo "lake: only 'lake build' and 'lake env lean' are supported" >&2; exit 1; }
shift 2
[ "$#" -eq 1 ] && [ "$1" = probes/install/InstallCertificate.lean ] ||
  { echo "lake: unexpected producer arguments: $*" >&2; exit 1; }
case "${CERT_UNIT:-}" in
  baseline|candidate|json_scan) cert_unit=$CERT_UNIT ;;
  *) echo "lake: CERT_UNIT must name baseline, candidate or json_scan" >&2; exit 1 ;;
esac
case "${CERT_MANIFEST:-}" in
  /*) ;;
  *) echo "lake: CERT_MANIFEST must be an absolute path" >&2; exit 1 ;;
esac
case "${CERT_OUT:-}" in
  /*) ;;
  *) echo "lake: CERT_OUT must be an absolute path" >&2; exit 1 ;;
esac
[ -f "$CERT_MANIFEST" ] || { echo "lake: no manifest at $CERT_MANIFEST" >&2; exit 1; }
cp "$FAKE_CANONICAL_DIR/$cert_unit.env" "$CERT_OUT"
SHIM

chmod +x "$fakebin/clang" "$fakebin/ld" "$fakebin/file" "$fakebin/nm" \
  "$fakebin/leanc" "$fakebin/lean" "$fakebin/lake"
PATH="$fakebin:$PATH"
export PATH

# The temporary tree mirrors the repository root the selector resolves: the
# revision-bearing pin files, the selector at probes/install/select.sh, the
# producer, the toolchain helper and the project olean directory the selector
# rebuilds the proof module in.
for pinned in lean-toolchain flake.nix flake.lock lakefile.toml \
  lake-manifest.json; do
  cp "$repo/$pinned" "$mirror/$pinned"
done
cp "$selector_source" "$selector"
chmod +x "$selector"
cp "$repo/probes/install/InstallCertificate.lean" \
  "$mirror/probes/install/InstallCertificate.lean"
cp "$repo/probes/install/toolchain-id.sh" \
  "$mirror/probes/install/toolchain-id.sh"
chmod +x "$mirror/probes/install/toolchain-id.sh"

# --- fixtures -------------------------------------------------------------
sha() { sha256sum "$1" | cut -d' ' -f1; }

# The stand-in window body for the selector route: it declares the unit's symbol
# and returns a constant.  No assertion depends on that constant; the stand-in
# is scaffolding, and the emitted body's agreement with the model is checked by
# the separate body-vs-model route.
cat > "$fixtures/ir/json_scan.ll" <<'LL'
; The json_scan window body stand-in for the selector route.  It declares the
; unit's symbol; the value it returns is not this route's observable.
define i32 @leanllvm_json_scan_window(ptr %arg) {
bb:
  ret i32 0
}
LL

cat > "$fixtures/ir/marker_json_scan.ll" <<'LL'
define i64 @leanllvm_impl_id(i64 %dummy) {
bb:
  ret i64 0
}
LL

# The baseline and candidate units are the repository's fixtures, copied; each
# object is built with the same basenames and command sequence `build.sh` uses,
# so the manifest values are computed from the fixture bytes and from what the
# selector will rebuild, never typed by hand.  The JSON unit is built the same
# way from its stand-in fixtures.
for unit in baseline candidate json_scan; do
  if [ "$unit" != json_scan ]; then
    cp "$ir/$unit.ll" "$fixtures/ir/$unit.ll"
    cp "$ir/marker_$unit.ll" "$fixtures/ir/marker_$unit.ll"
  fi
  mkdir -p "$units/$unit"
  cp "$fixtures/ir/$unit.ll" "$units/$unit/$unit.ll"
  cp "$fixtures/ir/marker_$unit.ll" "$units/$unit/marker_$unit.ll"
  (cd "$units/$unit" &&
    clang -c "$unit.ll" -o "$unit.o" &&
    clang -c "marker_$unit.ll" -o "marker_$unit.o" &&
    ld -r "$unit.o" "marker_$unit.o" -o unit.o)
  cp "$units/$unit/unit.o" "$fixtures/$unit.o"
done

printf 'OBJ caller\nU leanllvm_comma_mask8\nU leanllvm_json_scan_window\n' \
  > "$fixtures/caller.o"

cat > "$fixtures/differential.txt" <<'CERT'
kind: differential
symbol: leanllvm_json_scan_window
bodies: proved-baseline proved-candidate stand-in-json_scan
covers: candidate-vs-baseline, json_scan-vs-baseline
not-covered: none
RESULT: PASS
CERT

# The JSON unit's object must be exactly what a rebuild from its own fixture
# produces with the same tools: otherwise the selector's own rebuild check would
# reject the unit and the scenario would observe a fixture failure instead of
# the rule under test.
cp "$fixtures/ir/json_scan.ll" "$rebuild/json_scan.ll"
cp "$fixtures/ir/marker_json_scan.ll" "$rebuild/marker_json_scan.ll"
(cd "$rebuild" &&
  clang -c json_scan.ll -o json_scan.o &&
  clang -c marker_json_scan.ll -o marker_json_scan.o &&
  ld -r json_scan.o marker_json_scan.o -o unit.o)
if ! cmp -s "$rebuild/unit.o" "$fixtures/json_scan.o"; then
  echo "SETUP: the installed json_scan object is not the rebuild of its fixture" >&2
  exit 3
fi

# The certificate's field values are derived from the files the manifest names,
# from the toolchain the selector observes and from the pinned proof data, so a
# fixture value cannot silently disagree with the input it claims.  Each
# certificate carries the checked axiom set of the theorem it names: the pin
# under LeanLLVMTest/ when the theorem is pinned, and otherwise the selector's
# one checked set, read from the selector rather than retyped.
pinned_axioms() { # theorem short name
  sed -n "s/.*'LeanLLVM\.[A-Za-z0-9_.]*\.$1' depends on axioms: \[\([^]]*\)\].*/\1/p" \
    "$repo"/LeanLLVMTest/*.lean |
    tr ',' '\n' | sed 's/^ *//; s/ *$//' | grep -v '^$' |
    LC_ALL=C sort | paste -sd, -
}
selector_axioms() {
  sed -n 's/^expected_axioms=//p' "$selector_source" | sed -n '1p'
}
certificate_axioms() { # theorem short name
  local axioms
  axioms=$(pinned_axioms "$1")
  [ -n "$axioms" ] || axioms=$(selector_axioms)
  printf '%s' "$axioms"
}
# The toolchain revision is the SHA-256 of a fixed nine-line record: a header,
# then the digest of each revision-bearing pin file and of each version
# command's stdout, in that order, every line terminated by one LF.  A single
# component change changes the digest.
hash_bytes() { sha256sum "$1" | cut -d' ' -f1; }
hash_stdout() { LC_ALL=C "$@" | sha256sum | cut -d' ' -f1; }
toolchain_record() {
  printf 'leanllvm-toolchain-v1\n'
  printf 'lean-toolchain=%s\n' "$(hash_bytes "$mirror/lean-toolchain")"
  printf 'flake-nix=%s\n' "$(hash_bytes "$mirror/flake.nix")"
  printf 'flake-lock=%s\n' "$(hash_bytes "$mirror/flake.lock")"
  printf 'lakefile=%s\n' "$(hash_bytes "$mirror/lakefile.toml")"
  printf 'lake-manifest=%s\n' "$(hash_bytes "$mirror/lake-manifest.json")"
  printf 'lean-version=%s\n' "$(hash_stdout lean --version)"
  printf 'clang-version=%s\n' "$(hash_stdout clang --version)"
  printf 'ld-version=%s\n' "$(hash_stdout ld --version)"
}
toolchain_revision="sha256:$(toolchain_record | sha256sum | cut -d' ' -f1)"
if ! printf '%s' "$toolchain_revision" | grep -Eq '^sha256:[0-9a-f]{64}$'; then
  echo "SETUP: cannot compute the toolchain revision" >&2
  exit 3
fi
helper_revision=$(cd "$mirror" && bash "$mirror/probes/install/toolchain-id.sh")
if [ "$helper_revision" != "$toolchain_revision" ]; then
  echo "SETUP: the toolchain helper and the artifact's toolchain revision disagree" >&2
  exit 3
fi
schema_version=leanllvm-install-v1

# The manifest binds the JSON unit's own theorem and contract beside the global
# comma pair, which keeps naming the candidate-to-baseline statement and the
# comma seam for the baseline and the candidate.
cat > "$manifest" <<EOF
kind=proof-bound
target=$target
triple=$target
symbol=leanllvm_comma_mask8
marker=leanllvm_impl_id
contract=LeanLLVM.Refinement.commaContract
theorem=LeanLLVM.Refinement.CommaMaskIR.IR_refines
json_scan_symbol=leanllvm_json_scan_window
json_scan_theorem=LeanLLVM.Refinement.JsonScanIR.scanWindowLLVM_refines
json_scan_contract=LeanLLVM.Refinement.JsonScanABI.jsonScanContract
attributes=reject
datalayout=$datalayout
target_features=none
baseline_fixture=$fixtures/ir/baseline.ll
candidate_fixture=$fixtures/ir/candidate.ll
json_scan_fixture=$fixtures/ir/json_scan.ll
baseline_marker=$fixtures/ir/marker_baseline.ll
candidate_marker=$fixtures/ir/marker_candidate.ll
json_scan_marker=$fixtures/ir/marker_json_scan.ll
baseline_fixture_sha256=$(sha "$fixtures/ir/baseline.ll")
candidate_fixture_sha256=$(sha "$fixtures/ir/candidate.ll")
json_scan_fixture_sha256=$(sha "$fixtures/ir/json_scan.ll")
baseline_marker_sha256=$(sha "$fixtures/ir/marker_baseline.ll")
candidate_marker_sha256=$(sha "$fixtures/ir/marker_candidate.ll")
json_scan_marker_sha256=$(sha "$fixtures/ir/marker_json_scan.ll")
caller=$fixtures/caller.o
baseline=$fixtures/baseline.o
candidate=$fixtures/candidate.o
json_scan=$fixtures/json_scan.o
differential=$fixtures/differential.txt
caller_sha256=$(sha "$fixtures/caller.o")
baseline_sha256=$(sha "$fixtures/baseline.o")
candidate_sha256=$(sha "$fixtures/candidate.o")
json_scan_sha256=$(sha "$fixtures/json_scan.o")
differential_sha256=$(sha "$fixtures/differential.txt")
EOF

proof_baseline=$proofs/proof_baseline.env
proof_candidate=$proofs/proof_candidate.env
proof_json_scan=$proofs/proof_json_scan.env
{
  printf 'proof_baseline=%s\n' "$proof_baseline"
  printf 'proof_candidate=%s\n' "$proof_candidate"
  printf 'proof_json_scan=%s\n' "$proof_json_scan"
} >> "$manifest"

manifest_value() { # key
  sed -n "s/^$1=//p" "$manifest" | sed -n '1p'
}

# The certificate a unit's producer publishes: every field derived from the file
# or input the field names.  The theorem and the contract are the ones bound to
# that unit in the manifest, and the axiom set is that theorem's checked
# footprint.
write_certificate() { # path artifact-unit certificate-unit theorem-key contract-key
  local path=$1 art_unit=$2 cert_unit=$3 theorem_key=$4 contract_key=$5 axioms_value
  axioms_value=$(certificate_axioms \
    "$(manifest_value "$theorem_key" | sed 's/.*\.//')")
  if ! printf '%s' "$axioms_value" |
       grep -Eq '^[A-Za-z0-9_.]+(,[A-Za-z0-9_.]+)*$'; then
    echo "SETUP: cannot read the axiom set for $art_unit" >&2
    exit 3
  fi
  {
    printf 'schema=%s\n' "$schema_version"
    printf 'unit=%s\n' "$cert_unit"
    printf 'unit_object_sha256=%s\n' "$(sha "$(manifest_value "$art_unit")")"
    printf 'unit_fixture_sha256=%s\n' \
      "$(sha "$(manifest_value "${art_unit}_fixture")")"
    printf 'unit_marker_sha256=%s\n' \
      "$(sha "$(manifest_value "${art_unit}_marker")")"
    printf 'baseline_object_sha256=%s\n' "$(sha "$(manifest_value baseline)")"
    printf 'candidate_object_sha256=%s\n' "$(sha "$(manifest_value candidate)")"
    printf 'baseline_fixture_sha256=%s\n' \
      "$(sha "$(manifest_value baseline_fixture)")"
    printf 'candidate_fixture_sha256=%s\n' \
      "$(sha "$(manifest_value candidate_fixture)")"
    printf 'baseline_marker_sha256=%s\n' \
      "$(sha "$(manifest_value baseline_marker)")"
    printf 'candidate_marker_sha256=%s\n' \
      "$(sha "$(manifest_value candidate_marker)")"
    printf 'theorem=%s\n' "$(manifest_value "$theorem_key")"
    printf 'axioms=%s\n' "$axioms_value"
    printf 'contract=%s\n' "$(manifest_value "$contract_key")"
    printf 'target_triple=%s\n' "$target"
    printf 'data_layout=%s\n' "$datalayout"
    printf 'toolchain_revision=%s\n' "$toolchain_revision"
  } > "$path"
}

# The canonical certificate of each unit is derived from the manifest inputs
# before any change is made, and the producer shim publishes it.  The fixture
# records the producer's bytes, so the certificate the selector re-derives is
# compared with what the manifest binds.
write_certificate "$canonical/baseline.env" baseline baseline theorem contract
write_certificate "$canonical/candidate.env" candidate candidate theorem contract
write_certificate "$canonical/json_scan.env" json_scan json_scan \
  json_scan_theorem json_scan_contract
(cd "$mirror" &&
  CERT_UNIT=baseline CERT_MANIFEST="$manifest" CERT_OUT="$proof_baseline" \
    lake env lean probes/install/InstallCertificate.lean)
(cd "$mirror" &&
  CERT_UNIT=candidate CERT_MANIFEST="$manifest" CERT_OUT="$proof_candidate" \
    lake env lean probes/install/InstallCertificate.lean)
(cd "$mirror" &&
  CERT_UNIT=json_scan CERT_MANIFEST="$manifest" CERT_OUT="$proof_json_scan" \
    lake env lean probes/install/InstallCertificate.lean)
cmp -s "$canonical/baseline.env" "$proof_baseline" ||
  { echo "SETUP: the producer's baseline certificate is not the derived one" >&2; exit 3; }
cmp -s "$canonical/candidate.env" "$proof_candidate" ||
  { echo "SETUP: the producer's candidate certificate is not the derived one" >&2; exit 3; }
cmp -s "$canonical/json_scan.env" "$proof_json_scan" ||
  { echo "SETUP: the producer's json_scan certificate is not the derived one" >&2; exit 3; }
{
  printf 'proof_baseline_sha256=%s\n' "$(sha "$proof_baseline")"
  printf 'proof_candidate_sha256=%s\n' "$(sha "$proof_candidate")"
  printf 'proof_json_scan_sha256=%s\n' "$(sha "$proof_json_scan")"
} >> "$manifest"

set +e
trap - ERR

# --- assertions -----------------------------------------------------------
fails=0
ok() { printf 'ok: %s\n' "$*"; }
bad() { printf 'FAIL: %s\n' "$*" >&2; fails=$((fails + 1)); }

# The value of a `key=value` line, empty when the file or the key is absent.
value_of() { # file key
  [ -f "$1" ] || return 0
  sed -n "s/^$2=//p" "$1" 2>/dev/null | sed -n '1p'
}

record_value() { # record key
  value_of "$1" "$2"
}

replace_value() { # file key value
  local file=$1 key=$2 value=$3
  awk -v k="$key" -v v="$value" '
    index($0, k "=") == 1 { print k "=" v; next }
    { print }
  ' "$file" > "$file.tmp" && mv "$file.tmp" "$file"
}

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

# The digest of the file a manifest key names, empty when the key or the file is
# absent, so the comparison is with the bytes of the named artifact rather than
# with a value the test retyped.
file_digest_at() { # manifest key
  local path
  path=$(manifest_value "$1")
  if [ -n "$path" ] && [ -f "$path" ]; then
    sha "$path"
  fi
}

# --- positive control -----------------------------------------------------
# A strict baseline selection from the same input must link the baseline object
# and leave a runnable output at the requested path, so the fake link, the
# digest and output detection are known to work before the same detectors are
# used to judge the JSON unit.
control_out=$outdir/control
control_record=$work/control.env
control_status=0
UNIT=baseline STRICT=1 MANIFEST="$manifest" OUT="$control_out" \
  RECORD="$control_record" "$selector" \
  >"$work/control.stdout" 2>"$work/control.stderr" || control_status=$?
control_selected=$(record_value "$control_record" selected)
control_linked=$(link_target "$control_out")
control_linked_sha=
if [ -n "$control_linked" ] && [ -f "$control_linked" ]; then
  control_linked_sha=$(sha "$control_linked")
fi
control_reason=
if [ "$control_status" -ne 0 ]; then
  control_reason="the strict baseline selection exited $control_status"
elif [ "$control_selected" != baseline ]; then
  control_reason="the selection record names '${control_selected:-nothing}', not the baseline"
elif [ -z "$control_linked_sha" ]; then
  control_reason="no object was handed to the linker"
elif [ "$control_linked_sha" != "$(file_digest_at baseline)" ]; then
  control_reason="the object handed to the linker is not the manifest's baseline object"
elif [ ! -x "$control_out" ]; then
  control_reason="no runnable app was emitted at $control_out"
fi
if [ -z "$control_reason" ]; then
  ok "control: a strict baseline selection exited 0, linked the baseline object and emitted an app"
else
  printf 'SETUP: the baseline control failed: %s\n' "$control_reason" >&2
  sed 's/^/  selector stderr: /' "$work/control.stderr" >&2
  exit 3
fi

# --- JS1 and JS2 ----------------------------------------------------------
if [ "$mode" = --strict ]; then
  json_out=$outdir/json_scan
  json_record=$work/json_scan.env
  json_status=0
  UNIT=json_scan STRICT=1 MANIFEST="$manifest" OUT="$json_out" \
    RECORD="$json_record" "$selector" \
    >"$work/js1.stdout" 2>"$work/js1.stderr" || json_status=$?
  json_selected=$(record_value "$json_record" selected)
  json_proof_sha=$(record_value "$json_record" proof_sha256)
  json_linked=$(link_target "$json_out")
  json_linked_sha=
  if [ -n "$json_linked" ] && [ -f "$json_linked" ]; then
    json_linked_sha=$(sha "$json_linked")
  fi
  certificate_sha=$(file_digest_at proof_json_scan)
  object_sha=$(file_digest_at json_scan)

  if [ "$json_status" -eq 0 ]; then
    ok "JS1: the strict json_scan request exited 0"
  else
    bad "JS1: the strict json_scan request exited $json_status"
  fi

  if [ "$json_selected" = json_scan ]; then
    ok "JS1: the selection record names json_scan"
  else
    bad "JS1: the selection record names '${json_selected:-nothing}'"
  fi

  if [ -n "$certificate_sha" ] && [ "$json_proof_sha" = "$certificate_sha" ]; then
    ok "JS1: the record's proof_sha256 is the certificate's digest"
  else
    bad "JS1: the record's proof_sha256 is '${json_proof_sha:-nothing}', not the digest of the certificate the manifest names"
  fi

  if [ -n "$object_sha" ] && [ "$json_linked_sha" = "$object_sha" ]; then
    ok "JS1: the object handed to the linker is the manifest's json_scan object"
  else
    bad "JS1: the object handed to the linker is '${json_linked:-nothing}' with digest '${json_linked_sha:-nothing}', not the manifest's json_scan object"
  fi

  # --- the one change -----------------------------------------------------
  # JS2 names the wrong theorem for the unit: a validly-shaped name that covers
  # the candidate and the baseline and not this unit.  The manifest's digest of
  # the certificate is then rewritten, so a stale outer digest cannot explain
  # the result.
  replace_value "$proof_json_scan" theorem LeanLLVM.Refinement.CommaMaskIR.IR_refines
  replace_value "$manifest" proof_json_scan_sha256 "$(sha "$proof_json_scan")"

  js2_out=$outdir/json_scan-refused
  js2_record=$work/json_scan-refused.env
  rm -f "$js2_out" "$js2_record"
  js2_status=0
  UNIT=json_scan STRICT=1 MANIFEST="$manifest" OUT="$js2_out" \
    RECORD="$js2_record" "$selector" \
    >"$work/js2.stdout" 2>"$work/js2.stderr" || js2_status=$?

  if [ "$js2_status" -ne 0 ]; then
    ok "JS2: the strict json_scan request was refused with status $js2_status"
  else
    bad "JS2: the strict json_scan request exited 0, so a certificate that disagrees with its unit was accepted"
  fi

  if [ ! -e "$js2_out" ]; then
    ok "JS2: no app was emitted"
  else
    bad "JS2: an app was emitted at $js2_out"
  fi

  if grep -qx '  - proof certificate invalid' "$work/js2.stderr"; then
    ok "JS2: the selector's stderr carries the certificate-invalid reason"
  else
    bad "JS2: the selector's stderr does not carry the certificate-invalid reason"
  fi

  printf 'JS1 selector stdout: %s\n' "$(cat "$work/js1.stdout")"
  sed 's/^/JS1 selector stderr: /' "$work/js1.stderr"
  if [ -f "$json_record" ]; then
    printf 'JS1 record selected: %s\n' "$(record_value "$json_record" selected)"
    printf 'JS1 record proof_sha256: %s\n' "$(record_value "$json_record" proof_sha256)"
    printf 'JS1 record reason: %s\n' "$(record_value "$json_record" reason)"
  fi
  printf 'JS2 selector stdout: %s\n' "$(cat "$work/js2.stdout")"
  sed 's/^/JS2 selector stderr: /' "$work/js2.stderr"
  if [ -f "$js2_record" ]; then
    printf 'JS2 record selected: %s\n' "$(record_value "$js2_record" selected)"
    printf 'JS2 record proof_sha256: %s\n' "$(record_value "$js2_record" proof_sha256)"
    printf 'JS2 record reason: %s\n' "$(record_value "$js2_record" reason)"
  fi
else
  # --- the one change -----------------------------------------------------
  # JS3 uses the same theorem-changed certificate as JS2, digest repaired.
  replace_value "$proof_json_scan" theorem LeanLLVM.Refinement.CommaMaskIR.IR_refines
  replace_value "$manifest" proof_json_scan_sha256 "$(sha "$proof_json_scan")"

  js3_out=$outdir/json_scan-fallback
  js3_record=$work/json_scan-fallback.env
  rm -f "$js3_out" "$js3_record"
  js3_status=0
  UNIT=json_scan STRICT=0 MANIFEST="$manifest" OUT="$js3_out" \
    RECORD="$js3_record" "$selector" \
    >"$work/js3.stdout" 2>"$work/js3.stderr" || js3_status=$?
  js3_selected=$(record_value "$js3_record" selected)
  js3_reason=$(record_value "$js3_record" reason)

  if [ "$js3_status" -eq 0 ]; then
    ok "JS3: the non-strict json_scan request exited 0"
  else
    bad "JS3: the non-strict json_scan request exited $js3_status"
  fi

  if [ "$js3_selected" = baseline ]; then
    ok "JS3: the selection record names the baseline"
  else
    bad "JS3: the selection record names '${js3_selected:-nothing}'"
  fi

  if [ "$js3_reason" = 'proof rejected: invalid certificate; installed baseline fallback' ]; then
    ok "JS3: the record's reason is the invalid-certificate fallback"
  else
    bad "JS3: the record's reason is '${js3_reason:-nothing}', not the invalid-certificate fallback"
  fi

  printf 'JS3 selector stdout: %s\n' "$(cat "$work/js3.stdout")"
  sed 's/^/JS3 selector stderr: /' "$work/js3.stderr"
  if [ -f "$js3_record" ]; then
    printf 'JS3 record selected: %s\n' "$(record_value "$js3_record" selected)"
    printf 'JS3 record proof_sha256: %s\n' "$(record_value "$js3_record" proof_sha256)"
    printf 'JS3 record reason: %s\n' "$(record_value "$js3_record" reason)"
  fi
fi

if [ "$fails" -ne 0 ]; then
  printf '%d assertion(s) failed\n' "$fails" >&2
  exit 1
fi
printf 'all assertions held\n'
