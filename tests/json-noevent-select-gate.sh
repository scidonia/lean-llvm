#!/usr/bin/env bash
# Checks for the no-event stage-2 entry's installation certificate.
#
#   bash tests/json-noevent-select-gate.sh --strict
#   bash tests/json-noevent-select-gate.sh --strict-theorem
#   bash tests/json-noevent-select-gate.sh --strict-hash
#   bash tests/json-noevent-select-gate.sh --no-body-theorem
#   bash tests/json-noevent-select-gate.sh --fallback-hash
#
# Each mode drives the selector CLI (probes/install/select.sh) against an
# isolated manifest built in a temporary directory.  The tools the selector
# invokes are local shims in a private PATH: clang, ld, file, nm and leanc;
# lean, which answers `--version` only; and lake, which accepts the proof-module
# rebuild and the certificate producer, and nothing else.  The remaining
# utilities are the real core utilities, operating on temporary inputs.  The
# temporary tree mirrors the repository root the selector resolves the
# revision-bearing pin files from.  No compiler, linker, proof checker or
# service is reached, and nothing outside the temporary directory is written.
#
# The unit under test is the no-event stage-2 entry
# (`kernel/json/stage2_noevent.c`), whose committed fixture is
# `probes/install/ir/stage2-noevent.candidate.ll` and whose exported symbol is
# `leanllvm_json_stage2_noevent`.  The certificate the selector is asked to
# accept is the one the manifest binds: the unit's object, fixture and marker
# hashes, the C8 body theorem `stage2NoEventWalkObligation_of_staging` and its
# pinned axiom footprint, and the unit's boundary contract
# `stage2NoEventBoundary`.
#
# Every mode first makes a strict baseline selection from the same input and
# asserts that it exits 0, links the baseline object and emits an output, so a
# working link and a detectable output are known before the same detectors are
# used to judge the no-event unit.
#
# --strict is NE11 a: a strict `noevent` request whose certificate names the
# unit's own theorem, contract, hashes and observed toolchain must install the
# unit.  The selection record must name `noevent`; its `noevent_sha256` must
# equal the manifest's and the object's own digest; its `proof_sha256` must
# equal the certificate's digest; and its `theorem` and `contract` must be the
# unit's, so the record publishes what the certificate bound.
#
# --strict-theorem is NE11 b: the same request against a certificate whose
# `theorem` field names `IR_refines`, another unit's statement, must be refused
# and the refusal must name the value it used, even after the manifest's digest
# of the certificate is rewritten to the changed bytes.
#
# --strict-hash is NE11 c: the same request against a certificate whose
# `unit_object_sha256` value has been exchanged with its own
# `baseline_object_sha256` value, so every hash token remains in the file and
# only the field-to-file relation breaks, must be refused with the certificate
# reason, again after the manifest digest is rewritten.
#
# --no-body-theorem is NE11 e: a manifest that binds only the unconditional
# boundary corollary `stage2NoEventBoundary_consumer` — the statement a unit
# without the C8 body theorem would have to name — with a matching certificate
# must not offer the strict install: the request is refused and the refusal
# names the unit's required body theorem.
#
# --fallback-hash is NE11 d: the --strict-hash certificate with `STRICT=0` must
# install the baseline and record the rejection as the invalid-certificate
# fallback.
#
# Exit status: 0 when the scenario's assertions hold, 1 when one fails,
# 2 on bad usage, 3 when the fixture itself is not usable.
set -uo pipefail

usage() {
  cat >&2 <<'USAGE'
usage: bash tests/json-noevent-select-gate.sh --strict
       bash tests/json-noevent-select-gate.sh --strict-theorem
       bash tests/json-noevent-select-gate.sh --strict-hash
       bash tests/json-noevent-select-gate.sh --no-body-theorem
       bash tests/json-noevent-select-gate.sh --fallback-hash
USAGE
  exit 2
}

mode=${1:-}
case "$mode" in
  --strict|--strict-theorem|--strict-hash|--no-body-theorem|--fallback-hash) ;;
  *) usage ;;
esac
[ "$#" -eq 1 ] || usage

repo=$(cd "$(dirname "$0")/.." && pwd)
selector_source=$repo/probes/install/select.sh
ir=$repo/probes/install/ir
noevent_fixture_source=$ir/stage2-noevent.candidate.ll
for path in "$selector_source" "$ir/baseline.ll" "$ir/candidate.ll" \
  "$ir/marker_baseline.ll" "$ir/marker_candidate.ll" \
  "$noevent_fixture_source" \
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
# Exit before the scenario's own assertions if the fixture cannot be built, so
# a construction failure is never read as an assertion result.
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

# leanc: records the exact objects it was asked to link and writes an output at
# the requested path.  What the output computes is not this route's observable;
# the route asserts which object the linker was handed and that the selection's
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
  baseline|candidate|noevent) cert_unit=$CERT_UNIT ;;
  *) echo "lake: CERT_UNIT must name baseline, candidate or noevent" >&2; exit 1 ;;
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

# The no-event unit's fixture is the repository's committed emission of
# `stage2_noevent.c`; its symbol is the one the fixture defines, read there
# rather than retyped.  The unit's marker is the two-line stub `build.sh` gives
# every unit, so the marker's own text is not an observable of this route.
cp "$noevent_fixture_source" "$fixtures/ir/noevent.ll"
cat > "$fixtures/ir/marker_noevent.ll" <<'LL'
define i64 @leanllvm_impl_id(i64 %dummy) {
bb:
  ret i64 0
}
LL

# The baseline and candidate units are the repository's fixtures, copied; each
# object is built with the same basenames and command sequence `build.sh` uses,
# so the manifest values are computed from the fixture bytes and from what the
# selector will rebuild, never typed by hand.
for unit in baseline candidate noevent; do
  if [ "$unit" != noevent ]; then
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

# The caller is the object that imports the selected unit's symbol.  The
# no-event entry's symbol is read from the fixture the way the compiler records
# it; the comma-mask import is the baseline control's.
noevent_symbol=$(sed -n 's/^define [^@]*@\([A-Za-z0-9_]*\)(.*/\1/p' \
  "$fixtures/ir/noevent.ll" | sed -n '1p')
[ -n "$noevent_symbol" ] ||
  { echo "SETUP: the no-event fixture defines no function" >&2; exit 3; }
printf 'OBJ caller\nU leanllvm_comma_mask8\nU %s\n' "$noevent_symbol" \
  > "$fixtures/caller.o"

cat > "$fixtures/differential.txt" <<CERT
kind: differential
symbol: $noevent_symbol
bodies: proved-baseline proved-candidate noevent
covers: candidate-vs-baseline, noevent-vs-stage2
not-covered: none
RESULT: PASS
CERT

# The no-event unit's object must be exactly what a rebuild from its own
# fixture produces with the same tools: otherwise the selector's own rebuild
# check would reject the unit and the scenario would observe a fixture failure
# instead of the rule under test.
cp "$fixtures/ir/noevent.ll" "$rebuild/noevent.ll"
cp "$fixtures/ir/marker_noevent.ll" "$rebuild/marker_noevent.ll"
(cd "$rebuild" &&
  clang -c noevent.ll -o noevent.o &&
  clang -c marker_noevent.ll -o marker_noevent.o &&
  ld -r noevent.o marker_noevent.o -o unit.o)
if ! cmp -s "$rebuild/unit.o" "$fixtures/noevent.o"; then
  echo "SETUP: the installed no-event object is not the rebuild of its fixture" >&2
  exit 3
fi

# The certificate's field values are derived from the files the manifest names,
# from the toolchain the selector observes and from the pinned proof data, so a
# fixture value cannot silently disagree with the input it claims.  Each
# certificate carries the checked axiom set of the theorem it names, read from
# that theorem's own `#print axioms` pin under LeanLLVMTest/.  A theorem with no
# pin has no known footprint, and there is nothing to carry for it: the fixture
# is refused with the missing pin's name and the directory it belongs in.  It is
# never substituted, because another declaration's checked set is a value that
# reads as a footprint while being about a different theorem.
pinned_axioms() { # theorem short name
  # Lean wraps a rendered `#print axioms` message at its print width, so the
  # pin can span several source lines.  Join them before matching: a reader that
  # assumes one line stops matching, silently, the moment the name or the set
  # crosses the width.
  local axioms
  axioms=$(
    cat "$repo"/LeanLLVMTest/*.lean |
      tr '\n' ' ' |
      sed -n "s/.*'LeanLLVM\.[A-Za-z0-9_.]*\.$1' depends on axioms: \[\([^]]*\)\].*/\1/p" |
      tr ',' '\n' | sed 's/^ *//; s/ *$//' | grep -v '^$' |
      LC_ALL=C sort | paste -sd, -
  )
  [ -n "$axioms" ] || return 1
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

# The theorem the unit's certificate must name: the C8 body theorem at the
# record's staging.  `stage2NoEventCallSatisfies_of_staging` derives the
# pipeline slot's call record from it and is the pipeline's covering statement;
# the unit's own certificate names the walk obligation it inhabits.
noevent_theorem=LeanLLVM.Refinement.stage2NoEventWalkObligation_of_staging
# The unconditional boundary corollary: what a unit without the C8 body theorem
# would have to name, and not the body theorem the strict install requires.
boundary_only_theorem=LeanLLVM.Refinement.stage2NoEventBoundary_consumer
# The boundary proposition the covering theorem is stated over.
noevent_contract=LeanLLVM.Refinement.stage2NoEventBoundary

# The manifest binds the no-event unit's own theorem and contract beside the
# global comma pair, which keeps naming the candidate-to-baseline statement and
# the comma seam for the baseline and the candidate.
cat > "$manifest" <<EOF
kind=proof-bound
target=$target
triple=$target
symbol=leanllvm_comma_mask8
marker=leanllvm_impl_id
contract=LeanLLVM.Refinement.commaContract
theorem=LeanLLVM.Refinement.CommaMaskIR.IR_refines
noevent_symbol=$noevent_symbol
noevent_theorem=$noevent_theorem
noevent_contract=$noevent_contract
attributes=reject
datalayout=$datalayout
target_features=none
baseline_fixture=$fixtures/ir/baseline.ll
candidate_fixture=$fixtures/ir/candidate.ll
noevent_fixture=$fixtures/ir/noevent.ll
baseline_marker=$fixtures/ir/marker_baseline.ll
candidate_marker=$fixtures/ir/marker_candidate.ll
noevent_marker=$fixtures/ir/marker_noevent.ll
baseline_fixture_sha256=$(sha "$fixtures/ir/baseline.ll")
candidate_fixture_sha256=$(sha "$fixtures/ir/candidate.ll")
noevent_fixture_sha256=$(sha "$fixtures/ir/noevent.ll")
baseline_marker_sha256=$(sha "$fixtures/ir/marker_baseline.ll")
candidate_marker_sha256=$(sha "$fixtures/ir/marker_candidate.ll")
noevent_marker_sha256=$(sha "$fixtures/ir/marker_noevent.ll")
caller=$fixtures/caller.o
baseline=$fixtures/baseline.o
candidate=$fixtures/candidate.o
noevent=$fixtures/noevent.o
differential=$fixtures/differential.txt
caller_sha256=$(sha "$fixtures/caller.o")
baseline_sha256=$(sha "$fixtures/baseline.o")
candidate_sha256=$(sha "$fixtures/candidate.o")
noevent_sha256=$(sha "$fixtures/noevent.o")
differential_sha256=$(sha "$fixtures/differential.txt")
EOF

proof_baseline=$proofs/proof_baseline.env
proof_noevent=$proofs/proof_noevent.env
{
  printf 'proof_baseline=%s\n' "$proof_baseline"
  printf 'proof_noevent=%s\n' "$proof_noevent"
} >> "$manifest"

manifest_value() { # key
  sed -n "s/^$1=//p" "$manifest" | sed -n '1p'
}

# The certificate a unit's producer publishes: every field derived from the file
# or input the field names.  The theorem and the contract are the ones bound to
# that unit in the manifest, and the axiom set is that theorem's checked
# footprint.
write_certificate() { # path artifact-unit certificate-unit theorem-key contract-key
  local path=$1 art_unit=$2 cert_unit=$3 theorem_key=$4 contract_key=$5
  local theorem axioms_value
  theorem=$(manifest_value "$theorem_key")
  if ! axioms_value=$(pinned_axioms "${theorem##*.}"); then
    echo "SETUP: no '#print axioms' pin for $theorem in $repo/LeanLLVMTest/" >&2
    echo "SETUP: the certificate's axioms field is that theorem's checked footprint," >&2
    echo "SETUP: and no other declaration's set stands in for a theorem without one" >&2
    exit 3
  fi
  if ! printf '%s' "$axioms_value" |
       grep -Eq '^[A-Za-z0-9_.]+(,[A-Za-z0-9_.]+)*$'; then
    echo "SETUP: the pin for $theorem does not name an axiom set" >&2
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
write_certificate "$canonical/noevent.env" noevent noevent \
  noevent_theorem noevent_contract
(cd "$mirror" &&
  CERT_UNIT=baseline CERT_MANIFEST="$manifest" CERT_OUT="$proof_baseline" \
    lake env lean probes/install/InstallCertificate.lean)
(cd "$mirror" &&
  CERT_UNIT=noevent CERT_MANIFEST="$manifest" CERT_OUT="$proof_noevent" \
    lake env lean probes/install/InstallCertificate.lean)
cmp -s "$canonical/baseline.env" "$proof_baseline" ||
  { echo "SETUP: the producer's baseline certificate is not the derived one" >&2; exit 3; }
cmp -s "$canonical/noevent.env" "$proof_noevent" ||
  { echo "SETUP: the producer's noevent certificate is not the derived one" >&2; exit 3; }
{
  printf 'proof_baseline_sha256=%s\n' "$(sha "$proof_baseline")"
  printf 'proof_noevent_sha256=%s\n' "$(sha "$proof_noevent")"
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

# A strict install of the no-event unit: the request exited 0, selected the
# unit, handed the linker its object, and the record republished the manifest's
# digests, the certificate's digest and the unit's theorem and contract.
assert_noevent_install() { # label status out record
  local label=$1 status=$2 out=$3 record=$4
  local selected proof_sha linked linked_sha certificate_sha object_sha
  local record_theorem record_contract

  selected=$(record_value "$record" selected)
  proof_sha=$(record_value "$record" proof_sha256)
  linked=$(link_target "$out")
  linked_sha=
  if [ -n "$linked" ] && [ -f "$linked" ]; then
    linked_sha=$(sha "$linked")
  fi
  certificate_sha=$(file_digest_at proof_noevent)
  object_sha=$(file_digest_at noevent)
  record_theorem=$(record_value "$record" theorem)
  record_contract=$(record_value "$record" contract)

  if [ "$status" -eq 0 ]; then
    ok "$label: the strict no-event request exited 0"
  else
    bad "$label: the strict no-event request exited $status"
  fi

  if [ "$selected" = noevent ]; then
    ok "$label: the selection record names noevent"
  else
    bad "$label: the selection record names '${selected:-nothing}'"
  fi

  if [ -n "$certificate_sha" ] && [ "$proof_sha" = "$certificate_sha" ]; then
    ok "$label: the record's proof_sha256 is the certificate's digest"
  else
    bad "$label: the record's proof_sha256 is '${proof_sha:-nothing}', not the digest of the certificate the manifest names"
  fi

  if [ -n "$object_sha" ] && [ "$linked_sha" = "$object_sha" ]; then
    ok "$label: the object handed to the linker is the manifest's no-event object"
  else
    bad "$label: the object handed to the linker is '${linked:-nothing}' with digest '${linked_sha:-nothing}', not the manifest's no-event object"
  fi

  if [ -n "$object_sha" ] &&
     [ "$(record_value "$record" noevent_sha256)" = "$object_sha" ] &&
     [ "$(record_value "$record" noevent_sha256)" = "$(manifest_value noevent_sha256)" ]; then
    ok "$label: the record's noevent_sha256 is the manifest's and the object's digest"
  else
    bad "$label: the record's noevent_sha256 is '$(record_value "$record" noevent_sha256)', not the manifest's $(manifest_value noevent_sha256)"
  fi

  if [ "$record_theorem" = "$noevent_theorem" ]; then
    ok "$label: the record names the unit's body theorem"
  else
    bad "$label: the record names the theorem '${record_theorem:-nothing}', not '$noevent_theorem'"
  fi

  if [ "$record_contract" = "$noevent_contract" ]; then
    ok "$label: the record names the unit's contract"
  else
    bad "$label: the record names the contract '${record_contract:-nothing}', not '$noevent_contract'"
  fi
}

# A refused strict request: nonzero status, no output, no record naming the
# unit, the certificate-invalid reason on stderr and, when the disagreement is
# a name, the exact detail line.
assert_refused() { # label status out record detail
  local label=$1 status=$2 out=$3 record=$4 detail=${5:-}

  if [ "$status" -ne 0 ]; then
    ok "$label: the strict no-event request was refused with status $status"
  else
    bad "$label: the strict no-event request exited 0, so a certificate that disagrees with its unit was accepted"
  fi

  if [ ! -e "$out" ]; then
    ok "$label: no output was emitted"
  else
    bad "$label: an output was emitted at $out"
  fi

  if [ -f "$record" ] && grep -qx 'selected=noevent' "$record"; then
    bad "$label: the selection record names noevent"
  else
    ok "$label: the selection record does not name noevent"
  fi

  if grep -qx '  - proof certificate invalid' "$work/$label.stderr"; then
    ok "$label: the selector's stderr carries the certificate-invalid reason"
  else
    bad "$label: the selector's stderr does not carry the certificate-invalid reason"
  fi

  if [ -n "$detail" ]; then
    if grep -qxF "$detail" "$work/$label.stderr"; then
      ok "$label: the refusal names the wrong field value"
    else
      bad "$label: the refusal does not name '$detail'"
    fi
  fi
}

# --- positive control -----------------------------------------------------
# A strict baseline selection from the same input must link the baseline object
# and leave a runnable output at the requested path, so the fake link, the
# digest and output detection are known to work before the same detectors are
# used to judge the no-event unit.
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
  control_reason="no runnable output was emitted at $control_out"
fi
if [ -z "$control_reason" ]; then
  ok "control: a strict baseline selection exited 0, linked the baseline object and emitted an output"
else
  printf 'SETUP: the baseline control failed: %s\n' "$control_reason" >&2
  sed 's/^/  selector stderr: /' "$work/control.stderr" >&2
  exit 3
fi

# The valid no-event selection: the certificate carries the values its fields
# claim, so the unit must be installable from it.  In every mode this is the
# affirmative control that shows the certificate under test was valid before
# the one change.
valid_out=$outdir/valid
valid_record=$work/valid.env
valid_status=0
UNIT=noevent STRICT=1 MANIFEST="$manifest" OUT="$valid_out" \
  RECORD="$valid_record" "$selector" \
  >"$work/valid.stdout" 2>"$work/valid.stderr" || valid_status=$?

under_test_stdout=$work/valid.stdout
under_test_stderr=$work/valid.stderr
under_test_record=$valid_record

if [ "$mode" = --strict ]; then
  assert_noevent_install NE11a "$valid_status" "$valid_out" "$valid_record"

  # The published certificate carries the covering theorem's checked axiom
  # footprint; the selector accepts the certificate only when the field equals
  # the pinned set, and the producer must reproduce the bytes.
  certificate_axioms=$(value_of "$proof_noevent" axioms)
  pinned=$(pinned_axioms "${noevent_theorem##*.}")
  if [ -n "$pinned" ] && [ "$certificate_axioms" = "$pinned" ]; then
    ok "NE11a: the published certificate's axioms are the theorem's pinned footprint [$pinned]"
  else
    bad "NE11a: the published certificate's axioms are '${certificate_axioms:-nothing}', not the pinned [$pinned]"
  fi
else
  assert_noevent_install control "$valid_status" "$valid_out" "$valid_record"

  case "$mode" in
    --strict-theorem)
      # NE11 b: the certificate names another unit's theorem, the
      # candidate-to-baseline statement, and the manifest's digest of the
      # certificate is rewritten to the changed bytes, so a stale outer digest
      # cannot explain the result.
      replace_value "$proof_noevent" theorem LeanLLVM.Refinement.CommaMaskIR.IR_refines
      replace_value "$manifest" proof_noevent_sha256 "$(sha "$proof_noevent")"
      test_strict=1
      label=NE11b
      detail="  - proof certificate detail: theorem 'LeanLLVM.Refinement.CommaMaskIR.IR_refines' is not the unit's theorem '$noevent_theorem'"
      ;;
    --strict-hash|--fallback-hash)
      # NE11 c and d: the certificate's `unit_object_sha256` value is exchanged
      # with its own `baseline_object_sha256` value, so every hash token stays
      # in the file and only the field-to-file relation breaks.  The manifest's
      # digest is rewritten to the changed bytes.
      noevent_hash=$(value_of "$proof_noevent" unit_object_sha256)
      baseline_hash=$(value_of "$proof_noevent" baseline_object_sha256)
      if [ -z "$noevent_hash" ] || [ -z "$baseline_hash" ] ||
         [ "$noevent_hash" = "$baseline_hash" ]; then
        echo "SETUP: the no-event certificate's object hashes are not distinct" >&2
        exit 3
      fi
      replace_value "$proof_noevent" unit_object_sha256 "$baseline_hash"
      replace_value "$proof_noevent" baseline_object_sha256 "$noevent_hash"
      replace_value "$manifest" proof_noevent_sha256 "$(sha "$proof_noevent")"
      if [ "$mode" = --strict-hash ]; then
        test_strict=1
        label=NE11c
        detail=
      else
        test_strict=0
        label=NE11d
        detail=
      fi
      ;;
    --no-body-theorem)
      # NE11 e: the manifest binds only the unconditional boundary corollary,
      # the statement a unit without the C8 body theorem would have to name.
      # The certificate is re-derived for that manifest and republished, so the
      # refusal cannot be explained by a certificate that disagrees with its
      # manifest: the strict install is not offered because the unit's body
      # theorem is what the certificate must name.
      replace_value "$manifest" noevent_theorem "$boundary_only_theorem"
      write_certificate "$canonical/noevent.env" noevent noevent \
        noevent_theorem noevent_contract
      cp "$canonical/noevent.env" "$proof_noevent"
      replace_value "$manifest" proof_noevent_sha256 "$(sha "$proof_noevent")"
      test_strict=1
      label=NE11e
      detail="  - proof certificate detail: theorem '$boundary_only_theorem' is not the unit's theorem '$noevent_theorem'"
      ;;
  esac

  test_out=$outdir/$label
  test_record=$work/$label.env
  rm -f "$test_out" "$test_record"
  test_status=0
  UNIT=noevent STRICT=$test_strict MANIFEST="$manifest" OUT="$test_out" \
    RECORD="$test_record" "$selector" \
    >"$work/$label.stdout" 2>"$work/$label.stderr" || test_status=$?

  under_test_stdout=$work/$label.stdout
  under_test_stderr=$work/$label.stderr
  under_test_record=$test_record

  if [ "$mode" = --fallback-hash ]; then
    # NE11 d: the non-strict request installs the baseline and records the
    # rejection as the invalid-certificate fallback.
    selected=$(record_value "$test_record" selected)
    reason=$(record_value "$test_record" reason)
    linked=$(link_target "$test_out")
    linked_sha=
    if [ -n "$linked" ] && [ -f "$linked" ]; then
      linked_sha=$(sha "$linked")
    fi
    baseline_sha=$(file_digest_at baseline)

    if [ "$test_status" -eq 0 ]; then
      ok "NE11d: the non-strict no-event request exited 0"
    else
      bad "NE11d: the non-strict no-event request exited $test_status"
    fi

    if [ "$selected" = baseline ]; then
      ok "NE11d: the selection record names the baseline"
    else
      bad "NE11d: the selection record names '${selected:-nothing}'"
    fi

    if [ -n "$baseline_sha" ] && [ "$linked_sha" = "$baseline_sha" ]; then
      ok "NE11d: the linker was given the baseline object"
    else
      bad "NE11d: the linker was given '${linked:-nothing}' with digest '${linked_sha:-nothing}', not the baseline object"
    fi

    if [ "$linked_sha" != "$(file_digest_at noevent)" ]; then
      ok "NE11d: the linked object is not the no-event unit"
    else
      bad "NE11d: the linked object is the no-event unit"
    fi

    if [ "$reason" = 'proof rejected: invalid certificate; installed baseline fallback' ]; then
      ok "NE11d: the record's reason is the invalid-certificate fallback"
    else
      bad "NE11d: the record's reason is '${reason:-nothing}', not the invalid-certificate fallback"
    fi
  else
    assert_refused "$label" "$test_status" "$test_out" "$test_record" "$detail"
  fi
fi

printf 'selector stdout: %s\n' "$(cat "$under_test_stdout")"
sed 's/^/selector stderr: /' "$under_test_stderr"
if [ -f "$under_test_record" ]; then
  printf 'selection record: %s\n' "$(tr '\n' ';' < "$under_test_record")"
fi

if [ "$fails" -ne 0 ]; then
  printf '%d assertion(s) failed\n' "$fails" >&2
  exit 1
fi
printf 'all assertions held\n'
