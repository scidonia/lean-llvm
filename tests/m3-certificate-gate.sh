#!/usr/bin/env bash
# Checks for the kernel-derived installation certificate gate.
#
#   bash tests/m3-certificate-gate.sh --strict FIELD
#   bash tests/m3-certificate-gate.sh --fallback FIELD
#   bash tests/m3-certificate-gate.sh --strict-baseline FIELD
#   bash tests/m3-certificate-gate.sh --strict-malformed VARIANT
#   bash tests/m3-certificate-gate.sh --fallback-malformed VARIANT
#   bash tests/m3-certificate-gate.sh --strict-stale-import CommaMaskKernel
#   bash tests/m3-certificate-gate.sh --fallback-stale-import CommaMaskKernel
#
# FIELD names one field of a proof artifact -- `schema`, `unit`, the object,
# fixture and marker hashes, `theorem`, `axioms`, `contract`,
# `target_triple`, `data_layout` or `toolchain_revision` -- or the artifact
# itself (`proof_candidate` in the two candidate modes, `proof_baseline` in
# the baseline mode) when it is absent.  One invocation tests exactly one
# field; the field matrix is one invocation per field in each mode.
#
# VARIANT names one structural malformation of the candidate artifact, and one
# invocation tests exactly one of them: `duplicate` repeats the `contract`
# line, `missing` deletes it, `reordered` swaps the adjacent `theorem` and
# `axioms` lines, and `extra` appends `extension=x` before the terminal LF.
# Every other field keeps its value, its `key=value` syntax and its position.
#
# `--strict-stale-import` and `--fallback-stale-import` take the imported proof
# source's module name instead, `CommaMaskKernel`.  One invocation appends a
# line that is not a Lean command to the copy of
# LeanLLVM/Vellum/CommaMaskKernel.lean in the fixture tree, so the imported
# graph no longer elaborates; the artifact, the manifest and every object keep
# their bytes.
#
# Each mode first selects with the valid artifact and asserts that selection
# succeeds, then makes one change and selects again.  A field run changes a
# single field value, and a malformed run changes the artifact's serialized
# bytes; both rewrite the manifest's digest of the artifact so an outer hash
# mismatch cannot explain the result.  An absence run instead removes the
# artifact file and keeps its path and recorded digest, so the absence is the
# only change.  A stale-import run appends the invalid-Lean line to the copied
# imported source and changes nothing else, so the imported graph's rebuild is
# the only input that differs.  --strict, --strict-baseline, --strict-malformed
# and --strict-stale-import must refuse; --fallback, --fallback-malformed and
# --fallback-stale-import must install the baseline.
#
# Each mode drives the selector CLI (probes/install/select.sh) against an
# isolated manifest built in a temporary directory.  The tools the selector
# invokes are local shims in a private PATH: clang, ld, file, nm and leanc;
# lean, which answers `--version` only; and lake, which accepts the
# imported-graph rebuild, the source-rebuild check and the certificate producer
# and nothing else.  The graph rebuild succeeds unless the copied imported
# source carries the appended invalid-Lean line; the other two forms always
# succeed, so only the graph rebuild can observe a stale import.  The
# remaining utilities (sha256sum, cut, sed, sort and the rest) are the real
# core utilities, operating on temporary inputs.  No compiler, linker, proof
# checker or service is reached, and nothing outside the temporary directory is
# written.
#
# The temporary tree mirrors the repository root the selector and the proof
# checker resolve their pinned inputs from: lean-toolchain, flake.nix,
# flake.lock, lakefile.toml and lake-manifest.json are copied byte for byte,
# the selector is copied to probes/install/select.sh beside the toolchain
# helper, and the project olean directory the source check writes into exists
# there.  The imported proof source LeanLLVM/Vellum/CommaMaskKernel.lean is
# copied there too, so a stale-import run marks only that copy and never the
# repository's source.
#
# Exit status: 0 when the scenario's assertions hold, 1 when one fails,
# 2 on bad usage, 3 when the fixture itself is not usable.
set -uo pipefail

usage() {
  echo "usage: bash tests/m3-certificate-gate.sh --strict FIELD" >&2
  echo "       bash tests/m3-certificate-gate.sh --fallback FIELD" >&2
  echo "       bash tests/m3-certificate-gate.sh --strict-baseline FIELD" >&2
  echo "       bash tests/m3-certificate-gate.sh --strict-malformed VARIANT" >&2
  echo "       bash tests/m3-certificate-gate.sh --fallback-malformed VARIANT" >&2
  echo "       bash tests/m3-certificate-gate.sh --strict-stale-import CommaMaskKernel" >&2
  echo "       bash tests/m3-certificate-gate.sh --fallback-stale-import CommaMaskKernel" >&2
  exit 2
}

mode=${1:-}
field=${2:-}
case "$mode" in
  --strict|--fallback|--strict-baseline|--strict-malformed|--fallback-malformed|\
  --strict-stale-import|--fallback-stale-import) ;;
  *) usage ;;
esac
[ "$#" -eq 2 ] || usage

schema_fields=(
  schema
  unit
  unit_object_sha256
  unit_fixture_sha256
  unit_marker_sha256
  baseline_object_sha256
  candidate_object_sha256
  baseline_fixture_sha256
  candidate_fixture_sha256
  baseline_marker_sha256
  candidate_marker_sha256
  theorem
  axioms
  contract
  target_triple
  data_layout
  toolchain_revision
)
known_field() {
  local want=$1 f
  for f in "${schema_fields[@]}"; do
    [ "$f" = "$want" ] && return 0
  done
  return 1
}

malformed=0
stale_import=0
variant=
case "$mode" in
  --strict|--fallback)
    if [ "$field" != proof_candidate ] && ! known_field "$field"; then
      usage
    fi
    unit=candidate
    strict=1
    [ "$mode" = --fallback ] && strict=0
    artifact=proof_candidate
    ;;
  --strict-baseline)
    if [ "$field" != proof_baseline ]; then
      usage
    fi
    unit=baseline
    strict=1
    artifact=proof_baseline
    ;;
  --strict-malformed|--fallback-malformed)
    case "$field" in
      duplicate|missing|reordered|extra) ;;
      *) usage ;;
    esac
    malformed=1
    variant=$field
    unit=candidate
    strict=1
    [ "$mode" = --fallback-malformed ] && strict=0
    artifact=proof_candidate
    ;;
  --strict-stale-import|--fallback-stale-import)
    if [ "$field" != CommaMaskKernel ]; then
      usage
    fi
    stale_import=1
    unit=candidate
    strict=1
    [ "$mode" = --fallback-stale-import ] && strict=0
    artifact=proof_candidate
    ;;
esac
absent_artifact=0
if [ "$malformed" -eq 0 ] && [ "$field" = "$artifact" ]; then
  absent_artifact=1
fi

# The scenario a run exercises: H1 and H2 change one field of a candidate
# artifact, H3 and H4 remove the candidate artifact, H5 removes the baseline
# artifact under a strict baseline request, H6 and H7 malform the
# candidate artifact's serialized bytes, and H8 and H9 mark the copied imported
# proof source stale.
if [ "$stale_import" -eq 1 ]; then
  case "$mode" in
    --strict-stale-import) label=H8 ;;
    --fallback-stale-import) label=H9 ;;
  esac
elif [ "$malformed" -eq 1 ]; then
  case "$mode" in
    --strict-malformed) label=H6 ;;
    --fallback-malformed) label=H7 ;;
  esac
else
  case "$mode:$absent_artifact" in
    --strict:0) label=H1 ;;
    --fallback:0) label=H2 ;;
    --strict:1) label=H3 ;;
    --fallback:1) label=H4 ;;
    --strict-baseline:1) label=H5 ;;
    *) label=H1 ;;
  esac
fi

repo=$(cd "$(dirname "$0")/.." && pwd)
selector_source=$repo/probes/install/select.sh
ir=$repo/probes/install/ir

setup_fail() {
  printf 'SETUP: %s\n' "$*" >&2
  exit 3
}

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

mkdir -p "$fakebin" "$fixtures/ir" "$units" "$outdir" "$rebuild" \
  "$proofs" "$canonical" "$mirror/probes/install/build" \
  "$mirror/.lake/build/lib/lean/LeanLLVM/Vellum"
: > "$link_log"

target=x86_64-unknown-linux-gnu
datalayout='e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128'
# The appended line is not a Lean command, so elaborating the imported source
# would fail on it; the lake shim recognises it by exact line.  Only the copy
# in this fixture tree is ever marked.
stale_sentinel='#stale-import-sentinel'
imported_source=$mirror/LeanLLVM/Vellum/CommaMaskKernel.lean

{
  printf 'FAKE_TARGET=%q\n' "$target"
  printf 'FAKE_DATALAYOUT=%q\n' "$datalayout"
  printf 'FAKE_LINK_LOG=%q\n' "$link_log"
  printf 'FAKE_CANONICAL_DIR=%q\n' "$canonical"
  printf 'FAKE_IMPORTED_SOURCE=%q\n' "$imported_source"
  printf 'FAKE_STALE_SENTINEL=%q\n' "$stale_sentinel"
} > "$fakebin/fake.env"

# --- fake toolchain -------------------------------------------------------
# clang: constant target, data layout and version, and object bytes fixed by
# the output basename and the bytes of the fixture it compiles.  The object
# records the symbols the unit exports, so nm and the selector's symbol checks
# observe a fixed per-object answer.
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
digest=$(sha256sum "$src" | cut -d' ' -f1)
{
  printf 'OBJ %s %s\n' "$name" "$digest"
  case "$name" in
    marker_*) printf 'T leanllvm_impl_id\n' ;;
    *) printf 'T leanllvm_comma_mask8\n' ;;
  esac
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

# lake: the proof checker the selector drives.  Three command forms are
# accepted: the imported-graph rebuild of the proof module, which succeeds
# unless the copied imported source carries the appended invalid-Lean line; the
# source-rebuild check, which succeeds without a proof system; and the
# certificate producer, which publishes the canonical certificate of the
# requested unit.  That certificate is derived from the manifest inputs before
# any change is made, so a changed artifact is never echoed back.  Any other
# invocation is refused.
cat > "$fakebin/lake" <<'SHIM'
#!/usr/bin/env bash
set -euo pipefail
. "$(dirname "$0")/fake.env"
if [ "${1:-}" = build ]; then
  [ "$#" -eq 2 ] && [ "$2" = LeanLLVM.Vellum.CommaMaskIR ] ||
    { echo "lake: unexpected build arguments: $*" >&2; exit 1; }
  if [ -f "$FAKE_IMPORTED_SOURCE" ] &&
     grep -qxF -- "$FAKE_STALE_SENTINEL" "$FAKE_IMPORTED_SOURCE"; then
    echo "lake: the imported proof source does not elaborate" >&2
    exit 1
  fi
  exit 0
fi
[ "${1:-}" = env ] && [ "${2:-}" = lean ] ||
  { echo "lake: only 'lake build' and 'lake env lean' are supported" >&2; exit 1; }
shift 2
if [ "${1:-}" = -o ]; then
  [ "$#" -eq 3 ] &&
    [ "$2" = .lake/build/lib/lean/LeanLLVM/Vellum/CommaMaskIR.olean ] &&
    [ "$3" = LeanLLVM/Vellum/CommaMaskIR.lean ] ||
    { echo "lake: unexpected source-check arguments: $*" >&2; exit 1; }
  exit 0
fi
[ "$#" -eq 1 ] && [ "$1" = probes/install/InstallCertificate.lean ] ||
  { echo "lake: unexpected producer arguments: $*" >&2; exit 1; }
case "${CERT_UNIT:-}" in
  baseline|candidate) ;;
  *) echo "lake: CERT_UNIT must name baseline or candidate" >&2; exit 1 ;;
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
cp "$FAKE_CANONICAL_DIR/$CERT_UNIT.env" "$CERT_OUT"
SHIM

chmod +x "$fakebin/clang" "$fakebin/ld" "$fakebin/file" "$fakebin/nm" \
  "$fakebin/leanc" "$fakebin/lean" "$fakebin/lake"
PATH="$fakebin:$PATH"
export PATH

# The temporary tree mirrors the repository root the selector resolves: the
# revision-bearing pin files, the selector at probes/install/select.sh, and
# the project olean directory the source check writes into.
for pinned in lean-toolchain flake.nix flake.lock lakefile.toml \
  lake-manifest.json; do
  cp "$repo/$pinned" "$mirror/$pinned"
done
# The imported proof source is copied under the fixture root, so a stale-import
# run marks only this copy: the repository's source and the objects built from
# the fixtures keep their bytes.
mkdir -p "$mirror/LeanLLVM/Vellum"
[ -f "$repo/LeanLLVM/Vellum/CommaMaskKernel.lean" ] ||
  setup_fail "no imported proof source at LeanLLVM/Vellum/CommaMaskKernel.lean"
cp "$repo/LeanLLVM/Vellum/CommaMaskKernel.lean" "$imported_source"
cp "$selector_source" "$selector"
chmod +x "$selector"
if [ -f "$repo/probes/install/InstallCertificate.lean" ]; then
  cp "$repo/probes/install/InstallCertificate.lean" \
    "$mirror/probes/install/InstallCertificate.lean"
fi
if [ -f "$repo/probes/install/toolchain-id.sh" ]; then
  cp "$repo/probes/install/toolchain-id.sh" \
    "$mirror/probes/install/toolchain-id.sh"
else
  # The selector's sibling helper: the same nine-line record, computed from the
  # mirrored pin files and the version commands' stdout.
  cat > "$mirror/probes/install/toolchain-id.sh" <<'HELPER'
#!/usr/bin/env bash
# The toolchain revision: SHA-256 of a fixed nine-line record built from the
# revision-bearing pin files at the repository root and the version commands'
# stdout under LC_ALL=C.  A single component change changes the digest.
toolchain_id() { # repository root
  local root record
  root=$(cd "$1" && pwd)
  record=$(
    printf 'leanllvm-toolchain-v1\n'
    printf 'lean-toolchain=%s\n' "$(sha256sum "$root/lean-toolchain" | cut -d' ' -f1)"
    printf 'flake-nix=%s\n' "$(sha256sum "$root/flake.nix" | cut -d' ' -f1)"
    printf 'flake-lock=%s\n' "$(sha256sum "$root/flake.lock" | cut -d' ' -f1)"
    printf 'lakefile=%s\n' "$(sha256sum "$root/lakefile.toml" | cut -d' ' -f1)"
    printf 'lake-manifest=%s\n' "$(sha256sum "$root/lake-manifest.json" | cut -d' ' -f1)"
    printf 'lean-version=%s\n' "$(LC_ALL=C lean --version | sha256sum | cut -d' ' -f1)"
    printf 'clang-version=%s\n' "$(LC_ALL=C clang --version | sha256sum | cut -d' ' -f1)"
    printf 'ld-version=%s\n' "$(LC_ALL=C ld --version | sha256sum | cut -d' ' -f1)"
  )
  printf 'sha256:%s\n' "$(printf '%s\n' "$record" | sha256sum | cut -d' ' -f1)"
}

if [ "${BASH_SOURCE[0]}" = "$0" ]; then
  here=$(cd "$(dirname "$0")" && pwd)
  toolchain_id "$here/../.."
fi
HELPER
  chmod +x "$mirror/probes/install/toolchain-id.sh"
fi

# --- fixtures -------------------------------------------------------------
# The unit IR is the repository's fixture, copied; each object is built with
# the same basenames and command sequence `build.sh` uses, so the manifest
# values are computed from the fixture bytes and from what the selector will
# rebuild, never typed by hand.
for u in baseline candidate loop; do
  cp "$ir/$u.ll" "$fixtures/ir/$u.ll"
  cp "$ir/marker_$u.ll" "$fixtures/ir/marker_$u.ll"
  mkdir -p "$units/$u"
  cp "$fixtures/ir/$u.ll" "$units/$u/$u.ll"
  cp "$fixtures/ir/marker_$u.ll" "$units/$u/marker_$u.ll"
  (cd "$units/$u" &&
    clang -c "$u.ll" -o "$u.o" &&
    clang -c "marker_$u.ll" -o "marker_$u.o" &&
    ld -r "$u.o" "marker_$u.o" -o unit.o)
  cp "$units/$u/unit.o" "$fixtures/$u.o"
done

printf 'OBJ caller\nU leanllvm_comma_mask8\n' > "$fixtures/caller.o"

cat > "$fixtures/differential.txt" <<'TRANSCRIPT'
kind: differential
symbol: leanllvm_comma_mask8
bodies: proved-baseline proved-candidate proved-loop lean-baseline lean-candidate
theorem: LeanLLVM.Vellum.CommaMaskIR.IR_refines
covers: candidate-vs-baseline
RESULT: PASS
TRANSCRIPT

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
  setup_fail "the installed loop object is not the rebuild of its fixture"
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
# The manifest is sourced shell, so both transcript key pairs are read as
# ordinary assignments: certificate and differential name the same bytes, and
# only the differential pair is a production binding.  The extra keys are inert
# on the certificate route.
certificate=$fixtures/differential.txt
differential=$fixtures/differential.txt
caller_sha256=$(sha "$fixtures/caller.o")
baseline_sha256=$(sha "$fixtures/baseline.o")
candidate_sha256=$(sha "$fixtures/candidate.o")
loop_sha256=$(sha "$fixtures/loop.o")
certificate_sha256=$(sha "$fixtures/differential.txt")
differential_sha256=$(sha "$fixtures/differential.txt")
EOF

proof_baseline=$proofs/proof_baseline.env
proof_candidate=$proofs/proof_candidate.env
{
  printf 'proof_baseline=%s\n' "$proof_baseline"
  printf 'proof_candidate=%s\n' "$proof_candidate"
} >> "$manifest"

manifest_value() { # key
  sed -n "s/^$1=//p" "$manifest" | sed -n '1p'
}

# The artifact's field values are derived from the files the manifest names,
# from the toolchain the selector observes, and from the pinned proof data, so
# a fixture value cannot silently disagree with the production rule it claims.
axioms=$(
  sed -n 's/.*IR_refines. depends on axioms: \[\(.*\)\]/\1/p' \
    "$repo/LeanLLVMTest/Vellum.lean" |
    tr ',' '\n' | sed 's/^ *//; s/ *$//' | grep -v '^$' |
    LC_ALL=C sort | paste -sd, -
)
[ -n "$axioms" ] || setup_fail "cannot read the pinned axiom set"
# The toolchain revision is the SHA-256 of a fixed nine-line record: a header,
# then the digest of each revision-bearing pin file and of each version
# command's stdout, in that order, every line terminated by one LF.  A single
# component change changes the digest.
hash_bytes() { sha256sum "$1" | cut -d' ' -f1; }
hash_stdout() { LC_ALL=C "$@" | sha256sum | cut -d' ' -f1; }
toolchain_record() { # [lakefile digest override]
  local lakefile=${1:-$(hash_bytes "$mirror/lakefile.toml")}
  printf 'leanllvm-toolchain-v1\n'
  printf 'lean-toolchain=%s\n' "$(hash_bytes "$mirror/lean-toolchain")"
  printf 'flake-nix=%s\n' "$(hash_bytes "$mirror/flake.nix")"
  printf 'flake-lock=%s\n' "$(hash_bytes "$mirror/flake.lock")"
  printf 'lakefile=%s\n' "$lakefile"
  printf 'lake-manifest=%s\n' "$(hash_bytes "$mirror/lake-manifest.json")"
  printf 'lean-version=%s\n' "$(hash_stdout lean --version)"
  printf 'clang-version=%s\n' "$(hash_stdout clang --version)"
  printf 'ld-version=%s\n' "$(hash_stdout ld --version)"
}
toolchain_revision="sha256:$(toolchain_record | sha256sum | cut -d' ' -f1)"
if ! printf '%s' "$toolchain_revision" | grep -Eq '^sha256:[0-9a-f]{64}$'; then
  setup_fail "cannot compute the toolchain revision"
fi
helper_revision=$(cd "$mirror" && bash "$mirror/probes/install/toolchain-id.sh")
if [ "$helper_revision" != "$toolchain_revision" ]; then
  setup_fail "the toolchain helper and the artifact's toolchain revision disagree"
fi
schema_version=leanllvm-install-v1

# One artifact per supported unit.  `unit=loop` has no covering theorem and no
# artifact, so it is not written.
write_artifact() { # path unit
  local path=$1 art_unit=$2
  {
    printf 'schema=%s\n' "$schema_version"
    printf 'unit=%s\n' "$art_unit"
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
    printf 'theorem=%s\n' "$(manifest_value theorem)"
    printf 'axioms=%s\n' "$axioms"
    printf 'contract=%s\n' "$(manifest_value contract)"
    printf 'target_triple=%s\n' "$target"
    printf 'data_layout=%s\n' "$datalayout"
    printf 'toolchain_revision=%s\n' "$toolchain_revision"
  } > "$path"
}

# The canonical certificate of each unit is derived from the manifest inputs
# before any change is made, and the producer shim publishes it.  The fixture
# records the producer's bytes, so the selector's own re-derived certificate is
# compared with what the manifest binds.
write_artifact "$canonical/baseline.env" baseline
write_artifact "$canonical/candidate.env" candidate
(cd "$mirror" &&
  CERT_UNIT=baseline CERT_MANIFEST="$manifest" CERT_OUT="$proof_baseline" \
    lake env lean probes/install/InstallCertificate.lean)
(cd "$mirror" &&
  CERT_UNIT=candidate CERT_MANIFEST="$manifest" CERT_OUT="$proof_candidate" \
    lake env lean probes/install/InstallCertificate.lean)
cmp -s "$canonical/baseline.env" "$proof_baseline" ||
  setup_fail "the producer's baseline certificate is not the derived one"
cmp -s "$canonical/candidate.env" "$proof_candidate" ||
  setup_fail "the producer's candidate certificate is not the derived one"

{
  printf 'proof_baseline_sha256=%s\n' "$(sha "$proof_baseline")"
  printf 'proof_candidate_sha256=%s\n' "$(sha "$proof_candidate")"
} >> "$manifest"

artifact_unit=$unit
artifact_path=$([ "$artifact" = proof_candidate ] && printf '%s' "$proof_candidate" ||
  printf '%s' "$proof_baseline")

# The value a field must carry in a valid artifact, derived from the file or
# input the field names rather than retyped.
intended_value() { # proof field
  case "$1" in
    schema) printf '%s' "$schema_version" ;;
    unit) printf '%s' "$artifact_unit" ;;
    unit_object_sha256) printf '%s' "$(sha "$(manifest_value "$artifact_unit")")" ;;
    unit_fixture_sha256)
      printf '%s' "$(sha "$(manifest_value "${artifact_unit}_fixture")")" ;;
    unit_marker_sha256)
      printf '%s' "$(sha "$(manifest_value "${artifact_unit}_marker")")" ;;
    baseline_object_sha256) printf '%s' "$(sha "$(manifest_value baseline)")" ;;
    candidate_object_sha256) printf '%s' "$(sha "$(manifest_value candidate)")" ;;
    baseline_fixture_sha256)
      printf '%s' "$(sha "$(manifest_value baseline_fixture)")" ;;
    candidate_fixture_sha256)
      printf '%s' "$(sha "$(manifest_value candidate_fixture)")" ;;
    baseline_marker_sha256)
      printf '%s' "$(sha "$(manifest_value baseline_marker)")" ;;
    candidate_marker_sha256)
      printf '%s' "$(sha "$(manifest_value candidate_marker)")" ;;
    theorem) printf '%s' "$(manifest_value theorem)" ;;
    axioms) printf '%s' "$axioms" ;;
    contract) printf '%s' "$(manifest_value contract)" ;;
    target_triple) printf '%s' "$target" ;;
    data_layout) printf '%s' "$datalayout" ;;
    toolchain_revision) printf '%s' "$toolchain_revision" ;;
  esac
}

value_of() { # file key
  sed -n "s/^$2=//p" "$1" | sed -n '1p'
}

replace_value() { # file key value
  local file=$1 key=$2 value=$3
  awk -v k="$key" -v v="$value" '
    index($0, k "=") == 1 { print k "=" v; next }
    { print }
  ' "$file" > "$file.tmp" && mv "$file.tmp" "$file"
}

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
# The same selector, the same detector and the valid artifact: the selection
# must succeed, emit the output and hand the requested unit's object to the
# linker, so a later refusal or fallback is attributable to the change made to
# the artifact and to nothing else.
control_out=$outdir/control
control_record=$work/control.env
control_status=0
UNIT=$unit STRICT=$strict MANIFEST="$manifest" OUT="$control_out" \
  RECORD="$control_record" "$selector" \
  >"$work/control.stdout" 2>"$work/control.stderr" || control_status=$?
control_selected=$(value_of "$control_record" selected)
control_linked=$(link_target "$control_out")
control_reason=$(value_of "$control_record" reason)
expected_object=$(manifest_value "$unit")

# A fallback scenario asserts an exact rejection reason, so its control must
# show the same parsed `reason` field carrying the acceptance reason of the
# unchanged artifact: the field is then observed to distinguish acceptance from
# rejection, not merely to carry a different sentence.
accepted_reason="hashes, fixtures, rebuild and certificate match; $(manifest_value theorem) covers the selected unit"
control_reason_ok=1
case "$label" in
  H2|H4|H7|H9)
    [ "$control_reason" = "$accepted_reason" ] || control_reason_ok=0
    ;;
esac

if [ "$control_status" -eq 0 ] &&
   [ "$control_selected" = "$unit" ] &&
   [ -e "$control_out" ] &&
   [ "$control_linked" = "$expected_object" ] &&
   [ "$control_reason_ok" -eq 1 ]; then
  ok "control: the valid artifact was accepted, selected $unit and linked its object"
  case "$label" in
    H2|H4|H7|H9)
      ok "control: the record's reason is the acceptance reason for the unchanged artifact"
      ;;
  esac
else
  printf 'SETUP: valid-artifact control failed (status %s, selected %s, linked %s, reason %s)\n' \
    "$control_status" "${control_selected:-nothing}" "${control_linked:-nothing}" "${control_reason:-nothing}" >&2
  sed 's/^/  selector stderr: /' "$work/control.stderr" >&2
  exit 3
fi

# --- the one change -------------------------------------------------------
# A schema field is changed in place; a paired object/fixture/marker hash is
# exchanged with its counterpart, which leaves every hash token in the file and
# breaks only the field-to-file relation the artifact claims.  The manifest's
# digest of the artifact is then rewritten, so the result cannot be explained
# by a stale outer hash.
pair_of() { # field
  case "$1" in
    baseline_object_sha256|candidate_object_sha256) printf 'baseline_object_sha256 candidate_object_sha256' ;;
    baseline_fixture_sha256|candidate_fixture_sha256) printf 'baseline_fixture_sha256 candidate_fixture_sha256' ;;
    baseline_marker_sha256|candidate_marker_sha256) printf 'baseline_marker_sha256 candidate_marker_sha256' ;;
    *) printf '%s' "$1" ;;
  esac
}

changed_fields() { # valid changed
  local valid=$1 changed=$2 k out=
  while IFS= read -r k; do
    if [ "$(value_of "$valid" "$k")" != "$(value_of "$changed" "$k")" ]; then
      out="$out $k"
    fi
  done < <(sed 's/=.*$//' "$valid")
  printf '%s' "${out# }"
}

sorted_values() { sed 's/^[^=]*=//' "$1" | LC_ALL=C sort; }

valid_copy=$work/valid.env
if [ "$stale_import" -eq 1 ]; then
  # The artifact, the manifest and both unit objects keep their bytes; only
  # the copied imported source gains the appended invalid-Lean line, so the
  # refusal or fallback is attributable to the imported graph and nothing else.
  cp "$artifact_path" "$valid_copy"
  unchanged_artifact=$(sha "$artifact_path")
  unchanged_manifest=$(sha "$manifest")
  unchanged_baseline=$(sha "$(manifest_value baseline)")
  unchanged_candidate=$(sha "$(manifest_value candidate)")
  cp "$imported_source" "$work/imported-before.lean" ||
    setup_fail "cannot read the copied imported source"
  {
    cat "$work/imported-before.lean"
    printf '%s\n' "$stale_sentinel"
  } > "$work/imported-stale.lean"
  cp "$work/imported-stale.lean" "$imported_source" ||
    setup_fail "cannot write the copied imported source"
  cmp -s "$work/imported-stale.lean" "$imported_source" ||
    setup_fail "the copied imported source is not the marked source"
  if cmp -s "$work/imported-before.lean" "$imported_source"; then
    setup_fail "marking the imported source changed nothing"
  fi
  [ "$(grep -cxF -- "$stale_sentinel" "$imported_source")" -eq 1 ] ||
    setup_fail "the copied imported source does not carry the sentinel once"
  [ "$(sha "$artifact_path")" = "$unchanged_artifact" ] ||
    setup_fail "the certificate changed with the imported source"
  [ "$(sha "$manifest")" = "$unchanged_manifest" ] ||
    setup_fail "the manifest changed with the imported source"
  [ "$(sha "$(manifest_value baseline)")" = "$unchanged_baseline" ] ||
    setup_fail "the baseline object changed with the imported source"
  [ "$(sha "$(manifest_value candidate)")" = "$unchanged_candidate" ] ||
    setup_fail "the candidate object changed with the imported source"
elif [ "$absent_artifact" -eq 1 ]; then
  cp "$artifact_path" "$valid_copy"
  rm -f "$artifact_path"
  [ ! -e "$artifact_path" ] || setup_fail "cannot remove $artifact_path"
elif [ "$malformed" -eq 1 ]; then
  cp "$artifact_path" "$valid_copy"

  # The malformation changes the serialized structure only.  The expected
  # bytes are built from the valid artifact with a different tool than the one
  # that applies the change, so a difference anywhere else in the file fails
  # the comparison instead of passing unnoticed.
  expected=$work/malformed.expected
  case "$variant" in
    duplicate)
      malformed_what="its contract line repeated"
      {
        while IFS= read -r line || [ -n "$line" ]; do
          printf '%s\n' "$line"
          case "$line" in
            contract=*) printf '%s\n' "$line" ;;
          esac
        done < "$valid_copy"
      } > "$expected"
      awk '
        /^contract=/ && !seen { seen = 1; print; print; next }
        { print }
      ' "$valid_copy" > "$artifact_path.tmp" &&
        mv "$artifact_path.tmp" "$artifact_path"
      ;;
    missing)
      malformed_what="its contract line removed"
      grep -v '^contract=' "$valid_copy" > "$expected"
      awk '!/^contract=/' "$valid_copy" > "$artifact_path.tmp" &&
        mv "$artifact_path.tmp" "$artifact_path"
      ;;
    reordered)
      malformed_what="its theorem and axioms lines swapped"
      theorem_line=$(grep -m1 '^theorem=' "$valid_copy")
      axioms_line=$(grep -m1 '^axioms=' "$valid_copy")
      theorem_no=$(grep -n '^theorem=' "$valid_copy" | sed -n '1s/:.*//p')
      axioms_no=$(grep -n '^axioms=' "$valid_copy" | sed -n '1s/:.*//p')
      if [ -z "$theorem_line" ] || [ -z "$axioms_line" ] ||
         [ "$((theorem_no + 1))" -ne "$axioms_no" ]; then
        setup_fail "the theorem and axioms lines are not adjacent in the artifact"
      fi
      sed -e "${theorem_no}s|.*|$axioms_line|" \
          -e "${axioms_no}s|.*|$theorem_line|" \
        "$valid_copy" > "$expected"
      awk '
        /^theorem=/ { pending = $0; next }
        /^axioms=/ && pending != "" { print; print pending; pending = ""; next }
        { print }
        END { if (pending != "") exit 1 }
      ' "$valid_copy" > "$artifact_path.tmp" &&
        mv "$artifact_path.tmp" "$artifact_path"
      ;;
    extra)
      malformed_what="an appended extension key"
      { cat "$valid_copy"; printf 'extension=x\n'; } > "$expected"
      awk '{ print } END { printf "extension=x\n" }' \
        "$valid_copy" > "$artifact_path.tmp" &&
        mv "$artifact_path.tmp" "$artifact_path"
      ;;
  esac

  if ! cmp -s "$expected" "$artifact_path"; then
    setup_fail "the $variant malformation is not the intended change"
  fi
  if cmp -s "$valid_copy" "$artifact_path"; then
    setup_fail "the $variant malformation left the artifact unchanged"
  fi
else
  cp "$artifact_path" "$valid_copy"

  # The valid artifact carries the derived value for the field about to change.
  valid_value=$(value_of "$artifact_path" "$field")
  intended=$(intended_value "$field")
  if [ "$valid_value" != "$intended" ]; then
    setup_fail "valid artifact $field is '$valid_value', not the derived '$intended'"
  fi

  other_unit=candidate
  [ "$artifact_unit" = candidate ] && other_unit=baseline
  lakefile_digest=$(hash_bytes "$mirror/lakefile.toml")
  last=${lakefile_digest: -1}
  if [ "$last" = 0 ]; then replacement=1; else replacement=0; fi
  lakefile_digest_mutated="${lakefile_digest%?}$replacement"
  toolchain_revision_mutated="sha256:$(toolchain_record "$lakefile_digest_mutated" | sha256sum | cut -d' ' -f1)"

  pair=$(pair_of "$field")
  if [ "$pair" != "$field" ]; then
    set -- $pair
    first=$1
    second=$2
    first_value=$(value_of "$artifact_path" "$first")
    second_value=$(value_of "$artifact_path" "$second")
    replace_value "$artifact_path" "$first" "$second_value"
    replace_value "$artifact_path" "$second" "$first_value"
  else
    case "$field" in
      schema) mutation=2 ;;
      unit) mutation=$other_unit ;;
      unit_object_sha256) mutation=$(intended_value "${other_unit}_object_sha256") ;;
      unit_fixture_sha256) mutation=$(intended_value "${other_unit}_fixture_sha256") ;;
      unit_marker_sha256) mutation=$(intended_value "${other_unit}_marker_sha256") ;;
      theorem) mutation=LeanLLVM.Vellum.CommaMaskKernel.byteLoop_refines_swar ;;
      axioms) mutation="$axioms,sorryAx" ;;
      contract) mutation=LeanLLVM.Vellum.commaLoopContract ;;
      target_triple) mutation=aarch64-unknown-linux-gnu ;;
      data_layout) mutation=$(printf '%s' "$datalayout" | sed 's/-f80:128//') ;;
      toolchain_revision) mutation=$toolchain_revision_mutated ;;
      *) setup_fail "no mutation for $field" ;;
    esac
    replace_value "$artifact_path" "$field" "$mutation"
  fi

  # The change is exactly the named field (or its pair), the field order is
  # unchanged, and for a pair exchange every value token is still present.
  changed=$(changed_fields "$valid_copy" "$artifact_path")
  expected_changed=$(pair_of "$field")
  if [ "$changed" != "$expected_changed" ]; then
    setup_fail "the mutation changed '$changed', not '$expected_changed'"
  fi
  if ! cmp -s <(sed 's/=.*$//' "$valid_copy") \
              <(sed 's/=.*$//' "$artifact_path"); then
    setup_fail "the mutation changed the artifact's field order"
  fi
  if [ "$pair" != "$field" ] &&
     ! cmp -s <(sorted_values "$valid_copy") <(sorted_values "$artifact_path"); then
    setup_fail "the pair exchange did not keep the artifact's values"
  fi
  mutated_value=$(value_of "$artifact_path" "$field")
  if [ "$mutated_value" = "$valid_value" ]; then
    setup_fail "the mutation of $field left its value unchanged"
  fi
fi

# The outer digest is repaired in the manifest: the artifact on disk is what
# the manifest now names, so a stale digest cannot be the reason the selector
# rejects it.  An absent artifact keeps the manifest's recorded digest, so its
# absence is the only change, and a stale-import run leaves the artifact and
# its digest untouched, so the imported source is the only change.
update_key=${artifact}_sha256
if [ "$absent_artifact" -eq 0 ] && [ "$stale_import" -eq 0 ]; then
  replace_value "$manifest" "$update_key" "$(sha "$artifact_path")"
  if [ "$(manifest_value "$update_key")" != "$(sha "$artifact_path")" ]; then
    setup_fail "the manifest does not carry the changed artifact's digest"
  fi
  if [ "$(sha "$artifact_path")" = "$(sha "$valid_copy")" ]; then
    setup_fail "the changed artifact has the valid artifact's digest"
  fi
fi

# --- the changed request --------------------------------------------------
tag=${mode#--}
if [ "$malformed" -eq 1 ]; then
  tag=$tag-$variant
fi
test_out=$outdir/$tag
test_record=$work/$tag.env
test_status=0
UNIT=$unit STRICT=$strict MANIFEST="$manifest" OUT="$test_out" \
  RECORD="$test_record" "$selector" \
  >"$work/test.stdout" 2>"$work/test.stderr" || test_status=$?
test_selected=$(value_of "$test_record" selected)
test_linked=$(link_target "$test_out")
test_reason=$(value_of "$test_record" reason)

if [ "$absent_artifact" -eq 1 ]; then
  what="the absent $field"
elif [ "$malformed" -eq 1 ]; then
  what="the artifact with $malformed_what"
elif [ "$stale_import" -eq 1 ]; then
  what="the copied imported source marked stale"
else
  what="$field changed from '$valid_value' to '$mutated_value'"
fi

if [ "$strict" -eq 0 ]; then
  # --- H2 / H4 / H7 / H9 -------------------------------------------------
  # The reason is an exact value, not merely a sentence different from the
  # control's: a changed field, a malformed artifact or a stale imported source
  # is rejected as an invalid certificate, and an absent artifact as a missing
  # one.
  if [ "$label" = H4 ]; then
    expected_reason='proof rejected: missing certificate; installed baseline fallback'
  else
    expected_reason='proof rejected: invalid certificate; installed baseline fallback'
  fi

  if [ "$test_status" -eq 0 ]; then
    ok "$label: the non-strict request with $what exited 0"
  else
    bad "$label: the non-strict request with $what exited $test_status"
  fi

  if [ "$test_selected" = baseline ]; then
    ok "$label: the record names the baseline"
  else
    bad "$label: the record names '${test_selected:-nothing}', not the baseline"
  fi

  if [ -n "$test_linked" ] && [ "$test_linked" = "$(manifest_value baseline)" ]; then
    ok "$label: the linker was given the baseline object"
  else
    bad "$label: the linker was given '${test_linked:-nothing}', not the baseline object"
  fi

  if [ "$test_linked" != "$(manifest_value candidate)" ]; then
    ok "$label: the linker was not given the candidate object"
  else
    bad "$label: the linker was given the candidate object"
  fi

  if [ "$test_reason" = "$expected_reason" ]; then
    ok "$label: the record's reason is the rejection of the refused certificate"
  else
    bad "$label: the record's reason is '${test_reason:-nothing}', not '$expected_reason'"
  fi
else
  # --- H1 / H3 / H5 / H6 -------------------------------------------------
  if [ "$test_status" -ne 0 ]; then
    ok "$label: the strict request with $what was refused with status $test_status"
  else
    bad "$label: the strict request with $what exited 0"
  fi

  if [ ! -e "$test_out" ]; then
    ok "$label: no executable was emitted"
  else
    bad "$label: an executable was emitted at $test_out"
  fi

  if [ -f "$test_record" ] && grep -qx "selected=$unit" "$test_record"; then
    bad "$label: the record names the $unit that was not certified"
  else
    ok "$label: no record names the $unit"
  fi

  if [ -z "$test_linked" ]; then
    ok "$label: no object was linked for the requested output"
  else
    bad "$label: the linker was given '${test_linked}' for the requested output"
  fi
fi

printf 'selector stdout: %s\n' "$(cat "$work/test.stdout")"
sed 's/^/selector stderr: /' "$work/test.stderr"
if [ -f "$test_record" ]; then
  printf 'selection record: %s\n' "$(tr '\n' ';' < "$test_record")"
fi

if [ "$fails" -ne 0 ]; then
  printf '%d assertion(s) failed\n' "$fails" >&2
  exit 1
fi
printf 'all assertions held\n'
