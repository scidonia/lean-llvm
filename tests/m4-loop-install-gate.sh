#!/usr/bin/env bash
# Checks for the certificate-bound loop installation gate.
#
#   bash tests/m4-loop-install-gate.sh --strict
#   bash tests/m4-loop-install-gate.sh --strict-theorem
#   bash tests/m4-loop-install-gate.sh --strict-hash
#   bash tests/m4-loop-install-gate.sh --fallback-hash
#
# Each mode drives the selector CLI (probes/install/select.sh) against an
# isolated manifest built in a temporary directory.  The tools the selector
# invokes are local shims in a private PATH: clang, ld, file, nm and leanc;
# lean, which answers `--version` only; and lake, which accepts the
# imported-graph rebuild of either proof module, the source-rebuild check of
# either module and the certificate producer, and nothing else.  The remaining
# utilities (sha256sum, cut, sed and the rest) are the real core utilities,
# operating on temporary inputs.  The temporary tree mirrors the repository
# root the selector resolves the revision-bearing pin files from.  No compiler,
# linker, proof checker or service is reached, and nothing outside the
# temporary directory is written.
#
# --strict is L1: a strict loop request whose certificate names the loop's own
# theorem, matches the loop object, its fixture and marker, and matches the
# baseline/candidate pair the manifest binds, must install the loop.  The
# certificate is the one the producer shim publishes for the loop, derived from
# the manifest inputs before anything is changed.
#
# --strict-theorem is L2: the same request against a certificate whose
# `theorem` field names `IR_refines`, the candidate-to-baseline statement,
# must be refused with the certificate reason, even after the manifest's digest
# of the certificate is rewritten to the changed bytes.
#
# --strict-hash is L3: the same request against a certificate whose
# `unit_object_sha256` value has been exchanged with its own
# `baseline_object_sha256` value, so every hash token remains in the file and
# only the field-to-file relation breaks, must be refused with the same reason.
#
# --fallback-hash is L4: the L3 certificate with `STRICT=0` must install the
# baseline and record the rejection as a fallback.
#
# Exit status: 0 when the scenario's assertions hold, 1 when one fails,
# 2 on bad usage, 3 when the fixture itself is not usable.
set -uo pipefail

usage() {
  echo "usage: bash tests/m4-loop-install-gate.sh --strict|--strict-theorem|--strict-hash|--fallback-hash" >&2
  exit 2
}

mode=${1:-}
case "$mode" in
  --strict|--strict-theorem|--strict-hash|--fallback-hash) ;;
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
  "$mirror/.lake/build/lib/lean/LeanLLVM/Vellum"
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
# accepted: the imported-graph rebuild of either proof module; the
# source-rebuild check of either module, which succeeds without a proof system;
# and the certificate producer, which publishes the canonical certificate of
# the requested unit derived from the manifest inputs.  Both proof modules are
# accepted unconditionally, so the gate is observed through the certificate and
# not through a stale import; that failure is covered by
# tests/m3-certificate-gate.sh.  Any other invocation is refused.
cat > "$fakebin/lake" <<'SHIM'
#!/usr/bin/env bash
set -euo pipefail
. "$(dirname "$0")/fake.env"
if [ "${1:-}" = build ]; then
  [ "$#" -eq 2 ] ||
    { echo "lake: unexpected build arguments: $*" >&2; exit 1; }
  case "$2" in
    LeanLLVM.Vellum.CommaMaskIR|LeanLLVM.Vellum.CommaMaskLoop) exit 0 ;;
    *) echo "lake: unexpected build target: $2" >&2; exit 1 ;;
  esac
fi
[ "${1:-}" = env ] && [ "${2:-}" = lean ] ||
  { echo "lake: only 'lake build' and 'lake env lean' are supported" >&2; exit 1; }
shift 2
if [ "${1:-}" = -o ]; then
  [ "$#" -eq 3 ] ||
    { echo "lake: unexpected source-check arguments: $*" >&2; exit 1; }
  case "$2:$3" in
    .lake/build/lib/lean/LeanLLVM/Vellum/CommaMaskIR.olean:LeanLLVM/Vellum/CommaMaskIR.lean)
      exit 0 ;;
    .lake/build/lib/lean/LeanLLVM/Vellum/CommaMaskLoop.olean:LeanLLVM/Vellum/CommaMaskLoop.lean)
      exit 0 ;;
  esac
  echo "lake: unexpected source-check arguments: $*" >&2
  exit 1
fi
[ "$#" -eq 1 ] && [ "$1" = probes/install/InstallCertificate.lean ] ||
  { echo "lake: unexpected producer arguments: $*" >&2; exit 1; }
case "${CERT_UNIT:-}" in
  baseline|candidate|loop) ;;
  *) echo "lake: CERT_UNIT must name baseline, candidate or loop" >&2; exit 1 ;;
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
covers: candidate-vs-baseline, loop-vs-candidate
RESULT: PASS
CERT

# The loop object must be exactly what a rebuild from its own fixture produces
# with the same tools: otherwise the selector's own rebuild check would reject
# the loop and the scenario would observe a fixture failure instead of the
# rule under test.
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

# The certificate's field values are derived from the files the manifest names,
# from the toolchain the selector observes and from the pinned proof data, so a
# fixture value cannot silently disagree with the input it claims.  Each
# certificate carries the checked axiom set of the theorem it names.
pinned_axioms() { # theorem name
  sed -n "s/.*$1. depends on axioms: \[\([^]]*\)\].*/\1/p" \
    "$repo/LeanLLVMTest/Vellum.lean" |
    tr ',' '\n' | sed 's/^ *//; s/ *$//' | grep -v '^$' |
    LC_ALL=C sort | paste -sd, -
}
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
  echo "SETUP: cannot compute the toolchain revision" >&2
  exit 3
fi
helper_revision=$(cd "$mirror" && bash "$mirror/probes/install/toolchain-id.sh")
if [ "$helper_revision" != "$toolchain_revision" ]; then
  echo "SETUP: the toolchain helper and the artifact's toolchain revision disagree" >&2
  exit 3
fi
schema_version=leanllvm-install-v1

# The manifest binds the loop's own theorem beside the global one, which keeps
# naming the candidate-to-baseline statement for every request.
cat > "$manifest" <<EOF
kind=proof-bound
target=$target
triple=$target
symbol=leanllvm_comma_mask8
marker=leanllvm_impl_id
contract=LeanLLVM.Vellum.commaContract
theorem=LeanLLVM.Vellum.CommaMaskIR.IR_refines
loop_theorem=LeanLLVM.Vellum.CommaMaskLoop.loop_refines_candidate_within
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
proof_loop=$proofs/proof_loop.env
{
  printf 'proof_baseline=%s\n' "$proof_baseline"
  printf 'proof_candidate=%s\n' "$proof_candidate"
  printf 'proof_loop=%s\n' "$proof_loop"
} >> "$manifest"

manifest_value() { # key
  sed -n "s/^$1=//p" "$manifest" | sed -n '1p'
}

# The certificate a unit's producer publishes: every field derived from the
# file or input the field names.  The theorem is the one bound to that unit in
# the manifest, and the axiom set is that theorem's own pinned footprint.
write_certificate() { # path unit
  local path=$1 art_unit=$2 theorem_key=theorem axioms_value
  if [ "$art_unit" = loop ]; then
    theorem_key=loop_theorem
  fi
  axioms_value=$(pinned_axioms "$(manifest_value "$theorem_key" | sed 's/.*\.//')")
  [ -n "$axioms_value" ] ||
    { echo "SETUP: cannot read the pinned axiom set for $art_unit" >&2; exit 3; }
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
    printf 'theorem=%s\n' "$(manifest_value "$theorem_key")"
    printf 'axioms=%s\n' "$axioms_value"
    printf 'contract=%s\n' "$(manifest_value contract)"
    printf 'target_triple=%s\n' "$target"
    printf 'data_layout=%s\n' "$datalayout"
    printf 'toolchain_revision=%s\n' "$toolchain_revision"
  } > "$path"
}

# The canonical certificate of each unit is derived from the manifest inputs
# before any change is made, and the producer shim publishes it.  The fixture
# records the producer's bytes, so the certificate the selector re-derives is
# compared with what the manifest binds.
write_certificate "$canonical/baseline.env" baseline
write_certificate "$canonical/candidate.env" candidate
write_certificate "$canonical/loop.env" loop
(cd "$mirror" &&
  CERT_UNIT=baseline CERT_MANIFEST="$manifest" CERT_OUT="$proof_baseline" \
    lake env lean probes/install/InstallCertificate.lean)
(cd "$mirror" &&
  CERT_UNIT=candidate CERT_MANIFEST="$manifest" CERT_OUT="$proof_candidate" \
    lake env lean probes/install/InstallCertificate.lean)
(cd "$mirror" &&
  CERT_UNIT=loop CERT_MANIFEST="$manifest" CERT_OUT="$proof_loop" \
    lake env lean probes/install/InstallCertificate.lean)
cmp -s "$canonical/baseline.env" "$proof_baseline" ||
  { echo "SETUP: the producer's baseline certificate is not the derived one" >&2; exit 3; }
cmp -s "$canonical/candidate.env" "$proof_candidate" ||
  { echo "SETUP: the producer's candidate certificate is not the derived one" >&2; exit 3; }
cmp -s "$canonical/loop.env" "$proof_loop" ||
  { echo "SETUP: the producer's loop certificate is not the derived one" >&2; exit 3; }
# The digest of the certificate the fixture constructed, captured before any
# mode changes its bytes, so the selection record is compared with the
# certificate the producer published and not with a file a later step rewrote.
loop_proof_digest=$(sha "$proof_loop")
{
  printf 'proof_baseline_sha256=%s\n' "$(sha "$proof_baseline")"
  printf 'proof_candidate_sha256=%s\n' "$(sha "$proof_candidate")"
  printf 'proof_loop_sha256=%s\n' "$(sha "$proof_loop")"
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

# --- affirmative control --------------------------------------------------
# A strict baseline selection from the same input must link the baseline object
# and leave an output at the requested path, so the fake link and output
# detection is known to work before the same detector is used to judge the
# loop.
control_out=$outdir/control
control_record=$work/control.env
control_status=0
UNIT=baseline STRICT=1 MANIFEST="$manifest" OUT="$control_out" \
  RECORD="$control_record" "$selector" \
  >"$work/control.stdout" 2>"$work/control.stderr" || control_status=$?
control_selected=$(record_value "$control_record" selected)
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

# The four facts that hold when a selection installs the loop from the matching
# certificate.  On --strict they are the scenario's own outcome; in the other
# modes they are the control that shows the certificate under test was valid
# before the change.
assert_loop_install() { # label status out record
  local label=$1 status=$2 out=$3 record=$4 selected linked proof_sha
  selected=$(record_value "$record" selected)
  linked=$(link_target "$out")
  proof_sha=$(record_value "$record" proof_sha256)

  if [ "$status" -eq 0 ]; then
    ok "$label: the strict loop request exited 0"
  else
    bad "$label: the strict loop request exited $status"
  fi

  if [ "$selected" = loop ]; then
    ok "$label: the selection record names the loop"
  else
    bad "$label: the selection record names '${selected:-nothing}'"
  fi

  if [ "$linked" = "$fixtures/loop.o" ]; then
    ok "$label: the linker was given the loop object"
  else
    bad "$label: the linker was given '${linked:-nothing}', not the loop object"
  fi

  if [ -n "$proof_sha" ] && [ "$proof_sha" = "$loop_proof_digest" ]; then
    ok "$label: the record's proof_sha256 is the loop certificate's digest"
  else
    bad "$label: the record's proof_sha256 is '${proof_sha:-nothing}', not the digest of $proof_loop"
  fi
}

# The valid loop selection: the certificate still carries the values its fields
# claim, so the loop must be installable from it.
valid_out=$outdir/valid
valid_record=$work/valid.env
valid_status=0
UNIT=loop STRICT=1 MANIFEST="$manifest" OUT="$valid_out" \
  RECORD="$valid_record" "$selector" \
  >"$work/valid.stdout" 2>"$work/valid.stderr" || valid_status=$?

if [ "$mode" = --strict ]; then
  # --- L1 ----------------------------------------------------------------
  assert_loop_install L1 "$valid_status" "$valid_out" "$valid_record"
  under_test_record=$valid_record
  under_test_stdout=$work/valid.stdout
  under_test_stderr=$work/valid.stderr
else
  assert_loop_install control "$valid_status" "$valid_out" "$valid_record"

  # --- the one change ----------------------------------------------------
  # L2 names the wrong theorem for the unit.  L3 and L4 exchange the
  # certificate's `unit_object_sha256` value with its own
  # `baseline_object_sha256` value, so every hash token stays in the file and
  # only the field-to-file relation breaks.  Either way the manifest's digest
  # of the certificate is then rewritten, so a stale outer digest cannot
  # explain the result.
  case "$mode" in
    --strict-theorem)
      replace_value "$proof_loop" theorem LeanLLVM.Vellum.CommaMaskIR.IR_refines
      ;;
    --strict-hash|--fallback-hash)
      loop_hash=$(value_of "$proof_loop" unit_object_sha256)
      baseline_hash=$(value_of "$proof_loop" baseline_object_sha256)
      if [ -z "$loop_hash" ] || [ -z "$baseline_hash" ] ||
         [ "$loop_hash" = "$baseline_hash" ]; then
        echo "SETUP: the loop certificate's object hashes are not distinct" >&2
        exit 3
      fi
      replace_value "$proof_loop" unit_object_sha256 "$baseline_hash"
      replace_value "$proof_loop" baseline_object_sha256 "$loop_hash"
      ;;
  esac
  replace_value "$manifest" proof_loop_sha256 "$(sha "$proof_loop")"

  # --- the changed request -----------------------------------------------
  case "$mode" in
    --strict-theorem|--strict-hash) test_strict=1 ;;
    --fallback-hash) test_strict=0 ;;
  esac
  tag=${mode#--}
  test_out=$outdir/$tag
  test_record=$work/$tag.env
  rm -f "$test_out" "$test_record"
  test_status=0
  UNIT=loop STRICT=$test_strict MANIFEST="$manifest" OUT="$test_out" \
    RECORD="$test_record" "$selector" \
    >"$work/$tag.stdout" 2>"$work/$tag.stderr" || test_status=$?

  if [ "$mode" = --fallback-hash ]; then
    # --- L4 --------------------------------------------------------------
    selected=$(record_value "$test_record" selected)
    reason=$(record_value "$test_record" reason)
    linked=$(link_target "$test_out")

    if [ "$test_status" -eq 0 ]; then
      ok "L4: the non-strict loop request exited 0"
    else
      bad "L4: the non-strict loop request exited $test_status"
    fi

    if [ "$selected" = baseline ]; then
      ok "L4: the selection record names the baseline"
    else
      bad "L4: the selection record names '${selected:-nothing}'"
    fi

    if [ "$linked" = "$fixtures/baseline.o" ]; then
      ok "L4: the linker was given the baseline object"
    else
      bad "L4: the linker was given '${linked:-nothing}', not the baseline object"
    fi

    if [ "$linked" != "$fixtures/loop.o" ]; then
      ok "L4: the linked object is not the loop"
    else
      bad "L4: the linked object is the loop"
    fi

    if [ "$reason" = 'proof rejected: invalid certificate; installed baseline fallback' ]; then
      ok "L4: the record's reason is the invalid-certificate fallback"
    else
      bad "L4: the record's reason is '${reason:-nothing}', not the invalid-certificate fallback"
    fi

    under_test_record=$test_record
    under_test_stdout=$work/$tag.stdout
    under_test_stderr=$work/$tag.stderr
  else
    # --- L2 and L3 -------------------------------------------------------
    label=$([ "$mode" = --strict-theorem ] && printf 'L2' || printf 'L3')
    selected=$(record_value "$test_record" selected)

    if [ "$test_status" -ne 0 ]; then
      ok "$label: the strict loop request was refused with status $test_status"
    else
      bad "$label: the strict loop request exited 0, so a certificate that disagrees with its unit was accepted"
    fi

    if [ ! -e "$test_out" ]; then
      ok "$label: no loop executable was emitted"
    else
      bad "$label: a loop executable was emitted at $test_out"
    fi

    if grep -qx 'selected=loop' "$test_record" 2>/dev/null; then
      bad "$label: the selection record names the loop"
    else
      ok "$label: the selection record does not name the loop"
    fi

    if grep -qx '  - proof certificate invalid' "$work/$tag.stderr"; then
      ok "$label: the selector's stderr carries the certificate-invalid reason"
    else
      bad "$label: the selector's stderr does not carry the certificate-invalid reason"
    fi

    under_test_record=$test_record
    under_test_stdout=$work/$tag.stdout
    under_test_stderr=$work/$tag.stderr
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
