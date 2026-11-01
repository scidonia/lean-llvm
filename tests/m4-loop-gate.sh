#!/usr/bin/env bash
# Checks for the loop installation gate.
#
#   bash tests/m4-loop-gate.sh --strict
#   bash tests/m4-loop-gate.sh --fallback
#   bash tests/m4-loop-gate.sh --strict-conflict
#   bash tests/m4-loop-gate.sh --fallback-conflict
#
# Each mode drives the selector CLI (probes/install/select.sh) against an
# isolated manifest built in a temporary directory.  The tools the selector
# invokes are local shims in a private PATH: clang, ld, file, nm and leanc;
# lean, which answers `--version` only; and lake, which accepts the
# imported-graph rebuild, the source-rebuild check and the certificate producer
# and nothing else.  The remaining utilities (sha256sum, cut, sed and the rest)
# are the real core utilities, operating on temporary inputs.  The temporary
# tree mirrors the repository root the selector resolves the revision-bearing
# pin files from.  No compiler, linker, proof checker or service is reached,
# and nothing outside the temporary directory is written.
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
# accepted: the imported-graph rebuild of the proof module, the source-rebuild
# check, which succeeds without a proof system, and the certificate producer,
# which publishes the canonical certificate of the requested unit derived from
# the manifest inputs.  Any other invocation is refused.
cat > "$fakebin/lake" <<'SHIM'
#!/usr/bin/env bash
set -euo pipefail
. "$(dirname "$0")/fake.env"
if [ "${1:-}" = build ]; then
  [ "$#" -eq 2 ] && [ "$2" = LeanLLVM.Vellum.CommaMaskIR ] ||
    { echo "lake: unexpected build arguments: $*" >&2; exit 1; }
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

# The certificate's field values are derived from the files the manifest names,
# from the toolchain the selector observes and from the pinned proof data, so a
# fixture value cannot silently disagree with the input it claims.
axioms=$(
  sed -n 's/.*IR_refines. depends on axioms: \[\(.*\)\]/\1/p' \
    "$repo/LeanLLVMTest/Vellum.lean" |
    tr ',' '\n' | sed 's/^ *//; s/ *$//' | grep -v '^$' |
    LC_ALL=C sort | paste -sd, -
)
[ -n "$axioms" ] || { echo "SETUP: cannot read the pinned axiom set" >&2; exit 3; }
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

# The candidate certificate is valid in every G1--G4 run, so a refused loop
# cannot be explained by a missing or invalid certificate.
proof_baseline=$work/proofs/proof_baseline.env
proof_candidate=$work/proofs/proof_candidate.env
{
  printf 'proof_baseline=%s\n' "$proof_baseline"
  printf 'proof_candidate=%s\n' "$proof_candidate"
} >> "$manifest"

manifest_value() { # key
  sed -n "s/^$1=//p" "$manifest" | sed -n '1p'
}

write_certificate() { # path unit
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

# The canonical certificate of each unit is derived from the manifest inputs,
# and the producer shim publishes it.
write_certificate "$canonical/baseline.env" baseline
write_certificate "$canonical/candidate.env" candidate
(cd "$mirror" &&
  CERT_UNIT=baseline CERT_MANIFEST="$manifest" CERT_OUT="$proof_baseline" \
    lake env lean probes/install/InstallCertificate.lean)
(cd "$mirror" &&
  CERT_UNIT=candidate CERT_MANIFEST="$manifest" CERT_OUT="$proof_candidate" \
    lake env lean probes/install/InstallCertificate.lean)
cmp -s "$canonical/baseline.env" "$proof_baseline" ||
  { echo "SETUP: the producer's baseline certificate is not the derived one" >&2; exit 3; }
cmp -s "$canonical/candidate.env" "$proof_candidate" ||
  { echo "SETUP: the producer's candidate certificate is not the derived one" >&2; exit 3; }
{
  printf 'proof_baseline_sha256=%s\n' "$(sha "$proof_baseline")"
  printf 'proof_candidate_sha256=%s\n' "$(sha "$proof_candidate")"
} >> "$manifest"

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
