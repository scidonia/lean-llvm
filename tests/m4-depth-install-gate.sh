#!/usr/bin/env bash
# Checks for the installed depth counter's selector decisions.
#
#   bash tests/m4-depth-install-gate.sh --strict
#   bash tests/m4-depth-install-gate.sh --strict-theorem
#   bash tests/m4-depth-install-gate.sh --strict-hash
#   bash tests/m4-depth-install-gate.sh --strict-contract
#   bash tests/m4-depth-install-gate.sh --fallback-hash
#
# Each mode drives the selector CLI (probes/install/select.sh) against an
# isolated manifest built in a temporary directory.  The tools the selector
# invokes are local shims in a private PATH: clang, ld, file, nm and leanc;
# lean, which answers `--version` only; and lake, which accepts the
# proof-module rebuilds of the depth module (and the comma-mask module the
# producer imports) and the certificate producer, and nothing else.  The
# remaining utilities are the real core utilities, operating on temporary
# inputs.  The temporary tree mirrors the repository root the selector resolves
# the revision-bearing pin files from.  No compiler, linker, proof checker or
# service is reached, and nothing outside the temporary directory is written.
#
# --strict is D1: a strict depth request whose certificate names
# `depth_count_refines` and `depthContract`, matches the depth object, its
# fixture (`tests/v16/depth_count.ll`) and marker, and matches the
# baseline/candidate pair the manifest binds, must install the unit.  The
# selection record must name `depth_count`, its `depth_count_sha256` must equal
# the manifest's and the object's own digest, and its `proof_sha256` must equal
# the certificate's digest.
#
# --strict-theorem is D2: the same request against a certificate whose
# `theorem` field names `IR_refines`, another unit's statement, must be refused
# and the refusal must name the value it used, even after the manifest's digest
# of the certificate is rewritten to the changed bytes.
#
# --strict-hash is D3: the same request against a certificate whose
# `unit_object_sha256` value has been exchanged with its own
# `baseline_object_sha256` value, so every hash token remains in the file and
# only the field-to-file relation breaks, must be refused with the same reason.
#
# --strict-contract is D4: the same request against a certificate whose
# `contract` field names `LeanLLVM.Refinement.commaContract`, another unit's
# contract, must be refused and the refusal must name it.  This is the property
# the unit-aware expected names introduce.
#
# --fallback-hash is D5: the D3 certificate with `STRICT=0` must install the
# baseline and record the rejection as a fallback.
#
# Exit status: 0 when the scenario's assertions hold, 1 when one fails,
# 2 on bad usage, 3 when the fixture itself is not usable.
set -uo pipefail

usage() {
  echo "usage: bash tests/m4-depth-install-gate.sh --strict|--strict-theorem|--strict-hash|--strict-contract|--fallback-hash" >&2
  exit 2
}

mode=${1:-}
case "$mode" in
  --strict|--strict-theorem|--strict-hash|--strict-contract|--fallback-hash) ;;
  *) usage ;;
esac
[ "$#" -eq 1 ] || usage

repo=$(cd "$(dirname "$0")/.." && pwd)
selector_source=$repo/probes/install/select.sh
ir=$repo/probes/install/ir
depth_fixture_source=$repo/tests/v16/depth_count.ll

for path in "$selector_source" "$ir/baseline.ll" "$ir/candidate.ll" \
  "$ir/loop.ll" "$ir/marker_baseline.ll" "$ir/marker_candidate.ll" \
  "$ir/marker_loop.ll" "$ir/marker_depth_count.ll" "$depth_fixture_source"; do
  [ -e "$path" ] || { echo "SETUP: absent: $path" >&2; exit 3; }
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
# symbols the unit exports, so nm and the selector's symbol checks observe a
# fixed per-object answer.  The depth unit's object exports `depth_count`; the
# marker exports `leanllvm_impl_id`; the comma-mask units export the seam.
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
    depth_count) printf 'T depth_count\n' ;;
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

# file: ELF classification for the fake unit objects only.
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
# the symbols the object holds, and an early-closed pipe is tolerated.
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

# lake: the proof checker the selector drives.  Two command forms are
# accepted: the rebuild of a proof module, and the certificate producer, which
# publishes the canonical certificate of the requested unit derived from the
# manifest inputs.  The rebuilds are accepted unconditionally, so the gate is
# observed through the certificate and not through a stale import.
cat > "$fakebin/lake" <<'SHIM'
#!/usr/bin/env bash
set -euo pipefail
. "$(dirname "$0")/fake.env"
if [ "${1:-}" = build ]; then
  [ "$#" -eq 2 ] ||
    { echo "lake: unexpected build arguments: $*" >&2; exit 1; }
  case "$2" in
    LeanLLVM.Refinement.CommaMaskIR|LeanLLVM.Refinement.CommaMaskLoop|\
    LeanLLVM.Refinement.DepthCountRefine) exit 0 ;;
    *) echo "lake: unexpected build target: $2" >&2; exit 1 ;;
  esac
fi
[ "${1:-}" = env ] && [ "${2:-}" = lean ] ||
  { echo "lake: only 'lake build' and 'lake env lean' are supported" >&2; exit 1; }
shift 2
[ "$#" -eq 1 ] && [ "$1" = probes/install/InstallCertificate.lean ] ||
  { echo "lake: unexpected producer arguments: $*" >&2; exit 1; }
case "${CERT_UNIT:-}" in
  baseline|candidate|loop|depth_count) ;;
  *) echo "lake: CERT_UNIT must name baseline, candidate, loop or depth_count" >&2; exit 1 ;;
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
# the project olean directory the selector rebuilds the proof modules in.
for pinned in lean-toolchain flake.nix flake.lock lakefile.toml \
  lake-manifest.json; do
  cp "$repo/$pinned" "$mirror/$pinned"
done
cp "$selector_source" "$selector"
chmod +x "$selector"
cp "$repo/probes/install/InstallCertificate.lean" \
  "$mirror/probes/install/InstallCertificate.lean"
if [ -f "$repo/probes/install/toolchain-id.sh" ]; then
  cp "$repo/probes/install/toolchain-id.sh" \
    "$mirror/probes/install/toolchain-id.sh"
else
  echo "SETUP: absent: probes/install/toolchain-id.sh" >&2
  exit 3
fi

# --- fixtures -------------------------------------------------------------
# Each non-depth fixture is the repository's IR, copied; the depth unit's
# fixture is the census text in tests/v16.  Each object is built with the same
# basenames and command sequence `build.sh` uses, so the manifest values are
# computed from the fixture bytes and from what the selector will rebuild,
# never typed by hand.
cp "$ir/baseline.ll" "$fixtures/ir/baseline.ll"
cp "$ir/candidate.ll" "$fixtures/ir/candidate.ll"
cp "$ir/loop.ll" "$fixtures/ir/loop.ll"
cp "$ir/marker_baseline.ll" "$fixtures/ir/marker_baseline.ll"
cp "$ir/marker_candidate.ll" "$fixtures/ir/marker_candidate.ll"
cp "$ir/marker_loop.ll" "$fixtures/ir/marker_loop.ll"
cp "$ir/marker_depth_count.ll" "$fixtures/ir/marker_depth_count.ll"
cp "$depth_fixture_source" "$fixtures/ir/depth_count.ll"

build_unit() { # unit
  local unit=$1
  mkdir -p "$units/$unit"
  cp "$fixtures/ir/$unit.ll" "$units/$unit/$unit.ll"
  cp "$fixtures/ir/marker_$unit.ll" "$units/$unit/marker_$unit.ll"
  (cd "$units/$unit" &&
    clang -c "$unit.ll" -o "$unit.o" &&
    clang -c "marker_$unit.ll" -o "marker_$unit.o" &&
    ld -r "$unit.o" "marker_$unit.o" -o unit.o)
  cp "$units/$unit/unit.o" "$fixtures/$unit.o"
}

for unit in baseline candidate loop depth_count; do
  build_unit "$unit"
done

# The callers: the comma-mask caller imports the seam, the depth caller imports
# the ABI the depth fixture defines.
printf 'OBJ caller\nU leanllvm_comma_mask8\n' > "$fixtures/caller.o"
printf 'OBJ depth_caller\nU depth_count\n' > "$fixtures/depth_caller.o"

cat > "$fixtures/differential.txt" <<'CERT'
kind: differential
symbol: leanllvm_comma_mask8
bodies: proved-baseline proved-candidate proved-loop lean-baseline lean-candidate
theorem: LeanLLVM.Refinement.CommaMaskIR.IR_refines
covers: candidate-vs-baseline, loop-vs-candidate
RESULT: PASS
CERT

sha() { sha256sum "$1" | cut -d' ' -f1; }

# The certificate's field values are derived from the files the manifest names,
# from the toolchain the selector observes and from the pinned proof data.
pinned_axioms() { # theorem name
  # Lean wraps a rendered `#print axioms` message at its print width, so the
  # pin can span several source lines.  Join them before matching: a reader that
  # assumes one line stops matching, silently, the moment the name or the set
  # crosses the width.
  tr '\n' ' ' < "$repo/LeanLLVMTest/Refinement.lean" |
    sed -n "s/.*$1. depends on axioms: \[\([^]]*\)\].*/\1/p" |
    tr ',' '\n' | sed 's/^ *//; s/ *$//' | grep -v '^$' |
    LC_ALL=C sort | paste -sd, -
}
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

# The manifest binds each unit's own theorem and contract beside the global
# comma-mask pair.
cat > "$manifest" <<EOF
kind=proof-bound
target=$target
triple=$target
symbol=leanllvm_comma_mask8
marker=leanllvm_impl_id
contract=LeanLLVM.Refinement.commaContract
theorem=LeanLLVM.Refinement.CommaMaskIR.IR_refines
loop_theorem=LeanLLVM.Refinement.CommaMaskLoop.loop_refines_candidate_within
depth_count_symbol=depth_count
depth_contract=LeanLLVM.Refinement.DepthCountRefine.depthContract
depth_count_theorem=LeanLLVM.Refinement.DepthCountRefine.depth_count_refines
attributes=reject
datalayout=$datalayout
target_features=none
baseline_fixture=$fixtures/ir/baseline.ll
candidate_fixture=$fixtures/ir/candidate.ll
loop_fixture=$fixtures/ir/loop.ll
depth_count_fixture=$fixtures/ir/depth_count.ll
baseline_marker=$fixtures/ir/marker_baseline.ll
candidate_marker=$fixtures/ir/marker_candidate.ll
loop_marker=$fixtures/ir/marker_loop.ll
depth_count_marker=$fixtures/ir/marker_depth_count.ll
baseline_fixture_sha256=$(sha "$fixtures/ir/baseline.ll")
candidate_fixture_sha256=$(sha "$fixtures/ir/candidate.ll")
loop_fixture_sha256=$(sha "$fixtures/ir/loop.ll")
depth_count_fixture_sha256=$(sha "$fixtures/ir/depth_count.ll")
baseline_marker_sha256=$(sha "$fixtures/ir/marker_baseline.ll")
candidate_marker_sha256=$(sha "$fixtures/ir/marker_candidate.ll")
loop_marker_sha256=$(sha "$fixtures/ir/marker_loop.ll")
depth_count_marker_sha256=$(sha "$fixtures/ir/marker_depth_count.ll")
caller=$fixtures/caller.o
baseline=$fixtures/baseline.o
candidate=$fixtures/candidate.o
loop=$fixtures/loop.o
depth_count=$fixtures/depth_count.o
depth_caller=$fixtures/depth_caller.o
differential=$fixtures/differential.txt
caller_sha256=$(sha "$fixtures/caller.o")
baseline_sha256=$(sha "$fixtures/baseline.o")
candidate_sha256=$(sha "$fixtures/candidate.o")
loop_sha256=$(sha "$fixtures/loop.o")
depth_count_sha256=$(sha "$fixtures/depth_count.o")
depth_caller_sha256=$(sha "$fixtures/depth_caller.o")
differential_sha256=$(sha "$fixtures/differential.txt")
EOF

proof_baseline=$proofs/proof_baseline.env
proof_candidate=$proofs/proof_candidate.env
proof_loop=$proofs/proof_loop.env
proof_depth_count=$proofs/proof_depth_count.env
{
  printf 'proof_baseline=%s\n' "$proof_baseline"
  printf 'proof_candidate=%s\n' "$proof_candidate"
  printf 'proof_loop=%s\n' "$proof_loop"
  printf 'proof_depth_count=%s\n' "$proof_depth_count"
} >> "$manifest"

manifest_value() { # key
  sed -n "s/^$1=//p" "$manifest" | sed -n '1p'
}

# The certificate a unit's producer publishes: every field derived from the
# file or input the field names.  The theorem and contract are the ones bound
# to that unit in the manifest, and the axiom set is that theorem's own pinned
# footprint.
write_certificate() { # path unit
  local path=$1 art_unit=$2 theorem_key=theorem contract_key=contract axioms_value
  case "$art_unit" in
    loop) theorem_key=loop_theorem ;;
    depth_count)
      theorem_key=depth_count_theorem
      contract_key=depth_contract
      ;;
  esac
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
    printf 'contract=%s\n' "$(manifest_value "$contract_key")"
    printf 'target_triple=%s\n' "$target"
    printf 'data_layout=%s\n' "$datalayout"
    printf 'toolchain_revision=%s\n' "$toolchain_revision"
  } > "$path"
}

write_certificate "$canonical/baseline.env" baseline
write_certificate "$canonical/candidate.env" candidate
write_certificate "$canonical/loop.env" loop
write_certificate "$canonical/depth_count.env" depth_count
(cd "$mirror" &&
  CERT_UNIT=baseline CERT_MANIFEST="$manifest" CERT_OUT="$proof_baseline" \
    lake env lean probes/install/InstallCertificate.lean)
(cd "$mirror" &&
  CERT_UNIT=candidate CERT_MANIFEST="$manifest" CERT_OUT="$proof_candidate" \
    lake env lean probes/install/InstallCertificate.lean)
(cd "$mirror" &&
  CERT_UNIT=loop CERT_MANIFEST="$manifest" CERT_OUT="$proof_loop" \
    lake env lean probes/install/InstallCertificate.lean)
(cd "$mirror" &&
  CERT_UNIT=depth_count CERT_MANIFEST="$manifest" \
    CERT_OUT="$proof_depth_count" \
    lake env lean probes/install/InstallCertificate.lean)
for unit in baseline candidate loop depth_count; do
  cmp -s "$canonical/$unit.env" "$proofs/proof_$unit.env" ||
    { echo "SETUP: the producer's $unit certificate is not the derived one" >&2; exit 3; }
done
depth_proof_digest=$(sha "$proof_depth_count")
{
  printf 'proof_baseline_sha256=%s\n' "$(sha "$proof_baseline")"
  printf 'proof_candidate_sha256=%s\n' "$(sha "$proof_candidate")"
  printf 'proof_loop_sha256=%s\n' "$(sha "$proof_loop")"
  printf 'proof_depth_count_sha256=%s\n' "$(sha "$proof_depth_count")"
} >> "$manifest"

set +e
trap - ERR

# --- assertions -----------------------------------------------------------
fails=0
ok() { printf 'ok: %s\n' "$*"; }
bad() { printf 'FAIL: %s\n' "$*" >&2; fails=$((fails + 1)); }

value_of() { # file key
  [ -f "$1" ] || return 0
  sed -n "s/^$2=//p" "$1" 2>/dev/null | sed -n '1p'
}
record_value() { value_of "$1" "$2"; }

replace_value() { # file key value
  local file=$1 key=$2 value=$3
  awk -v k="$key" -v v="$value" '
    index($0, k "=") == 1 { print k "=" v; next }
    { print }
  ' "$file" > "$file.tmp" && mv "$file.tmp" "$file"
}

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
# depth unit.
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

assert_depth_install() { # label status out record
  local label=$1 status=$2 out=$3 record=$4 selected linked proof_sha object_sha
  selected=$(record_value "$record" selected)
  linked=$(link_target "$out")
  proof_sha=$(record_value "$record" proof_sha256)
  object_sha=$(record_value "$record" depth_count_sha256)

  if [ "$status" -eq 0 ]; then
    ok "$label: the strict depth request exited 0"
  else
    bad "$label: the strict depth request exited $status"
  fi

  if [ "$selected" = depth_count ]; then
    ok "$label: the selection record names depth_count"
  else
    bad "$label: the selection record names '${selected:-nothing}'"
  fi

  if [ "$linked" = "$fixtures/depth_count.o" ]; then
    ok "$label: the linker was given the depth object"
  else
    bad "$label: the linker was given '${linked:-nothing}', not the depth object"
  fi

  if [ -n "$proof_sha" ] && [ "$proof_sha" = "$depth_proof_digest" ]; then
    ok "$label: the record's proof_sha256 is the depth certificate's digest"
  else
    bad "$label: the record's proof_sha256 is '${proof_sha:-nothing}', not the digest of $proof_depth_count"
  fi

  if [ -n "$object_sha" ] &&
     [ "$object_sha" = "$(manifest_value depth_count_sha256)" ] &&
     [ "$object_sha" = "$(sha "$fixtures/depth_count.o")" ]; then
    ok "$label: the record's depth_count_sha256 is the manifest's and the object's digest"
  else
    bad "$label: the record's depth_count_sha256 is '${object_sha:-nothing}', not the manifest's $(manifest_value depth_count_sha256)"
  fi
}

# The valid depth selection: the certificate carries the values its fields
# claim, so the unit must be installable from it.  In every mode this is the
# affirmative control that shows the certificate under test was valid before
# the one change.
valid_out=$outdir/valid
valid_record=$work/valid.env
valid_status=0
UNIT=depth_count STRICT=1 MANIFEST="$manifest" OUT="$valid_out" \
  RECORD="$valid_record" "$selector" \
  >"$work/valid.stdout" 2>"$work/valid.stderr" || valid_status=$?

if [ "$mode" = --strict ]; then
  assert_depth_install D1 "$valid_status" "$valid_out" "$valid_record"
  under_test_record=$valid_record
  under_test_stdout=$work/valid.stdout
  under_test_stderr=$work/valid.stderr
else
  assert_depth_install control "$valid_status" "$valid_out" "$valid_record"

  # --- the one change ----------------------------------------------------
  # D2 names another unit's theorem.  D3 and D5 exchange the certificate's
  # `unit_object_sha256` value with its own `baseline_object_sha256` value, so
  # every hash token stays in the file and only the field-to-file relation
  # breaks.  D4 names another unit's contract.  Either change then has the
  # manifest's digest of the certificate rewritten, so a stale outer digest
  # cannot explain the result.
  case "$mode" in
    --strict-theorem)
      replace_value "$proof_depth_count" theorem \
        LeanLLVM.Refinement.CommaMaskIR.IR_refines
      ;;
    --strict-contract)
      replace_value "$proof_depth_count" contract \
        LeanLLVM.Refinement.commaContract
      ;;
    --strict-hash|--fallback-hash)
      depth_hash=$(value_of "$proof_depth_count" unit_object_sha256)
      baseline_hash=$(value_of "$proof_depth_count" baseline_object_sha256)
      if [ -z "$depth_hash" ] || [ -z "$baseline_hash" ] ||
         [ "$depth_hash" = "$baseline_hash" ]; then
        echo "SETUP: the depth certificate's object hashes are not distinct" >&2
        exit 3
      fi
      replace_value "$proof_depth_count" unit_object_sha256 "$baseline_hash"
      replace_value "$proof_depth_count" baseline_object_sha256 "$depth_hash"
      ;;
  esac
  replace_value "$manifest" proof_depth_count_sha256 \
    "$(sha "$proof_depth_count")"

  case "$mode" in
    --strict-theorem|--strict-hash|--strict-contract) test_strict=1 ;;
    --fallback-hash) test_strict=0 ;;
  esac
  tag=${mode#--}
  test_out=$outdir/$tag
  test_record=$work/$tag.env
  rm -f "$test_out" "$test_record"
  test_status=0
  UNIT=depth_count STRICT=$test_strict MANIFEST="$manifest" OUT="$test_out" \
    RECORD="$test_record" "$selector" \
    >"$work/$tag.stdout" 2>"$work/$tag.stderr" || test_status=$?

  if [ "$mode" = --fallback-hash ]; then
    # --- D5 --------------------------------------------------------------
    selected=$(record_value "$test_record" selected)
    reason=$(record_value "$test_record" reason)
    linked=$(link_target "$test_out")

    if [ "$test_status" -eq 0 ]; then
      ok "D5: the non-strict depth request exited 0"
    else
      bad "D5: the non-strict depth request exited $test_status"
    fi

    if [ "$selected" = baseline ]; then
      ok "D5: the selection record names the baseline"
    else
      bad "D5: the selection record names '${selected:-nothing}'"
    fi

    if [ "$linked" = "$fixtures/baseline.o" ]; then
      ok "D5: the linker was given the baseline object"
    else
      bad "D5: the linker was given '${linked:-nothing}', not the baseline object"
    fi

    if [ "$linked" != "$fixtures/depth_count.o" ]; then
      ok "D5: the linked object is not the depth unit"
    else
      bad "D5: the linked object is the depth unit"
    fi

    if [ "$reason" = 'proof rejected: invalid certificate; installed baseline fallback' ]; then
      ok "D5: the record's reason is the invalid-certificate fallback"
    else
      bad "D5: the record's reason is '${reason:-nothing}', not the invalid-certificate fallback"
    fi

    under_test_record=$test_record
    under_test_stdout=$work/$tag.stdout
    under_test_stderr=$work/$tag.stderr
  else
    # --- D2, D3 and D4 ---------------------------------------------------
    case "$mode" in
      --strict-theorem) label=D2 ;;
      --strict-hash) label=D3 ;;
      --strict-contract) label=D4 ;;
    esac
    selected=$(record_value "$test_record" selected)

    if [ "$test_status" -ne 0 ]; then
      ok "$label: the strict depth request was refused with status $test_status"
    else
      bad "$label: the strict depth request exited 0, so a certificate that disagrees with its unit was accepted"
    fi

    if [ ! -e "$test_out" ]; then
      ok "$label: no depth executable was emitted"
    else
      bad "$label: a depth executable was emitted at $test_out"
    fi

    if grep -qx 'selected=depth_count' "$test_record" 2>/dev/null; then
      bad "$label: the selection record names depth_count"
    else
      ok "$label: the selection record does not name depth_count"
    fi

    if grep -qx '  - proof certificate invalid' "$work/$tag.stderr"; then
      ok "$label: the selector's stderr carries the certificate-invalid reason"
    else
      bad "$label: the selector's stderr does not carry the certificate-invalid reason"
    fi

    case "$mode" in
      --strict-theorem)
        expected_detail="  - proof certificate detail: theorem 'LeanLLVM.Refinement.CommaMaskIR.IR_refines' is not the unit's theorem 'LeanLLVM.Refinement.DepthCountRefine.depth_count_refines'"
        ;;
      --strict-contract)
        expected_detail="  - proof certificate detail: contract 'LeanLLVM.Refinement.commaContract' is not the unit's contract 'LeanLLVM.Refinement.DepthCountRefine.depthContract'"
        ;;
    esac
    if [ -n "${expected_detail:-}" ]; then
      if grep -qxF "$expected_detail" "$work/$tag.stderr"; then
        ok "$label: the refusal names the wrong field value"
      else
        bad "$label: the refusal does not name '$expected_detail'"
      fi
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
