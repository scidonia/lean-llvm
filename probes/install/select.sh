#!/usr/bin/env bash
# Verify a replacement unit against its manifest and link one body.
#
#   MANIFEST=... OUT=... RECORD=... STRICT=1 ./select.sh
#
# A unit is accepted only when
#   * the request names a known unit, and the manifest names the installation
#     contract and theorem exactly: the only checked statement is
#     `IR_refines` over the candidate and the baseline, so `UNIT=loop` is
#     always refused as an installation request, strict or not;
#   * every recorded hash matches: caller, unit objects, the differential
#     transcript, and the four fixture inputs (baseline/candidate body and
#     marker);
#   * each unit object is rebuilt from its fixtures and the rebuild matches the
#     installed bytes, so the object is the one the parser pinned;
#   * the target equals the manifest's `target` and `triple` and the triple
#     clang reports, and the data layout equals clang's;
#   * the requested unit's installation certificate is present, its manifest
#     digest matches its bytes, and it parses as closed data: exactly the
#     seventeen fields, in order, once each, with no unknown line, no extra
#     delimiter and one terminal newline;
#   * every certificate field equals the input it claims: the selected unit's
#     object, fixture and marker; both operands' objects, fixtures and markers;
#     the manifest's theorem and contract; the observed target and layout; the
#     checked axiom set; and the toolchain revision the repository's own
#     `toolchain-id.sh` prints now;
#   * the Lean producer, run after the imported proof graph is rebuilt from
#     current project source and the proof module is re-elaborated from source,
#     reproduces the certificate byte for byte.  That is the kernel re-check:
#     a changed field, a stale proof module or a stale imported proof source
#     fails here even if the certificate's manifest digest was rewritten;
#   * the objects are ELF64 and export the seam and marker symbols, and the
#     caller imports the seam.
#
# The differential transcript is a runtime comparison, not a proof of any unit,
# and it is never substituted for a certificate.
#
# The manifest is still executed as shell, so this assumes a trusted, locally
# produced artifact: it does not defend against a manifest that assigns `req_*`
# itself or runs hostile commands, and a closed data-only manifest format would
# be a separate change.  The caller's request is captured under `req_*` names
# before the manifest is sourced.  The certificate itself is not shell: it is
# parsed as data and never sourced or evaluated.
#
# The selector takes the repository source-elaboration lock before it sources
# the manifest and holds it through the link and the selection-record write, so
# a contender fails before reading mutable published inputs instead of treating
# a contended lock as a proof fallback.
#
# STRICT=1 fails instead of falling back to the baseline.  A non-strict request
# whose certificate is missing or rejected installs the baseline and records
# the rejection as a fallback; it never records the refused certificate as an
# accepted proof.
set -euo pipefail

here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/../.." && pwd)
req_manifest=${MANIFEST:-"$here/build/manifest.env"}
req_out=${OUT:-"$here/build/app"}
req_record=${RECORD:-"$here/build/selection.env"}
req_strict=${STRICT:-0}
req_unit=${UNIT:-}

[ -f "$req_manifest" ] || { echo "select: no manifest at $req_manifest" >&2; exit 1; }

# One source-elaboration writer at a time in this repository: the build and the
# selector both rebuild the proof module's imported graph, rewrite its olean and
# then import it.  The lock is a directory created atomically by `mkdir`, which
# is already pinned; only the owner removes it.  It is taken before the
# manifest is sourced or any mutable published input is read, and held through
# the link and the selection-record write, so a contender fails before touching
# published bytes and a validated certificate cannot be replaced between
# validation and use.  A lock left behind by a crashed run refuses too:
# removing it is a human decision after checking that no owner is running.
lock_dir="$root/.lake/install-certificate.lock"
lock_held=0

acquire_lock() {
  mkdir -p "$root/.lake" || return 1
  if ! mkdir "$lock_dir" 2>/dev/null; then
    printf 'select: another source elaboration holds %s\n' "$lock_dir" >&2
    printf 'select: if no such run exists, verify that and remove that directory\n' >&2
    return 1
  fi
  lock_held=1
}

release_lock() {
  [ "$lock_held" = 1 ] || return 0
  lock_held=0
  if ! rmdir "$lock_dir" 2>/dev/null; then
    printf 'select: could not remove %s\n' "$lock_dir" >&2
    printf 'select: verify that no run owns it and remove that directory\n' >&2
    return 1
  fi
}

cleanup() {
  local status=$?
  release_lock || status=1
  exit "$status"
}
trap cleanup EXIT

if ! acquire_lock; then
  exit 1
fi

# shellcheck disable=SC1090
source "$req_manifest"

sha() { sha256sum "$1" | cut -d' ' -f1; }
file_sha() { [ -f "$1" ] && sha "$1"; }
ok=1
reasons=()

expected_theorem=LeanLLVM.Vellum.CommaMaskIR.IR_refines
expected_contract=LeanLLVM.Vellum.commaContract
expected_axioms=Classical.choice,Quot.sound,propext
expected_symbol=leanllvm_comma_mask8
expected_marker=leanllvm_impl_id

# A tool probe whose answer does not depend on how much of the output is read.
# `tool | grep -q` leaves as soon as it matches, so the producer can be killed
# by SIGPIPE and `pipefail` then reports a valid object as invalid; capturing
# the output first removes the pipe, and a nonzero producer status still
# rejects.
probe() { # pattern, then the command to run
  local pattern=$1 out
  shift
  out=$("$@" 2>/dev/null) || return 1
  case "$out" in
    *"$pattern"*) return 0 ;;
    *) return 1 ;;
  esac
}

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

# The observed toolchain revision.  The certificate's field must equal what the
# repository's own helper prints now; a certificate is never allowed to supply
# the value it is checked against.
observed_toolchain=
if toolchain_out=$(bash "$here/toolchain-id.sh" 2>/dev/null) &&
   printf '%s' "$toolchain_out" | grep -Eq '^sha256:[0-9a-f]{64}$'; then
  observed_toolchain=$toolchain_out
fi

# The certificate is data.  These are the only fields, in this order, and this
# is the only grammar: one occurrence of each, ASCII key=value, one terminal
# newline.  A repeated, missing, reordered or unknown line is malformed, and so
# is a value outside the field's own shape.
certificate_fields=(
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
declare -A cert=()

parse_certificate() { # path
  local path=$1 line key value i count
  local -a keys=() values=()
  cert=()
  [ -f "$path" ] || return 1
  if LC_ALL=C grep -q $'\r' -- "$path" 2>/dev/null; then
    return 1
  fi
  # A NUL byte would be dropped by the shell's line reader, so a value could
  # otherwise smuggle one past the shape checks.
  if od -An -tx1 -- "$path" | tr -s ' ' '\n' | grep -qx '00'; then
    return 1
  fi
  count=$(wc -l < "$path") || return 1
  [ "$count" -eq "${#certificate_fields[@]}" ] || return 1
  while IFS= read -r line; do
    keys+=("${line%%=*}")
    values+=("${line#*=}")
  done < "$path"
  [ "${#keys[@]}" -eq "${#certificate_fields[@]}" ] || return 1
  for i in "${!certificate_fields[@]}"; do
    key=${keys[i]}
    value=${values[i]}
    [ "$key" = "${certificate_fields[i]}" ] || return 1
    [ -n "$value" ] || return 1
    case "$key" in
      *_sha256) [[ "$value" =~ ^[0-9a-f]{64}$ ]] || return 1 ;;
      schema) [ "$value" = leanllvm-install-v1 ] || return 1 ;;
      unit) [ "$value" = baseline ] || [ "$value" = candidate ] || return 1 ;;
      theorem | contract)
        [[ "$value" =~ ^LeanLLVM\.[A-Za-z0-9_.]+$ ]] || return 1 ;;
      axioms) [[ "$value" =~ ^[A-Za-z0-9_.]+(,[A-Za-z0-9_.]+)*$ ]] || return 1 ;;
      target_triple) [[ "$value" =~ ^[A-Za-z0-9_.-]+$ ]] || return 1 ;;
      data_layout) [[ "$value" =~ ^[A-Za-z0-9:_.-]+$ ]] || return 1 ;;
      toolchain_revision)
        [[ "$value" =~ ^sha256:[0-9a-f]{64}$ ]] || return 1 ;;
      *) return 1 ;;
    esac
    cert[$key]=$value
  done
  return 0
}

# Why the requested unit's certificate was refused: `missing` when the manifest
# names no certificate or the file is absent, `invalid` for any other failure.
# Empty when the certificate passed every check.
proof_failure=

check_certificate() { # unit
  local unit=$1
  local path_var=proof_$unit digest_var=proof_${unit}_sha256
  local fixture_var=${unit}_fixture marker_var=${unit}_marker
  local path=${!path_var:-} digest=${!digest_var:-}
  local unit_object unit_fixture unit_marker work derived manifest_abs

  if [ -z "$path" ] || [ ! -f "$path" ]; then
    proof_failure=missing
    return 1
  fi
  if [ -z "$digest" ] || [ "$(sha "$path")" != "$digest" ]; then
    proof_failure=invalid
    return 1
  fi
  if ! parse_certificate "$path"; then
    proof_failure=invalid
    return 1
  fi

  case "$unit" in
    baseline) unit_object=${baseline:-} ;;
    candidate) unit_object=${candidate:-} ;;
    *) proof_failure=invalid; return 1 ;;
  esac
  unit_fixture=${!fixture_var:-}
  unit_marker=${!marker_var:-}

  # Each field is compared with the file it names, not with another field and
  # not with the presence of a token.
  [ "${cert[unit]}" = "$unit" ] || { proof_failure=invalid; return 1; }
  [ "${cert[unit_object_sha256]}" = "$(file_sha "$unit_object")" ] ||
    { proof_failure=invalid; return 1; }
  [ "${cert[unit_fixture_sha256]}" = "$(file_sha "$unit_fixture")" ] ||
    { proof_failure=invalid; return 1; }
  [ "${cert[unit_marker_sha256]}" = "$(file_sha "$unit_marker")" ] ||
    { proof_failure=invalid; return 1; }
  [ "${cert[baseline_object_sha256]}" = "$(file_sha "${baseline:-}")" ] ||
    { proof_failure=invalid; return 1; }
  [ "${cert[candidate_object_sha256]}" = "$(file_sha "${candidate:-}")" ] ||
    { proof_failure=invalid; return 1; }
  [ "${cert[baseline_fixture_sha256]}" = "$(file_sha "${baseline_fixture:-}")" ] ||
    { proof_failure=invalid; return 1; }
  [ "${cert[candidate_fixture_sha256]}" = "$(file_sha "${candidate_fixture:-}")" ] ||
    { proof_failure=invalid; return 1; }
  [ "${cert[baseline_marker_sha256]}" = "$(file_sha "${baseline_marker:-}")" ] ||
    { proof_failure=invalid; return 1; }
  [ "${cert[candidate_marker_sha256]}" = "$(file_sha "${candidate_marker:-}")" ] ||
    { proof_failure=invalid; return 1; }
  [ "${cert[theorem]}" = "${theorem:-}" ] &&
    [ "${cert[theorem]}" = "$expected_theorem" ] ||
    { proof_failure=invalid; return 1; }
  [ "${cert[axioms]}" = "$expected_axioms" ] ||
    { proof_failure=invalid; return 1; }
  [ "${cert[contract]}" = "${contract:-}" ] &&
    [ "${cert[contract]}" = "$expected_contract" ] ||
    { proof_failure=invalid; return 1; }
  [ "${cert[target_triple]}" = "${target:-}" ] ||
    { proof_failure=invalid; return 1; }
  [ "${cert[data_layout]}" = "${datalayout:-}" ] ||
    { proof_failure=invalid; return 1; }
  [ -n "$observed_toolchain" ] &&
    [ "${cert[toolchain_revision]}" = "$observed_toolchain" ] ||
    { proof_failure=invalid; return 1; }

  # The kernel re-check: reconcile the imported proof graph, elaborate the
  # proof module from source, have the producer derive the certificate again,
  # and compare bytes.  The manifest path is passed absolute because the
  # producer runs from the repository root.  This runs under the script's
  # repository lock, which is held from before the manifest is sourced through
  # the link and record write.
  work=$(mktemp -d) || { proof_failure=invalid; return 1; }
  derived=$work/proof.env
  manifest_abs=$(cd "$(dirname "$req_manifest")" && pwd)/$(basename "$req_manifest")
  sequence_ok=1
  # Lake tracks imported project source but not the `include_str` fixtures, and
  # the direct re-elaboration below forces only the latter, so the imported
  # graph is rebuilt first.
  if ! (cd "$root" && lake build LeanLLVM.Vellum.CommaMaskIR) \
      >/dev/null 2>"$work/graph.log"; then
    sequence_ok=0
  fi
  if [ "$sequence_ok" -eq 1 ] &&
     ! (cd "$root" &&
        lake env lean -o .lake/build/lib/lean/LeanLLVM/Vellum/CommaMaskIR.olean \
          LeanLLVM/Vellum/CommaMaskIR.lean) >/dev/null 2>"$work/source.log"; then
    sequence_ok=0
  fi
  if [ "$sequence_ok" -eq 1 ] &&
     ! (cd "$root" &&
        CERT_UNIT="$unit" CERT_MANIFEST="$manifest_abs" CERT_OUT="$derived" \
          lake env lean probes/install/InstallCertificate.lean) \
      >/dev/null 2>"$work/producer.log"; then
    sequence_ok=0
  fi
  if [ "$sequence_ok" -eq 1 ] && ! cmp -s "$derived" "$path"; then
    sequence_ok=0
  fi
  if [ "$sequence_ok" -ne 1 ]; then
    rm -rf "$work"
    proof_failure=invalid
    return 1
  fi
  rm -rf "$work"
  return 0
}

# The request.  An unknown unit is refused, and a loop request is refused as an
# installation request: `IR_refines` relates the candidate to the baseline and
# says nothing about the loop body.
selected_unit=
case "$req_unit" in
  "" | candidate) selected_unit=candidate ;;
  baseline) selected_unit=baseline ;;
  loop) selected_unit=loop ;;
  *) selected_unit= ;;
esac
if [ -z "$selected_unit" ]; then
  ok=0; reasons+=("unknown unit $req_unit")
elif [ "$selected_unit" = loop ]; then
  ok=0; reasons+=("no checked theorem covers unit loop")
fi

check_hash "${caller:-}" "${caller_sha256:-}" "caller hash"
check_hash "${baseline:-}" "${baseline_sha256:-}" "baseline hash"
check_hash "${candidate:-}" "${candidate_sha256:-}" "candidate hash"
check_hash "${differential:-}" "${differential_sha256:-}" "differential hash"

check_hash "${baseline_fixture:-}" "${baseline_fixture_sha256:-}" "baseline fixture"
check_hash "${candidate_fixture:-}" "${candidate_fixture_sha256:-}" "candidate fixture"
check_hash "${baseline_marker:-}" "${baseline_marker_sha256:-}" "baseline marker"
check_hash "${candidate_marker:-}" "${candidate_marker_sha256:-}" "candidate marker"

if [ -n "${loop:-}" ]; then
  check_hash "${loop:-}" "${loop_sha256:-}" "loop hash"
  check_hash "${loop_fixture:-}" "${loop_fixture_sha256:-}" "loop fixture"
  check_hash "${loop_marker:-}" "${loop_marker_sha256:-}" "loop marker"
fi

if [ "${kind:-}" != "proof-bound" ]; then
  ok=0; reasons+=("manifest kind ${kind:-missing}")
fi
if [ -z "${contract:-}" ] || [ -z "${theorem:-}" ]; then
  ok=0; reasons+=("manifest does not name a contract and theorem")
else
  if [ "$contract" != "$expected_contract" ]; then
    ok=0; reasons+=("manifest contract $contract")
  fi
  if [ "$theorem" != "$expected_theorem" ]; then
    ok=0; reasons+=("manifest theorem $theorem")
  fi
fi
if [ -n "${symbol:-}" ] && [ "$symbol" != "$expected_symbol" ]; then
  ok=0; reasons+=("manifest symbol $symbol")
fi
if [ -n "${marker:-}" ] && [ "$marker" != "$expected_marker" ]; then
  ok=0; reasons+=("manifest marker $marker")
fi
if [ "${attributes:-}" != "reject" ]; then
  ok=0; reasons+=("attribute policy ${attributes:-missing}")
fi
if [ "${target_features:-}" != "none" ]; then
  ok=0; reasons+=("target features ${target_features:-missing}")
fi

if [ "$ok" -eq 1 ]; then
  if ! verify_rebuild baseline "${baseline_fixture:-}" "${baseline_marker:-}" \
      "${baseline_sha256:-}"; then
    ok=0; reasons+=("baseline unit not rebuilt from its fixture")
  fi
  if ! verify_rebuild candidate "${candidate_fixture:-}" "${candidate_marker:-}" \
      "${candidate_sha256:-}"; then
    ok=0; reasons+=("candidate unit not rebuilt from its fixture")
  fi
  if [ -n "${loop:-}" ]; then
    if ! verify_rebuild loop "${loop_fixture:-}" "${loop_marker:-}" \
        "${loop_sha256:-}"; then
      ok=0; reasons+=("loop unit not rebuilt from its fixture")
    fi
  fi
fi

if [ -z "${target:-}" ] || [ -z "${triple:-}" ] || [ -z "${datalayout:-}" ]; then
  ok=0; reasons+=("manifest does not bind the target triple and data layout")
fi
if command -v clang >/dev/null 2>&1; then
  observed_triple=$(clang -print-target-triple) ||
    { observed_triple=; ok=0; reasons+=("clang target probe failed"); }
  observed_layout=$(printf '' | clang -O0 -S -emit-llvm -x c - -o - 2>/dev/null \
    | sed -n 's/^target datalayout = "\(.*\)"$/\1/p') || observed_layout=
  if [ "$observed_triple" != "${target:-}" ]; then
    ok=0; reasons+=("target ${target:-missing}")
  fi
  if [ "${triple:-}" != "${target:-}" ]; then
    ok=0; reasons+=("manifest triple ${triple:-missing} differs from target ${target:-missing}")
  fi
  if [ -z "$observed_layout" ] || [ "$observed_layout" != "${datalayout:-}" ]; then
    ok=0; reasons+=("data layout ${datalayout:-missing}")
  fi
else
  ok=0; reasons+=("clang is not available to check the target")
fi
if ! grep -q '^RESULT: PASS$' "${differential:-}" 2>/dev/null; then
  ok=0; reasons+=("differential transcript result")
fi
if ! probe 'ELF 64-bit' file -b "${baseline:-}"; then
  ok=0; reasons+=("baseline is not ELF64")
fi
if ! probe ' T leanllvm_comma_mask8' nm -g "${baseline:-}"; then
  ok=0; reasons+=("baseline symbol")
fi
if ! probe ' T leanllvm_comma_mask8' nm -g "${candidate:-}"; then
  ok=0; reasons+=("candidate symbol")
fi
if ! probe ' T leanllvm_impl_id' nm -g "${candidate:-}"; then
  ok=0; reasons+=("candidate marker")
fi
if [ -n "${loop:-}" ]; then
  if ! probe 'ELF 64-bit' file -b "${loop:-}"; then
    ok=0; reasons+=("loop is not ELF64")
  fi
  if ! probe ' T leanllvm_comma_mask8' nm -g "${loop:-}"; then
    ok=0; reasons+=("loop symbol")
  fi
  if ! probe ' T leanllvm_impl_id' nm -g "${loop:-}"; then
    ok=0; reasons+=("loop marker")
  fi
fi
if ! probe 'leanllvm_comma_mask8' nm -u "${caller:-}"; then
  ok=0; reasons+=("caller import")
fi

# The certificate gate applies to the two units the theorem covers.  A loop or
# unknown request has no certificate to check.
if [ -n "$selected_unit" ] && [ "$selected_unit" != loop ]; then
  check_certificate "$selected_unit" || true
fi

if [ "$ok" -eq 1 ] && [ -z "$proof_failure" ]; then
  case "$selected_unit" in
    baseline) selected=${baseline:-} ;;
    candidate) selected=${candidate:-} ;;
  esac
  kind=$selected_unit
  reason="hashes, fixtures, rebuild and certificate match; $theorem covers the selected unit"
else
  if [ "$req_strict" = 1 ]; then
    printf 'select: strict failure\n' >&2
    if [ "${#reasons[@]}" -gt 0 ]; then
      printf '  - %s\n' "${reasons[@]}" >&2
    fi
    if [ -n "$proof_failure" ]; then
      printf '  - proof certificate %s\n' "$proof_failure" >&2
    fi
    exit 1
  fi
  selected=${baseline:-}
  kind=baseline
  if [ -n "$proof_failure" ]; then
    if [ "$proof_failure" = missing ]; then
      reason='proof rejected: missing certificate; installed baseline fallback'
    else
      reason='proof rejected: invalid certificate; installed baseline fallback'
    fi
  else
    reason=$(IFS='; '; echo "${reasons[*]}")
  fi
fi

leanc "$caller" "$selected" -o "$req_out" 2>>"$here/build/link.log"

requested_proof_sha256=
case "$selected_unit" in
  baseline) proof_path=${proof_baseline:-} ;;
  candidate) proof_path=${proof_candidate:-} ;;
  *) proof_path= ;;
esac
if [ -n "$proof_path" ] && [ -f "$proof_path" ]; then
  requested_proof_sha256=$(sha "$proof_path")
fi

{
  echo "selected=$kind"
  echo "output=$req_out"
  echo "target=${target:-}"
  echo "triple=${triple:-}"
  echo "datalayout=${datalayout:-}"
  echo "contract=${contract:-}"
  echo "theorem=${theorem:-}"
  echo "toolchain_revision=$observed_toolchain"
  echo "proof_sha256=$requested_proof_sha256"
  echo "reason=$reason"
  echo "baseline_fixture_sha256=${baseline_fixture_sha256:-}"
  echo "candidate_fixture_sha256=${candidate_fixture_sha256:-}"
  echo "baseline_sha256=${baseline_sha256:-}"
  echo "candidate_sha256=${candidate_sha256:-}"
  echo "loop_sha256=${loop_sha256:-}"
  echo "differential_sha256=${differential_sha256:-}"
} > "$req_record"

# The link and the record are written; only now release the lock that protected
# the validated bytes from publication to use.  A failed release is a failure
# of the selection, not a warning.
if ! release_lock; then
  echo "select: the selection is not accepted; the lock could not be released" >&2
  exit 1
fi

echo "$kind -> $req_out"
