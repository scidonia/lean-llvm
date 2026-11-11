#!/usr/bin/env bash
# Verify a replacement unit against its manifest and link one body.
#
#   MANIFEST=... OUT=... RECORD=... STRICT=1 ./select.sh
#
# A unit is accepted only when
#   * the request names a known unit, and the manifest names the installation
#     contract exactly and the theorem that covers the requested unit:
#     `IR_refines` over the candidate and the baseline for those two units,
#     the loop's own `loop_refines_candidate_within` in the manifest's
#     `loop_theorem` field for `UNIT=loop`, and
#     `depth_count_refines` with `depthContract` in `depth_count_theorem` and
#     `depth_contract` for `UNIT=depth_count`, so each request is decided by
#     its certificate;
#   * every recorded hash matches: caller, the unit objects, the differential
#     transcript, and each bound unit's fixture and marker inputs;
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
#     the covering theorem the manifest binds for that unit and the contract;
#     the observed target and layout; the checked axiom set; and the toolchain
#     revision the repository's own `toolchain-id.sh` prints now;
#   * the Lean producer, run after the imported proof graph is rebuilt from
#     current project source and the proof module is re-elaborated from source,
#     reproduces the certificate byte for byte.  That is the kernel re-check:
#     a changed field, a stale proof module or a stale imported proof source
#     fails here even if the certificate's manifest digest was rewritten.  A
#     loop request re-elaborates `CommaMaskLoop` after `CommaMaskIR`, because
#     the loop's proof module imports the one the fixture guards are about; a
#     depth request re-elaborates `DepthCountRefine`, which carries the depth
#     fixture through `include_str`;
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
# selector both re-elaborate the proof module by removing its olean and asking
# Lake to build the module, then import it.  The lock is a directory created
# atomically by `mkdir`, which is already pinned; only the owner removes it.  It
# is taken before the manifest is sourced or any mutable published input is
# read, and held through the link and the selection-record write, so a
# contender fails before touching published bytes and a validated certificate
# cannot be replaced between validation and use.  A lock left behind by a
# crashed run refuses too:
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

expected_theorem=LeanLLVM.Refinement.CommaMaskIR.IR_refines
expected_loop_theorem=LeanLLVM.Refinement.CommaMaskLoop.loop_refines_candidate_within
expected_depth_theorem=LeanLLVM.Refinement.DepthCountRefine.depth_count_refines
expected_contract=LeanLLVM.Refinement.commaContract
expected_depth_contract=LeanLLVM.Refinement.DepthCountRefine.depthContract
expected_axioms=Classical.choice,Quot.sound,propext
expected_symbol=leanllvm_comma_mask8
expected_marker=leanllvm_impl_id
expected_depth_symbol=depth_count

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
      unit)
        [ "$value" = baseline ] || [ "$value" = candidate ] ||
          [ "$value" = loop ] || [ "$value" = depth_count ] || return 1 ;;
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
# Empty when the certificate passed every check.  `proof_detail` names the
# field value when the disagreement is a wrong theorem or contract name.
proof_failure=
proof_detail=

check_certificate() { # unit
  local unit=$1
  local path_var=proof_$unit digest_var=proof_${unit}_sha256
  local fixture_var=${unit}_fixture marker_var=${unit}_marker
  local path=${!path_var:-} digest=${!digest_var:-}
  local unit_object unit_fixture unit_marker work derived manifest_abs
  local bound_theorem expected_unit_theorem bound_contract expected_unit_contract
  proof_detail=

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
    loop) unit_object=${loop:-} ;;
    depth_count) unit_object=${depth_count:-} ;;
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
  # The theorem and contract a certificate must name are the ones the manifest
  # binds for its unit: the loop and the depth counter each have their own
  # fields and their own statements, every other unit is covered by the global
  # `theorem`/`contract` fields.  Nothing is accepted from the certificate
  # alone: both the manifest binding and the expected name are required to
  # agree with it, and a disagreement names the value that was used.
  bound_theorem=${theorem:-}
  expected_unit_theorem=$expected_theorem
  bound_contract=${contract:-}
  expected_unit_contract=$expected_contract
  if [ "$unit" = loop ]; then
    bound_theorem=${loop_theorem:-}
    expected_unit_theorem=$expected_loop_theorem
  fi
  if [ "$unit" = depth_count ]; then
    bound_theorem=${depth_count_theorem:-}
    expected_unit_theorem=$expected_depth_theorem
    bound_contract=${depth_contract:-}
    expected_unit_contract=$expected_depth_contract
  fi
  if [ "${cert[theorem]}" != "$bound_theorem" ] ||
     [ "${cert[theorem]}" != "$expected_unit_theorem" ]; then
    proof_failure=invalid
    proof_detail="theorem '${cert[theorem]}' is not the unit's theorem '$expected_unit_theorem'"
    return 1
  fi
  [ "${cert[axioms]}" = "$expected_axioms" ] ||
    { proof_failure=invalid; return 1; }
  if [ "${cert[contract]}" != "$bound_contract" ] ||
     [ "${cert[contract]}" != "$expected_unit_contract" ]; then
    proof_failure=invalid
    proof_detail="contract '${cert[contract]}' is not the unit's contract '$expected_unit_contract'"
    return 1
  fi
  [ "${cert[target_triple]}" = "${target:-}" ] ||
    { proof_failure=invalid; return 1; }
  [ "${cert[data_layout]}" = "${datalayout:-}" ] ||
    { proof_failure=invalid; return 1; }
  [ -n "$observed_toolchain" ] &&
    [ "${cert[toolchain_revision]}" = "$observed_toolchain" ] ||
    { proof_failure=invalid; return 1; }

  # The kernel re-check: re-elaborate the proof module from current source,
  # have the producer derive the certificate again, and compare bytes.  The
  # force is removing the module's olean: Lake accepts an olean written by
  # another process as current and does not track the `include_str` fixtures,
  # while its own module job re-evaluates the guards and carries the `--setup`
  # package identity the dependent link needs; that job also rewrites the
  # module's ilean, C file, hash sidecars and trace.  The manifest path is
  # passed absolute because the producer runs from the repository root.  This
  # runs under the script's repository lock, which is held from before the
  # manifest is sourced through the link and record write.
  work=$(mktemp -d) || { proof_failure=invalid; return 1; }
  derived=$work/proof.env
  manifest_abs=$(cd "$(dirname "$req_manifest")" && pwd)/$(basename "$req_manifest")
  sequence_ok=1
  if ! (cd "$root" &&
        rm -f .lake/build/lib/lean/LeanLLVM/Refinement/CommaMaskIR.olean &&
        lake build LeanLLVM.Refinement.CommaMaskIR) \
      >/dev/null 2>"$work/rebuild.log"; then
    sequence_ok=0
  fi
  # `CommaMaskLoop` imports `CommaMaskIR`, so the loop's own proof module is
  # rebuilt only after it, and only when the requested unit is the loop: a
  # baseline or candidate request must not pay for a module its certificate
  # does not name.
  if [ "$sequence_ok" -eq 1 ] && [ "$unit" = loop ] &&
     ! (cd "$root" &&
        rm -f .lake/build/lib/lean/LeanLLVM/Refinement/CommaMaskLoop.olean &&
        lake build LeanLLVM.Refinement.CommaMaskLoop) \
      >/dev/null 2>"$work/loop-rebuild.log"; then
    sequence_ok=0
  fi
  # `DepthCountRefine` carries the depth fixture through `include_str` and its
  # own `#guard`, so a depth request re-elaborates it from source.  It does not
  # import the comma-mask modules, so it is independent of the two rebuilds
  # above.
  if [ "$sequence_ok" -eq 1 ] && [ "$unit" = depth_count ] &&
     ! (cd "$root" &&
        rm -f .lake/build/lib/lean/LeanLLVM/Refinement/DepthCountRefine.olean &&
        lake build LeanLLVM.Refinement.DepthCountRefine) \
      >/dev/null 2>"$work/depth-rebuild.log"; then
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

# The request.  An unknown unit fails here; a known unit — the loop and the
# depth counter included — is decided by the hash, rebuild, object and
# certificate checks below.
selected_unit=
case "$req_unit" in
  "" | candidate) selected_unit=candidate ;;
  baseline) selected_unit=baseline ;;
  loop) selected_unit=loop ;;
  depth_count) selected_unit=depth_count ;;
  *) selected_unit= ;;
esac
if [ -z "$selected_unit" ]; then
  ok=0; reasons+=("unknown unit $req_unit")
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

if [ -n "${depth_count:-}" ]; then
  check_hash "${depth_count:-}" "${depth_count_sha256:-}" "depth_count hash"
  check_hash "${depth_count_fixture:-}" "${depth_count_fixture_sha256:-}" \
    "depth_count fixture"
  check_hash "${depth_count_marker:-}" "${depth_count_marker_sha256:-}" \
    "depth_count marker"
  check_hash "${depth_caller:-}" "${depth_caller_sha256:-}" "depth_caller hash"
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
if [ -n "${depth_count_symbol:-}" ] &&
   [ "$depth_count_symbol" != "$expected_depth_symbol" ]; then
  ok=0; reasons+=("manifest depth_count symbol $depth_count_symbol")
fi
if [ -n "${depth_contract:-}" ] &&
   [ "$depth_contract" != "$expected_depth_contract" ]; then
  ok=0; reasons+=("manifest depth contract $depth_contract")
fi
if [ -n "${depth_count_theorem:-}" ] &&
   [ "$depth_count_theorem" != "$expected_depth_theorem" ]; then
  ok=0; reasons+=("manifest depth_count theorem $depth_count_theorem")
fi
if [ "$selected_unit" = depth_count ]; then
  if [ -z "${depth_count_symbol:-}" ] || [ -z "${depth_contract:-}" ] ||
     [ -z "${depth_count_theorem:-}" ] || [ -z "${depth_caller:-}" ]; then
    ok=0; reasons+=("manifest does not bind the depth_count unit")
  fi
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
  if [ -n "${depth_count:-}" ]; then
    if ! verify_rebuild depth_count "${depth_count_fixture:-}" \
        "${depth_count_marker:-}" "${depth_count_sha256:-}"; then
      ok=0; reasons+=("depth_count unit not rebuilt from its fixture")
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
if [ -n "${depth_count:-}" ]; then
  if ! probe 'ELF 64-bit' file -b "${depth_count:-}"; then
    ok=0; reasons+=("depth_count is not ELF64")
  fi
  if ! probe ' T depth_count' nm -g "${depth_count:-}"; then
    ok=0; reasons+=("depth_count symbol")
  fi
  if ! probe ' T leanllvm_impl_id' nm -g "${depth_count:-}"; then
    ok=0; reasons+=("depth_count marker")
  fi
fi
# The caller is the object that imports the selected unit's symbol: the
# comma-mask caller for the three mask units, the depth corpus driver for the
# depth counter, whose ABI is not the one-word seam.
link_caller=${caller:-}
if [ "$selected_unit" = depth_count ]; then
  link_caller=${depth_caller:-}
  if ! probe 'depth_count' nm -u "${link_caller:-}"; then
    ok=0; reasons+=("depth caller import")
  fi
elif ! probe 'leanllvm_comma_mask8' nm -u "${link_caller:-}"; then
  ok=0; reasons+=("caller import")
fi

# The certificate gate applies to every known unit: the loop has its own
# certificate and its own covering theorem, checked by the same code.
if [ -n "$selected_unit" ]; then
  check_certificate "$selected_unit" || true
fi

if [ "$ok" -eq 1 ] && [ -z "$proof_failure" ]; then
  covering_theorem=$theorem
  covering_contract=$contract
  case "$selected_unit" in
    baseline) selected=${baseline:-} ;;
    candidate) selected=${candidate:-} ;;
    loop) selected=${loop:-}; covering_theorem=${loop_theorem:-} ;;
    depth_count)
      selected=${depth_count:-}
      covering_theorem=${depth_count_theorem:-}
      covering_contract=${depth_contract:-}
      ;;
  esac
  kind=$selected_unit
  reason="hashes, fixtures, rebuild and certificate match; $covering_theorem covers the selected unit"
else
  covering_theorem=${theorem:-}
  covering_contract=${contract:-}
  if [ "$req_strict" = 1 ]; then
    printf 'select: strict failure\n' >&2
    if [ "${#reasons[@]}" -gt 0 ]; then
      printf '  - %s\n' "${reasons[@]}" >&2
    fi
    if [ -n "$proof_failure" ]; then
      printf '  - proof certificate %s\n' "$proof_failure" >&2
      if [ -n "$proof_detail" ]; then
        printf '  - proof certificate detail: %s\n' "$proof_detail" >&2
      fi
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

leanc "$link_caller" "$selected" -o "$req_out" 2>>"$here/build/link.log"

requested_proof_sha256=
case "$selected_unit" in
  baseline) proof_path=${proof_baseline:-} ;;
  candidate) proof_path=${proof_candidate:-} ;;
  loop) proof_path=${proof_loop:-} ;;
  depth_count) proof_path=${proof_depth_count:-} ;;
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
  echo "contract=$covering_contract"
  echo "theorem=$covering_theorem"
  echo "toolchain_revision=$observed_toolchain"
  echo "proof_sha256=$requested_proof_sha256"
  echo "reason=$reason"
  echo "baseline_fixture_sha256=${baseline_fixture_sha256:-}"
  echo "candidate_fixture_sha256=${candidate_fixture_sha256:-}"
  echo "baseline_sha256=${baseline_sha256:-}"
  echo "candidate_sha256=${candidate_sha256:-}"
  echo "loop_sha256=${loop_sha256:-}"
  echo "depth_count_sha256=${depth_count_sha256:-}"
  echo "depth_caller_sha256=${depth_caller_sha256:-}"
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
