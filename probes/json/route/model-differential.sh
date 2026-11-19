#!/usr/bin/env bash
# The object-versus-model differential for the JSON pipeline.
#
#   nix develop -c bash probes/json/route/model-differential.sh
#
# The route scenario (`check.sh`) compares two callers of the same object, so it
# cannot test the model: both sides run the native pipeline.  The proved body
# is `JsonPipelineIR.pipelineBody`, parsed from
# `probes/install/ir/json-pipeline.candidate.ll`, and this script puts a run of
# it against the object's answer on the same bytes.
#
# For every row the route admits, the object's `RouteCall` — the adapter's
# header words and the two payload extents, as `leanllvm-json-route --doc`
# prints them — must equal the model's projection at the same document: the
# verdict, the four cursor words, the refusal word, the arena's used prefix and
# the event stream, with the arena and events compared byte for byte.  A row
# the route does not admit is outside the differential's domain and is reported
# by name with both decisions; the two decisions must still agree, so a domain
# disagreement is a named mismatch rather than a skipped row.
#
# Three controls, each required to go red:
#
#   a. uninitialised pos8.  With the table never filled, the entry emitter
#      traps (`kernel/json/entry.c`), so there is no plausible object row to
#      compare.  `init-guard.sh` is the committed probe: its `bare` arm must
#      die by SIGILL (status 132), not return an answer.  No comparison row is
#      possible, which is the red in its strongest form.
#   b. a mutated fixture body.  A temporary copy of the pinned fixture with its
#      final `ret i64 %retval.0` replaced by `ret i64 0` is run by the model
#      (`--body`); its projection must differ from the object's row on an
#      accepted document.  The tampering is in a temporary directory only.
#   c. a tampered object.  A temporary copy of `kernel/json/stage2.c` with
#      `return r ? 1 : 0;` changed to `return r ? 0 : 1;` is compiled at the
#      route's kernel line and linked into a `driver.c` copy; the result must
#      differ from the model's row.  A comparison that survives that is not
#      comparing anything.
#
# Build identities are printed before the rows: the SHA-256 of the native route,
# the model executable, the fixture text, and the tampered object's source.
# The flags of the objects are the route's (`build.sh`): kernel
# `-O2 -march=x86-64-v3 -mpclmul -std=gnu11 -falign-loops=64
# -falign-functions=64`, adapter `-O2`; the model is the Lake target
# `leanllvm-json-pipeline-model`, compiled by the repository's toolchain.
#
# Exit status: 0 when every compared row agrees and all controls go red, 1 on a
# mismatch or a control that did not, 3 on a setup fault.
set -uo pipefail

here=$(cd "$(dirname "$0")" && pwd)
repo=$(cd "$here/../../.." && pwd)
route=${ROUTE:-"$here/build/leanllvm-json-route"}
model=${MODEL:-"$repo/.lake/build/bin/leanllvm-json-pipeline-model"}
driver_src="$here/driver.c"
corpus="$repo/tests/json/corpus"
manifest="$repo/tests/json/manifest.tsv"
fixture="$repo/probes/install/ir/json-pipeline.candidate.ll"
kernel="$repo/kernel/json"

for path in "$route" "$model" "$corpus" "$manifest" "$fixture" \
            "$driver_src" "$here/init-guard.sh" "$kernel/stage2.c"; do
  [ -e "$path" ] || {
    printf 'SETUP: absent: %s\n' "$path" >&2
    printf '  build the route: nix develop -c bash probes/json/route/build.sh\n' >&2
    printf '  build the model: nix develop -c bash probes/install/lake-locked.sh build leanllvm-json-pipeline-model\n' >&2
    exit 3
  }
done
for path in "$here/build/pipeline.o" "$here/build/s1_block.o" "$here/build/entry.o" \
            "$here/build/escape.o" "$here/build/utf8.o"; do
  [ -e "$path" ] || { printf 'SETUP: absent: %s\n' "$path" >&2; exit 3; }
done

work=$(mktemp -d "${TMPDIR:-/tmp}/json-model-differential.XXXXXX") || {
  printf 'SETUP: cannot create a temporary directory\n' >&2; exit 3; }
trap 'rm -rf "$work"' EXIT

failed=0
rows=0
compared=0
outside=0
mismatches=0
accept_doc=
accept_name=

fail() { printf 'FAIL: %s\n' "$*" >&2; failed=$((failed + 1)); }

# The observation line as the route prints it (six numbers), or empty.
observation_of() {
  awk 'NR == 1 && /^verdict=[0-9]+ nk=[0-9]+ nxp=[0-9]+ ndst=[0-9]+ nev=[0-9]+ err=[0-9]+$/ {
         print; exit }' "$1"
}

payload_of() { sed -n "s/^$2=//p" "$1"; }

# Compare the route's three lines with the model's observation.  A disagreement
# names its field; the payloads are compared whole, and their first differing
# byte is reported.
compare_row() { # <name> <route out> <model out>
  local name=$1 rf=$2 mf=$3 ro mo ra ma re me at
  ro=$(observation_of "$rf")
  mo=$(grep -m1 '^verdict=' "$mf" || true)
  if [ -z "$ro" ]; then
    fail "$name: the route did not print the observation in the pinned form"
    return 1
  fi
  if [ -z "$mo" ]; then
    fail "$name: the model printed no observation"
    sed -n '1,4p' "$mf" >&2
    return 1
  fi
  if [ "$ro" != "$mo" ]; then
    fail "$name: observation disagreement"
    printf '  route: %s\n  model: %s\n' "$ro" "$mo" >&2
    mismatches=$((mismatches + 1))
    return 1
  fi
  local stream
  for stream in arena events; do
    ra=$(payload_of "$rf" "$stream")
    ma=$(payload_of "$mf" "$stream")
    if [ "$ra" != "$ma" ]; then
      at=0
      local n=${#ra} m=${#ma} lim
      lim=$(( n < m ? n : m ))
      while [ "$at" -lt "$lim" ] && [ "${ra:$at:1}" = "${ma:$at:1}" ]; do
        at=$((at + 1))
      done
      fail "$name: $stream disagreement at half-byte $at (route ${#ra}, model ${#ma})"
      mismatches=$((mismatches + 1))
      return 1
    fi
  done
  return 0
}

# ---------------------------------------------------------------- identities --
printf 'object: %s\n' "$route"
printf 'object sha256: %s\n' "$(sha256sum "$route" | cut -d' ' -f1)"
printf 'object flags: kernel -O2 -march=x86-64-v3 -mpclmul -std=gnu11 -falign-loops=64 -falign-functions=64; adapter -O2\n'
printf 'model: %s\n' "$model"
printf 'model sha256: %s\n' "$(sha256sum "$model" | cut -d' ' -f1)"
printf 'model target: leanllvm-json-pipeline-model (lean toolchain: %s)\n' \
  "$(cat "$repo/lean-toolchain")"
printf 'fixture: %s\n' "$fixture"
printf 'fixture sha256: %s\n' "$(sha256sum "$fixture" | cut -d' ' -f1)"

# ---------------------------------------------------------------------- rows --
# The corpus rows the manifest names, then the boundary and malformed documents
# the corpus does not cover.  The generated files are inside the work directory.
doc_paths=()
while IFS=$'\t' read -r name verdict expected rest; do
  case $name in ''|'#'*) continue;; esac
  path="$corpus/$name"
  [ -e "$path" ] || { fail "corpus row '$name' is absent: $path"; continue; }
  doc_paths+=("$path")
done <"$manifest"

gen="$work/docs"
mkdir -p "$gen"
make_bytes() { # <file> <count> <byte>
  awk -v n="$2" -v b="$3" 'BEGIN { for (i = 0; i < n; i++) printf "%c", b }' >"$1"
}
# A valid string of exactly L bytes: quote, L-2 payload bytes, quote.
for L in 63 64 65; do
  { printf '"'; make_bytes "$work/docs/payload.tmp" $((L - 2)) 'a'; printf '"'; } \
    >"$gen/boundary-$L.json"
done
printf ']' >"$gen/malformed-close.json"
printf '0 0' >"$gen/malformed-trailing.json"
printf '   ' >"$gen/whitespace-only.json"
printf '""' >"$gen/empty-string.json"
printf '' >"$gen/empty.json"
make_bytes "$gen/over-bound.json" 1048577 'x'
for path in "$gen"/*.json; do doc_paths+=("$path"); done

for path in "${doc_paths[@]}"; do
  name=$(basename "$path")
  rows=$((rows + 1))
  "$route" --doc "$path" >"$work/route.out" 2>"$work/route.err"
  rs=$?
  "$model" --doc "$path" >"$work/model.out" 2>"$work/model.err"
  ms=$?

  if [ "$ms" -ne 0 ]; then
    fail "$name: the model exited $ms"
    cat "$work/model.err" >&2
    continue
  fi
  mdecision=$(sed -n 's/^decision=//p' "$work/model.out")
  if [ -n "$(observation_of "$work/route.out")" ]; then
    # The fast path: the object ran, so this row is compared.
    if [ "$mdecision" != admitted ]; then
      fail "$name: the route admitted and the model answered '$mdecision'"
      continue
    fi
    if compare_row "$name" "$work/route.out" "$work/model.out"; then
      compared=$((compared + 1))
    fi
    if [ -z "$accept_doc" ] && \
       grep -q '^verdict=1 ' "$work/route.out"; then
      accept_doc=$path
      accept_name=$name
    fi
  elif grep -q '^fallback=accepted' "$work/route.out"; then
    outside=$((outside + 1))
    if [ "$mdecision" != fallback ]; then
      fail "$name: the route fell back to the reference parser and the model answered '$mdecision'"
      continue
    fi
    printf 'outside: %s route=fallback model=fallback\n' "$name"
  elif [ "$rs" -eq 2 ]; then
    outside=$((outside + 1))
    if [ "$mdecision" != refused ]; then
      fail "$name: the route refused and the model answered '$mdecision'"
      continue
    fi
    printf 'outside: %s route=refused model=refused\n' "$name"
  else
    fail "$name: the route exited $rs without printing an observation or a fallback"
    cat "$work/route.err" >&2
  fi
done

# ------------------------------------------------------------------ control a --
# Uninitialised pos8: the emitter traps, so there is no object row at all.
if bash "$here/init-guard.sh" >"$work/guard.out" 2>&1; then
  if grep -qx 'ok: uninitialised pos8 trapped (status 132, SIGILL)' "$work/guard.out"; then
    printf 'control uninitialised-pos8: red (uninitialised pos8 died by SIGILL; no object row)\n'
  else
    fail "control uninitialised-pos8: the guard probe ran but did not report the trap"
    cat "$work/guard.out" >&2
  fi
else
  fail "control uninitialised-pos8: init-guard.sh failed"
  cat "$work/guard.out" >&2
fi

# ------------------------------------------------------------------ control b --
# A mutated fixture body: change the final constant return, in a temporary copy.
if [ -z "$accept_doc" ]; then
  fail "control mutated-body: no accepted row was available to compare"
else
  mutated="$work/mutated-pipeline.ll"
  sed 's/^  ret i64 %retval\.0$/  ret i64 0/' "$fixture" >"$mutated"
  if [ "$(grep -c '^  ret i64 0$' "$mutated")" -ne 1 ]; then
    fail "control mutated-body: the temporary fixture did not take exactly one constant return"
  else
    printf 'control mutated-body: fixture sha256: %s\n' \
      "$(sha256sum "$mutated" | cut -d' ' -f1)"
    "$route" --doc "$accept_doc" >"$work/accept-route.out" 2>"$work/accept-route.err"
    "$model" --doc "$accept_doc" --body "$mutated" >"$work/mutated.out" \
      2>"$work/mutated.err"
    ms=$?
    "$model" --doc "$accept_doc" >"$work/base-model.out" 2>&1
    base_obs=$(grep -m1 '^verdict=' "$work/base-model.out" || true)
    accept_obs=$(observation_of "$work/accept-route.out")
    mut_obs=$(grep -m1 '^verdict=' "$work/mutated.out" || true)
    if [ "$ms" -ne 0 ] || [ -z "$mut_obs" ]; then
      fail "control mutated-body: the model did not answer the mutated body (exit $ms)"
      cat "$work/mutated.err" >&2
    elif [ "$mut_obs" = "$base_obs" ]; then
      fail "control mutated-body: the mutated body did not change the projection ($mut_obs)"
    elif [ "$mut_obs" = "$accept_obs" ]; then
      fail "control mutated-body: the mutated projection still equals the object's row"
    else
      printf 'control mutated-body: red (%s: object/model %s, mutated %s)\n' \
        "$accept_name" "$base_obs" "$mut_obs"
    fi
  fi
fi

# ------------------------------------------------------------------ control c --
# A tampered object: one constant in stage2.c, rebuilt at the route's line.
kflags=(-O2 -march=x86-64-v3 -mpclmul -std=gnu11 -falign-loops=64
        -falign-functions=64 -I "$kernel")
tampered_src="$work/stage2-tampered.c"
cp "$kernel/stage2.c" "$tampered_src"
sed -i 's/return r ? 1 : 0;/return r ? 0 : 1;/' "$tampered_src"
if [ "$(grep -c 'return r ? 0 : 1;' "$tampered_src")" -ne 1 ]; then
  fail "control tampered-object: the temporary stage2.c did not take exactly one verdict flip"
elif [ -z "$accept_doc" ]; then
  fail "control tampered-object: no accepted row was available to compare"
else
  printf 'control tampered-object: source sha256: %s\n' \
    "$(sha256sum "$tampered_src" | cut -d' ' -f1)"
  if ! clang "${kflags[@]}" -c "$tampered_src" -o "$work/stage2-tampered.o" \
        2>"$work/tamper.build.err"; then
    fail "control tampered-object: the tampered unit did not compile"
    cat "$work/tamper.build.err" >&2
  elif ! clang "${kflags[@]}" "$driver_src" \
        "$here/build/pipeline.o" "$here/build/s1_block.o" "$here/build/entry.o" \
        "$here/build/escape.o" "$here/build/utf8.o" "$work/stage2-tampered.o" \
        -o "$work/driver-tampered" 2>"$work/tamper.link.err"; then
    fail "control tampered-object: the tampered driver did not link"
    cat "$work/tamper.link.err" >&2
  else
    printf 'control tampered-object: driver sha256: %s\n' \
      "$(sha256sum "$work/driver-tampered" | cut -d' ' -f1)"
    "$work/driver-tampered" "$accept_doc" >"$work/tampered.out" 2>"$work/tampered.err"
    ts=$?
    if [ "$ts" -ne 0 ]; then
      fail "control tampered-object: the tampered driver exited $ts"
      cat "$work/tampered.err" >&2
    else
      tam_obs=$(observation_of "$work/tampered.out")
      "$model" --doc "$accept_doc" >"$work/base-model.out" 2>&1
      base_obs=$(grep -m1 '^verdict=' "$work/base-model.out" || true)
      if [ -z "$tam_obs" ]; then
        fail "control tampered-object: the tampered driver printed no observation"
      elif [ "$tam_obs" = "$base_obs" ]; then
        fail "control tampered-object: the tampered object still equals the model ($tam_obs)"
      else
        printf 'control tampered-object: red (%s: model %s, tampered object %s)\n' \
          "$accept_name" "$base_obs" "$tam_obs"
      fi
    fi
  fi
fi

# -------------------------------------------------------------------- summary --
printf 'rows=%s compared=%s outside=%s mismatches=%s\n' \
  "$rows" "$compared" "$outside" "$mismatches"
if [ "$failed" -ne 0 ]; then
  printf 'FAIL: %s assertion(s) failed\n' "$failed" >&2
  exit 1
fi
if [ "$compared" -eq 0 ]; then
  printf 'FAIL: no row was compared\n' >&2
  exit 1
fi
printf 'ok: %s admitted row(s) agree with the model; each control went red\n' \
  "$compared"
exit 0
