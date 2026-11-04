#!/usr/bin/env bash
# The JSON subtree's import boundary.
#
# Four claims are checked against the actual Lean `import` declarations:
#
#   1. `Parse.lean` imports exactly `LeanLLVM.JSON.Spec`, `LeanLLVM.JSON.Scan`
#      and `LeanLLVM.JSON.Tape`, so the reference parser cannot reach the block
#      layer or the model above it;
#   2. no module under `LeanLLVM/JSON/` other than the four model modules imports
#      any of the four, so the model is reached only from the modules that build
#      it and from the umbrella;
#   3. `ScanBlock.lean` imports `LeanLLVM.JSON.Bytes` and nothing else, so the
#      block layer cannot reach the parser's chain in the other direction;
#   4. no module of the umbrella's own chain — `Spec`, `Utf8`, `Scan`, `Tape`,
#      `Parse`, `TapeCorrect`, `Correct` — names the block layer or the model in an
#      `import` line.
#
# The umbrella `LeanLLVM/JSON.lean` is the one source that imports the model, and it
# imports all four: an absence claim about every other file is worth checking only
# beside the presence claim that puts the model somewhere.  The four model modules'
# own import sets are checked as well, so the one direction that must exist is exact
# rather than merely present.
#
# Each claim is a filter over module names, defined once below.  Before every absence
# assertion the same filter is run on an in-memory sample that must be caught by it,
# and — where the corpus allows — on a file it must catch, so a filter that matches
# nothing cannot pass as an absence.
#
# Usage: bash tests/json-import-boundary.sh
set -euo pipefail
cd "$(dirname "$0")/.."

fail=0
report() { printf 'FAIL: %s\n' "$*" >&2; fail=1; }

# Print the module names of a file's Lean `import` declarations.  Block and line
# comments are removed first, and only lines of the form `import M ...` are
# taken, so a commented-out or quoted mention is not an import.  Several modules
# may be listed on one line.
imports_of() {
  awk '
    BEGIN { inblock = 0 }
    {
      line = $0; out = ""; i = 1; n = length(line)
      while (i <= n) {
        two = substr(line, i, 2)
        if (inblock) {
          if (two == "-/") { inblock = 0; i += 2 } else { i += 1 }
          continue
        }
        if (two == "/-") { inblock = 1; i += 2; continue }
        if (two == "--") { break }
        out = out substr(line, i, 1)
        i += 1
      }
      if (out ~ /^[ \t]*import[ \t]+[^ \t]/) {
        sub(/^[ \t]*import[ \t]+/, "", out); sub(/[ \t]+$/, "", out)
        nf = split(out, mods, /[ \t]+/)
        for (k = 1; k <= nf; k++) print mods[k]
      }
    }
  ' "$@"
}

# --- the detectors -----------------------------------------------------------
# Each reads module names on stdin, one per line, and prints what it selects.

# One of the four model modules.
model_hits() {
  grep -E '^LeanLLVM\.JSON\.(ScanBody|ScanWindow|ScanString|ScanBlocks)$' || true
}

# The block layer or the model, as an import name.
block_layer_hits() {
  grep -E '^LeanLLVM\.JSON\.(ScanBlock|ScanBody|ScanWindow|ScanString|ScanBlocks)$' || true
}

# Anything `Parse.lean` may not import: everything but its three.
parse_extras() {
  grep -vxE '^LeanLLVM\.JSON\.(Spec|Scan|Tape)$' || true
}

# Anything `ScanBlock.lean` may not import: everything but the carrier.
bytes_only_extras() {
  grep -vxE '^LeanLLVM\.JSON\.Bytes$' || true
}

# 0 iff the file's import set is exactly the space-separated list in $2.
imports_equal() {
  local f=$1 want got
  want=$(printf '%s\n' $2 | sort -u | tr '\n' ' ')
  got=$(imports_of "$f" | sort -u | tr '\n' ' ')
  [ "$got" = "$want" ]
}

# --- positive controls, one per detector, before any absence assertion -------
tmp=$(mktemp)
trap 'rm -f "$tmp"' EXIT

printf 'import LeanLLVM.JSON.Spec\nimport LeanLLVM.JSON.Scan\nimport LeanLLVM.JSON.Tape\n' > "$tmp"
imports_equal "$tmp" "LeanLLVM.JSON.Tape LeanLLVM.JSON.Scan LeanLLVM.JSON.Spec" ||
  report "control: the exact-set detector rejected the three imports 'Parse.lean' may have"
printf 'import LeanLLVM.JSON.Spec\nimport LeanLLVM.JSON.Scan\nimport LeanLLVM.JSON.Tape\nimport LeanLLVM.JSON.ScanBlock\n' > "$tmp"
if imports_equal "$tmp" "LeanLLVM.JSON.Spec LeanLLVM.JSON.Scan LeanLLVM.JSON.Tape"; then
  report "control: the exact-set detector missed an in-memory 'import LeanLLVM.JSON.ScanBlock'"
fi
echo "control: exact-set detector accepts the allowed three and catches an extra import"
printf 'import LeanLLVM.JSON.Spec\nimport LeanLLVM.JSON.Scan\nimport LeanLLVM.JSON.ScanBlock\n' > "$tmp"
hits=$(imports_of "$tmp" | parse_extras)
[ -n "$hits" ] || report "control: the Parse detector missed an in-memory 'import LeanLLVM.JSON.ScanBlock'"
printf 'import LeanLLVM.JSON.Spec\nimport LeanLLVM.JSON.Scan\nimport LeanLLVM.JSON.Tape\n' > "$tmp"
hits=$(imports_of "$tmp" | parse_extras)
[ -z "$hits" ] || report "control: the Parse detector flagged the three imports it allows"
echo "control: Parse detector catches a fourth import and passes the three allowed"

printf 'import LeanLLVM.JSON.ScanBlock\nimport LeanLLVM.JSON.ScanWindow\n' > "$tmp"
hits=$(imports_of "$tmp" | model_hits)
[ -n "$hits" ] || report "control: the model detector missed in-memory imports of ScanWindow and ScanBlock"
printf 'import LeanLLVM.JSON.Spec\nimport LeanLLVM.JSON.Scan\n' > "$tmp"
hits=$(imports_of "$tmp" | model_hits)
[ -z "$hits" ] || report "control: the model detector flagged the parser's own imports"
hits=$(imports_of LeanLLVM/JSON/ScanWindow.lean | model_hits | wc -l)
[ "$hits" -ge 1 ] || report "control: the model detector found no model import in LeanLLVM/JSON/ScanWindow.lean"
echo "control: model detector catches in-memory model imports and the model import in LeanLLVM/JSON/ScanWindow.lean"

printf 'import LeanLLVM.JSON.Bytes\n' > "$tmp"
imports_equal "$tmp" "LeanLLVM.JSON.Bytes" ||
  report "control: the exact-set detector rejected 'LeanLLVM.JSON.Bytes' alone"
printf 'import LeanLLVM.JSON.Bytes\nimport LeanLLVM.JSON.Scan\n' > "$tmp"
imports_equal "$tmp" "LeanLLVM.JSON.Bytes" &&
  report "control: the exact-set detector missed a second import beside 'LeanLLVM.JSON.Bytes'"
printf 'import LeanLLVM.JSON.Bytes\nimport LeanLLVM.JSON.Scan\n' > "$tmp"
hits=$(imports_of "$tmp" | bytes_only_extras)
[ -n "$hits" ] || report "control: the carrier-only detector missed an in-memory 'import LeanLLVM.JSON.Scan'"
echo "control: carrier-only detector catches a second import and passes bytes alone"

printf 'import LeanLLVM.JSON.ScanBlock\n' > "$tmp"
hits=$(imports_of "$tmp" | block_layer_hits)
[ -n "$hits" ] || report "control: the chain detector missed an in-memory 'import LeanLLVM.JSON.ScanBlock'"
printf 'import LeanLLVM.JSON.Scan\n' > "$tmp"
hits=$(imports_of "$tmp" | block_layer_hits)
[ -z "$hits" ] || report "control: the chain detector flagged the parser's own 'import LeanLLVM.JSON.Scan'"
printf -- '-- import LeanLLVM.JSON.ScanBlock\n/- import LeanLLVM.JSON.ScanBlocks -/\n' > "$tmp"
hits=$(imports_of "$tmp" | block_layer_hits)
[ -z "$hits" ] || report "control: a commented-out import was read as an import"
echo "control: chain detector catches 'import LeanLLVM.JSON.ScanBlock' and ignores commented-out mentions"

printf 'import LeanLLVM.JSON.ScanBody\nimport LeanLLVM.JSON.ScanWindow\n' > "$tmp"
[ "$(imports_of "$tmp" | model_hits | wc -l)" -eq 2 ] ||
  report "control: the umbrella presence count does not count"
echo "control: umbrella presence count measures two model imports in a two-line sample"

# --- 1. `Parse.lean` imports exactly its three ------------------------------
imports_equal LeanLLVM/JSON/Parse.lean \
  "LeanLLVM.JSON.Spec LeanLLVM.JSON.Scan LeanLLVM.JSON.Tape" ||
  report "LeanLLVM/JSON/Parse.lean imports $(imports_of LeanLLVM/JSON/Parse.lean | tr '\n' ' ')(expected Spec, Scan and Tape)"
hits=$(imports_of LeanLLVM/JSON/Parse.lean | parse_extras)
[ -z "$hits" ] || report "LeanLLVM/JSON/Parse.lean imports $hits"

# --- 2. only the model modules and the umbrella import the model -------------
mapfile -t json_files < <(find LeanLLVM/JSON -name '*.lean' | sort)
for f in "${json_files[@]}"; do
  case "$f" in
    LeanLLVM/JSON/ScanBody.lean|LeanLLVM/JSON/ScanWindow.lean|\
    LeanLLVM/JSON/ScanString.lean|LeanLLVM/JSON/ScanBlocks.lean) continue ;;
  esac
  bad=$(imports_of "$f" | model_hits)
  [ -z "$bad" ] || report "$f imports the model: $bad"
done
model_importers=""
for f in "${json_files[@]}" LeanLLVM/JSON.lean; do
  if imports_of "$f" | model_hits | grep -q .; then model_importers="$model_importers $f"; fi
done
echo "model importers:${model_importers:- none}"

# --- 3. `ScanBlock.lean` imports the carrier alone ---------------------------
imports_equal LeanLLVM/JSON/ScanBlock.lean "LeanLLVM.JSON.Bytes" ||
  report "LeanLLVM/JSON/ScanBlock.lean imports $(imports_of LeanLLVM/JSON/ScanBlock.lean | tr '\n' ' ')(expected LeanLLVM.JSON.Bytes)"
hits=$(imports_of LeanLLVM/JSON/ScanBlock.lean | bytes_only_extras)
[ -z "$hits" ] || report "LeanLLVM/JSON/ScanBlock.lean imports $hits"

# --- 4. the parser's chain does not reach the block layer or the model -------
chain=(Spec Utf8 Scan Tape Parse TapeCorrect Correct)
for m in "${chain[@]}"; do
  f="LeanLLVM/JSON/$m.lean"
  [ -f "$f" ] || report "$f is missing from the umbrella's chain"
  bad=$(imports_of "$f" | block_layer_hits)
  [ -z "$bad" ] || report "$f imports $bad"
done

# --- the umbrella imports all four, and each model module's own set is exact --
[ "$(imports_of LeanLLVM/JSON.lean | model_hits | wc -l)" -eq 4 ] ||
  report "LeanLLVM/JSON.lean imports $(imports_of LeanLLVM/JSON.lean | model_hits | tr '\n' ' ')(expected all four model modules)"
imports_equal LeanLLVM/JSON/ScanBody.lean "LeanLLVM.JSON.ScanBlock LeanLLVM.JSON.Utf8" ||
  report "LeanLLVM/JSON/ScanBody.lean imports $(imports_of LeanLLVM/JSON/ScanBody.lean | tr '\n' ' ')"
imports_equal LeanLLVM/JSON/ScanWindow.lean "LeanLLVM.JSON.ScanBlock LeanLLVM.JSON.ScanBody" ||
  report "LeanLLVM/JSON/ScanWindow.lean imports $(imports_of LeanLLVM/JSON/ScanWindow.lean | tr '\n' ' ')"
imports_equal LeanLLVM/JSON/ScanString.lean "LeanLLVM.JSON.ScanWindow" ||
  report "LeanLLVM/JSON/ScanString.lean imports $(imports_of LeanLLVM/JSON/ScanString.lean | tr '\n' ' ')"
imports_equal LeanLLVM/JSON/ScanBlocks.lean "LeanLLVM.JSON.ScanString LeanLLVM.JSON.Scan" ||
  report "LeanLLVM/JSON/ScanBlocks.lean imports $(imports_of LeanLLVM/JSON/ScanBlocks.lean | tr '\n' ' ')"

if [ "$fail" -ne 0 ]; then
  echo "import boundary check failed" >&2
  exit 1
fi
echo "import boundary check passed"
