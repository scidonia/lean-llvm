#!/usr/bin/env bash
# The import boundary of the generic interaction-tree library.
#
# Three claims are checked against the actual Lean `import` declarations:
#
#   1. no generic `ITree` source imports a `LeanLLVM` module, directly or
#      through another local `ITree` module, so `lake build ITree` builds
#      without the LLVM instantiation;
#   2. exactly two repository sources import mathlib directly, the adapters
#      `ITree/Internal/FloatingPoint.lean` and `ITree/Internal/PFunctor.lean`,
#      and every other module reaches mathlib through one of them; the
#      floating-point adapter also exports the carrier's three constructors, so
#      a client can build a value without naming mathlib's namespace;
#   3. the generic modules import nothing outside `ITree.*`, mathlib (only the
#      adapters) and Lean's own core libraries, and the host layer reaches the
#      generic library through its public entrypoints.
#
# Each claim is a filter over module names, defined once below.  Before every
# absence assertion the same filter is run on an in-memory sample that must be
# caught by it, so a filter that matches nothing cannot pass as an absence.
#
# Usage: bash tests/itree-boundary.sh
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

# A module of the LLVM instantiation.
leanllvm_hits() { grep -E '^LeanLLVM(\.|$)' || true; }

# Modules a generic module may import: its own, mathlib (which only the adapter
# imports), and Lean's core libraries.  Anything else is a violation.
allowlist_violations() {
  grep -vE '^(ITree(\.|$)|Mathlib\.|Lean(\.|$)|Init(\.|$)|Std(\.|$)|Batteries(\.|$)|Qq(\.|$))' || true
}

# A generic module reached past the public entrypoints.
generic_internal_hits() { grep -E '^ITree\.Internal(\.|$)' || true; }

# A direct mathlib importer.
mathlib_hits() { grep -E '^Mathlib\.' || true; }

# The names on the `export FP.Float (...)` lines of the files given, one per
# line and sorted, restricted to the carrier's constructors.  Line comments are
# removed first, so a commented-out export is not counted.  Unlike the
# detectors above this one reads files rather than stdin, because the claim it
# serves is about a file's own export list rather than about module names.
exported_float_ctors() {
  sed -E 's/--.*$//' "$@" \
    | grep -E '^[[:space:]]*export[[:space:]]+FP\.Float[[:space:]]*\(' \
    | sed -E 's/^[^(]*\(//; s/\).*$//' \
    | tr -s '[:space:]' '\n' \
    | grep -Ex 'inf|nan|finite' | sort -u
}

mapfile -t generic_files < <(printf '%s\n' ITree.lean; find ITree -name '*.lean' | sort)
mapfile -t host_files < <(printf '%s\n' LeanLLVM/ITree.lean; find LeanLLVM/ITree -name '*.lean' | sort)
mapfile -t all_files < <(
  find . -path ./.lake -prune -o -path ./.git -prune -o -path ./reference -prune \
    -o -name '*.lean' -print | sort
)

echo "generic modules:"
for f in "${generic_files[@]}"; do printf '  %s\n' "$f"; done

# --- positive controls, one per detector, before any absence assertion ------
tmp=$(mktemp)
trap 'rm -f "$tmp"' EXIT

printf 'import LeanLLVM.Semantics\n' > "$tmp"
hits=$(imports_of "$tmp" | leanllvm_hits | wc -l)
[ "$hits" -ge 1 ] || report "control: the LeanLLVM detector missed an in-memory 'import LeanLLVM.Semantics'"
echo "control: LeanLLVM detector catches an in-memory 'import LeanLLVM.Semantics' ($hits hit)"

printf 'import ITree.Core\nimport Mathlib.Data.Vector3\nimport Lean.Data.HashMap\nimport Init.Prelude\n' > "$tmp"
hits=$(imports_of "$tmp" | allowlist_violations | wc -l)
[ "$hits" -eq 0 ] || report "control: the allowlist flagged an allowed import ($hits hit)"
printf 'import ITree.Core\nimport SomeOther.Module\n' > "$tmp"
hits=$(imports_of "$tmp" | allowlist_violations)
[ -n "$hits" ] || report "control: the allowlist missed an in-memory 'import SomeOther.Module'"
echo "control: allowlist accepts the allowed set and catches 'import SomeOther.Module' (caught: ${hits//$'\n'/, })"

printf 'import ITree.Internal.PFunctor\n' > "$tmp"
hits=$(imports_of "$tmp" | generic_internal_hits | wc -l)
[ "$hits" -ge 1 ] || report "control: the generic-internal detector missed an in-memory 'import ITree.Internal.PFunctor'"
printf 'import ITree.Core\n' > "$tmp"
hits=$(imports_of "$tmp" | generic_internal_hits | wc -l)
[ "$hits" -eq 0 ] || report "control: the generic-internal detector flagged an entrypoint import"
echo "control: generic-internal detector catches 'import ITree.Internal.PFunctor' and passes 'import ITree.Core'"

adapters=(
  ./ITree/Internal/FloatingPoint.lean
  ./ITree/Internal/PFunctor.lean
)
for adapter in "${adapters[@]}"; do
  adapter_mathlib=$(imports_of "${adapter#./}" | mathlib_hits | wc -l)
  [ "$adapter_mathlib" -ge 1 ] \
    || report "control: the mathlib detector found nothing in $adapter"
  echo "control: mathlib detector finds $adapter_mathlib direct mathlib imports in $adapter"
done

printf 'export FP.Float (inf nan finite)\n' > "$tmp"
hits=$(exported_float_ctors "$tmp" | tr '\n' ' ')
[ "$hits" = "finite inf nan " ] \
  || report "control: the float-constructor detector missed an in-memory 'export FP.Float (inf nan finite)' (found: '$hits')"
printf -- '-- export FP.Float (inf nan finite)\nexport FP.Float (inf)\n' > "$tmp"
hits=$(exported_float_ctors "$tmp" | tr '\n' ' ')
[ "$hits" = "inf " ] \
  || report "control: the float-constructor detector reported '$hits' for 'export FP.Float (inf)' beside a commented-out full export"
echo "control: float-constructor detector finds all three constructors on a full export and only 'inf' on a partial one"

# --- 1. no generic LeanLLVM import ------------------------------------------
for f in "${generic_files[@]}"; do
  bad=$(imports_of "$f" | leanllvm_hits)
  [ -z "$bad" ] || report "$f imports $bad"
done

# --- 2. the generic allowlist ------------------------------------------------
# The transitive step: every local import of a generic module is itself generic,
# so no local edge can leave the library.
for f in "${generic_files[@]}"; do
  bad=$(imports_of "$f" | allowlist_violations)
  [ -z "$bad" ] || report "$f imports a module outside the generic boundary: $bad"
done

# --- 3. exactly the two direct mathlib importers ----------------------------
# The inventory is the set of adapter files, in sorted order, and the assertion
# compares against it as a whole: a third importer, or a missing one, changes
# the string and fails.  The adapters' own direct imports are the control
# above, so the detector is shown to fire before this absence is claimed.
expected_direct=" ./ITree/Internal/FloatingPoint.lean ./ITree/Internal/PFunctor.lean"
direct=""
for f in "${all_files[@]}"; do
  if imports_of "$f" | mathlib_hits | grep -q .; then
    direct="$direct $f"
  fi
done
if [ "$direct" != "$expected_direct" ]; then
  report "direct mathlib importers:${direct:- none} (expected${expected_direct} only)"
fi
echo "direct mathlib importers:${direct:- none}"

# The floating-point adapter's surface claim: a client builds values through
# the exported constructors, never through `FP.Float.finite`.  The control
# above shows the detector finds all three on a full export and only one on a
# partial one, so this presence assertion is not made by a filter that matches
# anything.
float_ctors=$(exported_float_ctors ITree/Internal/FloatingPoint.lean | tr '\n' ' ')
if [ "$float_ctors" != "finite inf nan " ]; then
  report "ITree/Internal/FloatingPoint.lean exports '${float_ctors}' from FP.Float (expected 'finite inf nan ')"
fi
echo "floating-point adapter exports from FP.Float: $float_ctors"

# --- 4. the host layer reaches the generic library through its entrypoints ---
for f in "${host_files[@]}"; do
  bad=$(imports_of "$f" | generic_internal_hits)
  [ -z "$bad" ] || report "$f imports a generic Internal module: $bad"
done

if [ "$fail" -ne 0 ]; then
  echo "boundary check failed" >&2
  exit 1
fi
echo "boundary check passed"
