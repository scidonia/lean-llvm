#!/usr/bin/env bash
# Refusal census over the LLVM IR corpus this repository ships.
#
# Corpus: every tracked `*.ll` file.  The manifest is the expectation, so both
# directions are checked: a file the manifest says parses must parse, and a file
# it says is refused must be refused with the named token.  A driver that
# accepts everything fails on the refused entries; one that refuses everything
# fails on the parsed ones.
#
# The driver must be built after the library it runs:
#
#   nix develop -c bash probes/install/lake-locked.sh build leanllvm
#
# Usage: [--driver PATH] [--all]
#   --all  also print the split over the working tree's IR (tracked files plus
#          generated build output).  That split is informational: the generated
#          files are not tracked, so they are not part of the checked manifest.
set -euo pipefail

here=$(cd "$(dirname "$0")" && pwd)
repo=$(cd "$here/../.." && pwd)
driver="$repo/.lake/build/bin/leanllvm"
manifest="$here/repo-corpus.manifest"
scan_all=0

while [ "$#" -gt 0 ]; do
  case "$1" in
    --driver) shift; driver=${1:-} ;;
    --all) scan_all=1 ;;
    *) echo "repo-census: unknown argument '$1'" >&2; exit 2 ;;
  esac
  shift
done

[ -n "$driver" ] && [ -x "$driver" ] || {
  echo "repo-census: no executable driver at '$driver'" >&2
  echo "repo-census: build it first: nix develop -c bash probes/install/lake-locked.sh build leanllvm" >&2
  exit 2
}

cd "$repo"

mapfile -t tracked < <(git ls-files '*.ll' | sort)

err=$(mktemp)
trap 'rm -f "$err"' EXIT

mismatch=0
parsed=0
refused=0
seen=""

while IFS=$'\t' read -r outcome path token; do
  [ -n "$outcome" ] || continue
  if ! printf '%s\n' "${tracked[@]}" | grep -qxF -- "$path"; then
    echo "repo-census: manifest names a path the corpus does not track: $path" >&2
    mismatch=1
    continue
  fi
  seen+="$path"$'\n'
  if "$driver" "$path" --passes none -o /dev/null 2>"$err"; then
    got=parsed
  else
    got=refused
  fi
  if [ "$got" != "$outcome" ]; then
    echo "repo-census: expected $outcome, got $got: $path" >&2
    mismatch=1
  fi
  if [ "$got" = refused ] && [ -n "${token:-}" ] && ! grep -qF -- "$token" "$err"; then
    echo "repo-census: refusal for $path does not name '$token'" >&2
    mismatch=1
  fi
  case "$got" in
    parsed) parsed=$((parsed + 1)) ;;
    refused) refused=$((refused + 1)) ;;
  esac
done < "$manifest"

missing=$(printf '%s\n' "${tracked[@]}" | while read -r p; do
  printf '%s' "$seen" | grep -qxF -- "$p" || printf '%s\n' "$p"
done)
if [ -n "$missing" ]; then
  echo "repo-census: manifest omits tracked file(s):" >&2
  printf '%s\n' "$missing" >&2
  mismatch=1
fi

ptr_lines=$(git ls-files '*.ll' | xargs grep -lE 'icmp[[:space:]]+(samesign[[:space:]]+)?[a-z]+[[:space:]]+ptr\b' 2>/dev/null | wc -l || true)
sig_lines=$(git ls-files '*.ll' | xargs grep -lE 'call[^=]*\([^()]*\)[[:space:]]*@' 2>/dev/null | wc -l || true)
veclit_lines=$(git ls-files '*.ll' | xargs grep -lE '<i[0-9]+[[:space:]]+(-?[0-9]|undef|poison)' 2>/dev/null | wc -l || true)
extract_lines=$(git ls-files '*.ll' | xargs grep -lE '^[[:space:]]*%[^[:space:]]*[[:space:]]*=[[:space:]]*extractelement[[:space:]]' 2>/dev/null | wc -l || true)
insert_lines=$(git ls-files '*.ll' | xargs grep -lE '^[[:space:]]*%[^[:space:]]*[[:space:]]*=[[:space:]]*insertelement[[:space:]]' 2>/dev/null | wc -l || true)
zeroinit_lines=$(git ls-files '*.ll' | xargs grep -lE '\bzeroinitializer\b' 2>/dev/null | wc -l || true)

echo "tracked corpus: $((parsed + refused)) files, $parsed parsed, $refused refused ($(printf '%s\n' "${tracked[@]}" | xargs grep -c '^define ' 2>/dev/null | awk -F: '{s+=$2} END{print s+0}') defines)"
echo "corpus coverage: $ptr_lines file(s) with an 'icmp ... ptr' line, $sig_lines file(s) with a written callee function type"
echo "corpus coverage: $veclit_lines file(s) with a literal vector operand, $extract_lines file(s) with an 'extractelement' line, $insert_lines file(s) with an 'insertelement' line, $zeroinit_lines file(s) with a 'zeroinitializer' operand"

if [ "$scan_all" = 1 ]; then
  all_parsed=0
  all_refused=0
  while read -r f; do
    if "$driver" "${f#./}" --passes none -o /dev/null 2>"$err"; then
      all_parsed=$((all_parsed + 1))
    else
      all_refused=$((all_refused + 1))
    fi
  done < <(find . -name '*.ll' -not -path './.lake/*' | sort)
  echo "working-tree corpus (tracked + generated): $((all_parsed + all_refused)) files, $all_parsed parsed, $all_refused refused"
fi

exit "$mismatch"
