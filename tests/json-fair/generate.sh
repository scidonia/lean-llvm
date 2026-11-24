#!/usr/bin/env bash
# Generate the fair corpus and pin it against `manifest.tsv`.
#
#   nix develop -c bash tests/json-fair/generate.sh             # materialise
#   nix develop -c bash tests/json-fair/generate.sh --verify    # assert an existing corpus
#   nix develop -c bash tests/json-fair/generate.sh --check     # regenerate, do not keep
#   nix develop -c bash tests/json-fair/generate.sh --check --exit-tmp
#
# The corpus is 151 documents in two groups:
#
#   the 148 heterogeneous documents of `gen.py`: four styles
#     (`pretty`, `tab`, `compact`, `spaced`) at seven sizes from 512 B to 1 MiB
#     with five seeds each, plus `deep` and `escapes` at 64 KiB and 256 KiB with
#     two seeds each.  Every document is at most 1 MiB, the route's input bound.
#     `gen.py` is the text of the generator the corpus was measured with; its
#     first line records where it was copied from and that file's sha256.
#   the three canonical 64 KiB documents (`dense`, `strings`, `utf8`) of
#     `tests/json-units-bench/gen.c` at its fixed splitmix64 seed, the same
#     bytes the stage-1 unit measurement used.
#
# Every document's size and sha256 is in `manifest.tsv`; this script asserts
# both for every row, so a generator, a toolchain or a locale that changes a
# byte is a failure and not a silently different corpus.  `gen.py`'s own
# manifest is also compared with the committed one, which is what makes the
# 148 rows a checked copy of the measured corpus rather than a retyping.
#
# `--verify` generates nothing: it asserts that a materialised corpus still
# matches the manifest, which is what the measurement harness runs before it
# times anything.  `--check` writes the documents into a private temporary
# directory and removes them, so it can run beside a materialised corpus and
# without write access to the repository.  It also runs a positive control: one byte of one
# generated document is flipped in a copy and the same per-row check that
# verified the corpus must reject it, so a detector that matches nothing
# cannot pass as green.
#
# `--exit-tmp` additionally compares the 148 heterogeneous documents
# byte-for-byte with the corpus that was measured in `/tmp`, by reading only.
# It is the one-time check that the port is a copy and not a reimplementation;
# once it has run, the repository (the generator plus the manifest) is the
# source of truth and the `/tmp` directory may be removed.  Run it only while
# that directory still exists; an absent source is a setup failure, never a
# pass.
#
# Environment: FAIR_CORPUS (the materialised directory,
# `tests/json-fair/corpus`), FAIR_TMP_SOURCE (`/tmp/hetero-corpus-large`),
# FAIR_CC (clang).
#
# Exit status: 0 when every row was generated and every check held, 1 when a
# document or the control disagrees with the manifest, 3 when the route is not
# usable (an absent or malformed manifest, an absent generator, `gen.c` or
# compiler, or a `--exit-tmp` run whose source directory is absent).
set -uo pipefail
export LC_ALL=C

here=$(cd "$(dirname "$0")" && pwd)
repo=$(cd "$here/../.." && pwd)
manifest=$here/manifest.tsv
genpy=$here/gen.py
genc=$repo/tests/json-units-bench/gen.c
cc=${FAIR_CC:-clang}
tmp_source=${FAIR_TMP_SOURCE:-/tmp/hetero-corpus-large}

mode=materialise
exit_tmp=0
out=${FAIR_CORPUS:-$here/corpus}

for arg in "$@"; do
  case "$arg" in
    --check) mode=check ;;
    --verify) mode=verify ;;
    --exit-tmp) exit_tmp=1 ;;
    --out=*) out=${arg#--out=} ;;
    -h|--help) sed -n '2,60p' "$0"; exit 0 ;;
    *) printf 'SETUP: unknown argument %s\n' "$arg" >&2; exit 3 ;;
  esac
done

die() { printf 'SETUP: %s\n' "$*" >&2; exit 3; }
fail() { printf 'FAIL: %s\n' "$*" >&2; exit 1; }

[ -f "$manifest" ] || die "absent manifest: $manifest"
[ -f "$genpy" ] || die "absent generator: $genpy"
[ -f "$genc" ] || die "absent canonical generator: $genc"
command -v python3 >/dev/null 2>&1 || die "no python3 on PATH; run this under nix develop"
command -v "$cc" >/dev/null 2>&1 || die "no $cc on PATH; run this under nix develop"

rows=$(awk 'END { print NR - 1 }' "$manifest")
[ "$rows" = 151 ] || die "manifest has $rows rows, not 151"
[ "$(head -1 "$manifest")" = "$(printf 'file\tstyle\ttarget_bytes\trecords\tbytes\tsha256\troot\tseed\tmax_depth\tseed_index')" ] ||
  die "manifest header is not the fair corpus header"

cleanup=""
if [ "$mode" = check ]; then
  out=$(mktemp -d "${TMPDIR:-/tmp}/json-fair.XXXXXX") || die "cannot create a temporary directory"
  cleanup=$out
else
  [ -n "$out" ] && [ "$out" != "/" ] || die "refusing output directory '$out'"
  mkdir -p "$out" || die "cannot create $out"
fi
trap '[ -n "$cleanup" ] && rm -rf "$cleanup"' EXIT

# The same per-row check is the corpus's assertion and the positive control's
# subject: size first, then sha256, both from the manifest.
verify_row() { # <path> <bytes> <sha256>
  local path=$1 size=$2 want=$3 got_size got_sha
  if [ ! -f "$path" ]; then
    printf '  %s: absent\n' "$path" >&2
    return 1
  fi
  got_size=$(stat -c %s "$path") || return 1
  if [ "$got_size" != "$size" ]; then
    printf '  %s: %s bytes, manifest %s\n' "$path" "$got_size" "$size" >&2
    return 1
  fi
  got_sha=$(sha256sum "$path" | cut -d' ' -f1)
  if [ "$got_sha" != "$want" ]; then
    printf '  %s: sha256 %s, manifest %s\n' "$path" "$got_sha" "$want" >&2
    return 1
  fi
  return 0
}

# --- Generation -------------------------------------------------------------
if [ "$mode" != verify ]; then
# `gen.py` is the measured file unchanged apart from its first line, so its
# output directory is overridden in the importing process rather than by
# editing the text.
PYTHONDONTWRITEBYTECODE=1 python3 - "$genpy" "$out" <<'PY' || fail "gen.py did not generate the 148 documents"
import importlib.util
import sys

path, out = sys.argv[1], sys.argv[2]
spec = importlib.util.spec_from_file_location("json_fair_gen", path)
mod = importlib.util.module_from_spec(spec)
spec.loader.exec_module(mod)
mod.OUT = out
raise SystemExit(mod.main())
PY

# gen.py writes its own manifest, which is the 148 rows the committed manifest
# was copied from; a difference means the committed rows and the generator
# have drifted apart.  The extra files are then removed, because the corpus
# directory holds the documents and nothing else.
if ! head -149 "$manifest" | cmp -s - "$out/manifest.tsv"; then
  fail "gen.py's manifest differs from the committed 148 rows"
fi
rm -f "$out/manifest.tsv" "$out/meta.txt"

# --- The three canonical 64 KiB documents -----------------------------------
tmpbin=$(mktemp -d "${TMPDIR:-/tmp}/json-fair-gen.XXXXXX") || die "cannot create a temporary directory"
"$cc" -O2 "$genc" -o "$tmpbin/gen" || die "gen.c did not build"
for shape in dense strings utf8; do
  "$tmpbin/gen" --shape "$shape" --size 65536 --out "$out/syn-$shape-64k.json" ||
    fail "gen.c did not write syn-$shape-64k.json"
done
rm -rf "$tmpbin"
fi

# --- Every row, and nothing outside the rows --------------------------------
[ -d "$out" ] || fail "absent corpus directory: $out"
present=$(find "$out" -maxdepth 1 -type f -name '*.json' | wc -l)
[ "$present" = 151 ] || fail "corpus holds $present documents, not 151"

checked=0
while IFS=$'\t' read -r file _style _target _records bytes sha _root _seed _depth _si; do
  [ "$file" = "file" ] && continue
  verify_row "$out/$file" "$bytes" "$sha" || fail "corpus disagrees with the manifest"
  checked=$((checked + 1))
done < "$manifest"
[ "$checked" = 151 ] || fail "checked $checked rows, not 151"

# --- The positive control ---------------------------------------------------
# One byte of a copy of a generated document is flipped; the same per-row
# check must reject it.  The control is a separate directory so the corpus is
# never touched.
ctrl=$(mktemp -d "${TMPDIR:-/tmp}/json-fair-ctrl.XXXXXX") || die "cannot create a temporary directory"
ctrl_file=hetero-pretty-0000512-s0-000.json
cp "$out/$ctrl_file" "$ctrl/$ctrl_file" || die "cannot copy the control document"
python3 - "$ctrl/$ctrl_file" <<'PY' || die "cannot mutate the control document"
import sys
p = sys.argv[1]
b = bytearray(open(p, "rb").read())
if not b:
    raise SystemExit("empty control document")
b[0] ^= 0xFF
open(p, "wb").write(b)
PY
ctrl_size=$(awk -F'\t' -v f="$ctrl_file" '$1 == f { print $5 }' "$manifest")
ctrl_sha=$(awk -F'\t' -v f="$ctrl_file" '$1 == f { print $6 }' "$manifest")
if verify_row "$ctrl/$ctrl_file" "$ctrl_size" "$ctrl_sha" 2>"$ctrl/why"; then
  rm -rf "$ctrl"
  fail "the positive control passed: a one-byte mutation was not detected"
fi
ctrl_why=$(cat "$ctrl/why")
rm -rf "$ctrl"

# --- The one-time comparison with the measured /tmp corpus ------------------
compared=0
if [ "$exit_tmp" = 1 ]; then
  [ -d "$tmp_source" ] || die "the /tmp corpus is absent: $tmp_source
  --exit-tmp is the one-time port check and needs the measured copies"
  while IFS=$'\t' read -r file _style _target _records _bytes _sha _root _seed _depth _si; do
    [ "$file" = "file" ] && continue
    case "$file" in hetero-*) ;; *) continue ;; esac
    cmp -s "$out/$file" "$tmp_source/$file" ||
      fail "$file differs from $tmp_source/$file"
    compared=$((compared + 1))
  done < "$manifest"
  [ "$compared" = 148 ] || fail "compared $compared documents with /tmp, not 148"
fi

printf 'generator: %s sha256=%s (first line is the source record)\n' \
  "$genpy" "$(sha256sum "$genpy" | cut -d' ' -f1)"
printf 'documents: %d; sha256 and size match the manifest: %d\n' "$present" "$checked"
if [ "$compared" -gt 0 ]; then
  printf 'byte-identical to %s: %d/148\n' "$tmp_source" "$compared"
fi
printf 'positive control: a one-byte mutation rejected (%s)\n' "$ctrl_why"
case "$mode" in
  materialise) printf 'corpus: %s\n' "$out" ;;
  verify) printf 'verified: %s\n' "$out" ;;
  check) printf 'check: regenerated in %s and discarded\n' "$out" ;;
esac
exit 0
