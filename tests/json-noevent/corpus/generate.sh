#!/usr/bin/env bash
# Corpus generator for the no-event stage-2 differential.
#
#   bash tests/json-noevent/corpus/generate.sh <outdir>
#
# <outdir> is created (and its `documents/` and `manifest.tsv` replaced), then
# receives one document per row of `spec.tsv` plus the seeded whitespace family,
# and the manifest that records every document's expected row.
#
# The spec's fields are, tab-separated:
#
#   name    the document's file name under `documents/`
#   arms    `both` (the escape-free arms), `list` (the document carries a
#           backslash or a control byte, so only the list arm is comparable),
#           or `pipeline` (the pipeline route only: the UTF-8 stage's
#           document-level refusal, which the stage-2 boundary never reaches)
#   class   `accept`, or the refusal class of `kernel/json/stage2.h`: the
#           structural, number, literal and string-body rules and the
#           end-of-stream rules (`unclosed`, `no-value`, `unterminated`); or
#           `utf8-gate`, the pipeline's UTF-8 validity stage, whose refusal is
#           the document's end and is read only at the pipeline boundary
#   err     the refusal offset, or `-` on acceptance; an `utf8-gate` row may
#           write `-`, because its offset is the document's length and the
#           generator derives it from the document it writes
#   origin  `-`, or the repository-relative file this document is copied from
#   bytes   the document in the escape form below, or `<empty>` for the empty
#           document when `origin` is `-` (a lone `-` is a one-byte document)
#
# Escape form: `\\` backslash, `\t` tab, `\n` newline, `\r` carriage return,
# `\xHH` one byte.  A copied document is escaped from its own bytes by this
# script, so its bytes never pass through the spec.
#
# The manifest's fields are, tab-separated:
#
#   path     `documents/<name>`
#   arms     as above
#   class    as above
#   verdict  `accept` or `refuse`
#   err      the refusal offset, or `-`
#   tokens   the certified fold's `tokens`, or `-` on refusal
#   values   the certified fold's `values` (= `tokens` in build mode), or `-`
#   sum      16 lowercase hex digits: the fold's `sum` word, or `-`
#   sha256   the document's digest
#   origin   `-`, or the repository-relative file it was copied from
#
# An accepted document's reading is derived here from the document's own bytes
# and the event encoding `kernel/json/stage2.h` states: one event per
# structural token, key, string and scalar; a number is its tag and the
# value's eight IEEE bytes; a key or string is its tag, the decoded length and
# the payload word (the input offset with bit 63 set for a plain body, the
# running decoded extent for an escaped one); the sum adds the arena's decoded
# bytes.  Numbers are looked up in the table below by their exact lexeme, so a
# document that carries a number this table does not pin is refused by the
# generator instead of being read with a guessed bit pattern.
#
# Every accepted document's sum must be below 2^64, the condition under which
# the word is the exact mathematical sum; the accumulator below is two 32-bit
# limbs and reports a document whose exact sum reaches 2^64 as a generator
# error.  The corpus also keeps each accepted document to at most one plain
# (unescaped) key or string and to numbers whose payloads fit beside it, so the
# bound is a property of the corpus and not of the arithmetic luck.
#
# A copied document is verified against its origin: the copy is written only
# after its digest equals the origin's, and the manifest carries that digest.
#
# Exit status: 0 when the corpus and manifest were written, 1 on a document the
# generator cannot read (an unpinned number, a sum at or past 2^64, a copy that
# does not match its origin, a malformed spec row), 2 on a usage fault.
set -uo pipefail

here=$(cd "$(dirname "$0")" && pwd)
repo=$(cd "$here/../../.." && pwd)
spec=$here/spec.tsv
seed_file=$here/seed
out=${1-}

if [ -z "$out" ]; then
  echo "usage: bash $0 <outdir>" >&2
  exit 2
fi
for path in "$spec" "$seed_file"; do
  [ -f "$path" ] || { printf 'generate: absent: %s\n' "$path" >&2; exit 2; }
done

seed=$(tr -d ' \t\n' < "$seed_file")
case $seed in
  '' | *[!0-9]*) printf 'generate: the seed file holds no integer\n' >&2; exit 2 ;;
esac

export LC_ALL=C
mkdir -p "$out/documents"
rm -f "$out/documents"/* "$out/manifest.tsv" || exit 1

fail() { printf 'generate: %s\n' "$1" >&2; exit 1; }

# --------------------------------------------------------------- the reader --
#
# One awk program, two modes.  `mode=bytes` decodes the escape form and prints
# the raw bytes, for writing an authored document.  `mode=scan` decodes and
# walks an accepted document, printing `SMALL <n>`, `TOKENS <n>` and one
# `ADD <hi> <lo>` per payload word (a plain key or string's span record, or a
# number's IEEE bytes); the caller accumulates the 64-bit sum in two limbs.
awk_prog=$(cat <<'AWK'
function hexdec(h,   i, v, d, c) {
  v = 0
  for (i = 1; i <= length(h); i++) {
    c = tolower(substr(h, i, 1))
    d = index("0123456789abcdef", c) - 1
    if (d < 0) return -1
    v = v * 16 + d
  }
  return v
}
function werr(msg) { print "ERR " msg; exit 1 }
function decode(e,   i, n, ch, c2, out) {
  out = ""
  n = length(e)
  for (i = 1; i <= n; i++) {
    ch = substr(e, i, 1)
    if (ch != "\\") { out = out ch; continue }
    i++
    c2 = substr(e, i, 1)
    if (c2 == "\\") out = out sprintf("%c", 92)
    else if (c2 == "t") out = out sprintf("%c", 9)
    else if (c2 == "n") out = out sprintf("%c", 10)
    else if (c2 == "r") out = out sprintf("%c", 13)
    else if (c2 == "x") {
      h = substr(e, i + 1, 2)
      i += 2
      v = hexdec(h)
      if (v < 0) werr("bad \\xHH in the spec")
      out = out sprintf("%c", v)
    } else werr("bad escape in the spec: \\" c2)
  }
  return out
}
function emit_utf8(cp) {
  if (cp < 128) { DLEN++; DSUM += cp }
  else if (cp < 2048) {
    DLEN += 2
    DSUM += 192 + int(cp / 64) + 128 + (cp % 64)
  } else if (cp < 65536) {
    DLEN += 3
    DSUM += 224 + int(cp / 4096) + 128 + int(cp / 64) % 64 + 128 + (cp % 64)
  } else {
    DLEN += 4
    DSUM += 240 + int(cp / 262144) + 128 + int(cp / 4096) % 64 \
           + 128 + int(cp / 64) % 64 + 128 + (cp % 64)
  }
}
function decode_body(b,   i, n, ch, e, h, cp, lo) {
  DLEN = 0
  DSUM = 0
  n = length(b)
  for (i = 1; i <= n; i++) {
    ch = substr(b, i, 1)
    if (ch != "\\") {
      if (!(ch in ORD)) werr("a body byte outside the byte map")
      DLEN++
      DSUM += ORD[ch]
      continue
    }
    i++
    e = substr(b, i, 1)
    cp = -1
    if (e == "\"") cp = 34
    else if (e == "\\") cp = 92
    else if (e == "/") cp = 47
    else if (e == "b") cp = 8
    else if (e == "f") cp = 12
    else if (e == "n") cp = 10
    else if (e == "r") cp = 13
    else if (e == "t") cp = 9
    else if (e == "u") {
      h = substr(b, i + 1, 4)
      if (length(h) != 4) werr("a truncated \\u escape in an accepted body")
      cp = hexdec(h)
      if (cp < 0) werr("a non-hex \\u escape in an accepted body")
      i += 4
      if (cp >= 55296 && cp <= 56319) {
        if (substr(b, i + 1, 2) != "\\u") werr("an unpaired high surrogate")
        h = substr(b, i + 3, 4)
        lo = hexdec(h)
        if (lo < 0 || lo < 56320 || lo > 57343) werr("a bad low surrogate")
        i += 6
        cp = 65536 + (cp - 55296) * 1024 + (lo - 56320)
      }
    } else werr("an escape the reader does not know: \\" e)
    if (cp != -1) emit_utf8(cp)
  }
}
function is_ws(ch) { return ch == " " || ch == "\t" || ch == "\n" || ch == "\r" }
BEGIN {
  for (i = 1; i < 256; i++) ORD[sprintf("%c", i)] = i
  NUM["0"] = "0000000000000000"
  NUM["-0"] = "8000000000000000"
  NUM["1"] = "3ff0000000000000"
  NUM["2"] = "4000000000000000"
  NUM["3"] = "4008000000000000"
  NUM["42"] = "4045000000000000"
  NUM["-1"] = "bff0000000000000"
  NUM["3.5"] = "400c000000000000"
  NUM["0.5"] = "3fe0000000000000"
  NUM["1e2"] = "4059000000000000"
  NUM["-2.5"] = "c004000000000000"

  s = decode(ENVIRON["DOC_ESC"])
  if (MODE == "validate") exit 0

  n = length(s)
  i = 1
  tokens = 0
  arena = 0
  alen = 0
  small = 0
  while (i <= n) {
    ch = substr(s, i, 1)
    if (is_ws(ch)) { i++; continue }
    if (ch == "{" || ch == "[") { tokens++; small += (ch == "{") ? 1 : 3; i++; continue }
    if (ch == "}" || ch == "]") { tokens++; small += (ch == "}") ? 2 : 4; i++; continue }
    if (ch == "," || ch == ":") { i++; continue }
    if (ch == "\"") {
      start = i
      j = i + 1
      closed = 0
      while (j <= n) {
        cj = substr(s, j, 1)
        if (cj == "\\") { j += 2; continue }
        if (cj == "\"") { closed = 1; break }
        j++
      }
      if (!closed) werr("an accepted document with an unterminated string")
      body = substr(s, start + 1, j - start - 1)
      m = j + 1
      while (m <= n && is_ws(substr(s, m, 1))) m++
      tag = (substr(s, m, 1) == ":") ? 5 : 6
      if (index(body, "\\") == 0) {
        tokens++
        small += tag + length(body)
        printf "ADD %d %d\n", 2147483648, start
      } else {
        decode_body(body)
        tokens++
        small += tag + DLEN
        printf "ADD %d %d\n", 0, alen
        alen += DLEN
        arena += DSUM
      }
      i = j + 1
      continue
    }
    rest = substr(s, i)
    if (substr(rest, 1, 4) == "true") { tokens++; small += 8; i += 4; continue }
    if (substr(rest, 1, 5) == "false") { tokens++; small += 9; i += 5; continue }
    if (substr(rest, 1, 4) == "null") { tokens++; small += 10; i += 4; continue }
    if (match(rest, /^-?(0|[1-9][0-9]*)(\.[0-9]+)?([eE][+-]?[0-9]+)?/) == 1) {
      lex = substr(rest, 1, RLENGTH)
      if (!(lex in NUM)) werr("unpinned number lexeme: " lex)
      h = NUM[lex]
      hi = hexdec(substr(h, 1, 8))
      lo = hexdec(substr(h, 9, 8))
      if (hi < 0 || lo < 0) werr("a malformed number pin for: " lex)
      tokens++
      small += 7
      printf "ADD %d %d\n", hi, lo
      i += RLENGTH
      continue
    }
    werr("an accepted document with a byte the reader does not know: " ch)
  }
  printf "SMALL %.0f\n", small + arena
  printf "TOKENS %.0f\n", tokens
}
AWK
)

# Write one authored document from its escape form.  The reader above validates
# the form (an unknown escape or a malformed `\xHH` is refused); the bytes are
# then emitted by `printf %b`, which writes `\xHH` as one raw byte rather than
# re-encoding a high code point as UTF-8.
write_document() { # escaped bytes, destination
  local esc=$1 dest=$2 msg
  if ! msg=$(DOC_ESC=$esc awk -v MODE=validate "$awk_prog" 2>&1) || [ -n "$msg" ]; then
    printf 'generate: %s\n' "${msg:-the document did not decode}" >&2
    return 1
  fi
  printf '%b' "$esc" >"$dest"
}

# The 8-bit escape form the spec and the reader share, from a file's bytes.
escape_bytes() {
  od -An -v -tu1 "$1" | awk '
    function esc(v) {
      if (v == 92) return "\\\\"
      if (v == 9) return "\\t"
      if (v == 10) return "\\n"
      if (v == 13) return "\\r"
      if (v >= 32 && v < 127) return sprintf("%c", v)
      return sprintf("\\x%02x", v)
    }
    { for (i = 1; i <= NF; i++) printf "%s", esc($i) }
  '
}

# An accepted document's row: `tokens tokens 16hexsum` into ROW, or a failure.
read_reading() {
  local esc=$1 out kind a b hi lo
  out=$(DOC_ESC=$esc awk -v MODE=scan "$awk_prog") || {
    printf 'generate: %s\n' "$out" >&2
    return 1
  }
  hi=0
  lo=0
  ROW_TOKENS=
  while read -r kind a b; do
    case $kind in
      SMALL)
        hi=$((hi + a / 4294967296))
        lo=$((lo + a % 4294967296))
        if [ "$lo" -ge 4294967296 ]; then
          lo=$((lo - 4294967296))
          hi=$((hi + 1))
        fi
        ;;
      ADD)
        hi=$((hi + a))
        lo=$((lo + b))
        if [ "$lo" -ge 4294967296 ]; then
          lo=$((lo - 4294967296))
          hi=$((hi + 1))
        fi
        ;;
      TOKENS) ROW_TOKENS=$a ;;
      *) printf 'generate: unexpected reader row: %s\n' "$kind" >&2; return 1 ;;
    esac
  done <<<"$out"
  if [ -z "$ROW_TOKENS" ]; then
    printf 'generate: the reader produced no token count\n' >&2
    return 1
  fi
  if [ "$hi" -ge 4294967296 ]; then
    printf 'generate: the exact sum reaches 2^64\n' >&2
    return 1
  fi
  ROW_SUM=$(printf '%08x%08x' "$hi" "$lo")
}

manifest=$out/manifest.tsv
: > "$manifest" || exit 1
declare -A seen=()

while IFS=$'\t' read -r name arms cls err origin bytes; do
  case $name in
    '' | '#'*) continue ;;
  esac
  if [ -n "${seen[$name]-}" ]; then fail "the spec names $name twice"; fi
  seen[$name]=1
  case $arms in both | list | pipeline) ;; *) fail "$name: arms must be both, list or pipeline" ;; esac
  case $cls in
    accept | structural | number | literal | string-body | unclosed | no-value | unterminated | utf8-gate) ;;
    *) fail "$name: unknown class $cls" ;;
  esac
  if [ "$cls" = utf8-gate ] && [ "$arms" != pipeline ]; then
    fail "$name: utf8-gate is the pipeline route's own refusal class"
  fi
  if [ "$arms" = pipeline ] && [ "$cls" != utf8-gate ]; then
    fail "$name: the pipeline arm is the UTF-8 gate's document-level refusal"
  fi

  dest=$out/documents/$name
  digest=

  if [ "$origin" != "-" ]; then
    src=$repo/$origin
    [ -f "$src" ] || fail "$name: absent origin $origin"
    cp "$src" "$dest" || fail "$name: cannot copy from $origin"
    origin_digest=$(sha256sum "$src" | cut -d' ' -f1)
    digest=$(sha256sum "$dest" | cut -d' ' -f1)
    [ "$origin_digest" = "$digest" ] ||
      fail "$name: the copy does not match $origin"
    [ "$cls" = accept ] && esc=$(escape_bytes "$dest")
  else
    if [ "$bytes" = "<empty>" ]; then bytes=; fi
    if [ "$cls" = accept ]; then
      esc=$bytes
      write_document "$esc" "$dest" ||
        fail "$name: the document did not decode"
    else
      write_document "$bytes" "$dest" ||
        fail "$name: the document did not decode"
    fi
    digest=$(sha256sum "$dest" | cut -d' ' -f1)
  fi

  if [ "$cls" = accept ]; then
    read_reading "$esc" || fail "$name: the reading could not be derived"
    verdict=accept
    sumhex=$ROW_SUM
    tokens=$ROW_TOKENS
    values=$ROW_TOKENS
    errfield=-
  else
    if [ "$cls" = utf8-gate ]; then
      nbytes=$(wc -c < "$dest")
      case $err in
        -) ;;
        '' | *[!0-9]*) fail "$name: a refusal offset must be numeric or -" ;;
        *) [ "$err" = "$nbytes" ] ||
             fail "$name: the UTF-8 gate refuses at the document's end" ;;
      esac
      err=$nbytes
    else
      case $err in
        '' | *[!0-9]*) fail "$name: a refusal needs a numeric offset" ;;
      esac
    fi
    verdict=refuse
    sumhex=-
    tokens=-
    values=-
    errfield=$err
  fi

  printf 'documents/%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n' \
    "$name" "$arms" "$cls" "$verdict" "$errfield" "$tokens" "$values" \
    "$sumhex" "$digest" "$origin" >> "$manifest"
done <"$spec"

# The seeded family: six whitespace documents whose gap lengths come from the
# fixed seed.  Each is `k-1` spaces, `[`, `a` spaces, `1`, `b` spaces, `]`, so
# the documents differ by their leading gap and the reading is the same shape as
# `acc-number-array`'s; only the seed decides the gaps, never the clock.
state=$seed
for k in 1 2 3 4 5 6; do
  state=$(( (state * 48271) % 2147483647 ))
  a=$((state % 5))
  state=$(( (state * 48271) % 2147483647 ))
  b=$((state % 5))
  name=$(printf 'gen-ws-%02d' "$k")
  doc=''
  p=1
  while [ "$p" -lt "$k" ]; do doc=$doc' '; p=$((p + 1)); done
  doc=$doc'['
  p=1
  while [ "$p" -le "$a" ]; do doc=$doc' '; p=$((p + 1)); done
  doc=$doc'1'
  p=1
  while [ "$p" -le "$b" ]; do doc=$doc' '; p=$((p + 1)); done
  doc=$doc']'
  dest=$out/documents/$name
  printf '%s' "$doc" >"$dest" || fail "$name: cannot write"
  read_reading "$doc" || fail "$name: the reading could not be derived"
  digest=$(sha256sum "$dest" | cut -d' ' -f1)
  printf 'documents/%s\tboth\taccept\taccept\t-\t%s\t%s\t%s\t%s\t-\n' \
    "$name" "$ROW_TOKENS" "$ROW_TOKENS" "$ROW_SUM" "$digest" >> "$manifest"
done

exit 0
