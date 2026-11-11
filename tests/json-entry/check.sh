#!/usr/bin/env bash
# Route check for the entry positions: the `ent` word's stream, and the two
# entry kernels as position emitters.
#
#   nix develop -c bash tests/json-entry/check.sh
#
# Two actors must agree, row for row, on the same rows:
#
#   * the Lean body — `entryPos8Function` / `entryB8Function`, the ASTs
#     `LeanLLVM/Refinement/JsonEntryIR.lean` pins to
#     `probes/install/ir/json-entry.candidate.ll` — run by
#     `leanllvm-json-entry` under the repository's semantics;
#   * the installed object — `kernel/json/entry.c` compiled with the measured
#     compiler line and called through `probes/json/entry_driver.c`.
#
# A row is one `(mask stream, blk0, nblk, k)` call, one line:
#
#   <source>\t<label>\t<kernel>\t<count>\t<words>\t<multi>\t<sentinel>
#
# `source` is the corpus path as given, or `arm:<arm>`; `label` names the row
# (below); `kernel` is `p` for POS8 and `b` for B8; `count` is the returned
# cursor `k'`; `words` is the first `k'` `i32` words, `0x` and eight lowercase
# hex digits each, comma-separated, or `-` when `k'` is 0; `multi` is 1 when a
# block of the stream has more than eight set lanes; and `sentinel` is the word
# at lane `k'+8`, the first lane neither kernel writes.  The output buffer is
# pre-filled with `0xA5`, so a store the body does not make — and the word at
# `k'+8` — read back as `0xa5a5a5a5`.  A row whose cursor starts at `k` therefore
# begins with `k` sentinel words.
#
# The region `[k', k'+8)` is excluded from the comparison by construction: POS8's
# eight group stores run unconditionally, so its last one writes eight lanes at
# the final cursor and reaches `k'+7`; B8 writes eight fixed slots per block and
# reaches `k'+6`.  Those lanes hold table-row padding and block bases rather than
# positions.  The sentinel at `k'+8` is what proves the body stopped inside that
# bound, and it is asserted on every row.
#
# PROVENANCE — the mask streams under tests/json-entry/corpus/.
#
# Each corpus file is one mask stream derived from a committed JSON document's
# block bytes, not written by hand.  The documents are the stage-1 route's own
# corpus, `tests/json-s1-masks/corpus/*.json`; each is partitioned into
# consecutive 64-byte blocks (the unit `S1F_DEFINE_KERNEL` advances `blk0` by),
# and the mask word's lane `i` is set iff the block's byte `i` is one of the
# eight structural bytes `IsStructuralB` reads — `"` 0x22, `\` 0x5c, `:` 0x3a,
# `,` 0x2c, `{` 0x7b, `}` 0x7d, `[` 0x5b, `]` 0x5d.  That is the `S1F_GRAIN=1`
# structural granularity the measured header documents, so the stream is a real
# entry-shaped input rather than arbitrary data.  Lanes past the document's end
# are clear.  `blk0` and `k` are staging parameters: one stream is staged at a
# nonzero base and one at a nonzero cursor, so neither is assumed zero.  A
# corpus file is
#
#   {"source": "<the document>", "blk0": <d>, "k": <d>, "masks": ["0x<16 hex>", ...]}
#
# one mask per line in the array, and its rows' label is
# `blk0<blk0>/k<k>/masks<n>`, so the file's staging is visible in the row
# identity.
#
# The generated arms, whose labels also name their data so the route can derive
# what it asserts rather than trust the driver:
#
#   arm:lane   label `lane<nn>`, nn = 00..63 — the mask `1 << nn`; 64 streams.
#   arm:byte   label `val<hh>`, hh = 00..ff — group 0's byte set to hh; 256
#              streams, so every table row is read.
#   arm:random label `idx<n>/mask<16 hex>` — 65536 masks from a fixed seed.
#   arm:empty  label `empty` — the zero mask.
#   arm:full   label `full` — all 64 lanes.
#   arm:nblk   label `masks1025` — the long-loop arm: the corpus streams' masks
#              concatenated in file order and repeated to 1025, so the kernel's
#              own loop runs long in one call.  `S1F_CHUNK` is the caller's chunk
#              size, not this unit's.
#
# Every arm starts at `blk0 = 0` and cursor `k = 0`, so an arm row's count and
# words are the mask's own set lanes from base 0.  A row is one kernel's call,
# so the arms contribute 64 + 256 + 65536 + 2 + 1 = 65859 streams and 131718
# rows, and each corpus stream contributes 2.
#
# What this scenario asserts, in order:
#
#   0. The fixture regenerates from the kernel source at the pinned flags and is
#      byte-identical to the committed copy; a difference is a setup failure,
#      not an assertion result.
#   1. Every row's count and first `k'` words are the positions the stream's
#      masks define — computed here from the committed corpus bytes and from the
#      label's own mask — so the assertion does not depend on the two actors
#      agreeing on the same mistake; `multi` is derived the same way and
#      asserted; every row's sentinel at `k'+8` is `0xa5a5a5a5`.
#   2. The object's rows equal the Lean body's rows line for line, in order, and
#      the row count is exactly `2 * (corpus files + 65859)`.
#   3. The table detector bites: a defect object built from a copy of the entry
#      source with `xl_pos8_init`'s row for mask `0x2C` given first entry `1`
#      instead of `2` disagrees with the Lean body on exactly the POS8 rows
#      whose stream has a byte equal to `0x2c`, and on no other row.
#   4. The B8 detector bites: a defect object with `s1f_ke_b8`'s tail loop cut
#      disagrees on exactly the B8 rows whose stream has a block with more than
#      eight set lanes, and on no other row.  The first differing row is named,
#      and two runs of each defect name the same row.
#   5. A tampered expectation is a mismatch naming its row: the runner, fed one
#      hand-changed word, exits nonzero, says `mismatch:` on stderr, names the
#      tampered row, and prints the same rows as the control.
#
# The runner is the artifact `lake build leanllvm-json-entry` produces; this
# script does not invoke `lake`.  `clang` compiles committed sources into a
# private temporary directory; `CC` is not consulted because the dev shell's
# `CC` is gcc.  The corpus, the fixture, the capture script and the driver
# source are only read — the fixture is replaced and restored around the
# regeneration comparison, and the script's exit trap puts the committed bytes
# back whatever happens.
#
# Exit status: 0 when the assertions hold, 1 when one fails, 3 when the route is
# not usable (an absent corpus, fixture, capture script, driver or kernel
# source, an absent runner binary, no `clang` on PATH, a capture that does not
# reproduce the fixture, or a mutation that does not apply), so a setup fault is
# never read as an assertion result.
set -uo pipefail

repo=$(cd "$(dirname "$0")/../.." && pwd)
corpus=$repo/tests/json-entry/corpus
fixture=$repo/probes/install/ir/json-entry.candidate.ll
capture=$repo/probes/install/ir/capture-entry.sh
driver_src=$repo/probes/json/entry_driver.c
kernel_src=$repo/kernel/json/entry.c
kernel_hdr=$repo/kernel/json/entry.h
runner=$repo/.lake/build/bin/leanllvm-json-entry
build_hint='nix develop -c lake build leanllvm-json-entry'
cc=clang

# The measured compiler line (`build49.sh:17`).
cflags=(-O3 -march=x86-64-v3 -mpclmul -std=gnu11 -falign-loops=64 -falign-functions=64)

for path in "$corpus" "$fixture" "$capture" "$driver_src" "$kernel_src" "$kernel_hdr"; do
  [ -e "$path" ] || { printf 'SETUP: absent: %s\n' "$path" >&2; exit 3; }
done

if [ ! -x "$runner" ]; then
  printf 'SETUP: absent runner: %s\n' "$runner" >&2
  printf 'SETUP: build it with: %s\n' "$build_hint" >&2
  exit 3
fi

if ! command -v "$cc" >/dev/null 2>&1; then
  printf 'SETUP: no %s on PATH, and the kernel is C\n' "$cc" >&2
  exit 3
fi

work=$(mktemp -d) || { echo "SETUP: cannot create a temporary directory" >&2; exit 3; }
restore_fixture() {
  if [ -f "$work/fixture.committed" ]; then
    cp "$work/fixture.committed" "$fixture"
  fi
}
trap 'restore_fixture; rm -rf "$work"' EXIT

cd "$repo" || exit 3

mapfile -t corpus_files < <(find "$corpus" -mindepth 1 -maxdepth 1 -type f | LC_ALL=C sort)
if [ "${#corpus_files[@]}" -eq 0 ]; then
  printf 'SETUP: no corpus files under %s\n' "$corpus" >&2
  exit 3
fi

corpus_args=()
corpus_rels=()
for f in "${corpus_files[@]}"; do
  rel=${f#"$repo"/}
  corpus_rels+=("$rel")
  corpus_args+=(--corpus "$rel")
done

# --- The object, compiled once with the measured line. ---

if ! "$cc" "${cflags[@]}" -I "$repo/kernel/json" -c "$kernel_src" \
    -o "$work/kernel.o" 2>"$work/cc.err"; then
  printf 'FAIL: the entry unit did not compile with the measured flags\n' >&2
  cat "$work/cc.err" >&2
  exit 1
fi

if ! "$cc" -O2 -o "$work/driver" "$driver_src" "$work/kernel.o" 2>"$work/link.err"; then
  printf 'FAIL: the driver did not link against the entry object\n' >&2
  cat "$work/link.err" >&2
  exit 1
fi

# --- 0. The fixture is the kernel source's emission at the same flags. ---
#
# The capture writes the fixture in place, so the committed bytes are copied
# aside, the file is removed, and the exit trap restores the copy whatever the
# outcome.  A capture that writes nothing, or writes different bytes, is a setup
# fault: the theorem's subject would not be the code the object arm ran.

cp "$fixture" "$work/fixture.committed"
rm -f "$fixture"

if ! bash "$capture" >"$work/capture.out" 2>"$work/capture.err"; then
  printf 'SETUP: %s exited nonzero; the fixture did not regenerate\n' "$capture" >&2
  cat "$work/capture.err" >&2
  exit 3
fi

if [ ! -f "$fixture" ]; then
  printf 'SETUP: %s wrote no fixture at %s\n' "$capture" "$fixture" >&2
  exit 3
fi

if ! cmp -s "$work/fixture.committed" "$fixture"; then
  printf 'SETUP: the committed fixture is not the kernel source emission at the pinned flags\n' >&2
  diff -u "$work/fixture.committed" "$fixture" | awk 'NR <= 40' >&2
  exit 3
fi

# --- The corpus map: what each committed stream's rows must hold. ---
#
# For each corpus file: its `blk0`, its cursor, its mask count, the two derived
# columns the detectors predicate on, and the row's expected count and words.
# Everything is computed from the committed bytes; none of it is retyped.

hexlib=$(cat <<'AWKLIB'
function popcount(h,   i, c, t, s) {
  t = "0112122312232334"
  s = 0
  for (i = 1; i <= length(h); i++) {
    c = index("0123456789abcdef", substr(h, i, 1)) - 1
    s += substr(t, c + 1, 1)
  }
  return s
}
function hexdig(d) { return substr("0123456789abcdef", d + 1, 1) }
function nibble(h, i) { return index("0123456789abcdef", substr(h, 16 - i, 1)) - 1 }
function bit(h, i) { return int(nibble(h, int(i / 4)) / (2 ^ (i % 4))) % 2 }
function has2c(h,   g, b) {
  for (g = 0; g < 8; g++) {
    b = substr(h, 15 - 2 * g, 2)
    if (b == "2c") return 1
  }
  return 0
}
function lanes(h, base,   i, out) {
  out = ""
  for (i = 0; i < 64; i++)
    if (bit(h, i)) out = out (out == "" ? "" : ",") sprintf("0x%08x", base + i)
  return out
}
AWKLIB
)

: > "$work/corpus.map"
for rel in "${corpus_rels[@]}"; do
  blk0=$(grep -o '"blk0"[^0-9]*[0-9]\+' "$rel" | grep -o '[0-9]\+$')
  kcur=$(grep -o '"k"[^0-9]*[0-9]\+' "$rel" | grep -o '[0-9]\+$')
  nmasks=$(grep -o '0x[0-9a-f]\{16\}' "$rel" | wc -l)
  if [ -z "$blk0" ] || [ -z "$kcur" ] || [ "$nmasks" -eq 0 ]; then
    printf 'SETUP: %s does not carry blk0, k and masks\n' "$rel" >&2
    exit 3
  fi
  maprow=$(grep -o '0x[0-9a-f]\{16\}' "$rel" |
    awk -v blk0="$blk0" -v k="$kcur" "$hexlib"'
      {
        h = substr($0, 3)
        words = words (words == "" ? "" : ",") lanes(h, 64 * (ind + blk0))
        count += popcount(h)
        if (has2c(h)) two = 1
        if (popcount(h) > 8) multi = 1
        ind++
      }
      END {
        prefix = ""
        for (i = 0; i < k; i++) prefix = prefix "0xa5a5a5a5,"
        total = count + k
        printf "%d\t%d\t%d\t%s\n", two + 0, multi + 0, total,
          (total == 0 ? "-" : prefix words)
      }')
  printf '%s\t%s\t%s\t%s\t%s\n' "$rel" "$blk0" "$kcur" "$nmasks" "$maprow" \
    >> "$work/corpus.map"
done
# Columns: rel, blk0, k, nmasks, has2c, multi, count, words

# The `nblk` arm is the corpus masks concatenated in file order and repeated to
# 1025; its derived columns are computed from the same committed bytes.
nblk_row=$(for rel in "${corpus_rels[@]}"; do grep -o '0x[0-9a-f]\{16\}' "$rel"; done |
  awk "$hexlib"'
    { h[NR - 1] = substr($0, 3); n = NR }
    END {
      count = 0
      for (i = 0; i < 1025; i++) {
        x = h[i % n]
        count += popcount(x)
        if (has2c(x)) two = 1
        if (popcount(x) > 8) multi = 1
      }
      printf "%d\t%d\t%d\n", two + 0, multi + 0, count
    }')
nblk_2c=$(printf '%s\n' "$nblk_row" | cut -f1)
nblk_multi=$(printf '%s\n' "$nblk_row" | cut -f2)
nblk_count=$(printf '%s\n' "$nblk_row" | cut -f3)

if [ -z "$nblk_count" ]; then
  printf 'SETUP: the nblk arm has no derived count\n' >&2
  exit 3
fi

# --- 1 and 2. The Lean body's rows, then the object's. ---

if ! "$runner" "${corpus_args[@]}" --arms >"$work/lean.out" 2>"$work/lean.err"; then
  printf 'FAIL: the Lean body did not emit every row\n' >&2
  cat "$work/lean.err" >&2
  exit 1
fi

rows=$(wc -l < "$work/lean.out")

lane_streams=64
byte_streams=256
random_streams=65536
shape_streams=2        # the empty mask and the full mask
nblk_streams=1         # the long-loop arm: one call, more blocks than a caller chunk
arm_streams=$((lane_streams + byte_streams + random_streams + shape_streams + nblk_streams))
computed=$((2 * (${#corpus_files[@]} + arm_streams)))

if [ "$rows" -ne "$computed" ]; then
  printf 'FAIL: %s row(s) printed, %s computed: 2 * (%s corpus + %s arm streams)\n' \
    "$rows" "$computed" "${#corpus_files[@]}" "$arm_streams" >&2
  exit 1
fi

# Every row's identity is one (source, label, kernel) and appears once; its
# count and words are the positions the stream's masks define.  The expectations
# come from the corpus map and from each arm's own label, so a wrong label, a
# wrong count or a wrong word fails here whatever the other actor says.  The
# same pass emits the two detection predicates, one line per row.
if ! awk -F '\t' -v nblk_2c="$nblk_2c" -v nblk_multi="$nblk_multi" \
    -v nblk_count="$nblk_count" "$hexlib"'
  NR == FNR {
    n = FNR
    bypath[$1] = FNR
    blk0[FNR] = $2; kc[FNR] = $3; nm[FNR] = $4
    two[FNR] = $5; mul[FNR] = $6; cnt[FNR] = $7; wds[FNR] = $8
    next
  }
  {
    id = $1 "\t" $2 "\t" $3
    if (id in seen) {
      printf "FAIL: duplicate row identity: %s\n", id > "/dev/stderr"; bad = 1
    }
    seen[id] = 1
    if ($3 != "p" && $3 != "b") {
      printf "FAIL: kernel %s on %s\n", $3, id > "/dev/stderr"; bad = 1
    }
    if ($7 != "0xa5a5a5a5") {
      printf "FAIL: sentinel %s at k+8 on %s\n", $7, id > "/dev/stderr"; bad = 1
    }

    if ($1 in bypath) {
      i = bypath[$1]
      want = "blk0" blk0[i] "/k" kc[i] "/masks" nm[i]
      if ($2 != want) {
        printf "FAIL: label %s, expected %s\n", $2, want > "/dev/stderr"; bad = 1
      }
      ecount = cnt[i]; ewords = wds[i]; emulti = mul[i]; e2c = (two[i] == 1)
    } else if ($1 == "arm:lane") {
      nn = substr($2, 5) + 0
      h = ""
      for (j = 15; j >= 0; j--) h = h hexdig((j == int(nn / 4)) ? 2 ^ (nn % 4) : 0)
      ecount = 1; ewords = lanes(h, 0); emulti = 0; e2c = 0
    } else if ($1 == "arm:byte") {
      hh = substr($2, 4)
      h = "00000000000000" hh
      ecount = popcount(h); ewords = (ecount == 0 ? "-" : lanes(h, 0)); emulti = 0; e2c = (hh == "2c")
    } else if ($1 == "arm:random") {
      h = $2
      sub(/^idx[0-9]+\/mask/, "", h)
      if (length(h) != 16 || h !~ /^[0-9a-f]+$/) {
        printf "FAIL: random row label carries no mask: %s\n", $2 > "/dev/stderr"
        bad = 1
        next
      }
      ecount = popcount(h); ewords = (ecount == 0 ? "-" : lanes(h, 0)); emulti = (ecount > 8)
      e2c = (has2c(h) == 1)
    } else if ($1 == "arm:empty") {
      ecount = 0; ewords = "-"; emulti = 0; e2c = 0
    } else if ($1 == "arm:full") {
      ecount = 64; ewords = lanes("ffffffffffffffff", 0); emulti = 1; e2c = 0
    } else if ($1 == "arm:nblk") {
      ecount = nblk_count; ewords = "-"; emulti = nblk_multi; e2c = (nblk_2c == 1)
    } else {
      printf "FAIL: row from an unknown source: %s\n", $1 > "/dev/stderr"
      bad = 1
      next
    }

    if ($4 != ecount) {
      printf "FAIL: count %s, expected %s, on %s\n", $4, ecount, id > "/dev/stderr"
      bad = 1
    }
    if ($1 != "arm:nblk" && $5 != ewords) {
      printf "FAIL: words %s, expected %s, on %s\n", $5, ewords, id > "/dev/stderr"
      bad = 1
    }
    if ($6 != emulti) {
      printf "FAIL: multi %s, expected %s, on %s\n", $6, emulti, id > "/dev/stderr"
      bad = 1
    }
    print (($3 == "p" && e2c) ? 1 : 0) "\t" (($3 == "b" && emulti == 1) ? 1 : 0)
  }
  END { exit bad }
' "$work/corpus.map" "$work/lean.out" >"$work/annot.tsv" 2>"$work/annot.err"; then
  cat "$work/annot.err" >&2
  exit 1
fi

if [ "$(wc -l < "$work/annot.tsv")" -ne "$rows" ]; then
  printf 'FAIL: the row check annotated %s row(s), the stream has %s\n' \
    "$(wc -l < "$work/annot.tsv")" "$rows" >&2
  exit 1
fi

if ! "$work/driver" "${corpus_args[@]}" --arms >"$work/object.out" 2>"$work/object.err"; then
  printf 'FAIL: the object did not emit every row\n' >&2
  cat "$work/object.err" >&2
  exit 1
fi

if ! cmp -s "$work/lean.out" "$work/object.out"; then
  printf 'FAIL: the object and the Lean body disagree\n' >&2
  diff -u "$work/lean.out" "$work/object.out" | awk 'NR <= 40' >&2
  exit 1
fi

kernel_sha=$(sha256sum "$work/kernel.o" | cut -d' ' -f1)

# --- 3 and 4. The two defect objects. ---

# The table defect: `xl_pos8_init`'s row for mask `0x2C` — whose set lanes are
# 2, 3 and 5 — is given first entry `1` where the measured rule gives `2`.
# `0x2C` is a byte value, so `m == 0x2C` names the row and `o == 0` its first
# entry.  The substitution is textual because the entry source owns the fill
# rule's spelling, and the number of substitutions that land is counted, so a
# source that lost the measured text fails here instead of passing silently.
if ! awk '
  BEGIN {
    pat = "if ((m >> t) & 1) xl_pos8[m][o++] = t;"
    repl = "if ((m >> t) & 1) { unsigned v = (m == 0x2C && o == 0) ? 1 : t; xl_pos8[m][o++] = v; }"
  }
  {
    line = $0
    p = index(line, pat)
    if (p > 0) {
      hits++
      line = substr(line, 1, p - 1) repl substr(line, p + length(pat))
    }
    print line
  }
  END {
    if (hits != 1) {
      printf "SETUP: the table mutation applied to %d site(s), not 1\n", hits > "/dev/stderr"
      exit 3
    }
  }
' "$kernel_src" > "$work/entry.table.c"; then
  printf 'SETUP: the table mutation did not apply\n' >&2
  exit 3
fi

if cmp -s "$kernel_src" "$work/entry.table.c"; then
  printf 'SETUP: the table mutation changed nothing\n' >&2
  exit 3
fi

# The B8 defect: the tail loop — the epilogue that emits the positions past the
# eight fixed slots — is cut, so a block with more than eight set lanes returns
# eight where the measured body returns its population count.  The loop is
# located by its own measured text inside `s1f_ke_b8`, and the number of cuts
# that land is counted.
if ! awk '
  BEGIN {
    pat = "while (c) { *o++ = base + (uint32_t)__builtin_ctzll(c); k++; c &= c - 1; }"
    repl = "/* the tail loop is cut: the positions past the eight slots are not written */"
  }
  /s1f_ke_b8\(uint64_t m/ { inb8 = 1 }
  {
    line = $0
    if (inb8 && index(line, pat) > 0) {
      p = index(line, pat)
      line = substr(line, 1, p - 1) repl substr(line, p + length(pat))
      hits++
    }
    print line
  }
  END {
    if (hits != 1) {
      printf "SETUP: the tail-loop cut applied to %d site(s), not 1\n", hits > "/dev/stderr"
      exit 3
    }
  }
' "$kernel_src" > "$work/entry.b8.c"; then
  printf 'SETUP: the tail-loop cut did not apply\n' >&2
  exit 3
fi

if cmp -s "$kernel_src" "$work/entry.b8.c"; then
  printf 'SETUP: the tail-loop cut changed nothing\n' >&2
  exit 3
fi

for which in table b8; do
  if ! "$cc" "${cflags[@]}" -I "$repo/kernel/json" -c "$work/entry.$which.c" \
      -o "$work/kernel.$which.o" 2>"$work/cc.$which.err"; then
    printf 'FAIL: the %s defect object did not compile\n' "$which" >&2
    cat "$work/cc.$which.err" >&2
    exit 1
  fi
  if ! "$cc" -O2 -o "$work/driver_$which" "$driver_src" "$work/kernel.$which.o" \
      2>"$work/link.$which.err"; then
    printf 'FAIL: the %s defect driver did not link\n' "$which" >&2
    cat "$work/link.$which.err" >&2
    exit 1
  fi
done

# Each defect's affected set is a predicate over the row's own label: POS8 rows
# whose stream has a byte equal to `0x2c` for the table defect, B8 rows whose
# stream has a block with more than eight set lanes for the cut.  Both are
# checked in both directions against the annotations the row check derived.
for which in table b8; do
  if ! "$work/driver_$which" "${corpus_args[@]}" --arms >"$work/defect.$which.out" \
      2>"$work/defect.$which.err"; then
    printf 'FAIL: the %s defect object did not emit every row\n' "$which" >&2
    cat "$work/defect.$which.err" >&2
    exit 1
  fi

  if ! "$work/driver_$which" "${corpus_args[@]}" --arms >"$work/defect.$which.2.out" \
      2>/dev/null; then
    printf 'FAIL: the second run of the %s defect failed\n' "$which" >&2
    exit 1
  fi

  defect_rows=$(wc -l < "$work/defect.$which.out")
  if [ "$defect_rows" -ne "$rows" ]; then
    printf 'FAIL: the %s defect printed %s row(s), the control %s\n' \
      "$which" "$defect_rows" "$rows" >&2
    exit 1
  fi

  if ! cmp -s "$work/defect.$which.out" "$work/defect.$which.2.out"; then
    printf 'FAIL: the %s defect is not deterministic across two runs\n' "$which" >&2
    exit 1
  fi

  if ! awk -F '\t' 'NR == FNR { c[FNR] = $0; next } { print ($0 != c[FNR]) ? 1 : 0 }' \
      "$work/lean.out" "$work/defect.$which.out" > "$work/moved.$which"; then
    printf 'FAIL: the %s defect comparison did not run\n' "$which" >&2
    exit 1
  fi

  if [ "$which" = table ]; then column=1; else column=2; fi

  if ! awk -F '\t' -v col="$column" -v which="$which" '
    NR == FNR { want[FNR] = $col; next }
    {
      moved = ($1 == 1)
      if (want[FNR] == 1 && !moved) {
        printf "FAIL: the %s defect did not move row %d, which its predicate names\n", which, FNR > "/dev/stderr"
        bad = 1
      }
      if (want[FNR] == 0 && moved) {
        printf "FAIL: the %s defect moved row %d, which its predicate does not name\n", which, FNR > "/dev/stderr"
        bad = 1
      }
      if (want[FNR] == 1) named++
      if (moved) movedcount++
    }
    END {
      if (named == 0) {
        printf "FAIL: the %s defect has nothing to bite: no row is in its set\n", which > "/dev/stderr"
        bad = 1
      }
      if (movedcount != named) {
        printf "FAIL: the %s defect moved %d row(s), %d named\n", which, movedcount + 0, named + 0 > "/dev/stderr"
        bad = 1
      }
      if (!bad) print movedcount + 0
      exit bad
    }
  ' "$work/annot.tsv" "$work/moved.$which" > "$work/moved.$which.count" 2>"$work/moved.$which.err"; then
    cat "$work/moved.$which.err" >&2
    exit 1
  fi

  first_row=$(awk 'NR == FNR { c[FNR] = $0; next } $0 != c[FNR] { print FNR; exit }' \
    "$work/lean.out" "$work/defect.$which.out")
  if [ -z "$first_row" ]; then
    printf 'FAIL: the %s defect differs but no differing row was found\n' "$which" >&2
    exit 1
  fi
  first_line=$(awk -v n="$first_row" 'NR == n' "$work/lean.out")
  count=$(cat "$work/moved.$which.count")

  if [ "$which" = table ]; then
    moved_table=$count
    first_table_line=$first_line
  else
    moved_b8=$count
    first_b8_line=$first_line
  fi
done

# --- 5. A tampered expectation is a mismatch naming its row. ---

# The first row that emitted a word, so the tamper changes a position rather
# than an empty field.
tamper_id=$(awk -F '\t' '$5 != "-" { print $1 "\t" $2; exit }' "$work/lean.out")
if [ -z "$tamper_id" ]; then
  printf 'SETUP: no row emitted a word, so no position can be tampered\n' >&2
  exit 3
fi

awk -F '\t' -v OFS='\t' '
  !done && $5 != "-" {
    sub(/^0x[0-9a-f]+/, "0xdeadbeef", $5)
    done = 1
  }
  { print }
' "$work/lean.out" > "$work/tampered.tsv"

if cmp -s "$work/lean.out" "$work/tampered.tsv"; then
  printf 'SETUP: the tamper changed nothing\n' >&2
  exit 3
fi

"$runner" "${corpus_args[@]}" --arms --expect "$work/tampered.tsv" \
  >"$work/tampered.out" 2>"$work/tampered.err"
status=$?

if [ "$status" -eq 0 ]; then
  printf 'FAIL: a tampered expectation exited 0\n' >&2
  exit 1
fi

if ! grep -q '^mismatch:' "$work/tampered.err"; then
  printf 'FAIL: the tampered run did not report a mismatch\n' >&2
  cat "$work/tampered.err" >&2
  exit 1
fi

if ! grep -qF "mismatch: $tamper_id" "$work/tampered.err"; then
  printf 'FAIL: the mismatch does not name the tampered row (%s)\n' "$tamper_id" >&2
  cat "$work/tampered.err" >&2
  exit 1
fi

if ! cmp -s "$work/lean.out" "$work/tampered.out"; then
  printf 'FAIL: the tampered run printed different rows\n' >&2
  exit 1
fi

# --- Report ---

printf 'ok: the fixture is the kernel source emission at the pinned flags\n'
printf 'ok: %s row(s) from %s corpus stream(s) and %s arm streams, each carrying the positions its masks define\n' \
  "$rows" "${#corpus_files[@]}" "$arm_streams"
printf 'ok: the sentinel at k+8 is 0xa5a5a5a5 on every row\n'
printf 'ok: the object (kernel sha256 %s) agrees with the Lean body on %s row(s)\n' \
  "$kernel_sha" "$rows"
printf 'ok: the table detector bites: %s row(s) moved, exactly the POS8 rows whose stream has a 0x2c byte; first is %s\n' \
  "$moved_table" "$first_table_line"
printf 'ok: the B8 detector bites: %s row(s) moved, exactly the B8 rows with more than eight set lanes; first is %s\n' \
  "$moved_b8" "$first_b8_line"
printf 'ok: a tampered expectation is a mismatch naming its row\n'
