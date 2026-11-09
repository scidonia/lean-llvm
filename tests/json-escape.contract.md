# The stage-1 escape-position list

The stage-1 builder produces two position streams: the structural entry stream
and, on the documents the density probe does not call plain, the escape list
the unescaper's windows are driven from.  The entry stream has its route in
`tests/json-entry/check.sh`; this file is the escape list's, and its subject is
the list the measured builder actually leaves, not a body pinned from a
fixture.

Two derivations over one committed corpus are compared:

* the measured actor — `probes/json/escape_measured.c`, compiled from
  `kernel/json/measured/s1fuse.h` at the measured compiler line
  (`kernel/json/measured/PROVENANCE.md`, `build49.sh:17`) and the measured `-D`
  set (`-DS1F_XS=5 … -DS1F_XS_DYN=1`), which returns the stream the builder
  left in `s1f_esc_list` and its count;
* the reference — `probes/json/escape_driver.c`'s byte scan, written from the
  escape rule rather than from the emitter's text.

The driver also re-derives the document-level gate from the same bytes, and
the route checks it against the class the actor exhibits (whether it left a
list at all), so the gate's rule is a relation over two observations rather
than a definition the suppressed rows could satisfy by naming.

A row is

```
<source>\t<label>\t<n>\t<count>\t<positions or ->
```

with the positions space-separated in document order, so the line is the
ordered sequence and not the presence of numbers in a transcript.  The corpus
`tests/json-escape/corpus.tsv` is a three-column TSV with no header — `label`,
lowercase hex (`-` for the empty document), `n` — and its line count is its row
count.

The route is

```
nix develop -c bash tests/json-escape/check.sh
```

### ES1 — the measured escape list is the positions the escape rule names

- **Actor:** the measured stage-1 escape-list emitter.  The list is built in
  `s1f_build2`'s classify loop from the block's control, backslash and
  in-string masks through `xl_lanes` and appended by `xl_emit`
  (`kernel/json/measured/xlist.h`); at `S1F_XS=5` that is the per-block-gated
  eight-entry batch.  `probes/json/escape_measured.c` compiles that builder at
  the measured configuration and exposes one entry point.
- **Boundary:** the probe translation unit's own C entry point,
  `escape_measured_list(const uint8_t *doc, uint64_t n, uint64_t *nx)`.  A
  document's bytes go in; the stream the measured builder left and its count
  come out, including the NULL and zero the document gate leaves on a document
  it does not build a list for.  The caller stages 64 readable bytes per
  block, which is the builder's own read contract.  No Lean code is called and
  no helper of the unit is stubbed.
- **Given:** the twenty-one committed rows of `tests/json-escape/corpus.tsv`:
  short documents with and without a position, long documents that are dense
  in nothing, one that carries a raw control byte inside a string, one whose
  only backslash sits in an upper half-block, a sparse document with one
  escape, escape-dense documents of one and two blocks, the six backslash-run
  cases whose run crosses the 64-byte boundary at every phase
  (`carry:run1@63` … `carry:run6@60`), a 64-byte block with twenty positions,
  a backslash outside any string, an escaped quote, an escaped control byte,
  and an escape at the last byte of a 65-byte document.
- **When:** the probe's entry point is called once per row, on a zero-padded
  copy of the document, and the reference is evaluated over the same bytes.
- **Then:** three clauses hold over the same rows:
  1. **(a) the built arm.**  On every row the re-derived density rule calls
     non-plain, the emitted stream's `count` entries, in order, equal the
     reference's tuple.  The comparison is over the two transcripts, so a
     reordering, a missing position, an extra position or a changed count
     fails.
  2. **(b) the suppressed arm.**  On every row that rule calls plain, the
     emitted count is zero and no position is claimed.  This clause does not
     assert that a plain document carries no escape: seven of the committed
     rows carry an escape the reference names and the gate suppresses, and
     that is a fact about the measured code rather than something the
     reference may be weakened to hide.
  3. **(c) the gate's rule is a checked relation.**  For every row, the class
     the driver re-derives from the document's bytes equals the class the
     actor exhibits — a list left, or none.  The re-derivation is written in
     the driver from the rule instead of from the builder: a document with no
     whole 64-byte block is plain (`kernel/json/measured/dens.h:222`);
     otherwise blocks are sampled at the stride `nb/64`
     (`dens.h:223-224`) and only the backslashes among each sampled block's
     low 32 bytes are counted (`dens.h:227-234`); the document is plain when
     `hits*64 < samples*DENS_PLAIN_NUM` (`dens.h:261-262`), with the
     threshold read from the header and passed to the driver at compile time.
     The actor's exhibited class is a separate observation — whether the
     returned list pointer is non-NULL — so the relation is between the bytes
     and what the measure did, not a restatement of one variable.  The
     per-row table (label, re-derived class, exhibited class) is printed,
     because this is a row-level relation; without (c), (b) would hold by the
     definition of "suppressed".
  The reference is a scalar walk: an unescaped quote opens and closes a
  string; inside a string every control byte is a position; a backslash run
  contributes its even offsets (the first of `\\`, `\\\`, …), and an
  odd-length run escapes the byte after it.
- **Expected failure:** **green against the measured actor, and therefore
  vacuous as pre-fix evidence.**  It is not a red and must not be manufactured
  into one.  All three clauses hold today.  The ten rows the rule calls
  non-plain — `sparse:one-escape`, `heavy:forty-escapes`, the six
  `carry:run*` rows, `many:one-block` and `heavy:across-blocks` — emit exactly
  the reference tuple, including the runs that cross the block boundary at
  every phase.  The eleven rows it calls plain emit count `0` and no
  positions, and the re-derived class matches the class the actor exhibits on
  every row.  The scenario's pre-fix evidence is a staged cut taken at a later
  slice, when an extracted object exists to cut; it is recorded with that
  slice, not here.  The earlier reading of this route — seven rows where the
  reference names a position and the actor emits none — is a finding about the
  measured gate, not a failure of a clause: `dens_probe` counts backslashes
  only in the low 32 bytes of sampled blocks and calls a document with no
  whole block plain, so a document under 64 bytes, a document whose only
  escape sits in an upper half-block, and a document whose only position is a
  raw control byte are suppressed.  Clause (b) covers exactly those rows, and
  clause (c) checks the rule that produces them.
- **Controls:** two, both exercised before the clauses so a failing clause
  cannot hide whether the comparison itself is live.
  1. A defect object is compiled from a copy of `kernel/json/measured/` with
     the per-document gate forced on (`s1f_xs_on = 1` at both builders'
     assignments); nothing in `kernel/json/measured/` is edited.  It moves
     exactly the 7 suppressed rows and no other row, its first differing row
     is `short:backslash-n`, and two runs are byte-identical.
  2. The measured transcript with one listed row's position list changed by
     hand, fed back through the driver's `--expect`, exits nonzero and reports
     `mismatch: sparse:one-escape`, while printing the control's rows
     unchanged.
- **Why:** the escape list is what the unescaper visits; a list that omits a
  position, moves one, or is silently not built at all moves the decoded text.
  The measured builder's agreement with a derivation from the rule is the
  executable half of that claim, and the document-level gate is part of what
  the builder actually does.
- **Not claimed:** that a document the rule calls plain carries no escape —
  the rule samples only the low 32 bytes of each sampled block, and the corpus
  holds seven counterexamples the reference names and the gate suppresses; the
  expansion half (`us_dec_x` in `usdec.h`), which is not vendored here; any
  document outside the committed rows; the emitter's timing; or that the
  reference's string-state reading is the only admissible one — it is the rule
  written down, and the corpus's positions are what it names.
- **Where it lives:** `probes/json/escape_measured.c`, `probes/json/escape_driver.c`,
  `tests/json-escape/corpus.tsv`, `tests/json-escape/check.sh`.  The route
  compiles committed sources into a private temporary directory and reads the
  corpus and the vendored headers only.
