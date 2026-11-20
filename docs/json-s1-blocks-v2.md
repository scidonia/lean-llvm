# The stage-1 block unit, v2: the fused UTF-8 loop with an ASCII phase

Status: the body, its contract, its emitted-IR pin and its route are in the
tree; the refinement traces are the next stage.  This page records what
changed, what the pipeline consumes, the proof delta, and the measurement that
motivated the shape.

## The body

`kernel/json/s1_blocks.c` is the classifier over 64-byte blocks, in two loop
shapes.  The first (`for.body`) classifies the leading blocks while they are all
ASCII: it composes each block's entry word, stores it at `ent[i]`, and — when
`arm & 2` — appends the escape list.  It carries no UTF-8 state.  On the first
block with a high bit it runs that block's DFA step, sets `prev_ascii` for it,
and hands the rest of the document to the fused loop.

The fused loop (`for.body54`) runs the classifier and the UTF-8
stage's Keiser–Lemire DFA over the same block loads:

* `%u8k`, the accumulated `<4 x i64>` error vector (`FusedState.u8k`), and
  `%prev_ascii`, the previous block's ASCII answer (`FusedState.prevAscii`);
* the block's two vectors are the ones the classifier already loaded, and the
  DFA's load-form carry is the three bytes at `p - 3`;
* the gated path (`arm & 4 == 0`) skips the DFA when the block and its
  predecessor are both ASCII, which is `utf8.c`'s and `fusedStep`'s skip; the
  ungated path (`arm & 4 != 0`) runs it on every block the loop reaches.  The
  leading all-ASCII blocks never reach it and contribute zero to `u8k`, so the
  verdict does not depend on the arm (`klAll_gate_invariant`).

The return word is two bits:

| bit | meaning |
|---|---|
| 0 | the ASCII probe: `1` exactly when every document byte is below `0x80` (the v1 word) |
| 1 | the UTF-8 error word: `1` exactly when the staged window is **not** a valid prefix; `0` when it is |
| 2+ | zero |

`r & 2 == 0` is the verdict and `r & 1` the ASCII class.  The pipeline therefore
reads the verdict from this unit and the separate `leanllvm_json_utf8` call
disappears; `r & 1 = 1` implies `r & 2 = 0` because an all-ASCII window is a
valid prefix (`fusedVerdict_ascii`, `ascii_window_prefix`).

The caller stages three zero bytes before the document (`3 ≤ b`), which is
`utf8.h`'s obligation and the reason the fixture's buffer places the document at
offset four.  The pre in `JsonS1BlocksContract.lean` states the read of those
three bytes and the `n < 2^63` bound.

## The contract and the pin

* `s1BlocksPost` (`JsonS1BlocksSteps.lean`) keeps the entry-word, escape-list
  and frame clauses and replaces the `0/1` return clause with the two-bit
  clauses: `r &&& 3 = r`, `(r &&& 1 = 1 ↔ ∀ x ∈ bs, x.toNat < 0x80)`, and
  `(r &&& 2 = 0 ↔ utf8WinPrefix (utf8Window bs bs.length (blocksOf bs.length)))`.
* `probes/install/ir/json-s1-blocks.candidate.ll` is the new emission (23
  blocks, 633 lines).  `JsonS1BlocksIR` pins it block by block, including the
  five call targets and the no-`alloca` guard.  The census is the classifier's
  two intrinsics, `llvm.usub.sat.v32i8` and the two lane tests, and the escape
  list: three escape-list calls, twelve `usub.sat`, six `ptestz`, thirty
  `pshuf.b`, and three `pclmulqdq`, because the ASCII phase, the fused loop and
  the peeled tail each carry a classifier body and a DFA site.
* `tests/json-s1-blocks/check.sh` runs four arms (`0, 2, 4, 6`): gated/ungated,
  each without/with the escape list.  It compares the object with the pinned
  Lean body; checks bit 0 against the staged document's high bits; checks bit 1
  against a scalar UTF-8 prefix reader that shares no code with the object; and
  asserts that the gate does not move the word.

  On the EPYC worker the route's first step — regenerate the fixture and require
  the committed bytes — must run with the flake's `clang`, because the worker's
  system `clang` emits different hardening attributes (`sspstrong`,
  `probe-stack`, `zero-call-used-regs`, `dso_local`) from the pinned compiler
  line.  The object-versus-model half runs on that worker directly: the driver
  and `leanllvm-json-s1-blocks` produce identical rows over the corpus and all
  four arms.

## The measurement

`tests/json-units-bench/bench-s1-blocks.sh` times the v1 composite
(`s1_blocks_v1.c` + the separate `leanllvm_json_utf8` call) against the v2 body
at the same ABI.  The transcript is
`tests/json-units-bench/bench-s1-blocks-transcript.txt`; the full table and its
caveats are in
[the performance page](json-pipeline-performance.md#the-fused-block-unit-v2-measured).

The run is one AMD EPYC 7B12 session, 11 rounds of 41 repetitions, `taskset -c
0`, load 1.09 at start; the transcript records the host, both bodies' sha256s
and the corpus.  The ASCII phase removes the v2 regression: the ASCII-first
documents read 0.95–0.99 as v2 ÷ v1 across the four arms, including
`syn-dense-64k`'s ungated list arm — the row that read 1.198 before — at 0.991.
The UTF-8 classes keep the fused gain: `syn-utf8-64k` reads 0.914 (gated,
list-free), 0.957 (gated, list), 0.931 (ungated, list-free) and 0.964 (ungated,
list), and `syn-utf8-4m` reads 0.927–0.962 in every arm.

## Proof delta

The v1 traces are not re-proved.  The ASCII phase is a new loop, the fused loop
keeps the v2 meaning, and the post is unchanged.  What changes, block by block:

| block | relation to v2 | obligation |
|---|---|---|
| `entry` | unchanged except the register numbers | v2 trace, renamed |
| `for.body.lr.ph` | phase-1 preheader; no DFA state is carried | one `denoteCode` step |
| `for.body` | the ASCII-phase loop: classifier and entry word only, with the escape-list arm; no `u8k`, no `prev_ascii`, no ASCII accumulator | the v1 mask trace at the phase's registers |
| `if.end` | the phase's `ptestz` on the block's `or` and the break test | `klAsciiBlk`'s reading of the two vectors |
| `for.inc` | the ASCII phase's latch | the v1 latch trace |
| `if.then38` | the hand-off: the block's DFA step, `prev_ascii = 0`, `u8k = klErrBlk` | `klErrBlk`'s fold; `fusedStep` at an ASCII predecessor |
| `if.end50` | the phase-to-fused phis: `prevS`, the three carries, `u8k`, `prev_ascii`, `ascii` and `i` | one phi step per register; `fusedRun`'s pair at the hand-off |
| `for.body54.lr.ph` | the fused loop's preheader and the escape-list test | one `denoteCode` step |
| `for.body54` | the fused loop; the v2 body's block, renamed | the v1 mask trace; the block's `klAsciiBlk`/`klErrBlk`; `fusedStep_klStep` |
| `if.then90` | the fused loop's DFA arm | `klErrBlk`'s fold; `fusedStep_advances` |
| `if.end93` | the fused loop's `u8k` phi | one phi step |
| `if.then96` | the fused loop's escape-list arm | the v1 escape-list trace |
| `if.end98` | the fused latch | v1 trace |
| `for.end101` | the fused loop's exit | one `denoteCode` step |
| `if.then103` | the peeled tail plus its `ptestz`/gate select | the v1 tail trace and the block's `klErrBlk` |
| `if.then144` | the tail DFA arm | as `if.then90` |
| `if.end147` | tail `u8k` phi and the escape-list test | one phi step plus the v1 arm test |
| `if.then150` | the tail escape-list arm | v1 trace |
| `if.end153.thread` / `if.end153` | the stage's document-end rule | `fusedVerdict`'s body, `fusedVerdict_run_eq_klStage` |
| `if.then164` | the tail-byte test | `klTailByte`'s definition |
| `if.end170` | the ASCII word and the two-bit composition | `r & 1` is the v1 probe and `r & 2` is `fusedVerdict` |

`JsonUtf8Fused` plugs into the fused loop's trace at four points:

1. `fusedStep_klStep` — the `if.then90`/`if.then144` arms are `klStep` at
   `klPre win bi`/`klBlk win bi`, so the arm's register computation is the
   stage's step rather than a look-alike.  `klPre_succ` ties the `p - 3` carry
   of block `bi + 1` to the previous block's last three bytes.
2. `fusedRun_advance` / `fusedRun_word_eq_klAcc` — the `%u8k` phi at
   `for.body54` carries `klAcc bs i`; this is the loop invariant the trace must
   establish at `if.end98`.
3. `fusedRun_word_eq_klAll` — at the fused loop's exit the accumulator is the
   stage's `klAll`, so the cleanup phi and the tail arm's `or` land on the
   stage's word.  The hand-off's `u8k` is the same pair at the first non-ASCII
   block; the ASCII prefix contributes zero (`utf8Skip_eq_zero`).
4. `fusedVerdict_run_eq_klStage`, `fusedVerdict_zero_iff_unit_post` and
   `fusedVerdict_eq_of_unit_post` — the document-end composition is
   `fusedVerdict`, and its zero set is `utf8WinPrefix (utf8Window bs n nb)`,
   which is the post's clause.  The ASCII shortcut is
   `fusedRun_ascii`/`fusedVerdict_ascii`; the `r & 1` clause is the v1 ASCII
   trace.

The budget in `JsonS1BlocksContract.lean` is now `8 * blocksOf n + 32`.  The
fused loop's worst path is five control steps (body → DFA arm → escape arm →
latch); the ASCII phase is shorter, and the hand-off's DFA step and the tail's
own two arms are the constant part.

Still owed, and not claimed here:

* `s1_blocks_refines` — the per-block `denoteCode` composition for the 23
  blocks, the phase loop's induction and its hand-off, the fused loop's
  induction at `if.end98`, the DFA arms' refinement (`JsonUtf8Steps`'
  `utf8Gated_loop_run` at the host's registers), and the return-word
  composition;
* `s1_blocks_undefined_of_no_read` — the same totality companion as v1, now
  including the `p - 3` reads of the hand-off block and the tail's `b[n-1]`;
* `s1_blocks_satisfies` — the `Γ_s1_blocks` instance at the new post and budget;
* the frame theorem over `ent`, `xp`, `nxp` and `xcarry` (v1's obligations,
  unchanged), and the pre's `readBytes (b - 3) 3 = [0, 0, 0]` in the
  environment.
