# The stage-1 block unit, v2: the fused UTF-8 loop

Status: the body, its contract, its emitted-IR pin and its route are in the
tree; the refinement traces are the next stage.  This page records what
changed, what the pipeline consumes, the proof delta, and the measurement that
motivated the shape.

## The body

`kernel/json/s1_blocks.c` is one loop over 64-byte blocks.  It classifies the
block, composes the entry word, stores it at `ent[i]`, and — when `arm & 2` —
appends the escape list.  Unlike the first body, the same loop also carries the
UTF-8 stage's Keiser–Lemire DFA:

* `%u8k`, the accumulated `<4 x i64>` error vector (`FusedState.u8k`), and
  `%prev_ascii`, the previous block's ASCII answer (`FusedState.prevAscii`);
* the block's two vectors are the ones the classifier already loaded, and the
  DFA's load-form carry is the three bytes at `p - 3`;
* the gated path (`arm & 4 == 0`) skips the DFA when the block and its
  predecessor are both ASCII, which is `utf8.c`'s and `fusedStep`'s skip; the
  ungated path (`arm & 4 != 0`) runs it on every block.  The verdict does not
  depend on the choice (`klAll_gate_invariant`).

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
* `probes/install/ir/json-s1-blocks.candidate.ll` is the new emission
  (17 blocks, 436 lines).  `JsonS1BlocksIR` pins it block by block, including
  the five call targets and the no-`alloca` guard.  The census is the
  classifier's two intrinsics, `llvm.usub.sat.v32i8` and the two lane tests, and
  the escape list.
* `tests/json-s1-blocks/check.sh` runs four arms (`0, 2, 4, 6`): gated/ungated,
  each without/with the escape list.  It compares the object with the pinned
  Lean body; checks bit 0 against the staged document's high bits; checks bit 1
  against a scalar UTF-8 prefix reader that shares no code with the object; and
  asserts that the gate does not move the word.

  On the EPYC worker the route's first step — regenerate the fixture and require
  the committed bytes — is a setup failure, because the worker's system `clang`
  emits different hardening attributes (`sspstrong`, `probe-stack`,
  `zero-call-used-regs`, `dso_local`) from the pinned flake compiler line.  The
  object-versus-model half was run directly on that worker instead: the driver
  and `leanllvm-json-s1-blocks` produced 84,252 identical rows over the corpus
  and all four arms.  The capture self-check still belongs to a flake-clang
  host.

## The measurement

`tests/json-units-bench/bench-s1-blocks.sh` times the v1 composite
(`s1_blocks_v1.c` + the separate `leanllvm_json_utf8` call) against the v2 body
at the same ABI.  The transcript is
`tests/json-units-bench/bench-s1-blocks-transcript.txt`; the full table and its
caveats are in
[the performance page](json-pipeline-performance.md#the-fused-block-unit-v2-measured).
The acceptance row, `syn-utf8-64k`, reads 0.903 (gated, list-free), 1.081
(gated, list-on), 0.953 (ungated, list-free) and 1.370 (ungated, list-on) as
v2 ÷ v1; `syn-utf8-4m` and `route-u8-64k` read 0.91-0.95 in every arm.  The
ASCII-first documents pay 1.00-1.39, the ungated arms most, because the gate's
skip is the work they avoid.

## Proof delta

The v1 traces are not re-proved.  The v1 body's blocks keep their meaning; the
new emission splits the escape arm and the DFA arm into their own blocks and
adds the word composition.  What changes, block by block:

| v2 block | relation to v1 | obligation |
|---|---|---|
| `entry` | new `%conv = (arm >> 2) & 1`; the `n < 64` test is unchanged | the shift/and are `denoteCode` steps; no new state |
| `for.body.lr.ph` | unchanged except the register numbers | v1 trace, renamed |
| `for.cond.cleanup.loopexit` | new: carries `%5` (the last block's ASCII answer) into the cleanup phi | one `denoteCode` step |
| `for.cond.cleanup` | new `%prev_ascii` and `%u8k` phis; the tail test is unchanged | `fusedRun`'s pair at the block count; the v1 tail dispatch |
| `for.body` | adds `%or.i170`, its `ptestz`, `%or.i169` (the same ASCII accumulator), the `u8k` phi and the gate select; the entry word is unchanged | the v1 mask trace; the block's `klAsciiBlk`/`klErrBlk` reading; `fusedStep_klStep` |
| `if.then` | the DFA arm: the three loads at `p-1,p-2,p-3`, the three `pshuf.b` tables, two `usub.sat`, the `xor`, and the `or` into `%u8k` | `klErrBlk`'s fold over the block, i.e. `JsonUtf8Steps`' byte-level `klErr32` and `fusedStep_advances` |
| `if.end` | new `%u8k` phi | one phi step |
| `if.then29` | the escape-list arm, moved out of the body (registers unchanged) | the v1 escape-list trace |
| `if.end31` | the latch, unchanged | v1 trace |
| `if.then33` | the peeled tail plus its `ptestz`/gate select | the v1 tail trace and the block's `klErrBlk` |
| `if.then74` | the tail DFA arm | as `if.then` |
| `if.end77` | tail `u8k` phi and the escape-list test | one phi step plus the v1 arm test |
| `if.then80` | the tail escape-list arm | v1 trace |
| `if.end83.thread` / `if.end83` | the stage's document-end rule: `ptestz` on `u8k`, and (for `n % 64 = 0`) the last byte's `klTailByte` | `fusedVerdict`'s body, `fusedVerdict_run_eq_klStage` |
| `if.then94` | the tail-byte test (`(b & 0xFE) == 0xC0 || b >= 0xF5`) | `klTailByte`'s definition |
| `if.end100` | `%ascii.1278` phi, `ptestz` on it, `%conv104 = ascii`, `%shl105 = err ? 2 : 0`, `%or106 = ascii | (err << 1)` | the two-bit word: `r & 1` is the v1 probe and `r & 2` is `fusedVerdict` |

`JsonUtf8Fused` plugs into the loop trace at four points:

1. `fusedStep_klStep` — the `if.then`/`if.then74` arm is `klStep` at
   `klPre win bi`/`klBlk win bi`, so the arm's register computation is the
   stage's step rather than a look-alike.  `klPre_succ` is what ties the
   `p - 3` carry of block `bi + 1` to the previous block's last three bytes.
2. `fusedRun_advance` / `fusedRun_word_eq_klAcc` — the `%u8k` phi at
   `for.body` and `if.end` carries `klAcc bs i`; this is the loop invariant the
   trace must establish at `if.end31`.
3. `fusedRun_word_eq_klAll` — at `for.cond.cleanup.loopexit`/`if.end83` the
   accumulator is the stage's `klAll`, so the cleanup phi and the tail
   arm's `or` land on the stage's word.
4. `fusedVerdict_run_eq_klStage`, `fusedVerdict_zero_iff_unit_post` and
   `fusedVerdict_eq_of_unit_post` — the `if.end83`/`if.then94`/`if.end100`
   composition is `fusedVerdict`, and its zero set is
   `utf8WinPrefix (utf8Window bs n nb)`, which is the post's clause.  The ASCII
   shortcut is `fusedRun_ascii`/`fusedVerdict_ascii`; the `r & 1` clause is the
   v1 ASCII trace.

The budget in `JsonS1BlocksContract.lean` is now `8 * blocksOf n + 16`.  The
worst path through a block is `for.body` → DFA arm (or `if.end`) → escape arm
(or `if.end31`) → latch: five control steps, plus the tail path's own two; the
constant is slack, not a tight count.  The v1 constant (`4 * blocks + 8`) no
longer covers the CFG.

Still owed, and not claimed here:

* `s1_blocks_refines` — the per-block `denoteCode` composition for the 17
  blocks, the loop induction at `if.end31`, the DFA arm's refinement
  (`JsonUtf8Steps`' `utf8Gated_loop_run` at the host's registers), and the
  return-word composition;
* `s1_blocks_undefined_of_no_read` — the same totality companion as v1, now
  including the `p - 3` reads of the first block and the tail's `b[n-1]`;
* `s1_blocks_satisfies` — the `Γ_s1_blocks` instance at the new post and budget;
* the frame theorem over `ent`, `xp`, `nxp` and `xcarry` (v1's obligations,
  unchanged), and the pre's `readBytes (b - 3) 3 = [0, 0, 0]` in the environment.
