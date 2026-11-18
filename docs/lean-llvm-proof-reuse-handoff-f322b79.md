# Reusing LLVM proofs across JSON parser changes

Captain’s handoff · 18 November 2026 · [scidonia/lean-llvm at `f322b79`](https://github.com/scidonia/lean-llvm/commit/f322b79db02fd8c8d53d0309937c2417b478070b)

**Extract a reusable path-transport theorem and a framing rule for `BoundLoop`. Use the fraction scan as the first new client.** The practical test is whether a caller can ask for one more preserved register, obtain it at the actual loop exit, and finish its proof without reopening the digit-loop induction.

## Where the proof time goes

At this revision, `intScan_t1_arm_at_entry` runs the emitted function from entry to return for its covered tier‑1 integer inputs. Under its lexeme, range and table assumptions, it returns success, writes the eight bytes specified by `strtodSpec`, preserves the allocator cursor and frames the memory update. This is a useful regression theorem because its conclusion is observable at the caller. The full numeric arm still needs other routes and arithmetic obligations. [Integer entry theorem](https://github.com/scidonia/lean-llvm/blob/f322b79db02fd8c8d53d0309937c2417b478070b/LeanLLVM/Refinement/JsonStage2NumFastCellsRun.lean#L213) · [Remaining obligations](https://github.com/scidonia/lean-llvm/blob/f322b79db02fd8c8d53d0309937c2417b478070b/LeanLLVM/Refinement/JsonStage2NumFastArm.lean#L357)

The integer scan already had an execution proof when the converter needed the output pointer, table symbols and sign at the exit. Its fuel equation explained how to continue from the exit, but exposed too little about the path to transport those facts. The developers went back to the iteration arms, proved preservation there and conjoined it to the loop invariant. The fraction scan now needs the integer accumulator cells `%idig.4` and `%ip.5` that an earlier block established. This is the recurring cost to remove. [Integer loop with carried cells](https://github.com/scidonia/lean-llvm/blob/f322b79db02fd8c8d53d0309937c2417b478070b/LeanLLVM/Refinement/JsonStage2NumFastCellsRun.lean#L103) · [Fraction and exponent loop arms](https://github.com/scidonia/lean-llvm/blob/f322b79db02fd8c8d53d0309937c2417b478070b/LeanLLVM/Refinement/JsonStage2NumFastDigitRuns.lean#L2759)

## 1. Keep a counted witness for the executed path

Generalise `NumFastChain` over the function being executed. Its existing constructors already describe an empty path or an admitted jump followed by the rest of the path. Give the generic path a count and retain the predicate on visited blocks. Export composition, a continuation fuel equation, and transport of any property preserved by each admitted step. A region can then hide its internal SSA details while callers retain access to these three consequences. [Existing chain and transport lemmas](https://github.com/scidonia/lean-llvm/blob/f322b79db02fd8c8d53d0309937c2417b478070b/LeanLLVM/Refinement/JsonStage2NumFastCells.lean#L269)

For a path of length `j` from `s` to `e`, the fuel consequence is `∀ k, runFuel calls (j + k) f s = runFuel calls k f e`. Transport says that if `P s` holds and every admitted jump preserves `P`, then `P e` holds. Both conclusions must use the same `e`. Have the producer build the witness from the concrete jump proofs it already performs. A fuel equation on its own does not tell a later caller which blocks were visited.

Begin with registers. `numFast_step_lookup` already proves that a successful jump preserves a register lookup when the executed block contains no instruction writing that register. Its proof reuses an instruction-list lemma from the JSON entry emitter. Generalise this result once, then use a decidable check over the pinned blocks’ destinations to prove the side condition. Keep the domain narrow enough to admit facts such as “the sign survives after leaving the block that writes it.” For memory across a store or call, use separation and the callee’s write frame. Preserving a pointer register alone says nothing about its pointee. [Step-level preservation proof](https://github.com/scidonia/lean-llvm/blob/f322b79db02fd8c8d53d0309937c2417b478070b/LeanLLVM/Refinement/JsonStage2NumFastCells.lean#L202)

## 2. Lift a caller property through a bounded loop

Add a companion rule to `BoundLoop`. Given loop invariant `I`, exit postcondition `Q`, and caller property `P`, let a caller use `I ∧ P` at the head and obtain `Q ∧ P` at the exit. Reuse the same measure, cost and fuel bound. Each exit or back-edge arm supplies one endpoint and counted execution witness. Its transport proof establishes `P` at **that endpoint**. Back edges additionally establish the next invariant and decrease the remaining budget. [Current loop interface](https://github.com/scidonia/lean-llvm/blob/f322b79db02fd8c8d53d0309937c2417b478070b/LeanLLVM/Refinement/LoopFuel.lean#L243)

Keep the present `BoundLoop` available to existing users. A compatible implementation can take stronger arm witnesses and project the existing fuel equations from them. This lets the integer and fraction scans migrate first. It also avoids a subtle invalid rule: an arbitrary existing `BoundLoop` value need not expose enough information to derive preservation of a newly requested property.

**Pilot acceptance**

1. Recover the existing `intScan_t1_arm_at_entry` statement through the generic rule, with the same input assumptions, observable postcondition and permitted axiom footprint.
2. Carry `%idig.4` and `%ip.5` through the fraction scan starting after their defining block. Use the resulting equalities in the caller’s arithmetic proof at the actual exit.
3. Request another live, unwritten register at the consumer. Record which files changed and the warm build time. Success means the new proof is local to the consumer and its write-set check.
4. In a small negative fixture, add a write to a claimed preserved register. Verify that the original generic side condition fails. Retain a positive control showing the original fixture passes.

## 3. Automate repeated straight-line proofs

The source review counted 388 lines containing `repeat rw [lookupName_cons_ne` across 46 files under `LeanLLVM/Refinement`. This is evidence of repeated authoring work. Its contribution to elaboration time still needs measurement.

After the framing pilot, try a kernel-checked tactic on two pinned blocks with different phi predecessors. Have it select the incoming operand from the actual predecessor, evaluate the straight-line instructions, and discharge lookup preservation from the block’s destinations. Leave arithmetic bounds, memory aliasing and callee contracts as explicit goals. Test a changed incoming edge as well as a changed register destination. Compare proof-edit time and elaboration time against the existing scripts before widening its use.

## Runtime evidence and the next performance experiment

Correct the ratio interpretation before choosing which code to rewrite. For `syn-strings-64k` on the P core, the table reports **simdjson stage‑1 time divided by summed unit time = 0.49**. Its throughput columns give 16.0 GB/s for simdjson and 8.68 GB/s for the units. Simdjson takes roughly half the time on this case. The optimisation note currently describes that row in the opposite direction. [Stage‑1 comparison](https://github.com/scidonia/lean-llvm/blob/f322b79db02fd8c8d53d0309937c2417b478070b/docs/json-pipeline-performance.md#L745) · [Optimisation note](https://github.com/scidonia/lean-llvm/blob/f322b79db02fd8c8d53d0309937c2417b478070b/docs/speed-ratio-measures.md)

The full native call also costs more than simdjson’s full parse on the three accepted 64 KiB documents. The two implementations produce different outputs. The ratios below compare elapsed time on the same input. Absolute times are P-core medians rounded to microseconds. [Stage timings](https://github.com/scidonia/lean-llvm/blob/f322b79db02fd8c8d53d0309937c2417b478070b/docs/json-pipeline-performance.md#L1082) · [Paired ratios](https://github.com/scidonia/lean-llvm/blob/f322b79db02fd8c8d53d0309937c2417b478070b/docs/json-pipeline-performance.md#L1177)

| Input | Admission | Staging | Native | Consumer | Native time ÷ simdjson full-parse time |
|---|---:|---:|---:|---:|---:|
| Dense | 64 µs | 42 µs | 140 µs | 268 µs | 1.68 |
| Strings | 231 µs | 163 µs | 86 µs | 93 µs | 5.98 |
| UTF‑8 | 373 µs | 164 µs | 74 µs | 36 µs | 4.32 |

For strings, removing the entire 86 µs native interval from the measured 575 µs end-to-end time would give approximately **1.18×** speedup if the other intervals stayed fixed. On dense input the consumer is the largest component. These figures support keeping the current kernel pinned while testing workspace reuse. Measure the same three documents with fresh and reused workspaces. Keep all four intervals, the output and the error policy comparable. Include alternating documents of different shapes to exercise cursor reset and stale buffer contents. A new allocation or reuse discipline will need its own wrapper proof before adoption.

## Assignments for the captain

| Owner | Deliverable | How it joins |
|---|---|---|
| Path and loop rules | Generic counted path, register transport, loop framing and migration of the covered integer theorem | Publish the proposed signatures and downstream application first. Preserve the integer theorem as the first integration check. |
| Fraction route | A caller proof consuming both integer accumulator cells at the fraction exit | Start against an explicit parameter of the agreed type. Close it using the first worker’s theorem and an actual staged input. |
| Runtime experiment | Paired fresh/reused-workspace timings, unchanged result checks and the corrected ratio interpretation | Own the benchmark and its report in a separate branch. Run on an idle measurement host. |

Give each owner a branch at the same immutable base and exclusive writable paths. Keep edits to the shared import roots with the integrator. Judge the proof pilot by elapsed time until the fraction *consumer* builds and by the cost of adding a new preserved register afterwards. If a faster runtime candidate earns its proof cost, state its contract in the same caller-visible terms so a replacement can reuse the surrounding parser proof.

This handoff is based on the pinned source and the project’s reported timings. The proposed abstraction, its proof-rate improvement and the workspace-reuse experiment have not been independently built or measured here.

