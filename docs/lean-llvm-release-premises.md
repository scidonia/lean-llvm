# The release claim, and every premise under it

**28 November 2026 · `main` at `98bd149` (92 commits since the handoff at `e88ee2d`)**

This page exists so that a reader can see, without reconstructing it from the
tree, exactly what a release claim for the certified JSON parser rests on at
this revision — which parts are theorems, which are assumptions the claim
names, and which are outside the proof entirely. It is the list the review at
`2477864` asked the next review to open with.

The claim under discussion is the deployed fast call, on the admitted input
domain, terminating and returning the same caller-visible result as the
reference decoder.

## Theorem: the run and its value

| statement | anchor | footprint |
|---|---|---|
| the emitted stream's value at the run's post is the reference decoder's canonical value, given the run's own facts | `JsonEventEmission.evb_emission_of_spec` | pinned in `LeanLLVMTest/Refinement.lean` |
| the emission at `[1]`'s accept route, from the walk's four reads | `JsonStage2WalkSpansChain.evb_emission_of_bracket_walk` | `[propext, Classical.choice, Quot.sound]` |
| the walk's interface: the `%ndst` and `%nev` words and the two payloads, each read at its own address and length | `JsonNumFastSpine.JsonWalkReads`, `JsonStage2WalkSpansNil.walk_accept_ndst_zero_of_reads` | `[propext, Quot.sound]` |
| **the caller's result for staged `[1]`** — verdict, both cursors, both payloads, the canonical value and the certificate, with **no** segment, carry equation, numeral record or window among its hypotheses | `JsonEventCallerResultEntry.evb_caller_result_staged` | `[propext, Classical.choice, Quot.sound]` |

A frame cannot substitute for the interface: `UnchangedOutside` is silent
inside its region list, and the report's list is not the walk's. Both failures
are proved there (`frame_not_identifying`, `reportFrame_not_walkWideAt`), which
is why the interface is four reads rather than an equality of the heap.

## Theorem: the callees

| callee | statement | anchor |
|---|---|---|
| `num_d8_el1` | both exits of the digit shortcut | `JsonStage2NumFastCalleeD8.numD8_run_success`, `numD8_run_refusal` |
| `num_el_el1` | the body's run as a `CallOutcome` equality on all four routes, and its site | `JsonStage2NumFastCalleeElRun.numElBodyCalls_eq`, `JsonStage2NumFastCalleeElSeam.numFast_ifEnd268_denote_body` |
| `stk_mul_u64` | the group loop from its head to the join, measure decreasing | `JsonStage2NumFastCalleeMulRun.loop_run_at` |
| `stk_cmp` | the copy block and what the caller relies on | `JsonStage2NumFastCalleeCmp.numCmp_run_copy_stage2`, `numCmp_copy_span`, `numCmp_copy_count` |
| `__memcpy_chk` | the fortified copy's contract, and its answer derived from the selection | `JsonStage2NumFastCalls.numMemcpyChkAnswer_copy`, `JsonNumFastAssumed.numFastCalleesAnswered_memcpyChk` |

Two facts about this list are worth stating because they are easy to get wrong.
The selection and the body's own environment can **never** be the same function
— one answers four callees and the other one — and that is proved, with the two
answers in view (`numElBodyCalls_ne_stage2NumFastCalls`); what the route needs,
and has, is the kernel's answer at its own arguments. And the exponent's table
bound (`t.e` inside the signed decode's range) is a **kernel check over all
ninety-one rows**, not a comment (`epow_rows_e_bounds`).

## Theorem: the bounds

| bound | statement | anchor |
|---|---|---|
| the window's significand and its fold fit the limb capacity | `window_M_lt_two_pow`, `window_fold_lt` | `JsonStage2NumFastStkArith` |
| the five- and ten-powers fit at the largest exponent the clamps admit | `pow_five_lt`, `pow_ten_lt` | same |
| the accumulation's carry stays inside a limb | `stkMulFold_carry_lt_96` | same |
| the comparator's copy length, and the constant half | `numCmpCopyLen_le_of_value` (`8·n ≤ 776`) | same |
| the producer's two counts, from the nests' own call counts | `ingest_limbs_le`, `pow_five_limbs_le`, `pow_ten_limbs_le`, `fold_limbs_le` (`41`, `42`, `59`, `58` limbs) | `JsonStage2NumFastProducerCount` |

## Assumption: three, all named in the tree

| premise | anchor | what it says | what would discharge it |
|---|---|---|---|
| `NumFastCalleesAnswered calls epow` | `JsonNumFastAssumed:176` | `calls = stage2NumFastCalls epow`: the selection is the model of the measured C | nothing in this tree — it is the trust statement |
| `fbStkCounts mem v` | `JsonStage2NumFastFallback:349`, read at `NumFastProducerCount.stkBnCountTie` | the two bignum counts in memory, each within its ninety-six-limb array | a statement that each nest's memory is the model's run: the counts are bounded from the nests' guards (`41`, `42`, `59`, `58` limbs, each under `96`) and the store's own count is proved (`stkMulAddAnswer_count`), so what remains is that the emitted body is `stkMulAddRun` from the entry's zero or one |

| the cursor record's words at `%c.i` | `JsonEventCallerResultSeamWords` (the seam's environment row), reported by the caller | the staged record's base and error pointer, which `walkSeg3Stores` writes and no block of the walk rewrites | nothing in the walk's invariant: `WalkInv` carries the record's address, its presence and a frame that is silent *inside* it, so the words have to be a row where the seam reads them — or `WalkInv` gains them beside a second frame, which is the widening this tree has been shrinking |

| ~~the staged error pointer's width~~ | **removed in `98bd149`** | the bound is now part of the ABI precondition, the staging record, the route's precondition and the walk's stage, so the error word is produced from the entry memory rather than assumed | — |

The fourth assumption — the staged error pointer's width — was removed rather than
discharged by argument: the bound joined the ABI precondition's address-word group
(beside `b`, `ep`, `dst` and `ev`), was threaded through the staging record and the
route's precondition by the layout refusal, became a field of the walk's stage and
geometry, and with it the seam's error word is produced from the entry memory. The
measurement that made this worth doing is recorded in the commit: eleven files,
+171/−52, one constructor that needed the workspace table's address word named.

The second is the count tie. The third is the cursor record: its token half —
position, end and kind — is now **proved** from the seam's own stores
(`evbSeam_pos`, `evbSeam_end`, `evbSeam_kind`), and what remains unproved is the
base word the staging reads at `%c.i`, without which the lexeme's window and
therefore the numeral's record are not determined.

The count tie. Its *numbers* are no longer only the C's:
`JsonStage2NumFastProducerCount` bounds the counts the emitting blocks can write
from the guards alone — one `stk_mul_add` appends at most one limb
(`stkMulAddCalls_length_le`), the digit guard `R < 768` makes the ingest at most
`41` limbs, and the clamps make the power nests at most `42` (sticky, `5 ^ 27`)
and `59` (exact, `10 ^ 19`), with `58` for the significand on the one branch
that folds `10 ^ S` into it. The store's own count is proved too: the add-carry
answer `stkMulAddAnswer` leaves `stkCount mem a = some (stkMulAddLimbs ws m c).length`
(`stkMulAddAnswer_count`), `stkMulAddRun_exact` keeps that invariant over a nest's
calls, and `sticky_ties_of_runs` composes the ingest's and the sticky power's
runs into `numCmp_copyLen_le_of_sticky_runs`, which carries no tie and no count
bound. What is left of the tie is the one thing no arithmetic gives: that the
emitted nests *are* those runs — `mem = (stkMulAddRun base a ws calls).1` with
`calls.length = nestSteps` at the inlined stores
(`for.body.i.i.i`:1415, `while.body.us.i.i.i.i`:1709, `for.body.i566.i.i`:2012).
`stkBnCountTie` is that statement at each store, and `fbStkCounts_of_ties` turns
it into the epilogue's premise. What *is* proved is the rest of the chain: the
count word bounds the length, and the length bounds the bytes the copy is given.

The tie's other side is now read off the store's own block rather than off the
run: `stkCount_writeCount_bytes` (four bytes at `base + 768` read back as the
count) composed with the block that writes the cell — `cleanup_denote` /
`sinkSplit_denote` for the ingest, `end151_denote` for the power's `1`,
`end176_denote` / `whileEnd_denote` for its counts — *is* the tie, so what is
left at each of them is one `Nat` inequality on the word the block stored, with
no memory shape carried (`fbStkCounts_of_cleanup_end151` takes `fbStkCounts`
across the ingest's spill and the staging's two stores from `%78 ≤ nestSteps 19
R`, and `powOneCountTie_of_end151` needs no bound at all). The remaining
inequality is the nest's trip count. The residual digit-ingest append is stated:
`while.body.us.i520.i.i` has its step and count readback (`bus520_step`,
`bus520_count_read`), and `bus520_count_tie` derives both the `≤ 95` bound and
the tie's `x + 1 ≤ nestSteps 19 R` from the chunk loop's exit invariant,
`ingestChunkInvariant`, leaving `ingestCountTie` at `nestSteps 19 R`
(`JsonStage2NumFastIngestAppend`). The same invariant gives `%78 ≤ nestSteps 19
R`, so `fbStkCounts_of_chunkEnd151` feeds the cleanup path's
`fbStkCounts_of_cleanup_end151`. What remains there is that invariant at the
loop's own exit. The fold's append is now stated with its readback —
`while.body.us.i.i624.i.i` (`bus624_step`, `bus624_readback`) — and the count
store outside it, `while.end190.i.i`'s `%116` spill, reads back at the count's
cell with the limbs untouched (`end190_readback`, `end190_spill_tie`), both in
`JsonStage2NumFastFoldAppend`. The exact power's append of the same shape,
`while.body.us.i.i557.i.i`, is stated with its readback in
`JsonStage2NumFastPowAppend` (`bus557_readback`, `bus557_bnLimbs`), taking the
loop invariant that the counter and the index name the same number
(`c.toNat = w`) — which is the one premise no block statement can supply.

## Outside the proof: two items

**The artifact transfer.** The fixture and the linked object are not the same
function, and `docs/json-route-artifact-correspondence.md` measures the gap: same
source, flags differing in the optimisation level alone, three of eleven helper
bodies identical under the transform, the walk's body different (937 instruction
lines against 622), and **ten helper call sites the fixture keeps that the object
inlines**. A release claim therefore carries, in addition to the theorems above:
the fixture→object correspondence as measured, the compiler/backend trust row,
and the transfer of each differing helper's contract. None of the three is
implied by the shared filename.

**The compiler and ABI step — decided, and scoped.** The certificate is scoped to
the modelled IR and its stated hypotheses. For the existing production object, the
fixture-to-production correspondence is a **separate, open premise**; the
differential tests (`tests/json-*`) are its evidence, not its proof. The pinned
LLVM toolchain is trusted to compile the identified IR, and the Lean/C ABI
assumptions are to be stated explicitly beside the certificate rather than implied
by its fields.

The direction that closes the gap structurally is stated here so it is not lost:
**emit the production IR once, prove that module against the caller contract, and
compile and link that same artifact**, so no fixture-versus-production step exists
to transfer. A validated semantics-preserving bridge from the existing fixture is
an acceptable alternative. Per-helper correspondence is deferred unless it closes
a specific obligation on this path — and the measurements above say it would be
partial by nature (six of eleven bodies differ under the transform).

## The one-line summary

Three of the release's obligations are theorems with callers (the run and its
value, the five callees, the bounds); two are assumptions the tree names; two are
outside the proof — the measured artifact gap, and the compiler/ABI trust
decision. Nothing else is load-bearing, and anything added to this page should
carry its anchor and its footprint.
