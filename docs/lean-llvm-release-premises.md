# The release claim, and every premise under it

**27 November 2026 · `main` at `a88eba5` (64 commits since the handoff at `e88ee2d`)**

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

## Assumption: two, both named in the tree

| premise | anchor | what it says | what would discharge it |
|---|---|---|---|
| `NumFastCalleesAnswered calls epow` | `JsonNumFastAssumed:176` | `calls = stage2NumFastCalls epow`: the selection is the model of the measured C | nothing in this tree — it is the trust statement |
| `fbStkCounts mem v` | `JsonStage2NumFastFallback:349` | the two bignum counts in memory, each within its ninety-six-limb array | a run of the digit ingest and the power nests, which have no model here; the C's clamps give at most forty and fifty-nine limbs |

The second is the count tie. Its numbers are the C's own and are **not**
theorems; the docstring at the tie says so. What *is* proved is the rest of the
chain: the count word bounds the length, and the length bounds the bytes the
copy is given.

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

**The compiler and ABI step.** That the emitted IR the proofs analyse is what the
compiler produces for the measured C, at the measured flags, and that the ABI the
certificate names is the one the driver calls. This is a scoping decision for the
release, not a proved statement, and it is recorded as such.

## The one-line summary

Three of the release's obligations are theorems with callers (the run and its
value, the five callees, the bounds); two are assumptions the tree names; two are
outside the proof — the measured artifact gap, and the compiler/ABI trust
decision. Nothing else is load-bearing, and anything added to this page should
carry its anchor and its footprint.
