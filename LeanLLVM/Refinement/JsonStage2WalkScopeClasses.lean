import LeanLLVM.Refinement.JsonStage2WalkScopeDispatch

set_option autoImplicit false

namespace LeanLLVM.Refinement

open LeanLLVM
open LeanLLVM.Refinement.JsonStage2IR
open LeanLLVM.Refinement.BlockEval

/-! ## The middle's two classes

`WalkLink` is what the dispatch's trace is made of, and the two links above are
hand-written: a block's `denoteCode`, its terminator, and the twenty-two clauses
of `WalkInv` re-established one at a time.  At that price the ~140 blocks between
the arms are not writable, so the middle is classified instead, and each class is
one lemma whose instances differ only in the block's text.

## The census

The classification is a census of the pinned body's 165 blocks by the shape that
decides what a link proof costs.  The shape is the opcode sequence, because a
block's `denoteCode` is one step per instruction and what a step costs is set by
the instruction's constructor, not by the block's name.

| class | shape | blocks | proved |
|---|---|---:|---|
| A | one `icmp` and a `condbr` on its result | 60 | 60 |
| B | no instructions and a `br` | 9 | 9 |
| B′ | no instructions and a `condbr` on a carried bit | 1 | 1 |
| C | the refusal store: `gep %e+8`, `store i64`, `br` | 18 | 18 |
| D | other `store` shapes | 11 | 11 |
| E | a `phi`-headed block | 15 | 15 |
| F | a block that calls | 19 | 17 |
| G | `load` and compare | 14 | 14 |
| H1 | the arithmetic latch: `add` + `icmp` + `condbr` | 10 | 6 links + 4 rounds |
| H2 | `while.body.i.lr.ph` (five `gep`) and `if.then281.i` (`add`/`zext`/`or`) | 2 | 2 |
| — | `entry`, `if.end`, four `unreachable` traps | 6 | 0 |

**A hundred and fifty-three of the 165 blocks are links**, and the table's proved
column is the decomposition: 60 + 9 + 1 + 18 (A, B, B′, C) + 11 (D) + 15 (E) +
14 (G) + 6 (H1) + 2 (H2's `while.body.i.lr.ph` and `if.then281.i`) + 17 (F's
`JsonStage2WalkCall` and `JsonStage2WalkFinal`) = 153, with the one measure arm
(`WalkLink.forInc`) among those classes rather than beside them.  H1's other four
are the four scans' headers, and none is a one-block link: its visit is the counted
round (`walkScanRounds457_of_cell` applying `scanRound_at`,
`JsonStage2WalkRevolutionScanRound`), four segments covering those four blocks, so
the walk's coverage is unchanged and only the discharge differs.  The twelve outside
the links are named below: the five rows still without a link, the three
finalisation blocks discharged as steps, and those four headers.  The blocks that
are not links at all are the seed, `if.end`, the return's two arms (`s2_walk.exit`
and `if.then`) and the four `unreachable` arms.

**The call census, measured.**  The F row's 19 is the number of blocks between the
arms whose instruction list contains an `Instr.call` or `Instr.callVoid`, read off
`stage2Body`'s own block list.  The callee of a value-returning call is the
instruction's *third* field: the first quoted string of `Instr.call "%call14.i"
(Ty.int 32) "s2_value_pos" [...]` is the destination register, and enumerating
calls by the first quoted string instead reports those blocks under a register
name.  Measured that way the body has **25** call-containing blocks: `entry` (11
calls, `s2_init` among them), `if.end` (3 `lifetime.end`), the four `unreachable`
arms, and the 19 class F rows — so the table's 19 is right and an earlier
enumeration of "22 blocks, 16 F rows" undercounted F by three, all of them
`lifetime.end`-only blocks near the body's end (`cleanup474.i`, `s2_walk.exit`,
`if.then`).  Of the 19, **13 write only inside the present frame** (the three
`s2_value_pos` callers, the eight `lifetime`-only blocks, `if.then25.i` and
`if.then425.i`'s `od_scalar_value`, whose three-footprint union is the log's
cursor word, the event stream and the refusal record) and **6 need the frame
widening** — `if.then109.i`, `if.else334.i` and `if.then447.i` through
`s2_after_value`'s `%root_done.i`, `z_arena_reserve.exit` through
`s2_string_body`'s `%xj.i`/`%outn.i`, `if.then19.i` through `num_fast_el1`'s
`%d.i`/`%ei.i`, and `if.end256.i`'s own zero store to `%outn.i`.

The count that mattered was the number of classes, not of blocks.  A, B and B′ are
70 blocks between them and need no memory reasoning at all: none touches memory
and none rebinds a register the invariant carries, so each link is one
`lookupName_cons_ne` per carried register and nothing else.  Two more classes
close the same way once their own small gap is filled — H1's five `LeafBlock`s
need one `add` of a negative literal before the comparison, and H2's two are five
`getelementptr`s and three arithmetic instructions.  Class C's eighteen were the
same bargain at a larger scale: one address the invariant does not bind, one
clause it does not carry, and one lemma.

## What each class needs

**C, the refusal store (18) — proved.**  The shape is `%off1.i.iNN =
getelementptr inbounds i8, ptr %e, i64 8; store i64 <reg>, %off1.i.iNN; br label
%if.then` (fifteen) or `%cleanup474.i` (three).  `WalkInv` has four clauses for the
log's fields and none for the refusal record's, so the store has no `readBytes`
clause to preserve; `WalkLink.refusalStore` therefore takes `%e`'s binding and the
stored value's bound as hypotheses, exactly as class A takes the compared
register's, and the link it builds is `{ C with block := t, eoff := j, refusal :=
true }`.  `eoff_le` is the caller's `j ≤ G.n`; `owned` and `frame` survive by
`walkStaged_write` and `walkFrame_write_inside` at `eoff_inside`; and the six memory clauses survive
because the record is a region of its own — `e_z_sep` and `e_ev_sep` are the
staging's separation read at indices 13/14 and 4/14, and
`walkReadBytes_log_of_eoff_write` and `walkReadBytes_ev_of_eoff_write` turn them
into the six equalities.  Nothing in `WalkInv` was weakened, and nothing was
added: the clause the arm is missing is still missing, and it is now a hypothesis
on the eighteen instances rather than a wall.

**D, the other stores (11) — proved (`JsonStage2WalkStore`).**  Ten shapes, one
each: the hash word at `%z + 24` (`if.then.i.i`, `if.then.i.i50` — six
instructions of `xor`, `mul`, `add` over the mask constants, and the invariant has
no clause for that word); the event stream's byte and its length
(`out_reserve.exit.i.i`, `.i60` — two stores that move `evlen`, and so the carry's
`events`, `evlen_eq` and `evBytes` all three); the container-stack byte at
`%cst.i + idxprom` (`if.end150.i`, `if.end162.i`, `if.end195.i`); the cursor's `k`
field (`if.end207.i`, at `%k11.i`, which is `WalkPtrs`' own address); the arena
cursor (`if.else285.i`, at `%alen`); and the state stack at `cst + sp - 1`
(`if.then330.i`).  None is a class — ten addresses with ten clause preservations
behind them — so the module proves one transfer per shape (a container-stack byte,
the hash word, the event stream's tag-and-length pair, the cursor's `k`, the arena
cursor) and one instance per block.  The addresses the invariant does not bind are
the caller's, as class C takes `%e`'s, and the two cursor moves are the carry's:
`events`/`evlen` for the event stream, `alen`/`spans` for the arena, the latter
with `pending` cleared (the merge that reserves the next record re-establishes
it).

**E, the `phi` run (15) — proved.**
The run reads `s.pre`, which the invariant does not constrain beyond the block it
is at (`denoteCode_phiRun` is the mechanism).  The four `land.rhs*` blocks are the
important ones: each selects the scan's counter and then loads the document byte at
it, so each is where a scan's `%NN` — class A's compared register — is produced, and
each is on the path between a scan header and the comparison that ends the scan.
`if.end372.i`, `while.end.i`, `while.end78.i`, `if.end245.i` and `if.end290.i` are
merges whose incoming values are the previous arm's registers, so their links are
one `PhiSelects` per incoming edge.  `cond.end.i96` is the string scan's entry and
`if.end48.i` the literal comparison's; their links are `JsonStage2WalkEntry`'s,
together with the landing facts that `land.rhs.i.preheader`'s and `if.end67.i`'s
links take as arguments.  The rest of the class is `JsonStage2WalkPhi`: the four
landing blocks are one lemma's instances (`WalkLink.scanLanding`), the pure merges
are `pureCore`/`pureJumpCore` over their `PhiSelects` runs, `for.body.i.i` builds
its `for.inc.i.i` guard from the disjunctive landing fact, and the three store
blocks are hand-rebuilt — `if.end372.i` at the token's end slot (no clause names
 and `if.then57.i`/`while.end78.i` with class C's
`eoff`/`refusal` carry update.  `if.end290.i`'s first `phi` takes `%32` — the
arena reserve's decoded length, loaded from `%outn.i` — as the caller's fact; its
*production* is `s2_string_body`'s write (`s2StringBody_outn_le`), the F datum the
merge's edge reads.

**F, the calls (19; nine proved).**  Every call has to resolve through
`stage2Calls`, and what it leaves is a `CallOutcome`: the
`lifetime.start`/`lifetime.end` markers (twelve and twenty-one of them,
`JsonStage2IR`'s guards) and the two `memset`s are resolved there and leave memory
alone, `@llvm.trap` is the reserve's refusal arm, and `s2_init`, `s2_value_pos`,
`s2_after_value`, `s2_string_body`, `num_fast_el1` and `od_scalar_value` are the
`sub` parameter.  So each of these links is a contract question — the callee's post
at the caller's staging — and `JsonStage2WalkCall` is where the walk's selection is
fixed (`stage2Calls stage2SubCalls`, the selection the six proved contracts are
stated at) and where the step is: `walkDenoteCode_call`/`walkDenoteCode_callVoid`
are the `denoteCode` steps of a call at an arbitrary argument list, and
`walkArgs_*` are the six helpers' argument lists read off the pinned body.

Nine of the nineteen are closed there.  Four are marker blocks
(`cleanup339.critedge.i`, `if.end67.critedge.i`, `if.end473.i`, `cleanup474.i`):
`walkDenoteCode_lifetimeEnd` is the marker's step — the state it was handed — so
each link is a pure run.  Four call a helper through the contract:
`if.then.i` and `if.then219.i` call `s2_value_pos`, whose footprint is empty and
whose memory is the caller's, so their links are `WalkLink.pureCore` at the two
returns; `if.else334.i` and `if.then447.i` call `s2_after_value`, whose model writes
one of two places (`stage2AfterValue_form`), and `walkAfterValue_facts` is the
frame, presence, log and trace at that write.  The depth-zero arm's root slot
(`%root_done.i`, the second `alloca` at `G.next0 + 8`) misses the log and the
stream, and that is now *structural* rather than a hypothesis beside the two
links: `WalkStage.sevenEnd` is the adapter's watermark at the seven appended
objects — every one of them ends at or below the call's cursor, which is the same
clause `Γ_stage2.pre` states for its thirteen — and `WalkStage.rootSlot_log` and
`WalkStage.rootSlot_ev` read it (`%d.i`'s and the stream's entries come from
`WalkGeom.watermark`).  The fact lives in both: `stage2StagedPre` states it at the
seven (the adapter carries the call's `next`), and `WalkStage.sevenEnd` is that
clause at the geometry, transported by `walkStage_at_pre`.

`if.end256.i` is the ninth, and it is the arena's reservation itself: the token's
extent, the marker, the zero store at `%outn.i`, the two log words and the check.
Its run is where class F's step vocabulary gains a literal store
(`walkDenoteCode_store64_imm` — the tree's store steps all take a register) and
where the two log words are read out of the invariant's `log_alen`/`log_acap`
rather than from a caller's fact.  The branch is stated at the bit the run
computed, so it composes with the trap verdict (`walkArenaReserve_clear`, which is
now a theorem of the invariant) instead of assuming it.

What remains is one.  `z_arena_reserve.exit` (the decoded body's prefix in the
arena, which the frame's arena extent at `C.alen` does not yet cover) is the class's
open link.  `if.then19.i` is closed (`WalkLink.if_then19_i`,
`JsonStage2WalkFinal`): `num_fast_el1`'s two output slots are its only writes,
`walkNumFast_facts` turns that into the frame, presence, log and stream facts, and
the branch's bit is the answer's.  `if.then109.i` is closed
(`WalkLink.if_then109_i`, `JsonStage2WalkFinal`): its call's depth is `%sub.i`, so
the facts lemma is stated at the register (`walkAfterValue_facts_at`) and the block
reads the log's zeroed hash word to its `if.end.i.i55` edge.  `if.then425.i` is closed as the carry's
link (`WalkLink.if_then425_i_emit`/`_refuse`, `JsonStage2WalkFinal`): the
contract's post names the appended record, so the emitting arm advances the trace
and the refusing arm leaves the carry where it was.  The two finalisation arms
(`s2_walk.exit`, `if.then`) are steps, not links, for the reason above.

**G, `load` and compare (14; all proved).**  Each reads a word the invariant does not
bind.  `if.end.i.i` and `if.end.i.i55` read `%len` and `%cap` — which `log_len` and
`log_cap` *do* bind, so these two are the closest of the fourteen; the rest read a
container-stack byte at `idxprom` or `sp - 1`, the document byte at `%cond350.i`
(`land.lhs.true357.i`), `%root_done.i`'s alloca (`if.end490.i`), or the document
byte at `%idxprom.i` (`if.end.i97`).  Each instance is `JsonStage2WalkPure`'s: the
block's run written out as a `denoteCode` equality and handed to its edge's
transfer — `pureCore` for a bit the block computes, `pureCoreCarried` for
`if.end74.i`'s carried bit, `pureJumpCore` for the four jump shapes — with the
`getelementptr` at a computed index its own step (`denoteCode_gep8_ofNat`).
The four rows that read a container-stack byte through `sp - 1`
(`if.end179.i`, `land.lhs.true.i`, `if.end133.i`, `if.end59.i`) failed the
kernel's type-checker when their runs were written at the block's literal
instruction list with the outgoing environment duplicated in the hypothesis
types: a deep-recursion error, not a depth limit (`maxRecDepth 50000` does not
help), while the statement alone and each proof term's parts type-check.
Stating the run at the block's *variables* and supplying each block by `rfl` —
`WalkLink.addImmBr`'s device — closes the two five-instruction rows
(`WalkLink.if_end179_i`, `WalkLink.land_lhs_true_i`); the other two are closed by
naming the seven- and eight-cell environment **once** as a parameter
(`env' : Env` with an equation `env' = walkPairEnv …`/`walkSelectEnv …`) so the
statement never contains it twice: `WalkLink.if_end133_i` and
`WalkLink.if_end59_i`.  The measurement that forced that shape: with the
environment written into the two `WalkLocal` hypotheses, the pair's declaration
alone reached 7.8 GB resident under a 6 GB cap (the marker's 1.7 GB).

**H1's five `LeafBlock`s — proved.**  `%.off = add i8 %NN, -9; %SwitchLeafNN =
icmp ule i8 %.off, 1`.  Two instructions and no memory: `walkDenoteCode_add_imm_w`
at a negative constant, then class A's terminator.  The compared byte is the
loaded document byte, which is the same caller-supplied fact class A takes; what
stopped them was that `WalkLink.icmpBr`'s `hinstrs` is a singleton, and
`WalkLink.addImmBr` (`JsonStage2WalkRest`) is the pair's own class lemma.  The five
links are `WalkLink.LeafBlock33`, `…43`, `…64`, `…85` and `…96`.

**H2.**  `while.body.i.lr.ph` binds five `getelementptr`s — `%c.i + 32`,
`%z + 24`, `%t352.i + 20`, `+ 8`, `+ 16` — of which only the first is in
`WalkPtrs`, so its link needs four more fixed addresses (and `%t352.i` itself is
not a `WalkPtrs` register).  The five also fix the *order* of the environment the
link's carrier is read at: each bind prepends, so the run leaves `%kind404.i`
outermost and `%k11.i` oldest, and `preheaderRegs` states the carrier at that
list — `cells`' newest-first order, not the source order of the writes.  The two
orders are not interchangeable: the carrier is about the cells the run holds, and
a list in write order describes an environment the block never produces.  `if.then281.i` is `add i32 %7, 1`, a `zext`, and an
`or` with the top bit set; it needs `%7`'s value, which is `if.then328.i`'s
`%conv286.i.sink`, and it carries `inner` untouched.

**The six that are not links.**  `entry` is the initialisation and its obligation
is `WalkSeedState`, already stated.  `if.end` returns: `walkIfEnd_step`
(`JsonStage2WalkCall`) is its step at either arm's `phi` value, and
`WalkChain.finalisation` composes a chain to `s2_walk.exit` with the exit's jump
(`walkExitBlock_denote`) and that return into a completion, without demanding a
`WalkLink` of either — the exit's stores are the record's, outside the walk's
frame by design.  `if.then`'s refusal copy still owes its three instructions; its
live-range prefix is `walkExitBlock_denote` at the same nine.  The four
`unreachable` blocks are `@llvm.trap` arms: a link
cannot enter one without concluding the run does not complete — `walkTrap_noStep`
(`JsonStage2WalkCall`) is that fact, since `stage2Calls` answers `none` at the trap
— so their obligation is the guard before them — `if.end.i.i`'s and
`if.end.i.i55`'s event reserve, `if.end256.i`'s arena reserve, `if.end290.i`'s
thirteen-byte reserve — never failing.

Three of the four guards are excluded by the invariant plus the loop head's own
guard (`C.k < G.nep`, the strictness `whileBody_step` already takes): the event
cursor is `nev0 + sum(events)`, at most `nev0 + 13·k ≤ nev0 + 13·nep ≤ evcap`, and
`k ≤ nep - 1 ≤ n - 1` leaves twelve bytes of slack at the widest record, so the
`len + 1 > cap` and `len + 13 > cap` tests are clear; `walkEventReserve_clear`
(`JsonStage2WalkRest`) is that arithmetic, stated at the invariant.  The **arena
trap** (`if.end.i83`) is excluded by `walkArenaReserve_clear`
(`JsonStage2WalkCall`), and the exclusion is now a theorem *of the invariant*: the
record in flight is a triple `(p, off, len)`, `pending_at` bounds its offset by the
cursor, `pending_cursor` bounds the cursor by the staging's offset plus `p`, and
`pending_len` places `p + len` inside the document.  The three are the whole of
the check's premises — `alen + len + 64 ≤ dstcap` follows from them and
`G.arenaRoom` — so no hypothesis sits beside the invariant.  The test is
`alen + (entry[k+1] - entry[k] - 1) + 64 > dstcap`, and `len` is exactly that
extent.  The three clauses' **production** is `if.end256.i`: it is the first
block that holds all three components — the entry's position (`%idxprom.i`), the
arena offset reserved (`%alen`'s word, bounded by the carry's cursor through
`logArena_le`) and the token's extent (`%sub260.i`) — so `WalkLink.if_end256_i`
sets `pending` there, and `WalkLink.z_arena_reserve_exit` clears it once the
reserved window has been decoded.  The exclusion is therefore one a traversal supplies at
the reservation rather than a clause every carry leaves empty.  The class of the
finding is in `JsonStage2WalkRest`'s header, with the arithmetic.

## The remainder, named

The census's rows: five blocks still without a link, 153 already closed as links,
four scan headers closed as counted rounds and three (`s2_walk.exit`, `if.then`,
`if.end`) closed as steps — 165 in all.  `class` is the census's;
`what a link needs` is the block's own instance of the class's obstruction, naming
the register or address that is missing, and for a closed row the link that closed
it.

| # | block | class | what a link needs |
|---:|---|---|---|
| 1 | `entry` | seed | the initialisation, 58 instructions |
| 2 | `while.body.i.lr.ph` | H2 | five `gep`s — proved (`WalkLink.while_body_i_lr_ph`) |
| 17 | `if.then.i` | F | calls `@s2_value_pos` — proved (`WalkLink.if_then_i`) |
| 22 | `if.then.i.i` | D | the hash word at `%z + 24` — proved (`WalkLink.if_then_i_i`) |
| 23 | `if.end.i.i` | G | the two log words — proved (`WalkLink.if_end_i_i`) |
| 24 | `if.end.i.i.i` | trap | `@llvm.trap`, `unreachable` |
| 25 | `out_reserve.exit.i.i` | D | the tag byte and the cursor — proved (`WalkLink.out_reserve_exit_i_i`) |
| 28 | `if.end59.i` | G | the type stack's byte — proved (`WalkLink.if_end59_i`) |
| 30 | `if.end74.i` | G | the state stack's byte, carried bit — proved (`WalkLink.if_end74_i`) |
| 37 | `if.then109.i` | F | calls `@s2_after_value` — proved (`WalkLink.if_then109_i`) |
| 38 | `if.then.i.i50` | D | the hash word at `%z + 24` — proved (`WalkLink.if_then_i_i50`) |
| 39 | `if.end.i.i55` | G | the two log words — proved (`WalkLink.if_end_i_i55`) |
| 40 | `if.end.i.i.i64` | trap | `@llvm.trap`, `unreachable` |
| 41 | `out_reserve.exit.i.i60` | D | the tag byte and the cursor — proved (`WalkLink.out_reserve_exit_i_i60`) |
| 44 | `if.end133.i` | G | both stacks' bytes at `sp - 1` — proved (`WalkLink.if_end133_i`) |
| 47 | `if.end150.i` | D | the state stack's byte — proved (`WalkLink.if_end150_i`) |
| 50 | `if.end162.i` | D | the state stack's byte — proved (`WalkLink.if_end162_i`) |
| 53 | `if.end179.i` | G | the type stack's byte — proved (`WalkLink.if_end179_i`) |
| 54 | `lor.lhs.false.i` | G | the state stack's byte — proved (`WalkLink.lor_lhs_false_i`) |
| 56 | `if.end195.i` | D | the state stack's byte — proved (`WalkLink.if_end195_i`) |
| 59 | `if.end207.i` | D | the cursor record's `k` — proved (`WalkLink.if_end207_i`) |
| 61 | `if.then219.i` | F | calls `@s2_value_pos` — proved (`WalkLink.if_then219_i`) |
| 62 | `land.lhs.true.i` | G | the type stack's byte — proved (`WalkLink.land_lhs_true_i`) |
| 63 | `if.then231.i` | G | the state stack's masked byte — proved (`WalkLink.if_then231_i`) |
| 64 | `if.end245.i` | E | the `phi` run `%key.1.i` and the callee's return — proved (`WalkLink.if_end245_i`) |
| 66 | `if.end256.i` | F | the arena check, and the record in flight's entry into the carry — proved (`WalkLink.if_end256_i`) |
| 67 | `if.end.i83` | trap | `@llvm.trap`, `unreachable` |
| 68 | `z_arena_reserve.exit` | F | calls `@s2_string_body` — proved (`WalkLink.z_arena_reserve_exit`), the block's own run with it (`walkZArenaReserveExit_denote`) |
| 71 | `if.then281.i` | H2 | `add`/`zext`/`or` — proved (`WalkLink.if_then281_i`) |
| 72 | `if.else285.i` | D | the log's arena-cursor word at the reserved cursor — proved (`WalkLink.if_else285_i`) |
| 73 | `if.end290.i` | E | the two `phi`s and the thirteen-byte reserve — proved (`WalkLink.if_end290_i`); `%32` is `s2_string_body`'s write, the F datum the edge reads |
| 74 | `if.end.i86` | trap | `@llvm.trap`, `unreachable` |
| 75 | `if.then328.i` | F | the record, the cursor and the log's `len` — proved (`WalkLink.if_then328_i`) |
| 76 | `if.then330.i` | D | the state stack's byte — proved (`WalkLink.if_then330_i`) |
| 77 | `if.else334.i` | F | calls `@s2_after_value` — proved (`WalkLink.if_else334_i`) |
| 78 | `cleanup339.critedge.i` | F | calls `@llvm.lifetime.end.p0` — proved (`WalkLink.cleanup339_critedge_i`) |
| 80 | `cond.true345.i` | G | the stream's next lane — proved (`WalkLink.cond_true345_i`) |
| 81 | `cond.end349.i` | F | the token's position and gap flag — proved (`WalkLink.cond_end349_i`) |
| 82 | `land.lhs.true357.i` | G | the document byte at the bound — proved (`WalkLink.land_lhs_true357_i`) |
| 87 | `LeafBlock33` | H1 | `add` + `icmp` latch — proved (`WalkLink.LeafBlock33`) |
| 89 | `land.rhs.i` | E | the counter `phi` and the document byte — proved (`WalkLink.land_rhs_i`) |
| 94 | `LeafBlock43` | H1 | `add` + `icmp` latch — proved (`WalkLink.LeafBlock43`) |
| 96 | `if.end372.i` | E | the end `phi` and the token's end slot — proved (`WalkLink.if_end372_i`) |
| 106 | `if.then413.i` | F | the kind byte and `@s2_value_pos` — proved (`WalkLink.if_then413_i`) |
| 108 | `if.then425.i` | F | calls `@od_scalar_value` — proved (`WalkLink.if_then425_i_emit`, `WalkLink.if_then425_i_refuse`) |
| 110 | `cond.true.i106` | G | the stream's bound lane — proved (`WalkLink.cond_true_i106`) |
| 111 | `cond.end.i96` | E | the bound `phi` and the entry test — proved (`WalkLink.cond_end_i96`) |
| 112 | `land.rhs.i103` | E | the counter `phi` and the document byte — proved (`WalkLink.land_rhs_i103`) |
| 117 | `LeafBlock64` | H1 | `add` + `icmp` latch — proved (`WalkLink.LeafBlock64`) |
| 119 | `while.end.i` | E | the landing `phi` and the exit test — proved (`WalkLink.while_end_i`) |
| 120 | `if.end.i97` | G | the byte after the scan — proved (`WalkLink.if_end_i97`) |
| 121 | `if.then19.i` | F | calls `@llvm.lifetime.start.p0`, `@num_fast_el1` — proved (`WalkLink.if_then19_i`) |
| 122 | `if.then25.i` | F | the error offset's computed store — proved (`WalkLink.if_then25_i`) |
| 132 | `if.end48.i` | E | the two `phi`s, `min`, and the entry test — proved (`WalkLink.if_end48_i`) |
| 133 | `for.body.i.i` | E | the `phi` run and the `for.inc.i.i` guard — proved (`WalkLink.for_body_i_i`) |
| 136 | `if.then57.i` | E | the `phi`, the `add`, and the refusal store — proved (`WalkLink.if_then57_i`) |
| 137 | `if.end67.critedge.i` | F | calls `@llvm.lifetime.end.p0` — proved (`WalkLink.if_end67_critedge_i`) |
| 139 | `land.rhs71.i` | E | the counter `phi` and the document byte — proved (`WalkLink.land_rhs71_i`) |
| 144 | `LeafBlock85` | H1 | `add` + `icmp` latch — proved (`WalkLink.LeafBlock85`) |
| 146 | `while.end78.i` | E | the landing `phi` and the refusal store — proved (`WalkLink.while_end78_i`) |
| 147 | `if.then447.i` | F | calls `@s2_after_value` — proved (`WalkLink.if_then447_i`) |
| 148 | `land.rhs457.i` | E | the counter `phi` and the document byte — proved (`WalkLink.land_rhs457_i`) |
| 153 | `LeafBlock96` | H1 | `add` + `icmp` latch — proved (`WalkLink.LeafBlock96`) |
| 156 | `if.end473.i` | F | calls `@llvm.lifetime.end.p0` — proved (`WalkLink.if_end473_i`) |
| 157 | `cleanup474.i` | F | calls `@llvm.lifetime.end.p0` — proved (`WalkLink.cleanup474_i`) |
| 158 | `cleanup478.i` | E | the depth and index `phi`s — proved (`WalkLink.cleanup478_i`) |
| 161 | `if.end490.i` | G | the `%root_done.i` slot — proved (`WalkLink.if_end490_i`) |
| 163 | `s2_walk.exit` | F | the terminal step — proved (`walkExitBlock_denote`, `WalkChain.finalisation`) |
| 164 | `if.then` | F | the refusal copy — proved as a step (`walkIfThenBlock_denote`, `walkIfThen_step`) |
| 165 | `if.end` | ret | the return — proved as the terminal step (`walkIfEnd_step`, `WalkChain.finalisation`) |

## Whether the chain closes

The completion is not inhabited: the loop's own pass is not a proof.  It is
*assembled*, though, and the assembly is `JsonStage2WalkTraverse`, which turns the
loop into an induction on the entry index (`walkLoopFinishesThree`) and leaves one
premise, `WalkLoopStepThree` — the revolution or the terminal run at a loop-head
state.  Read as
a proof obligation the completion is four pieces, in order:

1. **the five rows** — `entry` (item 2) and the four `unreachable` arms (whose
   verdicts are proved:
   `walkTrap_noStep`, `walkEventReserve_clear`, `walkArenaReserve_clear`), so the
   traversal has no gap;
2. **the seed** — *landed*: `walkSeedState` (`JsonStage2WalkSeedRun`) is
   `WalkSeedState` at the state the entry run leaves, `walkSeedState_geometry`
   derives its two loads from the staging, and `walkSeedInvariant_geometry` reads
   `WalkInv` at it — the loop head's invariant with nothing assumed beside the
   geometry, the staging and the initial state's own three bindings.  The *prefix* half of this item is `walkSeedPrefix_runFuel`: the
   entry block, the preheader and the header's first pass composed into one
   `runFuel` equality from the entry state to the loop head, which is
   `walkCompletes_of_prefix_chain`'s `hprefix` at the blocks whose steps are
   proved here;
3. **the return** — *stated and composed*: `walkIfEnd_step` is `if.end`'s step at
   either arm's `phi` value, `walkExitBlock_denote` and `walkIfThenBlock_denote`
   are the two arms' copies (with `walkIfThen_step` the refusal arm's jump), and
   `WalkChain.finalisation` turns a chain to either arm plus those steps into the
   completion.  Nothing of the return remains open; and
4. **the count** — *closed as arithmetic* (`JsonStage2WalkTraverse`):
   `walkCompletes_of_loop_budget` reads the completion at `32 * nep + 8 * n + 32`
   — the record's two counted terms and the finalisation allowance — from a
   *potential* `walkPotential`, `32` per unconsumed entry plus `8` per document
   byte not yet reached, rather than from the measure.  The revolution's premise is
   `p + walkPotential C' ≤ walkPotential C`, which `walkPotential_spend` reads as the
   price inside the credit consumed — `p ≤ 32·Δk + 8·ΔA` — the 22-and-six readings
   of *The budget, counted* being that premise; the credit is the entry stream's
   own span, so the byte-dependent scans inside an entry are paid by the bytes the
   entry spans.  The
   measure's `(nep - k) * (4 * n + 6)` is a *termination* radix, not a count:
   `walkIterations_le_measure` is its only use in this direction, and at a hundred
   entries and a hundred bytes it is 40,600 against the record's 4,032
   (`walkMeasure_exceeds_budget_at_100`) — so spending the measure against the
   budget would not have been a proof of anything.

`WalkLoopStepThree`'s two branches are therefore the one premise the completion still
owes: the left is the revolution — the dispatch's pass from `NodeBlock21` to
`cleanup478.i` (the census's class links), the back edge (`walkBack_step`), the
header's pass (`whileBody_step`) and the two `phi` runs — with its price, and the
right is the exit: the test's false edge and the tail through `s2_walk.exit` to
`if.end`'s return, inside `F ≤ 27` (the finalisation allowance less the seed's
three steps and the return's one).  Both are stated at `WalkInv` and admit nothing
beside it.

Two of the non-link rows cannot be links under the record's post as it stands.
`if.then`'s refusal copy stores the three report words (`%ndst`, `%nev`, `%err`)
that the record's post proves *itself*, from `err_not_in_walkFrame` and the
wrapper's `frameSlots`; a walk frame that covered them would make `errAccept`
unprovable, so the copy is the terminal step.  The walk's frame is a *prefix* of
the record's (`walkFrame_reportFrame_coverage` maps `(dst, alen)` into
`(dst, alen + 64)`), so widening the walk's frame widens the record's, and
`err_not_in_walkFrame` places the refusal slot outside it.  That is a decision
about `stage2Boundary`, for the record that owns it.

`z_arena_reserve.exit` is not that case, and it is a link
(`WalkLink.z_arena_reserve_exit`, with the block's own run beside it at
`walkZArenaReserveExit_denote` in `JsonStage2WalkCall`): the
block writes nothing of its own — one
load (`%31 = load ptr, ptr %ar`), two `gep`s, the `s2_string_body` call and a jump
— and the callee's writes are the cursor word, `%outn.i`'s word, a `len`-wide
window at the arena offset, and the error record.  The window's start is the word
`if.end256.i` loaded, which `logArena_le` bounds by the carried cursor, so a link
that *reserves* the window in the carry — `alen + ext`, the extent appended to
`spans` at the cursor — places the write inside `walkWide`'s arena entry; `spans_end`
and the relaxed `log_alen` are what keep `alen_le_sum`, and the later
`if.else285.i`, consistent with that reservation.  The call's own composition is
the link's hypotheses: `s2_string_body`'s answer is one `stage2StringBody` result,
so the frame and the presence are read off `s2StringBody_framed` at
`s2StringBodyFoot`, and the caller presents the log's and the event stream's
readbacks beside them — the same shape the `if.then425.i` and `if.then328.i`
links take.

The two rows that had a *contract* gap instead are links: `s2ScalarValuePost`
carries a second conjunct naming the record an emitting arm appended
(`s2ScalarValueAppend` at an `EventRecord`), so `if.then425.i`'s carry advances
from the call's own post, and `if.then328.i` writes its thirteen bytes and moves
the log's `%len` word directly.  Both read the log's buffer-pointer word at `%z`,
which the invariant binds as `C.stage`'s own object rather than as one of the four
fields at `%z + 8` on.

`JsonStage2WalkRest` supplies H1's five `LeafBlock` links (its class lemma reads the
`add`'s literal at the instruction's own width) and `if.then281.i`, and states the
three transfers the rest of the pure classes share: `WalkLink.pureCore` (a run that
binds no carried register and whose edge is a carried or computed bit),
`WalkLink.pureJumpCore` and `WalkLink.pureCoreCarried`.  What remains absent, with
the reason in each row, is five of the nineteen call blocks
(`JsonStage2WalkCall` closes the other fourteen); classes D, E and G are
`JsonStage2WalkStore`, `JsonStage2WalkPhi` and `JsonStage2WalkPure`, the last
proved for all fourteen of its rows, four of them stated through a named outgoing
environment because the kernel recursion its header records blocks the doubled
statement.

The scan entries are links, and the measure is what made them.  `for.body.i.i` is
reached from `if.end48.i` as well as from `for.inc.i.i`, and its landing fact is the
disjunction `ScanLanded ∨ (the phi's zero)` (`WalkLocal` and the four `land.rhs*`
landing facts are disjunctive for the same reason — their preheaders are second
predecessors).  The entry disjunct reads `C.inner`, so an entry edge that *reset* it
to the new scan's remaining work would raise the measure whenever a later scan has
more work than the earlier one left.  The measure's inner component is therefore the
iteration's **shared budget** (`walkInnerCap G = 4 * n + 5`, `JsonStage2WalkEntry`),
an entry edge leaves it where it is and shows only that the budget covers the scan
it enters, and the refill at the loop head is paid for by the outer factor.  Under
that measure `if.end48.i` and `cond.end.i96`, and the two landed links whose landing
fact was an argument (`land.rhs.i.preheader`, `if.end67.i`), are links; the escape
scan's entry (`if.then447.i`) is a call block and stays F's.  The landing blocks'
own `phi` runs and the rest of E's merges are `JsonStage2WalkPhi`'s, and what is
left below is the calls' contract gap.

The arena guard's remaining need and F's gap are the same kind of statement.  Each
of the nineteen call blocks needs its callee's `CallOutcome` at the caller's
staging; `stage2Calls` resolves the lifetime markers and `@llvm.trap` and leaves
`s2_init`, `s2_value_pos`, `s2_after_value`, `s2_string_body`, `num_fast_el1` and
`od_scalar_value` to the `sub` parameter, so a call block's link is a contract
question.  The blocks that read a returned word (`if.end256.i` reads
`%call272.i`'s successors, `if.then328.i` reads `%outn.i`) need the callee's frame
as well as its post, and `z_arena_reserve.exit` needs the arena's reservation to
be the cursor's — the same datum `pending_cursor` reads.  No link in this module is
proved against a `CallOutcome` that the `sub` parameter's contract does not state,
which is why F is reported as a contract gap rather than closed here.

The step count is likewise not established, but the two numbers it is compared
against now are, and the comparison itself is arithmetic.  `WalkChain.steps` reads
a chain as a run, and a chain with 16 of its links missing has no step count to
compare against `stage2Budget`.  What the budget's arithmetic needs is one link per
block the dispatch traverses, and *The budget, counted* below takes that path off
the pinned AST: the dispatch's longest path is 22 blocks against
`stage2EntryAllowance` 32, and the widest scan step is six blocks against
`stage2ByteAllowance` 8.  `JsonStage2WalkTraverse` turns that into the comparison
`p + walkPotential C' ≤ walkPotential C` and the induction that spends it
(`walkLoopFinishesThree`), so what remains open is the revolution's price — that the
pass, the back edge and the header's pass cost what the potential's fall allows —
and not the count against the budget.

**The register carriers, and what is still open.**  `JsonStage2WalkSeed` now
states the two predicates the traversal's successor hypotheses need: `WalkRegs`,
the 24 static addresses bound by `entry`/`while.body.i.lr.ph` and never rebound,
and `WalkIter`, `%7`, `%8` and `%arrayidx10.i` at
`entryPos G C.k`/`entryByte G C.k`/`G.b + entryPos G C.k`.  Their
preservation lemmas are `WalkRegs.of_run` and `WalkIter.of_run`, both by
`denoteCode_lookupName` and nothing else.  `walkCompletes_of_prefix_chain` states
the assembly — the seed's prefix run, the dispatch chain, the chain's step count,
the return, and the budget comparison — as five named premises, with no `sorry`
and no claim of the obligation; its count, its induction and its potential are
`JsonStage2WalkTraverse`'s (`walkLoopFinishesThree`, `walkCompletes_of_loop_budget`).

The census's carriers, with their costs named:

* the two register carriers **are** `WalkInv` fields, and their production is
  stated: the static carrier by the seed's bindings and the per-iteration
  registers by `whileBody_step`'s own three binds;
* the container stacks' bytes read at `ctype/cst + (C.sp - 1)` are carried as a
  map at a written mark, not as a per-depth byte: the byte at a popped depth was
  written at an earlier index.  `WalkCarry` carries `wlen` and the two maps,
  `WalkInv` carries the two `WalkStackBytes` clauses and their bounds, and the
  conversions are `if.end24_step` (`walkStack_ifEnd24_at`), the class-D stores
  (`WalkStackBytes.storeAt`), the two `s2_after_value` links
  (`walkAfterValueMapAt`), and `WalkStackBytes.write_outside` at every link that
  writes a staged object, the cursor record, `%d.i` or an alloca;
* the seed's entry run is stated in four segments and only partly proved.  The
  block's own list is `walkEntryInstrs` and `JsonStage2WalkRun` cuts it into
  four segments, pinned to the block by `walkEntryInstrs_segments` (an `rfl`).
  Three `denoteCode` equalities are proved at a symbolic environment and state
  (`walkEntrySeg1_denote`, `walkEntrySeg3_denote`, `walkEntrySeg4_denote`); the
  second — the initialisation, the `S2` record's fields, the log's memset and
  stores, and the two cursor loads — is cut into its two halves
  (`walkEntrySeg2a`/`walkEntrySeg2b`, pinned by `walkEntrySeg2_split`) and its
  twenty-two instructions after the initialisation are pinned as
  `walkEntrySeg2Post` (`walkEntrySeg2_cut`), and its equality is **not**
  proved.  Its read obstruction is discharged: its store runs are the lists
  `walkSeg2Ws1`/`Ws2`/`Ws3`, `readBytes_stage2WriteStores_of_all_outside` reads a
  list rather than a window, and `seg2StoreOutside` carries each entry across the
  record's and the log's extents, so the two cursor loads are taken at the
  incoming memory *before* any step runs.  What remains is the shape of each
  step's own conclusion: `stateAt env {s with mem := …}` repeats the previous
  state literal in four fields, so the accumulated term grows four-fold per store
  and the closing `rfl` is a defeq check over that growth — the direct chain,
  reads consumed first, times out at `whnf` at `maxHeartbeats 4000000` after two
  minutes, and restating the run as eleven flats between explicit states still
  times out inside the two-step runs at the default budget.  The vocabulary that
  avoids it is a step lemma stated with a memory-only updater over `State` rather
  than a structure literal; it is a change to `BlockEval`'s step set and is
  recorded here rather than worked around.  The three reads back out of the `S2`
  record (`%3`, `%4`, `%5`) are `readBytes_s2Init_of_outside`'s inside case,
  which it does not state, and which the third segment's composition needs.  The
  composition of the segments into the block's `runFuel` prefix is therefore also
  still open, and the five open rows stay open until it is produced.-/

/-- **A comparison**, at a state rather than at a builder and at arbitrary operands:
the step `denoteCode_icmp_eq_imm_w` is its `eq`-with-literal case, and the
dispatch's binary search uses `slt`, `ult`, `ule` and `eq` over both registers and
literals indifferently. -/
theorem walkDenoteCode_icmp {calls : Calls} (env : Env) (s : State) (d : String)
    (w : Nat) (p : IPred) {oa ob : Operand} {x y : BitVec w}
    (ha : evalOperand (stateAt env s) oa = some (.int w x))
    (hb : evalOperand (stateAt env s) ob = some (.int w y)) (is : List Instr) :
    denoteCode calls (.icmp d p w oa ob :: is) (stateAt env s) =
      denoteCode calls is (stateAt ((d, .int 1 (evalICmp p x y)) :: env) s) := by
  rw [denoteCode_cons_of _ _ _ _ _ (by
    rw [LeanLLVM.Refinement.JsonS1MasksIR.evalInstr_icmp (s := stateAt env s) ha hb])]
  simp only [stateAt, State.bind]

/-- **A `condbr` on a one-bit register** takes the edge its bit names.  `execTerm`
answers `ub` on a bit that is neither zero nor one, and a `BitVec 1` has no third
value, so the edge is total. -/
theorem walkExecTerm_condbr {s : State} {d tl fl : String} {bit : BitVec 1}
    (hd : lookupName s.env d = some (.int 1 bit)) :
    execTerm s (Term.condbr (.reg d) tl fl) =
      .jump { s with pc := (if bit = 1 then tl else fl), pre := some s.pc } := by
  simp only [execTerm, evalOperand, hd]
  rcases bitVec1_eq_zero_or_one bit with h | h
  · rw [h]; simp
  · rw [h]; simp

/-- **Class A: one comparison and a branch.**  The block reads two operands at one
width, binds the one-bit result and branches on it.  Nothing else in the
environment moves, so the six pointer registers, the entry index and the depth
register survive a `lookupName_cons_ne` each, the memory is untouched, and the
measure does not move because the block advances neither the entry index nor the
inner work.

The operands are the caller's: `%8` is the document byte `while.body.i` loaded,
`%sp.i.0248` is the depth the invariant carries, and `%35`, `%ee.0.i238` and their
siblings are a scan's counters.  What the block *does* with the answer is the edge
it takes, which is why the target block is the bit's own value.

The block-local clause is taken at the two edges rather than at the test, because
the test is a `BitVec` comparison the lemma cannot decide: a caller with a literal
target discharges each by `simp [WalkLocal]`. -/
theorem WalkLink.icmpBr {calls : Calls} {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G)
    (s : State) (hInv : WalkInv G C s)
    {B : Block} (hfind : stage2Body.findBlock C.block = some B)
    {d tl fl : String} {p : IPred} {w : Nat} {oa ob : Operand} {x y : BitVec w}
    (hinstrs : B.instrs = [Instr.icmp d p w oa ob])
    (hterm : B.term = Term.condbr (.reg d) tl fl)
    (ha : evalOperand s oa = some (.int w x)) (hb : evalOperand s ob = some (.int w y))
    (hk : d ≠ "%k.0.i249") (hsp : d ≠ "%sp.i.0248")
    (h3 : d ≠ "%3") (h5 : d ≠ "%5") (hkk : d ≠ "%k11.i")
    (hc : d ≠ "%ctype.i") (hs : d ≠ "%cst.i") (hh : d ≠ "%hash1.i.i")
    (hS : walkFreshName d) (hI7 : d ≠ "%7") (hI8 : d ≠ "%8")
    (hl : WalkLocal { C with block := tl }
      { stateAt ((d, .int 1 (evalICmp p x y)) :: s.env) s with pc := tl, pre := some s.pc })
    (hf : WalkLocal { C with block := fl }
      { stateAt ((d, .int 1 (evalICmp p x y)) :: s.env) s with
        pc := fl, pre := some s.pc }) :
    ∃ s', WalkLink calls G C s
      { C with block := (if evalICmp p x y = 1 then tl else fl) } s' := by
  have hpc : s.pc = C.block := hInv.pc_eq
  have hden : denoteCode calls B.instrs s =
      some (stateAt ((d, .int 1 (evalICmp p x y)) :: s.env) s) := by
    rw [hinstrs, ← stateAt_self s]
    exact walkDenoteCode_icmp (calls := calls) s.env s d w p ha hb []
  let s' : State :=
    { stateAt ((d, .int 1 (evalICmp p x y)) :: s.env) s with pc := (if evalICmp p x y = 1 then tl else fl), pre := some s.pc }
  have hstep : LeanLLVM.step calls stage2Body s = Ctrl.jump s' := by
    simp only [LeanLLVM.step, hpc, hfind, hden, hterm]
    exact walkExecTerm_condbr (d := d) (tl := tl) (fl := fl)
      (bit := evalICmp p x y) (by simp only [stateAt, lookupName_cons_self])
  refine ⟨s', ⟨hInv, hstep, ?_, ?_, rfl⟩⟩
  · have hnm : B.name = C.block := findBlockList_name hfind
    have hle := walkEmitC_condbr_le (findBlockList_mem hfind) hterm
    have hph : walkEmitC C.block ≤
        walkEmitC (if evalICmp p x y = 1 then tl else fl) := by
      rw [← hnm]
      by_cases hbit : evalICmp p x y = 1
      · rw [if_pos hbit]; exact hle.1
      · rw [if_neg hbit]; exact hle.2
    refine
      { pc_eq := rfl
        blockIndex := ?_
        k_le := hInv.k_le
        events_le := by
          dsimp only
          have h := hInv.events_le
          omega
        events_nep := hInv.events_nep
        evlen_eq := hInv.evlen_eq
        evBytes := ?_
        alen_le_sum := hInv.alen_le_sum
        alen_ge := hInv.alen_ge
        spans_order := hInv.spans_order
        spans_end := hInv.spans_end
        spans_inside := hInv.spans_inside
        pending_at := hInv.pending_at
        pending_cursor := hInv.pending_cursor
        pending_len := hInv.pending_len
        eoff_le := hInv.eoff_le
        inner_cap := hInv.inner_cap
        depth_cap := hInv.depth_cap
        depth_reg := ?_
        ptrs := ?_
        sp_le_wlen := hInv.sp_le_wlen
        wlen_cap := hInv.wlen_cap
        tyBytes := hInv.tyBytes
        stBytes := hInv.stBytes
        regs := ?_
        iter := ?_
        log_hash := hInv.log_hash
        log_len := hInv.log_len
        log_cap := hInv.log_cap
        log_alen := hInv.log_alen
        log_acap := hInv.log_acap
        log_base := hInv.log_base
        log_dst := hInv.log_dst
        owned := hInv.owned
        root_slot := hInv.root_slot
        next_ge := hInv.next_ge
        frame := hInv.frame
        inc_reg := by
          dsimp only [s', stateAt]
          rw [lookupName_cons_ne _ _ hS.2.1]
          exact hInv.inc_reg
        idx_reg := by
          dsimp only [s', stateAt]
          rw [lookupName_cons_ne (k := d) (n := "%idxprom.i") _ _ hS.2.2.2]
          exact hInv.idx_reg
        blockLocal := ?_ }
    · dsimp only [s', stateAt]
      rw [lookupName_cons_ne _ _ hk]
      exact hInv.blockIndex
    · dsimp only [s', stateAt]
      exact hInv.evBytes
    · dsimp only [s', stateAt]
      rw [lookupName_cons_ne _ _ hsp]
      exact hInv.depth_reg
    · dsimp only [s', stateAt]
      exact hInv.ptrs.bind h3 h5 hkk hc hs hh
    · dsimp only [s', stateAt]
      exact hInv.regs.bind hS.1
    · dsimp only [s', stateAt]
      exact hInv.iter.bind (v := .int 1 (evalICmp p x y)) ⟨hI7, hI8, hS.2.2.1⟩
    · dsimp only [s']
      by_cases ht : evalICmp p x y = 1
      · rw [ite_eq_left ht]; exact hl
      · rw [ite_eq_right ht]; exact hf
  · rfl

/-! ### Class C: the refusal store

Eighteen blocks of the dispatch write the refusal record's offset and leave for
the refusal's exit: `%off1.i.iNN = getelementptr inbounds i8, ptr %e, i64 8;
store i64 <reg>, %off1.i.iNN; br label %if.then` — fifteen of them to `if.then`
and three to `cleanup474.i`.  The stored register is the block's own: thirteen
store `%idxprom.i`, four store `%4`, and one stores `%q.0.i246`.

What the invariant gives is everything except the offset's own bound.  The store's
address is fixed by the staging (`C.stage.e + 8`), so the only register fact the
block needs is `%e`'s binding — which `WalkPtrs` does not carry, exactly as it does
not carry `%8`.  The values stored are entry positions and the document's length,
so `eoff_le` follows from the caller's `≤ G.n`; nothing in `WalkInv` produces it,
which is the clause the refusal arm is missing. -/

/-- The refusal record's `%e + 8` field is inside its staged extent. -/
theorem eoff_inside {c ctype cst tok s z e k : Nat} (hk : k < 8) :
    inRegions (stage2StagedWrites c ctype cst tok s z e) (e + 8 + k) :=
  ⟨(e, stage2ErrorExtent), by simp [stage2StagedWrites], by omega,
    by simp [stage2ErrorExtent]; omega⟩

/-- The refusal record and the log are separate regions of the staging. -/
theorem e_z_sep {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {s : State}
    (_h : WalkInv G C s) :
    C.stage.e + stage2ErrorExtent ≤ C.stage.z ∨
      C.stage.z + stage2LogExtent ≤ C.stage.e := by
  have hpair : (stage2WalkRegions G.b G.n G.ep G.nep G.xp G.nxp G.dst G.ndst0 G.ev
      G.evcap G.ndst G.nev G.err C.stage.c C.stage.ctype C.stage.cst C.stage.tok
      C.stage.s C.stage.z C.stage.e).Pairwise
      (fun r q => r.1 + r.2 ≤ q.1 ∨ q.1 + q.2 ≤ r.1) := by
    have hsep := C.stage.separate
    unfold DisjointRegions at hsep
    rw [stage2StagedRegions] at hsep
    exact (List.pairwise_append.mp hsep).1
  have hlen : (stage2WalkRegions G.b G.n G.ep G.nep G.xp G.nxp G.dst G.ndst0 G.ev
      G.evcap G.ndst G.nev G.err C.stage.c C.stage.ctype C.stage.cst C.stage.tok
      C.stage.s C.stage.z C.stage.e).length = 15 := by
    simp [stage2WalkRegions, stage2Regions, stage2StagedWrites]
  have h' := List.pairwise_iff_getElem.mp hpair 13 14 (by omega) (by omega) (by omega)
  simpa [stage2WalkRegions, stage2Regions, stage2StagedWrites] using h'.symm

/-- The refusal record and the event stream are separate regions of the
staging. -/
theorem e_ev_sep {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {s : State}
    (_h : WalkInv G C s) :
    C.stage.e + stage2ErrorExtent ≤ G.ev ∨ G.ev + G.evcap ≤ C.stage.e := by
  have hpair : (stage2WalkRegions G.b G.n G.ep G.nep G.xp G.nxp G.dst G.ndst0 G.ev
      G.evcap G.ndst G.nev G.err C.stage.c C.stage.ctype C.stage.cst C.stage.tok
      C.stage.s C.stage.z C.stage.e).Pairwise
      (fun r q => r.1 + r.2 ≤ q.1 ∨ q.1 + q.2 ≤ r.1) := by
    have hsep := C.stage.separate
    unfold DisjointRegions at hsep
    rw [stage2StagedRegions] at hsep
    exact (List.pairwise_append.mp hsep).1
  have hlen : (stage2WalkRegions G.b G.n G.ep G.nep G.xp G.nxp G.dst G.ndst0 G.ev
      G.evcap G.ndst G.nev G.err C.stage.c C.stage.ctype C.stage.cst C.stage.tok
      C.stage.s C.stage.z C.stage.e).length = 15 := by
    simp [stage2WalkRegions, stage2Regions, stage2StagedWrites]
  have h' := List.pairwise_iff_getElem.mp hpair 4 14 (by omega) (by omega) (by omega)
  simpa [stage2WalkRegions, stage2Regions, stage2StagedWrites] using h'.symm

/-- **A write to the refusal's offset leaves the log alone.**  Every log field is
an `off` and a width inside the log's extent, and the record is a separate region,
so the eight bytes at `%e + 8` miss it. -/
theorem walkReadBytes_log_of_eoff_write {m : Mem} {e z off j N : Nat}
    (hez : e + stage2ErrorExtent ≤ z ∨ z + stage2LogExtent ≤ e)
    (hoff : off + N ≤ stage2LogExtent) :
    readBytes (writeBytes m (e + 8) (wordBytes 8 j)) (z + off) N = readBytes m (z + off) N := by
  refine walkReadBytes_writeBytes_outside (start := e + 8) (addr := z + off) (n := N) ?_
  have hw : (wordBytes 8 j).length = 8 := by simp [wordBytes, natToBytes_length]
  rcases hez with hez | hez
  · refine Or.inr ?_
    have h1 := hez
    simp only [stage2ErrorExtent] at h1
    rw [hw]; omega
  · refine Or.inl ?_
    have h1 := hez
    simp only [stage2LogExtent] at h1
    omega

/-- **A write to the refusal's offset leaves the log's base word alone.**
`walkReadBytes_log_of_eoff_write` at offset zero. -/
theorem walkReadBytes_log_base_of_eoff_write {m : Mem} {e z j : Nat}
    (hez : e + stage2ErrorExtent ≤ z ∨ z + stage2LogExtent ≤ e) :
    readBytes (writeBytes m (e + 8) (wordBytes 8 j)) z 8 = readBytes m z 8 := by
  simpa using walkReadBytes_log_of_eoff_write (m := m) (e := e) (z := z) (off := 0) (j := j)
    (N := 8) hez (by decide)

/-- **A write to the refusal's offset leaves the event stream alone.** -/
theorem walkReadBytes_ev_of_eoff_write {m : Mem} {e ev evcap nev0 j N : Nat}
    (hev : e + stage2ErrorExtent ≤ ev ∨ ev + evcap ≤ e) (hN : nev0 + N ≤ evcap) :
    readBytes (writeBytes m (e + 8) (wordBytes 8 j)) (ev + nev0) N =
      readBytes m (ev + nev0) N := by
  refine walkReadBytes_writeBytes_outside (start := e + 8) (addr := ev + nev0) (n := N) ?_
  have hw : (wordBytes 8 j).length = 8 := by simp [wordBytes, natToBytes_length]
  rcases hev with hev | hev
  · refine Or.inr ?_
    have h1 := hev
    simp only [stage2ErrorExtent] at h1
    rw [hw]; omega
  · refine Or.inl ?_
    omega

/-- An `i8` `getelementptr` at a literal offset. -/
theorem walkEvalInstr_gep8_imm (calls : Calls) (s : State) (d base : String)
    (a c : Nat) (hb : lookupName s.env base = some (.ptr a)) (hc : c < 2 ^ 63) :
    evalInstr calls s (.gep d (.int 8) (.reg base) (.imm (.int 64 (BitVec.ofNat 64 c)))) =
      some (s.bind d (.ptr (a + c))) := by
  have hs := sExt_ofNat64 hc
  have hpos : (BitVec.ofNat 64 c).toNat < 2 ^ 63 := by
    rw [walkToNat_ofNat64 (by omega)]; exact hc
  have hmod : c % 2 ^ 64 = c := Nat.mod_eq_of_lt (by omega)
  simp only [evalInstr, evalOperand, Const.toValue, hb, hs,
    show (8 + 7) / 8 = 1 from rfl, Ty.sizeBytes]
  rw [ite_eq_left hc]
  simp

/-- A `getelementptr i8` at a literal offset, in the chain's shape. -/
theorem walkDenoteCode_gep8_imm {calls : Calls} (s : State) (d base : String)
    {a c : Nat} (hb : lookupName s.env base = some (.ptr a)) (hc : c < 2 ^ 63)
    (is : List Instr) :
    denoteCode calls
        (.gep d (.int 8) (.reg base) (.imm (.int 64 (BitVec.ofNat 64 c))) :: is) s =
      denoteCode calls is (s.bind d (.ptr (a + c))) :=
  denoteCode_cons_of _ _ _ _ _ (walkEvalInstr_gep8_imm calls s d base a c hb hc)

/-- A register read that succeeds names a cell bound to the value it returned.
`evalOperand` refuses a cell holding the marker, so a read of `some v` also says
the cell's value is not `poison`: this is the converse of `evalOperand_reg_of`,
and the way a read at a later environment recovers the binding.  It replaces the
`simpa only [evalOperand]` bridge that held while `evalOperand` was a lookup. -/
theorem lookupName_of_evalOperand_reg {s : State} {n : String} {v : Value}
    (h : evalOperand s (.reg n) = some v) : lookupName s.env n = some v := by
  cases hlk : lookupName s.env n with
  | none =>
      simp only [evalOperand, hlk] at h
      exact h
  | some w =>
      simp only [evalOperand, hlk] at h
      cases w with
      | poison => simp at h
      | int a b => simpa using h
      | ptr a => simpa using h
      | vec a b c => simpa using h
      | float a => simpa using h

/-- Close a read against the binding that holds it, in whichever direction the
goal names: a binding from a read, a read from a binding, or the read itself
when both sides already agree.  One name for the three shapes a
`simpa only [evalOperand]` site carried while `evalOperand` read a cell directly;
a read and a binding are no longer the same term, so the direction is said here
rather than at every site. -/
macro "walk_read" "using" h:term : tactic => `(tactic|
  (first
   | exact lookupName_of_evalOperand_reg $h
   | exact LeanLLVM.evalOperand_reg_of $h
   | simpa only [evalOperand] using $h))

/-- **Class C: the refusal store.**  One `getelementptr` at `%e + 8`, one
eight-byte store, and the edge to the refusal's exit.  The memory clauses that
survive are the ones whose addresses lie outside those eight bytes; `e_z_sep` and
`e_ev_sep` are what say so, and `frame` survives by `eoff_inside`. -/
theorem WalkLink.refusalStore {calls : Calls} {m0 : Mem} (G : WalkGeom m0)
    (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    {B : Block} (hfind : stage2Body.findBlock C.block = some B)
    {d v t : String} {j : Nat}
    (hinstrs : B.instrs =
      [Instr.gep d (.int 8) (.reg "%e") (.imm (.int 64 (BitVec.ofNat 64 8))),
       Instr.store (.int 64) (.reg v) (.reg d)])
    (hterm : B.term = Term.br t)
    (he : lookupName s.env "%e" = some (.ptr C.stage.e))
    (hv : evalOperand s (.reg v) = some (.int 64 (BitVec.ofNat 64 j)))
    (hj : j ≤ G.n) (hj64 : j < 2 ^ 64)
    (hvd : d ≠ v)
    (hd : d ≠ "%k.0.i249") (hds : d ≠ "%sp.i.0248")
    (h3 : d ≠ "%3") (h5 : d ≠ "%5") (hkk : d ≠ "%k11.i")
    (hc : d ≠ "%ctype.i") (hs : d ≠ "%cst.i") (hh : d ≠ "%hash1.i.i")
    (hS : walkFreshName d) (hI7 : d ≠ "%7") (hI8 : d ≠ "%8")
    (hloc : WalkLocal { C with block := t, eoff := j, refusal := true }
      { stateAt ((d, .ptr (C.stage.e + 8)) :: s.env)
          { s with mem := writeBytes s.mem (C.stage.e + 8) (wordBytes 8 j) } with
        pc := t, pre := some s.pc })
    (hne : C.block ≠ "while.body.i") :
    ∃ s', WalkLink calls G C s { C with block := t, eoff := j, refusal := true } s' := by
  have hpc : s.pc = C.block := hInv.pc_eq
  let m' : Mem := writeBytes s.mem (C.stage.e + 8) (wordBytes 8 j)
  let s' : State :=
    { stateAt ((d, .ptr (C.stage.e + 8)) :: s.env) { s with mem := m' } with pc := t, pre := some s.pc }
  have hden : denoteCode calls B.instrs s =
      some (stateAt ((d, .ptr (C.stage.e + 8)) :: s.env) { s with mem := m' }) := by
    rw [hinstrs,
      walkDenoteCode_gep8_imm (calls := calls) s d "%e" he (by decide)
        [Instr.store (.int 64) (.reg v) (.reg d)]]
    exact denoteCode_store64_ofNat (calls := calls)
      (env := (d, .ptr (C.stage.e + 8)) :: s.env) s v d
      (by rw [lookupName_cons_ne _ _ hvd]; exact lookupName_of_evalOperand_reg hv) hj64
      (lookupName_cons_self d (.ptr (C.stage.e + 8)) s.env) []
  have hfind' : stage2Body.findBlock s.pc = some B := by rw [hpc]; exact hfind
  have hstep : LeanLLVM.step calls stage2Body s = Ctrl.jump s' := by
    simp only [LeanLLVM.step, hfind', hden, hterm, execTerm]
    dsimp only [s', m', stateAt]
  have hnm : B.name = C.block := findBlockList_name hfind
  have hph : walkEmitC C.block ≤ walkEmitC t := by
    rw [← hnm]
    exact walkEmitC_br_le (findBlockList_mem hfind) (by rw [hnm]; exact hne) hterm
  refine ⟨s', ⟨hInv, hstep, ?_, ?_, rfl⟩⟩
  · refine
      { pc_eq := rfl
        blockIndex := ?_
        k_le := hInv.k_le
        events_le := by
          dsimp only
          have h := hInv.events_le
          omega
        events_nep := hInv.events_nep
        evlen_eq := hInv.evlen_eq
        evBytes := ?_
        alen_le_sum := hInv.alen_le_sum
        alen_ge := hInv.alen_ge
        spans_order := hInv.spans_order
        spans_end := hInv.spans_end
        spans_inside := hInv.spans_inside
        pending_at := hInv.pending_at
        pending_cursor := hInv.pending_cursor
        pending_len := hInv.pending_len
        eoff_le := hj
        inner_cap := hInv.inner_cap
        depth_cap := hInv.depth_cap
        depth_reg := ?_
        sp_le_wlen := hInv.sp_le_wlen
        wlen_cap := hInv.wlen_cap
        tyBytes := hInv.tyBytes.write_outside (by
          have hw : (wordBytes 8 j).length = 8 := by simp [wordBytes, natToBytes_length]
          have hx : stage2ErrorExtent = 24 := rfl
          rcases (stack_e_sep hInv).1 with h' | h'
          · exact Or.inr (by omega)
          · exact Or.inl (by omega))
        stBytes := hInv.stBytes.write_outside (by
          have hw : (wordBytes 8 j).length = 8 := by simp [wordBytes, natToBytes_length]
          have hx : stage2ErrorExtent = 24 := rfl
          rcases (stack_e_sep hInv).2 with h' | h'
          · exact Or.inr (by omega)
          · exact Or.inl (by omega))
        ptrs := ?_
        regs := ?_
        iter := ?_
        log_hash := ?_
        log_len := ?_
        log_cap := ?_
        log_alen := ?_
        log_acap := ?_
        log_base := ?_
        log_dst := ?_
        owned := by dsimp only [s', stateAt, m']; exact walkStaged_write rfl hInv.owned
        root_slot := by
          dsimp only [s', stateAt, m']
          exact hasBytes_writeBytes hInv.root_slot
        next_ge := hInv.next_ge
        frame := ?_
        inc_reg := by
          dsimp only [s', stateAt, m']
          rw [lookupName_cons_ne _ _ hS.2.1]
          exact hInv.inc_reg
        idx_reg := by
          dsimp only [s', stateAt, m']
          rw [lookupName_cons_ne (k := d) (n := "%idxprom.i") _ _ hS.2.2.2]
          exact hInv.idx_reg
        blockLocal := hloc }
    · dsimp only [s', stateAt, m']
      rw [lookupName_cons_ne _ _ hd]
      exact hInv.blockIndex
    · have hlen : (C.events.map EventRecord.encodedBytes).flatten.length =
          (C.events.map EventRecord.encodedSize).sum := by
        simp only [List.length_flatten, List.map_map]; rfl
      have hsum := EventRecord.sum_encodedSize_le C.events
      simp only [stage2RecordBytes] at hsum
      have hroom := G.evRoom
      simp only [stage2RecordBytes] at hroom
      have hN : G.nev0 + (C.events.map EventRecord.encodedBytes).flatten.length ≤ G.evcap := by
        have h1 : C.events.length ≤ G.nep := hInv.events_nep
        have h3 := G.nep_le
        rw [hlen]; omega
      dsimp only [s', stateAt, m']
      rw [walkReadBytes_ev_of_eoff_write (e := C.stage.e) (ev := G.ev) (evcap := G.evcap)
        (nev0 := G.nev0) (j := j) (N := _) (e_ev_sep hInv) hN]
      exact hInv.evBytes
    · dsimp only [s', stateAt, m']
      rw [lookupName_cons_ne _ _ hds]
      exact hInv.depth_reg
    · dsimp only [s', stateAt, m']
      exact hInv.ptrs.bind h3 h5 hkk hc hs hh
    · dsimp only [s', stateAt, m']
      exact hInv.regs.bind hS.1
    · dsimp only [s', stateAt, m']
      exact hInv.iter.bind (v := .ptr (C.stage.e + 8)) ⟨hI7, hI8, hS.2.2.1⟩
    · dsimp only [s', stateAt, m']
      rw [walkReadBytes_log_of_eoff_write (e := C.stage.e) (z := C.stage.z) (off := 32)
        (j := j) (N := 4) (e_z_sep hInv) (by decide)]
      exact hInv.log_hash
    · dsimp only [s', stateAt, m']
      rw [walkReadBytes_log_of_eoff_write (e := C.stage.e) (z := C.stage.z) (off := 8)
        (j := j) (N := 8) (e_z_sep hInv) (by decide)]
      exact hInv.log_len
    · dsimp only [s', stateAt, m']
      rw [walkReadBytes_log_of_eoff_write (e := C.stage.e) (z := C.stage.z) (off := 16)
        (j := j) (N := 8) (e_z_sep hInv) (by decide)]
      exact hInv.log_cap
    · dsimp only [s', stateAt, m']
      rw [walkReadBytes_log_of_eoff_write (e := C.stage.e) (z := C.stage.z) (off := 48)
        (j := j) (N := 8) (e_z_sep hInv) (by decide)]
      exact hInv.log_alen
    · dsimp only [s', stateAt, m']
      rw [walkReadBytes_log_of_eoff_write (e := C.stage.e) (z := C.stage.z) (off := 56)
        (j := j) (N := 8) (e_z_sep hInv) (by decide)]
      exact hInv.log_acap
    · dsimp only [s', stateAt, m']
      rw [walkReadBytes_log_base_of_eoff_write (e := C.stage.e) (z := C.stage.z)
        (j := j) (e_z_sep hInv)]
      exact hInv.log_base
    · dsimp only [s', stateAt, m']
      rw [walkReadBytes_log_of_eoff_write (e := C.stage.e) (z := C.stage.z) (off := 40)
        (j := j) (N := 8) (e_z_sep hInv) (by decide)]
      exact hInv.log_dst
    · dsimp only [s', stateAt, m']
      refine walkFrame_write_inside hInv.frame ?_
      intro k hk
      have hw : (wordBytes 8 j).length = 8 := by simp [wordBytes, natToBytes_length]
      exact walkWideAt_of_seven
        (eoff_inside (c := C.stage.c) (ctype := C.stage.ctype) (cst := C.stage.cst)
          (tok := C.stage.tok) (s := C.stage.s) (z := C.stage.z) (e := C.stage.e)
          (k := k) (by omega))
  · rfl

end LeanLLVM.Refinement
