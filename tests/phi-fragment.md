# `phi`

`phi` selects one incoming value per predecessor block, at entry to the block, by
the block the edge came from.  The model knows that block: `State` carries a
predecessor field, a jump writes it with the block it is leaving, and a `phi`
reads it.  A `phi` whose incoming list has no entry for the actual predecessor is
`ub`; so is a `phi` in a block with no predecessor at all, which is the same
undefinedness for a different reason.  A predecessor label listed twice is
refused at the parser, and so is a register name bound twice.

The checks drive the parser, the printer and the semantics in process; the
differential compiles the same two `.ll` files with `clang` and compares its
answers with the model's.  No compiler is reached by the `lean` checks, and the
differential reaches nothing but `clang` and the built model.

    nix develop -c lake env lean tests/phi-fragment.lean
    nix develop -c bash tests/phi-differential.sh

The four paths and what each is for:

| path | role |
|---|---|
| `tests/phi-fragment.lean` | the focused checks: the `#guard` assertions this record describes (P1–P6) |
| `tests/phi-differential.sh` | the differential: builds and runs the two fixtures with `clang`, compares with the model, prints the predictions and `RESULT` |
| `tests/phi-model.lean` | the model-side runner the differential calls: parses each fixture and prints the model's answers; asserts nothing itself, and fails only on an unreadable or unparsable fixture |
| `tests/phi/` | the two fixtures, `loop.ll` and `three.ll`, read by both the runner and the compiler |

P1–P4 are the semantics' behaviour, P5 the non-interference instance, P6 the
parser's refusals.

### P1 — edge timing decides the value

- **Actor:** the semantics.
- **Given:** the loop `%i = phi i32 [ 0, %entry ], [ %j, %body ]` at the head of
  a counting loop, with `%j` bound to `4`.
- **When:** the instruction is executed from a state whose predecessor is
  `entry`, and again from one whose predecessor is `body` — the same
  instruction, the same registers, the same memory.
- **Then:** the first binds `%i` to `0` and the second to `4`, and the whole
  program returns `3`.
- **Why:** a semantics that fixed the first incoming entry would answer `0`
  twice; one that fixed the last would answer `4` twice; one that ignored edge
  timing could not return `3` for the loop.  The pair is what makes the wrong
  readings *visibly wrong* rather than merely unproved.
- **Not claimed:** that every well-typed `phi` is exercised; that an incoming
  label that is not a predecessor of the block is refused (it is not — an entry
  naming a block that never jumps there is simply never selected).

### P2 — three predecessors

- **Actor:** the semantics.
- **Given:** one program whose `join` is reached from `entry`, `a` or `b`, with
  `%p = phi i32 [ 10, %entry ], [ 20, %a ], [ 30, %b ]`.
- **When:** it is run with `argc` 1, 2 and 3, which take the three edges.
- **Then:** it returns `10`, `20` and `30` respectively; `argc` 4 takes the
  third edge again and returns `30`.
- **Why:** three different answers from one instruction exclude a selector that
  reads a fixed position.  The fourth run shows the third answer belongs to the
  third edge.
- **Not claimed:** anything about an incoming list longer than the block's
  predecessors, beyond the `ub` of P4.

### P3 — an entry-block `phi`

- **Actor:** the semantics.
- **Given:** `%p = phi i32 [ 7, %entry ]` in the entry block.
- **When:** the program is parsed and run.
- **Then:** it parses (the parser is not a verifier) and the run is `ub`,
  because `initState` leaves the predecessor `none` and no incoming entry can
  name `none`.
- **Why:** the entry block has no predecessor, so there is nothing to select by.
  The module is one LLVM's verifier refuses; `ub` is the conservative reading,
  and it cannot admit a behaviour LLVM forbids.
- **Not claimed:** that the parser rejects dominance problems elsewhere.

### P4 — a missing predecessor is `ub`

- **Actor:** the semantics.
- **Given:** `%p = phi i32 [ 1, %a ]` at a `join` reached from both `a` and `b`.
- **When:** the program is run with the condition that takes each edge.
- **Then:** the run through `a` returns `1`, and the run through `b` is `ub`.
- **Why:** the same program, the same instruction, two edges, two different
  results.  The `ub` is reached at run time because the module itself is one a
  verifier refuses; that is why the second answer is not a refusal at parse
  time.
- **Not claimed:** that a program reaching this `ub` in practice would have been
  accepted by an LLVM verifier.

### P5 — non-interference, exercised

- **Actor:** the model.
- **Given:** a program with a back edge (`head` branches to itself), a branch and
  no `phi`; it carries its counter in memory, so it loops without a `phi`.
- **When:** it is run from `initState` and from `initState` with the predecessor
  set to `some "head"` (and to `none`), at the same budget.
- **Then:** the two runs return the same outcome, and that outcome is `3` — the
  value the loop reaches after three back edges, so the two runs are an outcome
  and not two `none`s, and the field is written on the path taken.
- **Why:** the field exists for `phi`, and the claim "additive" is a theorem
  (`runFuel_init_setPre`) not an assertion.  The instance here goes through
  jumps, so it exercises the one transition that writes the field.
- **Not claimed:** that a `phi`-free program's *memory* is unchanged in any
  finer sense than the outcome being equal.

### P6 — the parser's refusals, and their control

- **Actor:** the parser.
- **Given:** a `phi` of `void`; a `phi i8` whose incoming register is an `i32`;
  a `phi` after another instruction in its block; an entry written without its
  comma; an empty incoming list; a `phi` that lists one predecessor twice; a
  register name bound twice in one function; and a definition that reuses a
  parameter's name.
- **When:** each is parsed.
- **Then:** each is refused with a message naming what was refused (`void`; both
  types; that a `phi` must be first; the entry's shape; the duplicated label; the
  repeated register name; the parameter it shadows), and, in the same run, the
  controls parse: a correctly written one-entry `phi`, a two-entry `phi` on
  *distinct* labels, one definition of a name, and two distinct names in one
  block — so each check is shown to be about the thing it refuses and not about
  its shape.
- **Why:** a refusal that does not name the construct is not actionable, and an
  absence claim needs its affirmative control in the same run.
- **The asymmetry, and why it is not an oversight:** a duplicate label is refused
  because first-match would give a *defined* meaning to a module LLVM's verifier
  rejects — narrowing what the model permits below what the text says — while a
  label naming no real predecessor is accepted, because selecting nothing is
  `ub`, which widens the model's permitted behaviours instead.  The duplicate
  check is local to the incoming list and needs no environment; checking labels
  against the block list would make the parser a verifier for a dominance fact it
  does not otherwise police.
- **The duplicate-name refusal, and why it is the same check in another costume:**
  the semantics binds a later definition over an earlier one (`State.bind`
  prepends, `lookupName` reads the head) while the `phi` type check reads the
  first definition in program order, so a function that bound a name twice would
  get a defined meaning from the two readings disagreeing.  Refusing the repeat is
  what keeps them in step; the check is over the function's own definition list
  and needs no environment.
- **Not claimed:** that labels are compared with the function's block list (they
  are not), or that a `phi` whose incoming list is longer than the block's
  predecessor set is refused, or that a use-before-definition is refused (the
  semantics makes an unbound register `ub`, and the parser does not order the
  bindings).

## The differential observation

`tests/phi-differential.sh` builds `tests/phi/loop.ll` and `tests/phi/three.ll`
with `clang`, runs them (`three` at four different `argc` values, so all three
edges are exercised), and compares the exit codes with the model's answers over
the same files.  The transcript records both sides and ends `RESULT: PASS` only
when every comparison held.

The comparison is an observation: two programs, one compiler version, one host.
It does not establish that the model and the compiler agree in general, and it
is not a substitute for the theorems.

**What the wrong readings would have printed**, so the pass is agreement where
disagreement was possible rather than agreement by construction.  Each follows
from the fixtures: the loop's guard is `%i < 3`, `%i`'s entry-edge value is `0`,
its back-edge value is `%j = %i + 1`, and `%j` is bound only by `body`.

| reading | `loop` | `three` (argc 1–4) |
|---|---|---|
| edge timing (the model, and `clang`) | `3` | `10 20 30 30` |
| first incoming entry always | `ub` — `%i` stays `0`, the guard never fails, the run never returns | `10 10 10 10` |
| last incoming entry always | `ub` — `%j` is read before `body` has bound it, so the first step is undefined | `30 30 30 30` |

Every wrong reading differs from the observed answer on both programs, and the
three-predecessor program differs on every one of its four runs.

## What the new field moved, line by line

Adding a predecessor to `State` changes no statement.  It does change proof
terms that spell out an expected state, because such a term must now spell out
the new field; this is the list a reader can check item by item.

| where | what changed |
|---|---|
| `Frames.State.AgreesOutside` | the relation gains `s.pre = t.pre` (the one *definition* that moved, so that a relation named "agrees" is not silent about a field `phi` reads); `agreesOutside_refl` gains the matching `rfl`. No consumer exists, so no theorem elsewhere moved. |
| `Vellum/CommaMaskIR.baseline_step_entry` | the expected `.jump` state gains `pre := some "bb"` (the block it leaves). |
| `Vellum/CommaMaskLoop.entryStateMemAt` | the expected state at `cond` gains `pre := some "entry"`; `entry_inv_at`'s two scratch states gain `pre := none`. |
| `Vellum/CommaMaskLoop.cond_step`, `body_step`, `cond_done_step` | the expected jump states `s3`/`s12` gain `pre := some <the block the jump leaves>`; each step proof closes with `hpc` for the `pc` premise the field now exposes. |
| `Vellum/SeamContext.envForBody`, `Vellum/JsonSeam.envForBodySym` | the run's initial record literal gains `pre := none` (a callee starts at its entry block, which has no predecessor). |
| `Vellum/ModuleRefinement` | the run literals in that file and `memCaller_step`'s expected `.ret` state gain `pre := none`. |
| `Vellum/JsonSeam` | the run literals in that file and `scanCaller_step_of_call`'s expected `.ret` state gain `pre := none`. |
| `Vellum/JsonScanLane.structBitStart` | the table's starting state gains `pre := none`. |
| `ITree/LoopInstance` | three hand-built jump states gain `pre := some <source>.pc`. |
| `tests/getelementptr.lean` | three scratch states gain `pre := none`. |

Every change in that table is a field added to a term whose other fields are
unchanged, `pre := none` where the state is an initial or scratch state and
`pre := some <label>` where the term is the result of a jump.  No theorem's
statement, no definition's exported meaning beyond `State` and
`State.AgreesOutside`, and no proof hypothesis moved.
