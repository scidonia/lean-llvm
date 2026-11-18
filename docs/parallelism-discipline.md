# Parallelism in this repository, and how to get more of it

**Date:** 2026-11-18. **State:** `bd21ce2`, default target green at 2096 jobs.

## The constraint, and why it is real

One compilation at a time is not a preference: two concurrent Lean elaborations crashed this host twice. The lock (`probes/install/lake-locked.sh`) serialises source-elaboration writers, and a timing measurement must not overlap with any elaboration. Those are the only two hard rules.

## What can be parallel, today

| kind of work | can it overlap a Lean build? | notes |
|---|---|---|
| reading, `grep`, surveys, doc edits, ledger updates, scenario text | **yes, always** | no elaboration, no effect on a build |
| C/native builds, drivers, benchmarks | **yes, but not during a timing run** | a C build does not elaborate; a timing run must be on an idle machine |
| editing **disjoint import cones** | **yes, with one compiler at a time** | the discipline below |
| two Lean elaborations at once | **no** | crashed the host twice |

## The discipline that makes editing parallel possible

1. **Slice by import cone, not by file.** Before launching a worker, compute its cone from the import graph and require that no other worker's cone shares a module. `JsonStage2WalkPremisesOfStaging` imports every bundle, so most pairs share it — that is the serialisation point to respect.
2. **One compiler, one queue.** Every compilation goes through the lock. A worker checks `pgrep -af 'lake build'` and yields if a build is running; it does not assume the machine is idle because it was idle a moment ago.
3. **Hand off by patch, not by tree.** A stopped round saves its patch, so a stopped round costs only elapsed time and the next owner continues from it.
4. **No duplicate of a resuming worker.** A worker that resumes must announce itself and yield to the current owner. Three duplicate rounds this session came from that omission.

## The immediate application

The remaining work splits into disjoint cones:

| cone | files | status |
|---|---|---|
| A — the fraction's entry and the guarded join | `JsonStage2NumFastTaken`, `NumFastJoin` | landed |
| B — tier-1's tie and tier-3's copy loop/fold | `JsonStage2NumFastTier1`, `NumFastTier3` | running |
| C — the native route's artifact and benchmark work | `probes/`, `tests/` (no Lean edits) | independent |

A and C, or B and C, can run in parallel because their files are disjoint and C does not elaborate Lean. A and B must not run together, because `JsonStage2NumFast*` is one cone and shares modules.

## The other lever: build parallelism inside one target

`lake build -jN` can elaborate independent modules in parallel. That is a build-config change, not a source change, and it needs a memory-budget test on this host (30 GB, 8 cores) before it is adopted: elaboration is mostly single-threaded per file, so the win is across independent modules, not within a file.

## Bottom line

Parallelism is **not out of reach**: it is constrained to read-only work, disjoint-cone editing with one compiler at a time, and C/native work that does not overlap a timing run. The mechanism is the cone computation and the lock, not a general increase in workers.
