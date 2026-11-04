/-
The JSON parser's scaling instrument.

It measures one thing: how the parser's cost grows with the document, on binary
objects built from that revision's own sources.  A timed region is one
repetition, and it contains the file read and the parse:

    t0 ← monoNanosNow ; bytes ← IO.FS.readBinFile path ;
    let r := parseDocument limits bytes ; t1 ← monoNanosNow

so the input arrives as a runtime read that no two revisions can share and the
parse cannot be folded out of the repetition — a pure call over a loop-invariant
buffer is hoisted, and a region that stays flat while the wall clock grows is
measuring nothing.  The parse's token count is folded into `acc`, so a discarded
or partly evaluated parse shows up as a different `acc` rather than as a fast
time.

Three modes, all on the documents in `probes/bench/json/`:

    leanllvm-json-bench <file> <reps>     one row: median and every repetition
    leanllvm-json-bench --floor <file>     the same region on the cheapest document
    leanllvm-json-bench --digest <dir>     `repr` of every parse in a directory

`--floor` is the calibration: it is the read plus the minimal parse, and a floor
that is a large share of a size's median means the harness is being measured, not
the parser.  `--digest` is the cross-revision check: two binaries' digests must be
identical before their timings are compared, because otherwise they did different
work.

`probes/bench/json-bench.sh` runs the rows for one binary; comparing revisions is
two builds of this same source, each against its own oleans.
-/
import LeanLLVM.JSON.Parse

open LeanLLVM.JSON

/-- The limits a scaling run uses: large enough that a limit is not the subject, so
the parse is. -/
def benchLimits : Limits :=
  { maxInput := 1 <<< 26, maxDepth := 512, maxTokens := 1 <<< 26 }

/-- Read a document inside the timed region and parse it, per repetition, so the
timed call cannot be folded away; the input arrives as a runtime read both
binaries share.  Reports every repetition and the median. -/
def timed (path : String) (reps : Nat) : IO Unit := do
  let size ← (← IO.FS.readBinFile path).size |> pure
  let mut times : Array Nat := #[]
  let mut acc : Nat := 0
  let mut okCount : Nat := 0
  for _ in List.range reps do
    let t0 ← IO.monoNanosNow
    let bytes ← IO.FS.readBinFile path
    let r := parseDocument benchLimits bytes
    let t1 ← IO.monoNanosNow
    times := times.push (t1 - t0)
    match r with
    | .ok tape => acc := acc + tape.tokens.length; okCount := okCount + 1
    | .error _ => acc := acc + 1
  let sorted := times.qsort (· < ·)
  let med := if sorted.isEmpty then 0 else sorted[sorted.size / 2]!
  let perByte := if size == 0 then 0.0 else med.toFloat / size.toFloat
  IO.println s!"path={path} size={size} reps={reps} ok={okCount} acc={acc} median_ns={med} ns_per_byte={perByte} times_ns={times.toList}"

/-- Floor calibration: the cheapest valid document at a size, read and parsed the
same way.  Its time is the I/O plus minimal-parse floor the family time sits on;
a floor that is a large share of a family time means the harness, not the parser,
is being measured. -/
def floor (path : String) : IO Unit := do
  let size ← (← IO.FS.readBinFile path).size |> pure
  let reps := 5
  let mut times : Array Nat := #[]
  let mut acc : Nat := 0
  for _ in List.range reps do
    let t0 ← IO.monoNanosNow
    let bytes ← IO.FS.readBinFile path
    let r := parseDocument benchLimits bytes
    let t1 ← IO.monoNanosNow
    times := times.push (t1 - t0)
    match r with
    | .ok tape => acc := acc + tape.tokens.length
    | .error _ => acc := acc + 1
  let sorted := times.qsort (· < ·)
  let med := sorted[sorted.size / 2]!
  let perByte := if size == 0 then 0.0 else med.toFloat / size.toFloat
  IO.println s!"floor path={path} size={size} reps={reps} acc={acc} median_ns={med} ns_per_byte={perByte} times_ns={times.toList}"

/-- Print the parse result for every corpus document so two revisions' binaries
can be diffed; identical output is the check that they are timing the same work. -/
def digest (dir : String) : IO Unit := do
  let entries ← System.FilePath.readDir dir
  let files := (entries.filter (fun e => e.path.extension == some "json")).map (·.path)
  let files := files.qsort (fun a b => a.toString < b.toString)
  for f in files do
    let bytes ← IO.FS.readBinFile f
    let r := parseDocument benchLimits bytes
    IO.println s!"{f.fileName}\t{repr r}"

def main (args : List String) : IO Unit := do
  match args with
  | ["--digest", dir] => digest dir
  | ["--floor", path] => floor path
  | [path, repsStr] => timed path repsStr.toNat!
  | _ => IO.eprintln "usage: leanllvm-json-bench <file> <reps> | --floor <file> | --digest <dir>"
