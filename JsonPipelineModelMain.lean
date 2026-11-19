/-
`leanllvm-json-pipeline-model`: the pipeline's model, run at the route's own
arguments and projected the way the record's post reads them.

The proved body is `LeanLLVM.Refinement.JsonPipelineIR.pipelineBody`, parsed
from `probes/install/ir/json-pipeline.candidate.ll` and pinned to the literal
beside it.  This program runs that body with the repository's semantics —
`runFuel` at `pipelineCalls tab base` with the stage-2 selection
`WalkScope.envForStage2Work tab stage2SubCalls`, from `EntryState` at
`routeArgs l doc` and `stagedMem l doc` — and prints the caller-visible
projection: the verdict word, the four cursor slots, the refusal word, the
arena's used prefix and the event stream.

The projection is not a second decoder.  `routeResult` is the caller-visible
projection of `JsonCallRoute.routePost`; the words it names are read at the
route's own buffers, the two payloads at the extents the post names
(`routePost_outputs`), and the assembled bytes are read back through
`JsonCallRoute.decodeRouteCall`, whose correctness on an adapter-shaped record
is `decodeRouteCall_bytes`.  A run whose shape the projection does not fit is a
loud failure, never a plausible row.

What this program is *for* is the differential in
`probes/json/route/model-differential.sh`: the same document goes to the native
route (the shim's call of `leanllvm_json_pipeline`) and to this model, and the
two printed projections are required to agree.  The model's document decision
is the library's `documentDecision`; a document it does not admit is reported
as outside the differential's domain rather than compared.

`--body <file>` runs a body parsed from another IR fixture instead of the
pinned one.  It exists for the differential's control: a temporary copy of the
fixture with one constant changed must project differently, which is what shows
the comparison can go red.

Usage:

  leanllvm-json-pipeline-model --doc <file> [--body <ir>]

Exit status: 0 when a row was printed (admitted or outside the domain), 1 on a
usage error, 2 when an input cannot be read, 3 when the model run itself fails
(the run does not return, the fuel is exhausted, or the projection does not
fit).
-/
import LeanLLVM.JsonCallRoute
import LeanLLVM.Refinement.JsonStage2Body
import LeanLLVM.Refinement.JsonStage2WalkFlushPost

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

open LeanLLVM
open LeanLLVM.Refinement
open LeanLLVM.Refinement.JsonPipelineIR

namespace JsonPipelineModel

/-! ### The staged layout -/

/-- The staged layout for a document of `n` bytes.  The addresses are not the
native route's — the model's memory is an association list, not a buffer — but
the object's shape is: the window with its three prefix bytes and its read-past
tail, the 8 KiB POS8 table, the sixteen caller objects at the record's
capacities, and the stage-2 work space above the table.  The stride keeps every
region separate for a document of any length the route admits. -/
def layoutFor (n : Nat) : RouteLayout :=
  let blocks := (n + 63) / 64
  let stride := 16 * n + 65536
  let addrAt (k : Nat) : Nat := 1048576 + k * stride
  { base := 1048576
    tab := addrAt 1
    sc := addrAt 2
    mkSlot := addrAt 3
    entw := addrAt 4
    ep := addrAt 5
    nk := addrAt 6
    xp := addrAt 7
    nxp := addrAt 8
    xcarry := addrAt 9
    dst := addrAt 10
    ndst := addrAt 11
    ev := addrAt 12
    nev := addrAt 13
    err := addrAt 14
    epcap := 64 * blocks + 9
    xpcap := 64 * blocks + 8
    dstcap := n + 64
    evcap := 13 * n + 128
    arm := 0
    nxp0 := 0
    ndst0 := 0
    nev0 := 0 }

/-- The escape-list guard's fact, over the document's bytes: no byte is `0x5C`
and no byte is at or below `0x1F`, so the stage-1 list is empty on every block
and the arm word's bit 1 may be cleared.  This is the predicate
`escape_guard.h` implements natively and the route takes its arm from. -/
def escapeCanSkip (doc : List UInt8) : Bool :=
  doc.all fun b => b != 0x5C && 0x1F < b.toNat

/-- The route's arm word: bit 1 selects the escape list, and the guard clears it
exactly where the list it would build is empty. -/
def armWord (doc : List UInt8) : Nat :=
  if escapeCanSkip doc then 0 else 2

/-- The layout with the arm the document's guard fact selects. -/
def routeLayout (doc : List UInt8) : RouteLayout :=
  { layoutFor doc.length with arm := armWord doc }

/-- The allocator cursor the run starts at: above every staged object, so an
`alloca` in a callee lands in fresh memory rather than in a staged region. -/
def nextCursor (l : RouteLayout) : Nat := l.err + 65536

/-! ### The projection -/

/-- The caller-visible outcome: the verdict, the four cursor words, the refusal
word, and the two payloads at the extents the post names. -/
structure ModelRow where
  verdict : Nat
  nk : Nat
  nxp : Nat
  ndst : Nat
  nev : Nat
  err : Nat
  arena : List UInt8
  events : List UInt8
deriving Repr, DecidableEq

/-- The record the adapter would have returned, assembled from the run's own
memory.  Its header's first four words are the adapter's failure words and are
zero: a returning run is an observation, and the differential compares the
observable fields the post names. -/
def modelCall (r : RouteResult) (err : Nat)
    (arena events : List UInt8) : RouteCall :=
  { tag := 0, detail := 0, want := 0, got := 0
    verdict := r.verdict
    nk := bytesToNat r.nkWord
    nxp := bytesToNat r.nxpWord
    ndst := bytesToNat r.ndstWord
    nev := bytesToNat r.nevWord
    err := err
    arena := arena
    events := events }

/-- The post's caller-visible projection, read off the run's returned memory.
`routeResult` gives the verdict and the four slot words; the payloads are read
at the extents those words name; the assembled record is then decoded by
`decodeRouteCall`, the reader `decodeRouteCall_bytes` is about.  Every failure
is named, with the field that did not fit. -/
def projectModel (l : RouteLayout) (args : List Value) (o : Outcome) :
    Except String ModelRow :=
  match o with
  | .ub => .error "the model run returned .ub"
  | .ret _ m =>
      match routeResult args o with
      | none =>
          .error "the run's outcome is not the ABI's 64-bit return the post projects"
      | some r =>
          let ndst := bytesToNat r.ndstWord
          let nev := bytesToNat r.nevWord
          match readBytes m l.dst ndst, readBytes m l.ev nev, readBytes m l.err 8 with
          | some arena, some events, some errBytes =>
              let c := modelCall r (bytesToNat errBytes) arena events
              match decodeRouteCall c.bytes with
              | none =>
                  .error "the adapter-shaped record does not decode at its own extents"
              | some view =>
                  if view.verdict = r.verdict && view.ndstUsed = ndst &&
                      view.nev = nev && view.arena = arena && view.events = events then
                    .ok
                      { verdict := r.verdict
                        nk := bytesToNat r.nkWord
                        nxp := bytesToNat r.nxpWord
                        ndst := ndst
                        nev := nev
                        err := bytesToNat errBytes
                        arena := arena
                        events := events }
                  else
                    .error "the record reader did not recover the projection's fields"
          | _, _, _ =>
              .error "a payload the post names is not readable at the run's extent"

/-! ### Running the body -/

/-- One model run: the document decision, and — for an admitted document — the
body's outcome and its projection. -/
inductive Result where
  | refused
  | fallback
  | admitted (row : ModelRow)
  | failed (message : String)

/-- Run `body` at the route's arguments for `doc`, under the call environment
the assembled pipeline's record is stated at: `pipelineCalls` at the staged
table and the document's base, with the stage-2 slot at the workspace selection
the pipeline's own theorem uses. -/
def runModel (body : Function) (doc : List UInt8) : Result :=
  match documentDecision doc with
  | .refused _ => .refused
  | .fallback _ => .fallback
  | .admitted =>
      let l := routeLayout doc
      let args := routeArgs l doc
      let mem := stagedMem l doc
      let next := nextCursor l
      let calls :=
        (pipelineCalls l.tab l.base (WalkScope.envForStage2Work l.tab stage2SubCalls) :
          Calls)
      match runFuel calls (pipelineBudget args mem) body (EntryState body args mem next) with
      | none =>
          .failed s!"the run did not return inside the record's budget \
            ({pipelineBudget args mem} control steps)"
      | some o =>
          match projectModel l args o with
          | .ok row => .admitted row
          | .error message => .failed message

/-! ### Printing -/

/-- One payload line: the label, then two lowercase hex digits per byte.  The
native route's `payloadLine` prints the same form, so the two rows compare
byte for byte. -/
def payloadLine (label : String) (bs : List UInt8) : String :=
  let digits := bs.flatMap fun b =>
    let s := Nat.toDigits 16 b.toNat
    if s.length == 1 then ['0', s.headD '0'] else s
  label ++ "=" ++ String.ofList digits

/-- The observation line, in the native route's pinned form. -/
def observationLine (row : ModelRow) : String :=
  s!"verdict={row.verdict} nk={row.nk} nxp={row.nxp} ndst={row.ndst} \
nev={row.nev} err={row.err}"

/-- The decision line, printed before the observation so a row the model does
not answer is named rather than silently skipped. -/
def decisionLine : Result → String
  | .refused => "decision=refused"
  | .fallback => "decision=fallback"
  | .admitted _ => "decision=admitted"
  | .failed _ => "decision=failed"

/-! ### The command line -/

structure Options where
  doc : Option String := none
  body : Option String := none

def usage : String :=
  "usage: leanllvm-json-pipeline-model --doc <file> [--body <ir fixture>]"

def parseArgsAux : Options → List String → Except String Options
  | o, [] => .ok o
  | o, "--doc" :: file :: rest => parseArgsAux { o with doc := some file } rest
  | _, ["--doc"] => .error "missing file after --doc"
  | o, "--body" :: file :: rest => parseArgsAux { o with body := some file } rest
  | _, ["--body"] => .error "missing file after --body"
  | _, arg :: _ => .error s!"unknown argument '{arg}'"

def parseArgs (args : List String) : Except String Options :=
  parseArgsAux {} args

/-- The body a run uses: the pinned AST, or the first function of an IR fixture
the caller names.  A fixture that does not parse is a failure, not a fallback
to the pinned body. -/
def resolveBody (opts : Options) : IO (Except String Function) := do
  match opts.body with
  | none => return .ok pipelineBody
  | some path =>
      try
        let text ← IO.FS.readFile path
        match JsonPipelineIR.firstFunction text with
        | some f => return .ok f
        | none => return .error s!"'{path}' does not parse to a function"
      catch e =>
        return .error s!"cannot read '{path}': {e}"

def main (args : List String) : IO UInt32 := do
  match parseArgs args with
  | .error e =>
      IO.eprintln s!"leanllvm-json-pipeline-model: {e}"
      IO.eprintln usage
      return 1
  | .ok opts =>
      match opts.doc with
      | none =>
          IO.eprintln "leanllvm-json-pipeline-model: --doc is required"
          IO.eprintln usage
          return 1
      | some path =>
          let bytes ←
            try
              IO.FS.readBinFile path
            catch e =>
              IO.eprintln s!"leanllvm-json-pipeline-model: cannot read '{path}': {e}"
              return 2
          let doc := bytes.toList
          match ← resolveBody opts with
          | .error message =>
              IO.eprintln s!"leanllvm-json-pipeline-model: {message}"
              return 2
          | .ok body =>
              match runModel body doc with
              | .failed message =>
                  IO.eprintln s!"leanllvm-json-pipeline-model: {message}"
                  return 3
              | .admitted row =>
                  IO.println (decisionLine (.admitted row))
                  IO.println (observationLine row)
                  IO.println (payloadLine "arena" row.arena)
                  IO.println (payloadLine "events" row.events)
                  return 0
              | result =>
                  IO.println (decisionLine result)
                  return 0

end JsonPipelineModel

def main (args : List String) : IO UInt32 := JsonPipelineModel.main args
