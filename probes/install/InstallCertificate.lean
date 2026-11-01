/-
The installation certificate producer.

`probes/install/build.sh` and `probes/install/select.sh` elaborate this module
with

  CERT_UNIT=<baseline|candidate|loop> CERT_MANIFEST=<absolute manifest path> \
    CERT_OUT=<absolute output path> lake env lean probes/install/InstallCertificate.lean

from the repository root, after re-elaborating `LeanLLVM/Vellum/CommaMaskIR.lean`
from source and, for the loop unit, `LeanLLVM/Vellum/CommaMaskLoop.lean` too.
The module imports those freshly built proof modules, checks the statement and
axiom footprint of the theorem that covers the requested unit, and writes one
canonical certificate to `CERT_OUT`:

  schema unit unit_object_sha256 unit_fixture_sha256 unit_marker_sha256
  baseline_object_sha256 candidate_object_sha256 baseline_fixture_sha256
  candidate_fixture_sha256 baseline_marker_sha256 candidate_marker_sha256
  theorem axioms contract target_triple data_layout toolchain_revision

One `key=value` line per field, in that order, ASCII, one terminal LF.  The
certificate holds hashes, not paths, so it is data rather than a source of
build inputs; nothing compiles it.

The producer is not a verifier of a supplied certificate.  It derives the
certificate from the environment it was given -- the manifest's object, fixture
and marker paths, which it hashes itself, the target triple and data layout the
manifest records, and the toolchain revision the repository's
`toolchain-id.sh` prints -- and it checks the theorem, the contract-level
theorem and the axiom footprint in the Lean environment it loaded.  An
externally supplied theorem, type, axiom list or contract is never accepted.
Before serializing a fixture hash, the producer compares the file with the
`include_str` string the loaded proof module carries, so a stale module whose
guards ran against different fixture text cannot certify the current bytes.
A failed check writes nothing, so the previously published certificate bytes
are left untouched.
-/
import Lean
import LeanLLVM.Vellum.CommaMaskIR
import LeanLLVM.Vellum.CommaMaskLoop
import Lean.Util.CollectAxioms

open Lean Elab Command

namespace InstallCertificate

/-! ### The installation binding -/

/-- The serialized schema of an installation certificate. -/
def schemaVersion : String := "leanllvm-install-v1"

/-- The theorem the certificate names. -/
def theoremName : Name := ``LeanLLVM.Vellum.CommaMaskIR.IR_refines

/-- The same name as it is serialized. -/
def theoremText : String := "LeanLLVM.Vellum.CommaMaskIR.IR_refines"

/-- The theorem the loop unit's certificate names: the framed refinement of the
memory-backed loop to the unrolled candidate within the band the loop's own two
allocations cover. -/
def loopTheoremName : Name :=
  ``LeanLLVM.Vellum.CommaMaskLoop.loop_refines_candidate_within

/-- The same name as it is serialized. -/
def loopTheoremText : String :=
  "LeanLLVM.Vellum.CommaMaskLoop.loop_refines_candidate_within"

/-- The theorem that covers a unit: the loop has its own statement, every other
unit is covered by `IR_refines`, which relates the candidate to the baseline. -/
def theoremNameFor (unit : String) : Name :=
  if unit == "loop" then loopTheoremName else theoremName

/-- The serialized form of `theoremNameFor`. -/
def theoremTextFor (unit : String) : String :=
  if unit == "loop" then loopTheoremText else theoremText

/-- The contract the certificate names. -/
def contractName : Name := ``LeanLLVM.Vellum.commaContract

/-- The same name as it is serialized. -/
def contractText : String := "LeanLLVM.Vellum.commaContract"

/-- The contract-level theorem that links the named contract to the Lean
functions the emitted-IR theorem relates. -/
def contractTheoremName : Name := ``LeanLLVM.Vellum.byteLoop_refines_swar

/-- The permitted axiom footprint, in the canonical serialized order: the
names sorted by their serialized form in byte order.  This is the footprint
pinned in `LeanLLVMTest/Vellum.lean`; any other set is refused rather than
recorded. -/
def axiomFootprint : List String :=
  ["Classical.choice", "Quot.sound", "propext"]

/-! ### Shapes -/

def isLowerHex (c : Char) : Bool :=
  (48 ≤ c.val && c.val ≤ 57) || (97 ≤ c.val && c.val ≤ 102)

/-- The digest prefix of a `sha256sum` line: 64 lowercase hex digits followed
by the separator. -/
def digestOfLine (line : String) : Option String :=
  let cs := line.toList
  let head := cs.take 64
  if head.length == 64 && head.all isLowerHex then
    match cs.drop 64 with
    | ' ' :: _ => some (String.ofList head)
    | _ => none
  else
    none

/-- A `sha256:<64 lowercase hex>` toolchain revision, terminated by one LF. -/
def revisionOf (text : String) : Option String :=
  let cs := text.toList
  let head := cs.take 7
  let rest := cs.drop 7
  if head == ['s', 'h', 'a', '2', '5', '6', ':'] && rest.length == 65 &&
      rest.getLast? == some '\n' && (rest.dropLast).length == 64 &&
      (rest.dropLast).all isLowerHex then
    some (String.ofList (head ++ rest.dropLast))
  else
    none

def isNameChar (c : Char) : Bool := c.isAlphanum || c == '_' || c == '.'

def isTripleChar (c : Char) : Bool := isNameChar c || c == '-'

def isLayoutChar (c : Char) : Bool := isNameChar c || c == '-' || c == ':'

/-- A nonempty value over a closed character set. -/
def shaped (p : Char → Bool) (s : String) : Bool :=
  !s.isEmpty && s.toList.all p

/-! ### The manifest, read as data

The manifest is the build's `key=value` record.  It is read with a closed
split on the first `=`, blank and `#` lines are skipped, a repeated key is
refused, and only the values this producer needs are read.  Nothing here
evaluates the file. -/

structure Manifest where
  path : String
  entries : List (String × String)

def splitAssignment (line : String) : Option (String × String) :=
  let rec go : List Char → List Char → Option (String × String)
    | [], _ => none
    | '=' :: rest, acc => some (String.ofList acc.reverse, String.ofList rest)
    | c :: rest, acc => go rest (c :: acc)
  go line.toList []

def parseManifest (path text : String) : IO Manifest := do
  if text.toList.contains '\r' then
    throw <| IO.userError s!"manifest {path} is not LF-only"
  let mut entries : List (String × String) := []
  let mut keys : List String := []
  for line in text.splitOn "\n" do
    if line.isEmpty then
      continue
    match line.toList with
    | '#' :: _ => continue
    | _ =>
      match splitAssignment line with
      | none =>
        throw <| IO.userError
          s!"manifest {path} has a line without a key/value separator: {line}"
      | some (key, value) =>
        if keys.contains key then
          throw <| IO.userError s!"manifest {path} repeats the key '{key}'"
        keys := key :: keys
        entries := entries ++ [(key, value)]
  pure { path := path, entries := entries }

def Manifest.lookup? (m : Manifest) (key : String) : Option String :=
  (m.entries.find? fun entry => entry.1 == key).map fun entry => entry.2

def Manifest.require (m : Manifest) (key : String) : IO String := do
  match m.lookup? key with
  | none =>
    throw <| IO.userError s!"manifest {m.path} does not bind '{key}'"
  | some value =>
    if value.isEmpty then
      throw <| IO.userError s!"manifest {m.path} binds an empty '{key}'"
    else
      pure value

/-! ### Files and versions -/

def runCommand (cmd : String) (args : Array String) : IO String := do
  let out ← IO.Process.output { cmd := cmd, args := args }
  if out.exitCode != 0 then
    throw <| IO.userError
      s!"{cmd} {String.intercalate " " args.toList} failed with status {out.exitCode}: {out.stderr}"
  pure out.stdout

def sha256File (path : String) : IO String := do
  let stdout ← runCommand "sha256sum" #[path]
  match digestOfLine stdout with
  | some digest => pure digest
  | none =>
    throw <| IO.userError s!"sha256sum reported no digest for {path}"

/-- The toolchain revision, measured by the repository's own helper against
the tree this process runs in.  A supplied revision is never accepted. -/
def observedToolchain : IO String := do
  let stdout ← runCommand "bash" #["probes/install/toolchain-id.sh"]
  match revisionOf stdout with
  | some revision => pure revision
  | none =>
    throw <| IO.userError
      s!"probes/install/toolchain-id.sh printed no toolchain revision: {stdout}"

/-- The hashes and inputs the certificate serializes, all measured from the
files the manifest names. -/
structure Inputs where
  unitObject : String
  unitFixture : String
  unitMarker : String
  baselineObject : String
  candidateObject : String
  baselineFixture : String
  candidateFixture : String
  baselineMarker : String
  candidateMarker : String
  targetTriple : String
  dataLayout : String
  toolchainRevision : String

def gather (m : Manifest) (unit triple layout : String) : IO Inputs := do
  let baselineObjectPath ← m.require "baseline"
  let candidateObjectPath ← m.require "candidate"
  let baselineFixturePath ← m.require "baseline_fixture"
  let candidateFixturePath ← m.require "candidate_fixture"
  let baselineMarkerPath ← m.require "baseline_marker"
  let candidateMarkerPath ← m.require "candidate_marker"
  let unitObjectPath ← m.require unit
  let unitFixturePath ← m.require s!"{unit}_fixture"
  let unitMarkerPath ← m.require s!"{unit}_marker"
  -- The parsed fixtures the loaded theorem is about are the `include_str`
  -- strings the proof module carries.  If the module was not elaborated from
  -- the current fixture bytes, it is stale: hashing those bytes would bind the
  -- certificate to text the loaded proof never parsed.  Refuse instead.
  let baselineFixtureText ← IO.FS.readFile baselineFixturePath
  unless baselineFixtureText == LeanLLVM.Vellum.CommaMaskIR.baselineSrc do
    throw <| IO.userError
      s!"the loaded proof module was not elaborated from the current baseline fixture {baselineFixturePath}"
  let candidateFixtureText ← IO.FS.readFile candidateFixturePath
  unless candidateFixtureText == LeanLLVM.Vellum.CommaMaskIR.candidateSrc do
    throw <| IO.userError
      s!"the loaded proof module was not elaborated from the current candidate fixture {candidateFixturePath}"
  -- `CommaMaskLoop` carries the printed loop fixture the same way, so the same
  -- staleness argument applies when the requested unit is the loop.
  if unit == "loop" then
    let loopFixtureText ← IO.FS.readFile unitFixturePath
    unless loopFixtureText == LeanLLVM.Vellum.CommaMaskLoop.loopSrc do
      throw <| IO.userError
        s!"the loaded proof module was not elaborated from the current loop fixture {unitFixturePath}"
  pure {
    unitObject := (← sha256File unitObjectPath)
    unitFixture := (← sha256File unitFixturePath)
    unitMarker := (← sha256File unitMarkerPath)
    baselineObject := (← sha256File baselineObjectPath)
    candidateObject := (← sha256File candidateObjectPath)
    baselineFixture := (← sha256File baselineFixturePath)
    candidateFixture := (← sha256File candidateFixturePath)
    baselineMarker := (← sha256File baselineMarkerPath)
    candidateMarker := (← sha256File candidateMarkerPath)
    targetTriple := triple
    dataLayout := layout
    toolchainRevision := (← observedToolchain)
  }

/-! ### The environment checks -/

/-- The theorem that covers `unit` must be a theorem of exactly the proposition
the installation relies on: `IR_refines` for the candidate and the baseline, and
the framed loop-to-candidate refinement within the loop's own allocations for
the loop. -/
def checkTheorem (unit : String) : TermElabM Unit := do
  let name := theoremNameFor unit
  let info ← getConstInfo name
  match info with
  | ConstantInfo.thmInfo _ => pure ()
  | _ => throwError m!"{name} is not a theorem"
  let expected ← Term.elabType (←
    if unit == "loop" then
      `(∀ (x : BitVec 64) (o : LeanLLVM.Outcome),
        LeanLLVM.Beh LeanLLVM.noCalls
            LeanLLVM.Vellum.CommaMaskLoop.loopFunction [LeanLLVM.Value.int 64 x] o →
          ∃ o', LeanLLVM.Beh LeanLLVM.noCalls
              LeanLLVM.Vellum.CommaMaskIR.candidateFunction
              [LeanLLVM.Value.int 64 x] o' ∧
            o.AgreesOutside (LeanLLVM.Vellum.CommaMaskLoop.loopFrame x) o')
    else
      `(∀ calls, LeanLLVM.Refines calls
        LeanLLVM.Vellum.CommaMaskIR.candidateFunction
        LeanLLVM.Vellum.CommaMaskIR.baselineFunction))
  unless info.type.isForall do
    throwError m!"{name} is not a universally quantified statement"
  let ok ← Lean.Meta.withNewMCtxDepth do Lean.Meta.isDefEq info.type expected
  unless ok do
    throwError m!"{name} does not state the expected refinement"
  pure ()

/-- The named contract must be the contract structure's value, and the
contract-level theorem must state the relation that links it to the two Lean
functions. -/
def checkContract : TermElabM Unit := do
  let contractInfo ← getConstInfo contractName
  match contractInfo with
  | ConstantInfo.defnInfo _ => pure ()
  | ConstantInfo.opaqueInfo _ => pure ()
  | _ => throwError m!"{contractName} is not a definition"
  let contractType ← Term.elabType (← `(LeanLLVM.Vellum.Contract))
  let ok ← Lean.Meta.withNewMCtxDepth do Lean.Meta.isDefEq contractInfo.type contractType
  unless ok do
    throwError m!"{contractName} is not a LeanLLVM.Vellum.Contract"
  let theoremInfo ← getConstInfo contractTheoremName
  match theoremInfo with
  | ConstantInfo.thmInfo _ => pure ()
  | _ => throwError m!"{contractTheoremName} is not a theorem"
  let expected ← Term.elabType (← `(LeanLLVM.Vellum.commaContract ⊢
    LeanLLVM.Vellum.byteLoop ⊑ LeanLLVM.Vellum.swar))
  let ok ← Lean.Meta.withNewMCtxDepth do Lean.Meta.isDefEq theoremInfo.type expected
  unless ok do
    throwError m!"{contractTheoremName} does not state the contract refinement"

/-- The covering theorem's axiom footprint, read from the environment rather
than from printed output, must be exactly the standard pinned set. -/
def checkAxioms (name : Name) : CommandElabM (List String) := do
  let axioms ← Lean.collectAxioms name
  let names := axioms.toList.map fun n => n.toString
  if names.contains "sorryAx" then
    throwError m!"{name} depends on sorryAx"
  unless names.length == axiomFootprint.length do
    throwError m!"{name} depends on axioms {names}, not {axiomFootprint}"
  for required in axiomFootprint do
    unless names.contains required do
      throwError m!"{name} does not depend on {required}; footprint {names}"
  pure axiomFootprint

/-! ### Publication -/

def render (unit : String) (inputs : Inputs) (axioms : List String) : String :=
  let lines : List String := [
    s!"schema={schemaVersion}",
    s!"unit={unit}",
    s!"unit_object_sha256={inputs.unitObject}",
    s!"unit_fixture_sha256={inputs.unitFixture}",
    s!"unit_marker_sha256={inputs.unitMarker}",
    s!"baseline_object_sha256={inputs.baselineObject}",
    s!"candidate_object_sha256={inputs.candidateObject}",
    s!"baseline_fixture_sha256={inputs.baselineFixture}",
    s!"candidate_fixture_sha256={inputs.candidateFixture}",
    s!"baseline_marker_sha256={inputs.baselineMarker}",
    s!"candidate_marker_sha256={inputs.candidateMarker}",
    s!"theorem={theoremTextFor unit}",
    s!"axioms={String.intercalate "," axioms}",
    s!"contract={contractText}",
    s!"target_triple={inputs.targetTriple}",
    s!"data_layout={inputs.dataLayout}",
    s!"toolchain_revision={inputs.toolchainRevision}"
  ]
  String.intercalate "\n" lines ++ "\n"

/-- Publish in one rename, so a reader sees the previous bytes or the whole
new certificate.  The temporary file is removed if publication fails. -/
def publish (path contents : String) : IO Unit := do
  let pid ← IO.Process.getPID
  let tmp := path ++ s!".tmp-{pid}"
  try
    IO.FS.writeFile tmp contents
    IO.FS.rename tmp path
  catch err =>
    try IO.FS.removeFile tmp catch _ => pure ()
    throw err

def requireEnv (name : String) : IO String := do
  match ← IO.getEnv name with
  | none => throw <| IO.userError s!"{name} is not set"
  | some value =>
    if value.isEmpty then
      throw <| IO.userError s!"{name} is empty"
    else
      pure value

def requireAbsolute (name value : String) : IO Unit := do
  unless (System.FilePath.mk value).isAbsolute do
    throw <| IO.userError s!"{name} must be an absolute path: {value}"

end InstallCertificate

open InstallCertificate

run_cmd do
  let unit ← liftIO (requireEnv "CERT_UNIT")
  unless unit == "baseline" || unit == "candidate" || unit == "loop" do
    throwError s!"CERT_UNIT must name baseline, candidate or loop, not '{unit}'"
  let manifestPath ← liftIO (requireEnv "CERT_MANIFEST")
  let outPath ← liftIO (requireEnv "CERT_OUT")
  liftIO do
    requireAbsolute "CERT_MANIFEST" manifestPath
    requireAbsolute "CERT_OUT" outPath
  let manifestText ← liftIO (IO.FS.readFile manifestPath)
  let manifest ← liftIO (parseManifest manifestPath manifestText)
  if let some declared := manifest.lookup? "schema" then
    unless declared == schemaVersion do
      throwError s!"manifest {manifestPath} has schema '{declared}', not '{schemaVersion}'"
  let manifestTheorem ← liftIO (manifest.require "theorem")
  unless manifestTheorem == theoremText do
    throwError s!"manifest {manifestPath} names theorem '{manifestTheorem}', not '{theoremText}'"
  let manifestContract ← liftIO (manifest.require "contract")
  unless manifestContract == contractText do
    throwError s!"manifest {manifestPath} names contract '{manifestContract}', not '{contractText}'"
  if unit == "loop" then
    let manifestLoopTheorem ← liftIO (manifest.require "loop_theorem")
    unless manifestLoopTheorem == loopTheoremText do
      throwError s!"manifest {manifestPath} names loop theorem '{manifestLoopTheorem}', not '{loopTheoremText}'"
  let target ← liftIO (manifest.require "target")
  let triple ← liftIO (manifest.require "triple")
  unless target == triple do
    throwError s!"manifest {manifestPath} has target '{target}' but triple '{triple}'"
  unless shaped isTripleChar triple do
    throwError s!"manifest {manifestPath} has a malformed target triple '{triple}'"
  let layout ← liftIO (manifest.require "datalayout")
  unless shaped isLayoutChar layout do
    throwError s!"manifest {manifestPath} has a malformed data layout '{layout}'"
  let inputs ← liftIO (gather manifest unit triple layout)
  liftTermElabM (checkTheorem unit)
  liftTermElabM checkContract
  let axioms ← checkAxioms (theoremNameFor unit)
  liftIO (publish outPath (render unit inputs axioms))
