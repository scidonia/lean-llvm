/-
The `leanllvm` driver.

It reads textual LLVM IR, runs the certified pipeline on every function, and
writes textual LLVM IR back.  The output is a drop-in replacement for the input
on the modelled subset, so it can be placed between `llvm-as`/`clang` and
`opt`/`llc` in a late-optimisation toolchain.
-/
import LeanLLVM

open LeanLLVM

structure Options where
  input : Option String := none
  output : Option String := none
  passes : List Pass := defaultPipeline
  check : Bool := true
  deriving Inhabited

def usage : String :=
  "usage: leanllvm <input.ll> [-o <output.ll>] [--passes constprop,foldbr,strength|none] [--no-check]"

def parsePassName (s : String) : Option Pass :=
  match s with
  | "constprop" => some constantPropagation
  | "foldbr" => some branchFolding
  | "strength" => some strengthReduction
  | _ => none

def parsePasses (s : String) : Except String (List Pass) :=
  if s = "none" then .ok []
  else
    let names := s.splitOn ","
    let ps := names.map parsePassName
    if ps.all (fun p => p.isSome) then
      .ok (ps.filterMap id)
    else
      let bad := names.zip ps |>.filterMap fun (n, p) => if p.isNone then some n else none
      .error s!"unknown pass(es): {String.intercalate ", " bad}"

def parseArgsAux (o : Options) : List String → Except String Options
  | [] =>
      if o.input.isNone then .error "missing input file" else .ok o
  | "-o" :: out :: rest => parseArgsAux { o with output := some out } rest
  | "-o" :: [] => .error "missing file name after -o"
  | "--passes" :: spec :: rest => do
      let ps ← parsePasses spec
      parseArgsAux { o with passes := ps } rest
  | "--passes" :: [] => .error "missing pass list after --passes"
  | "--no-check" :: rest => parseArgsAux { o with check := false } rest
  | arg :: rest =>
      if arg.startsWith "-" then .error s!"unknown option '{arg}'"
      else if o.input.isSome then .error "more than one input file"
      else parseArgsAux { o with input := some arg } rest

def parseArgs (args : List String) : Except String Options :=
  parseArgsAux {} args

def runPipeline (m : Module) (passes : List Pass) : Module :=
  { m with functions := m.functions.map (Pass.pipeline passes).run }

def main (args : List String) : IO UInt32 := do
  let opts ← match parseArgs args with
    | .ok opts => pure opts
    | .error e =>
        IO.eprintln s!"leanllvm: {e}"
        IO.eprintln usage
        return 1
  let some input := opts.input
    | IO.eprintln "leanllvm: missing input file"; return 1
  let src ← try
      IO.FS.readFile input
    catch e =>
      IO.eprintln s!"leanllvm: cannot read '{input}': {e}"
      return 1
  let module ← match parseModule src with
    | .ok m => pure m
    | .error e =>
        IO.eprintln s!"leanllvm: parse error in '{input}': {e}"
        return 1
  if opts.check then
    for f in module.functions do
      unless f.wf do
        IO.eprintln s!"leanllvm: function @{f.name} is not well formed (unique block names, every branch target defined)"
        return 1
  let out := runPipeline module opts.passes
  let text := Module.render out
  match opts.output with
  | some path =>
      IO.FS.writeFile path text
  | none => IO.print text
  return 0
