import LeanLLVM.Parser

open LeanLLVM

/-- Report whether each captured callee's fixture parses, and the first refusal. -/
def main : IO Unit := do
  let cases : List (String × Layout × String) :=
    [ ("num_el_el1", [("EPow", 24)], "probes/install/ir/stage2.callee.num_el_el1.ll"),
      ("stk_mul_u64", [], "probes/install/ir/stage2.callee.stk_mul_u64.ll") ]
  for (sym, layout, path) in cases do
    let src ← IO.FS.readFile path
    match parseModuleWith layout src with
    | .error e => IO.println s!"{sym}: PARSE ERROR: {e}"
    | .ok m =>
        match m.functions.head? with
        | none => IO.println s!"{sym}: parsed, no function"
        | some f =>
            IO.println s!"{sym}: parsed, {f.blocks.length} blocks, \
              {(f.blocks.flatMap (·.instrs)).length} instructions, \
              {f.params.length} params"
