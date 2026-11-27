import LeanLLVM.Parser

/- Report each captured callee's parsed shape, one tab-separated row per symbol:

    symbol <TAB> blocks <TAB> instructions <TAB> params <TAB> layout

The header of `stage2.callees.tsv` is generated from this output by
`capture-stage2-callees.sh`, so the counts and the layout literal it states are
the parse's own rather than a transcription that can drift.

  nix develop -c lake env lean --run probes/install/ir/parse-callees.lean
-/

open LeanLLVM

/-- The declared layout each fixture needs: the extent is the datalayout's, and
the parser takes it from the caller.  `%struct.EPow` is `uint64_t hi, lo;
int32_t e` — twenty bytes padded to its eight-byte alignment; `%struct.StkBn` is
`uint64_t w[96]` and the `int` count — 776 bytes — and `%struct.Stk` is two of
those, the `int64_t` exponent and the `int` sticky flag — 1568 bytes.  The key
is the name after `%struct.`, which is what `Parser.resolveStruct` looks up. -/
def layoutOf : String → Layout
  | "num_el_el1" => [("EPow", 24)]
  | "stk_cmp" => [("StkBn", 776), ("Stk", 1568)]
  | _ => []

/-- A layout in the Lean syntax the module's `numElLayout` uses. -/
def layoutStr (l : Layout) : String :=
  "[" ++ String.intercalate ", " (l.map fun (n, b) => s!"(\"{n}\", {b})") ++ "]"

def main : IO Unit := do
  let cases : List String := ["num_d8_el1", "num_el_el1", "stk_mul_u64", "stk_cmp"]
  for sym in cases do
    let layout := layoutOf sym
    let src ← IO.FS.readFile s!"probes/install/ir/stage2.callee.{sym}.ll"
    match parseModuleWith layout src with
    | .error e => IO.println s!"{sym}\tERROR\t{e}\t-1\t{layoutStr layout}"
    | .ok m =>
        match m.functions.head? with
        | none => IO.println s!"{sym}\tERROR\tno function\t-1\t{layoutStr layout}"
        | some f =>
            IO.println s!"{sym}\t{f.blocks.length}\t{(f.blocks.flatMap (·.instrs)).length}\t\
              {f.params.length}\t{layoutStr layout}"
