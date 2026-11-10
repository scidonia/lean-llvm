/-
The specification's side of the cross-check: `strtodSpec` run on the corpus.

The lexeme is turned into the decomposition `strtodSpec` takes (sign, `int`
part, optional `frac` digits, optional `exp` sign and digits) by a reader that
belongs to this driver, not to the module: the specification is stated over the
decomposition, and this file is the evidence that its results agree with
glibc's `strtod` on the corpus.  Evidence, not proof.
-/
import LeanLLVM.JSON.Strtod

open LeanLLVM.JSON

namespace StrtodCheck

def bytesOfChars (cs : List Char) : Bytes :=
  ByteString.literal (cs.map (fun c => UInt8.ofNat c.toNat))

/-- Split at the first character satisfying the predicate. -/
def splitFirst (p : Char → Bool) : List Char → List Char × List Char
  | [] => ([], [])
  | c :: cs => if p c then ([], cs) else
      let (a, b) := splitFirst p cs
      (c :: a, b)

/-- Read a lexeme into the decomposition: `[minus] int [frac] [exp]`. -/
def parseDecimal (s : String) : Option Decimal := do
  let cs := s.toList
  let (neg, cs) := match cs with
    | '-' :: rest => (true, rest)
    | _ => (false, cs)
  let (mant, expPart) : List Char × Option (Bool × List Char) :=
    match splitFirst (fun c => c == 'e' || c == 'E') cs with
    | (m, []) => (m, none)
    | (m, e) =>
      let (esign, ds) := match e with
        | '-' :: r => (true, r)
        | '+' :: r => (false, r)
        | _ => (false, e)
      (m, some (esign, ds))
  let (ip, fr) : List Char × Option (List Char) :=
    match splitFirst (fun c => c == '.') mant with
    | (i, []) => (i, none)
    | (i, f) => (i, some f)
  let ex := expPart.map (fun (sign, ds) => (sign, bytesOfChars ds))
  return ⟨neg, bytesOfChars ip, fr.map bytesOfChars, ex⟩

def run : IO Unit := do
  let text ← IO.FS.readFile "tests/json-strtod/corpus.txt"
  for line in text.splitOn "\n" do
    if line.isEmpty then continue
    match parseDecimal line with
    | none => IO.println s!"{line}\tsetup: unreadable lexeme"
    | some d => IO.println s!"{line}\t{(strtodSpec d).toBits}"

end StrtodCheck

#eval StrtodCheck.run
