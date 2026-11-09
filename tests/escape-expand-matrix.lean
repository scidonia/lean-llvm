/-
The expander's staging matrix, generated.

The record `Γ_escape_expand` speaks only about stagings its `pre` admits, so a
falsity is evidence only if the staging is admitted.  This file generates the
stagings rather than listing them: every escape shape the body has an arm for, at
three body lengths, at two position offsets, at three cursor values, and under
every aliasing layout of the six pointer arguments — including the pairs the record
does not exclude, both directions and partial overlaps.  For each row it records

* whether the record's `pre` admits the staging (`admitted`),
* whether the run's outcome satisfies the `post` at the witnesses the staging fixes
  (`post`), and
* the class, so the counts are the evidence rather than an impression.

The rows whose `pre` and `post` both hold are the detector's affirmative control:
they show the comparison accepts a body it should accept, without which a negative
row is unreadable.  A row the `pre` does not admit is outside the contract and is
counted apart; it is not a falsity.

The comparison is a `Bool` over the concrete run, so it is the pinned body's
behaviour at a staging, not a second reading of the record.  It checks the clauses
the aliasing can reach: the decoded prefix (or the refusal's marker), the cursor
slot, and the offset slot.  The record's unchanged-outside conjunct is not checked
here; the four aliasing findings are all inside the clauses that are.

Run: `nix develop -c lake env lean tests/escape-expand-matrix.lean`.
-/
import LeanLLVM.Vellum.JsonEscapeDecodeRun

set_option maxRecDepth 20000

open LeanLLVM
open LeanLLVM.Vellum
open LeanLLVM.Vellum.JsonEscapeIR
open LeanLLVM.Vellum.JsonEscapeIntrinsics
open LeanLLVM.Vellum.JsonScanSpec

namespace EscapeMatrix

/-! ### Building a staging -/

/-- Bytes at an address, contiguously. -/
def bytesAt (base : Nat) (bs : List UInt8) : Mem :=
  (List.range bs.length).map fun i => (base + i, bs.getD i 0)

/-- One byte repeated. -/
def fill (base k : Nat) (byte : UInt8) : Mem :=
  (List.range k).map fun i => (base + i, byte)

/-- A staging.  The regions are written in a fixed precedence — the table, the
body, the position stream, the cursor slot, the offset slot, then the destination's
extent — because a staging is one memory: where two regions share an address the
first writes the byte, which is what makes containment and partial overlap
different rows. -/
def mkMem (body : List UInt8) (ps : List Nat) (err0 k0 : Nat)
    (b dst err xp xj tab : Nat) : Mem :=
  bytesAt tab unescapeTable ++
  bytesAt b (body ++ List.replicate 32 (0x20 : UInt8)) ++
  bytesAt xp (positionsBytes 4 ps ++ List.replicate 4 0) ++
  bytesAt xj (natToBytes k0 8) ++
  bytesAt err (natToBytes err0 8) ++
  fill dst (body.length + 72) 0

/-- The argument list of the measured expander. -/
def mkArgs (b n dst err xp xj nps pos0 tab : Nat) : List Value :=
  [.ptr b, .int 64 (BitVec.ofNat 64 n), .ptr dst, .ptr err, .ptr xp, .ptr xj,
   .int 64 (BitVec.ofNat 64 nps), .int 64 (BitVec.ofNat 64 pos0), .ptr tab]

/-! ### The row -/

/-- One generated staging. -/
structure Row where
  label : String
  shape : String
  b : Nat
  dst : Nat
  err : Nat
  xp : Nat
  xj : Nat
  tab : Nat
  n : Nat
  pos0 : Nat
  k0 : Nat
  err0 : Nat
  body : List UInt8
  ps : List Nat

/-- The row's memory and arguments. -/
def Row.mem (r : Row) : Mem := mkMem r.body r.ps r.err0 r.k0 r.b r.dst r.err r.xp r.xj r.tab

def Row.args (r : Row) : List Value :=
  mkArgs r.b r.n r.dst r.err r.xp r.xj r.ps.length r.pos0 r.tab

/-! ### The record's admission, as a decision -/

/-- The `pre` at the row's own witnesses.  Every clause of `Γ_escape_expand.pre`
except the ones the staging fixes by construction (the body read and the argument
list). -/
def Row.admitted (r : Row) : Bool :=
  (readBytes r.mem r.xp (4 * r.ps.length) == some (positionsBytes 4 r.ps)) &&
  r.ps.all (fun q => decide (r.pos0 ≤ q) && decide (q < r.pos0 + r.n)) &&
  (r.ps.map (fun q => q - r.pos0) == escapePositionsFrom r.body ⟨true, false⟩) &&
  decide (r.pos0 + r.n ≤ 2 ^ 32) &&
  (readBytes r.mem r.xj 8 == some (wordBytes 8 r.k0)) &&
  decide (r.k0 ≤ r.ps.length) &&
  (readBytes r.mem r.err 8 == some (wordBytes 8 r.err0)) &&
  (readBytes r.mem r.tab 256 == some unescapeTable) &&
  (readBytes r.mem (r.b + r.n) 32).isSome &&
  (readBytes r.mem r.dst (r.n + 64)).isSome &&
  (decide (r.b + r.n + 32 ≤ r.dst) || decide (r.dst + r.n + 64 ≤ r.b)) &&
  (decide (r.xp + 4 * r.ps.length ≤ r.dst) || decide (r.dst + r.n + 64 ≤ r.xp)) &&
  (decide (r.tab + 256 ≤ r.dst) || decide (r.dst + r.n + 64 ≤ r.tab)) &&
  (decide (r.err + 8 ≤ r.dst) || decide (r.dst + r.n + 64 ≤ r.err)) &&
  (decide (r.err + 8 ≤ r.xj) || decide (r.xj + 8 ≤ r.err)) &&
  (decide (r.xj + 8 ≤ r.dst) || decide (r.dst + r.n + 64 ≤ r.xj))

/-! ### The post at the row's witnesses -/

/-- The observable result of a row. -/
inductive Verdict where
  | timeout
  | ub
  | ok (admitted : Bool)
  | bad (admitted : Bool) (why : String)
  | outside
deriving Repr

/-- The run's outcome against the specification's walk, at the witnesses the
staging fixes. -/
def Row.verdict (r : Row) : Verdict :=
  let admitted := r.admitted
  match runFuel escapeCalls 800 usDecFunction (EntryState usDecFunction r.args r.mem 1) with
  | none => .timeout
  | some .ub => if admitted then .bad true "ub" else .outside
  | some (.ret v m) =>
      let spec := escapeDecodeGo r.body 0 r.k0
        ((r.ps.map (fun q => q - r.pos0)).drop r.k0) []
      match spec with
      | .decoded out k =>
          let vok := v == some (.int 64 (BitVec.ofNat 64 out.length))
          let dok := readBytes m r.dst out.length == some out
          let xok := readBytes m r.xj 8 == some (wordBytes 8 k)
          let eok := readBytes m r.err 8 == some (wordBytes 8 r.err0)
          if admitted && vok && dok && xok && eok then .ok true
          else if admitted then
            .bad true (if !vok then "return length" else if !dok then "decoded prefix"
              else if !xok then "cursor slot" else "offset slot")
          else .outside
      | .refused off k =>
          let vok := v == some (.int 64 (BitVec.allOnes 64))
          let eok := readBytes m r.err 8 == some (wordBytes 8 off)
          let xok := readBytes m r.xj 8 == some (wordBytes 8 k)
          if admitted && vok && eok && xok then .ok true
          else if admitted then
            .bad true (if !vok then "refusal marker" else if !eok then "offset slot"
              else "cursor slot")
          else .outside

/-! ### The rows -/

/-- The escape shapes the body has an arm for, with a trailing space run so a body
length past the escape reads bytes that are neither control nor backslash. -/
def shapes : List (String × List UInt8) :=
  [("plain", List.replicate 20 0x61),
   ("simple", [0x41, 0x5C, 0x6E, 0x42]),
   ("quote", List.replicate 34 0x61 ++ [0x5C, 0x22]),
   ("six", [0x5C, 0x75, 0x30, 0x30, 0x34, 0x31]),
   ("pair", [0x5C, 0x75, 0x44, 0x38, 0x33, 0x44,
             0x5C, 0x75, 0x44, 0x45, 0x30, 0x30]),
   ("control", [0x41, 0x0A, 0x42])]

/-- The aliasing layouts of the six pointer arguments: all distinct, and each pair
the record must exclude, in both containment directions. -/
def base (b dst err xp xj tab : Nat) : Nat × Nat × Nat × Nat × Nat × Nat :=
  (b, dst, err, xp, xj, tab)

def layouts : List (String × (Nat → Nat → Nat → Nat → Nat → Nat →
    Nat × Nat × Nat × Nat × Nat × Nat)) :=
  [("distinct", fun b d e x j t => base b d e x j t),
   ("tab=dst", fun b _d e x j t => base b t e x j t),
   ("dst-in-tab", fun b _d e x j t => base b (t + 16) e x j t),
   ("tab-in-dst", fun b d _e x j _t => base b d _e x j (d + 16)),
   ("err=dst", fun b d _e x j t => base b d d x j t),
   ("err-in-dst", fun b d _e x j t => base b d (d + 8) x j t),
   ("xj=dst", fun b d e x _j t => base b d e x d t),
   ("err=xj", fun b _d _e x j _t => base b _d j x j _t),
   ("tab=xj", fun b d _e x _j t => base b d _e x t t),
   ("tab=err", fun b d _e x j t => base b d t x j t)]

/-- One row per shape, length, offset, cursor and layout. -/
def rows : List Row :=
  let bs := 0x100
  let ds := 0x4000
  let es := 0x6000
  let xs := 0x8000
  let js := 0xA000
  let ts := 0xC000
  shapes.flatMap fun (sname, sbytes) =>
    let full := sbytes ++ List.replicate 32 (0x20 : UInt8)
    [sbytes.length - 1, sbytes.length, sbytes.length + 1].flatMap fun n =>
      [0, 1].flatMap fun pos0 =>
        let body := full.take n
        let ps := (escapePositionsFrom body ⟨true, false⟩).map (fun q => q + pos0)
        [0, min 1 ps.length, ps.length].flatMap fun k0 =>
          layouts.map fun (lname, f) =>
            let (b, dst, err, xp, xj, tab) := f bs ds es xs js ts
            { label := sname ++ "/n=" ++ toString n ++ "/pos0=" ++ toString pos0 ++
                "/k0=" ++ toString k0 ++ "/" ++ lname,
              shape := sname, b := b, dst := dst, err := err, xp := xp, xj := xj,
              tab := tab, n := n, pos0 := pos0, k0 := k0, err0 := 0,
              body := body, ps := ps }

/-! ### The counts -/

def verdicts : List (Row × Verdict) := rows.map fun r => (r, r.verdict)

def countOk : Nat := (verdicts.filter fun p => match p.2 with | .ok _ => true | _ => false).length

def countBad : Nat := (verdicts.filter fun p => match p.2 with | .bad _ _ => true | _ => false).length

def countOutside : Nat := (verdicts.filter fun p => match p.2 with | .outside => true | _ => false).length

def countOther : Nat := (verdicts.filter fun p => match p.2 with
  | .ok _ => false | .bad _ _ => false | .outside => false | _ => true).length

#guard rows.length = shapes.length * 3 * 2 * 3 * layouts.length
#guard countOk + countBad + countOutside + countOther = rows.length

-- The counts: the affirmative controls, the admitted falsities, the stagings the
-- record does not admit, and the runs that exhausted the fuel.
#eval (rows.length, countOk, countBad, countOutside, countOther)

-- The affirmative control: the distinct layout's rows at the natural length and
-- the fresh cursor must be admitted and satisfy the post.
#eval (verdicts.filter fun p =>
    p.1.label.endsWith "/distinct" && p.1.n == p.1.body.length &&
    p.1.k0 == 0).map fun p => (p.1.label, reprStr p.2)

-- One falsity per breaking clause, and the count per clause.
#eval (verdicts.filter fun p => match p.2 with | .bad _ _ => true | _ => false).foldl
  (fun acc p => match p.2 with
    | .bad _ why => if acc.any (fun q => q.1 == why) then acc
        else acc ++ [(why, p.1.label)]
    | _ => acc) []

/-! ### Focused rows named in the record's amendment -/

/-- The row the table's aliasing witness names. -/
def quoteTabRow : Option Row :=
  rows.find? (fun r => r.label == "quote/n=36/pos0=0/k0=0/tab=dst")

#eval quoteTabRow.map (fun r => (r.label, reprStr r.admitted, reprStr r.verdict))

/-- The falsities of the `quote` shape under the three table layouts, with the
decoded prefix as observed. -/
def quoteTabVerdicts : List (String × String × String) :=
  let rs := verdicts.filter (fun p =>
    p.1.shape == "quote" && p.1.n == 36 && p.1.k0 == 0 && p.1.pos0 == 0 &&
    (p.1.label.endsWith "/tab=dst" || p.1.label.endsWith "/dst-in-tab" ||
     p.1.label.endsWith "/tab-in-dst"))
  rs.map (fun p =>
    let run := runFuel escapeCalls 800 usDecFunction
      (EntryState usDecFunction p.1.args p.1.mem 1)
    (p.1.label, reprStr p.2,
     reprStr (match run with
       | some (.ret _ m) => readBytes m p.1.dst 37
       | _ => none)))

#eval quoteTabVerdicts

end EscapeMatrix
