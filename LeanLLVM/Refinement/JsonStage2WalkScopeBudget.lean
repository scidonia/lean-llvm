import LeanLLVM.Refinement.JsonStage2WalkScopeClassAB

set_option autoImplicit false

namespace LeanLLVM.Refinement
namespace WalkScope

open LeanLLVM
open LeanLLVM.Refinement.JsonStage2IR
open LeanLLVM.Refinement.BlockEval

/-! ### The budget, counted

`stage2Budget` is `stage2EntryAllowance * nep + stage2ByteAllowance * n +
stage2PositionAllowance * nxp + stage2FinalisationAllowance` with the constants
32, 8, 32 and 32 (`JsonStage2Contract`).  Two of the four are readings of the
pinned body rather than choices, and this section takes them.

**The per-entry allowance.**  One iteration of the entry loop is the whole
dispatch, and the dispatch's own price is the longest path from its head
(`while.body.i`) to the merge that closes the iteration (`cleanup478.i`), over the
graph with the five scans' repeated visits removed: what is left is a path through
the switch, the nesting arm, the record's write and the two container arms.
`walkDispatchPrice` is that path over `stage2Body`'s own block list and
terminators, and it is **22 blocks** — ten inside the allowance's 32.  The
allowance's remainder is not slack the dispatch spends: the head's own `phi` run,
the merge's two `phi`s and the retest are steps of blocks already counted, and a
`WalkLink` per block is the one step the trace charges.

The path is `while.body.i → NodeBlock21 → … → if.end473.i → cleanup478.i`; the
scans' *exits* (`while.end.i`, `while.end78.i`, `if.end372.i`, `if.end290.i`) are on
it, and their repeated *visits* are not — they are charged to a document byte.

**The per-byte allowance.**  A scan's repeated visit is one step of the scan, and a
scan step stays inside its own block set: the header, the landing block, and the
two switch levels between the landing and the header.  `walkScanStepSets` is the
five sets as the body's own names; the widest is six blocks (the four token scans
have two switch levels with two leaves each), so one byte's visit is at most six
steps — inside the allowance's 8.  The literal comparison's set is two, and its
own count is bounded by `min (ee - idx) ln` with `ln ≤ 5` at `if.end48.i`'s phi, so
its five bytes are five byte-allowances.

**The per-position allowance.**  32 is the expander's `(nps + 1) * 3` scan and its
`(nps + 1) * decodeIterCost` walk, counted per escape position by
`escapeExpandBudget`; nothing in this module reads it, and the decoder's own cost
is the `n / 64` term the byte allowance covers sixty-four times over.

What the count does not do is *compose*.  `walkMeasure`'s decrease is one step per
link and a chain's step count is the number of links it contains
(`WalkChain.steps`), so the comparison of that count against `stage2Budget` is the
completed chain's work; this section fixes the two numbers the comparison needs and
reads them off the pinned AST rather than asserting them. -/

set_option maxRecDepth 100000

/-- The ten blocks the five scans visit repeatedly: each scan's header and its
landing block.  A visit to one of them is charged to a document byte
(`stage2ByteAllowance`), not to an entry. -/
def walkScanBlocks : List String :=
  ["for.body.i.i", "for.inc.i.i", "land.rhs.i", "while.body370.i",
   "land.rhs.i103", "while.body.i104", "land.rhs71.i", "while.body76.i",
   "land.rhs457.i", "while.body462.i"]

/-- The five scans' own block sets, at the body's names: the header, the landing
block, the switch levels between the landing and the header, and the switch's
leaves.  A scan step stays inside its set, so the set's size bounds one byte's
visit. -/
def walkScanStepSets : List (List String) :=
  [ -- the literal comparison's latch
    ["for.body.i.i", "for.inc.i.i"],
   -- the whitespace scan
    ["while.body370.i", "land.rhs.i", "NodeBlock52", "NodeBlock50", "LeafBlock46",
     "LeafBlock48"],
   -- the string scan
    ["while.body.i104", "land.rhs.i103", "NodeBlock73", "NodeBlock71",
     "LeafBlock67", "LeafBlock69"],
   -- the escape scan
    ["while.body76.i", "land.rhs71.i", "NodeBlock94", "NodeBlock92", "LeafBlock88",
     "LeafBlock90"],
   -- the extra-token scan
    ["while.body462.i", "land.rhs457.i", "NodeBlock105", "NodeBlock103",
     "LeafBlock99", "LeafBlock101"]]

/-- A block's successors, at its own terminator: the body's control flow as the
pinned AST states it. -/
def walkSucc (n : String) : List String :=
  match stage2Body.findBlock n with
  | none => []
  | some b =>
      match b.term with
      | .br t => [t]
      | .condbr _ t e => [t, e]
      | .ret _ _ => []
      | .unreachable => []

/-- **The longest path between two blocks**, over the graph with `banned`
removed, at a fuel that bounds the search.  `none` is "no path": a branch that
does not reach the target contributes nothing, which is what keeps a path that
leaves the loop (`if.then`, `s2_walk.exit`) out of the count. -/
def walkLongest (fuel : Nat) (banned : List String) (s t : String) : Option Nat :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
      if s = t then some 0
      else
        ((walkSucc s).filter (fun u => !banned.contains u)).foldr
          (fun u acc =>
            match walkLongest fuel banned u t with
            | none => acc
            | some d => max (some (d + 1)) acc)
          none

/-- **The dispatch's price**: the longest path from the loop head to the merge
that closes an iteration, with the scans' repeated visits removed. -/
def walkDispatchPrice : Option Nat :=
  walkLongest 40 walkScanBlocks "while.body.i" "cleanup478.i"

#guard walkScanBlocks.all (fun n => (stage2Body.findBlock n).isSome) = true

#guard walkScanBlocks.length = 10
#guard walkScanBlocks.eraseDups.length = 10

#guard walkScanStepSets.all (fun xs => xs.all (fun n => (stage2Body.findBlock n).isSome)) = true
#guard walkScanStepSets.all (fun xs => xs.eraseDups.length = xs.length) = true
#guard walkScanStepSets.foldr (fun xs acc => max xs.length acc) 0 = 6

#guard walkDispatchPrice = some 22

/-- **The dispatch's own path is 22 blocks, and the per-entry allowance covers
it.**  The allowance is 32; the ten not spent are the head's `phi` run and the
merge's two `phi`s and retest, which are steps of blocks the path already counts,
and the entry's own record write, which is a block of the path. -/
theorem walkDispatch_le_entryAllowance :
    ∃ d, walkDispatchPrice = some d ∧ d ≤ stage2EntryAllowance := by
  refine ⟨22, by decide, by decide⟩

/-- **A byte's visit is inside the byte allowance.**  The widest scan step is six
blocks and the allowance is 8. -/
theorem walkScanStep_width_le_byteAllowance :
    walkScanStepSets.foldr (fun xs acc => max xs.length acc) 0 ≤ stage2ByteAllowance := by
  decide

/-- **The budget, as the four allowances read the arguments.**  This is the term
`stage2Budget` states, with the two counted factors named beside their values. -/
theorem walkBudget_count (nep n nxp : Nat) :
    stage2EntryAllowance * nep + stage2ByteAllowance * n +
        stage2PositionAllowance * nxp + stage2FinalisationAllowance =
      32 * nep + 8 * n + 32 * nxp + 32 := rfl

/-- info: 'LeanLLVM.Refinement.WalkScope.walkDispatch_le_entryAllowance' does not depend on any axioms -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.WalkScope.walkDispatch_le_entryAllowance

/-- info: 'LeanLLVM.Refinement.WalkScope.walkScanStep_width_le_byteAllowance' does not depend on any axioms -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.WalkScope.walkScanStep_width_le_byteAllowance

/-- info: 'LeanLLVM.Refinement.WalkScope.walkBudget_count' does not depend on any axioms -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.WalkScope.walkBudget_count

end WalkScope

end LeanLLVM.Refinement

/-! ### The nesting arm's and the trace's footprints, measured

Each is `#print axioms` on the declaration itself, and each is at or below the
`[propext, Classical.choice, Quot.sound]` ceiling the file's other pinned
declarations report.  The append lemma and the trace's arithmetic are below it —
`[propext, Quot.sound]` — because they read no `String` register name; the block's
pin, chain, terminator and step, and the two links that wrap them, do. -/

/-- info: 'LeanLLVM.Refinement.WalkScope.walkDenoteCode_append_some' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.WalkScope.walkDenoteCode_append_some

/-- info: 'LeanLLVM.Refinement.WalkScope.ifEnd24_find' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.WalkScope.ifEnd24_find

/-- info: 'LeanLLVM.Refinement.WalkScope.ifEnd24_denote' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.WalkScope.ifEnd24_denote

/-- info: 'LeanLLVM.Refinement.WalkScope.ifEnd24_term' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.WalkScope.ifEnd24_term

/-- info: 'LeanLLVM.Refinement.WalkScope.ifEnd24_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.WalkScope.ifEnd24_step

/-- info: 'LeanLLVM.Refinement.WalkScope.WalkChain.measure_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.WalkScope.WalkChain.measure_le

/-- info: 'LeanLLVM.Refinement.WalkScope.WalkChain.steps' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.WalkScope.WalkChain.steps

/-- info: 'LeanLLVM.Refinement.WalkScope.WalkChain.completes' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.WalkScope.WalkChain.completes

/-- info: 'LeanLLVM.Refinement.WalkScope.WalkLink.whileBody' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.WalkScope.WalkLink.whileBody

/-- info: 'LeanLLVM.Refinement.WalkScope.WalkLink.ifEnd24' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.WalkScope.WalkLink.ifEnd24

/-! ### The middle's class lemmas and two instances, measured

The two general lemmas and one instance of each class, at `#print axioms`: each is
at the `[propext, Classical.choice, Quot.sound]` ceiling the file's other pinned
declarations report.  The rest of the instances are the same application of the
same lemmas, so a per-instance reading adds nothing; what it would add is the
`decide` on the eight disequalities, which reads no axiom beyond `propext`. -/

/-- info: 'LeanLLVM.Refinement.WalkScope.WalkLink.icmpBr' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.WalkScope.WalkLink.icmpBr

/-- info: 'LeanLLVM.Refinement.WalkScope.WalkLink.br' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.WalkScope.WalkLink.br

/-- info: 'LeanLLVM.Refinement.WalkScope.WalkLink.NodeBlock21' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.WalkScope.WalkLink.NodeBlock21

/-- info: 'LeanLLVM.Refinement.WalkScope.WalkLink.condBr' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.WalkScope.WalkLink.condBr

/-- info: 'LeanLLVM.Refinement.WalkScope.WalkLink.refusalStore' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.WalkScope.WalkLink.refusalStore

/-- info: 'LeanLLVM.Refinement.WalkScope.WalkLink.if_then16_i' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.WalkScope.WalkLink.if_then16_i

/-- info: 'LeanLLVM.Refinement.WalkScope.WalkLink.cond_true_i' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.WalkScope.WalkLink.cond_true_i

/-- info: 'LeanLLVM.Refinement.WalkScope.walkDenoteCode_icmp' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.WalkScope.walkDenoteCode_icmp


/-- info: 'LeanLLVM.Refinement.WalkScope.walkExecTerm_condbr' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.WalkScope.walkExecTerm_condbr

namespace LeanLLVM.Refinement
namespace WalkScope
open BlockEval
/-- The value-position call's successor, named: the four cells it binds, at the answer's memory
and the block its test picks. -/
abbrev TailS₁ (s : State) (r : CallOutcome) (c rdv x : BitVec 32) : State :=
  { stateAt (cells
      [("%tobool417.not.i", .int 1 (evalICmp .eq x (BitVec.ofNat 32 0))),
       ("%call416.i", .int 32 x), ("%38", .int 32 rdv),
       ("%.sink372", .int 32 c)] s.env)
      { s with mem := r.mem, next := r.next } with
    pc := (if evalICmp .eq x (BitVec.ofNat 32 0) = 1 then "if.then418.i" else "if.then425.i")
    pre := some s.pc }

/-- The scalar call's emit arm, named. -/
abbrev TailS₂ (s : State) (r : CallOutcome) : State :=
  { stateAt (cells
      [("%tobool428.not.i", .int 1 (evalICmp .eq (BitVec.ofNat 32 1)
        (BitVec.ofNat 32 0))),
       ("%call427.i", .int 32 (BitVec.ofNat 32 1))] s.env)
      { s with mem := r.mem, next := r.next } with
    pc := "if.then447.i"
    pre := some s.pc }

/-- The copy call's successor, named: the whitespace scan's entry. -/
abbrev TailS₃ (s : State) (r : CallOutcome) (ei cd : Nat) : State :=
  { stateAt (cells
      [("%cmp451.i", .int 1 (evalICmp .ult (BitVec.ofNat 64 ei)
        (BitVec.ofNat 64 cd)))] s.env)
      { s with mem := r.mem, next := r.next } with
    pc := (if evalICmp .ult (BitVec.ofNat 64 ei) (BitVec.ofNat 64 cd) = 1
      then "land.rhs457.i" else "if.end473.i")
    pre := some s.pc }
end WalkScope
end LeanLLVM.Refinement
