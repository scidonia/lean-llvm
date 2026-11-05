/-
The `phi` scenario: the shape the parser accepts, the meaning the semantics
gives it, the meaning it refuses, and the two facts that make "additive" a
measurement rather than a claim.

Four behaviours are observed here, each chosen so that a wrong semantics answers
differently rather than merely failing to be proved:

* **edge timing** — the loop's `phi` takes `0` on entry and `%j` on the
  back-edge.  The same instruction is evaluated from two states that differ only
  in the predecessor field, and it returns `0` from one and `4` from the other.
  A semantics that ignored which edge was taken, or that fixed the first (or
  last) incoming entry, could not produce both.
* **three predecessors** — one program whose `phi` has three incoming entries
  returns `10`, `20` and `30` from its three edges.  A selector that read the
  first entry always, or the last always, would return a constant.
* **an entry-block phi** — accepted by the parser, `ub` at the semantics,
  because the entry block has no predecessor and `initState` leaves the field
  `none`.  This is a different reason from the next case.
* **a missing predecessor** — one program that returns `1` from one edge and
  `ub` from the other, because its incoming list names only the first.

Then the non-interference claim: for a program with a loop and a branch and no
`phi`, the run from `initState` and the run from a state whose predecessor is
some other block give the same outcome.  That is the `#guard` below, and the
theorem behind it is `runFuel_init_setPre` (pinned in `LeanLLVMTest/Core.lean`).

Elaborated by `nix develop -c lake env lean tests/phi-fragment.lean`.  A
`#guard` that does not hold stops elaboration with a nonzero exit status.

The differential run against a compiler is separate — `tests/phi-differential.sh`
— and is an observation about two programs, not a proof about the fragment.
-/
import LeanLLVM

namespace PhiFragment

open LeanLLVM

/-! ### Reading a module -/

def parseOk (src : String) : Module :=
  match parseModule src with
  | .ok m => m
  | .error _ => ⟨[], []⟩

def mainOf (src : String) : Function :=
  match (parseOk src).functions with
  | [f] => f
  | _ => ⟨"", .void, [], []⟩

/-- Whether `sub` occurs in `s`. -/
def mentions (s sub : String) : Bool := (s.splitOn sub).length > 1

def refusedWith (src : String) (tokens : List String) : Bool :=
  match parseModule src with
  | .error e => tokens.all (mentions e)
  | .ok _ => false

/-- The integer a run returns, or `none` for `ub` and for an unfinished run. -/
def intOut (o : Option Outcome) : Option Nat :=
  match o with
  | some (.ret (some (.int _ v)) _) => some v.toNat
  | _ => none

/-! ### Edge timing: the loop's `phi`

The loop fixture `tests/phi/loop.ll` reads `%i = phi i32 [ 0, %entry ],
[ %j, %body ]` at the head of a counting loop.  Its two incoming values differ,
so the value selected is a function of which edge was taken — which is exactly
what a semantics that ignores edge timing cannot reproduce. -/

def loopSrc : String :=
"define i32 @main() {
entry:
  br label %head
head:
  %i = phi i32 [ 0, %entry ], [ %j, %body ]
  %c = icmp ult i32 %i, 3
  br i1 %c, label %body, label %exit
body:
  %j = add i32 %i, 1
  br label %head
exit:
  ret i32 %i
}
"

-- The program parses, prints back to the same module, and running it returns 3:
-- one step per back-edge, so an edge-blind selector cannot land on 3.
#guard (parseOk loopSrc).functions.length = 1
#guard parseModule (Module.render (parseOk loopSrc)) = .ok (parseOk loopSrc)
#guard intOut (run noCalls (mainOf loopSrc) []) = some 3

/-- The state at the loop head with `%j` bound, entered from `from`. -/
def headState (block : String) : State :=
  { env := [("%j", .int 32 (BitVec.ofNat 32 4))], mem := [], next := 1
    pc := "head", pre := some block }

/-- The loop's `phi` instruction, as the fixture writes it. -/
def loopPhi : Instr :=
  .phi "%i" (.int 32) [("entry", .imm (.int 32 0)), ("body", .reg "%j")]

-- The discrimination: one instruction, two edges, two different answers.
#guard
  match evalInstr noCalls (headState "entry") loopPhi with
  | some s => lookupName s.env "%i" = some (.int 32 (BitVec.ofNat 32 0))
  | none => false

#guard
  match evalInstr noCalls (headState "body") loopPhi with
  | some s => lookupName s.env "%i" = some (.int 32 (BitVec.ofNat 32 4))
  | none => false

-- The order of the incoming list does not decide the answer: reversing it
-- leaves the two calls' answers as they were, so a "first entry wins" reading is
-- excluded by the pair above rather than by this one.
#guard
  match evalInstr noCalls (headState "body") (.phi "%i" (.int 32)
      [("body", .reg "%j"), ("entry", .imm (.int 32 0))]) with
  | some s => lookupName s.env "%i" = some (.int 32 (BitVec.ofNat 32 4))
  | none => false

/-! ### Three predecessors

`join` is reached from `entry`, `a` or `b`, and the incoming list names each
with a different value.  `argc` picks the edge, so one program answers three
ways. -/

def threeSrc : String :=
"define i32 @main(i32 %argc, ptr %argv) {
entry:
  %c1 = icmp eq i32 %argc, 1
  br i1 %c1, label %join, label %a
a:
  %c2 = icmp eq i32 %argc, 2
  br i1 %c2, label %join, label %b
b:
  br label %join
join:
  %p = phi i32 [ 10, %entry ], [ 20, %a ], [ 30, %b ]
  ret i32 %p
}
"

def threeRun (argc : Nat) : Option Nat :=
  intOut (run noCalls (mainOf threeSrc)
    [.int 32 (BitVec.ofNat 32 argc), .ptr 0])

#guard threeRun 1 = some 10
#guard threeRun 2 = some 20
#guard threeRun 3 = some 30
-- A fourth argument takes the same edge as the third; the answer is the same,
-- which is what makes the three preceding values the three edges rather than a
-- coincidence of the argument.
#guard threeRun 4 = some 30

/-! ### An entry-block `phi`

The parser accepts it; the semantics has no predecessor to select with, because
`initState` leaves the field `none`.  The module is one LLVM's verifier refuses —
an entry block has no predecessor, so its `phi` has nothing to select — and `ub`
is the conservative reading of that. -/

def entryPhiSrc : String :=
"define i32 @main() {
entry:
  %p = phi i32 [ 7, %entry ]
  ret i32 %p
}
"

#guard (parseOk entryPhiSrc).functions.length = 1
#guard run noCalls (mainOf entryPhiSrc) [] = some .ub

/-! ### A missing predecessor

The same program answers `1` from one edge and `ub` from the other, because its
incoming list names only `%a`.  The `ub` is reached at run time rather than at
parse time: the module is one LLVM's verifier refuses, and the reading admits no
behaviour LLVM forbids. -/

def missingSrc : String :=
"define i32 @main(i1 %c) {
entry:
  br i1 %c, label %a, label %b
a:
  br label %join
b:
  br label %join
join:
  %p = phi i32 [ 1, %a ]
  ret i32 %p
}
"

#guard intOut (run noCalls (mainOf missingSrc) [.int 1 (BitVec.ofNat 1 1)]) = some 1
#guard run noCalls (mainOf missingSrc) [.int 1 (BitVec.ofNat 1 0)] = some .ub

/-! ### Non-interference, exercised

A program with a back edge (`head` branches to itself) and a branch and no
`phi`: its run cannot see the predecessor field, so the outcome is the same
whatever the field holds at the start.  The theorem is `runFuel_init_setPre`; this
is the executable instance, and the path it takes goes through jumps in both
directions. -/

/-- A program with a back edge and a branch and no `phi`: a memory-backed
counter, so it loops without needing a `phi` to carry the induction variable. -/
def loopAndBranch : String :=
"define i32 @main(i32 %n) {
entry:
  %p = alloca i32
  store i32 %n, ptr %p
  br label %head
head:
  %i = load i32, ptr %p
  %i2 = add i32 %i, 1
  store i32 %i2, ptr %p
  %c = icmp ult i32 %i2, 3
  br i1 %c, label %head, label %exit
exit:
  %r = load i32, ptr %p
  ret i32 %r
}
"

#guard
  let f := mainOf loopAndBranch
  let s := initState f [.int 32 (BitVec.ofNat 32 0)]
  runFuel noCalls 100 f (s.setPre (some "head")) = runFuel noCalls 100 f s

#guard
  let f := mainOf loopAndBranch
  let s := initState f [.int 32 (BitVec.ofNat 32 0)]
  runFuel noCalls 100 f (s.setPre none) = runFuel noCalls 100 f s

-- The program reaches a `ret` through three back edges, so the two runs above
-- are an outcome and not two `none`s, and the field really is written on the
-- path: `head` is re-entered from `head`.
#guard intOut (run noCalls (mainOf loopAndBranch) [.int 32 (BitVec.ofNat 32 0)]) = some 3

/-! ### What the parser refuses

Each refusal names what it refused: a `phi` of `void` has no value to select; an
incoming value whose type disagrees with the instruction's is named with both
types; a `phi` that is not at the head of its block is refused, because LLVM
gives a mid-block `phi` no meaning either; and an incoming entry must be written
`[ <value>, %<block> ]`. -/

def withBody (line : String) : String :=
"define i32 @f(i32 %x) {
entry:
  br label %bb
bb:
" ++ line ++ "
  ret i32 %x
}
"

#guard refusedWith (withBody "  %p = phi void [ %x, %entry ]") ["void"]
#guard refusedWith (withBody "  %p = phi i8 [ %x, %entry ]") ["phi", "i8", "i32"]
#guard refusedWith (withBody "  %y = add i32 %x, 1\n  %p = phi i32 [ %x, %entry ]")
  ["phi", "first"]
#guard refusedWith (withBody "  %p = phi i32 [ %x %entry ]") ["phi"]
#guard refusedWith (withBody "  %p = phi i32 []") ["phi"]

-- A predecessor listed twice is refused by name.  First-match would give a
-- defined meaning to a module LLVM's verifier rejects, which is the one
-- direction the model must not take; the message names both the instruction and
-- the duplicated label.
#guard refusedWith (withBody "  %p = phi i32 [ %x, %entry ], [ %x, %entry ]")
  ["phi", "entry"]

-- The control for that refusal, in the same run: two entries on *distinct*
-- labels parse.  Together with the refusal above it shows the check is about
-- duplication and not about a two-entry list.
#guard (parseOk (withBody "  %p = phi i32 [ %x, %entry ], [ %x, %other ]")).functions.length = 1

-- A register name bound twice is refused, and so is a definition that reuses a
-- parameter's name: the semantics binds the later one while the `phi` type check
-- reads the first, so accepting the module would hand a defined meaning to text
-- LLVM's verifier rejects.
#guard refusedWith (withBody "  %y = add i32 %x, 1\n  %y = add i32 %x, 2")
  ["%y", "more than once"]
#guard refusedWith (withBody "  %x = add i32 %x, 1") ["%x", "parameter"]

-- Their controls, in the same run: one definition parses, and distinct names in
-- one block parse.
#guard (parseOk (withBody "  %y = add i32 %x, 1")).functions.length = 1
#guard (parseOk (withBody "  %y = add i32 %x, 1\n  %z = add i32 %y, 2")).functions.length = 1

-- And the control for the refusals above: the same shape, written correctly, parses.
#guard (parseOk (withBody "  %p = phi i32 [ %x, %entry ]")).functions.length = 1

end PhiFragment
