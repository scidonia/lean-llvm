/-
The no-event walk's rows, assembled from the four head classes' producers.

`JsonStage2NoEventWalkRowsDispatch`'s `stage2NoEventWalkRows_of_classes` takes one
producer per head class — a function from the head, the walk's trace and the
class predicate to the row.  This module states that contract as one predicate
per class (`Stage2NoEventWalk*Ready`), reduces the two committed empty-pair
producers to it, and runs the assembly and its step corollary at that contract.

**What the class predicates carry.**  `Stage2NoEventWalkHeadByteClass` holds the
entry's lane, the document's byte there, the byte's `%3` cell and the class's
value, and no more.  `Head` adds the head block's run equation (the six read
cells and the nine `phi` cells over an existential tail, with the depth `sp`,
the frame `fr`, the zero extension and the widths `sp < 2 ^ 32`, `fr < 2 ^ 8`),
the invariant, the index bound and the consumed-count bound.  `Trace` adds the
events so far.  Nothing in the three carries a class's *route* staging: the
closer's entry, the push and pop reads, the separator at the next entry.  A
class's producer therefore takes those as the facts below, and the assembly
takes the producers as parameters.

**The class producers.**  The bracket and brace classes' rows are the committed
empty-pair routes (`stage2NoEventWalkRow_cont_bracketPair`,
`stage2NoEventWalkRow_cont_bracePair`); the reductions below replace the class's
three staging hypotheses (`K.ent[k]?`, `K.bs[lane]?`, the byte's value) with the
class predicate and leave the rest explicit.  The value class's producer is the
`Stage2NoEventWalkValueReady` parameter, supplied by the four per-arm rows and
`stage2NoEventWalkValueRow_of_head`; the whitespace/remainder arm has no
producer yet.

**The gap.**  The ideal assembly — a single remaining parameter, the string
producer — is not reachable from the committed bytes.  The string producer
composes a route rather than a producer; the value producer is the
`Stage2NoEventWalkValueReady` parameter, since the four per-arm rows do not fill
its `hvalue` slot and the whitespace/remainder arm has no producer; the bracket
and brace producers are conditional, as the reductions below show.  The assembly
therefore states all four as parameters.  The per-class facts a producer needs
beyond its class predicate are its reduction's argument list.
-/
import LeanLLVM.Refinement.JsonStage2NoEventWalkRowsDispatch
import LeanLLVM.Refinement.JsonStage2NoEventWalkRowsBrace
import LeanLLVM.Refinement.JsonStage2NoEventWalkRowsValue
import LeanLLVM.Refinement.JsonStage2NoEventWalkRowsString

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000
set_option pp.maxSteps 200000

namespace LeanLLVM.Refinement

open LeanLLVM
open LeanLLVM.JSON
open LeanLLVM.Refinement.JsonStage2NoEventIR

/-! ### The producer contract, one predicate per head class

`stage2NoEventWalkRows_of_classes`'s four arguments, at their names.  The
predicates are the class table's four constructors as the dispatch reads them:
the head, the walk's trace and the class's staging. -/

/-- **The string class's producer.** -/
abbrev Stage2NoEventWalkStringReady (calls : Calls) (mem : Mem) (F : Nat) :=
  ∀ (K : Stage2NoEventWalkCarry) (k : Nat) (s : State),
    Stage2NoEventWalkHead K mem k s →
    Stage2NoEventWalkTrace K →
    Stage2NoEventWalkHeadStringClass K k s →
    Stage2NoEventWalkRow calls mem F K k s

/-- **The bracket class's producer.** -/
abbrev Stage2NoEventWalkBracketReady (calls : Calls) (mem : Mem) (F : Nat) :=
  ∀ (K : Stage2NoEventWalkCarry) (k : Nat) (s : State),
    Stage2NoEventWalkHead K mem k s →
    Stage2NoEventWalkTrace K →
    Stage2NoEventWalkHeadBracketClass K k s →
    Stage2NoEventWalkRow calls mem F K k s

/-- **The brace class's producer.** -/
abbrev Stage2NoEventWalkBraceReady (calls : Calls) (mem : Mem) (F : Nat) :=
  ∀ (K : Stage2NoEventWalkCarry) (k : Nat) (s : State),
    Stage2NoEventWalkHead K mem k s →
    Stage2NoEventWalkTrace K →
    Stage2NoEventWalkHeadBraceClass K k s →
    Stage2NoEventWalkRow calls mem F K k s

/-- **The value class's producer.** -/
abbrev Stage2NoEventWalkValueReady (calls : Calls) (mem : Mem) (F : Nat) :=
  ∀ (K : Stage2NoEventWalkCarry) (k : Nat) (s : State),
    Stage2NoEventWalkHead K mem k s →
    Stage2NoEventWalkTrace K →
    Stage2NoEventWalkHeadValueClass K k s →
    Stage2NoEventWalkRow calls mem F K k s

/-! ### The empty array's producer at the class predicate

The pair route's three class facts (`K.ent[k]?`, `K.bs[lane]?` and the opener's
value) are the bracket predicate's; the reduction reads them from the predicate
and leaves the route's own staging as arguments.  Those are, beyond the
predicate and `Head`/`Trace`: the closer's entry (`K.ent[k+1]?`, `K.bs[next]?`
and `nextByte = 93`), the depth and frame the push reads (`Head.spPhi` supplies
the cells and `Head.layers` their widths), the pair's memory staging (the
post-push entry lane's four bytes, the closer's one byte at the sign-extended
lane, and the popped stack byte equal to the frame), the separator at `k + 2`,
and the next head's liveness `k + 3 < nep`. -/

/-- **The empty array's row from the bracket class.**  The class predicate
supplies `K.ent[k]?`, `K.bs[lane]?` and the byte `[`; the route's staging is
explicit. -/
noncomputable def stage2NoEventWalkBracketRow_of_class {calls : Calls} {mem : Mem}
    {F : Nat} {K : Stage2NoEventWalkCarry} {k : Nat} {s : State}
    (h : Stage2NoEventWalkHead K mem k s)
    (htrace : Stage2NoEventWalkTrace K)
    (hclass : Stage2NoEventWalkHeadBracketClass K k s)
    {next : Nat} {nextByte : UInt8}
    (hk1 : K.ent[k + 1]? = some next) (hbs1 : K.bs[next]? = some nextByte)
    (hb1 : nextByte.toNat = 93)
    {sp fr : Nat}
    (hspH : lookupName s.env "%sp.0.ph1403" = some (.int 32 (BitVec.ofNat 32 sp)))
    (hfrH : lookupName s.env "%frame.0.ph1402" = some (.int 8 (BitVec.ofNat 8 fr)))
    (h1H : lookupName s.env "%1" = some (.int 64 (BitVec.ofNat 64 sp)))
    (hspPos : 1 ≤ sp) (hspLe : sp ≤ 519) (hspLt : sp < 2 ^ 32)
    (hfrLt : fr < 2 ^ 8) (hfrPos : 1 ≤ fr)
    (hkbound : k + 2 ≤ K.nep)
    {bs4 : List UInt8}
    (hlaneW : readBytes (writeBytes s.mem
      (bracketPushAddr K (BitVec.ofNat 64 sp))
      (natToBytes ((BitVec.ofNat 8 fr).toNat) 1))
      (K.ep + (BitVec.ofNat 64 (k + 1)).toNat * 4) 4 = some bs4)
    (hval4lt : bytesToNat bs4 < 2 ^ 32)
    (hbyte1W : readBytes (writeBytes s.mem
      (bracketPushAddr K (BitVec.ofNat 64 sp))
      (natToBytes ((BitVec.ofNat 8 fr).toNat) 1))
      (K.b + (BitVec.signExtend 64 (BitVec.ofNat 64 (bytesToNat bs4))).toNat) 1
      = some [nextByte])
    {bs : List UInt8}
    (hbytePop : readBytes (writeBytes s.mem
      (bracketPushAddr K (BitVec.ofNat 64 sp))
      (natToBytes ((BitVec.ofNat 8 fr).toNat) 1))
      (closeReadAddr K.stk
        (BitVec.ofNat 32 sp + BitVec.ofNat 32 4294967295).toNat) 1 = some bs)
    (hbsLen : bs.length = 1) (hbsVal : bytesToNat bs = fr)
    (hcomma : ∀ q, K.ent[k + 2]? = some q → K.bs.getD q 0 = 44)
    (hlt : k + 3 < K.nep) (hk63 : k + 3 < 2 ^ 63) :
    Stage2NoEventWalkRow calls mem F K k s := by
  classical
  apply Classical.choice
  obtain ⟨lane, byte, hent, hbs, -, -, hb⟩ := hclass
  exact ⟨stage2NoEventWalkRow_cont_bracketPair h htrace hent hbs hb hk1 hbs1 hb1
    hspH hfrH h1H hspPos hspLe hspLt hfrLt hfrPos hkbound hlaneW hval4lt hbyte1W
    hbytePop hbsLen hbsVal hcomma hlt hk63⟩

/-! ### The empty object's producer at the class predicate

The same reduction at the brace class: the predicate supplies the opener `{`'s
staging, and the route's staging is explicit.  Beyond the predicate and
`Head`/`Trace` it needs the closer's entry (`}`), the depth's and the frame's
positivity, the push/pop staging at `bracePushAddr` and `bracePopAddr`, the
separator at `k + 2`, and `k + 3 < nep`.  Unlike the array's route it has no
`%1` cell: `if.then9` reads the depth and frame only. -/

/-- **The empty object's row from the brace class.**  The class predicate
supplies `K.ent[k]?`, `K.bs[lane]?` and the byte `{`; the route's staging is
explicit. -/
noncomputable def stage2NoEventWalkBraceRow_of_class {calls : Calls} {mem : Mem}
    {F : Nat} {K : Stage2NoEventWalkCarry} {k : Nat} {s : State}
    (h : Stage2NoEventWalkHead K mem k s)
    (htrace : Stage2NoEventWalkTrace K)
    (hclass : Stage2NoEventWalkHeadBraceClass K k s)
    {next : Nat} {nextByte : UInt8}
    (hk1 : K.ent[k + 1]? = some next) (hbs1 : K.bs[next]? = some nextByte)
    (hb1 : nextByte.toNat = 125)
    {sp fr : Nat}
    (hspH : lookupName s.env "%sp.0.ph1403" = some (.int 32 (BitVec.ofNat 32 sp)))
    (hfrH : lookupName s.env "%frame.0.ph1402" = some (.int 8 (BitVec.ofNat 8 fr)))
    (hspPos : 1 ≤ sp) (hspLe : sp ≤ 519) (hspLt : sp < 2 ^ 32)
    (hfrLt : fr < 2 ^ 8) (hfrPos : 1 ≤ fr)
    (hkbound : k + 2 ≤ K.nep)
    {bs4 : List UInt8}
    (hlaneW : readBytes (writeBytes s.mem (bracePushAddr K (BitVec.ofNat 32 sp))
      (natToBytes ((BitVec.ofNat 8 fr).toNat) 1))
      (K.ep + (BitVec.ofNat 64 (k + 1)).toNat * 4) 4 = some bs4)
    (hval4lt : bytesToNat bs4 < 2 ^ 32)
    (hbyte1W : readBytes (writeBytes s.mem (bracePushAddr K (BitVec.ofNat 32 sp))
      (natToBytes ((BitVec.ofNat 8 fr).toNat) 1))
      (K.b + (BitVec.signExtend 64 (BitVec.ofNat 64 (bytesToNat bs4))).toNat) 1
      = some [nextByte])
    {bs : List UInt8}
    (hbytePop : readBytes (writeBytes s.mem (bracePushAddr K (BitVec.ofNat 32 sp))
      (natToBytes ((BitVec.ofNat 8 fr).toNat) 1))
      (bracePopAddr K sp) 1 = some bs)
    (hbsLen : bs.length = 1) (hbsVal : bytesToNat bs = fr)
    (hcomma : ∀ q, K.ent[k + 2]? = some q → K.bs.getD q 0 = 44)
    (hlt : k + 3 < K.nep) (hk63 : k + 3 < 2 ^ 63) :
    Stage2NoEventWalkRow calls mem F K k s := by
  classical
  apply Classical.choice
  obtain ⟨lane, byte, hent, hbs, -, -, hb⟩ := hclass
  exact ⟨stage2NoEventWalkRow_cont_bracePair h htrace hent hbs hb hk1 hbs1 hb1
    hspH hfrH hspPos hspLe hspLt hfrLt hfrPos hkbound hlaneW hval4lt hbyte1W
    hbytePop hbsLen hbsVal hcomma hlt hk63⟩

/-! ### The value class's producer

The value class's producer is the `Stage2NoEventWalkValueReady` parameter, not a
term in this module: the four per-arm rows and
`stage2NoEventWalkValueRow_of_head` supply the number and literal arms, and the
whitespace/remainder arm has no producer yet.  The assembly and its step
corollary therefore take the whole producer as an argument. -/

/-! ### The assembly

The four producers at their contract, through the dispatch's own case
analysis. -/

/-- **The rows, from one producer per head class.**  `stage2NoEventWalkRows_of_classes`
at the four producer predicates: the class table's four constructors are the
cases, and no row is computed here. -/
noncomputable def stage2NoEventWalkRows_of_ready {calls : Calls} {mem : Mem} {F : Nat}
    (hstring : Stage2NoEventWalkStringReady calls mem F)
    (hbracket : Stage2NoEventWalkBracketReady calls mem F)
    (hbrace : Stage2NoEventWalkBraceReady calls mem F)
    (hvalue : Stage2NoEventWalkValueReady calls mem F) :
    Stage2NoEventWalkRows calls mem F :=
  stage2NoEventWalkRows_of_classes hstring hbracket hbrace hvalue

/-- **The step, from one producer per head class.**  One line through
`stage2NoEventWalkStep_of_classes`: the trace the rows take is the step's own. -/
theorem stage2NoEventWalkStep_of_ready {calls : Calls} {mem : Mem} {F : Nat}
    (hstring : Stage2NoEventWalkStringReady calls mem F)
    (hbracket : Stage2NoEventWalkBracketReady calls mem F)
    (hbrace : Stage2NoEventWalkBraceReady calls mem F)
    (hvalue : Stage2NoEventWalkValueReady calls mem F) :
    Stage2NoEventWalkStep calls mem F :=
  stage2NoEventWalkStep_of_classes hstring hbracket hbrace hvalue

/-! ### Axiom footprints -/

#print axioms stage2NoEventWalkBracketRow_of_class
#print axioms stage2NoEventWalkBraceRow_of_class
#print axioms stage2NoEventWalkRows_of_ready
#print axioms stage2NoEventWalkStep_of_ready

end LeanLLVM.Refinement
