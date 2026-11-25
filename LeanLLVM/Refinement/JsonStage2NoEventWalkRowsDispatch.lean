/-
The no-event walk's row dispatch, by the head's own class.

`Stage2NoEventWalkRows` (`JsonStage2NoEventWalkPremises`) asks for a row at every
head.  The head block `NodeBlock5` compares its `%3` cell — the document's byte at
the entry's lane — against `"`, `[` and `{` (`LeafBlock`, `NodeBlock`/`LeafBlock1`,
`LeafBlock3` in `JsonStage2NoEventWalkLoop`/`JsonStage2NoEventWalkClose`), and
every other byte falls through to the scalar route.  That four-way vocabulary is
`Stage2NoEventHeadClass` in `JsonStage2NoEventWalkHead`, with
`stage2NoEventHeadClass_complete` exhaustive at every byte; this module reads the
head's class from that table and nothing else, so the vocabulary has one home.

The four predicates `Stage2NoEventWalkHead{String,Bracket,Brace,Value}Class` are
the producer interface: one per table constructor, each holding the head's
staging at that constructor's guard — the entry's lane, the document's byte, the
byte's `%3` cell, and the class value.  They name the table's classes; they are
not a second partition.  Both the split and the dispatch case
`stage2NoEventHeadClass_complete` at the head's byte: the entry's lane and the
document's byte are read from the state's own data (`K.ent[k]?`, `K.bs[lane]?`,
with the impossible branches closed against `Head.laneRead`), and each
constructor's guard is the class value its predicate names.
`stage2NoEventWalkHeadClass_split` is that case analysis as a disjunction, the
dispatch is the same case analysis producing the rows, and the priced step is the
corollary through `stage2NoEventWalkStep_of_rows`.

The predicates hold the head's staging and the class value, and no more.  A
class's producer also reads the head's depth (`%sp.0.ph1403`, `%frame.0.ph1402`,
`%1`), the entry stream and the document, and the registers and memory its route
touches; those are `Head`'s projections (`klt`, `spPhi`, `laneRead`,
`baseLookups`) or the producer's own route facts, so they are not restated here.
`Stage2NoEventWalkHead` does not carry the walk's accumulated output evidence
either: a continuing row's target trace is the source's stepped by the class's
event, so the class's producer needs `Stage2NoEventWalkTrace K` beside the head.
The rows and the step therefore take it as a second head premise, exactly as the
loop's step does.

The other four class tables are not head pivots: `Stage2NoEventContinuationClass`
is `NodeBlock15`'s dispatch at the next iteration, `Stage2NoEventValueClass` is
`scalar`/`cond.end`/`if.end457`'s at `%.lcssa`, `Stage2NoEventAfterValueClass` is
`after_value`'s at `%frame.6` and the following byte, and `Stage2NoEventPairClass`
is `expect_colon`'s at the post-key byte.  Each class's producer reaches its table
at that block and cases it there; the head's split is exhausted by the head table
alone, and no head state is left uncovered (the value class is every byte the
three `%3` comparisons reject).
-/
import LeanLLVM.Refinement.JsonStage2NoEventWalkPremises

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 800000

namespace LeanLLVM.Refinement

open LeanLLVM
open LeanLLVM.JSON
open LeanLLVM.Refinement.JsonStage2NoEventIR

/-! ### The producer interface

Each predicate is the head's staging at one class value: `Head.classStage`'s lane
and byte (the entry's index and the document's byte there), `Head.bytePresent`'s
`%3` cell, and the class value.  The four classes are the four constructors of
`Stage2NoEventHeadClass`; the value each predicate names is that constructor's
guard, so a predicate is a projection of the table at the head's byte. -/

/-- **The head's staging at one class value.**  The entry's lane, the document's
byte there, the byte's `%3` cell, and the byte's `Nat` value. -/
def Stage2NoEventWalkHeadByteClass (K : Stage2NoEventWalkCarry) (k : Nat)
    (s : State) (x : Nat) : Prop :=
  ∃ (lane : Nat) (byte : UInt8),
    K.ent[k]? = some lane ∧ K.bs[lane]? = some byte ∧
    readBytes s.mem (K.b + lane) 1 = some [byte] ∧
    lookupName s.env "%3" = some (.int 8 (BitVec.ofNat 8 byte.toNat)) ∧
    byte.toNat = x

/-- **The head's string class**: the table's `.string` constructor, whose guard is
`x = 34`. -/
def Stage2NoEventWalkHeadStringClass (K : Stage2NoEventWalkCarry) (k : Nat)
    (s : State) : Prop :=
  Stage2NoEventWalkHeadByteClass K k s 34

/-- **The head's bracket class**: the table's `.bracket` constructor, whose guard
is `x = 91`. -/
def Stage2NoEventWalkHeadBracketClass (K : Stage2NoEventWalkCarry) (k : Nat)
    (s : State) : Prop :=
  Stage2NoEventWalkHeadByteClass K k s 91

/-- **The head's brace class**: the table's `.brace` constructor, whose guard is
`x = 123`. -/
def Stage2NoEventWalkHeadBraceClass (K : Stage2NoEventWalkCarry) (k : Nat)
    (s : State) : Prop :=
  Stage2NoEventWalkHeadByteClass K k s 123

/-- **The head's value class**: the table's `.value` constructor, whose guards are
the three inequalities.  The value table's own four classes (whitespace, number,
literal, refusal) are read later, at `%.lcssa`; at the head this class is one. -/
def Stage2NoEventWalkHeadValueClass (K : Stage2NoEventWalkCarry) (k : Nat)
    (s : State) : Prop :=
  ∃ (lane : Nat) (byte : UInt8),
    K.ent[k]? = some lane ∧ K.bs[lane]? = some byte ∧
    readBytes s.mem (K.b + lane) 1 = some [byte] ∧
    lookupName s.env "%3" = some (.int 8 (BitVec.ofNat 8 byte.toNat)) ∧
    byte.toNat ≠ 34 ∧ byte.toNat ≠ 91 ∧ byte.toNat ≠ 123

/-! ### The staging at the state's own lane and byte

The dispatch picks the head's lane and byte out of the state's data, so the
`Head.laneRead` facts must be restated at that pair.  The entry stream and the
document determine the pair; the read and the `%3` cell are the head's. -/

/-- **The head's read at a lane and byte the data names.**  `Head.laneRead`'s
existential is unique in its lane and byte, so the read and the `%3` cell it
carries are those of `K.ent[k]? = some lane` and `K.bs[lane]? = some byte`. -/
theorem stage2NoEventWalkHeadStagingAt {K : Stage2NoEventWalkCarry} {mem : Mem}
    {k : Nat} {s : State} (h : Stage2NoEventWalkHead K mem k s)
    {lane : Nat} {byte : UInt8} (hent : K.ent[k]? = some lane)
    (hbs : K.bs[lane]? = some byte) :
    readBytes s.mem (K.b + lane) 1 = some [byte] ∧
      lookupName s.env "%3" = some (.int 8 (BitVec.ofNat 8 byte.toNat)) := by
  obtain ⟨lane', byte', hent', -, hbs', hread', -, -, -, -, -, h3'⟩ := h.laneRead
  have hlane : lane = lane' := Option.some.inj (by rw [← hent, hent'])
  subst hlane
  have hbyte : byte = byte' := Option.some.inj (by rw [← hbs, hbs'])
  subst hbyte
  exact ⟨hread', h3'⟩

/-! ### The split

The case analysis is the head's table at the byte `Head.laneRead` supplies; each
constructor's guard is the class value the matching predicate names. -/

/-- **The head table is exhaustive at the head's staging.**  No head state is
outside the four classes, and the partition is the table's, not a separate one. -/
theorem stage2NoEventWalkHeadClass_split {K : Stage2NoEventWalkCarry} {mem : Mem}
    {k : Nat} {s : State} (h : Stage2NoEventWalkHead K mem k s) :
    Stage2NoEventWalkHeadStringClass K k s ∨
      Stage2NoEventWalkHeadBracketClass K k s ∨
      Stage2NoEventWalkHeadBraceClass K k s ∨
      Stage2NoEventWalkHeadValueClass K k s := by
  obtain ⟨lane, byte, hent, -, hbs, hread, -, -, -, -, -, h3⟩ := h.laneRead
  cases stage2NoEventHeadClass_complete byte.toNat with
  | string h34 => exact Or.inl ⟨lane, byte, hent, hbs, hread, h3, h34⟩
  | bracket h91 => exact Or.inr (Or.inl ⟨lane, byte, hent, hbs, hread, h3, h91⟩)
  | brace h123 =>
      exact Or.inr (Or.inr (Or.inl ⟨lane, byte, hent, hbs, hread, h3, h123⟩))
  | value h34 h91 h123 =>
      exact Or.inr (Or.inr (Or.inr
        ⟨lane, byte, hent, hbs, hread, h3, h34, h91, h123⟩))

/-! ### The dispatch

One producer per head class, each at the head's staging and the walk's trace.  The
row is data, so the class is read from the state's lane and byte and cased through
the head's table; the `Head.laneRead` facts are transported to that pair by
`stage2NoEventWalkHeadStagingAt`. -/

/-- **The rows, from one producer per head class.**  The class predicates are the
table's four constructors; the case analysis selects the matching producer, and no
class's row is computed by this definition.  The trace is the head's carried
evidence, which a continuing row's target trace is built from. -/
noncomputable def stage2NoEventWalkRows_of_classes {calls : Calls} {mem : Mem} {F : Nat}
    (hstring : ∀ (K : Stage2NoEventWalkCarry) (k : Nat) (s : State),
      Stage2NoEventWalkHead K mem k s → Stage2NoEventWalkTrace K →
      Stage2NoEventWalkHeadStringClass K k s →
      Stage2NoEventWalkRow calls mem F K k s)
    (hbracket : ∀ (K : Stage2NoEventWalkCarry) (k : Nat) (s : State),
      Stage2NoEventWalkHead K mem k s → Stage2NoEventWalkTrace K →
      Stage2NoEventWalkHeadBracketClass K k s →
      Stage2NoEventWalkRow calls mem F K k s)
    (hbrace : ∀ (K : Stage2NoEventWalkCarry) (k : Nat) (s : State),
      Stage2NoEventWalkHead K mem k s → Stage2NoEventWalkTrace K →
      Stage2NoEventWalkHeadBraceClass K k s →
      Stage2NoEventWalkRow calls mem F K k s)
    (hvalue : ∀ (K : Stage2NoEventWalkCarry) (k : Nat) (s : State),
      Stage2NoEventWalkHead K mem k s → Stage2NoEventWalkTrace K →
      Stage2NoEventWalkHeadValueClass K k s →
      Stage2NoEventWalkRow calls mem F K k s) :
    Stage2NoEventWalkRows calls mem F where
  row K k s hhead htrace := by
    cases hent : K.ent[k]? with
    | none =>
        exact False.elim (by
          have hlen : K.ent.length = K.nep :=
            readLanes32_length mem K.ep K.nep K.ent hhead.inv.entries
          have hk : k < K.ent.length := by rw [hlen]; exact hhead.klt
          rw [List.getElem?_eq_getElem hk] at hent
          cases hent)
    | some lane =>
        cases hbs : K.bs[lane]? with
        | none =>
            exact False.elim (by
              have hmem : lane ∈ K.ent := List.mem_of_getElem? hent
              have hlane : lane < K.n := hhead.inv.inside lane hmem
              have hlen : K.bs.length = K.n :=
                JsonEntrySteps.readBytes_length mem K.b K.n hhead.inv.doc
              have hlt : lane < K.bs.length := by rw [hlen]; exact hlane
              rw [List.getElem?_eq_getElem hlt] at hbs
              cases hbs)
        | some byte =>
            have hst := stage2NoEventWalkHeadStagingAt hhead hent hbs
            cases stage2NoEventHeadClass_complete byte.toNat with
            | string h34 =>
                exact hstring K k s hhead htrace
                  ⟨lane, byte, hent, hbs, hst.1, hst.2, h34⟩
            | bracket h91 =>
                exact hbracket K k s hhead htrace
                  ⟨lane, byte, hent, hbs, hst.1, hst.2, h91⟩
            | brace h123 =>
                exact hbrace K k s hhead htrace
                  ⟨lane, byte, hent, hbs, hst.1, hst.2, h123⟩
            | value h34 h91 h123 =>
                exact hvalue K k s hhead htrace
                  ⟨lane, byte, hent, hbs, hst.1, hst.2, h34, h91, h123⟩

/-- **The step, from the class producers.**  One line through
`stage2NoEventWalkStep_of_rows`: the trace the rows take is the step's own. -/
theorem stage2NoEventWalkStep_of_classes {calls : Calls} {mem : Mem} {F : Nat}
    (hstring : ∀ (K : Stage2NoEventWalkCarry) (k : Nat) (s : State),
      Stage2NoEventWalkHead K mem k s → Stage2NoEventWalkTrace K →
      Stage2NoEventWalkHeadStringClass K k s →
      Stage2NoEventWalkRow calls mem F K k s)
    (hbracket : ∀ (K : Stage2NoEventWalkCarry) (k : Nat) (s : State),
      Stage2NoEventWalkHead K mem k s → Stage2NoEventWalkTrace K →
      Stage2NoEventWalkHeadBracketClass K k s →
      Stage2NoEventWalkRow calls mem F K k s)
    (hbrace : ∀ (K : Stage2NoEventWalkCarry) (k : Nat) (s : State),
      Stage2NoEventWalkHead K mem k s → Stage2NoEventWalkTrace K →
      Stage2NoEventWalkHeadBraceClass K k s →
      Stage2NoEventWalkRow calls mem F K k s)
    (hvalue : ∀ (K : Stage2NoEventWalkCarry) (k : Nat) (s : State),
      Stage2NoEventWalkHead K mem k s → Stage2NoEventWalkTrace K →
      Stage2NoEventWalkHeadValueClass K k s →
      Stage2NoEventWalkRow calls mem F K k s) :
    Stage2NoEventWalkStep calls mem F :=
  stage2NoEventWalkStep_of_rows
    (stage2NoEventWalkRows_of_classes hstring hbracket hbrace hvalue)

/-! ### Axiom footprints -/

#print axioms stage2NoEventWalkHeadStagingAt
#print axioms stage2NoEventWalkHeadClass_split
#print axioms stage2NoEventWalkRows_of_classes
#print axioms stage2NoEventWalkStep_of_classes

end LeanLLVM.Refinement
