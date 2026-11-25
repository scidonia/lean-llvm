/-
The no-event walk's invariant, and its seed at the record's precondition.

`Stage2NoEventWalkObligation` (`JsonStage2NoEventBody`) is a `Satisfies` at the
pinned body and the record's flattened adapter, and nothing in that module
inhabits it.  This module starts the family that does: the data the loop carries
(`Stage2NoEventWalkCarry`), the predicate every arm re-establishes
(`Stage2NoEventWalkInv`), and the seed — the invariant at the state the body is
entered from, at the four staging objects `Γ_stage2_noevent_at`'s `pre` fixes.

**The layering is the certified walk's.**  `WalkCarry`/`WalkInv` split the data
from the predicates for the same reason: a `Prop` structure cannot carry data
whose projections the arms must compute, so the carried numbers are the
predicate's indices rather than its fields.

**What the invariant is, and what it is not.**  It is the record's `pre` clauses
(`doc`, `tail`, `entries`, `order`, `inside`, `esc`, `scratchBytes`,
`scratchRoom`, the four staged word slots, `maxDoc`, the three count bounds,
`separate`, `watermark`), the four staging objects' `stagedPre` clauses that do
not mention the ABI numbers (`stagedBytes`, `stagedEnd`), the four carried
readings' facts (`tokLe`, `arenaEq`), and the run's frame so far (`walkPresent`,
`walkFrame`).  It is **not** the parse relation: `Stage2NoEvent bs arena obs toks`
is a property of the whole document, which no state before the last entry has,
so the terminal acceptance arm takes it as a premise
(`JsonStage2NoEventWalkTerminal`) rather than the invariant carrying it.

**The cross separation is one named surface.**  `Stage2NoEventWalkSep` is the
`DisjointRegions` over the caller's ABI regions concatenated with the four staged
objects, and it is a conjunct of the invariant, proved once from the adapter's
precondition rather than per arm.  The two relations that make up
`Γ_stage2_noevent_at.pre` decompose the twelve-slot argument list independently,
so the proof crosses between two decompositions of the same `BitVec 64` words; the
bounds both sides now carry (`Γ_stage2_noevent.pre`'s, and
`stage2NoEventStagedPre`'s) make each pair the same `Nat`, so the region lists are
equal and the staging's separation is the invariant's.

**The register facts are the state's, not the arms'.**  `Stage2NoEventWalkParams`
is the part the entry state can carry; `Stage2NoEventWalkLocals` is what the entry
block binds (`%xj`, `%off`); `Stage2NoEventWalkAcc` is the loop's accumulators with
their relation to the carry's numbers.  The arms read them at their entry state;
the seed establishes the parameter part, and the entry block's bootstrap and the
loop's dispatch establish the rest.
-/
import LeanLLVM.Refinement.JsonStage2NoEventBody

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 800000

namespace LeanLLVM.Refinement

open LeanLLVM
open LeanLLVM.JSON
open LeanLLVM.Refinement.JsonStage2NoEventIR
open LeanLLVM.Refinement.JsonEntryIR (readLanes32)

/-! ### The carry -/

/-- **The data the no-event walk carries.**  The record's static numbers at the
run's own values, the four staging objects, the four reading accumulators, and
the stack interval's right end.  The arms move `tok`, `terms`, `arena`,
`arenaWord`, `nextEnd` and the state; nothing else changes. -/
structure Stage2NoEventWalkCarry where
  /-- The twelve-slot ABI argument list the record's `pre` and post are read at. -/
  a12 : List Value
  /-- The allocator cursor the call was made at. -/
  next0 : Nat
  b : Nat
  n : Nat
  ep : Nat
  nep : Nat
  xp : Nat
  nxp : Nat
  scratch : Nat
  scratchcap : Nat
  tokensOut : Nat
  valuesOut : Nat
  sumOut : Nat
  err : Nat
  bs : List UInt8
  ent : List Nat
  /-- The container stack `%stk`. -/
  stk : Nat
  /-- The number path's output slot `%d`.  -/
  d : Nat
  /-- The `%xj` alloca's address: the entry block's first allocation. -/
  xj : Nat
  /-- The refusal record `%e`. -/
  e : Nat
  /-- The cursor record `%c`. -/
  c : Nat
  /-- The count the reading words carry so far. -/
  tok : Nat
  /-- The token's document index, as `%idxprom.lcssa` carries it. -/
  pos : Nat
  /-- The events' per-record contribution so far. -/
  terms : Nat
  /-- The decoded string bodies, in document order. -/
  arena : List UInt8
  /-- The arena's running byte sum, as the loop's register carries it. -/
  arenaWord : Nat
  /-- The allocator cursor the run's stack writes have reached. -/
  nextEnd : Nat

/-! ### The one separation surface -/

/-- **The walk's separation, once.**  Every ABI region the caller staged is
separate from every other, and the four staged objects are separate from all of
them and from each other.  It is `stage2NoEventStagedPre`'s cross clause, and it
is a conjunct of the invariant: an arm reads the slot it needs (the refusal word
against the three output words, the output words against each other, the cursor
against the record) by projecting this one list, never from a fact of its own. -/
def Stage2NoEventWalkSep (b n ep nep xp nxp scratch scratchcap tokensOut valuesOut
    sumOut err stk e c d : Nat) : Prop :=
  DisjointRegions
    (stage2NoEventRegions b n ep nep xp nxp scratch scratchcap tokensOut valuesOut
      sumOut err ++ stage2NoEventStagedRegions stk e c d)

/-- **The twelve-slot ABI list at `Nat` numbers**: the shape both `Γ_stage2_noevent.pre`
and `stage2NoEventStagedPre` write, named once so the congruence below has two
sides to compare. -/
def Stage2NoEventAbiList (b n ep nep xp nxp scratch scratchcap tokensOut valuesOut
    sumOut err : Nat) : List Value :=
  [.ptr b, .int 64 (BitVec.ofNat 64 n), .ptr ep, .int 64 (BitVec.ofNat 64 nep),
   .ptr xp, .int 64 (BitVec.ofNat 64 nxp), .ptr scratch,
   .int 64 (BitVec.ofNat 64 scratchcap), .ptr tokensOut, .ptr valuesOut,
   .ptr sumOut, .ptr err]

/-- **Two decompositions of one argument list agree at each slot.**  The pointer
slots are injective outright; each count slot is the same `BitVec 64` word, and
with both representatives below `2 ^ 64` the words' equality is the numbers'. -/
theorem stage2NoEventAbiList_eq {b n ep nep xp nxp scratch scratchcap tokensOut
    valuesOut sumOut err b' n' ep' nep' xp' nxp' scratch' scratchcap' tokensOut'
    valuesOut' sumOut' err' : Nat}
    (h : Stage2NoEventAbiList b n ep nep xp nxp scratch scratchcap tokensOut
      valuesOut sumOut err = Stage2NoEventAbiList b' n' ep' nep' xp' nxp' scratch'
      scratchcap' tokensOut' valuesOut' sumOut' err')
    (hn : n < 2 ^ 64) (hn' : n' < 2 ^ 64) (hsc : scratchcap < 2 ^ 64)
    (hsc' : scratchcap' < 2 ^ 64) (hne : nep < 2 ^ 64) (hne' : nep' < 2 ^ 64)
    (hnx : nxp < 2 ^ 64) (hnx' : nxp' < 2 ^ 64) :
    b = b' ∧ n = n' ∧ ep = ep' ∧ nep = nep' ∧ xp = xp' ∧ nxp = nxp' ∧
      scratch = scratch' ∧ scratchcap = scratchcap' ∧ tokensOut = tokensOut' ∧
      valuesOut = valuesOut' ∧ sumOut = sumOut' ∧ err = err' := by
  simp only [Stage2NoEventAbiList, List.cons.injEq, and_true,
    true_and, Value.ptr.injEq, Value.int.injEq] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := h
  refine ⟨h1, ?_, h3, ?_, h5, ?_, h7, ?_, h9, h10, h11, h12⟩
  · have := congrArg BitVec.toNat (eq_of_heq h2)
    simp only [BitVec.toNat_ofNat] at this
    rw [Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt hn'] at this
    exact this
  · have := congrArg BitVec.toNat (eq_of_heq h4)
    simp only [BitVec.toNat_ofNat] at this
    rw [Nat.mod_eq_of_lt hne, Nat.mod_eq_of_lt hne'] at this
    exact this
  · have := congrArg BitVec.toNat (eq_of_heq h6)
    simp only [BitVec.toNat_ofNat] at this
    rw [Nat.mod_eq_of_lt hnx, Nat.mod_eq_of_lt hnx'] at this
    exact this
  · have := congrArg BitVec.toNat (eq_of_heq h8)
    simp only [BitVec.toNat_ofNat] at this
    rw [Nat.mod_eq_of_lt hsc, Nat.mod_eq_of_lt hsc'] at this
    exact this

/-- **The separation, proved once from the adapter's precondition.**  The bounds
are the record's own (`Γ_stage2_noevent.pre`'s, at the same argument list); the
staging supplies that list at its own decomposition and the cross separation; the
two decompositions are one list, so the separation is the invariant's. -/
theorem stage2NoEventWalkSep_of_pre {a12 : List Value} {mem : Mem} {next : Nat}
    {stk e c d : Nat} {b n ep nep xp nxp scratch scratchcap tokensOut valuesOut
      sumOut err : Nat}
    (hargs : a12 = Stage2NoEventAbiList b n ep nep xp nxp scratch scratchcap
      tokensOut valuesOut sumOut err)
    (hnLt : n < 2 ^ 64) (hscLt : scratchcap < 2 ^ 64) (hneLt : nep < 2 ^ 64)
    (hnxLt : nxp < 2 ^ 64)
    (hstaged : stage2NoEventStagedPre a12 mem next stk e c d) :
    Stage2NoEventWalkSep b n ep nep xp nxp scratch scratchcap tokensOut valuesOut
      sumOut err stk e c d := by
  obtain ⟨-, b₃, n₃, ep₃, nep₃, xp₃, nxp₃, scratch₃, scratchcap₃, tokensOut₃,
    valuesOut₃, sumOut₃, err₃, hargs₃, hn₃, hsc₃, hne₃, hnx₃, hsep₃, -, -⟩ := hstaged
  have hlist : Stage2NoEventAbiList b n ep nep xp nxp scratch scratchcap tokensOut
      valuesOut sumOut err =
      Stage2NoEventAbiList b₃ n₃ ep₃ nep₃ xp₃ nxp₃ scratch₃ scratchcap₃ tokensOut₃
        valuesOut₃ sumOut₃ err₃ := hargs.symm.trans hargs₃
  obtain ⟨hb, hn, hep, hne, hxp, hnx, hscr, hsc, hto, hvo, hso, herr⟩ :=
    stage2NoEventAbiList_eq hlist hnLt hn₃ hscLt hsc₃ hneLt hne₃ hnxLt hnx₃
  show DisjointRegions (stage2NoEventRegions b n ep nep xp nxp scratch scratchcap
    tokensOut valuesOut sumOut err ++ stage2NoEventStagedRegions stk e c d)
  rw [hb, hn, hep, hne, hxp, hnx, hscr, hsc, hto, hvo, hso, herr]
  exact hsep₃

/-! ### The register facts

The arms do not carry these; they read them at their entry state, and each is
established where the body binds it.  A parameter is bound at `EntryState`
(`Stage2NoEventWalkParams`); `%xj` and `%off` are the entry block's own bindings
(`Stage2NoEventWalkLocals`); the three accumulators and the token index are bound
by the loop (`Stage2NoEventWalkAcc`). -/

/-- **What the entry state binds**: every parameter of the flattened body. -/
structure Stage2NoEventWalkParams (K : Stage2NoEventWalkCarry) (s : State) : Prop where
  b : lookupName s.env "%b" = some (.ptr K.b)
  n : lookupName s.env "%n" = some (.int 64 (BitVec.ofNat 64 K.n))
  ep : lookupName s.env "%ep" = some (.ptr K.ep)
  nep : lookupName s.env "%nep" = some (.int 64 (BitVec.ofNat 64 K.nep))
  xp : lookupName s.env "%xp" = some (.ptr K.xp)
  nxp : lookupName s.env "%nxp" = some (.int 64 (BitVec.ofNat 64 K.nxp))
  scratch : lookupName s.env "%scratch" = some (.ptr K.scratch)
  scratchcap : lookupName s.env "%scratchcap" = some (.int 64 (BitVec.ofNat 64 K.scratchcap))
  tokensOut : lookupName s.env "%tokens_out" = some (.ptr K.tokensOut)
  valuesOut : lookupName s.env "%values_out" = some (.ptr K.valuesOut)
  sumOut : lookupName s.env "%sum_out" = some (.ptr K.sumOut)
  err : lookupName s.env "%err" = some (.ptr K.err)
  stk : lookupName s.env "%stk" = some (.ptr K.stk)
  e : lookupName s.env "%e" = some (.ptr K.e)
  c : lookupName s.env "%c" = some (.ptr K.c)
  d : lookupName s.env "%d" = some (.ptr K.d)

/-- **What the entry block binds**: the `%xj` alloca and the `%off` address of the
refusal word at `%e + 8`. -/
structure Stage2NoEventWalkLocals (K : Stage2NoEventWalkCarry) (s : State) : Prop where
  xj : lookupName s.env "%xj" = some (.ptr K.xj)
  off : lookupName s.env "%off" = some (.ptr (K.e + 8))

/-- **What the loop binds**: the token index and the three accumulators, at the
carry's numbers. -/
structure Stage2NoEventWalkAcc (K : Stage2NoEventWalkCarry) (s : State) : Prop where
  pos : lookupName s.env "%idxprom.lcssa" = some (.int 64 (BitVec.ofNat 64 K.pos))
  tokens : lookupName s.env "%tokens.8" = some (.int 64 (BitVec.ofNat 64 K.tok))
  terms : lookupName s.env "%terms.8" = some (.int 64 (BitVec.ofNat 64 K.terms))
  arena : lookupName s.env "%arena.10" = some (.int 64 (BitVec.ofNat 64 K.arenaWord))

/-! ### The output evidence and the acceptance's reading

Both are vocabulary about the carry and the state (not about the segment tier), so
they sit with the invariant: the walk's terminal routes and the row's evidence are
stated at them.

`Stage2NoEventWalkTrace` is the events the walk has consumed, the reference
parser's tokens for them, the two counts the carry reads, and the span bound the
arena's later extension needs.  It is a row-tier predicate, not
an invariant field: `Stage2NoEventWalkInv` is frozen and does not carry the parse
relation, and the trace carries no memory read of its own — the arena is the
carry's logical list, extended by the rows' deltas.

`Stage2NoEventWalkAcceptAcc` is the acceptance's three stores' reading at the
terminal state.  It is not the loop's `Stage2NoEventWalkAcc`: `%idxprom.lcssa` is
defined on the number route only and `%tokens.8`/`%terms.8`/`%arena.10` on the
value route only, so no single `Acc` is inhabitable at every route's terminal
state — the acceptance reads exactly the three words it stores. -/

/-- **The output evidence at a carry.**  The trace says nothing about a state:
every field is a fact about the carry. -/
inductive Stage2NoEventWalkTrace (K : Stage2NoEventWalkCarry) : Prop where
  /-- The evidence at one carry. -/
  | intro (obs : List ConsumerEvent) (toks : List Token)
      (rel : Stage2NoEvent K.bs K.arena obs toks)
      (obsLen : obs.length = K.tok)
      (termsEq : K.terms = (obs.map ConsumerEvent.terms).sum)
      (arenaBound : Stage2NoEventArenaBound K.arena obs) :
      Stage2NoEventWalkTrace K

/-- **The three stores' reading at the acceptance's terminal state.** -/
structure Stage2NoEventWalkAcceptAcc (K : Stage2NoEventWalkCarry) (sT : State) : Prop where
  tokens : lookupName sT.env "%tokens.8" = some (.int 64 (BitVec.ofNat 64 K.tok))
  terms : lookupName sT.env "%terms.8" = some (.int 64 (BitVec.ofNat 64 K.terms))
  arena : lookupName sT.env "%arena.10" = some (.int 64 (BitVec.ofNat 64 K.arenaWord))

/-- **The loop's accumulator implies the acceptance's reading.**  The `Acc`
carries the three words beside the token index, so a terminal state that has the
full `Acc` has the acceptance's three-word form. -/
theorem Stage2NoEventWalkAcc.toAcceptAcc {K : Stage2NoEventWalkCarry} {s : State}
    (h : Stage2NoEventWalkAcc K s) : Stage2NoEventWalkAcceptAcc K s :=
  ⟨h.tokens, h.terms, h.arena⟩

/-! ### The invariant -/

/-- **The no-event walk's invariant.**  Everything the record's precondition
says, kept at the caller's memory; the carried readings' facts; and the frame
the state's memory has kept.  Every arm the family proves re-establishes it at
its target; the terminal arms read the carry and the frame to produce the
record's post. -/
structure Stage2NoEventWalkInv (K : Stage2NoEventWalkCarry) (mem : Mem) (s : State) :
    Prop where
  /-- The argument list's twelve components. -/
  args_eq : K.a12 = [.ptr K.b, .int 64 (BitVec.ofNat 64 K.n), .ptr K.ep,
    .int 64 (BitVec.ofNat 64 K.nep), .ptr K.xp, .int 64 (BitVec.ofNat 64 K.nxp),
    .ptr K.scratch, .int 64 (BitVec.ofNat 64 K.scratchcap), .ptr K.tokensOut,
    .ptr K.valuesOut, .ptr K.sumOut, .ptr K.err]
  /-- The document's bytes, as the caller staged them. -/
  doc : readBytes mem K.b K.n = some K.bs
  /-- The decoder's read-past tail. -/
  tail : HasBytes mem (K.b + K.n) stage2ReadTail
  /-- The entry stream. -/
  entries : readLanes32 mem K.ep K.nep = some K.ent
  /-- The entries are in document order. -/
  order : K.ent.Pairwise (· < ·)
  /-- Every entry starts inside the document. -/
  inside : ∀ q ∈ K.ent, q < K.n
  /-- The escape list's bytes. -/
  esc : HasBytes mem K.xp (4 * K.nxp)
  /-- The scratch buffer. -/
  scratchBytes : HasBytes mem K.scratch K.scratchcap
  /-- Its room for the document and the decoder's reserve. -/
  scratchRoom : K.n + stage2ArenaReserve ≤ K.scratchcap
  tokensBytes : HasBytes mem K.tokensOut 8
  valuesBytes : HasBytes mem K.valuesOut 8
  sumBytes : HasBytes mem K.sumOut 8
  errBytes : HasBytes mem K.err 8
  maxDoc : K.n ≤ stage2MaxDocument
  nLt : K.n < 2 ^ 64
  scratchcapLt : K.scratchcap < 2 ^ 64
  nepLt : K.nep < 2 ^ 64
  nxpLt : K.nxp < 2 ^ 64
  /-- The ABI regions are pairwise separate. -/
  separate : DisjointRegions
    (stage2NoEventRegions K.b K.n K.ep K.nep K.xp K.nxp K.scratch K.scratchcap
      K.tokensOut K.valuesOut K.sumOut K.err)
  /-- Every ABI region ends at or below the call's cursor. -/
  watermark : ∀ r ∈ stage2NoEventRegions K.b K.n K.ep K.nep K.xp K.nxp K.scratch
      K.scratchcap K.tokensOut K.valuesOut K.sumOut K.err, r.1 + r.2 ≤ K.next0
  /-- The four staged objects are present at their extents. -/
  stagedBytes : ∀ r ∈ stage2NoEventStagedRegions K.stk K.e K.c K.d, HasBytes mem r.1 r.2
  /-- And they end at or below the call's cursor. -/
  stagedEnd : ∀ r ∈ stage2NoEventStagedRegions K.stk K.e K.c K.d, r.1 + r.2 ≤ K.next0
  /-- **The one separation surface**: the staged objects against every ABI region. -/
  sep : Stage2NoEventWalkSep K.b K.n K.ep K.nep K.xp K.nxp K.scratch K.scratchcap
    K.tokensOut K.valuesOut K.sumOut K.err K.stk K.e K.c K.d
  /-- The register word is the arena's byte sum modulo a word. -/
  arenaEq : byteSum K.arena % 2 ^ 64 = K.arenaWord
  /-- The count never passes the document's length. -/
  tokLe : K.tok ≤ K.n
  /-- The bootstrap's own extent is inside the stack interval. -/
  nextEnd_static : K.next0 + (stage2BootstrapExtent + 8) ≤ K.nextEnd
  /-- The run's own writes are present at the state's memory. -/
  walkPresent : ∀ a, inRegions
    (stage2NoEventRunRegions K.scratch K.scratchcap K.stk K.e K.c K.d) a →
      present s.mem a
  /-- The run's memory has kept the caller's outside its own regions. -/
  walkFrame : UnchangedOutside mem s.mem
    (stage2NoEventRunRegions K.scratch K.scratchcap K.stk K.e K.c K.d ++
      [(K.next0, K.nextEnd - K.next0)])

/-- An offset below a range's width, from membership. -/
theorem sub_lt_of_le_of_lt {a b c : Nat} (h1 : b ≤ a) (h2 : a < b + c) : a - b < c := by
  omega

namespace Stage2NoEventWalkInv

variable {K : Stage2NoEventWalkCarry} {mem : Mem} {s : State}

/-- A location a present range covers is present, for the `∃ vs, readBytes`
form of `HasBytes` the record states. -/
theorem present_of_readBytes_has {a n : Nat} (h : HasBytes mem a n) :
    ∀ k, k < n → present mem (a + k) := by
  obtain ⟨vs, hvs⟩ := h
  exact readBytes_some_present mem a n vs hvs

/-- The ABI argument list is twelve long. -/
theorem a12_length (h : Stage2NoEventWalkInv K mem s) : K.a12.length = 12 := by
  rw [h.args_eq]
  rfl

/-- The record's precondition, read off the invariant, at a non-null document
pointer.  The pointer's clause is the caller's staging fact, so it is a hypothesis
here rather than a field of the invariant. -/
theorem pre (h : Stage2NoEventWalkInv K mem s) (hb : 1 ≤ K.b) :
    Γ_stage2_noevent.pre K.a12 mem K.next0 :=
  ⟨K.b, K.n, K.ep, K.nep, K.xp, K.nxp, K.scratch, K.scratchcap, K.tokensOut,
    K.valuesOut, K.sumOut, K.err, K.bs, K.ent, h.args_eq, h.doc, hb, h.tail,
    h.entries, h.order, h.inside, h.esc, h.scratchBytes, h.scratchRoom,
    h.tokensBytes, h.valuesBytes, h.sumBytes, h.errBytes, h.maxDoc, h.nLt,
    h.scratchcapLt, h.nepLt, h.nxpLt, h.separate, h.watermark⟩

/-- **The run's regions are present in the state's memory.**  The scratch buffer
and the four objects are the caller's, and the frame keeps them. -/
theorem runRegions_present (h : Stage2NoEventWalkInv K mem s) :
    ∀ a, inRegions
      (stage2NoEventRunRegions K.scratch K.scratchcap K.stk K.e K.c K.d) a →
        present s.mem a :=
  h.walkPresent

end Stage2NoEventWalkInv

/-! ### The seed

The invariant at the state the body is entered from: `EntryState` binds the
sixteen parameters to the flattened argument list, and the memory is the caller's
staging.  Every reading accumulator is zero, the arena is the empty list, and the
frame is the identity — no instruction has run, so nothing outside the run's
regions has moved.

The four staged objects are the caller's, so their presence is the record's
`stagedPre`; the ABI regions' presence and their separation from the four objects
are the record's `pre` and staging together, through
`stage2NoEventWalkSep_of_pre`.  `nextEnd` is the bootstrap's own bound, which
`nextEnd_static` requires and the seed chooses as the interval's right end; `%xj`
is the entry block's first allocation, at the cursor the body is entered with. -/

/-- **The seed.**  From the record's precondition and the staging of the four
objects, some carry's invariant holds at the entry state of the flattened body,
with the readings at their initial values and the memory untouched. -/
theorem stage2NoEventWalkInv_seed
    {a12 : List Value} {mem : Mem} {next : Nat} {stk e c d : Nat}
    (hpre : Γ_stage2_noevent.pre a12 mem next)
    (hstaged : stage2NoEventStagedPre a12 mem next stk e c d) :
    ∃ K : Stage2NoEventWalkCarry,
      K.a12 = a12 ∧ K.stk = stk ∧ K.e = e ∧ K.c = c ∧ K.d = d ∧
      K.next0 = next ∧ K.xj = next ∧ K.tok = 0 ∧ K.terms = 0 ∧ K.arena = [] ∧
      Stage2NoEventWalkInv K mem
        (EntryState stage2NoEventBody (stage2NoEventArgs a12 stk e c d) mem next) := by
  have hpre' := hpre
  obtain ⟨b, n, ep, nep, xp, nxp, scratch, scratchcap, tokensOut, valuesOut,
    sumOut, err, bs, ent, hargs, hdoc, hb1, htail, hentries, horder, hinside, hesc,
    hscratchBytes, hscratchRoom, htokB, hvalB, hsumB, herrB, hmaxDoc, hnLt,
    hscLt, hneLt, hnxLt, hsep, hwater⟩ := hpre'
  have hstaged' := hstaged
  obtain ⟨hstagedBytes, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
    _, hstagedEnd⟩ := hstaged'
  have hsepW : Stage2NoEventWalkSep b n ep nep xp nxp scratch scratchcap tokensOut
      valuesOut sumOut err stk e c d :=
    stage2NoEventWalkSep_of_pre (stk := stk) (e := e) (c := c) (d := d) hargs
      hnLt hscLt hneLt hnxLt hstaged
  refine ⟨
    { a12 := a12, next0 := next, b := b, n := n, ep := ep, nep := nep, xp := xp,
      nxp := nxp, scratch := scratch, scratchcap := scratchcap,
      tokensOut := tokensOut, valuesOut := valuesOut, sumOut := sumOut, err := err,
      bs := bs, ent := ent, stk := stk, d := d, xj := next, e := e, c := c,
      tok := 0, pos := 0, terms := 0, arena := [], arenaWord := 0,
      nextEnd := next + (stage2BootstrapExtent + 8) },
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    { args_eq := hargs, doc := hdoc, tail := htail, entries := hentries,
      order := horder, inside := hinside, esc := hesc,
      scratchBytes := hscratchBytes, scratchRoom := hscratchRoom,
      tokensBytes := htokB, valuesBytes := hvalB, sumBytes := hsumB,
      errBytes := herrB, maxDoc := hmaxDoc, nLt := hnLt, scratchcapLt := hscLt,
      nepLt := hneLt, nxpLt := hnxLt, separate := hsep, watermark := hwater,
      stagedBytes := hstagedBytes, stagedEnd := hstagedEnd, sep := hsepW,
      arenaEq := rfl, tokLe := Nat.zero_le n, nextEnd_static := Nat.le_refl _,
      walkPresent := ?_,
      walkFrame := fun _ _ => rfl }⟩
  intro a ha
  obtain ⟨r, hr, hlo, hhi⟩ := ha
  rcases List.mem_cons.mp hr with rfl | hr
  · have h := Stage2NoEventWalkInv.present_of_readBytes_has hscratchBytes (a - scratch) (sub_lt_of_le_of_lt hlo hhi)
    rwa [Nat.add_sub_of_le hlo] at h
  · have h := Stage2NoEventWalkInv.present_of_readBytes_has (hstagedBytes r hr) (a - r.1) (sub_lt_of_le_of_lt hlo hhi)
    rwa [Nat.add_sub_of_le hlo] at h

/-! ### Axiom footprints -/

#print axioms stage2NoEventAbiList_eq
#print axioms stage2NoEventWalkSep_of_pre
#print axioms stage2NoEventWalkInv_seed

end LeanLLVM.Refinement
