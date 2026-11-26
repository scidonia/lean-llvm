/-
The no-event walk's instance: the rows at the assembly's own premises, run to the
reference's word and value, and what the admitted domain does and does not give.

**The instance.**  `stage2NoEventWalkInstance` is one theorem.  Its hypotheses are
the ten a deployment supplies at the record's own selection — the eight producer
and arm premises `JsonStage2NoEventWalkRowsDischarge`'s
`stage2NoEventWalkRows_assembled_discharged` takes (the string and value
producers, the bracket closer-other / descend supply / trailing exit, the brace
closer / descend / trailing exit), the head, and the walk's trace — and its
conclusion is `JsonStage2NoEventWalkReference`'s
`stage2NoEventWalkReferenceRun_spec` at `stage2NoEventCalls stage2GapRecover`,
`mem` and fuel `27`.  Nothing is added and nothing is weakened: the proof is the
assembly's rows handed to the spec.

**Which conjuncts are whose.**  Splitting the accept disjunct by the spec's own
producer, `stage2NoEventWalkReferenceRun_terminal`:

* the **walk's** — the run `runFuel … = some (.ret (some (.int 64 w)) m)` at a
  price inside the potential, and `stage2NoEventBoundary` at that memory.  These
  are read from the row (its `cont` segment's price and run, or its terminal
  exit's), and the word is fixed by the route the row takes.
* the **reference's** — the parse equality `parsed`, the relation
  `Stage2NoEvent`, `Stage2Records`, `obs = consumeRecords …` and the value
  equation.  These are the accept row's carried data (`JsonStage2NoEventWalkPremises`
  `Stage2NoEventWalkExit.accept`'s `parsed`, `facts`, `rel`, `obsLen`,
  `termsEq`): a producer building the row at the reference parse places them
  there, and the spec reads them back.  The refusal arm's `refused` is carried
  the same way.

**The admitted domain.**  `Stage2NoEventAdmitted bs`
(`JsonStage2NoEventAdmission`) is the domain the arrow is stated on.  What it
contributes to the instance is exactly one thing: the reference's parse exists at
`bs`, and — the parser being a function — that tape is the only one, so the
`parsed` field of any accept row built at the parser's tape at `bs` is that
equality.  What it does not contribute: the head, the trace, the eight producers
and the arm premises.  `Stage2NoEventWalkInstance_admitted` states both halves as
one corollary — the domain's parse-and-its-uniqueness, and the instance at the
domain's document with the caller's tier unchanged.  Admission never produces the
run; it fixes the document at which a caller's rows report the reference's value.

**The residue, one list.**  Every hypothesis a deployment must supply for the
instance to have a call site, attributed to the committed module that hosts it,
with its status at this revision.  *Runnable-now*: the tree contains the row
composition at that shape, so a caller holding the shape's staging can build the
premise.  *Tree-coverage*: the tree lacks that shape's route or staging — a row
composition may exist, but the route premise it needs is unproduced.

| premise | committed module | status |
| --- | --- | --- |
| `hstring` | `Stage2NoEventWalkStringReady` (`JsonStage2NoEventWalkRowsAssemble`); rows composed by `JsonStage2NoEventWalkRowsString` (`stage2NoEventWalkStringRow_arena`, `…_plainArm`, `StringRoute_arena`, `StringRoute_plain`) | runnable-now from a head plus the route the module names; its two bridges are the caller's (the endpoint's invariant, and the three `cleanup287` `phi` registers) |
| `hvalue` | `JsonStage2NoEventWalkRowsValue`: `stage2NoEventWalkValueRow_number/_literalTrue/_literalFalse/_literalNull`, `…ValueRow_of_head` | number and `true`/`false`/`null` runnable-now; the `.ws`/`.other` dispatch is a **refusal** (`if.else510` → `cleanup580`), not a continuation: its route and price are stated in `JsonStage2NoEventWalkValueRemainder`, and the block's eight-instruction denotation with the `gapElse` evidence is `JsonStage2NoEventWalkIfElse510` (`stage2NoEventIfElse510_denote`/`_step`, `Stage2NoEventWalkValueRemainderTail.ofIfElse510`, `stage2NoEventWalkValueRemainderRow`), so the refusal row is runnable-now from the route, the entry's parameters and locals, and the helper call's observed words |
| `hcloserOther` | bracket closer at `]` off the comma continuation: `JsonStage2NoEventWalkRowsParentCloser`'s `Stage2NoEventWalkParentSep`; the pair route at the parent's `]` and its `]` arm in `JsonStage2NoEventWalkBracketParentCloser` (`stage2NoEventWalkBracketPairAfterValue`, `stage2NoEventWalkParentSepToCloseArr`, `stage2NoEventWalkParentSepArmDeep`/`…ArmTop`, `stage2NoEventWalkBracketParentSepRow`) | comma continuation runnable-now: `stage2NoEventWalkBracketCloserRow_of_comma` (`JsonStage2NoEventWalkRowsDischarge`), and depth zero by `stage2NoEventWalkBracketZeroRow` (`JsonStage2NoEventWalkRowsAfterValue`); the parent-closer `]` (`Stage2NoEventWalkParentSep K k 93`) runnable-now at a nested depth (`2 ≤ sp`), where `stage2NoEventWalkBracketParentSepRow` composes the eleven-block pair route, the nine-block `]` arm (its one-entry allowance proved as `stage2NoEventWalkParentSepArmPrice`) and the committed cycle at `k + 3` into a `Row.cont` — its residue is the caller's: the parent arm's pop at the endpoint's memory, the popped enclosing tag's non-zero, and the comma at `k + 3`; at depth one (`%sp.4 = 1`) the arm (`…ArmTop`) reaches the depth-zero entry at `k + 3` and the terminal row's acceptance/refusal evidence is the caller's, as for `htrail` |
| `D.branch` | `Stage2NoEventWalkDescendBranch` (`JsonStage2NoEventWalkRowsDescend`): depth non-zero, `sp ≤ 519`, `k + 3 < nep` | runnable-now (state facts; no head carries them — the seed head is depth zero) |
| `D.window` | `Stage2NoEventWalkBracketInnerWindow` at every dispatch state (`Stage2NoEventWalkBracketInner`); the class-indexed restatement of the window over the dispatch's four classes, with its bracket instance recovered from the committed one, is `Stage2NoEventWalkDescendWindow` (`JsonStage2NoEventWalkDescendClasses`) | runnable-now where the inner entry opens an **array**: the window's `byte91` pins that byte, so the committed supply is uninhabited when an array's first element is not an array. Tree-coverage for the other openers — the indexed window exists at every byte (the class table is total and deterministic, and each class's entry chain is reached), but the class's own staging is the missing piece, since no head holds at a class's entry (`…entry_notHead`); the entry head and its `phi` cells are now proved at each non-array class's entry (`JsonStage2NoEventWalkEntryRooted`'s `stage2NoEventWalkBraceEntryHead`, `…StringEntryHead`, `…ScalarEntryHead_true`/`_false`), so that class's staging comes from the entry's own registers rather than a head — what remains there is the class's route from the head's branch (row `D.inner`) |
| `D.inner` | `Stage2NoEventWalkBracketInnerAll` (`JsonStage2NoEventWalkBracketInner`), the `[` class's obligation; the other classes' producers are indexed by `JsonStage2NoEventWalkDescendClasses`'s `…DescendClass.producer`/`…routeAtDispatch` | runnable-now at `[`: `…BracketInner_of_windowSupply` turns the recursion plus the window supply into `Stage2NoEventWalkBracketInner`, and `…BracketDescendRow_of_windowSupply` yields the row with the committed two arms (`…InnerOutCloser`, `…InnerOutElement`). The head is no longer needed for the row composition at `"` and scalar: `JsonStage2NoEventWalkEntryRooted`'s `stage2NoEventWalkStringRow_cont_of_route_count`, `…ValueRoute.cycleSrc_count` and `stage2NoEventWalkValueRow_cont_of_route_count` take the consumed-count bound as the caller's supply (it was the only field read off `Stage2NoEventWalkHead`), so those rows are stated at any state whose route and count are known. The value provider from `scalar`'s post-`phi` branch is `JsonStage2NoEventWalkScalarValueProvider`: `stage2NoEventWalkValueLand` runs `land.lhs.true` through the scan, `if.end457`'s `%ee.1` selection, its `%k219` store and `%or.cond901` to `if.then471`/`if.else495`; `stage2NoEventWalkValueProviderAt_condTrue`/`…_condEnd` prepend `cond.true`/`cond.end`; and `stage2NoEventWalkValueProv_of_entry_true` composes them with the entry head's two links, transporting the base table and the two loop-carried arena readings. `stage2NoEventWalkValueRow_of_prov` is the class's row at the `.loopexit` entry from that provider and the arm's route; the arms' lexical facts and measured price stay the caller's, and at the last entry (`%cond = %n`, `k + 1 = K.nep`) no continuing row exists because the row's `k + 2 < K'.nep` fails — that row is the terminal lane's. The `"` class is closed at its entry (runnable-now at the entry: the entry head plus the base table **and** the two loop-carried readings `%alen.0.ph1405`/`%arena.0.ph1406`, which are the entry's supplies): `JsonStage2NoEventWalkStringCallLeg` proves the four-block call leg from a generic `if.end216` entry (`stage2NoEventWalkStringCallLeg`), `LeafBlock27`'s step at either form (`stage2NoEventWalkStringLeaf27StepArena`/`…StepPlain`) and the row at the `.loopexit` entry end to end (`stage2NoEventWalkStringRow_of_entry_arena`/`…_plain`), from `JsonStage2NoEventWalkEntryRooted`'s entry head plus the base table `stage2NoEventWalkStringEntryBase` transports to `if.end216`. The `{` prologue's cell assembly from `if.end19` is now `JsonStage2NoEventWalkBracePrologueFromEntry`: `stage2NoEventWalkBracePrologueFromEnd19` runs the four links and reads the prologue's cells at `NodeBlock21`'s entry, `…EntryAPrologueFromEnd19` states them as the key route's predicate at the member's opening quote, and `…BraceRouteFromEnd19` composes the key route to the pair endpoint in fourteen steps from `if.end19`. What remains between the `.loopexit` entry and `if.end19` is the two loop-carried arena readings (`%alen.0.ph1405`, `%arena.0.ph1406`), which the entry head's statement omits and the assembly therefore takes as supplies at `if.end19` |
| `htrail` | bracket trailing exit `nep ≤ k + 3`: `stage2NoEventWalkBracketZeroRow` (`JsonStage2NoEventWalkRowsAfterValue`) over `JsonStage2NoEventWalkRowsContainerZero`'s terminal routes | runnable-now at depth zero, where the acceptance's `hrefAcc`, the refusal's `hdata` and the report/boundary words `hreportAcc`/`hboundAcc`/`hreportRef` are the caller's reference-side supply; at a live depth runnable-now as a refusal when the entry at `k + 1` is `]` and `k + 2 = K.nep` (`stage2NoEventWalkBracketTrailDeepRow`, `JsonStage2NoEventWalkTrailingDeep`), with the push's staging and the report at the pushed memory the caller's; `k + 3 = K.nep` is denominated only to `if.end378`'s entry (`stage2NoEventWalkAfterValueContinuePrefix`), the parent's element route not being in this tree, and `k + 1 = K.nep` is the head's `if.end51.peel` refusal, runnable-now: `stage2NoEventWalkBracketHeadRefuseRow` (`JsonStage2NoEventWalkHeadFalseArms`) composes the committed block's false arm (`link_ifEnd51peel_false`, `%cmp319.not.peel = 0` → `if.then321`) with the terminal lane's zero-store row (`%n` at `%err`, `cleanup580` returning zero), from the caller's route to `if.end51.peel`'s entry and its invariant, its `%inc.peel`/`%nep` cells with `%inc.peel ≮ %nep`, the base table there, the report at the refusal's memory and the reference's verdict |
| `hbraceCloser` | `}` at `k + 1`: comma continuation `stage2NoEventWalkBraceRow_of_head` (`JsonStage2NoEventWalkRowsReady`); depth zero `stage2NoEventWalkBraceZeroRow`; the frame-zero pair's `}` route `stage2NoEventWalkBraceFrameZeroCloserRow` (`JsonStage2NoEventWalkRowsDischarge`), at the endpoint entry exposed by `stage2NoEventWalkBraceFrameZeroCloserRowOfEntry` (`JsonStage2NoEventWalkBraceCloseEntry`) | runnable-now at a **frame-zero** head: the nested close (`2 ≤ sp`) reaches the head at `k + 4` with the endpoint's frame and depth read off the entry the arm produces (`stage2NoEventWalkFrameZeroBraceDeepEntry`: frame `bytesToNat bs`, depth `sp - 1`), so no post over the endpoint's states is the caller's; what remains is the popped tag's non-zero (`bytesToNat bs ≠ 0`), the comma at `k + 3`, the price `jl + 9 ≤ 96`, the index bounds and the pair leg's staging. The top-level close (`sp = 1`) ends at depth and frame zero (`stage2NoEventWalkFrameZeroBraceTopEntry`) — the terminal lane's, not a continuation. Tree-coverage for the parent's `]` at `k + 2` (`Stage2NoEventWalkParentSep K k 93`), which no listed producer covers. A `}` at `k + 3` under a **non-zero** enclosing frame is not this route at all: the dispatch's `NodeBlock41` takes `LeafBlock39` to `if.then428`, the refusal arm (`JsonStage2NoEventIR`), so that shape is a refusal's, not a missing closer |
| `hbraceDescend` | quote shape `stage2NoEventWalkBraceDescendRow_quote`, non-quote `stage2NoEventWalkBraceDescendRow_of_refusal` needing `Stage2NoEventWalkBraceDescendRefusal` (`JsonStage2NoEventWalkRowsDescend`) | quote shape runnable-now; the non-quote branch tree-coverage (its refusing route is unlinked and its exit evidence is the caller's post) |
| `hbraceTrail` | `stage2NoEventWalkBraceZeroRow` (`JsonStage2NoEventWalkRowsAfterValue`) | as `htrail`: depth zero runnable-now; at a live depth runnable-now as a refusal when the entry at `k + 1` is `}` and `k + 2 = K.nep` (`stage2NoEventWalkBraceTrailDeepRow` over `stage2NoEventWalkBraceTrailPairRoute`, `JsonStage2NoEventWalkTrailingDeep`), the thirteen-block pair route re-stated at its trailing endpoint; the `k + 3 = K.nep` continuation ; the `k + 1 = K.nep` head refusal (`if.end23` → `if.then68` for `}`) is runnable-now: `stage2NoEventWalkBraceHeadRefuseRow` (`JsonStage2NoEventWalkHeadFalseArms`) composes `link_ifEnd23_false` with the terminal lane's zero-store row at `if.then68`, from the caller's route to `if.end23`'s entry and its invariant, its `%sp`/`%inc.lcssa1129` cells with `%inc.lcssa1129 ≮ %nep`, the base table there, the report at the refusal's memory and the reference's verdict |
| `hhead` | `Stage2NoEventWalkHead` (`JsonStage2NoEventWalkHead`), produced at `k = 0` by `stage2NoEventWalkSeedRun` (`JsonStage2NoEventWalkSeed`), which beyond the entry invariant and params requires `s0.pc = "entry"`, `s0.next = K.next0`, `1 ≤ K.b`, `0 < K.nep`, `K.tok = K.terms = 0` and `K.arena = []` — all the caller's | runnable-now; the heads at later `k` ride in the continuing rows' `Stage2NoEventWalkHeadPricedSegment` |
| `htrace` | `Stage2NoEventWalkTrace` (`JsonStage2NoEventWalkInv`), produced at `k = 0` by the same seed run, stepped by the classes' own events | runnable-now |

Nothing here makes a premise hold or claims the model reaches the shapes marked
tree-coverage: the instance is a conditional, and the table says where each
antecedent would come from.
-/
import LeanLLVM.Refinement.JsonStage2NoEventWalkRowsDischarge
import LeanLLVM.Refinement.JsonStage2NoEventWalkBraceCloseEntry
import LeanLLVM.Refinement.JsonStage2NoEventWalkBracketParentCloser
import LeanLLVM.Refinement.JsonStage2NoEventWalkReference
import LeanLLVM.Refinement.JsonStage2NoEventAdmission

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000
set_option pp.maxSteps 200000

namespace LeanLLVM.Refinement

open LeanLLVM
open LeanLLVM.JSON
open LeanLLVM.Refinement.JsonStage2NoEventIR

/-! ### The instance

The assembly's premises at the record's selection, handed to the reference run's
spec.  One theorem, ten hypotheses, the spec's own conclusion. -/

/-- **The no-event walk's instance at `stage2GapRecover` and fuel 27.**  The eight
producer and arm premises are `stage2NoEventWalkRows_assembled_discharged`'s —
the string producer, the bracket closer-other, the descend supply `D` and its
trailing exit, the brace closer/descend/trailing exit, the value producer — and
the head with its trace is the walk's.  The conclusion is
`stage2NoEventWalkReferenceRun_spec`'s statement at those rows: on the accept
route the run returns the reference's word at a price inside the potential with
`stage2NoEventBoundary`, and the row's carried parse, `Stage2NoEvent`,
`Stage2Records`, the record consumption and the value equation hold; on the
refusal route the run returns zero with its boundary.

Splitting the accept disjunct by the spec's own producer
(`stage2NoEventWalkReferenceRun_terminal`): the run, its price and the boundary
are the walk's; the parse equality, the relation, the records and the value
equation are the reference's, carried by the accept row.  Nothing is quantified
over `Stage2NoEvent`, and no hypothesis ties the facts' tape to the parser's
result — that tie is the accept row's own `parsed` field. -/
theorem stage2NoEventWalkInstance {mem : Mem} {K : Stage2NoEventWalkCarry}
    {k : Nat} {s : State}
    (hstring : Stage2NoEventWalkStringReady
      (stage2NoEventCalls stage2GapRecover) mem 27)
    (hcloserOther : ∀ (K : Stage2NoEventWalkCarry) (k : Nat) (s : State)
        (sp : Nat) (next : Nat) (nextByte : UInt8),
      Stage2NoEventWalkHead K mem k s →
      Stage2NoEventWalkTrace K →
      Stage2NoEventWalkHeadBracketClass K k s →
      lookupName s.env "%sp.0.ph1403" = some (.int 32 (BitVec.ofNat 32 sp)) →
      K.ent[k + 1]? = some next →
      K.bs[next]? = some nextByte →
      nextByte.toNat = 93 →
      ¬ Stage2NoEventWalkPairBranch K k s →
      Stage2NoEventWalkRow (stage2NoEventCalls stage2GapRecover) mem 27 K k s)
    (D : Stage2NoEventWalkBracketDescendSupply
      (stage2NoEventCalls stage2GapRecover) mem)
    (htrail : ∀ (K : Stage2NoEventWalkCarry) (k : Nat) (s : State) (sp : Nat),
      Stage2NoEventWalkHead K mem k s →
      Stage2NoEventWalkTrace K →
      Stage2NoEventWalkHeadBracketClass K k s →
      lookupName s.env "%sp.0.ph1403" = some (.int 32 (BitVec.ofNat 32 sp)) →
      K.nep ≤ k + 3 →
      Stage2NoEventWalkRow (stage2NoEventCalls stage2GapRecover) mem 27 K k s)
    (hbraceCloser : ∀ (K : Stage2NoEventWalkCarry) (k : Nat) (s : State)
        (sp : Nat) (next : Nat) (nextByte : UInt8),
      Stage2NoEventWalkHead K mem k s →
      Stage2NoEventWalkTrace K →
      Stage2NoEventWalkHeadBraceClass K k s →
      lookupName s.env "%sp.0.ph1403" = some (.int 32 (BitVec.ofNat 32 sp)) →
      K.ent[k + 1]? = some next →
      K.bs[next]? = some nextByte →
      nextByte.toNat = 125 →
      Stage2NoEventWalkRow (stage2NoEventCalls stage2GapRecover) mem 27 K k s)
    (hbraceDescend : ∀ (K : Stage2NoEventWalkCarry) (k : Nat) (s : State)
        (sp : Nat) (next : Nat) (nextByte : UInt8),
      Stage2NoEventWalkHead K mem k s →
      Stage2NoEventWalkTrace K →
      Stage2NoEventWalkHeadBraceClass K k s →
      lookupName s.env "%sp.0.ph1403" = some (.int 32 (BitVec.ofNat 32 sp)) →
      K.ent[k + 1]? = some next →
      K.bs[next]? = some nextByte →
      nextByte.toNat ≠ 125 →
      Stage2NoEventWalkRow (stage2NoEventCalls stage2GapRecover) mem 27 K k s)
    (hbraceTrail : ∀ (K : Stage2NoEventWalkCarry) (k : Nat) (s : State)
        (sp : Nat),
      Stage2NoEventWalkHead K mem k s →
      Stage2NoEventWalkTrace K →
      Stage2NoEventWalkHeadBraceClass K k s →
      lookupName s.env "%sp.0.ph1403" = some (.int 32 (BitVec.ofNat 32 sp)) →
      K.nep ≤ k + 3 →
      Stage2NoEventWalkRow (stage2NoEventCalls stage2GapRecover) mem 27 K k s)
    (hvalue : Stage2NoEventWalkValueReady
      (stage2NoEventCalls stage2GapRecover) mem 27)
    (hhead : Stage2NoEventWalkHead K mem k s)
    (htrace : Stage2NoEventWalkTrace K) :
    (∃ (q : Nat) (m : Mem) (arena : List UInt8) (obs : List ConsumerEvent)
        (toks : List Token) (t : Tape)
        (parsed : parseBytes Limits.default (ByteString.literal K.bs) = .ok t)
        (facts : Stage2NoEventWalkReferenceFacts K.bs arena obs toks t),
        q + 2 ≤ stage2NoEventWalkPotential K k + 27 + 2 ∧
        runFuel (stage2NoEventCalls stage2GapRecover) (q + 2) stage2NoEventBody s =
          some (.ret (some (.int 64 (Stage2NoEventWalkReferenceWord K.bs))) m) ∧
        stage2NoEventBoundary K.a12 mem K.next0 m
          (.int 64 (Stage2NoEventWalkReferenceWord K.bs)) ∧
        Stage2NoEvent K.bs arena obs toks ∧
        Stage2Records K.bs arena facts.rs toks ∧
        obs = consumeRecords K.bs arena facts.rs ∧
        (eventsOfBytes K.bs (facts.rs.map EventRecord.encodedBytes).flatten arena).bind
            valueOfEvents = scalarCanonValueOfBytes K.bs) ∨
      (∃ (q : Nat) (m : Mem),
        q + 2 ≤ stage2NoEventWalkPotential K k + 27 + 2 ∧
        runFuel (stage2NoEventCalls stage2GapRecover) (q + 2) stage2NoEventBody s =
          some (.ret (some (.int 64 0)) m) ∧
        stage2NoEventBoundary K.a12 mem K.next0 m (.int 64 0)) :=
  stage2NoEventWalkReferenceRun_spec
    (stage2NoEventWalkRows_assembled_discharged hstring hcloserOther D htrail
      hbraceCloser hbraceDescend hbraceTrail hvalue)
    hhead htrace

/-! ### The admitted-domain reading

The parser is a function, so a document has at most one tape; that is the only
tie admission gives the accept row's `parsed` field. -/

/-- **The reference's parse is unique at a document.**  `parseBytes` is a
function, so two accepting outcomes at the same bytes carry the same tape.  This
is why the domain's parse existence fixes a producer's `parsed` field: whichever
tape the producer writes, it is the one the parser returns at `bs`. -/
theorem stage2NoEventParse_tape_unique {bs : List UInt8} {t t' : Tape}
    (h : parseBytes Limits.default (ByteString.literal bs) = .ok t)
    (h' : parseBytes Limits.default (ByteString.literal bs) = .ok t') : t' = t := by
  rw [h] at h'
  exact (ParseResult.ok.inj h').symm

/-- **What admission contributes to the instance, and what it does not.**

At an admitted document and a caller-supplied carry at it (`hK : K.bs = bs`),
the theorem's two conjuncts are:

* the **domain's** — the reference's parse exists at `bs`, and it is unique, so
  any accept row built at the parser's tape at `bs` carries this tape in its
  `parsed` field (`JsonStage2NoEventAdmission`'s `Stage2NoEventAdmitted.hparse`
  and the uniqueness above);
* the **caller's** — the instance at `bs`, at exactly the ten hypotheses
  `stage2NoEventWalkInstance` takes.  Admission supplies none of them: the head,
  the trace, the eight producer and arm premises are untouched by `hK` and by
  the domain's clauses, so the second conjunct is the same conditional as the
  instance and not a run the domain produces.

The accept route's value equation and relation are the reference's and ride in
the row (the first conjunct fixes only the tape they are read at); the run, its
price and the boundary are the walk's.  `hK` is the document tie the deployment
supplies; admission does not give it, because it says nothing about `mem`, `K`,
`k` or `s`. -/
theorem Stage2NoEventWalkInstance_admitted {bs : List UInt8}
    (hadm : Stage2NoEventAdmitted bs)
    {mem : Mem} {K : Stage2NoEventWalkCarry} {k : Nat} {s : State}
    (hK : K.bs = bs)
    (hstring : Stage2NoEventWalkStringReady
      (stage2NoEventCalls stage2GapRecover) mem 27)
    (hcloserOther : ∀ (K : Stage2NoEventWalkCarry) (k : Nat) (s : State)
        (sp : Nat) (next : Nat) (nextByte : UInt8),
      Stage2NoEventWalkHead K mem k s →
      Stage2NoEventWalkTrace K →
      Stage2NoEventWalkHeadBracketClass K k s →
      lookupName s.env "%sp.0.ph1403" = some (.int 32 (BitVec.ofNat 32 sp)) →
      K.ent[k + 1]? = some next →
      K.bs[next]? = some nextByte →
      nextByte.toNat = 93 →
      ¬ Stage2NoEventWalkPairBranch K k s →
      Stage2NoEventWalkRow (stage2NoEventCalls stage2GapRecover) mem 27 K k s)
    (D : Stage2NoEventWalkBracketDescendSupply
      (stage2NoEventCalls stage2GapRecover) mem)
    (htrail : ∀ (K : Stage2NoEventWalkCarry) (k : Nat) (s : State) (sp : Nat),
      Stage2NoEventWalkHead K mem k s →
      Stage2NoEventWalkTrace K →
      Stage2NoEventWalkHeadBracketClass K k s →
      lookupName s.env "%sp.0.ph1403" = some (.int 32 (BitVec.ofNat 32 sp)) →
      K.nep ≤ k + 3 →
      Stage2NoEventWalkRow (stage2NoEventCalls stage2GapRecover) mem 27 K k s)
    (hbraceCloser : ∀ (K : Stage2NoEventWalkCarry) (k : Nat) (s : State)
        (sp : Nat) (next : Nat) (nextByte : UInt8),
      Stage2NoEventWalkHead K mem k s →
      Stage2NoEventWalkTrace K →
      Stage2NoEventWalkHeadBraceClass K k s →
      lookupName s.env "%sp.0.ph1403" = some (.int 32 (BitVec.ofNat 32 sp)) →
      K.ent[k + 1]? = some next →
      K.bs[next]? = some nextByte →
      nextByte.toNat = 125 →
      Stage2NoEventWalkRow (stage2NoEventCalls stage2GapRecover) mem 27 K k s)
    (hbraceDescend : ∀ (K : Stage2NoEventWalkCarry) (k : Nat) (s : State)
        (sp : Nat) (next : Nat) (nextByte : UInt8),
      Stage2NoEventWalkHead K mem k s →
      Stage2NoEventWalkTrace K →
      Stage2NoEventWalkHeadBraceClass K k s →
      lookupName s.env "%sp.0.ph1403" = some (.int 32 (BitVec.ofNat 32 sp)) →
      K.ent[k + 1]? = some next →
      K.bs[next]? = some nextByte →
      nextByte.toNat ≠ 125 →
      Stage2NoEventWalkRow (stage2NoEventCalls stage2GapRecover) mem 27 K k s)
    (hbraceTrail : ∀ (K : Stage2NoEventWalkCarry) (k : Nat) (s : State)
        (sp : Nat),
      Stage2NoEventWalkHead K mem k s →
      Stage2NoEventWalkTrace K →
      Stage2NoEventWalkHeadBraceClass K k s →
      lookupName s.env "%sp.0.ph1403" = some (.int 32 (BitVec.ofNat 32 sp)) →
      K.nep ≤ k + 3 →
      Stage2NoEventWalkRow (stage2NoEventCalls stage2GapRecover) mem 27 K k s)
    (hvalue : Stage2NoEventWalkValueReady
      (stage2NoEventCalls stage2GapRecover) mem 27)
    (hhead : Stage2NoEventWalkHead K mem k s)
    (htrace : Stage2NoEventWalkTrace K) :
    (∃ t : Tape, parseBytes Limits.default (ByteString.literal bs) = .ok t ∧
      ∀ t' : Tape, parseBytes Limits.default (ByteString.literal bs) = .ok t' →
        t' = t) ∧
    ((∃ (q : Nat) (m : Mem) (arena : List UInt8) (obs : List ConsumerEvent)
        (toks : List Token) (t : Tape)
        (parsed : parseBytes Limits.default (ByteString.literal bs) = .ok t)
        (facts : Stage2NoEventWalkReferenceFacts bs arena obs toks t),
        q + 2 ≤ stage2NoEventWalkPotential K k + 27 + 2 ∧
        runFuel (stage2NoEventCalls stage2GapRecover) (q + 2) stage2NoEventBody s =
          some (.ret (some (.int 64 (Stage2NoEventWalkReferenceWord bs))) m) ∧
        stage2NoEventBoundary K.a12 mem K.next0 m
          (.int 64 (Stage2NoEventWalkReferenceWord bs)) ∧
        Stage2NoEvent bs arena obs toks ∧
        Stage2Records bs arena facts.rs toks ∧
        obs = consumeRecords bs arena facts.rs ∧
        (eventsOfBytes bs (facts.rs.map EventRecord.encodedBytes).flatten arena).bind
            valueOfEvents = scalarCanonValueOfBytes bs) ∨
      (∃ (q : Nat) (m : Mem),
        q + 2 ≤ stage2NoEventWalkPotential K k + 27 + 2 ∧
        runFuel (stage2NoEventCalls stage2GapRecover) (q + 2) stage2NoEventBody s =
          some (.ret (some (.int 64 0)) m) ∧
        stage2NoEventBoundary K.a12 mem K.next0 m (.int 64 0))) := by
  subst bs
  obtain ⟨t0, h0⟩ := hadm.hparse
  exact
    ⟨⟨t0, h0, fun t' ht' => stage2NoEventParse_tape_unique h0 ht'⟩,
      stage2NoEventWalkInstance hstring hcloserOther D htrail hbraceCloser
        hbraceDescend hbraceTrail hvalue hhead htrace⟩

/-! ### Axiom footprints -/

#print axioms stage2NoEventWalkInstance
#print axioms stage2NoEventParse_tape_unique
#print axioms Stage2NoEventWalkInstance_admitted

end LeanLLVM.Refinement
