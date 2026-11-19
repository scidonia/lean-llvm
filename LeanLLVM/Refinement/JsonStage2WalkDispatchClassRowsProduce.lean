/-
# The class rows' producers, and the supply they still need

`HcontClassRows` (`JsonStage2WalkDispatchClassRows`) is the continuing level's per-class
row group and `HlastClassRows` is the last entry's; the walk's obligation takes both as
`∀ G` premises (`JsonStage2WalkFlushPost`).  This module builds them at the geometry's own
parameters from the groups the tree already has, and states exactly which fields it cannot
build.

## What is produced

| field | producer |
|---|---|
| `HcontClassRows.cleanup` | `hcontCleanupDoc_of_lane`: the document row at the byte's route.  Its two rewrites are the head chain's own — the increment's word (`cont_inc_toNat`) and the index's spelling (`contIx`) — so the class the table marks *document* costs no new supply. |
| `HcontClassRows.run` | `hcontArm_run_of_row`: the class's prefix, the check state's rows and the byte's own leaf below `if.else387.i`, at the arm's own span. |
| `HcontClassRows.seam` | `hcontSeamAbi` from `HcontSeamStaging`.  The five seams are one re-indexing of the staged words: the refusal edge's group is derived (`hcontSeamRefusalOf`), the three emit groups are `hcontSeamKindOf`'s, and the last entry's is `hcontSeamCallsOf`'s at its literal. |
| `HlastClassRows.tail` | `HlastPayload.lane.tail`.  The two are the same `∀`-field: `HlastClassDoc` is `HlastLane.tail`'s type spelled at the class. |

## What is supply, and where it is carried

The rest of both groups is stated as a field of `HcontClassRowsSupply` /
`HlastClassRowsSupply` below, at the field's own type.  Each is a document fact, a
caller-supplied staged word, or a route the tree has not composed:

| field | what it is, and the structure/section that carries it |
|---|---|
| `cleanupRow` | the scan-free class's seam row.  No producer: `HcontSeamStaging`'s fields are the *run* class's seams (`contWsTailStart`, `FS413`, `ClsS413T`, `ClsS58T`) and the last entry's, not `contTailStartByte`'s.  **And the field is uninhabited as stated**: its literal is `0` (`contTailStartOfDoc_pre`'s predecessor `if.else405.i`, `contTailStart_phi`), where no three-call group exists (`HcontSeamRow.not_nonempty_zero` below).  The rows that edge carries are the refusal group's (`HcontSeamRefusal`, `hcontSeamRefusalOf`) and the route is `refuseSeg`'s. |
| `scalar` | the plain-value class's seam row at `scSeamByte … pre.hb`, literal `7`.  Carrier: the class's own staged words at that state (`HcontSeamStage`/`HcontSeamKind`), which the tree does not state at `scSeamByte`; the row's root word is stated at the *head* memory, one transport the staged words do not carry. |
| `scalarRun` | `.value × wsByte`: `HcontScalarWsRow`'s document cells, the byte's class with the run's stop, the seam's cells and the three calls.  Carrier: the document (`JsonStage2WalkHcontWsScalar`'s bundle content); its consumer `hcontArm_scalarRun_of_row` builds the arm from it. |
| `letters` | the letters leaf's seam row.  **Uninhabited as stated**: `LetS413`'s predecessor is `if.else405.i` (`letS413_pre`), the literal `0`, and no three-call group exists there (`HcontSeamRow.not_nonempty_zero`).  The edge's rows are the refusal group's; the route is `refuseSeg`'s. |
| `fLetter` | the `'f'` leaf's seam row at `FS413`, literal `9`.  Carrier: the staged words at that seam (`HcontSeamEmitStage`, whose producer is `hcontSeamCallsOf`), less the head-memory root word. |
| `c56True` | `110`'s leaf at `ClsS413T`, literal `10`.  Same carrier as `fLetter`. |
| `c56Else` | `111 … 115`'s leaf at `ClsS413F`.  **Uninhabited as stated** (literal `0`, refusal edge); the rows are `HcontSeamRefusal`'s. |
| `c58True` | `116`'s leaf at `ClsS58T`, literal `8`.  Same carrier as `fLetter`. |
| `c58Else` | `117 … 125`'s leaf at `HeadS413`.  **Uninhabited as stated** (literal `0`, refusal edge); the rows are `HcontSeamRefusal`'s. |
| `deep` | the positive-depth opener's route: the merge's counted segment and endpoint, or the refusal's witness (`HcontDeepRow`).  No theorem states the merge's segment, so the arm carries it. |
| `runSkip` | the whitespace skip's class (`HcontRunSkip`): the per-index run, the stop and the stop's place in the entry.  The document's content; `HcontRunBody`'s producer (`hcontRunBody_of_skip`) reads it. |
| `runTail` | the run's tail rows (`HcontRunTail`): the landing's byte and reads, the traversal's `hround`/`hbyte`, the appended record.  `hcontRunRow_of_rows` joins it to the row. |
| `refuseSeg` | the kind-`0` refusal route as a priced segment to `if.then` (`HcontClassRows.refuseSeg`'s own statement).  The links are proved individually (`if_then413_i`, `if_then425_i_refuse`, …, `cleanup474_i`); the composition is the class's route, spent by `hcontArm_badToken_of_row`. |
| `HlastClassRows.seam` | the last level's seam at any byte-route tail (`HlastSeam`'s sum).  Carrier: `HcontSeamStage` at `hlastTailByte` and the class's `HlastRefuseRoute`; the producers `hlastSeamRefusal_of_stage`/`hlastSeamZero_of_calls` name the two arms (`JsonStage2WalkDispatchHlastSupply`). |

## The four zero-literal fields cannot be carried as three-call rows

`HcontSeamCalls`'s scalar row demands the emit answer (`hret₂ : r₂.ret = 1`), and
`stage2ScalarValue` answers `0` at `kind = 0` (`s2ScalarValue_refused`;
`hcontSeamCalls_no_kind_zero`, `hcontSeamCalls_no_literal_zero`,
`JsonStage2WalkDispatchSeamCalls`).  So a `HcontSeamRow` whose literal is `0` has no
inhabitant, which the theorem `HcontSeamRow.not_nonempty_zero` below records.  Four of the
group's fields are stated at that literal — `cleanupRow`, `letters`, `c56Else`, `c58Else` —
so they are not merely unwritten supply: as stated they cannot be supplied at all.  The
rows those seams actually carry are the refusal group's (`HcontSeamRefusal`'s two leading
calls, the derived answer and the record) and the class's route is `refuseSeg`'s; the arm
they feed is `hcontArm_badToken_of_row`, not the emit tail.  Restating the four fields is
a change to the frozen field types, so it is left to the structure's owner.
-/
import LeanLLVM.Refinement.JsonStage2WalkDispatchClassRows
import LeanLLVM.Refinement.JsonStage2WalkDispatchSeamCalls
import LeanLLVM.Refinement.JsonStage2WalkDispatchHlastSupply

set_option autoImplicit false

namespace LeanLLVM.Refinement
open LeanLLVM
open LeanLLVM.Refinement.BlockEval
open LeanLLVM.Refinement.JsonStage2IR

namespace WalkScope

/-! ### The continuing group's supply

Every field here is one the tree does not produce, at the field's own type.  The produced
fields — `cleanup`, `run` and `seam` — are not repeated. -/

/-- **The continuing class rows' supply**: the fields of `HcontClassRows` the tree does not
produce, stated at the structure's own parameters.  See the module header for each field's
carrier; four of them (`cleanupRow`, `letters`, `c56Else`, `c58Else`) are stated at the
literal `0` and are refuted by `HcontSeamRow.not_nonempty_zero`. -/
structure HcontClassRowsSupply {m0 : Mem} (G : WalkGeom m0) : Type where
  /-- The scan-free class's seam row, at the byte route's tail start. -/
  cleanupRow : ∀ (C : WalkCarry G) (s : State) (doc : HcontCleanupDoc G C s),
    HcontSeamRow G s (ContTailStartC C)
      (contTailStartByte C s (hlastByte G C) (hlastIncV C) (hlastNepV G) G.ep doc.v
        (contIx G C) (contB35 G doc.v) (hlastByte G C) (hlastByte G C) doc.hb)
      (BitVec.ofNat 32 0)
  /-- The plain-value class's seam row, at the class's own prefix and byte route. -/
  scalar : ∀ (C : WalkCarry G) (s : State) (pre : HcontScalarPrefix G C s),
    HcontSeamRow G s (HeadC₄₁₃ (ContAC₇ C))
      (scSeamByte (sLand C s pre.x pre.inc pre.nep pre.ep pre.v pre.ix pre.b35)
        pre.v.toNat pre.x C.stage.tok pre.b35 pre.hb)
      (BitVec.ofNat 32 7)
  /-- The plain-value class's whitespace-run row. -/
  scalarRun : ∀ (C : WalkCarry G) (s : State), WalkInv G C s → C.block = walkLoopHead →
    C.k + 1 < G.nep → HcontScalarWsRow G C s
  /-- The letters class's seam row, at the head chain's endpoint. -/
  letters : ∀ (C : WalkCarry G) (s : State) {x : BitVec 8} (ch : HcontHeadChain G C s x),
    HcontSeamRow G s (HeadC₄₁₃ (LetC₄₀₅ ch.Cm)) (LetS413 ch.sm x) (BitVec.ofNat 32 0)
  /-- The `'f'` leaf's seam row, at `FS413`. -/
  fLetter : ∀ (C : WalkCarry G) (s : State) {x : BitVec 8} (ch : HcontHeadChain G C s x),
    HcontSeamRow G s (FC₄₁₃ ch.Cm) (FS413 ch.sm x) (BitVec.ofNat 32 9)
  /-- `110`'s leaf seam, at `ClsS413T`. -/
  c56True : ∀ (C : WalkCarry G) (s : State) {x : BitVec 8} (ch : HcontHeadChain G C s x),
    HcontSeamRow G s ({ ClsC₄₀₃ ch.Cm with block := "if.then413.i" }) (ClsS413T ch.sm x)
      (BitVec.ofNat 32 10)
  /-- `111 … 115`'s leaf seam, at `ClsS413F`. -/
  c56Else : ∀ (C : WalkCarry G) (s : State) {x : BitVec 8} (ch : HcontHeadChain G C s x),
    HcontSeamRow G s (HeadC₄₁₃ (ClsC₄₀₅ ch.Cm)) (ClsS413F ch.sm x) (BitVec.ofNat 32 0)
  /-- `116`'s leaf seam, at `ClsS58T`. -/
  c58True : ∀ (C : WalkCarry G) (s : State) {x : BitVec 8} (ch : HcontHeadChain G C s x),
    HcontSeamRow G s ({ HeadC₅₈ ch.Cm with block := "if.then413.i" }) (ClsS58T ch.sm x)
      (BitVec.ofNat 32 8)
  /-- `117 … 125`'s leaf seam, at `HeadS413`. -/
  c58Else : ∀ (C : WalkCarry G) (s : State) {x : BitVec 8} (ch : HcontHeadChain G C s x),
    HcontSeamRow G s (HeadC₄₁₃ ch.Cm) (HeadS413 ch.sm x) (BitVec.ofNat 32 0)
  /-- The positive-depth opener's route row. -/
  deep : ∀ (C : WalkCarry G) (s : State), WalkInv G C s → C.block = walkLoopHead →
    C.k + 1 < G.nep → evalICmp .eq (hlastByte G C) (BitVec.ofNat 8 34) = 1 →
    C.sp ≠ 0 → HcontDeepRow G C s
  /-- The whitespace skip's class. -/
  runSkip : ∀ (C : WalkCarry G) (s : State), WalkInv G C s → C.block = walkLoopHead →
    C.k + 1 < G.nep → (r : HcontDefaultRow G C s) → wsStop G (r.v.toNat - 1) →
    HcontRunSkip G C s r
  /-- The run's tail rows, at the check state the class's prefix builds and the byte's
  leaf. -/
  runTail : ∀ (C : WalkCarry G) (s : State), WalkInv G C s → C.block = walkLoopHead →
    C.k + 1 < G.nep → (r : HcontDefaultRow G C s) → wsStop G (r.v.toNat - 1) →
    (q5 : State) → WalkInv G (HeadAC₄ C) q5 → q5.mem = s.mem →
    (leaf : HcontRunLeaf G C) →
    (b : HcontRunBody G C (contRunCheck G C q5 (hlastIncV C) (hlastNepV G) G.ep r.v
      (contIx G C) (contB35 G r.v))) →
    HcontRunTail G C s r q5 leaf b
  /-- The kind-`0` refusal route, as a priced segment to `if.then`. -/
  refuseSeg : ∀ (C : WalkCarry G) (s : State) (x : BitVec 8),
    WalkInv G C s → C.block = walkLoopHead → C.k + 1 < G.nep →
    evalOperand s (.reg "%8") = some (.int 8 x) →
    (evalICmp .eq x (BitVec.ofNat 8 45) |||
      evalICmp .ult (x + BitVec.ofNat 8 208) (BitVec.ofNat 8 10)) = 0 →
    evalICmp .eq x (BitVec.ofNat 8 102) = 0 →
    evalICmp .eq x (BitVec.ofNat 8 110) = 0 →
    evalICmp .eq x (BitVec.ofNat 8 116) = 0 →
    ∃ (Cd : WalkCarry G) (sd : State) (p : Nat),
      WalkSegment (stage2Calls stage2SubCalls) G C s Cd sd p ∧
      Cd.block = "if.then" ∧
      (∃ k, k ≤ G.n ∧ readBytes sd.mem (Cd.stage.e + 8) 8 = some (wordBytes 8 k)) ∧
      Cd.eoff ≤ G.n ∧
      p + 2 ≤ stage2EntryAllowance * (G.nep - C.k) +
        stage2ByteAllowance * (G.n - entryPos G C.k)

/-! ### The two constructors

The continuing group's `cleanup`, `run` and `seam` are the tree's; the last group's `tail` is
the payload's.  Nothing else is filled in, so the constructor's supply argument is exactly
the list in the header. -/

/-- **The continuing class rows, from the seam's staged words and the supply.**  `seam` is
`hcontSeamAbi`'s at `HcontSeamStaging`, `cleanup` is the default row's document fact, and
`run` is the arm's producer at the row.  Every other field is the supply's. -/
noncomputable def hcontClassRows_of_supply {m0 : Mem} (G : WalkGeom m0)
    (hs : HcontSeamStaging G) (sup : HcontClassRowsSupply G) : HcontClassRows G where
  cleanup := fun _C _s _hInv _hblock hk r hb => hcontCleanupDoc_of_lane hk r hb
  cleanupRow := sup.cleanupRow
  scalar := sup.scalar
  scalarRun := sup.scalarRun
  letters := sup.letters
  fLetter := sup.fLetter
  c56True := sup.c56True
  c56Else := sup.c56Else
  c58True := sup.c58True
  c58Else := sup.c58Else
  deep := sup.deep
  runSkip := sup.runSkip
  runTail := sup.runTail
  run := fun _C _s hInv hblock hk row {_nS} hSpan hnS =>
    ⟨hcontArm_run_of_row hInv hblock hk row hSpan hnS⟩
  seam := hcontSeamAbi G hs
  refuseSeg := sup.refuseSeg

/-- **The continuing class rows at every geometry**, in the shape the walk's obligation
takes: `∀ G, HcontClassRows G`, from the staged words and the supply. -/
noncomputable def hcontClassRows_of_supply_all
    (hs : ∀ {m0 : Mem} (G : WalkGeom m0), HcontSeamStaging G)
    (sup : ∀ {m0 : Mem} (G : WalkGeom m0), HcontClassRowsSupply G) :
    ∀ {m0 : Mem} (G : WalkGeom m0), HcontClassRows G :=
  fun {m0} (G : WalkGeom m0) => hcontClassRows_of_supply G (hs G) (sup G)

/-- **The last entry's class rows' supply**: the last level's seam at any byte-route tail.
The document row is the payload's, so it is not repeated. -/
structure HlastClassRowsSupply {m0 : Mem} (G : WalkGeom m0) : Type where
  /-- The last level's seam, at the byte route's tail: `HlastSeam`'s sum, whose literal is
  the class's (`0` at `%8 ∈ {126, 127}` — the refusal arm — and `s2_value_pos`'s own zero
  answer is the other arm). -/
  seam : ∀ (C : WalkCarry G) (s : State) (x : BitVec 8) (inc nep : BitVec 64)
    (v : Nat) (ix : BitVec 64) (b35 : UInt8)
    (hb : HcontByteRoute (head35 b35)),
    HlastSeam G (TailStartC C) (hlastTailByte C s x inc nep v ix b35 hb)

/-- **The last entry's class rows, from the payload and the seam supply.**  `tail` is
`HlastPayload.lane.tail`'s field — the same `∀`-field at the class — so the only supply is
the seam. -/
def hlastClassRows_of_supply {m0 : Mem} (G : WalkGeom m0) (hp : HlastPayload G)
    (sup : HlastClassRowsSupply G) : HlastClassRows G where
  tail := hp.lane.tail
  seam := sup.seam

/-- **The last entry's class rows at every geometry**. -/
def hlastClassRows_of_supply_all
    (hp : ∀ {m0 : Mem} (G : WalkGeom m0), HlastPayload G)
    (sup : ∀ {m0 : Mem} (G : WalkGeom m0), HlastClassRowsSupply G) :
    ∀ {m0 : Mem} (G : WalkGeom m0), HlastClassRows G :=
  fun {m0} (G : WalkGeom m0) => hlastClassRows_of_supply G (hp G) (sup G)

/-! ### The zero-literal obstruction

`HcontSeamCalls` carries the emit arm's answer, so no seam group exists at a store of `0`
(`hcontSeamCalls_no_literal_zero`).  A `HcontSeamRow` names that group *and* the literal, so
the structure is empty at `0`: this is the theorem that makes the four fields in the header
uninhabited as stated rather than merely unwritten. -/

/-- **No seam row exists at the literal `0`.**  The row's `hcA` fixes the calls' stored
literal to `0`, and the scalar call's emit answer is impossible there
(`hcontSeamCalls_no_literal_zero`). -/
theorem HcontSeamRow.not_nonempty_zero {m0 : Mem} {G : WalkGeom m0} {s : State}
    {Cp : WalkCarry G} {sp : State} :
    ¬ Nonempty (HcontSeamRow G s Cp sp (BitVec.ofNat 32 0)) := by
  rintro ⟨r⟩
  exact hcontSeamCalls_no_literal_zero r.calls r.hcA

/-! ### The instrument -/

#print axioms LeanLLVM.Refinement.WalkScope.hcontClassRows_of_supply
#print axioms LeanLLVM.Refinement.WalkScope.hcontClassRows_of_supply_all
#print axioms LeanLLVM.Refinement.WalkScope.hlastClassRows_of_supply
#print axioms LeanLLVM.Refinement.WalkScope.hlastClassRows_of_supply_all
#print axioms LeanLLVM.Refinement.WalkScope.HcontSeamRow.not_nonempty_zero

end WalkScope
end LeanLLVM.Refinement
