/-
The conservative `_plain` shipping path, as a contract.

`kernel/json/pipeline_fast_plain.c` is the split-stage-1 candidate: a per-block
`leanllvm_json_s1_masks` sweep that collects one entry word per 64-byte block
into the caller's `ent` array, one `leanllvm_json_entry_pos8`/`_b8` call over
that array, the `leanllvm_json_utf8` verdict, and the unchanged
`leanllvm_json_stage2` with no escape list (`nxp = 0`).  The default
`leanllvm_json_pipeline` at `arm == 0` composes the same three certified units
but calls the emitter once per block.  The two shapes emit the same stream, and
the difference between them is a re-association, not a second algorithm.

This module states that equivalence and the route it supports, at the three
levels the certified modules already provide:

* **the stage-1 composition** — for the collected words the loop computes, one
  emitter call over the `ent` array is the per-block fold.  `plainStage1_words`
  is the loop's word identity (`collectWords_eq`), `plainStage1_fold` is the
  array's cursor and stream (`perBlockFold_eq`, `perBlockFold`), and
  `plainStage1_pos8`/`plainStage1_b8` are the one-call run at the emitter's own
  refinery (`pf_plain_spec`/`pf_plain_spec_b8`).  Nothing here re-executes a unit
  body: each statement is the certified unit's conclusion at the plain shape.
* **the staging the plain shape adds** — the `ent` array is one word per block
  (`plainEntBytes`), which the route's `entw` scratch (one word) does not
  reserve.  `PlainEntStaged` states the array's presence; the route's staging
  passing it unchanged is recorded as the open obligation below, not assumed.
* **the route-level theorem** — `plain_routePost` reads the certified assembled
  body at the route's staging and concludes `routePost`, the route's own post,
  unchanged.  Its stage-2 member is the certified one, and the one contractual
  premise it names that the list-path proof did not need is the no-list
  `s2_string_body` arm, `NoListStringBodyContract`.

**The no-list premise and its owner.**  `NoListStringBodyContract` is the
statement of `LeanLLVM.Refinement.JsonStage2StringBodyNoList.s2StringBodyArm_noList`
(owner: `ProofNoList`), verbatim: the string body's `nxp = 0` scan arm concludes
the string body's contract at `s2StringBodyConcludes`/`s2StringBodyBudget`'s
shape.  That module and its `.olean`
(`.lake/build/lib/lean/LeanLLVM/Refinement/JsonStage2StringBodyNoList.olean`)
are not in this tree yet, so the theorem carries the arm as a hypothesis; it is
not imported, restated at a weaker form, or assumed proved.

**What remains after this pass** (all named where they are used):

1. the module's `.olean` landing, which turns `PlainStage2.noList` from a field
   into a discharged premise;
2. the plain body's `Satisfies`.  The bench-only body is now at the certified
   pipeline's own twenty-slot ABI and has no `alloca`
   (`kernel/json/pipeline_fast_plain.c`'s `pf_plain_pipeline`), and
   `probes/install/ir/pipeline_fast_plain.candidate.ll` is its captured
   emission; `plainShapeOk` pins the fixture's one-function/twenty-slot/ten-block
   shape.  The remaining body work is the AST transcription and the run: the
   mask loop's fold into `ent`, the one emitter call over it (`plainStage1_pos8`),
   the UTF-8 gate, the stage-2 call, and the `pipelineUnitsPost` composition;
3. the plain record itself: `PlainRoutePre` adds `PlainEntArray`, and the post's
   frame substitutes `plainFrameEntry` for the default's `(entw, 8)`.  A full
   `PlainRoutePost` is `pipelineUnitsPost` with that one entry replaced (the
   mechanical copy is the next pass); `pipelineRegions`'s `(entw, 8)` widens the
   same way;
4. the escape list's arm: the plain shape passes `xp`/`nxp` through unchanged,
   which is the route's `arm == 0` contract and not a new clause.
-/
import LeanLLVM.Refinement.JsonPipelineFastStage1
import LeanLLVM.Refinement.PipelineDischarge
import LeanLLVM.JsonCallRoute
import LeanLLVM.Refinement.JsonStage2StringBodyJoin
import LeanLLVM.Parser

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace LeanLLVM.Refinement

open LeanLLVM
open LeanLLVM.JSON
open LeanLLVM.Refinement.JsonEntryIR
open LeanLLVM.Refinement.JsonEntrySteps
open LeanLLVM.Refinement.JsonB8Steps
open LeanLLVM.Refinement.JsonScanSpec
open LeanLLVM.Refinement.JsonS1MasksIR
open LeanLLVM.Refinement.BitLanes
open LeanLLVM.Refinement.JsonPipelineFastStage1
open LeanLLVM.Refinement.JsonPipelineIR
open LeanLLVM.Refinement.BlockEval (stateAt cells)
open LeanLLVM.Refinement.JsonPipelineBlockEval (litv)

/-! ### The entry array's extent -/

/-- The plain shape's `ent` array: one 64-bit word per 64-byte block.  The
default route stages `entw` as a single word because it calls the emitter once
per block; the plain shape reads the whole array in one call, so its extent is
the block count. -/
def plainEntBytes (n : Nat) : Nat := 8 * pipelineBlocks n

/-- The plain shape's `ent` array is staged at `ent`, as the block sequence's
words.  This is the region the route's `entw` scratch does not reserve; the
route theorem below does not assume it (the certified body it reads uses the
route's own staging), and the obligation is recorded rather than discharged. -/
def PlainEntStaged (ent n : Nat) (mem : Mem) (words : List (BitVec 64)) : Prop :=
  readBytes mem ent (plainEntBytes n) = some (wordsOf words) ∧
    words.length = pipelineBlocks n

/-- The extent's definition, read at the block count. -/
theorem plainEntBytes_eq (n : Nat) : plainEntBytes n = 8 * pipelineBlocks n := rfl

/-- A non-empty document's array is non-empty: the block count of a positive
length is positive, so the plain shape's staged array has at least one word. -/
theorem plainEntBytes_pos {n : Nat} (h : 0 < n) : 0 < plainEntBytes n := by
  simp only [plainEntBytes]
  have hk : 0 < pipelineBlocks n := by
    unfold pipelineBlocks
    exact Nat.div_pos (by omega) (by decide)
  omega

/-! ### The stage-1 composition

The loop's word identity, the array's fold, and the one-call run.  Each is the
certified statement at the plain shape; the first two are the model facts the
fused pass also uses, and the last two are the emitter's own refinery. -/

/-- **The loop's collected words are the default's per-block words.**
`collectWords` is the plain pass's `S`/`e` line (the classifier words are the
specification's, by `s1_masks_refines`), and `specWords` is `entryMask64` at each
block's state and previous top lane.  The carries evolve identically, so the
arrays agree word for word. -/
theorem plainStage1_words (blocks : List (Block32 × Block32)) (st : ClassState)
    (prevS : Bool) :
    (collectWords blocks st prevS).1 = specWords blocks st prevS :=
  collectWords_eq blocks st prevS

/-- **The array's cursor and stream are the one call's model.**  The per-block
fold at the collected array is the cursor plus the array's population count and
the stream prefix at the whole array; `perBlockFold_eq` is that identity. -/
theorem plainStage1_fold (ent : List (BitVec 64)) (blk0 k : Nat) :
    perBlockFold ent (64 * blk0) k =
      (k + (ent.map ctpop).sum, streamPrefix ent blk0 ent.length) :=
  perBlockFold_eq ent blk0 k

/-- **The plain POS8 entry is the per-block fold.**  One `entryPos8Function` call
over the array returns the cursor and appends the stream the per-block calls
compose: `pf_plain_spec` at the array's own length. -/
theorem plainStage1_pos8 (ent : List (BitVec 64)) (blk0 nblk k : Nat) (mem : Mem)
    (e o tab outCap : Nat)
    (hnblk : nblk = ent.length)
    (hblk : 64 * (blk0 + nblk) + 63 < 2 ^ 32)
    (hent : readBytes mem e (8 * ent.length) = some (wordsOf ent))
    (htab : readBytes mem tab 8192 = some pos8Table)
    (hdisjP : (e + 8 * ent.length ≤ o ∨ o + 4 * (k + 64 * ent.length + 8) ≤ e) ∧
              (tab + 8192 ≤ o ∨ o + 4 * (k + 64 * ent.length + 8) ≤ tab))
    (hcap : k + 64 * ent.length + 9 ≤ outCap)
    (hk63 : k + 64 * ent.length + 9 < 2 ^ 63) :
    ∃ (k' : Nat) (m' : Mem),
      runFuel entryCalls (3 * nblk + 3) entryPos8Function
        { (initState entryPos8Function
            [.ptr e, .int 64 blk0, .int 64 nblk, .ptr o, .int 64 k, .ptr tab])
          with mem := mem }
        = some (.ret (some (.int 64 (BitVec.ofNat 64 k'))) m') ∧
      perBlockFold ent (64 * blk0) k =
        (k', streamPrefix ent blk0 nblk) ∧
      k' = k + (ent.map ctpop).sum ∧
      readLanes32 m' (o + 4 * k) (k' - k) = streamPrefix ent blk0 nblk :=
  pf_plain_spec ent blk0 nblk k mem e o tab outCap hnblk hblk hent htab hdisjP
    hcap hk63

/-- **The plain B8 entry is the per-block fold.**  The same array shape with the
B8 emitter's fuel and no table or capacity premise. -/
theorem plainStage1_b8 (ent : List (BitVec 64)) (blk0 nblk k : Nat) (mem : Mem)
    (e o : Nat)
    (hnblk : nblk = ent.length)
    (hblk : 64 * (blk0 + nblk) + 63 < 2 ^ 32)
    (hent : readBytes mem e (8 * ent.length) = some (wordsOf ent))
    (hdisj : e + 8 * ent.length ≤ o ∨ o + 4 * (k + 64 * ent.length + 8) ≤ e)
    (hk63 : k + 64 * ent.length + 9 < 2 ^ 63) :
    ∃ (k' : Nat) (m' : Mem),
      runFuel entryCalls (b8RunSteps ent + nblk + 2) entryB8Function
        { (initState entryB8Function
            [.ptr e, .int 64 blk0, .int 64 nblk, .ptr o, .int 64 k])
          with mem := mem }
        = some (.ret (some (.int 64 (BitVec.ofNat 64 k'))) m') ∧
      perBlockFold ent (64 * blk0) k =
        (k', streamPrefix ent blk0 nblk) ∧
      k' = k + (ent.map ctpop).sum ∧
      readLanes32 m' (o + 4 * k) (k' - k) = streamPrefix ent blk0 nblk :=
  pf_plain_spec_b8 ent blk0 nblk k mem e o hnblk hblk hent hdisj hk63

/-! ### The no-list string body

The conservative plain shape hands stage 2 no escape list.  Stage 2's string body
then scans the body's own span instead of indexing the list; that arm is the one
contract this route names that the list-path proof did not need. -/

/-- **The no-list `s2_string_body` arm**, as `ProofNoList` states it
(`LeanLLVM.Refinement.JsonStage2StringBodyNoList.s2StringBodyArm_noList`, not yet
landed).  A concrete `mem`/args fact: at the staged body state, with `nxp = 0`,
the body concludes its contract at eight fuel, with the post and footprint
`s2StringBodyPost`/`s2StringBodyFoot` name.  The seventeen premises are the
staging's: the cursor word, the body's bytes, the error pointer, the 64-bit
address bounds, the length's one-away bound, the zero count, the three presence
reads and the six region separations. -/
def NoListStringBodyContract : Prop :=
  ∀ {mem : Mem} {next c p dst outn xp xj : Nat}
    {len nxp : BitVec 64} {base : Nat} {body : List UInt8} {e : Nat},
    stage2ReadWord mem c 8 = some base →
    readBytes mem p len.toNat = some body →
    stage2ReadWord mem (c + 1112) 8 = some e →
    p < 2 ^ 64 → base ≤ p → p - base + len.toNat < 2 ^ 64 →
    len.toNat + 1 < 2 ^ 63 → nxp.toNat = 0 →
    readBytes mem outn 8 ≠ none →
    readBytes mem dst len.toNat ≠ none →
    readBytes mem e stage2ErrorExtent ≠ none →
    RegionsApart next 8 dst len.toNat →
    RegionsApart next 8 outn 8 →
    RegionsApart next 8 e stage2ErrorExtent →
    RegionsApart next 8 p len.toNat →
    RegionsApart dst len.toNat p len.toNat →
    RegionsApart next 8 (c + 1112) 8 →
    s2StringBodyConcludes
      [.ptr c, .ptr p, .int 64 len, .ptr dst, .ptr outn, .ptr xp, .ptr xj,
        .int 64 nxp] mem next 8
      (stagedState s2StringBodyBody
        [.ptr c, .ptr p, .int 64 len, .ptr dst, .ptr outn, .ptr xp, .ptr xj,
          .int 64 nxp] mem next)

/-! ### The stage-2 premise

The certified walk's five payload groups, plus the no-list arm the plain shape
requires.  The groups are the certified theorem's own hypotheses; the no-list arm
is the contract `ProofNoList` owns.  Bundling them keeps the route theorem's
premise one object and keeps the dependency visible. -/

/-- The stage-2 side of the conservative plain route: the walk's five payload
groups at `Γ_stage2work` and the no-list string-body arm.  The groups are
`pipeline_satisfies_at_stage2_of_exitStage2`'s hypotheses; the arm is the plain
shape's additional requirement. -/
structure PlainStage2 (tab : Nat) where
  /-- The no-list string body, `ProofNoList`'s `s2StringBodyArm_noList`. -/
  noList : NoListStringBodyContract
  hcont : ∀ {m0 : Mem} (G : WalkGeom m0), WalkScope.HcontPayload G
  hrows : ∀ {m0 : Mem} (G : WalkGeom m0), WalkScope.HcontClassRows G
  hlast : ∀ {m0 : Mem} (G : WalkGeom m0), WalkScope.HlastPayload G
  hlastRows : ∀ {m0 : Mem} (G : WalkGeom m0), WalkScope.HlastClassRows G
  hlastArms : ∀ {m0 : Mem} (G : WalkGeom m0), WalkScope.HlastArmRows G

/-! ### The route's post, from the record -/

/-- **A returning outcome of the pipeline record has the ABI's shape.**  The
record's post is false for `ub`, for a valueless return and for a value of any
width but 64; so a returning run it admits returns `some (.int 64 verdict)`. -/
theorem pipelineUnitsPost_return {args : List Value} {mem : Mem} {next : Nat}
    {o : Outcome} (h : pipelineUnitsPost args mem next o) :
    ∃ (verdict : BitVec 64) (m : Mem), o = .ret (some (.int 64 verdict)) m := by
  unfold pipelineUnitsPost at h
  split at h
  · exact absurd h (by simp)
  · rename_i verdict m
    exact ⟨verdict, m, rfl⟩
  · exact absurd h (by simp)

/-- **The record at the route's staging yields the route's post.**  `Satisfies`
at `Γ_pipeline_units` runs the body from the staging the route builds
(`routeSpecPre` supplies `Γ_pipeline_units.pre`), and its post is `routePost` by
definition.  The budget is the record's own, `pipelineBudget`. -/
theorem routePost_of_satisfies {base : Nat} {s2 : Calls} {l : RouteLayout}
    {doc : List UInt8}
    (h : Satisfies (pipelineCalls l.tab base s2) pipelineBody (Γ_pipeline_units l.tab base))
    (hbase : l.base = base) (hpre : routePre l doc) :
    ∃ (verdict : BitVec 64) (m : Mem),
      runFuel (pipelineCalls l.tab base s2)
        (pipelineBudget (routeArgs l doc) (stagedMem l doc))
        pipelineBody
        (EntryState pipelineBody (routeArgs l doc) (stagedMem l doc) (routeNext l doc))
        = some (.ret (some (.int 64 verdict)) m) ∧
      routePost l doc (routeNext l doc) (.ret (some (.int 64 verdict)) m) := by
  cases hbase
  obtain ⟨hst, hbelow, hwork, _⟩ := routeSpecPre l doc hpre
  have hpre' : (Γ_pipeline_units l.tab l.base).pre
      (routeArgs l doc) (stagedMem l doc) (routeNext l doc) :=
    ⟨hst, hbelow, hwork⟩
  obtain ⟨⟨v, m, hrun⟩, hpost⟩ :=
    h (routeArgs l doc) (stagedMem l doc) (routeNext l doc) hpre'
  have hbeh : BehFromState (pipelineCalls l.tab l.base s2) pipelineBody
      (EntryState pipelineBody (routeArgs l doc) (stagedMem l doc) (routeNext l doc))
      (.ret v m) := Or.inr ⟨_, hrun⟩
  have hpf := hpost (.ret v m) hbeh
  have hpf' : pipelineUnitsPost (routeArgs l doc) (stagedMem l doc)
      (routeNext l doc) (.ret v m) := by
    simpa only [Γ_pipeline_units] using hpf
  obtain ⟨verdict, m', hshape⟩ := pipelineUnitsPost_return hpf'
  cases hshape
  exact ⟨verdict, m, by simpa only [Γ_pipeline_units] using hrun, hpf'⟩

/-- **The record at the route's staging, for an arbitrary body.**  The
composition `routePost_of_satisfies` at an opaque `calls`/`f` pair: the staging
is the route's, the post is `Γ_pipeline_units`'s, and the body is whatever the
caller supplies.  This is the shape a pinned plain body plugs into once its
`Satisfies` (at the widened record) is in hand. -/
theorem routePost_of_satisfies_gen {base : Nat} {calls : Calls} {f : Function}
    {l : RouteLayout} {doc : List UInt8}
    (h : Satisfies calls f (Γ_pipeline_units l.tab base))
    (hbase : l.base = base) (hpre : routePre l doc) :
    ∃ (verdict : BitVec 64) (m : Mem),
      runFuel calls (pipelineBudget (routeArgs l doc) (stagedMem l doc)) f
        (EntryState f (routeArgs l doc) (stagedMem l doc) (routeNext l doc))
        = some (.ret (some (.int 64 verdict)) m) ∧
      routePost l doc (routeNext l doc) (.ret (some (.int 64 verdict)) m) := by
  cases hbase
  obtain ⟨hst, hbelow, hwork, _⟩ := routeSpecPre l doc hpre
  have hpre' : (Γ_pipeline_units l.tab l.base).pre
      (routeArgs l doc) (stagedMem l doc) (routeNext l doc) :=
    ⟨hst, hbelow, hwork⟩
  obtain ⟨⟨v, m, hrun⟩, hpost⟩ :=
    h (routeArgs l doc) (stagedMem l doc) (routeNext l doc) hpre'
  have hbeh : BehFromState calls f
      (EntryState f (routeArgs l doc) (stagedMem l doc) (routeNext l doc))
      (.ret v m) := Or.inr ⟨_, hrun⟩
  have hpf := hpost (.ret v m) hbeh
  have hpf' : pipelineUnitsPost (routeArgs l doc) (stagedMem l doc)
      (routeNext l doc) (.ret v m) := by
    simpa only [Γ_pipeline_units] using hpf
  obtain ⟨verdict, m', hshape⟩ := pipelineUnitsPost_return hpf'
  cases hshape
  exact ⟨verdict, m, by simpa only [Γ_pipeline_units] using hrun, hpf'⟩

/-! ### The conservative plain route -/

/-- **The conservative plain route.**  The certified assembled body at
`Γ_pipeline_units` — `pipeline_satisfies_at_stage2_of_exitStage2`'s conclusion —
read at the route's own staging, satisfies `routePost`.  The stage-1 side is the
plain composition (`plainStage1_words`, `plainStage1_fold`,
`plainStage1_pos8`/`_b8`); the stage-2 side is the certified walk plus the no-list
arm the plain shape requires.  The post, the staging and the route are the
default route's, unchanged. -/
theorem plain_routePost {l : RouteLayout} (h2 : PlainStage2 l.tab)
    {doc : List UInt8} (hpre : routePre l doc) :
    ∃ (verdict : BitVec 64) (m : Mem),
      routePost l doc (routeNext l doc) (.ret (some (.int 64 verdict)) m) := by
  have hsat : ∀ base, Satisfies
      (pipelineCalls l.tab base (WalkScope.envForStage2Work l.tab stage2SubCalls))
      pipelineBody (Γ_pipeline_units l.tab base) :=
    pipeline_satisfies_at_stage2_of_exitStage2 l.tab
      h2.hcont h2.hrows h2.hlast h2.hlastRows h2.hlastArms
  obtain ⟨verdict, m, _, hpost⟩ :=
    routePost_of_satisfies (hsat l.base) rfl hpre
  exact ⟨verdict, m, hpost⟩

/-! ### The plain body's `ent` staging and the route pre/post delta

The captured plain body (`probes/install/ir/pipeline_fast_plain.candidate.ll`)
reads its third argument as the `(n + 63) / 64`-word entry array, not as the
default's one-word `entw` scratch.  The route's staging and post therefore differ
at exactly one region: `(entw, 8)` becomes `(entw, 8 * pipelineBlocks n)`.

* the pre adds `PlainEntArray` — the array is readable at its plain extent from
  `l.entw`; `pipelineStaging`'s own `entw` clause stages only eight bytes;
* the post's `UnchangedOutside` list widens `(entw, 8)` to `plainEntRegion`, so
  `pipelineUnitsPost` as stated is *false* for the plain body past `entw + 8`;
  the plain route's post is `pipelineUnitsPost` with that one entry replaced;
* `pipelineRegions`'s `(entw, 8)` entry widens the same way.

Nothing else in the pre or the post changes: the `ep` capacity already carries
`64 * pipelineBlocks n + 9`, and the stage-2, utf8 and output regions are the
default's.  The body also allocates its two stage-1 slots as struct locals
(`%sc` 24 B, `%m` 48 B) and zeroes them with `llvm.memset`; the parser's `Ty`
has no struct types and `pipelineBody` has no `alloca`, so pinning the body and
proving its `Satisfies` needs a stack region and intrinsic modelling.  That gap
and the whole-body induction are the remaining body obligations, not clauses of
this module. -/

/-- The region the plain body reads its entry array from: the route's `entw`
slot at one word per block. -/
def plainEntRegion (l : RouteLayout) (doc : List UInt8) : Nat × Nat :=
  (l.entw, plainEntBytes doc.length)

/-- The region's width, at the route's document length. -/
theorem plainEntRegion_eq (l : RouteLayout) (doc : List UInt8) :
    plainEntRegion l doc = (l.entw, 8 * pipelineBlocks doc.length) := rfl

/-- For a non-empty document the plain region is strictly wider than the
default's eight-byte scratch: the widening extends the route's region and does
not replace a same-width one. -/
theorem plainEntRegion_wider {l : RouteLayout} {doc : List UInt8}
    (h : 0 < doc.length) : 8 ≤ (plainEntRegion l doc).2 := by
  simp only [plainEntRegion, plainEntBytes]
  have hk : 0 < pipelineBlocks doc.length := by
    unfold pipelineBlocks
    exact Nat.div_pos (by omega) (by decide)
  omega

/-- The plain pre's one additional clause: the entry array is staged at its
`8 * pipelineBlocks n` extent from the route's `entw` slot.  The default
`pipelineStaging` stages eight bytes there, so this is the pre delta. -/
def PlainEntArray (l : RouteLayout) (doc : List UInt8) : Prop :=
  readBytes (stagedMem l doc) l.entw (plainEntBytes doc.length) ≠ none

/-- The route's precondition for the plain body: the default's `routePre` plus
the entry array's plain extent.  This is the *only* pre difference; every other
clause (document admission, capacities, separation, cursors) is the default's. -/
def PlainRoutePre (l : RouteLayout) (doc : List UInt8) : Prop :=
  routePre l doc ∧ PlainEntArray l doc

/-- The plain pre contains the default's: a caller that stages the array also
meets every default clause. -/
theorem plainRoutePre_routePre {l : RouteLayout} {doc : List UInt8}
    (h : PlainRoutePre l doc) : routePre l doc := h.1

/-- The route post's one changed frame entry: the default names `(entw, 8)`, the
plain body writes the whole array.  A post that leaves `(entw, 8)` unchanged
while the body writes past it is false, which is why the plain post substitutes
this entry. -/
def plainFrameEntry (l : RouteLayout) (doc : List UInt8) : Nat × Nat :=
  plainEntRegion l doc

/-- The substituted entry is the array's region, at the plain extent. -/
theorem plainFrameEntry_eq (l : RouteLayout) (doc : List UInt8) :
    plainFrameEntry l doc = (l.entw, 8 * pipelineBlocks doc.length) := rfl

/-! ### The route's entry stream is the plain composition's -/

/-- **The route post's entry stream is a readable stream at its own cursor.**
`pipelineUnitsPost` reads `nk'` at the count slot and the lanes `[0, nk')` at the
entry buffer; the plain shape's one emitter call writes exactly those lanes
(`plainStage1_pos8`/`_b8`'s `readLanes32` clause).  This is the projection the
route's caller reads, and it is the field the plain stage-1 composition lands
in. -/
theorem plain_route_ent {l : RouteLayout} {doc : List UInt8} {next : Nat}
    {verdict : BitVec 64} {m : Mem}
    (h : routePost l doc next (.ret (some (.int 64 verdict)) m)) :
    ∃ (nk' : Nat) (ent : List Nat),
      readBytes m l.nk 8 = some (wordBytes 8 nk') ∧
      readLanes32 m l.ep nk' = some ent := by
  simp only [routePost, pipelineUnitsPost, routeArgs] at h
  obtain ⟨-, nk', nxp', ndstU, ndst', nev', ent, ps, out, evs,
    c, ctype, cst, tok, s, z, e, d, alloc, allocEnd,
    hle, hout, hnk, hnxp, hlanes, hrest⟩ := h
  exact ⟨nk', ent, hnk, hlanes⟩


/-! ### The plain record and the body's obligation -/

/-- The plain body's argument list carries the entry array in the `entw` slot.
This clause says the array is readable at its `8 * pipelineBlocks n` extent; it
is the pre half of the widening. -/
def EntArrayStaged (args : List Value) (mem : Mem) : Prop :=
  match args with
  | [.ptr _, .int 64 n, .ptr _, .ptr _, .ptr ent, .ptr _, .int 64 _, .ptr _,
     .ptr _, .int 64 _, .ptr _, .ptr _, .ptr _, .int 64 _, .ptr _, .ptr _,
     .int 64 _, .ptr _, .ptr _, .int 64 _] =>
      readBytes mem ent (plainEntBytes n.toNat) ≠ none
  | _ => False

def pipelinePlainPost (args : List Value) (mem : Mem) (_next : Nat)
    (o : Outcome) : Prop :=
  match o with
  | .ub => False
  | .ret (some (.int 64 verdict)) m =>
      match args with
      | [.ptr _, .int 64 n, .ptr sc, .ptr mk, .ptr entw, .ptr ep, .int 64 _,
         .ptr nk, .ptr xp, .int 64 _, .ptr nxp, .ptr xcarry, .ptr dst, .int 64 _,
         .ptr ndst, .ptr ev, .int 64 _, .ptr nev, .ptr err, .int 64 _] =>
          (verdict = 0 ∨ verdict = 1) ∧
          ∃ (nk' nxp' ndstU ndst' nev' : Nat) (ent : List Nat) (ps : List Nat)
            (out evs : List UInt8) (c ctype cst tok s z e d alloc allocEnd : Nat),
            ndstU ≤ ndst' ∧
            pipelineOutputExtents args o ndstU nev' ∧
            readBytes m nk 8 = some (wordBytes 8 nk') ∧
            readBytes m nxp 8 = some (wordBytes 8 nxp') ∧
            readLanes32 m ep nk' = some ent ∧
            readBytes m xp (4 * nxp') = some (positionsBytes 4 ps) ∧
            readBytes m dst ndstU = some out ∧
            readBytes m ev nev' = some evs ∧
            (verdict = 0 →
              ∃ e : Nat, readBytes m err 8 = some (wordBytes 8 e)) ∧
            (verdict = 1 → readBytes m err 8 = readBytes mem err 8) ∧
            alloc ≤ allocEnd ∧
            UnchangedOutside mem m
              (([(sc, 24), (mk, 48), (entw, plainEntBytes n.toNat), (ep, 4 * (nk' + 8)), (nk, 8),
                 (xp, 4 * (nxp' + batchReserve)), (nxp, 8), (xcarry, 16),
                 (dst, ndst' + 64), (ndst, 8), (ev, nev'), (nev, 8), (err, 8)] ++
                stage2ReportScratch c ctype cst tok s z e d) ++
                [(alloc, allocEnd - alloc)])
      | _ => False
  | _ => False

/-- The plain body's record: the default's budget and pre, plus the array's
staged extent, and `pipelinePlainPost` — `pipelineUnitsPost` with the one frame
entry `(entw, 8)` replaced by `(entw, 8 * pipelineBlocks n)`. -/
def plainContract (tab base : Nat) : MemContract where
  budget := pipelineBudget
  pre := fun args mem next =>
    (Γ_pipeline_units tab base).pre args mem next ∧ EntArrayStaged args mem
  post := pipelinePlainPost

/-- **The plain body's obligation**, stated at the widened record.  `body` is
the captured `@pf_plain_pipeline` (the certified twenty-slot ABI, ten blocks:
the mask loop, the `ent` array, one emitter call, the UTF-8 gate, the stage-2
call); `calls` is the pipeline's call environment with the no-list stage-2
selection.  The run that discharges this is the remaining body pass; this module
states it and supplies the stage-1 model it consumes. -/
def PlainBodySatisfies (body : Function) (calls : Calls) (tab base : Nat) : Prop :=
  Satisfies calls body (plainContract tab base)

/-! ### The capture pin

The emitted body of `probes/install/ir/pipeline_fast_plain.candidate.ll` is the
pin target for the plain body's `Satisfies`.  The guard below checks the shape
the statement needs: one function, the certified ABI's twenty slots, and the
plain shape's ten blocks.  `plainSrc_control` is the discriminating control — a
malformed copy — so the guard is known to reject a text that does not parse. -/

/-- The plain body's emission, as committed. -/
def plainSrc : String :=
  include_str "../../probes/install/ir/pipeline_fast_plain.candidate.ll"

/-- The shape the body pin needs: one definition at the certified ABI's twenty
slots and ten blocks. -/
def plainShapeOk (src : String) : Bool :=
  match parseModule src with
  | .ok m =>
      m.functions.length == 1 &&
      (match m.functions.head? with
       | some f => f.params.length == 20 && f.blocks.length == 10
       | none => false)
  | .error _ => false

/-- The control: the same text with a terminator's target corrupted.  It must
not answer `true`, or the guard matches text it does not read. -/
def plainSrc_control : String :=
  plainSrc.replace "br i1 %cmp61.not, label" "br i1 %cmp61.not label"

#guard plainShapeOk plainSrc

#guard !plainShapeOk plainSrc_control


/-! ### The body, pinned

The transcribed `@pf_plain_pipeline`, exactly the parser's own result on the
committed fixture.  The transcription is the parser's `Repr` output, so the
`#guard` below is the pin: a change to either the fixture or this literal that
the other does not carry fails elaboration. -/

/-- The plain body: `@pf_plain_pipeline`'s ten blocks. -/
def plainBody : Function :=
{ name := "pf_plain_pipeline",
  retTy := LeanLLVM.Ty.int 64,
  params := [("%b", LeanLLVM.Ty.ptr),
             ("%n", LeanLLVM.Ty.int 64),
             ("%sc", LeanLLVM.Ty.ptr),
             ("%mk", LeanLLVM.Ty.ptr),
             ("%ent", LeanLLVM.Ty.ptr),
             ("%ep", LeanLLVM.Ty.ptr),
             ("%epcap", LeanLLVM.Ty.int 64),
             ("%nk", LeanLLVM.Ty.ptr),
             ("%xp", LeanLLVM.Ty.ptr),
             ("%xpcap", LeanLLVM.Ty.int 64),
             ("%nxp", LeanLLVM.Ty.ptr),
             ("%xcarry", LeanLLVM.Ty.ptr),
             ("%dst", LeanLLVM.Ty.ptr),
             ("%dstcap", LeanLLVM.Ty.int 64),
             ("%ndst", LeanLLVM.Ty.ptr),
             ("%ev", LeanLLVM.Ty.ptr),
             ("%evcap", LeanLLVM.Ty.int 64),
             ("%nev", LeanLLVM.Ty.ptr),
             ("%err", LeanLLVM.Ty.ptr),
             ("%arm", LeanLLVM.Ty.int 64)],
  blocks := [{ name := "entry",
               instrs := [LeanLLVM.Instr.binop
                            "%add"
                            (LeanLLVM.BinOp.add)
                            64
                            (LeanLLVM.Operand.reg "%n")
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.int 64 0x000000000000003f#64)),
                          LeanLLVM.Instr.binop
                            "%shr"
                            (LeanLLVM.BinOp.lshr)
                            64
                            (LeanLLVM.Operand.reg "%add")
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.int 64 0x0000000000000006#64)),
                          LeanLLVM.Instr.icmp
                            "%cmp61.not"
                            (LeanLLVM.IPred.ult)
                            64
                            (LeanLLVM.Operand.reg "%add")
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.int 64 0x0000000000000040#64))],
               term := LeanLLVM.Term.condbr (LeanLLVM.Operand.reg "%cmp61.not") "for.cond.cleanup" "for.body.lr.ph" },
             { name := "for.body.lr.ph",
               instrs := [LeanLLVM.Instr.gep
                            "%delim"
                            (LeanLLVM.Ty.int 8)
                            (LeanLLVM.Operand.reg "%mk")
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.int 64 0x0000000000000008#64)),
                          LeanLLVM.Instr.gep
                            "%in_string"
                            (LeanLLVM.Ty.int 8)
                            (LeanLLVM.Operand.reg "%mk")
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.int 64 0x0000000000000010#64)),
                          LeanLLVM.Instr.gep
                            "%ws"
                            (LeanLLVM.Ty.int 8)
                            (LeanLLVM.Operand.reg "%mk")
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.int 64 0x0000000000000018#64))],
               term := LeanLLVM.Term.br "for.body" },
             { name := "for.cond.cleanup",
               instrs := [LeanLLVM.Instr.binop
                            "%and19"
                            (LeanLLVM.BinOp.and)
                            64
                            (LeanLLVM.Operand.reg "%arm")
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.int 64 0x0000000000000001#64)),
                          LeanLLVM.Instr.icmp
                            "%tobool.not"
                            (LeanLLVM.IPred.eq)
                            64
                            (LeanLLVM.Operand.reg "%and19")
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.int 64 0x0000000000000000#64)),
                          LeanLLVM.Instr.load "%0" (LeanLLVM.Ty.int 64) (LeanLLVM.Operand.reg "%nk")],
               term := LeanLLVM.Term.condbr (LeanLLVM.Operand.reg "%tobool.not") "cond.false" "cond.true" },
             { name := "for.body",
               instrs := [LeanLLVM.Instr.phi
                            "%prevS.063"
                            (LeanLLVM.Ty.int 64)
                            [("for.body.lr.ph", LeanLLVM.Operand.imm (LeanLLVM.Const.int 64 0x0000000000000000#64)),
                             ("for.body", LeanLLVM.Operand.reg "%shr13")],
                          LeanLLVM.Instr.phi
                            "%i.062"
                            (LeanLLVM.Ty.int 64)
                            [("for.body.lr.ph", LeanLLVM.Operand.imm (LeanLLVM.Const.int 64 0x0000000000000000#64)),
                             ("for.body", LeanLLVM.Operand.reg "%inc")],
                          LeanLLVM.Instr.binop
                            "%shl"
                            (LeanLLVM.BinOp.shl)
                            64
                            (LeanLLVM.Operand.reg "%i.062")
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.int 64 0x0000000000000006#64)),
                          LeanLLVM.Instr.gep
                            "%add.ptr"
                            (LeanLLVM.Ty.int 8)
                            (LeanLLVM.Operand.reg "%b")
                            (LeanLLVM.Operand.reg "%shl"),
                          LeanLLVM.Instr.callVoid
                            "leanllvm_json_s1_masks"
                            [(LeanLLVM.Ty.ptr, LeanLLVM.Operand.reg "%add.ptr"),
                             (LeanLLVM.Ty.ptr, LeanLLVM.Operand.reg "%sc"),
                             (LeanLLVM.Ty.ptr, LeanLLVM.Operand.reg "%mk")],
                          LeanLLVM.Instr.load "%1" (LeanLLVM.Ty.int 64) (LeanLLVM.Operand.reg "%mk"),
                          LeanLLVM.Instr.load "%2" (LeanLLVM.Ty.int 64) (LeanLLVM.Operand.reg "%delim"),
                          LeanLLVM.Instr.load "%3" (LeanLLVM.Ty.int 64) (LeanLLVM.Operand.reg "%in_string"),
                          LeanLLVM.Instr.load "%4" (LeanLLVM.Ty.int 64) (LeanLLVM.Operand.reg "%ws"),
                          LeanLLVM.Instr.binop
                            "%5"
                            (LeanLLVM.BinOp.or)
                            64
                            (LeanLLVM.Operand.reg "%1")
                            (LeanLLVM.Operand.reg "%4"),
                          LeanLLVM.Instr.binop
                            "%6"
                            (LeanLLVM.BinOp.or)
                            64
                            (LeanLLVM.Operand.reg "%5")
                            (LeanLLVM.Operand.reg "%2"),
                          LeanLLVM.Instr.binop
                            "%or2"
                            (LeanLLVM.BinOp.or)
                            64
                            (LeanLLVM.Operand.reg "%6")
                            (LeanLLVM.Operand.reg "%3"),
                          LeanLLVM.Instr.binop
                            "%not"
                            (LeanLLVM.BinOp.xor)
                            64
                            (LeanLLVM.Operand.reg "%or2")
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.int 64 0xffffffffffffffff#64)),
                          LeanLLVM.Instr.binop
                            "%not6"
                            (LeanLLVM.BinOp.xor)
                            64
                            (LeanLLVM.Operand.reg "%3")
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.int 64 0xffffffffffffffff#64)),
                          LeanLLVM.Instr.binop
                            "%and"
                            (LeanLLVM.BinOp.and)
                            64
                            (LeanLLVM.Operand.reg "%2")
                            (LeanLLVM.Operand.reg "%not6"),
                          LeanLLVM.Instr.binop
                            "%shl8"
                            (LeanLLVM.BinOp.shl)
                            64
                            (LeanLLVM.Operand.reg "%not")
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.int 64 0x0000000000000001#64)),
                          LeanLLVM.Instr.binop
                            "%or9"
                            (LeanLLVM.BinOp.or)
                            64
                            (LeanLLVM.Operand.reg "%shl8")
                            (LeanLLVM.Operand.reg "%prevS.063"),
                          LeanLLVM.Instr.binop
                            "%not10"
                            (LeanLLVM.BinOp.xor)
                            64
                            (LeanLLVM.Operand.reg "%or9")
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.int 64 0xffffffffffffffff#64)),
                          LeanLLVM.Instr.binop
                            "%and11"
                            (LeanLLVM.BinOp.and)
                            64
                            (LeanLLVM.Operand.reg "%not10")
                            (LeanLLVM.Operand.reg "%not"),
                          LeanLLVM.Instr.binop
                            "%7"
                            (LeanLLVM.BinOp.or)
                            64
                            (LeanLLVM.Operand.reg "%and")
                            (LeanLLVM.Operand.reg "%and11"),
                          LeanLLVM.Instr.binop
                            "%or12"
                            (LeanLLVM.BinOp.or)
                            64
                            (LeanLLVM.Operand.reg "%7")
                            (LeanLLVM.Operand.reg "%1"),
                          LeanLLVM.Instr.binop
                            "%shr13"
                            (LeanLLVM.BinOp.lshr)
                            64
                            (LeanLLVM.Operand.reg "%not")
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.int 64 0x000000000000003f#64)),
                          LeanLLVM.Instr.binop
                            "%sub"
                            (LeanLLVM.BinOp.sub)
                            64
                            (LeanLLVM.Operand.reg "%n")
                            (LeanLLVM.Operand.reg "%shl"),
                          LeanLLVM.Instr.icmp
                            "%cmp15"
                            (LeanLLVM.IPred.ult)
                            64
                            (LeanLLVM.Operand.reg "%sub")
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.int 64 0x0000000000000040#64)),
                          LeanLLVM.Instr.binop
                            "%notmask"
                            (LeanLLVM.BinOp.shl)
                            64
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.int 64 0xffffffffffffffff#64))
                            (LeanLLVM.Operand.reg "%sub"),
                          LeanLLVM.Instr.binop
                            "%sub17"
                            (LeanLLVM.BinOp.xor)
                            64
                            (LeanLLVM.Operand.reg "%notmask")
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.int 64 0xffffffffffffffff#64)),
                          LeanLLVM.Instr.select
                            "%and18"
                            (LeanLLVM.Ty.int 64)
                            (LeanLLVM.Operand.reg "%cmp15")
                            (LeanLLVM.Operand.reg "%sub17")
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.int 64 0xffffffffffffffff#64)),
                          LeanLLVM.Instr.binop
                            "%e.0"
                            (LeanLLVM.BinOp.and)
                            64
                            (LeanLLVM.Operand.reg "%or12")
                            (LeanLLVM.Operand.reg "%and18"),
                          LeanLLVM.Instr.gep
                            "%arrayidx"
                            (LeanLLVM.Ty.int 64)
                            (LeanLLVM.Operand.reg "%ent")
                            (LeanLLVM.Operand.reg "%i.062"),
                          LeanLLVM.Instr.store
                            (LeanLLVM.Ty.int 64)
                            (LeanLLVM.Operand.reg "%e.0")
                            (LeanLLVM.Operand.reg "%arrayidx"),
                          LeanLLVM.Instr.binop
                            "%inc"
                            (LeanLLVM.BinOp.add)
                            64
                            (LeanLLVM.Operand.reg "%i.062")
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.int 64 0x0000000000000001#64)),
                          LeanLLVM.Instr.icmp
                            "%exitcond.not"
                            (LeanLLVM.IPred.eq)
                            64
                            (LeanLLVM.Operand.reg "%inc")
                            (LeanLLVM.Operand.reg "%shr")],
               term := LeanLLVM.Term.condbr (LeanLLVM.Operand.reg "%exitcond.not") "for.cond.cleanup" "for.body" },
             { name := "cond.true",
               instrs := [LeanLLVM.Instr.call
                            "%call"
                            (LeanLLVM.Ty.int 64)
                            "leanllvm_json_entry_b8"
                            [(LeanLLVM.Ty.ptr, LeanLLVM.Operand.reg "%ent"),
                             (LeanLLVM.Ty.int 64, LeanLLVM.Operand.imm (LeanLLVM.Const.int 64 0x0000000000000000#64)),
                             (LeanLLVM.Ty.int 64, LeanLLVM.Operand.reg "%shr"),
                             (LeanLLVM.Ty.ptr, LeanLLVM.Operand.reg "%ep"),
                             (LeanLLVM.Ty.int 64, LeanLLVM.Operand.reg "%0")]],
               term := LeanLLVM.Term.br "cond.end" },
             { name := "cond.false",
               instrs := [LeanLLVM.Instr.call
                            "%call20"
                            (LeanLLVM.Ty.int 64)
                            "leanllvm_json_entry_pos8"
                            [(LeanLLVM.Ty.ptr, LeanLLVM.Operand.reg "%ent"),
                             (LeanLLVM.Ty.int 64, LeanLLVM.Operand.imm (LeanLLVM.Const.int 64 0x0000000000000000#64)),
                             (LeanLLVM.Ty.int 64, LeanLLVM.Operand.reg "%shr"),
                             (LeanLLVM.Ty.ptr, LeanLLVM.Operand.reg "%ep"),
                             (LeanLLVM.Ty.int 64, LeanLLVM.Operand.reg "%0")]],
               term := LeanLLVM.Term.br "cond.end" },
             { name := "cond.end",
               instrs := [LeanLLVM.Instr.phi
                            "%cond"
                            (LeanLLVM.Ty.int 64)
                            [("cond.true", LeanLLVM.Operand.reg "%call"),
                             ("cond.false", LeanLLVM.Operand.reg "%call20")],
                          LeanLLVM.Instr.store
                            (LeanLLVM.Ty.int 64)
                            (LeanLLVM.Operand.reg "%cond")
                            (LeanLLVM.Operand.reg "%nk"),
                          LeanLLVM.Instr.call
                            "%call21"
                            (LeanLLVM.Ty.int 64)
                            "leanllvm_json_utf8"
                            [(LeanLLVM.Ty.ptr, LeanLLVM.Operand.reg "%b"),
                             (LeanLLVM.Ty.int 64, LeanLLVM.Operand.reg "%n"),
                             (LeanLLVM.Ty.int 32, LeanLLVM.Operand.imm (LeanLLVM.Const.int 32 0x00000000#32))],
                          LeanLLVM.Instr.icmp
                            "%cmp22.not"
                            (LeanLLVM.IPred.eq)
                            64
                            (LeanLLVM.Operand.reg "%call21")
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.int 64 0x0000000000000000#64))],
               term := LeanLLVM.Term.condbr (LeanLLVM.Operand.reg "%cmp22.not") "if.end24" "if.then23" },
             { name := "if.then23",
               instrs := [LeanLLVM.Instr.store
                            (LeanLLVM.Ty.int 64)
                            (LeanLLVM.Operand.reg "%n")
                            (LeanLLVM.Operand.reg "%err")],
               term := LeanLLVM.Term.br "cleanup" },
             { name := "if.end24",
               instrs := [LeanLLVM.Instr.load "%8" (LeanLLVM.Ty.int 64) (LeanLLVM.Operand.reg "%nxp"),
                          LeanLLVM.Instr.call
                            "%call25"
                            (LeanLLVM.Ty.int 64)
                            "leanllvm_json_stage2"
                            [(LeanLLVM.Ty.ptr, LeanLLVM.Operand.reg "%b"),
                             (LeanLLVM.Ty.int 64, LeanLLVM.Operand.reg "%n"),
                             (LeanLLVM.Ty.ptr, LeanLLVM.Operand.reg "%ep"),
                             (LeanLLVM.Ty.int 64, LeanLLVM.Operand.reg "%cond"),
                             (LeanLLVM.Ty.ptr, LeanLLVM.Operand.reg "%xp"),
                             (LeanLLVM.Ty.int 64, LeanLLVM.Operand.reg "%8"),
                             (LeanLLVM.Ty.ptr, LeanLLVM.Operand.reg "%dst"),
                             (LeanLLVM.Ty.int 64, LeanLLVM.Operand.reg "%dstcap"),
                             (LeanLLVM.Ty.ptr, LeanLLVM.Operand.reg "%ndst"),
                             (LeanLLVM.Ty.ptr, LeanLLVM.Operand.reg "%ev"),
                             (LeanLLVM.Ty.int 64, LeanLLVM.Operand.reg "%evcap"),
                             (LeanLLVM.Ty.ptr, LeanLLVM.Operand.reg "%nev"),
                             (LeanLLVM.Ty.ptr, LeanLLVM.Operand.reg "%err")]],
               term := LeanLLVM.Term.br "cleanup" },
             { name := "cleanup",
               instrs := [LeanLLVM.Instr.phi
                            "%retval.0"
                            (LeanLLVM.Ty.int 64)
                            [("if.then23", LeanLLVM.Operand.imm (LeanLLVM.Const.int 64 0x0000000000000000#64)),
                             ("if.end24", LeanLLVM.Operand.reg "%call25")]],
               term := LeanLLVM.Term.ret (LeanLLVM.Ty.int 64) (some (LeanLLVM.Operand.reg "%retval.0")) }] }

#guard decide (firstFunction plainSrc = some plainBody)

#guard decide (plainBody.params.length = 20 ∧ plainBody.blocks.length = 10)


/-- The loop head block. -/
def plainBodyBlock : Block := plainBody.blocks.get ⟨3, by decide⟩

/-- The loop head's instructions, as the pin carries them. -/
theorem plainBodyBlock_instrs : plainBodyBlock.instrs =
    [LeanLLVM.Instr.phi
                            "%prevS.063"
                            (LeanLLVM.Ty.int 64)
                            [("for.body.lr.ph", LeanLLVM.Operand.imm (LeanLLVM.Const.int 64 0x0000000000000000#64)),
                             ("for.body", LeanLLVM.Operand.reg "%shr13")],
                          LeanLLVM.Instr.phi
                            "%i.062"
                            (LeanLLVM.Ty.int 64)
                            [("for.body.lr.ph", LeanLLVM.Operand.imm (LeanLLVM.Const.int 64 0x0000000000000000#64)),
                             ("for.body", LeanLLVM.Operand.reg "%inc")],
                          LeanLLVM.Instr.binop
                            "%shl"
                            (LeanLLVM.BinOp.shl)
                            64
                            (LeanLLVM.Operand.reg "%i.062")
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.int 64 0x0000000000000006#64)),
                          LeanLLVM.Instr.gep
                            "%add.ptr"
                            (LeanLLVM.Ty.int 8)
                            (LeanLLVM.Operand.reg "%b")
                            (LeanLLVM.Operand.reg "%shl"),
                          LeanLLVM.Instr.callVoid
                            "leanllvm_json_s1_masks"
                            [(LeanLLVM.Ty.ptr, LeanLLVM.Operand.reg "%add.ptr"),
                             (LeanLLVM.Ty.ptr, LeanLLVM.Operand.reg "%sc"),
                             (LeanLLVM.Ty.ptr, LeanLLVM.Operand.reg "%mk")],
                          LeanLLVM.Instr.load "%1" (LeanLLVM.Ty.int 64) (LeanLLVM.Operand.reg "%mk"),
                          LeanLLVM.Instr.load "%2" (LeanLLVM.Ty.int 64) (LeanLLVM.Operand.reg "%delim"),
                          LeanLLVM.Instr.load "%3" (LeanLLVM.Ty.int 64) (LeanLLVM.Operand.reg "%in_string"),
                          LeanLLVM.Instr.load "%4" (LeanLLVM.Ty.int 64) (LeanLLVM.Operand.reg "%ws"),
                          LeanLLVM.Instr.binop
                            "%5"
                            (LeanLLVM.BinOp.or)
                            64
                            (LeanLLVM.Operand.reg "%1")
                            (LeanLLVM.Operand.reg "%4"),
                          LeanLLVM.Instr.binop
                            "%6"
                            (LeanLLVM.BinOp.or)
                            64
                            (LeanLLVM.Operand.reg "%5")
                            (LeanLLVM.Operand.reg "%2"),
                          LeanLLVM.Instr.binop
                            "%or2"
                            (LeanLLVM.BinOp.or)
                            64
                            (LeanLLVM.Operand.reg "%6")
                            (LeanLLVM.Operand.reg "%3"),
                          LeanLLVM.Instr.binop
                            "%not"
                            (LeanLLVM.BinOp.xor)
                            64
                            (LeanLLVM.Operand.reg "%or2")
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.int 64 0xffffffffffffffff#64)),
                          LeanLLVM.Instr.binop
                            "%not6"
                            (LeanLLVM.BinOp.xor)
                            64
                            (LeanLLVM.Operand.reg "%3")
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.int 64 0xffffffffffffffff#64)),
                          LeanLLVM.Instr.binop
                            "%and"
                            (LeanLLVM.BinOp.and)
                            64
                            (LeanLLVM.Operand.reg "%2")
                            (LeanLLVM.Operand.reg "%not6"),
                          LeanLLVM.Instr.binop
                            "%shl8"
                            (LeanLLVM.BinOp.shl)
                            64
                            (LeanLLVM.Operand.reg "%not")
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.int 64 0x0000000000000001#64)),
                          LeanLLVM.Instr.binop
                            "%or9"
                            (LeanLLVM.BinOp.or)
                            64
                            (LeanLLVM.Operand.reg "%shl8")
                            (LeanLLVM.Operand.reg "%prevS.063"),
                          LeanLLVM.Instr.binop
                            "%not10"
                            (LeanLLVM.BinOp.xor)
                            64
                            (LeanLLVM.Operand.reg "%or9")
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.int 64 0xffffffffffffffff#64)),
                          LeanLLVM.Instr.binop
                            "%and11"
                            (LeanLLVM.BinOp.and)
                            64
                            (LeanLLVM.Operand.reg "%not10")
                            (LeanLLVM.Operand.reg "%not"),
                          LeanLLVM.Instr.binop
                            "%7"
                            (LeanLLVM.BinOp.or)
                            64
                            (LeanLLVM.Operand.reg "%and")
                            (LeanLLVM.Operand.reg "%and11"),
                          LeanLLVM.Instr.binop
                            "%or12"
                            (LeanLLVM.BinOp.or)
                            64
                            (LeanLLVM.Operand.reg "%7")
                            (LeanLLVM.Operand.reg "%1"),
                          LeanLLVM.Instr.binop
                            "%shr13"
                            (LeanLLVM.BinOp.lshr)
                            64
                            (LeanLLVM.Operand.reg "%not")
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.int 64 0x000000000000003f#64)),
                          LeanLLVM.Instr.binop
                            "%sub"
                            (LeanLLVM.BinOp.sub)
                            64
                            (LeanLLVM.Operand.reg "%n")
                            (LeanLLVM.Operand.reg "%shl"),
                          LeanLLVM.Instr.icmp
                            "%cmp15"
                            (LeanLLVM.IPred.ult)
                            64
                            (LeanLLVM.Operand.reg "%sub")
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.int 64 0x0000000000000040#64)),
                          LeanLLVM.Instr.binop
                            "%notmask"
                            (LeanLLVM.BinOp.shl)
                            64
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.int 64 0xffffffffffffffff#64))
                            (LeanLLVM.Operand.reg "%sub"),
                          LeanLLVM.Instr.binop
                            "%sub17"
                            (LeanLLVM.BinOp.xor)
                            64
                            (LeanLLVM.Operand.reg "%notmask")
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.int 64 0xffffffffffffffff#64)),
                          LeanLLVM.Instr.select
                            "%and18"
                            (LeanLLVM.Ty.int 64)
                            (LeanLLVM.Operand.reg "%cmp15")
                            (LeanLLVM.Operand.reg "%sub17")
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.int 64 0xffffffffffffffff#64)),
                          LeanLLVM.Instr.binop
                            "%e.0"
                            (LeanLLVM.BinOp.and)
                            64
                            (LeanLLVM.Operand.reg "%or12")
                            (LeanLLVM.Operand.reg "%and18"),
                          LeanLLVM.Instr.gep
                            "%arrayidx"
                            (LeanLLVM.Ty.int 64)
                            (LeanLLVM.Operand.reg "%ent")
                            (LeanLLVM.Operand.reg "%i.062"),
                          LeanLLVM.Instr.store
                            (LeanLLVM.Ty.int 64)
                            (LeanLLVM.Operand.reg "%e.0")
                            (LeanLLVM.Operand.reg "%arrayidx"),
                          LeanLLVM.Instr.binop
                            "%inc"
                            (LeanLLVM.BinOp.add)
                            64
                            (LeanLLVM.Operand.reg "%i.062")
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.int 64 0x0000000000000001#64)),
                          LeanLLVM.Instr.icmp
                            "%exitcond.not"
                            (LeanLLVM.IPred.eq)
                            64
                            (LeanLLVM.Operand.reg "%inc")
                            (LeanLLVM.Operand.reg "%shr")] := rfl

/-- The loop head's terminator. -/
theorem plainBodyBlock_term : plainBodyBlock.term =
    LeanLLVM.Term.condbr (LeanLLVM.Operand.reg "%exitcond.not") "for.cond.cleanup" "for.body" := rfl

/-! ### The stored word's identity

The loop's only arithmetic is the entry word it stores.  At the six masks the
classifier returns, the body's `%or2`/`%not`/`%and`/`%shl8`/`%or9`/`%and11`/
`%or12` line is `entryMask64` once `%not` is `specScalar64`, and the `%and18`
tail clamp is `limMask`.  This is the semantic content of the `ent[i]` store,
independent of the run. -/

/-- The body's `%not` is the specification's scalar word: the four mask words
OR-ed in the body's order are the model's, inside the complement. -/
theorem plain_scalar_eq (lo hi : Block32) (st : ClassState) :
    ~~~ (specQuote64 lo hi st ||| specSpace64 lo hi st |||
          specDelimiter64 lo hi st ||| specInString64 lo hi st)
      = specScalar64 lo hi st := by
  simp only [specScalar64, BitVec.not_or]
  ac_rfl

/-- **The stored entry word.**  With `prevS` the previous block's top lane — a
word that is `0` or `1` — the body's line equals `entryMask64` at the same
state, before the tail clamp. -/
theorem plain_entry_word (lo hi : Block32) (st : ClassState) (prevS : BitVec 64)
    (hp : prevS = 0 ∨ prevS = 1) :
    (specQuote64 lo hi st |||
        (specDelimiter64 lo hi st &&& ~~~ specInString64 lo hi st)) |||
      (specScalar64 lo hi st &&&
        ~~~ ((specScalar64 lo hi st <<< 1) ||| prevS))
      = entryMask64 lo hi st (decide (prevS = 1)) := by
  rw [entryMask64, structuralOnly64, scalarStarts64]
  rcases hp with h | h <;> subst h <;> simp

/-- **The value the loop stores.**  The same line clamped by `limMask lim` is
`entryMask64 … &&& limMask lim`, the value `entryMask64`'s definition gives on
the block's `lim = n - 64i`. -/
theorem plain_stored_word (lo hi : Block32) (st : ClassState) (prevS : BitVec 64)
    (hp : prevS = 0 ∨ prevS = 1) (lim : Nat) :
    ((specQuote64 lo hi st |||
        (specDelimiter64 lo hi st &&& ~~~ specInString64 lo hi st)) |||
      (specScalar64 lo hi st &&&
        ~~~ ((specScalar64 lo hi st <<< 1) ||| prevS))) &&& limMask lim
      = entryMask64 lo hi st (decide (prevS = 1)) &&& limMask lim := by
  rw [plain_entry_word lo hi st prevS hp]

/-! ### The run, row by row

The first row is the entry block: its three instructions compute the rounded
length, the block count and the length test, and its terminator branches to
`for.cond.cleanup` on a document shorter than one block and to
`for.body.lr.ph` otherwise.  The arithmetic is the certified seed's
(`shr_ofNat_blocks`), at the plain body's own block names. -/

/-- The plain body's entry block. -/
def plainEntry : Block := plainBody.blocks.get ⟨0, by decide⟩

/-- The entry block's instructions, as the pin carries them. -/
theorem plainEntry_instrs : plainEntry.instrs =
    [Instr.binop "%add" BinOp.add 64 (Operand.reg "%n") (JsonPipelineIR.lit 64 63),
     Instr.binop "%shr" BinOp.lshr 64 (Operand.reg "%add") (JsonPipelineIR.lit 64 6),
     Instr.icmp "%cmp61.not" IPred.ult 64 (Operand.reg "%add") (JsonPipelineIR.lit 64 64)] := rfl

/-- The entry block's terminator. -/
theorem plainEntry_term : plainEntry.term =
    Term.condbr (Operand.reg "%cmp61.not") "for.cond.cleanup" "for.body.lr.ph" := rfl

/-- The caller's environment at the plain ABI's twenty slots. -/
def plainIn0 (base sc mk entw ep nk xp nxp xcarry dst ndst ev nev err : Nat)
    (n epcap xpcap dstcap evcap arm : BitVec 64) : Env :=
  cells [("%b", .ptr base), ("%n", .int 64 n), ("%sc", .ptr sc),
         ("%mk", .ptr mk), ("%entw", .ptr entw), ("%ep", .ptr ep),
         ("%epcap", .int 64 epcap), ("%nk", .ptr nk), ("%xp", .ptr xp),
         ("%xpcap", .int 64 xpcap), ("%nxp", .ptr nxp), ("%xcarry", .ptr xcarry),
         ("%dst", .ptr dst), ("%dstcap", .int 64 dstcap), ("%ndst", .ptr ndst),
         ("%ev", .ptr ev), ("%evcap", .int 64 evcap), ("%nev", .ptr nev),
         ("%err", .ptr err), ("%arm", .int 64 arm)] []

/-- The entry block's three cells on top of the caller's environment. -/
def plainIn1 (base sc mk entw ep nk xp nxp xcarry dst ndst ev nev err : Nat)
    (n epcap xpcap dstcap evcap arm : BitVec 64) : Env :=
  cells [("%cmp61.not", .int 1 (evalICmp .ult (n + litv 64 63) (litv 64 64))),
         ("%shr", .int 64 ((n + litv 64 63) >>> (litv 64 6).toNat)),
         ("%add", .int 64 (n + litv 64 63))]
    (plainIn0 base sc mk entw ep nk xp nxp xcarry dst ndst ev nev err n epcap xpcap
      dstcap evcap arm)

/-- The entry block's trace. -/
theorem plain_entry_denote (calls : Calls) (s : State)
    (base sc mk entw ep nk xp nxp xcarry dst ndst ev nev err : Nat)
    (n epcap xpcap dstcap evcap arm : BitVec 64) :
    denoteCode calls plainEntry.instrs
        (stateAt (plainIn0 base sc mk entw ep nk xp nxp xcarry dst ndst ev nev err n
          epcap xpcap dstcap evcap arm) s) =
      some (stateAt (plainIn1 base sc mk entw ep nk xp nxp xcarry dst ndst ev nev err n
        epcap xpcap dstcap evcap arm) s) := by
  rw [plainEntry_instrs]
  simp only [JsonPipelineIR.lit, litv, plainIn0, plainIn1]
  pipeline_block_eval

/-- **The first run row.**  From the caller's environment, the entry block
computes `%add`, `%shr` and `%cmp61.not` and branches: a document shorter than
one block leaves for `for.cond.cleanup`, otherwise for `for.body.lr.ph`.  The
memory and allocator are unchanged. -/
theorem plainEntry_step (calls : Calls) (s : State)
    (base sc mk entw ep nk xp nxp xcarry dst ndst ev nev err : Nat)
    (n epcap xpcap dstcap evcap arm : BitVec 64)
    (hpc : s.pc = "entry")
    (henv : s.env = plainIn0 base sc mk entw ep nk xp nxp xcarry dst ndst ev nev err n
      epcap xpcap dstcap evcap arm) :
    (evalICmp .ult (n + litv 64 63) (litv 64 64) = 0 ∧
      ∃ e : State, step calls plainBody s = .jump e ∧ e.pc = "for.body.lr.ph" ∧
        e.env = plainIn1 base sc mk entw ep nk xp nxp xcarry dst ndst ev nev err n
          epcap xpcap dstcap evcap arm ∧
        e.pre = some s.pc ∧ e.mem = s.mem ∧ e.next = s.next) ∨
    (evalICmp .ult (n + litv 64 63) (litv 64 64) = 1 ∧
      ∃ e : State, step calls plainBody s = .jump e ∧ e.pc = "for.cond.cleanup" ∧
        e.env = plainIn1 base sc mk entw ep nk xp nxp xcarry dst ndst ev nev err n
          epcap xpcap dstcap evcap arm ∧
        e.pre = some s.pc ∧ e.mem = s.mem ∧ e.next = s.next) := by
  have hfind : plainBody.findBlock s.pc = some plainEntry := by
    rw [hpc]; rfl
  have hs : stateAt (plainIn0 base sc mk entw ep nk xp nxp xcarry dst ndst ev nev err n
      epcap xpcap dstcap evcap arm) s = s := by
    rw [stateAt, ← henv]
  let s1 : State := stateAt (plainIn1 base sc mk entw ep nk xp nxp xcarry dst ndst ev
    nev err n epcap xpcap dstcap evcap arm) s
  have hcode : denoteCode calls plainEntry.instrs s = some s1 := by
    rw [← hs]
    exact plain_entry_denote calls s base sc mk entw ep nk xp nxp xcarry dst ndst ev
      nev err n epcap xpcap dstcap evcap arm
  have hop : evalOperand s1 (Operand.reg "%cmp61.not") =
      some (.int 1 (evalICmp .ult (n + litv 64 63) (litv 64 64))) := by
    simp [s1, stateAt, evalOperand, plainIn1, cells]
  rcases bitVec1_zero_or_one (evalICmp .ult (n + litv 64 63) (litv 64 64)) with hb | hb
  · refine Or.inl ⟨hb, ⟨{ s1 with pc := "for.body.lr.ph", pre := some s.pc }, ?_,
      rfl, rfl, rfl, rfl, rfl⟩⟩
    refine PipelineBodyFacts.step_of_blocks hfind hcode ?_
    rw [plainEntry_term]
    exact PipelineBodyFacts.execTerm_condbr_zero (c := Operand.reg "%cmp61.not")
      (t := "for.cond.cleanup") (f := "for.body.lr.ph") (by rw [hop, hb])
  · refine Or.inr ⟨hb, ⟨{ s1 with pc := "for.cond.cleanup", pre := some s.pc }, ?_,
      rfl, rfl, rfl, rfl, rfl⟩⟩
    refine PipelineBodyFacts.step_of_blocks hfind hcode ?_
    rw [plainEntry_term]
    exact PipelineBodyFacts.execTerm_condbr_one (c := Operand.reg "%cmp61.not")
      (t := "for.cond.cleanup") (f := "for.body.lr.ph") (by rw [hop, hb])


/-- The loop preheader block. -/
def plainLrPh : Block := plainBody.blocks.get ⟨1, by decide⟩

/-- The preheader's instructions, as the pin carries them. -/
theorem plainLrPh_instrs : plainLrPh.instrs =
    [Instr.gep "%delim" (Ty.int 8) (Operand.reg "%mk") (JsonPipelineIR.lit 64 8),
     Instr.gep "%in_string" (Ty.int 8) (Operand.reg "%mk") (JsonPipelineIR.lit 64 16),
     Instr.gep "%ws" (Ty.int 8) (Operand.reg "%mk") (JsonPipelineIR.lit 64 24)] := rfl

/-- The preheader's terminator. -/
theorem plainLrPh_term : plainLrPh.term = Term.br "for.body" := rfl

/-- The preheader's three offsets on top of the entry block's environment. -/
def plainIn2 (base sc mk entw ep nk xp nxp xcarry dst ndst ev nev err : Nat)
    (n epcap xpcap dstcap evcap arm : BitVec 64) : Env :=
  cells [("%ws", .ptr (mk + 24)), ("%in_string", .ptr (mk + 16)),
         ("%delim", .ptr (mk + 8))]
    (plainIn1 base sc mk entw ep nk xp nxp xcarry dst ndst ev nev err n epcap xpcap
      dstcap evcap arm)

/-- The preheader's trace. -/
theorem plain_lrPh_denote (calls : Calls) (s : State)
    (base sc mk entw ep nk xp nxp xcarry dst ndst ev nev err : Nat)
    (n epcap xpcap dstcap evcap arm : BitVec 64) :
    denoteCode calls plainLrPh.instrs
        (stateAt (plainIn1 base sc mk entw ep nk xp nxp xcarry dst ndst ev nev err n
          epcap xpcap dstcap evcap arm) s) =
      some (stateAt (plainIn2 base sc mk entw ep nk xp nxp xcarry dst ndst ev nev err n
        epcap xpcap dstcap evcap arm) s) := by
  rw [plainLrPh_instrs]
  simp only [JsonPipelineIR.lit, litv, plainIn1, plainIn2]
  pipeline_block_eval

/-- **The second run row.**  From the preheader's environment, its three
`getelementptr`s name the mask slot's three offsets and its terminator jumps to
the loop head; memory and allocator are unchanged. -/
theorem plainLrPh_step (calls : Calls) (s : State)
    (base sc mk entw ep nk xp nxp xcarry dst ndst ev nev err : Nat)
    (n epcap xpcap dstcap evcap arm : BitVec 64)
    (hpc : s.pc = "for.body.lr.ph")
    (henv : s.env = plainIn1 base sc mk entw ep nk xp nxp xcarry dst ndst ev nev err n
      epcap xpcap dstcap evcap arm) :
    ∃ e : State, step calls plainBody s = .jump e ∧ e.pc = "for.body" ∧
      e.env = plainIn2 base sc mk entw ep nk xp nxp xcarry dst ndst ev nev err n
        epcap xpcap dstcap evcap arm ∧
      e.pre = some s.pc ∧ e.mem = s.mem ∧ e.next = s.next := by
  have hfind : plainBody.findBlock s.pc = some plainLrPh := by
    rw [hpc]; rfl
  have hs : stateAt (plainIn1 base sc mk entw ep nk xp nxp xcarry dst ndst ev nev err n
      epcap xpcap dstcap evcap arm) s = s := by
    rw [stateAt, ← henv]
  let s1 : State := stateAt (plainIn2 base sc mk entw ep nk xp nxp xcarry dst ndst ev
    nev err n epcap xpcap dstcap evcap arm) s
  have hcode : denoteCode calls plainLrPh.instrs s = some s1 := by
    rw [← hs]
    exact plain_lrPh_denote calls s base sc mk entw ep nk xp nxp xcarry dst ndst ev nev
      err n epcap xpcap dstcap evcap arm
  refine ⟨{ s1 with pc := "for.body", pre := some s.pc }, ?_, rfl, rfl, rfl, rfl, rfl⟩
  refine PipelineBodyFacts.step_of_blocks hfind hcode ?_
  rw [plainLrPh_term]
  rfl

/-! ### Axiom footprints

The composition adds no carrier of its own.  `plainEntBytes_eq` is a
definitional equality and carries nothing; the array's positivity is arithmetic
(`propext`, `Quot.sound`); the two model identities and the two emitter refineries
inherit the certified units' `Classical.choice`; the post-shape and the route's
entry projection are `propext`/`Quot.sound`; and the route theorem carries the
units' `Classical.choice` through the certified bundle.  The no-list arm is a
hypothesis, so it contributes no axiom to these statements.
-/

/-- info: 'LeanLLVM.Refinement.plainEntBytes_eq' does not depend on any axioms -/
#guard_msgs in
#print axioms plainEntBytes_eq

/-- info: 'LeanLLVM.Refinement.plainEntBytes_pos' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms plainEntBytes_pos

/-- info: 'LeanLLVM.Refinement.plainStage1_words' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms plainStage1_words

/-- info: 'LeanLLVM.Refinement.plainStage1_fold' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms plainStage1_fold

/-- info: 'LeanLLVM.Refinement.plainStage1_pos8' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms plainStage1_pos8

/-- info: 'LeanLLVM.Refinement.plainStage1_b8' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms plainStage1_b8

/-- info: 'LeanLLVM.Refinement.pipelineUnitsPost_return' depends on axioms: [propext] -/
#guard_msgs in
#print axioms pipelineUnitsPost_return

/-- info: 'LeanLLVM.Refinement.routePost_of_satisfies' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms routePost_of_satisfies

/-- info: 'LeanLLVM.Refinement.plain_route_ent' depends on axioms: [propext] -/
#guard_msgs in
#print axioms plain_route_ent

/-- info: 'LeanLLVM.Refinement.plain_routePost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms plain_routePost

/-- info: 'LeanLLVM.Refinement.plainEntRegion_eq' does not depend on any axioms -/
#guard_msgs in
#print axioms plainEntRegion_eq

/-- info: 'LeanLLVM.Refinement.plainEntRegion_wider' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms plainEntRegion_wider

/-- info: 'LeanLLVM.Refinement.plainRoutePre_routePre' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms plainRoutePre_routePre

/-- info: 'LeanLLVM.Refinement.plainFrameEntry_eq' does not depend on any axioms -/
#guard_msgs in
#print axioms plainFrameEntry_eq

/-- info: 'LeanLLVM.Refinement.routePost_of_satisfies_gen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms routePost_of_satisfies_gen

/-- info: 'LeanLLVM.Refinement.plainEntry_instrs' depends on axioms: [propext] -/
#guard_msgs in
#print axioms plainEntry_instrs

/-- info: 'LeanLLVM.Refinement.plainEntry_term' does not depend on any axioms -/
#guard_msgs in
#print axioms plainEntry_term

/-- info: 'LeanLLVM.Refinement.plain_entry_denote' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms plain_entry_denote

/-- info: 'LeanLLVM.Refinement.plainEntry_step' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms plainEntry_step

/-- info: 'LeanLLVM.Refinement.plainLrPh_instrs' depends on axioms: [propext] -/
#guard_msgs in
#print axioms plainLrPh_instrs

/-- info: 'LeanLLVM.Refinement.plainLrPh_term' does not depend on any axioms -/
#guard_msgs in
#print axioms plainLrPh_term

/-- info: 'LeanLLVM.Refinement.plain_lrPh_denote' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms plain_lrPh_denote

/-- info: 'LeanLLVM.Refinement.plainLrPh_step' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms plainLrPh_step

/-- info: 'LeanLLVM.Refinement.plain_scalar_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms plain_scalar_eq

/-- info: 'LeanLLVM.Refinement.plain_entry_word' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms plain_entry_word

/-- info: 'LeanLLVM.Refinement.plain_stored_word' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms plain_stored_word

/-- info: 'LeanLLVM.Refinement.plainBodyBlock_instrs' does not depend on any axioms -/
#guard_msgs in
#print axioms plainBodyBlock_instrs

/-- info: 'LeanLLVM.Refinement.plainBodyBlock_term' does not depend on any axioms -/
#guard_msgs in
#print axioms plainBodyBlock_term

end LeanLLVM.Refinement
