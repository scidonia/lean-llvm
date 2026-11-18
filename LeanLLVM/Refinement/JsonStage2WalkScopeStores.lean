import LeanLLVM.Refinement.JsonStage2WalkScopeArms

set_option autoImplicit false

namespace LeanLLVM.Refinement

open LeanLLVM
open LeanLLVM.Refinement.JsonStage2IR
open LeanLLVM.Refinement.JsonEntryIR (readLanes32)
open LeanLLVM.Refinement.BlockEval

/-! ### The loop's forward stores, and the region they need

The entry loop's arm is the dispatch: `while.body.i` reads the entry stream and the
document, the switch tree classifies the byte, and one of the arms assembles a
record or refuses.  The edge that closes the iteration is proved (`walkBack_step`:
the merge at `cleanup478.i`, its two `phi`s, the exit test, and the budget refill),
and the iteration's forward edges are not; the obstruction to those is not the
nesting state, either reserve, or a refusal path: it is the first store the loop
executes, before any of them.

`while.body.i` stores the advanced index to the caller's cursor record,
`store i64 %inc.i, %k11.i` with `%k11.i = %c.i + 32` (`while.body.i.lr.ph`'s
`gep`), and `if.end207.i` does the same for the two-entry advance.  The
initialisation writes the record's other fields (`%c.i + 0/8/16/24`, and
`%c.i + 1112` for `%e`), and the walk writes the two container stacks
`%ctype.i`/`%cst.i` at `%sp.i.0248`, the log's `%z + 0/8/16/24/40/48/56`, `%s`'s
three fields, `%e + 8`, and `%t352.i`.  None of those addresses is staged by
`WalkGeom`, which is `stage2Pre` unpacked, and `stage2Pre` names only the thirteen
ABI objects — the staging is at the adapter (`stage2StagedPre`), and the record's
frame at `stage2WalkWrites`; both are `JsonStage2Contract`'s, and the next
paragraphs say what they buy and what they cannot yet.

The invariant's region claim is the walk's frame, and the two paragraphs that
follow record what the widening cost and what it bought, because both were
record-level questions and neither was an arm's.

**The narrow claim, and why it was false.**  Before this widening the claim was
`Owns (inRegions [(dst, alen), (ev, evlen)])`.  `Owns`'s unchanged half is a
statement about *every address outside* the region, so a store outside it
contradicts the claim unless the bytes happen to agree —
`owns_writeBytes_outside` is that argument — and only a store whose whole range is
inside it is admitted (`owns_writeBytes_inside`).  The loop's first store is to
`%c.i + 32`, which is outside both extents in the emitted pipeline, where the
cursor record is an object of its own; nothing in `WalkGeom` places it inside
them, so the narrow claim was not preserved one step into the loop.  The seed's
claim failed the same way, one step earlier: `entry`'s own stores (`%s +
56/72/80`, `%z + 0/8/16/24/40/48/56`, `%c.i + 0/8/16/24/1112`, and the `memset`
over `%c.i + 40`) are to the same unstaged objects, which is why `WalkSeedState`
takes the claim as a hypothesis rather than deriving it.

**The split, and where it had to begin.**  Presence is monotone in its region
and silence is anti-monotone: an `Owns` claim over one list is not the claim
over another, so the two are carried separately (`WalkInv.owned` and
`WalkInv.frame`) and handed to the record as two clauses through `WalkInv.report`,
which feeds `Stage2Run`, which `stage2Run_boundary` turns into
`stage2Boundary`'s post.  The post is at the ABI's thirteen arguments and the
seven appended objects are the *body's* parameters, so the post is where they
become nameable: `stage2Boundary` now carries them as witnesses (their extents
are `stage2StagedWrites`, the numbers `JsonStage2IR`'s `lifetimeExtents` guards
read off the pinned AST) together with `DisjointRegions
(stage2StagedRegions …)`.  `Stage2Run` carries the same seven, the caller's two
count slots and that separation; `WalkInv.owned`/`WalkInv.frame` are the
record's two region clauses at the run's cursors; `WalkInv.report` gives them back
at `alen + 64` (`Stage2Run.walkPresent_of_written` and
`Stage2Run.walkFrame_of_written`, whose staging separation places the seven and
whose watermark places the four stack objects).  So the loop's stores at `%c.i +
32` (`while.body.i`, `if.end207.i`), at `%ctype.i[sp]`/`%cst.i[sp]` (`if.end24.i`),
at `%z + 0/8/16/24/40/48/56`, `%s + 56/72/80` and `%e + 8` all land inside the
claim, and `walkStaged_write`/`walkFrame_write_inside` admit them.  The two
forward stores are `WalkInv.frame_cursorK` and `WalkInv.frame_stack` below.
`WalkSeedState`'s own claim is widened the same way; it is the initialisation's
promise, and it is the one clause of the loop head that is a hypothesis rather
than a reading of `WalkGeom`.

**What the widening costs its consumers, and which clause is pending.**  The
pipeline's tail read "the two count slots and the two streams are unchanged" off
the post, and unchanged-outside-a-wider-region does not yield
unchanged-outside-a-narrower one.  Of its four transport pairs, the two streams
(`S.ep`, `S.xp`) follow from the post's staging separation, because both are
stage-2 *arguments* and the staging names them at the counts the call carried
(the post carries `nep < 2 ^ 64` and `nxp < 2 ^ 64` so its counts are the
arguments' words' values — `one word with two widths is one number`, the same
move the two capacities make).  The two count slots (`S.nk`, `S.nxp`) do not:
they are the pipeline's, not stage-2's arguments, and no clause of the record can
name them.  `PipelineDischarge.Stage2SlotKeeps` is that statement, taken as a
hypothesis and documented as the model's missing stack discipline; it is the
composite's only frame-wise conditional clause.  `JsonPipelineSpec.SigmaFrame` is
no longer a premise beside it: it is a *definition* now — a `CallerView` naming the
caller's thirteen regions, with the seven staged objects existentially bound — so
the finalisation derives it rather than assuming it.  An existential footprint
does not by itself say the document is untouched, which is the limit
`SigmaFrame`'s own docstring records.

**The nesting clause is carried.**  `WalkInv.depth_reg` names the register —
`%sp.i.0248` holds the carry's `sp` — and `WalkInv.depth_cap` bounds it by
`stage2StackExtent`, so `if.end24.i`'s two stack stores index inside their staged
extents.  The `519` of `if.end.i`'s `%cmp19.i` is the *arm's* guard (`NestGuard`),
not the invariant's bound: a push at `519` carries `520` out of `if.end24.i`, and
the check is what refuses the next push.  Every arm that touches the depth carries
it: the seed sets it to zero (`walkSeed_depth_cap`, and `WalkSeedState`'s third
clause is the loop head's `phi` reading `0`), the five proved arms leave it alone
and carry the register through their binds, and `walkBack_step` carries it across
`cleanup478.i`'s merge, which moves the next depth into `%sp.i.1` instead of
`%sp.i.0248`.  What the clause does not say is the stacks' *contents* — the
push/pop discipline `%ctype.i[i]`/`%cst.i[i]` and `s2_value_pos` maintain — because
that is the dispatch's, and the dispatch's forward edges are what remains.

Two structural facts about the edge are worth recording beside it.  First, the
header's leading `phi` rebinds `%k.0.i249` inside the block, not on the edge, so
the outer arm is the two-block step `cleanup478.i → while.body.i → NodeBlock21`:
the carry's `k` advances only when the header's own instructions run, which is why
the strict decrease is `walkMeasure_step`'s (the header's block) and not the
edge's.  Second, the header's `phi` takes `%k.2.i` from `cleanup478.i`, whose
incoming value is the dispatch's, so the edge's guard is that merge's own — the
carry does not record it, and the dispatch to `while.body.i` needs the ten
predecessors' register facts at `cleanup478.i`'s two `phi`s. -/

/-- A block's store destinations, in text order, with the stored types. -/
def storeTargets (f : Function) (name : String) : List (String × Ty) :=
  match f.findBlock name with
  | none => []
  | some b =>
      b.instrs.filterMap fun i =>
        match i with
        | .store ty _ (.reg p) => some (p, ty)
        | _ => none

/-- The base register and displacement of a named `gep` in a block: the address
the store above is computed from. -/
def gepDef (f : Function) (name dst : String) : Option (String × Nat) :=
  match f.findBlock name with
  | none => none
  | some b =>
      (b.instrs.filterMap fun i =>
        match i with
        | .gep d _ (.reg base) (.imm (.int _ off)) =>
            if d = dst then some (base, off.toNat) else none
        | _ => none).head?

-- The loop head's first write is the cursor record's `k` field, and the field is
-- `%c.i + 32`; the store is eight bytes wide.
#guard storeTargets stage2Body "while.body.i" = [("%k11.i", Ty.int 64)]
#guard gepDef stage2Body "while.body.i.lr.ph" "%k11.i" = some ("%c.i", 32)

-- The two-entry advance writes the same field with the same width.
#guard storeTargets stage2Body "if.end207.i" = [("%k11.i", Ty.int 64)]

-- The nesting arm's stores are the two container stacks, at the running depth.
#guard storeTargets stage2Body "if.end24.i" =
  [("%arrayidx30.i", Ty.int 8), ("%arrayidx32.i", Ty.int 8)]

-- The hash update and the event reserve's two stores, in the order the record
-- path reaches them.
#guard storeTargets stage2Body "if.then.i.i" = [("%h1.i.i.i51", Ty.int 64)]
#guard storeTargets stage2Body "out_reserve.exit.i.i" =
  [("%add.ptr.i.i", Ty.int 8), ("%len", Ty.int 64)]

/-- **A write whose whole range is inside the owned region preserves the region
claim.**  The unchanged half is about the addresses outside the region, so a range
inside it asks nothing of them — at an address below the range or above it the
bytes are untouched (`readByte_writeBytes_outside`) — and the presence half holds
of the written bytes because a write adds presence. -/
theorem owns_writeBytes_inside {P : Nat → Prop} {mem m : Mem} {w : Nat} {v : List UInt8}
    (h : Owns P mem m) (hw : ∀ k, k < v.length → P (w + k)) :
    Owns P mem (writeBytes m w v) := by
  refine ⟨?_, ?_⟩
  · intro a ha
    by_cases hbelow : a < w
    · exact (readByte_writeBytes_outside m v (Or.inl hbelow)).trans (h.unchanged a ha)
    · by_cases habove : w + v.length ≤ a
      · exact (readByte_writeBytes_outside m v (Or.inr habove)).trans (h.unchanged a ha)
      · exfalso
        apply ha
        have hk : a - w < v.length := by omega
        have hP := hw (a - w) hk
        rwa [show w + (a - w) = a by omega] at hP
  · intro a ha
    exact present_writeBytes m w v (h.present a ha)

/-- **A write outside the owned region breaks the claim.**  If the write changes
the byte at an address the region excludes, no `Owns` at that region survives it:
the unchanged half demands that byte agree with the pre-state, and the store is
exactly what makes it not.  This is why the loop's first store is a record
question and not a detail of an arm: a frame that omits `%c.i` cannot survive
`while.body.i`, however the arm is proved. -/
theorem owns_writeBytes_outside {P : Nat → Prop} {mem m : Mem} {w : Nat} {v : List UInt8}
    (hw : ¬ P w) (hdiff : readByte (writeBytes m w v) w ≠ readByte mem w) :
    ¬ Owns P mem (writeBytes m w v) := by
  intro h
  exact hdiff (h.unchanged w hw)

/-! ### The forward stores the record now admits

The loop's forward edges write four things before any reserve is checked: the
cursor record's `k` field (`while.body.i`, and again at `if.end207.i` for the
two-entry advance), and the two container stacks at the running depth
(`if.end24.i`).  Each is inside an extent `stage2StagedWrites` names, so
`owns_writeBytes_inside` keeps the walk's region claim across it — which is the
whole of what the record change buys, and what the narrow frame could not do at
any price.  The instances below are stated at the record's own region list, so an
invariant that carries `stage2WalkFrame` discharges them without a side condition.

The depth bound is the `MAXD` check's `519`, and it is stated here rather than in
`WalkInv`: a push at `519` carries `520` out of `if.end24.i`, which is why the
invariant bounds the depth by the stacks' extent and the *check* bounds the index. -/

/-- The `MAXD` check's bound: the depth at which `if.end24.i` still indexes the
stacks.  This is the arm's guard, not the invariant's clause. -/
def NestGuard (sp : Nat) : Prop := sp ≤ 519

/-- A region list's tail denotes a sub-predicate of the whole. -/
theorem inRegions_append_right {rs ss : List (Nat × Nat)} {a : Nat}
    (h : inRegions ss a) : inRegions (rs ++ ss) a := by
  obtain ⟨r, hr, hi⟩ := h
  exact ⟨r, List.mem_append_right _ hr, hi⟩

/-- The loop head's store target: byte `j` of the eight-byte `%k11.i` store at
`%c.i + 32` is inside the cursor record's extent. -/
theorem cursorK_inside {c ctype cst tok s z e j : Nat} (hj : j < 8) :
    inRegions (stage2StagedWrites c ctype cst tok s z e) (c + 32 + j) :=
  ⟨(c, stage2CursorExtent),
    by simp [stage2StagedWrites], by omega, by simp [stage2CursorExtent]; omega⟩

/-- The nesting arm's type-stack store at the depth the check admits is inside the
type stack's extent. -/
theorem ctype_inside {c ctype cst tok s z e sp : Nat} (h : NestGuard sp) :
    inRegions (stage2StagedWrites c ctype cst tok s z e) (ctype + sp) :=
  ⟨(ctype, stage2StackExtent), by simp [stage2StagedWrites], Nat.le_add_right _ _,
    by have := h; simp only [NestGuard] at this; simp [stage2StackExtent]; omega⟩

/-- The nesting arm's state-stack store at the same index is inside its extent. -/
theorem cst_inside {c ctype cst tok s z e sp : Nat} (h : NestGuard sp) :
    inRegions (stage2StagedWrites c ctype cst tok s z e) (cst + sp) :=
  ⟨(cst, stage2StackExtent), by simp [stage2StagedWrites], Nat.le_add_right _ _,
    by have := h; simp only [NestGuard] at this; simp [stage2StackExtent]; omega⟩

/-- **The loop head's store preserves the walk's frame.**  `while.body.i` writes
eight bytes at `%c.i + 32`; every written byte is inside the cursor record's
extent, which is one of the seven staged objects the frame's list names. -/
theorem walkFrame_cursorK {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {n : Nat}
    {m : Mem} {v : List UInt8} (hv : v.length ≤ 8)
    (h : UnchangedOutside m0 m (walkWideAt G C n)) :
    UnchangedOutside m0 (writeBytes m (C.stage.c + 32) v) (walkWideAt G C n) :=
  h.write_inside (fun k hk => walkWideAt_of_seven
    (cursorK_inside (j := k) (by omega)))

/-- **The nesting arm's type-stack store preserves the frame.** -/
theorem walkFrame_ctype {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {n : Nat}
    {m : Mem} {v : List UInt8} (hv : v.length ≤ 1) (hsp : NestGuard C.sp)
    (h : UnchangedOutside m0 m (walkWideAt G C n)) :
    UnchangedOutside m0 (writeBytes m (C.stage.ctype + C.sp) v) (walkWideAt G C n) :=
  h.write_inside (fun k hk => by
    have hk0 : k = 0 := by omega
    subst hk0
    exact walkWideAt_of_seven (ctype_inside hsp))

/-- **The nesting arm's state-stack store preserves the frame.** -/
theorem walkFrame_cst {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {n : Nat}
    {m : Mem} {v : List UInt8} (hv : v.length ≤ 1) (hsp : NestGuard C.sp)
    (h : UnchangedOutside m0 m (walkWideAt G C n)) :
    UnchangedOutside m0 (writeBytes m (C.stage.cst + C.sp) v) (walkWideAt G C n) :=
  h.write_inside (fun k hk => by
    have hk0 : k = 0 := by omega
    subst hk0
    exact walkWideAt_of_seven (cst_inside hsp))

/-- **The loop head's store, at the invariant.**  `while.body.i` writes the
advanced index to `%c.i + 32`; the store is inside the cursor record's extent, so
the invariant's own frame survives it. -/
theorem WalkInv.frame_cursorK {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G}
    {s : State} (h : WalkInv G C s) {v : List UInt8} (hv : v.length ≤ 8) :
    UnchangedOutside m0 (writeBytes s.mem (C.stage.c + 32) v)
      (walkWideAt G C (s.next - G.next0)) :=
  walkFrame_cursorK hv h.frame

/-- **The nesting arm's two stack stores, at the invariant.**  `if.end24.i` writes
`%ctype.i[sp]` and `%cst.i[sp]`; both are inside the stacks' staged extents at the
depth the `MAXD` check admits (`NestGuard`, the arm's guard — not the invariant's
`depth_cap`), so the invariant's frame survives them. -/
theorem WalkInv.frame_stack {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G}
    {s : State} (h : WalkInv G C s) {cv sv : List UInt8}
    (hcv : cv.length ≤ 1) (hsv : sv.length ≤ 1) (hsp : NestGuard C.sp) :
    UnchangedOutside m0
      (writeBytes (writeBytes s.mem (C.stage.ctype + C.sp) cv)
        (C.stage.cst + C.sp) sv) (walkWideAt G C (s.next - G.next0)) :=
  walkFrame_cst hsv hsp (walkFrame_ctype hcv hsp h.frame)

-- The three store families' provenance, off the pinned body: the cursor field's
-- `gep` at the loop entry, and the two stack stores at the `zext` of the depth.
#guard gepDef stage2Body "while.body.i.lr.ph" "%k11.i" = some ("%c.i", 32)
#guard storeTargets stage2Body "if.end24.i" =
  [("%arrayidx30.i", Ty.int 8), ("%arrayidx32.i", Ty.int 8)]

-- The `MAXD` check the indexing bound comes from, and the two `gep`s it guards.
#guard (stage2Body.blocks.flatMap (·.instrs)).any (fun i =>
  match i with
  | .icmp _ .ugt 32 (.reg "%sp.i.0248") (.imm (.int 32 (BitVec.ofNat 32 519))) => true
  | _ => false) = true

-- The two reserves read the log's own fields: the arena's cursor and capacity at
-- `%z + 48`/`%z + 56`, the event stream's length and capacity at
-- `%z + 8`/`%z + 16`.  The checks themselves write no memory; the cursor moves in
-- the store after them.
#guard gepDef stage2Body "entry" "%alen" = some ("%z", 48)
#guard gepDef stage2Body "entry" "%acap" = some ("%z", 56)
#guard gepDef stage2Body "entry" "%len" = some ("%z", 8)
#guard gepDef stage2Body "entry" "%cap" = some ("%z", 16)
#guard storeTargets stage2Body "if.end.i.i" = []

/-! #### What resists, in order

Three things stand between this invariant and the dispatch, and **none of them is
one of the three the lead named** — the nesting and the two reserves are all
*downstream* of the first:

1. **The register facts the dispatch reads.**  The log's four fields are a clause
   of the invariant (`log_len`, `log_cap`, `log_alen`, `log_acap`), read at
   `%z + 8/16/48/56` with the `#guard`s above as the addresses' provenance, so
   `if.end256.i`'s `%add.i82 = (%add.i) + %z.val36` compares `alen + len + 64`
   against the word the staging fixed as `dstcap`; they were **measured** from
   the run's cursors rather than assumed.  The six pointer registers the header
   and the nesting arm read are now carried too, by `WalkPtrs`: `%3` and `%5`
   (the document and entry stream bases, loaded in `entry`), `%k11.i`
   (`%c.i + 32`), `%ctype.i`/`%cst.i` as pointers, and `%hash1.i.i`.  They are
   bindings of the emitted body rather than clauses of the walk's memory, but a
   block's `denoteCode` needs them before its edge can be a step, so they are
   fields of the invariant: produced at the seed (`WalkSeedState` carries them)
   and preserved by `forInc_step`, `scan_step` and `walkBack_step` through
   `WalkPtrs.bind`.  `WalkInv.log_hash` carries the last memory clause the
   nesting arm reads, the zeroed hash word at `%z + 32`.  One register is read
   by a proved block and still not carried: `%ar` (`%z + 40`), which no proved
   block reads yet.  `%8` and the lane `%7` are carried, by `WalkIter`, at the
   header's own read of the document and the entry stream at the carried index —
   the header's step produces them, and `WalkLink.ifEnd24` reads `%8` from the
   invariant rather than taking it as a hypothesis.  The other blocks that
   compare `%8` (`if.end59.i`, `if.end372.i` and the literal comparison's
   neighbours) still take it as a hypothesis of their own lemmas; each is the
   value the invariant now names, and deriving it there is the same one-line
   read, left to those instances.
2. **The dispatch's own completion**, which is where the nesting and both reserves
   are decided; `WalkLocal` is `True` at every block between them.  The *frame*
   question no longer lands here: `WalkInv.frame` is the record's own write
   extent and `WalkInv.frame_cursorK`/`WalkInv.frame_stack` are the two forward
   stores preserved at it.  The two blocks whose edges were named are steps now
   (`whileBody_step`, `ifEnd24_step`), and the trace they belong to is stated
   (`WalkLink`/`WalkChain`, with `WalkLink.whileBody` and `WalkLink.ifEnd24` its
   two proved links).  What remains is the ten predecessors' `phi` facts at
   `cleanup478.i` and the links between the arms.  The two steps now compose with
   the back edge rather than standing beside it: `JsonStage2WalkAssembly` names the
   merge's target state (`cleanup478Out`), so `walkBack_step_at` hands
   `whileBody_step` its two `phi` values and its predecessor by definition, and one
   revolution is a single segment (`WalkDispatch.revolution`).  The links between
   the arms are stated there as `WalkDispatch` — the chain from the head to
   `cleanup478.i` with the index's strict advance and the iteration's price — with
   `WalkDispatchThree`'s three outcomes choosing the revolution or the terminal
   branch, whose run is `WalkTargetRun` (supplied at the merge by `ExitTail`,
   `JsonStage2WalkExitProducer`).
3. **The six sub-unit contracts.**  `s2_init`, `s2_value_pos`, `s2_after_value`,
   `s2_string_body`, `od_scalar_value` and `num_fast_el1` all fall through
   `stage2Calls` to the parameter `sub`, and the `#guard` in `JsonStage2IR` pins
   that list.  `stage2SubCalls` (`JsonStage2Body`) answers all six from their
   bodies in `kernel/json/stage2.c`, so a selection answering `none` at `s2_init`
   is no longer the only choice: the six calls of the pinned body have a model,
   and `stage2Calls_s2_init` … `stage2Calls_num_fast_el1` are the reductions from
   the walk's environment to it.

So `Stage2WalkObligation` is stated and not inhabited, and its *post* half is now
statable at a region that is true of the body: `WalkInv.report` yields
`stage2WalkFrame`'s claim, `Stage2Run` carries the seven and the staging, and
`stage2Run_boundary` turns the report into `stage2Boundary` at the ABI's thirteen
arguments.  The assembly point is `JsonStage2Body.stage2WalkObligation_at_subCalls`
(completion beside the post) and
`JsonStage2IR.stage2WalkObligation_iff_completion` (the same at the adapter's
record).  What is missing is the obligation's completion conjunct,
`JsonStage2Body.Stage2WalkCompletes`: a budget at which the pinned body returns.
This module states the object that conjunct is a `WalkChain` from the loop head to
a returning last state, proves that a chain *is* such a run at its own step count
(`WalkChain.completes`) and that it carries the measure bound
(`WalkChain.measure_le`), and supplies two of its links — the header's block and
the nesting arm's.  What it does not supply is the chain itself: the links between
the arms, which are per-block `denoteCode` traces at blocks `WalkLocal` is still
`True` at, and the step count against `stage2Budget`.  No well-foundedness claim is
made here: the five proved arms, the closed back edge and the two dispatch steps
are exactly the edges whose measures are shown, and `WalkLocal`'s `True` elsewhere
is the statement of what is not.
-/

/-! ### The back edge: `cleanup478.i`'s merge

The edge's own block is the merge and the exit test: the depth and the index the
dispatch left, and the unsigned test against the entry count.  It writes no
memory, so the region claim and the carried extents are untouched, and its effect
on the carry is the reset — the next iteration's dispatch has spent nothing, so
`inner` is the whole allowance again.  The index does not advance here: the
header's leading `phi` rebinds `%k.0.i249` inside `while.body.i`, which is why the
strict decrease is the next block's (`walkMeasure_step`) and not this edge's. -/

/-- The merge's depth `phi`, as the pinned body writes it. -/
def cleanupSpIncoming : List (String × Operand) :=
  [("if.end473.i", .reg "%sp.i.0248"), ("if.end150.i", .reg "%sp.i.0248"),
   ("if.end162.i", .reg "%sp.i.0248"), ("if.end195.i", .reg "%sp.i.0248"),
   ("if.else334.i", .reg "%sp.i.0248"), ("if.then330.i", .reg "%sp.i.0248"),
   ("if.then.i.i", .reg "%inc33.i"), ("out_reserve.exit.i.i", .reg "%inc33.i"),
   ("if.then.i.i50", .reg "%sub.i"), ("out_reserve.exit.i.i60", .reg "%sub.i")]

/-- The merge's index `phi`, as the pinned body writes it. -/
def cleanupKIncoming : List (String × Operand) :=
  [("if.end473.i", .reg "%inc.i"), ("if.end150.i", .reg "%inc.i"),
   ("if.end162.i", .reg "%inc.i"), ("if.end195.i", .reg "%inc.i"),
   ("if.else334.i", .reg "%inc208.i"), ("if.then330.i", .reg "%inc208.i"),
   ("if.then.i.i", .reg "%inc.i"), ("out_reserve.exit.i.i", .reg "%inc.i"),
   ("if.then.i.i50", .reg "%inc.i"), ("out_reserve.exit.i.i60", .reg "%inc.i")]

/-- `cleanup478.i`: the merge and the unsigned test against the entry count. -/
def cleanup478Block : Block :=
  { name := "cleanup478.i",
    instrs := [
      Instr.phi "%sp.i.1" (Ty.int 32) cleanupSpIncoming,
      Instr.phi "%k.2.i" (Ty.int 64) cleanupKIncoming,
      Instr.icmp "%cmp.i" IPred.ult 64 (Operand.reg "%k.2.i") (Operand.reg "%nep")],
    term := Term.condbr (Operand.reg "%cmp.i") "while.body.i" "if.then485.i" }

/-- The merge is the pinned body's block: the arm is about `stage2Body`, not a
transcription of it. -/
theorem cleanup478_find :
    stage2Body.findBlock "cleanup478.i" = some cleanup478Block := by
  simp [stage2Body, Function.findBlock, findBlockList, cleanup478Block,
    cleanupSpIncoming, cleanupKIncoming]

/-- The merge's two `phi`s and the test, at the state's own environment: the
bindings are the two selected values, and the test's bit is one because the
dispatch's index is still short of the entry count. -/
theorem cleanup478_denote (calls : Calls) (s : State) (p : String)
    {spv k2 : Nat} {spOp kOp : Operand} {nepv : BitVec 64}
    (hpre : s.pre = some p)
    (hsp : phiIncoming p cleanupSpIncoming = some spOp)
    (hspv : evalOperand s spOp = some (.int 32 (BitVec.ofNat 32 spv)))
    (hk : phiIncoming p cleanupKIncoming = some kOp)
    (hkv : evalOperand s kOp = some (.int 64 (BitVec.ofNat 64 k2)))
    (hnep : lookupName s.env "%nep" = some (.int 64 nepv))
    (hguard : k2 < nepv.toNat) :
    denoteCode calls cleanup478Block.instrs s =
      some (((s.bind "%sp.i.1" (.int 32 (BitVec.ofNat 32 spv))).bind
        "%k.2.i" (.int 64 (BitVec.ofNat 64 k2))).bind
        "%cmp.i" (.int 1 (1 : BitVec 1))) := by
  have hult : evalICmp .ult (BitVec.ofNat 64 k2) nepv = (1 : BitVec 1) := by
    have hlt : (BitVec.ofNat 64 k2).toNat < nepv.toNat := by
      rw [BitVec.toNat_ofNat]
      omega
    rw [show evalICmp .ult (BitVec.ofNat 64 k2) nepv
          = BitVec.ofBool (BitVec.ult (BitVec.ofNat 64 k2) nepv) from rfl]
    rw [show BitVec.ult (BitVec.ofNat 64 k2) nepv = true from
      (BitVec.ult_iff_toNat_lt).2 hlt]
    rfl
  have hsel : PhiSelects s p
      [{ dst := "%sp.i.1", ty := Ty.int 32, incoming := cleanupSpIncoming },
       { dst := "%k.2.i", ty := Ty.int 64, incoming := cleanupKIncoming }]
      [("%sp.i.1", .int 32 (BitVec.ofNat 32 spv)),
       ("%k.2.i", .int 64 (BitVec.ofNat 64 k2))] :=
    PhiSelects.cons hsp hspv (PhiSelects.cons hk hkv PhiSelects.nil)
  have hspecs : cleanup478Block.instrs =
      ([{ dst := "%sp.i.1", ty := Ty.int 32, incoming := cleanupSpIncoming },
        { dst := "%k.2.i", ty := Ty.int 64, incoming := cleanupKIncoming }].map
          PhiSpec.instr) ++
        [Instr.icmp "%cmp.i" IPred.ult 64 (Operand.reg "%k.2.i")
          (Operand.reg "%nep")] := by
    simp [cleanup478Block, PhiSpec.instr]
  rw [hspecs, denoteCode_phiRun (specs :=
      [{ dst := "%sp.i.1", ty := Ty.int 32, incoming := cleanupSpIncoming },
       { dst := "%k.2.i", ty := Ty.int 64, incoming := cleanupKIncoming }])
      (vs := [("%sp.i.1", .int 32 (BitVec.ofNat 32 spv)),
              ("%k.2.i", .int 64 (BitVec.ofNat 64 k2))])
      (rest := [Instr.icmp "%cmp.i" IPred.ult 64 (Operand.reg "%k.2.i")
        (Operand.reg "%nep")]) hpre hsel (by rfl)]
  rw [show s.bindAll [("%sp.i.1", .int 32 (BitVec.ofNat 32 spv)),
        ("%k.2.i", .int 64 (BitVec.ofNat 64 k2))] =
      stateAt (("%k.2.i", .int 64 (BitVec.ofNat 64 k2)) ::
        ("%sp.i.1", .int 32 (BitVec.ofNat 32 spv)) :: s.env) s from rfl]
  rw [denoteCode_icmp_ult_reg (x := BitVec.ofNat 64 k2) (y := nepv)
    calls _ s "%cmp.i" "%k.2.i" "%nep"
    (by simp only [lookupName_cons_self])
    (by
      rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide)]
      exact hnep)
    []]
  rw [hult]
  rfl

/-- **The back edge, at the invariant.**  From `WalkInv` at `cleanup478.i`, whose
merge selects the dispatch's depth and index and whose test is clear, one control
step lands at `while.body.i` with every clause preserved and the inner component
reset to the allowance. -/
theorem walkBack_step {calls : Calls} {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G)
    (s : State) (hInv : WalkInv G C s) (hblock : C.block = "cleanup478.i")
    {p : String} {spv k2 : Nat} {spOp kOp : Operand} {nepv : BitVec 64}
    (hpre : s.pre = some p)
    (hsp : phiIncoming p cleanupSpIncoming = some spOp)
    (hspv : evalOperand s spOp = some (.int 32 (BitVec.ofNat 32 spv)))
    (hk : phiIncoming p cleanupKIncoming = some kOp)
    (hkv : evalOperand s kOp = some (.int 64 (BitVec.ofNat 64 k2)))
    (hnep : lookupName s.env "%nep" = some (.int 64 nepv))
    (hguard : k2 < nepv.toNat) :
    ∃ e : State,
      step calls stage2Body s = .jump e ∧
      WalkInv G { C with block := "while.body.i", inner := walkInnerCap G } e ∧
      ∀ k, runFuel calls (1 + k) stage2Body s = runFuel calls k stage2Body e := by
  have hpc : s.pc = "cleanup478.i" := by rw [hInv.pc_eq, hblock]
  let e : State :=
    { ((s.bind "%sp.i.1" (.int 32 (BitVec.ofNat 32 spv))).bind
        "%k.2.i" (.int 64 (BitVec.ofNat 64 k2))).bind
        "%cmp.i" (.int 1 (1 : BitVec 1)) with
      pc := "while.body.i"
      pre := some "cleanup478.i" }
  have hden := cleanup478_denote calls s p hpre hsp hspv hk hkv hnep hguard
  have hterm : cleanup478Block.term =
      Term.condbr (Operand.reg "%cmp.i") "while.body.i" "if.then485.i" := rfl
  have hstep : step calls stage2Body s = .jump e := by
    have hfind : stage2Body.findBlock s.pc = some cleanup478Block := by
      rw [hpc, cleanup478_find]
    simp only [step, hfind, hden, hterm]
    dsimp only [e, State.bind]
    simp only [execTerm, evalOperand, lookupName_cons_self, hpc]
    simp
  refine ⟨e, hstep, ?_, ?_⟩
  · refine
      { pc_eq := rfl
        blockIndex := ?_
        k_le := hInv.k_le
        events_le := by
          show C.events.length ≤ C.k + walkEmitC "while.body.i"
          have h := hInv.events_le
          rw [hblock] at h
          have h1 : walkEmitC "cleanup478.i" = 1 := walkEmitC_of_contains (by decide)
          have h2 : walkEmitC "while.body.i" = 1 := walkEmitC_of_contains (by decide)
          omega
        events_nep := hInv.events_nep
        evlen_eq := hInv.evlen_eq
        evBytes := hInv.evBytes
        alen_le_sum := hInv.alen_le_sum
        alen_ge := hInv.alen_ge
        spans_order := hInv.spans_order
        spans_end := hInv.spans_end
        spans_inside := hInv.spans_inside
        pending_at := hInv.pending_at
        pending_cursor := hInv.pending_cursor
        pending_len := hInv.pending_len
        eoff_le := hInv.eoff_le
        inner_cap := Nat.le_refl _
        depth_cap := hInv.depth_cap
        depth_reg := by
          dsimp only [e, State.bind]
          rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
            lookupName_cons_ne _ _ (by decide)]
          exact hInv.depth_reg
        sp_le_wlen := hInv.sp_le_wlen
        wlen_cap := hInv.wlen_cap
        tyBytes := hInv.tyBytes
        stBytes := hInv.stBytes
        ptrs := by
          dsimp only [e, State.bind]
          have h1 := hInv.ptrs.bind_pair (a := "%sp.i.1") (b := "%k.2.i")
            (va := .int 32 (BitVec.ofNat 32 spv))
            (vb := .int 64 (BitVec.ofNat 64 k2))
            ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩
            ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩
          exact h1.bind (d := "%cmp.i") (v := .int 1 (1 : BitVec 1))
            (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        regs := by
          dsimp only [e, State.bind]
          exact (hInv.regs.bind_pair (a := "%sp.i.1") (b := "%k.2.i")
            (by decide) (by decide)).bind (d := "%cmp.i") (by decide)
        iter := by
          dsimp only [e, State.bind]
          exact ((hInv.iter.bind_pair (a := "%sp.i.1") (b := "%k.2.i")
            (va := .int 32 (BitVec.ofNat 32 spv)) (vb := .int 64 (BitVec.ofNat 64 k2))
            (by decide) (by decide)).bind (d := "%cmp.i")
            (v := .int 1 (1 : BitVec 1)) (by decide))
        log_hash := by dsimp only [e]; exact hInv.log_hash
        log_len := hInv.log_len
        log_cap := hInv.log_cap
        log_alen := hInv.log_alen
        log_acap := hInv.log_acap
        log_base := hInv.log_base
        log_dst := hInv.log_dst
        owned := by dsimp only [e, State.bind]; exact hInv.owned
        root_slot := by dsimp only [e, State.bind]; exact hInv.root_slot
        next_ge := by dsimp only [e, State.bind]; exact hInv.next_ge
        frame := by dsimp only [e, State.bind]; exact hInv.frame
        inc_reg := by
          dsimp only [e, State.bind]
          rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
            lookupName_cons_ne _ _ (by decide)]
          exact hInv.inc_reg
        idx_reg := by
          dsimp only [e, State.bind]
          rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
            lookupName_cons_ne _ _ (by decide)]
          exact hInv.idx_reg
        blockLocal := by simp [WalkLocal] }
    dsimp only [e, State.bind]
    rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide)]
    exact hInv.blockIndex
  · intro k
    rw [show 1 + k = k + 1 from by omega]
    simp only [runFuel, hstep]

/-! ### The outer iteration's arithmetic

The entry loop's back edge (`walkBack_step`) resets `inner` to the next dispatch's
work; the index advances at the header's `phi`, which `while.body.i` binds from
`%k.2.i` inside the block rather than on the edge.  So the iteration is the
two-block step `cleanup478.i → while.body.i → NodeBlock21`: its reset is the
edge's, its advance is the header's block's, and the cap is what makes the reset
survive the radix.  `walkMeasure_step` is the strict decrease, and it is the only
place the cap's value is consumed. -/

/-- **An iteration that advances the index and stays inside the cap is strict.**
`k' ≥ k + 1` takes at least one whole radix off the outer term, and `inner' ≤ cap`
is smaller than the radix that was removed, so the inner component's reset cannot
give it back. -/
theorem walkMeasure_step {m0 : Mem} (G : WalkGeom m0) (C C' : WalkCarry G)
    (hk : C.k < C'.k) (hk' : C'.k ≤ G.nep)
    (hinner : C'.inner ≤ walkInnerCap G) :
    walkMeasure G C' < walkMeasure G C := by
  have hsplit : G.nep - C.k = (G.nep - C'.k) + (C'.k - C.k) := by omega
  have hstep : 1 ≤ C'.k - C.k := by omega
  have hmul : (G.nep - C.k) * (walkInnerCap G + 1)
      = (G.nep - C'.k) * (walkInnerCap G + 1) + (C'.k - C.k) * (walkInnerCap G + 1) := by
    rw [hsplit, Nat.add_mul]
  have hradix : walkInnerCap G + 1 ≤ (C'.k - C.k) * (walkInnerCap G + 1) := by
    simpa using Nat.mul_le_mul_right (walkInnerCap G + 1) hstep
  simp only [walkMeasure]
  rw [hmul]
  omega

/-- **The iteration's measure, from the two halves.**  The edge resets `inner`
(`walkBack_step`) and the header's block advances `k`; the carry with both applied
is the one above, and its decrease is `walkMeasure_step` with the cap holding by
`Nat.le_refl`.  This is the arithmetic the header's block still owes: prove it
lands with the index advanced, and the decrease is this. -/
theorem walkIter_measure {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (k2 : Nat)
    (hk : C.k < k2) (hk' : k2 ≤ G.nep) :
    walkMeasure G { C with k := k2, inner := walkInnerCap G } < walkMeasure G C :=
  walkMeasure_step G C { C with k := k2, inner := walkInnerCap G } hk hk'
    (Nat.le_refl _)

/-! ### The instrument -/

/-- info: 'LeanLLVM.Refinement.WalkGeom.nonempty' depends on axioms: [propext] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.WalkGeom.nonempty

/-- info: 'LeanLLVM.Refinement.WalkInv.alen_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.WalkInv.alen_le

/-- info: 'LeanLLVM.Refinement.WalkInv.evlen_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.WalkInv.evlen_le

/-- info: 'LeanLLVM.Refinement.WalkInv.logArena_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.WalkInv.logArena_le

/-- info: 'LeanLLVM.Refinement.EventRecord.encodedSize_number' depends on axioms: [propext] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.EventRecord.encodedSize_number

/-- info: 'LeanLLVM.Refinement.EventRecord.encodedSize_le' depends on axioms: [propext] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.EventRecord.encodedSize_le

/-- info: 'LeanLLVM.Refinement.EventRecord.sum_encodedSize_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.EventRecord.sum_encodedSize_le

/-- info: 'LeanLLVM.Refinement.forInc_find' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.forInc_find

/-- info: 'LeanLLVM.Refinement.forInc_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.forInc_step

/-- info: 'LeanLLVM.Refinement.WalkGeom.nep_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.WalkGeom.nep_le

/-- info: 'LeanLLVM.Refinement.WalkInv.forInc' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.WalkInv.forInc

/-- info: 'LeanLLVM.Refinement.denoteCode_add_one' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.denoteCode_add_one

/-- info: 'LeanLLVM.Refinement.denoteCode_icmp_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.denoteCode_icmp_eq

/-- info: 'LeanLLVM.Refinement.forInc_denote' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.forInc_denote

/-- info: 'LeanLLVM.Refinement.forInc_term' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.forInc_term

/-- info: 'LeanLLVM.Refinement.forInc_arm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.forInc_arm

/-- info: 'LeanLLVM.Refinement.scanWhitespace_find' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.scanWhitespace_find

/-- info: 'LeanLLVM.Refinement.scanString_find' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.scanString_find

/-- info: 'LeanLLVM.Refinement.scanEscape_find' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.scanEscape_find

/-- info: 'LeanLLVM.Refinement.scanExtraToken_find' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.scanExtraToken_find

/-- info: 'LeanLLVM.Refinement.WalkLocal.whitespace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.WalkLocal.whitespace

/-- info: 'LeanLLVM.Refinement.WalkLocal.whitespaceLanded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.WalkLocal.whitespaceLanded

/-- info: 'LeanLLVM.Refinement.WalkLocal.stringScan' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.WalkLocal.stringScan

/-- info: 'LeanLLVM.Refinement.WalkLocal.stringScanLanded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.WalkLocal.stringScanLanded

/-- info: 'LeanLLVM.Refinement.WalkLocal.escape' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.WalkLocal.escape

/-- info: 'LeanLLVM.Refinement.WalkLocal.escapeLanded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.WalkLocal.escapeLanded

/-- info: 'LeanLLVM.Refinement.WalkLocal.extraToken' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.WalkLocal.extraToken

/-- info: 'LeanLLVM.Refinement.WalkLocal.extraTokenLanded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.WalkLocal.extraTokenLanded

/-- info: 'LeanLLVM.Refinement.WalkInv.whitespace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.WalkInv.whitespace

/-- info: 'LeanLLVM.Refinement.WalkInv.stringScan' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.WalkInv.stringScan

/-- info: 'LeanLLVM.Refinement.WalkInv.escape' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.WalkInv.escape

/-- info: 'LeanLLVM.Refinement.WalkInv.extraToken' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.WalkInv.extraToken

/-- info: 'LeanLLVM.Refinement.scan_denote' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.scan_denote

/-- info: 'LeanLLVM.Refinement.scan_term' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.scan_term

/-- info: 'LeanLLVM.Refinement.scan_step' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.scan_step

/-- info: 'LeanLLVM.Refinement.walkSeed_inner_cap' does not depend on any axioms -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.walkSeed_inner_cap

/-- info: 'LeanLLVM.Refinement.walkSeed_invariant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.walkSeed_invariant

/-- info: 'LeanLLVM.Refinement.WalkInv.report' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.WalkInv.report

/-- info: 'LeanLLVM.Refinement.owns_writeBytes_inside' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.owns_writeBytes_inside

/-- info: 'LeanLLVM.Refinement.owns_writeBytes_outside' does not depend on any axioms -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.owns_writeBytes_outside

/-- info: 'LeanLLVM.Refinement.walkMeasure_step' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.walkMeasure_step

/-- info: 'LeanLLVM.Refinement.cleanup478_find' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.cleanup478_find

/-- info: 'LeanLLVM.Refinement.cleanup478_denote' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.cleanup478_denote

/-- info: 'LeanLLVM.Refinement.walkBack_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.walkBack_step

/-- info: 'LeanLLVM.Refinement.walkIter_measure' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.walkIter_measure

/-- info: 'LeanLLVM.Refinement.walkSeed_depth_cap' depends on axioms: [propext] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.walkSeed_depth_cap

/-- info: 'LeanLLVM.Refinement.cursorK_inside' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.cursorK_inside

/-- info: 'LeanLLVM.Refinement.ctype_inside' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.ctype_inside

/-- info: 'LeanLLVM.Refinement.cst_inside' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.cst_inside


end LeanLLVM.Refinement
