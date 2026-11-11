/-
The pipeline's body discharge: the loop instance, its bound, its cost and its
seed, and the tail's target.

`JsonPipelineRefine.pipeline_satisfies_of_units` takes the body's facts as
`PipelineBodyFacts`, and `JsonStage2Contract.pipeline_satisfies_at_stage2` pins
that bundle's `Γ2` at `Γ_stage2` and still takes it.  Four of the bundle's five
fields are theorems about `pipelineBody` at the staging, and this module proves
them at the staging's own block count:

* `loop` — `PipelineBodyStep.pipelineLoop`, whose `step` is the four arms' steps
  per entry shape and whose `exit` is the spent budget;
* `N_eq` — the iteration bound is `pipelineBlocks (pipelineArgLen args)`, the
  number the loop was instantiated at;
* `cost_le` — the instance's cost is one step, inside the record's per-block
  allowance of four;
* `seed` — `PipelineBodyStep.pipelineSeed`, the three control steps from
  `EntryState` to the loop's first iteration, at the split shape.

# The exit predicate takes the caller's argument list

The fifth field is the tail: from any exit state, the run and the record's own
post.  `pipelineLoopExit` is the predicate the loop hands over, and it is stated
at the caller's memory **and at the caller's argument list**.  The argument list
is not decoration.  The predicate's frame is `UnchangedOutside mem s.mem
(pipelineLoopWrites S)`, whose regions are the carried record's addresses
(`S.sc`, `S.maskSlot`, `S.entw`, `S.xcarry`, …), while every consumer downstream
states its claims at the *caller's* (`sc`, `mk`, `entw`, `xcarry`, …): the UTF-8
window, `Γ_stage2.pre`'s staged objects, and `Γ_pipeline_units.post`'s
`UnchangedOutside`.  Stated at the state alone the predicate says nothing about
which addresses are the caller's, so `S.sc` and `args.sc` were two different
addresses until something said they were the same — and the exit predicate is the
only thing in scope at the moment the claim is made.  `exitArgs` is that tie: the
slot-match between the argument list and `S`, produced by the seed when it builds
`S` from the staging's witnesses and carried by the split and back shapes, so
every step hands it on and the tie arrives with the state rather than being
assumed at the tail.  `PipelineLoop.Exit` and `PipelineLoop.Inv` therefore take
the list — the retype is four-way (`Exit`, `Inv`, `step`, `exit`) because
`PipelineLoop.exit : Inv mem args 0 s → ∃ e, Exit mem args e` cannot produce an
argument-tied exit from an argument-free invariant.

# What the exit predicate carries, and what the tail still owes

`pipelineLoopExit` carries the exit block's program counter, the argument-list
match, the entry stream's read, order, document and block bounds, the
predecessor, the fourteen tail cells, the exiting count, the escape count slot's
content at the exit's memory, its growth, the document read at the exit's memory,
the escape stream's presence at the exit's count, the frame at the caller's
memory, the resumed block index's bound and the caller escape slot's *initial*
count together with its width bound.  The two escape-count facts and the document
read are the loop's own (the invariant's escaped slot, count growth, window read
and emitter writes), and the eight exit-producing steps are where they reach the
predicate.

`PipelineTailTarget` is the `exit` field's conclusion at that predicate: the
run's three steps and the record's own post.  **It is still supplied by the
caller** in this tree, and what remains is one clause, named in the residue note
above the target: stage 2's post pins its two reported extents only through
eight-byte slot words, so `pipelineOutputExtents`'s `ndst' < 2 ^ 64` does not
follow from `Γ_stage2.post` at the staging's witnesses.

What is proved is the rest of the tail's *premises*:

* `stage2Pre_of_exit` — `Γ_stage2.pre` at the exit state's memory with the
  exiting count stored: the document read, its read-past tail, the entry stream
  at the exiting count, the escape list, the arena and event capacities, the two
  cursor slots, the refusal slot, the `uint32` document bound, and the eight
  staged objects' 28 pairwise separations (`DisjointRegions (stage2Regions …)`,
  assembled from the caller's `pipelineRegions` promise with the count growths
  `S.k ≤ 64 * S.i` and `S.xn ≤ S.xn0 + 64 * S.i`);
* `utf8Pre_of_staging` — `Γ_utf8.pre` at the same memory, with the window
  `[0, 0, 0] ++ S.doc` read as `utf8Window`;
* `tailGate_zero_or_one` — the arm's gate is the ABI's flag;
* `positionsBytes_surjective` — every `4 * k`-byte escape stream is a
  `positionsBytes` stream, which is where the post's `ps` witness comes from.

The two call outcomes and their posts (`PipelineUnits.utf8`,
`PipelineUnits.stage2`), the three control steps
(`PipelineBodyStep.pipelineExit_run`) and the frame composition are the rest of
the assembly; `PipelineBodyStep.pipelineExit_accept_at` exposes the acceptance
branch's memory so a post can be read at stage 2's own outcome.  That assembly is
not carried out here, because it cannot conclude: the extents clause it must
produce is the one the residue note shows is not derivable.

Nothing here narrows a record or weakens a post: the tail's target is stated at
the same predicate the loop hands over, now with the caller's arguments in it.
-/
import LeanLLVM.Refinement.JsonStage2Contract
import LeanLLVM.Refinement.PipelineBodyStep

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace LeanLLVM.Refinement

open LeanLLVM
open LeanLLVM.Refinement.JsonPipelineIR
open LeanLLVM.Refinement.JsonEntryIR (readLanes32)

/-! ### The loop's block count, from the staging -/

/-- **The staging's block bound, at the length argument's block count.**  The
staging states `64 * pipelineBlocks bs.length + 63 < 2 ^ 32`, and `pipelineArgLen`
reads the second slot, which the staging pins to `bs.length`, so the count the
loop is instantiated at is the one the staging bounds. -/
theorem pipelineBlocks_argLen_cap {tab base : Nat} {args : List Value} {mem : Mem}
    (hst : pipelineStaging tab base args mem) :
    64 * pipelineBlocks (pipelineArgLen args) + 63 < 2 ^ 32 := by
  obtain ⟨sc, mk, entw, ep, nk, xp, nxp, xcarry, dst, ndst, ev, nev, err, nxp0, ndst0,
    nev0, n, epcap, xpcap, dstcap, evcap, arm, bs, hargs, hn, hlim, hwin, htail, hb3,
    hzero3, hpos, htab, hsc, hcarry, hnk, hnxp, hepcap, hxp, hdstcap, hdst, hev, hevcap,
    hndst, hnev, hroomk, hroomxn, hblk, -⟩ := hst
  have hlen : pipelineArgLen args = bs.length := by
    rw [hargs]
    simp only [pipelineArgLen, hn]
  rw [hlen]
  exact hblk

/-! ### The loop instance and its three arithmetic fields -/

/-- **The loop instance, at the staging's block count.**  `PipelineBodyStep.pipelineLoop`
takes the block bound as a parameter because the invariant is about the state and
not about the arguments; the staging supplies it, so the instance exists at every
staged argument list. -/
def pipelineLoop_of_staging {tab base : Nat} {args : List Value} {mem : Mem}
    (hst : pipelineStaging tab base args mem) (s2 : Calls) (Γ2 : MemContract)
    (units : PipelineUnits tab base s2 Γ2) :
    PipelineLoop (pipelineCalls tab base s2) pipelineBody :=
  pipelineLoop tab base s2 Γ2 units (pipelineBlocks (pipelineArgLen args))
    (pipelineBlocks_argLen_cap hst)

/-- The instance's iteration bound is the staging's block count, by construction. -/
theorem pipelineLoop_of_staging_N {tab base : Nat} {args : List Value} {mem : Mem}
    (hst : pipelineStaging tab base args mem) (s2 : Calls) (Γ2 : MemContract)
    (units : PipelineUnits tab base s2 Γ2) :
    (pipelineLoop_of_staging hst s2 Γ2 units).N = pipelineBlocks (pipelineArgLen args) :=
  rfl

/-- The instance's per-iteration cost is one control step. -/
theorem pipelineLoop_of_staging_cost {tab base : Nat} {args : List Value} {mem : Mem}
    (hst : pipelineStaging tab base args mem) (s2 : Calls) (Γ2 : MemContract)
    (units : PipelineUnits tab base s2 Γ2) :
    (pipelineLoop_of_staging hst s2 Γ2 units).cost = 1 :=
  rfl

/-- One control step is inside the record's per-block allowance of four. -/
theorem pipelineLoop_of_staging_cost_le {tab base : Nat} {args : List Value} {mem : Mem}
    (hst : pipelineStaging tab base args mem) (s2 : Calls) (Γ2 : MemContract)
    (units : PipelineUnits tab base s2 Γ2) :
    (pipelineLoop_of_staging hst s2 Γ2 units).cost ≤ pipelineBlockAllowance := by
  rw [pipelineLoop_of_staging_cost, pipelineBlockAllowance]
  decide

/-! ### The loop's frame, read at a staged object

The exit predicate carries the caller's memory and the frame
`UnchangedOutside mem s.mem (pipelineLoopWrites S)`, whose eight regions are the
loop's own write extents at the carried record's addresses.  The tail reads
*staged* objects — the document window, its read-past tail, the arena and the
event stream at their capacities, the two cursor slots and the refusal slot —
and every one of them is an entry of the caller's `pipelineRegions` list, whose
`DisjointRegions` the staging states.  The loop's write regions are contained in
eight of those entries (the counts and the emitters' extents), so the staged
objects and the write regions are separated by the caller's own promise and the
frame applies at every byte of a staged object.

The pieces below are the arithmetic of that: `loopWrites_cover` is the eight
membership cases, `readBytes_of_loop_frame` and `hasBytes_of_loop_frame` turn a
covering family into a range fact, and `loop_frame_of_staging` applies them to
the seven objects the tail reads. -/

/-- **Two separated regions have no common byte.**  The disjunction is
`DisjointRegions`' pair form: one region ends before the other begins. -/
theorem not_inside_region {a N p W q : Nat}
    (h : a + N ≤ p ∨ p + W ≤ a) (hq1 : a ≤ q) (hq2 : q < a + N)
    (hp1 : p ≤ q) (hp2 : q < p + W) : False := by
  rcases h with h | h <;> omega

/-- **One store leaves a disjoint range as it was.**  The store touches
`[start, start + bs.length)`; a range outside it reads back unchanged, which is
the per-byte frame `readByte_writeBytes_outside` at range granularity. -/
theorem readBytes_writeBytes_of_disjoint {m : Mem} {start : Nat} {bs : List UInt8}
    {a N : Nat} (h : a + N ≤ start ∨ start + bs.length ≤ a) :
    readBytes (writeBytes m start bs) a N = readBytes m a N := by
  refine readBytes_of_readByte_eq (fun k hk => ?_)
  exact readByte_writeBytes_outside m bs (by
    rcases h with h | h
    · exact Or.inl (by omega)
    · exact Or.inr (by omega))

/-- **A separated list separates its members at distinct positions.**  This is
`DisjointRegions` read by index, which is how a concrete `pipelineRegions` list
is used: the entries are literal, so the positions are numerals and the pair is
a projection rather than a case analysis. -/
theorem disjointRegions_pair : ∀ (L : List (Nat × Nat)) (i j : Nat), i < j →
    ∀ (r s : Nat × Nat), L[i]? = some r → L[j]? = some s → DisjointRegions L →
    r.1 + r.2 ≤ s.1 ∨ s.1 + s.2 ≤ r.1
  | [], _, _, _, _, _, hi, _, _ => by simp at hi
  | _ :: t, i, j, hij, r, s, hi, hj, h => by
      obtain ⟨hx, ht⟩ := List.pairwise_cons.mp h
      cases i with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
          subst hi
          cases j with
          | zero => omega
          | succ j' =>
              simp only [List.getElem?_cons_succ] at hj
              exact hx s (List.mem_of_getElem? hj)
      | succ i' =>
          cases j with
          | zero => omega
          | succ j' =>
              simp only [List.getElem?_cons_succ] at hi hj
              exact disjointRegions_pair t i' j' (by omega) r s hi hj ht

/-- **A sub-region of a region separated from an object misses the object.**  The
containment is stated at both ends, so the same fact serves a write region inside
its staged extent and a document window inside the UTF-8 window. -/
theorem outside_of_sub_disjoint {r r' obj : Nat × Nat} {a : Nat}
    (ha1 : obj.1 ≤ a) (ha2 : a < obj.1 + obj.2)
    (hsub : r'.1 ≤ r.1) (hsub2 : r.1 + r.2 ≤ r'.1 + r'.2)
    (hd : r'.1 + r'.2 ≤ obj.1 ∨ obj.1 + obj.2 ≤ r'.1) :
    ¬ (r.1 ≤ a ∧ a < r.1 + r.2) := by
  rintro ⟨hb1, hb2⟩
  rcases hd with h | h <;> omega

/-- **The frame at a staged object, from its covering entries.**  Every region of
`pipelineLoopWrites` is contained in a staged entry that is separated from the
object, so no byte of the object lies inside a write region and the frame's
hypothesis is met at each of them. -/
theorem outside_loopWrites {S : PipelineLoopCarried} {obj : Nat × Nat} {a : Nat}
    (ha1 : obj.1 ≤ a) (ha2 : a < obj.1 + obj.2)
    (hcover : ∀ r ∈ pipelineLoopWrites S, ∃ r' : Nat × Nat,
      r'.1 ≤ r.1 ∧ r.1 + r.2 ≤ r'.1 + r'.2 ∧
        (r'.1 + r'.2 ≤ obj.1 ∨ obj.1 + obj.2 ≤ r'.1)) :
    ∀ r ∈ pipelineLoopWrites S, ¬ (r.1 ≤ a ∧ a < r.1 + r.2) := by
  intro r hr
  obtain ⟨r', h1, h2, hd⟩ := hcover r hr
  exact outside_of_sub_disjoint ha1 ha2 h1 h2 hd

/-- **The loop's write list, contained in the staged extents.**  The eight
membership cases, each a containment in the entry the caller's staging separates:
the carry slot, the mask slot, the entry word, the entry stream at its capacity,
the entry count, the escape stream at its capacity, the escape count and the
escape carry.  The two counted extents are the only non-trivial cases, and both
are the occurrence bounds the loop's own counts satisfy. -/
theorem loopWrites_cover {S : PipelineLoopCarried} {blocks nxp0 : Nat}
    (hkgr : S.k ≤ 64 * blocks) (hxgr : S.xn ≤ nxp0 + 64 * blocks) :
    ∀ r ∈ pipelineLoopWrites S, ∃ r' ∈
      ([(S.sc, 24), (S.maskSlot, 48), (S.entw, 8),
        (S.ep, 4 * (64 * blocks + 9)), (S.nk, 8),
        (S.xp, 4 * (nxp0 + 64 * blocks + 8)), (S.nxp, 8),
        (S.xcarry, 16)] : List (Nat × Nat)),
      r'.1 ≤ r.1 ∧ r.1 + r.2 ≤ r'.1 + r'.2 := by
  intro r hr
  simp only [pipelineLoopWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨(S.sc, 24), by simp, Nat.le_refl _, Nat.le_refl _⟩
  · exact ⟨(S.maskSlot, 48), by simp, Nat.le_refl _, Nat.le_refl _⟩
  · exact ⟨(S.entw, 8), by simp, Nat.le_refl _, Nat.le_refl _⟩
  · refine ⟨(S.ep, 4 * (64 * blocks + 9)), by simp, Nat.le_refl _, ?_⟩
    omega
  · exact ⟨(S.nk, 8), by simp, Nat.le_refl _, Nat.le_refl _⟩
  · refine ⟨(S.xp, 4 * (nxp0 + 64 * blocks + 8)), by simp, Nat.le_refl _, ?_⟩
    unfold batchReserve
    omega
  · exact ⟨(S.nxp, 8), by simp, Nat.le_refl _, Nat.le_refl _⟩
  · exact ⟨(S.xcarry, 16), by simp, Nat.le_refl _, Nat.le_refl _⟩

/-- **Presence survives the loop, at a staged object.**  The same range argument as
`readBytes_of_loop_frame`, in the presence form so that a staging's `HasBytes`
clause reaches the exit state's memory. -/
theorem hasBytes_of_loop_frame {mem m : Mem} {S : PipelineLoopCarried}
    (hframe : UnchangedOutside mem m (pipelineLoopWrites S))
    {obj : Nat × Nat} {a K : Nat}
    (hcover : ∀ r ∈ pipelineLoopWrites S, ∃ r' : Nat × Nat,
      r'.1 ≤ r.1 ∧ r.1 + r.2 ≤ r'.1 + r'.2 ∧
        (r'.1 + r'.2 ≤ obj.1 ∨ obj.1 + obj.2 ≤ r'.1))
    (hinner : ∀ k, k < K → obj.1 ≤ a + k ∧ a + k < obj.1 + obj.2)
    (h : HasBytes mem a K) : HasBytes m a K :=
  hasBytes_of_readByte_eq h (fun k hk => by
    obtain ⟨h1, h2⟩ := hinner k hk
    exact hframe (a + k) (outside_loopWrites h1 h2 hcover))

/-- **The frame, at range granularity, for any staged object.**  The per-byte
obligation is the caller's: it supplies the range inside the object and the eight
covering entries with their separation.  This is the form every staged object's
transport takes. -/
theorem readBytes_of_loop_frame {mem m : Mem} {S : PipelineLoopCarried}
    (hframe : UnchangedOutside mem m (pipelineLoopWrites S))
    {obj : Nat × Nat} {a N : Nat}
    (hcover : ∀ r ∈ pipelineLoopWrites S, ∃ r' : Nat × Nat,
      r'.1 ≤ r.1 ∧ r.1 + r.2 ≤ r'.1 + r'.2 ∧
        (r'.1 + r'.2 ≤ obj.1 ∨ obj.1 + obj.2 ≤ r'.1))
    (hinner : ∀ k, k < N → obj.1 ≤ a + k ∧ a + k < obj.1 + obj.2) :
    readBytes m a N = readBytes mem a N := by
  refine readBytes_of_readByte_eq (fun k hk => ?_)
  obtain ⟨h1, h2⟩ := hinner k hk
  exact hframe (a + k) (outside_loopWrites h1 h2 hcover)

/-- **The document's region against a separated region, through the window and
the read-past tail.**  Stage 2's document region is `(b, n + 32)`, while the
caller stages the document as the UTF-8 window `(b - 3, 3 + 64 * blocks)` and the
read-past tail `(b + 64 * blocks, 32)`: two entries, neither of which contains
the document region.  A region separated from both is separated from their union
inside `[b, b + n + 32)` — which needs `n ≤ 64 * blocks` and the tail's width to
be positive, because a zero-width region placed between the window's end and the
tail's end is separated from both and still meets the union.  The `Wbig`
hypothesis is that positivity at the *staged* width, and `W ≤ Wbig` is the
sub-extent relation. -/
theorem disjoint_doc_of_window_tail {base blocks n x W Wbig : Nat}
    (hWd : W ≤ Wbig) (hWbig : 0 < Wbig) (hn : n ≤ 64 * blocks)
    (hw : base + 64 * blocks ≤ x ∨ x + Wbig ≤ base - 3)
    (ht : base + 64 * blocks + 32 ≤ x ∨ x + Wbig ≤ base + 64 * blocks) :
    base + (n + 32) ≤ x ∨ x + W ≤ base := by
  rcases hw with hw | hw
  · rcases ht with ht | ht
    · exact Or.inl (by omega)
    · omega
  · exact Or.inr (by omega)

/-- **The frame at the staged objects the tail reads.**  The document window, its
read-past tail, the arena and the event stream at their capacities, the two cursor
slots and the refusal slot are all entries of `pipelineRegions`, and the loop's
eight write extents are contained in eight others; the caller's own separation
therefore puts every one of these objects outside the loop's writes, and the exit
frame carries the caller's staging to the state the loop leaves. -/
theorem loop_frame_of_staging {tab base : Nat} {args : List Value} {mem m : Mem}
    (hst : pipelineStaging tab base args mem)
    {S : PipelineLoopCarried} (htie : exitArgs S args)
    (hkgr : S.k ≤ 64 * S.i) (hib : S.i ≤ pipelineBlocks S.n.toNat)
    (hxgr : S.xn ≤ S.xn0 + 64 * S.i)
    (hslot : readBytes mem S.nxp 8 = some (wordBytes 8 S.xn0))
    (hxn0lt : S.xn0 < 2 ^ 63)
    (hframe : UnchangedOutside mem m (pipelineLoopWrites S)) :
    (readBytes m S.b (64 * pipelineBlocks S.n.toNat) =
        readBytes mem S.b (64 * pipelineBlocks S.n.toNat)) ∧
    HasBytes m (S.b + 64 * pipelineBlocks S.n.toNat) 32 ∧
    HasBytes m S.dst S.dstcap.toNat ∧
    (readBytes m S.ndst 8 = readBytes mem S.ndst 8) ∧
    HasBytes m S.ev S.evcap.toNat ∧
    (readBytes m S.nev 8 = readBytes mem S.nev 8) ∧
    HasBytes m S.err 8 ∧
    (readBytes m S.err 8 = readBytes mem S.err 8) := by
  obtain ⟨sc, mk, entw, ep, nk, xp, nxp, xcarry, dst, ndst, ev, nev, err, nxp0, ndst0,
    nev0, n, epcap, xpcap, dstcap, evcap, arm, bs, hargs, hn, hlim, hwin, htail, hb3,
    hzero3, hpos, htab, hsc, hcarry, hcount, hnxp, hepcap, hxp, hdstcap, hdst, hev,
    hnev, hndst, hnev', hroomk, hroomxn, hblk, harm, hreads, hdisj⟩ := hst
  subst hargs
  simp only [exitArgs] at htie
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl⟩ := htie
  have hrn : nxp0 + 64 * pipelineBlocks bs.length + 9 < 2 ^ 63 := hroomxn
  -- the staging's escape count slot is the exit's, so the two witnesses agree
  have hnx0eq : S.xn0 = nxp0 :=
    slotExtent_eq (x := S.xn0) (y := nxp0) (by omega) (by omega) hslot hnxp
  have hbeq : pipelineBlocks S.n.toNat = pipelineBlocks bs.length := by rw [hn]
  have htail' : HasBytes mem (S.b + 64 * pipelineBlocks S.n.toNat) 32 := by
    rw [hbeq]; exact htail
  have herr8 : HasBytes mem S.err 8 := hreads (S.err, 8) (by simp [pipelineReads])
  have hkgr' : S.k ≤ 64 * pipelineBlocks S.n.toNat := by omega
  have hxgr' : S.xn ≤ nxp0 + 64 * pipelineBlocks S.n.toNat := by omega
  simp only [pipelineRegions, Nat.zero_add] at hdisj
  have hwinobj : ∀ r ∈ pipelineLoopWrites S, ∃ r' : Nat × Nat,
      r'.1 ≤ r.1 ∧ r.1 + r.2 ≤ r'.1 + r'.2 ∧
        (r'.1 + r'.2 ≤ S.b - 3 ∨ S.b - 3 + (3 + 64 * pipelineBlocks S.n.toNat) ≤ r'.1) := by
    intro r hr
    obtain ⟨r', hr', h1, h2⟩ := loopWrites_cover (S := S) (blocks := pipelineBlocks S.n.toNat) (nxp0 := nxp0)
      hkgr' hxgr' r hr
    refine ⟨r', h1, h2, ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with h | h | h | h | h | h | h | h
    · subst h
      exact Or.comm.mp (by
        simpa using disjointRegions_pair _ 0 3 (by decide) _ _ rfl rfl hdisj)
    · subst h
      exact Or.comm.mp (by
        simpa using disjointRegions_pair _ 0 4 (by decide) _ _ rfl rfl hdisj)
    · subst h
      exact Or.comm.mp (by
        simpa using disjointRegions_pair _ 0 5 (by decide) _ _ rfl rfl hdisj)
    · subst h
      exact Or.comm.mp (by
        simpa using disjointRegions_pair _ 0 6 (by decide) _ _ rfl rfl hdisj)
    · subst h
      exact Or.comm.mp (by
        simpa using disjointRegions_pair _ 0 7 (by decide) _ _ rfl rfl hdisj)
    · subst h
      exact Or.comm.mp (by
        simpa using disjointRegions_pair _ 0 8 (by decide) _ _ rfl rfl hdisj)
    · subst h
      exact Or.comm.mp (by
        simpa using disjointRegions_pair _ 0 9 (by decide) _ _ rfl rfl hdisj)
    · subst h
      exact Or.comm.mp (by
        simpa using disjointRegions_pair _ 0 10 (by decide) _ _ rfl rfl hdisj)
  have htailobj : ∀ r ∈ pipelineLoopWrites S, ∃ r' : Nat × Nat,
      r'.1 ≤ r.1 ∧ r.1 + r.2 ≤ r'.1 + r'.2 ∧
        (r'.1 + r'.2 ≤ S.b + 64 * pipelineBlocks S.n.toNat ∨ S.b + 64 * pipelineBlocks S.n.toNat + (32) ≤ r'.1) := by
    intro r hr
    obtain ⟨r', hr', h1, h2⟩ := loopWrites_cover (S := S) (blocks := pipelineBlocks S.n.toNat) (nxp0 := nxp0)
      hkgr' hxgr' r hr
    refine ⟨r', h1, h2, ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with h | h | h | h | h | h | h | h
    · subst h
      exact Or.comm.mp (by
        simpa using disjointRegions_pair _ 1 3 (by decide) _ _ rfl rfl hdisj)
    · subst h
      exact Or.comm.mp (by
        simpa using disjointRegions_pair _ 1 4 (by decide) _ _ rfl rfl hdisj)
    · subst h
      exact Or.comm.mp (by
        simpa using disjointRegions_pair _ 1 5 (by decide) _ _ rfl rfl hdisj)
    · subst h
      exact Or.comm.mp (by
        simpa using disjointRegions_pair _ 1 6 (by decide) _ _ rfl rfl hdisj)
    · subst h
      exact Or.comm.mp (by
        simpa using disjointRegions_pair _ 1 7 (by decide) _ _ rfl rfl hdisj)
    · subst h
      exact Or.comm.mp (by
        simpa using disjointRegions_pair _ 1 8 (by decide) _ _ rfl rfl hdisj)
    · subst h
      exact Or.comm.mp (by
        simpa using disjointRegions_pair _ 1 9 (by decide) _ _ rfl rfl hdisj)
    · subst h
      exact Or.comm.mp (by
        simpa using disjointRegions_pair _ 1 10 (by decide) _ _ rfl rfl hdisj)
  have hdstobj : ∀ r ∈ pipelineLoopWrites S, ∃ r' : Nat × Nat,
      r'.1 ≤ r.1 ∧ r.1 + r.2 ≤ r'.1 + r'.2 ∧
        (r'.1 + r'.2 ≤ S.dst ∨ S.dst + (S.dstcap.toNat) ≤ r'.1) := by
    intro r hr
    obtain ⟨r', hr', h1, h2⟩ := loopWrites_cover (S := S) (blocks := pipelineBlocks S.n.toNat) (nxp0 := nxp0)
      hkgr' hxgr' r hr
    refine ⟨r', h1, h2, ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with h | h | h | h | h | h | h | h
    · subst h
      exact by
        simpa using disjointRegions_pair _ 3 11 (by decide) _ _ rfl rfl hdisj
    · subst h
      exact by
        simpa using disjointRegions_pair _ 4 11 (by decide) _ _ rfl rfl hdisj
    · subst h
      exact by
        simpa using disjointRegions_pair _ 5 11 (by decide) _ _ rfl rfl hdisj
    · subst h
      exact by
        simpa using disjointRegions_pair _ 6 11 (by decide) _ _ rfl rfl hdisj
    · subst h
      exact by
        simpa using disjointRegions_pair _ 7 11 (by decide) _ _ rfl rfl hdisj
    · subst h
      exact by
        simpa using disjointRegions_pair _ 8 11 (by decide) _ _ rfl rfl hdisj
    · subst h
      exact by
        simpa using disjointRegions_pair _ 9 11 (by decide) _ _ rfl rfl hdisj
    · subst h
      exact by
        simpa using disjointRegions_pair _ 10 11 (by decide) _ _ rfl rfl hdisj
  have hndstobj : ∀ r ∈ pipelineLoopWrites S, ∃ r' : Nat × Nat,
      r'.1 ≤ r.1 ∧ r.1 + r.2 ≤ r'.1 + r'.2 ∧
        (r'.1 + r'.2 ≤ S.ndst ∨ S.ndst + (8) ≤ r'.1) := by
    intro r hr
    obtain ⟨r', hr', h1, h2⟩ := loopWrites_cover (S := S) (blocks := pipelineBlocks S.n.toNat) (nxp0 := nxp0)
      hkgr' hxgr' r hr
    refine ⟨r', h1, h2, ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with h | h | h | h | h | h | h | h
    · subst h
      exact by
        simpa using disjointRegions_pair _ 3 12 (by decide) _ _ rfl rfl hdisj
    · subst h
      exact by
        simpa using disjointRegions_pair _ 4 12 (by decide) _ _ rfl rfl hdisj
    · subst h
      exact by
        simpa using disjointRegions_pair _ 5 12 (by decide) _ _ rfl rfl hdisj
    · subst h
      exact by
        simpa using disjointRegions_pair _ 6 12 (by decide) _ _ rfl rfl hdisj
    · subst h
      exact by
        simpa using disjointRegions_pair _ 7 12 (by decide) _ _ rfl rfl hdisj
    · subst h
      exact by
        simpa using disjointRegions_pair _ 8 12 (by decide) _ _ rfl rfl hdisj
    · subst h
      exact by
        simpa using disjointRegions_pair _ 9 12 (by decide) _ _ rfl rfl hdisj
    · subst h
      exact by
        simpa using disjointRegions_pair _ 10 12 (by decide) _ _ rfl rfl hdisj
  have hevobj : ∀ r ∈ pipelineLoopWrites S, ∃ r' : Nat × Nat,
      r'.1 ≤ r.1 ∧ r.1 + r.2 ≤ r'.1 + r'.2 ∧
        (r'.1 + r'.2 ≤ S.ev ∨ S.ev + (S.evcap.toNat) ≤ r'.1) := by
    intro r hr
    obtain ⟨r', hr', h1, h2⟩ := loopWrites_cover (S := S) (blocks := pipelineBlocks S.n.toNat) (nxp0 := nxp0)
      hkgr' hxgr' r hr
    refine ⟨r', h1, h2, ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with h | h | h | h | h | h | h | h
    · subst h
      exact by
        simpa using disjointRegions_pair _ 3 13 (by decide) _ _ rfl rfl hdisj
    · subst h
      exact by
        simpa using disjointRegions_pair _ 4 13 (by decide) _ _ rfl rfl hdisj
    · subst h
      exact by
        simpa using disjointRegions_pair _ 5 13 (by decide) _ _ rfl rfl hdisj
    · subst h
      exact by
        simpa using disjointRegions_pair _ 6 13 (by decide) _ _ rfl rfl hdisj
    · subst h
      exact by
        simpa using disjointRegions_pair _ 7 13 (by decide) _ _ rfl rfl hdisj
    · subst h
      exact by
        simpa using disjointRegions_pair _ 8 13 (by decide) _ _ rfl rfl hdisj
    · subst h
      exact by
        simpa using disjointRegions_pair _ 9 13 (by decide) _ _ rfl rfl hdisj
    · subst h
      exact by
        simpa using disjointRegions_pair _ 10 13 (by decide) _ _ rfl rfl hdisj
  have hnevobj : ∀ r ∈ pipelineLoopWrites S, ∃ r' : Nat × Nat,
      r'.1 ≤ r.1 ∧ r.1 + r.2 ≤ r'.1 + r'.2 ∧
        (r'.1 + r'.2 ≤ S.nev ∨ S.nev + (8) ≤ r'.1) := by
    intro r hr
    obtain ⟨r', hr', h1, h2⟩ := loopWrites_cover (S := S) (blocks := pipelineBlocks S.n.toNat) (nxp0 := nxp0)
      hkgr' hxgr' r hr
    refine ⟨r', h1, h2, ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with h | h | h | h | h | h | h | h
    · subst h
      exact by
        simpa using disjointRegions_pair _ 3 14 (by decide) _ _ rfl rfl hdisj
    · subst h
      exact by
        simpa using disjointRegions_pair _ 4 14 (by decide) _ _ rfl rfl hdisj
    · subst h
      exact by
        simpa using disjointRegions_pair _ 5 14 (by decide) _ _ rfl rfl hdisj
    · subst h
      exact by
        simpa using disjointRegions_pair _ 6 14 (by decide) _ _ rfl rfl hdisj
    · subst h
      exact by
        simpa using disjointRegions_pair _ 7 14 (by decide) _ _ rfl rfl hdisj
    · subst h
      exact by
        simpa using disjointRegions_pair _ 8 14 (by decide) _ _ rfl rfl hdisj
    · subst h
      exact by
        simpa using disjointRegions_pair _ 9 14 (by decide) _ _ rfl rfl hdisj
    · subst h
      exact by
        simpa using disjointRegions_pair _ 10 14 (by decide) _ _ rfl rfl hdisj
  have herrobj : ∀ r ∈ pipelineLoopWrites S, ∃ r' : Nat × Nat,
      r'.1 ≤ r.1 ∧ r.1 + r.2 ≤ r'.1 + r'.2 ∧
        (r'.1 + r'.2 ≤ S.err ∨ S.err + (8) ≤ r'.1) := by
    intro r hr
    obtain ⟨r', hr', h1, h2⟩ := loopWrites_cover (S := S) (blocks := pipelineBlocks S.n.toNat) (nxp0 := nxp0)
      hkgr' hxgr' r hr
    refine ⟨r', h1, h2, ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with h | h | h | h | h | h | h | h
    · subst h
      exact by
        simpa using disjointRegions_pair _ 3 15 (by decide) _ _ rfl rfl hdisj
    · subst h
      exact by
        simpa using disjointRegions_pair _ 4 15 (by decide) _ _ rfl rfl hdisj
    · subst h
      exact by
        simpa using disjointRegions_pair _ 5 15 (by decide) _ _ rfl rfl hdisj
    · subst h
      exact by
        simpa using disjointRegions_pair _ 6 15 (by decide) _ _ rfl rfl hdisj
    · subst h
      exact by
        simpa using disjointRegions_pair _ 7 15 (by decide) _ _ rfl rfl hdisj
    · subst h
      exact by
        simpa using disjointRegions_pair _ 8 15 (by decide) _ _ rfl rfl hdisj
    · subst h
      exact by
        simpa using disjointRegions_pair _ 9 15 (by decide) _ _ rfl rfl hdisj
    · subst h
      exact by
        simpa using disjointRegions_pair _ 10 15 (by decide) _ _ rfl rfl hdisj

  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine readBytes_of_loop_frame hframe (obj := (S.b - 3, 3 + 64 * pipelineBlocks S.n.toNat)) hwinobj (fun k hk => ?_)
    omega
  · refine hasBytes_of_loop_frame hframe (obj := (S.b + 64 * pipelineBlocks S.n.toNat, 32)) htailobj (fun k hk => ?_) htail'
    omega
  · refine hasBytes_of_loop_frame hframe (obj := (S.dst, S.dstcap.toNat)) hdstobj (fun k hk => ?_) hdst
    omega
  · refine readBytes_of_loop_frame hframe (obj := (S.ndst, 8)) hndstobj (fun k hk => ?_)
    omega
  · refine hasBytes_of_loop_frame hframe (obj := (S.ev, S.evcap.toNat)) hevobj (fun k hk => ?_) hev
    omega
  · refine readBytes_of_loop_frame hframe (obj := (S.nev, 8)) hnevobj (fun k hk => ?_)
    omega
  · refine hasBytes_of_loop_frame hframe (obj := (S.err, 8)) herrobj (fun k hk => ?_) herr8
    omega
  · refine readBytes_of_loop_frame hframe (obj := (S.err, 8)) herrobj (fun k hk => ?_)
    omega

/-- **An arena capacity is not a lower-bound consequence.**  Stage 2's record reads
`HasBytes mem dst dstcap`, while a caller's staging can only promise the extent it
actually staged; a bound `reached ≤ dstcap` together with presence at `reached`
does not give presence at `dstcap`.  The witness is an arena of sixty-four bytes
whose capacity names a hundred.  This is why the pipeline's staging states the
arena's presence at its capacity and not at the expander's reached extent: the
narrower clause left the tail's stage-2 call without its precondition. -/
theorem hasBytes_capacity_not_implied_by_bound :
    ∃ (mem : Mem) (dst dstcap reached : Nat),
      reached ≤ dstcap ∧ HasBytes mem dst reached ∧ ¬ HasBytes mem dst dstcap := by
  refine ⟨writeBytes [] 0 (List.replicate 64 0), 0, 100, 64, by decide, ?_, ?_⟩
  · exact ⟨List.replicate 64 0, readBytes_writeBytes_same [] (bs := List.replicate 64 0) (addr := 0)⟩
  · rintro ⟨vs, hvs⟩
    have hnone : readBytes (writeBytes [] 0 (List.replicate 64 0)) 0 100 = none := by decide
    rw [hnone] at hvs
    cases hvs

/-! ### Piece 2: stage 2's staging at the loop's exit

The tail's first call needs `Γ_stage2.pre` at the memory the exit block leaves
`if.end34` in: the exit state's memory with the exiting count stored at `%nk`.
Every clause is either the caller's staging (`pipelineStaging`) read through the
loop's frame, the loop's own exit facts, or the staging's capacity clauses.

The two extents whose staged width differs from the record's are the entry stream
and the escape list: the record reads `k` and `xd` entries, the staging separates
the whole capacity.  Both are sub-extents, which is why the discharge needs
`S.k ≤ 64 * S.i` and `S.xn ≤ S.xn0 + 64 * S.i`.  The document is a *union*: the
record names `(b, n + 32)` and the staging names the window and the read-past tail
as two entries, so its separation is `disjoint_doc_of_window_tail`.

The frame carries the caller's staged bytes to the exit state's memory; the store
at `%nk` is inside `pipelineLoopWrites`, so the seven staged objects it must miss
are separated from it by the same pairwise promise. -/

/-- A present range reads back from an interior offset.  Presence of `L` bytes at
`a` gives presence of `K` bytes at `a + n` when `n + K ≤ L`. -/
theorem hasBytes_shift_of_read {m : Mem} {a L n K : Nat} (hnK : n + K ≤ L)
    {bs : List UInt8} (h : readBytes m a L = some bs) : HasBytes m (a + n) K := by
  have hL : L = n + (L - n) := by omega
  obtain ⟨-, h2⟩ := readBytes_split m a n (L - n) (by rw [← hL]; exact h)
  have hd : L - n = K + (L - n - K) := by omega
  rw [hd] at h2
  exact ⟨_, (readBytes_split m (a + n) K (L - n - K) h2).1⟩

/-- **A read is unchanged by a store it misses.**  The lane reader through a
`writeBytes` whose range misses every lane's four bytes. -/
theorem readLanes32_writeBytes_disjoint {m : Mem} {start : Nat} {ws : List UInt8}
    {addr k : Nat}
    (h : ∀ j : Nat, j < k → addr + 4 * j + 4 ≤ start ∨ start + ws.length ≤ addr + 4 * j) :
    readLanes32 (writeBytes m start ws) addr k = readLanes32 m addr k := by
  refine JsonEntrySteps.readLanes32_congr_bytes (fun j hj => ?_)
  have hj4 : j / 4 < k := by omega
  have hjr : j = 4 * (j / 4) + j % 4 := (Nat.div_add_mod j 4).symm
  have hmod : j % 4 < 4 := Nat.mod_lt _ (by decide)
  refine readByte_writeBytes_outside m ws ?_
  rcases h (j / 4) hj4 with h' | h'
  · left; omega
  · right; omega

/-- **Stage 2's `pre` at the loop's exit.**  The document read, its read-past
tail, the entry stream at the exiting count, the escape list at the escape
count, the arena and event capacities, the two cursor slots, the refusal slot,
the document's `uint32` bound and the eight staged objects' separation.

`sm` is the exit state's memory and the conclusion's memory is that state's with
the exiting count stored at `%nk` — the memory `for.cond.cleanup` hands
`if.end34`.  `hld` is the escape count's load, so `x37` is the value the
record's sixth slot receives. -/
theorem stage2Pre_of_exit
    {tab base : Nat} {args : List Value} {mem sm : Mem} {next : Nat}
    {S : PipelineLoopCarried} {kv x37 : BitVec 64}
    (hst : pipelineStaging tab base args mem) (htie : exitArgs S args)
    (hkgr : S.k ≤ 64 * S.i) (hib : S.i ≤ pipelineBlocks S.n.toNat)
    (hxgr : S.xn ≤ S.xn0 + 64 * S.i)
    (hsxn : readBytes sm S.nxp 8 = some (wordBytes 8 S.xn))
    (hslot : readBytes mem S.nxp 8 = some (wordBytes 8 S.xn0))
    (hxn0lt : S.xn0 < 2 ^ 63)
    (hframe : UnchangedOutside mem sm (pipelineLoopWrites S))
    (hstream : readLanes32 sm S.ep S.k = some S.ent)
    (hord : S.ent.Pairwise (· < ·))
    (hbnd : ∀ q ∈ S.ent, q < S.n.toNat)
    (hsxp : HasBytes sm S.xp (4 * S.xn))
    (hkv : kv = BitVec.ofNat 64 S.k)
    (hld : readBytes (writeBytes sm S.nk (natToBytes kv.toNat 8)) S.nxp 8 =
      some (natToBytes x37.toNat 8)) :
    Γ_stage2.pre
      (stage2Args S.b S.ep S.xp S.dst S.ndst S.ev S.nev S.err S.n kv x37
        S.dstcap S.evcap)
      (writeBytes sm S.nk (natToBytes kv.toNat 8)) next := by
  -- the frame's projections at the seven staged objects
  obtain ⟨hdoc, htailpos, hdstpos, hndstpos, hevpos, hnevpos, herrpos, herrread⟩ :=
    loop_frame_of_staging hst htie hkgr hib hxgr hslot hxn0lt hframe
  obtain ⟨sc, mk, entw, ep, nk, xp, nxp, xcarry, dst, ndst, ev, nev, err, nxp0, ndst0,
    nev0, n, epcap, xpcap, dstcap, evcap, arm, bs, hargs, hn, hlim, hwin, htail, hb3,
    hzero3, hpos, htab, hsc, hcarry, hcount, hnxp, hepcap, hxp, hdstcap, hdst, hev,
    hnev, hndst, hnev', hroomk, hroomxn, hblk, harm, hreads, hdisj⟩ := hst
  subst hargs
  simp only [exitArgs] at htie
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl⟩ := htie
  -- the caller's separation, at the list the region definitions reduce to
  simp only [pipelineRegions, Nat.zero_add] at hdisj
  -- the escape count's first value is the staging's, so its growth bounds the count
  have hrn : nxp0 + 64 * pipelineBlocks bs.length + 9 < 2 ^ 63 := hroomxn
  have hnx0eq : S.xn0 = nxp0 :=
    slotExtent_eq (x := S.xn0) (y := nxp0) (by omega) (by omega) hslot hnxp
  have hnB : pipelineBlocks S.n.toNat = pipelineBlocks bs.length := by rw [hn]
  have hble : bs.length ≤ 64 * pipelineBlocks bs.length := le_blocks_mul bs.length
  have hkB : S.k ≤ 64 * pipelineBlocks S.n.toNat := by omega
  have hxnB : S.xn ≤ nxp0 + 64 * pipelineBlocks S.n.toNat := by omega
  have hxn64 : S.xn < 2 ^ 64 := by
    have h1 : 64 * S.i ≤ 64 * pipelineBlocks S.n.toNat := Nat.mul_le_mul_left 64 hib
    omega
  -- the store at the count slot misses each object the record reads
  have sep_doc_nk : S.b + (S.n.toNat + 32) ≤ S.nk ∨ S.nk + 8 ≤ S.b := by
    have h0 : (S.b - 3) + (3 + 64 * pipelineBlocks S.n.toNat) ≤ S.nk ∨
        S.nk + 8 ≤ S.b - 3 := by
      simpa using disjointRegions_pair _ 0 7 (by decide) _ _ rfl rfl hdisj
    have h1 : (S.b + 64 * pipelineBlocks S.n.toNat) + 32 ≤ S.nk ∨
        S.nk + 8 ≤ S.b + 64 * pipelineBlocks S.n.toNat := by
      simpa using disjointRegions_pair _ 1 7 (by decide) _ _ rfl rfl hdisj
    exact disjoint_doc_of_window_tail (base := S.b)
      (blocks := pipelineBlocks S.n.toNat) (n := S.n.toNat) (x := S.nk)
      (W := 8) (Wbig := 8) (by omega) (by omega)
      (by have := le_blocks_mul S.n.toNat; omega) (by omega) (by omega)
  have sep_nk_ndst : S.nk + 8 ≤ S.ndst ∨ S.ndst + 8 ≤ S.nk := by
    simpa using disjointRegions_pair _ 7 12 (by decide) _ _ rfl rfl hdisj
  have sep_nk_nev : S.nk + 8 ≤ S.nev ∨ S.nev + 8 ≤ S.nk := by
    simpa using disjointRegions_pair _ 7 14 (by decide) _ _ rfl rfl hdisj
  have sep_nk_nxp : S.nk + 8 ≤ S.nxp ∨ S.nxp + 8 ≤ S.nk := by
    simpa using disjointRegions_pair _ 7 9 (by decide) _ _ rfl rfl hdisj
  have sep_ep_nk : S.ep + 4 * (64 * pipelineBlocks S.n.toNat + 9) ≤ S.nk ∨
      S.nk + 8 ≤ S.ep := by
    simpa using disjointRegions_pair _ 6 7 (by decide) _ _ rfl rfl hdisj
  -- the escape count's load is the exit's own slot content
  have hld_sm : readBytes sm S.nxp 8 = some (natToBytes x37.toNat 8) := by
    refine ((readBytes_writeBytes_of_disjoint (m := sm) (start := S.nk)
      (bs := natToBytes kv.toNat 8) (a := S.nxp) (N := 8) ?_).symm).trans hld
    rw [natToBytes_length]
    omega
  have hx37 : x37.toNat = S.xn := by
    have hw := Option.some.inj (hsxn.symm.trans hld_sm)
    have hres := wordBytes_residue hw
    rw [Nat.mod_eq_of_lt hxn64, Nat.mod_eq_of_lt (by omega)] at hres
    exact hres.symm
  -- the document's read, at the caller's memory as the staging states it
  obtain ⟨hbsmem, -⟩ := readBytes_split mem S.b bs.length
    (64 * pipelineBlocks bs.length - bs.length) (by
      rw [Nat.add_sub_of_le hble]; exact hwin)
  rw [List.take_left] at hbsmem
  -- and at the exit state's memory, through the loop's frame
  have hwinN : readBytes mem S.b (64 * pipelineBlocks S.n.toNat) =
      some (bs ++ List.replicate (64 * pipelineBlocks S.n.toNat - bs.length) 0) := by
    rw [hnB]; exact hwin
  have hsmL : readBytes sm S.b (64 * pipelineBlocks S.n.toNat) =
      some (bs ++ List.replicate (64 * pipelineBlocks S.n.toNat - bs.length) 0) :=
    hdoc.trans hwinN
  have hbsm : readBytes sm S.b bs.length = some bs := by
    obtain ⟨h1, -⟩ := readBytes_split sm S.b bs.length
      (64 * pipelineBlocks S.n.toNat - bs.length) (by
        rw [Nat.add_sub_of_le (by rw [hnB]; exact hble)]; exact hsmL)
    rwa [List.take_left] at h1
  -- and at the memory the count slot's store leaves
  have hdoc_ms : readBytes (writeBytes sm S.nk (natToBytes kv.toNat 8)) S.b
      S.n.toNat = some bs := by
    refine (readBytes_writeBytes_of_disjoint (m := sm) (start := S.nk)
      (bs := natToBytes kv.toNat 8) (a := S.b) (N := S.n.toNat) ?_).trans ?_
    · rw [natToBytes_length]; omega
    · rw [hn]; exact hbsm
  -- the read-past tail, at the exit state's memory, at the document's end
  have htail_sm : HasBytes sm (S.b + S.n.toNat) 32 := by
    obtain ⟨tvs, htvs⟩ := htailpos
    have happ := JsonEntrySteps.readBytes_append sm (64 * pipelineBlocks S.n.toNat) S.b
      (bs ++ List.replicate (64 * pipelineBlocks S.n.toNat - bs.length) 0) 32 tvs
      hsmL htvs
    refine hasBytes_shift_of_read (a := S.b)
      (L := 64 * pipelineBlocks S.n.toNat + 32) (n := S.n.toNat) (K := 32) ?_ happ
    omega
  -- the entry stream, through the store's separation from its capacity
  have hlanes : readLanes32 (writeBytes sm S.nk (natToBytes kv.toNat 8)) S.ep S.k =
      some S.ent := by
    have hcong := readLanes32_writeBytes_disjoint (m := sm) (start := S.nk)
      (ws := natToBytes kv.toNat 8) (addr := S.ep) (k := S.k) (fun j hj => by
        rw [natToBytes_length]
        omega)
    exact hcong.trans hstream
  -- the escape list's staged presence, at the count the load read
  have hesc_sm : HasBytes sm S.xp (4 * x37.toNat) := by rw [hx37]; exact hsxp
  -- everything the store at the count slot must leave alone
  have hesc_ms : HasBytes (writeBytes sm S.nk (natToBytes kv.toNat 8)) S.xp
      (4 * x37.toNat) := hasBytes_writeBytes hesc_sm
  have htail_ms : HasBytes (writeBytes sm S.nk (natToBytes kv.toNat 8))
      (S.b + S.n.toNat) 32 := hasBytes_writeBytes htail_sm
  have hdst_ms : HasBytes (writeBytes sm S.nk (natToBytes kv.toNat 8)) S.dst
      S.dstcap.toNat := hasBytes_writeBytes hdstpos
  have hev_ms : HasBytes (writeBytes sm S.nk (natToBytes kv.toNat 8)) S.ev
      S.evcap.toNat := hasBytes_writeBytes hevpos
  have herr_ms : HasBytes (writeBytes sm S.nk (natToBytes kv.toNat 8)) S.err 8 :=
    hasBytes_writeBytes herrpos
  have hndst_ms : readBytes (writeBytes sm S.nk (natToBytes kv.toNat 8)) S.ndst 8 =
      some (wordBytes 8 ndst0) := by
    refine (readBytes_writeBytes_of_disjoint (start := S.nk)
      (bs := natToBytes kv.toNat 8) (a := S.ndst) (N := 8) ?_).trans ?_
    · rw [natToBytes_length]; omega
    · exact hndstpos.trans hndst
  have hnev_ms : readBytes (writeBytes sm S.nk (natToBytes kv.toNat 8)) S.nev 8 =
      some (wordBytes 8 nev0) := by
    refine (readBytes_writeBytes_of_disjoint (m := sm) (start := S.nk)
      (bs := natToBytes kv.toNat 8) (a := S.nev) (N := 8) ?_).trans ?_
    · rw [natToBytes_length]; omega
    · exact hnevpos.trans hnev'
  -- the caller's pairwise promise, as the document's separation from the seven
  have sep_doc_ep : S.b + (S.n.toNat + 32) ≤ S.ep ∨ S.ep + 4 * S.k ≤ S.b := by
    have h0 : (S.b - 3) + (3 + 64 * pipelineBlocks S.n.toNat) ≤ S.ep ∨
        S.ep + 4 * (64 * pipelineBlocks S.n.toNat + 9) ≤ S.b - 3 := by
      simpa using disjointRegions_pair _ 0 6 (by decide) _ _ rfl rfl hdisj
    have h1 : (S.b + 64 * pipelineBlocks S.n.toNat) + 32 ≤ S.ep ∨
        S.ep + 4 * (64 * pipelineBlocks S.n.toNat + 9) ≤
          S.b + 64 * pipelineBlocks S.n.toNat := by
      simpa using disjointRegions_pair _ 1 6 (by decide) _ _ rfl rfl hdisj
    exact disjoint_doc_of_window_tail (base := S.b)
      (blocks := pipelineBlocks S.n.toNat) (n := S.n.toNat) (x := S.ep)
      (W := 4 * S.k) (Wbig := 4 * (64 * pipelineBlocks S.n.toNat + 9))
      (by omega) (by omega) (by have := le_blocks_mul S.n.toNat; omega)
      (by omega) (by omega)
  have sep_doc_xp : S.b + (S.n.toNat + 32) ≤ S.xp ∨ S.xp + 4 * S.xn ≤ S.b := by
    have h0 : (S.b - 3) + (3 + 64 * pipelineBlocks S.n.toNat) ≤ S.xp ∨
        S.xp + 4 * (nxp0 + 64 * pipelineBlocks S.n.toNat + 8) ≤ S.b - 3 := by
      simpa using disjointRegions_pair _ 0 8 (by decide) _ _ rfl rfl hdisj
    have h1 : (S.b + 64 * pipelineBlocks S.n.toNat) + 32 ≤ S.xp ∨
        S.xp + 4 * (nxp0 + 64 * pipelineBlocks S.n.toNat + 8) ≤
          S.b + 64 * pipelineBlocks S.n.toNat := by
      simpa using disjointRegions_pair _ 1 8 (by decide) _ _ rfl rfl hdisj
    exact disjoint_doc_of_window_tail (base := S.b)
      (blocks := pipelineBlocks S.n.toNat) (n := S.n.toNat) (x := S.xp)
      (W := 4 * S.xn) (Wbig := 4 * (nxp0 + 64 * pipelineBlocks S.n.toNat + 8))
      (by omega) (by omega) (by have := le_blocks_mul S.n.toNat; omega)
      (by omega) (by omega)
  have sep_doc_dst : S.b + (S.n.toNat + 32) ≤ S.dst ∨
      S.dst + (ndst0 + S.n.toNat + 64) ≤ S.b := by
    have h0 : (S.b - 3) + (3 + 64 * pipelineBlocks S.n.toNat) ≤ S.dst ∨
        S.dst + S.dstcap.toNat ≤ S.b - 3 := by
      simpa using disjointRegions_pair _ 0 11 (by decide) _ _ rfl rfl hdisj
    have h1 : (S.b + 64 * pipelineBlocks S.n.toNat) + 32 ≤ S.dst ∨
        S.dst + S.dstcap.toNat ≤ S.b + 64 * pipelineBlocks S.n.toNat := by
      simpa using disjointRegions_pair _ 1 11 (by decide) _ _ rfl rfl hdisj
    exact disjoint_doc_of_window_tail (base := S.b)
      (blocks := pipelineBlocks S.n.toNat) (n := S.n.toNat) (x := S.dst)
      (W := ndst0 + S.n.toNat + 64) (Wbig := S.dstcap.toNat)
      (by omega) (by omega) (by have := le_blocks_mul S.n.toNat; omega)
      (by omega) (by omega)
  have sep_doc_ev : S.b + (S.n.toNat + 32) ≤ S.ev ∨
      S.ev + S.evcap.toNat ≤ S.b := by
    have h0 : (S.b - 3) + (3 + 64 * pipelineBlocks S.n.toNat) ≤ S.ev ∨
        S.ev + S.evcap.toNat ≤ S.b - 3 := by
      simpa using disjointRegions_pair _ 0 13 (by decide) _ _ rfl rfl hdisj
    have h1 : (S.b + 64 * pipelineBlocks S.n.toNat) + 32 ≤ S.ev ∨
        S.ev + S.evcap.toNat ≤ S.b + 64 * pipelineBlocks S.n.toNat := by
      simpa using disjointRegions_pair _ 1 13 (by decide) _ _ rfl rfl hdisj
    exact disjoint_doc_of_window_tail (base := S.b)
      (blocks := pipelineBlocks S.n.toNat) (n := S.n.toNat) (x := S.ev)
      (W := S.evcap.toNat) (Wbig := S.evcap.toNat)
      (by omega) (by omega) (by have := le_blocks_mul S.n.toNat; omega)
      (by omega) (by omega)
  have sep_doc_ndst : S.b + (S.n.toNat + 32) ≤ S.ndst ∨ S.ndst + 8 ≤ S.b := by
    have h0 : (S.b - 3) + (3 + 64 * pipelineBlocks S.n.toNat) ≤ S.ndst ∨
        S.ndst + 8 ≤ S.b - 3 := by
      simpa using disjointRegions_pair _ 0 12 (by decide) _ _ rfl rfl hdisj
    have h1 : (S.b + 64 * pipelineBlocks S.n.toNat) + 32 ≤ S.ndst ∨
        S.ndst + 8 ≤ S.b + 64 * pipelineBlocks S.n.toNat := by
      simpa using disjointRegions_pair _ 1 12 (by decide) _ _ rfl rfl hdisj
    exact disjoint_doc_of_window_tail (base := S.b)
      (blocks := pipelineBlocks S.n.toNat) (n := S.n.toNat) (x := S.ndst)
      (W := 8) (Wbig := 8) (by omega) (by omega)
      (by have := le_blocks_mul S.n.toNat; omega) (by omega) (by omega)
  have sep_doc_nev : S.b + (S.n.toNat + 32) ≤ S.nev ∨ S.nev + 8 ≤ S.b := by
    have h0 : (S.b - 3) + (3 + 64 * pipelineBlocks S.n.toNat) ≤ S.nev ∨
        S.nev + 8 ≤ S.b - 3 := by
      simpa using disjointRegions_pair _ 0 14 (by decide) _ _ rfl rfl hdisj
    have h1 : (S.b + 64 * pipelineBlocks S.n.toNat) + 32 ≤ S.nev ∨
        S.nev + 8 ≤ S.b + 64 * pipelineBlocks S.n.toNat := by
      simpa using disjointRegions_pair _ 1 14 (by decide) _ _ rfl rfl hdisj
    exact disjoint_doc_of_window_tail (base := S.b)
      (blocks := pipelineBlocks S.n.toNat) (n := S.n.toNat) (x := S.nev)
      (W := 8) (Wbig := 8) (by omega) (by omega)
      (by have := le_blocks_mul S.n.toNat; omega) (by omega) (by omega)
  have sep_doc_err : S.b + (S.n.toNat + 32) ≤ S.err ∨ S.err + 8 ≤ S.b := by
    have h0 : (S.b - 3) + (3 + 64 * pipelineBlocks S.n.toNat) ≤ S.err ∨
        S.err + 8 ≤ S.b - 3 := by
      simpa using disjointRegions_pair _ 0 15 (by decide) _ _ rfl rfl hdisj
    have h1 : (S.b + 64 * pipelineBlocks S.n.toNat) + 32 ≤ S.err ∨
        S.err + 8 ≤ S.b + 64 * pipelineBlocks S.n.toNat := by
      simpa using disjointRegions_pair _ 1 15 (by decide) _ _ rfl rfl hdisj
    exact disjoint_doc_of_window_tail (base := S.b)
      (blocks := pipelineBlocks S.n.toNat) (n := S.n.toNat) (x := S.err)
      (W := 8) (Wbig := 8) (by omega) (by omega)
      (by have := le_blocks_mul S.n.toNat; omega) (by omega) (by omega)
  -- the eight staged objects, pairwise
  have hdisj2 : DisjointRegions
      (stage2Regions S.b S.n.toNat S.ep S.k S.xp S.xn S.dst ndst0 S.ev
        S.evcap.toNat S.ndst S.nev S.err) := by
    rw [show stage2Regions S.b S.n.toNat S.ep S.k S.xp S.xn S.dst ndst0 S.ev
        S.evcap.toNat S.ndst S.nev S.err =
      [(S.b, S.n.toNat + 32), (S.ep, 4 * S.k), (S.xp, 4 * S.xn),
       (S.dst, ndst0 + S.n.toNat + 64), (S.ev, S.evcap.toNat),
       (S.ndst, 8), (S.nev, 8), (S.err, 8)] from rfl]
    refine List.Pairwise.cons ?_ (List.Pairwise.cons ?_ (List.Pairwise.cons ?_
      (List.Pairwise.cons ?_ (List.Pairwise.cons ?_ (List.Pairwise.cons ?_
      (List.Pairwise.cons ?_ (List.Pairwise.cons ?_ List.Pairwise.nil)))))))
    · intro b hb
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact sep_doc_ep
      · exact sep_doc_xp
      · exact sep_doc_dst
      · exact sep_doc_ev
      · exact sep_doc_ndst
      · exact sep_doc_nev
      · exact sep_doc_err
    · intro b hb
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
      · have h : S.ep + 4 * (64 * pipelineBlocks S.n.toNat + 9) ≤ S.xp ∨
            S.xp + 4 * (nxp0 + 64 * pipelineBlocks S.n.toNat + 8) ≤ S.ep := by
          simpa using disjointRegions_pair _ 6 8 (by decide) _ _ rfl rfl hdisj
        omega
      · have h : S.ep + 4 * (64 * pipelineBlocks S.n.toNat + 9) ≤ S.dst ∨
            S.dst + S.dstcap.toNat ≤ S.ep := by
          simpa using disjointRegions_pair _ 6 11 (by decide) _ _ rfl rfl hdisj
        omega
      · have h : S.ep + 4 * (64 * pipelineBlocks S.n.toNat + 9) ≤ S.ev ∨
            S.ev + S.evcap.toNat ≤ S.ep := by
          simpa using disjointRegions_pair _ 6 13 (by decide) _ _ rfl rfl hdisj
        omega
      · have h : S.ep + 4 * (64 * pipelineBlocks S.n.toNat + 9) ≤ S.ndst ∨
            S.ndst + 8 ≤ S.ep := by
          simpa using disjointRegions_pair _ 6 12 (by decide) _ _ rfl rfl hdisj
        omega
      · have h : S.ep + 4 * (64 * pipelineBlocks S.n.toNat + 9) ≤ S.nev ∨
            S.nev + 8 ≤ S.ep := by
          simpa using disjointRegions_pair _ 6 14 (by decide) _ _ rfl rfl hdisj
        omega
      · have h : S.ep + 4 * (64 * pipelineBlocks S.n.toNat + 9) ≤ S.err ∨
            S.err + 8 ≤ S.ep := by
          simpa using disjointRegions_pair _ 6 15 (by decide) _ _ rfl rfl hdisj
        omega
    · intro b hb
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl | rfl | rfl | rfl | rfl
      · have h : S.xp + 4 * (nxp0 + 64 * pipelineBlocks S.n.toNat + 8) ≤ S.dst ∨
            S.dst + S.dstcap.toNat ≤ S.xp := by
          simpa using disjointRegions_pair _ 8 11 (by decide) _ _ rfl rfl hdisj
        omega
      · have h : S.xp + 4 * (nxp0 + 64 * pipelineBlocks S.n.toNat + 8) ≤ S.ev ∨
            S.ev + S.evcap.toNat ≤ S.xp := by
          simpa using disjointRegions_pair _ 8 13 (by decide) _ _ rfl rfl hdisj
        omega
      · have h : S.xp + 4 * (nxp0 + 64 * pipelineBlocks S.n.toNat + 8) ≤ S.ndst ∨
            S.ndst + 8 ≤ S.xp := by
          simpa using disjointRegions_pair _ 8 12 (by decide) _ _ rfl rfl hdisj
        omega
      · have h : S.xp + 4 * (nxp0 + 64 * pipelineBlocks S.n.toNat + 8) ≤ S.nev ∨
            S.nev + 8 ≤ S.xp := by
          simpa using disjointRegions_pair _ 8 14 (by decide) _ _ rfl rfl hdisj
        omega
      · have h : S.xp + 4 * (nxp0 + 64 * pipelineBlocks S.n.toNat + 8) ≤ S.err ∨
            S.err + 8 ≤ S.xp := by
          simpa using disjointRegions_pair _ 8 15 (by decide) _ _ rfl rfl hdisj
        omega
    · intro b hb
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl | rfl | rfl | rfl
      · have h : S.dst + S.dstcap.toNat ≤ S.ev ∨
            S.ev + S.evcap.toNat ≤ S.dst := by
          simpa using disjointRegions_pair _ 11 13 (by decide) _ _ rfl rfl hdisj
        omega
      · have h : S.dst + S.dstcap.toNat ≤ S.ndst ∨ S.ndst + 8 ≤ S.dst := by
          simpa using disjointRegions_pair _ 11 12 (by decide) _ _ rfl rfl hdisj
        omega
      · have h : S.dst + S.dstcap.toNat ≤ S.nev ∨ S.nev + 8 ≤ S.dst := by
          simpa using disjointRegions_pair _ 11 14 (by decide) _ _ rfl rfl hdisj
        omega
      · have h : S.dst + S.dstcap.toNat ≤ S.err ∨ S.err + 8 ≤ S.dst := by
          simpa using disjointRegions_pair _ 11 15 (by decide) _ _ rfl rfl hdisj
        omega
    · intro b hb
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl | rfl | rfl
      · -- the event stream's capacity against the first cursor slot
        have h : S.ndst + 8 ≤ S.ev ∨ S.ev + S.evcap.toNat ≤ S.ndst := by
          simpa using disjointRegions_pair _ 12 13 (by decide) _ _ rfl rfl hdisj
        rcases h with h | h
        · exact Or.inr h
        · exact Or.inl h
      · have h : S.ev + S.evcap.toNat ≤ S.nev ∨ S.nev + 8 ≤ S.ev := by
          simpa using disjointRegions_pair _ 13 14 (by decide) _ _ rfl rfl hdisj
        omega
      · have h : S.ev + S.evcap.toNat ≤ S.err ∨ S.err + 8 ≤ S.ev := by
          simpa using disjointRegions_pair _ 13 15 (by decide) _ _ rfl rfl hdisj
        omega
    · intro b hb
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl | rfl
      · have h : S.ndst + 8 ≤ S.nev ∨ S.nev + 8 ≤ S.ndst := by
          simpa using disjointRegions_pair _ 12 14 (by decide) _ _ rfl rfl hdisj
        omega
      · have h : S.ndst + 8 ≤ S.err ∨ S.err + 8 ≤ S.ndst := by
          simpa using disjointRegions_pair _ 12 15 (by decide) _ _ rfl rfl hdisj
        omega
    · intro b hb
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl
      have h : S.nev + 8 ≤ S.err ∨ S.err + 8 ≤ S.nev := by
        simpa using disjointRegions_pair _ 14 15 (by decide) _ _ rfl rfl hdisj
      omega
    · intro b hb
      simp at hb
  refine ⟨S.b, S.n.toNat, S.ep, S.k, S.xp, x37.toNat, S.dst, S.dstcap.toNat,
    S.ndst, S.ev, S.evcap.toNat, S.nev, S.err, bs, S.ent, ndst0, nev0,
    ?_, hdoc_ms, htail_ms, hlanes, hord, hbnd, hesc_ms, hdst_ms, ?_, hev_ms, ?_,
    hndst_ms, hnev_ms, herr_ms, ?_, hx37 ▸ hdisj2⟩
  · simpa [stage2Args] using hkv
  · simpa [stage2ArenaReserve] using hdstcap
  · simpa [stage2RecordBytes, ← hn] using hnev
  · simp only [stage2MaxDocument]
    omega

/-! ### Piece 3: the tail's run and post

The exit's three steps are `PipelineBodyStep.pipelineExit_run`, and the record's
post needs three further components: the UTF-8 call's own precondition (the
window, at the exit state's memory and through the count slot's store), the
escape list's read as a `positionsBytes` stream (every byte list of `4 * k` bytes
is one), and the two-valuedness of the arm's gate.

`pipelineOutputExtents`'s two bounds are where the assembly stops: stage 2's
post pins its extents only through the eight-byte slot words, and its argument
list pins the document length through `BitVec.ofNat 64`, so the record's clauses
bound `ndst' ≤ ndst0 + n` and `nev' ≤ nev0 + 13 * n` at *its own* witnesses,
which agree with the staging's only modulo `2 ^ 64`.  The record carries no
`n < 2 ^ 64` (its pre does), so `ndst' < 2 ^ 64` does not follow, and
`pipelineOutputExtents`'s bound is the one clause the tail cannot derive.  It is
a gap in the interface rather than in the run: the record's post would need the
document bound its pre already states.  See the residue note at the end of the
module. -/

/-- **Every byte list of a position stream's width is one.**  A list of `w * k`
bytes splits into `k` words of `w` bytes, and each word is the encoding of the
value its bytes denote, so the list is `positionsBytes w ps` for the list of
those values.  This is what turns the stage-2 pre's `HasBytes` at the escape
stream into the post's `readBytes … = some (positionsBytes 4 ps)` witness. -/
theorem positionsBytes_surjective (w : Nat) : ∀ (k : Nat) (bs : List UInt8),
    bs.length = w * k → ∃ ps : List Nat, positionsBytes w ps = bs ∧ ps.length = k
  | 0, bs, h => by
      have hnil : bs = [] := List.eq_nil_of_length_eq_zero (by simpa using h)
      subst hnil
      exact ⟨[], rfl, rfl⟩
  | k + 1, bs, h => by
      have hble : w ≤ bs.length := by
        rw [h]
        calc w = w * 1 := (Nat.mul_one w).symm
          _ ≤ w * (k + 1) := Nat.mul_le_mul_left w (by omega)
      have hlen : (bs.take w).length = w := by
        rw [List.length_take, Nat.min_eq_left hble]
      have hdrop : (bs.drop w).length = w * k := by
        rw [List.length_drop, h, Nat.mul_succ]
        omega
      obtain ⟨ps1, hps1, hlen1⟩ := positionsBytes_surjective w k (bs.drop w) hdrop
      refine ⟨bytesToNat (bs.take w) :: ps1, ?_, ?_⟩
      · have hrt : natToBytes (bytesToNat (bs.take w)) w = bs.take w := by
          have h := JsonEntrySteps.natToBytes_bytesToNat (bs.take w)
          rwa [hlen] at h
        show natToBytes (bytesToNat (bs.take w)) w ++ positionsBytes w ps1 = bs
        rw [hrt, hps1]
        exact List.take_append_drop w bs
      · simp only [List.length_cons, hlen1]

/-- **The escape gate is the ABI's flag.**  `for.cond.cleanup` masks the arm
selector with one bit, so the UTF-8 stage receives `0` or `1` at either width the
selector's reserved bits allow. -/
theorem tailGate_zero_or_one (arm : BitVec 64) : tailGate arm = 0 ∨ tailGate arm = 1 := by
  have h : (tailGate arm).toNat ≤ 1 := by
    rw [tailGate, BitVec.toNat_and]
    have h1 : (BitVec.ofInt 32 1).toNat = 1 := by decide
    rw [h1]
    exact Nat.and_le_right
  rcases Nat.eq_zero_or_pos (tailGate arm).toNat with h0 | hp
  · left
    exact BitVec.toNat_inj.mp (by rw [h0]; decide)
  · right
    have h1 : (tailGate arm).toNat = 1 := by omega
    exact BitVec.toNat_inj.mp (by rw [h1]; decide)

/-- **The UTF-8 stage's `pre` at the loop's exit.**  The window is the caller's:
three zeros at `b - 3`, the padded document at `b`, and the stage reads them as
one `utf8Window`.  The count slot's store at `%nk` misses the window, so the
call's memory carries it, and the record's own `3 ≤ b`, `0 < n` and block bounds
are the staging's. -/
theorem utf8Pre_of_staging {tab base : Nat} {args : List Value} {mem sm : Mem}
    {next : Nat} {S : PipelineLoopCarried} {kv : BitVec 64}
    (hst : pipelineStaging tab base args mem) (htie : exitArgs S args)
    (hwin_sm : readBytes sm (S.b - 3) (3 + 64 * pipelineBlocks S.n.toNat) =
      readBytes mem (S.b - 3) (3 + 64 * pipelineBlocks S.n.toNat)) :
    Γ_utf8.pre [.ptr S.b, .int 64 S.n, .int 32 (tailGate S.armSel)]
      (writeBytes sm S.nk (natToBytes kv.toNat 8)) next := by
  obtain ⟨sc, mk, entw, ep, nk, xp, nxp, xcarry, dst, ndst, ev, nev, err, nxp0, ndst0,
    nev0, n, epcap, xpcap, dstcap, evcap, arm, bs, hargs, hn, hlim, hwin, htail, hb3,
    hzero3, hpos, htab, hsc, hcarry, hcount, hnxp, hepcap, hxp, hdstcap, hdst, hev,
    hnev, hndst, hnev', hroomk, hroomxn, hblk, harm, hreads, hdisj⟩ := hst
  subst hargs
  simp only [exitArgs] at htie
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl⟩ := htie
  have hnB : pipelineBlocks S.n.toNat = pipelineBlocks bs.length := by rw [hn]
  have hble : bs.length ≤ 64 * pipelineBlocks bs.length := le_blocks_mul bs.length
  simp only [pipelineRegions, Nat.zero_add] at hdisj
  have hsep : (S.b - 3) + (3 + 64 * pipelineBlocks S.n.toNat) ≤ S.nk ∨
      S.nk + 8 ≤ S.b - 3 := by
    simpa using disjointRegions_pair _ 0 7 (by decide) _ _ rfl rfl hdisj
  -- the window at the caller's memory
  have hwindow_mem : readBytes mem (S.b - 3) (3 + 64 * pipelineBlocks S.n.toNat) =
      some (JsonUtf8IR.utf8Window (LeanLLVM.JSON.ByteString.literal bs).toList S.n.toNat
        (pipelineBlocks S.n.toNat)) := by
    have hdoc : readBytes mem ((S.b - 3) + 3) (64 * pipelineBlocks S.n.toNat) =
        some (bs ++ List.replicate (64 * pipelineBlocks S.n.toNat - bs.length) 0) := by
      rw [show (S.b - 3) + 3 = S.b from by omega, hnB]
      exact hwin
    have happ := JsonEntrySteps.readBytes_append mem 3 (S.b - 3) (List.replicate 3 0)
      (64 * pipelineBlocks S.n.toNat)
      (bs ++ List.replicate (64 * pipelineBlocks S.n.toNat - bs.length) 0) hzero3 hdoc
    rw [happ]
    simp only [JsonUtf8IR.utf8Window, LeanLLVM.JSON.ByteString.toList_literal, hn, List.append_assoc]
  -- and at the memory the count slot's store leaves
  have hwindow_ms : readBytes (writeBytes sm S.nk (natToBytes kv.toNat 8)) (S.b - 3)
      (3 + 64 * pipelineBlocks S.n.toNat) =
      some (JsonUtf8IR.utf8Window (LeanLLVM.JSON.ByteString.literal bs).toList S.n.toNat
        (pipelineBlocks S.n.toNat)) := by
    refine (readBytes_writeBytes_of_disjoint (m := sm) (start := S.nk)
      (bs := natToBytes kv.toNat 8) (a := S.b - 3)
      (N := 3 + 64 * pipelineBlocks S.n.toNat) ?_).trans ?_
    · rw [natToBytes_length]; omega
    · exact hwin_sm.trans hwindow_mem
  have hn64 : S.n.toNat + 63 < 2 ^ 64 := by
    have := hble
    omega
  have hn63 : S.n.toNat < 2 ^ 63 := by
    have := hble
    omega
  have hpos' : 0 < S.n.toNat := by omega
  rcases tailGate_zero_or_one S.armSel with hg | hg
  · refine ⟨S.b, S.n, tailGate S.armSel, false, LeanLLVM.JSON.ByteString.literal bs,
      pipelineBlocks S.n.toNat, rfl, ?_, ?_, rfl, hb3, hn64, hn63, hwindow_ms, hpos'⟩
    · rw [hg]; rfl
    · simp [LeanLLVM.JSON.ByteString.length_eq_size, LeanLLVM.JSON.ByteString.size_literal, hn]
  · refine ⟨S.b, S.n, tailGate S.armSel, true, LeanLLVM.JSON.ByteString.literal bs,
      pipelineBlocks S.n.toNat, rfl, ?_, ?_, rfl, hb3, hn64, hn63, hwindow_ms, hpos'⟩
    · rw [hg]; rfl
    · simp [LeanLLVM.JSON.ByteString.length_eq_size, LeanLLVM.JSON.ByteString.size_literal, hn]

/-! ### The residue

The tail's run and the frame composition around it are assembled from the three
components above and `PipelineBodyStep`'s branch traces; what does not close is
`pipelineOutputExtents`'s bound at stage 2's two reported extents.

`stage2Boundary` pins `ndst'` and `nev'` through eight-byte slot words, and its
argument list pins the document length through `BitVec.ofNat 64 n`.  Both are
`2 ^ 64`-periodic: the record's clauses hold at `(n, ndst0, nev0, ndst', nev')`
and at `(n + 2 ^ 64, ndst0 + 2 ^ 64, …)` for the same memory whenever the slot
words and the arena prefix agree, and its only upper bound is
`ndst' ≤ ndst0 + n`.  Since the staging's `n < 2 ^ 32` is a *pre* clause and the
post states no document bound, `ndst' < 2 ^ 64` — the bound `pipelineOutputExtents`
needs to make its slot word decide its value — is not derivable from
`Γ_stage2.post` at the staging's witnesses.  The record's post would need the
document bound its pre states; adding it is a change to `JsonStage2Contract`,
which is outside this change's file set, and supplying it as a hypothesis here
would be a hypothesis of the target's own shape.  So the tail is not stated as a
theorem at `Γ_stage2`: `PipelineTailTarget` remains the named obligation, with
the pieces above done.
-/

/-! ### The tail's target -/

/-- **The tail's target**: the field `PipelineBodyFacts.exit` states at
`pipelineLoopExit`, the predicate the loop hands over — at the caller's memory
*and* at the caller's argument list, which is what lets the target name the UTF-8
window, stage 2's staging and the post's frame at the caller's addresses.

The statement is the run's three steps and the record's own post.
`PipelineBodyStep.pipelineExit_run` supplies the steps once the two call
preconditions hold; both preconditions are proved above
(`utf8Pre_of_staging`, `stage2Pre_of_exit`), and the post's escape-stream witness
is `positionsBytes_surjective`.  This module does not supply the target, so it
remains a *hypothesis* of `pipelineBodyFacts_of_exitStage2`.  What is left is the
post's two extent bounds — see the residue note above — which is why the rest of
the assembly is not carried out: it would have to conclude at the extents. -/
def PipelineTailTarget (tab base : Nat) (s2 : Calls)
    (args : List Value) (mem : Mem) (next : Nat) : Prop :=
  ∀ e : State, pipelineLoopExit mem args e →
    ∃ (verdict : BitVec 64) (m : Mem),
      runFuel (pipelineCalls tab base s2) 3 pipelineBody e =
        some (.ret (some (.int 64 verdict)) m) ∧
      (Γ_pipeline_units tab base).post args mem next
        (.ret (some (.int 64 verdict)) m)

/-! ### The bundle, from the four fields and the tail -/

/-- **`PipelineBodyFacts` from the proved fields and the tail's target.**  The
loop, `N_eq`, `cost_le` and the seed are the theorems above; the fifth field is
the target at the exit predicate the loop produces.  `pipelineLoopExit` is the
loop's own exit and it now carries the caller's argument list, so the target's
domain is the field's domain and is stated at the caller's addresses; the target
itself is the caller's until the tail's assembly is proved. -/
def pipelineBodyFacts_of_exitStage2 {tab base : Nat} {s2 : Calls}
    {Γ2 : MemContract} {args : List Value} {mem : Mem} {next : Nat}
    (hst : pipelineStaging tab base args mem) (units : PipelineUnits tab base s2 Γ2)
    (tail : PipelineTailTarget tab base s2 args mem next) :
    PipelineBodyFacts tab base s2 Γ2 args mem next :=
  { loop := pipelineLoop_of_staging hst s2 Γ2 units
    N_eq := pipelineLoop_of_staging_N hst s2 Γ2 units
    cost_le := pipelineLoop_of_staging_cost_le hst s2 Γ2 units
    seed := pipelineSeed hst
    exit := fun e he => tail e he }

/-- **The assembled pipeline satisfies its unit-level record, from the four
fields and the tail's target.**  `pipeline_satisfies_at_stage2`'s `hbody` is
supplied by `pipelineBodyFacts_of_exitStage2`, so the remaining inputs are the
stage-2 selection `h2` and the tail target — the run from the exit the loop
leaves, which the excluded `PipelineBodyFacts.exit` field states. -/
theorem pipeline_satisfies_at_stage2_of_exitStage2 (tab : Nat) (s2 : Calls)
    (h2 : CallSatisfies s2 Γ_stage2 stage2Sym)
    (tail : ∀ (base : Nat) (args : List Value) (mem : Mem) (next : Nat),
      pipelineStaging tab base args mem → PipelineUnits tab base s2 Γ_stage2 →
      PipelineTailTarget tab base s2 args mem next) :
    ∀ base, Satisfies (pipelineCalls tab base s2) pipelineBody
      (Γ_pipeline_units tab base) :=
  pipeline_satisfies_at_stage2 tab s2 h2
    (fun base args mem next hpre units =>
      pipelineBodyFacts_of_exitStage2 hpre units
        (tail base args mem next hpre units))

/-! ### Axiom footprints

The four fields are `PipelineBodyStep`'s instance and two closed comparisons; the
tail's target is a definition; the bundle is the structure's constructor at them.
Nothing here adds a carrier: the tail is a named target whose proof is
`PipelineBodyStep.pipelineExit_run`, and the exit's three facts arrive with the
loop's producers.
-/

/-- info: 'LeanLLVM.Refinement.pipelineBlocks_argLen_cap' depends on axioms: [propext] -/
#guard_msgs in
#print axioms pipelineBlocks_argLen_cap

/-- info: 'LeanLLVM.Refinement.pipelineLoop_of_staging' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms pipelineLoop_of_staging

/-- info: 'LeanLLVM.Refinement.pipelineLoop_of_staging_N' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms pipelineLoop_of_staging_N

/-- info: 'LeanLLVM.Refinement.pipelineLoop_of_staging_cost_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms pipelineLoop_of_staging_cost_le

/-- info: 'LeanLLVM.Refinement.pipelineLoop_of_staging_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms pipelineLoop_of_staging_cost

/-- info: 'LeanLLVM.Refinement.not_inside_region' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms not_inside_region

/-- info: 'LeanLLVM.Refinement.readBytes_writeBytes_of_disjoint' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms readBytes_writeBytes_of_disjoint

/-- info: 'LeanLLVM.Refinement.disjointRegions_pair' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms disjointRegions_pair

/-- info: 'LeanLLVM.Refinement.outside_of_sub_disjoint' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms outside_of_sub_disjoint

/-- info: 'LeanLLVM.Refinement.outside_loopWrites' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms outside_loopWrites

/-- info: 'LeanLLVM.Refinement.loopWrites_cover' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms loopWrites_cover

/-- info: 'LeanLLVM.Refinement.readBytes_of_loop_frame' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms readBytes_of_loop_frame

/-- info: 'LeanLLVM.Refinement.disjoint_doc_of_window_tail' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms disjoint_doc_of_window_tail

/-- info: 'LeanLLVM.Refinement.hasBytes_of_loop_frame' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms hasBytes_of_loop_frame

/-- info: 'LeanLLVM.Refinement.loop_frame_of_staging' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms loop_frame_of_staging

/-- info: 'LeanLLVM.Refinement.hasBytes_capacity_not_implied_by_bound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms hasBytes_capacity_not_implied_by_bound

/-- info: 'LeanLLVM.Refinement.hasBytes_shift_of_read' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms hasBytes_shift_of_read

/-- info: 'LeanLLVM.Refinement.readLanes32_writeBytes_disjoint' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms readLanes32_writeBytes_disjoint

/-- info: 'LeanLLVM.Refinement.stage2Pre_of_exit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms stage2Pre_of_exit

/-- info: 'LeanLLVM.Refinement.positionsBytes_surjective' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms positionsBytes_surjective

/-- info: 'LeanLLVM.Refinement.tailGate_zero_or_one' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms tailGate_zero_or_one

/-- info: 'LeanLLVM.Refinement.utf8Pre_of_staging' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms utf8Pre_of_staging

/-- info: 'LeanLLVM.Refinement.PipelineTailTarget' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms PipelineTailTarget

/-- info: 'LeanLLVM.Refinement.pipelineBodyFacts_of_exitStage2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms pipelineBodyFacts_of_exitStage2

/-- info: 'LeanLLVM.Refinement.pipeline_satisfies_at_stage2_of_exitStage2' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms pipeline_satisfies_at_stage2_of_exitStage2

end LeanLLVM.Refinement
