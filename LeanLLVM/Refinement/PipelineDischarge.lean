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
caller** in this tree.  The retype above removes the structural obstruction — the
predicate can now name the caller, so the UTF-8 window, `Γ_stage2.pre` and the
post's frame are statements about addresses the state carries — but the
assembly of the run and the post at the exit's witnesses is the remaining work,
and the two calls' preconditions are where it starts: the UTF-8 window is
`[0,0,0] ++ S.doc` at `S.b - 3`, and stage 2's staging is the pipeline staging's
clauses at `S`'s fields, with its `DisjointRegions` derived from
`pipelineRegions` once the loop's write extents are seen to be sub-extents
(`S.k ≤ 64 * S.i` from the entry stream's order and length, `S.xn ≤ S.xn0 + 64 *
S.i` and `S.xn0 = nxp0` from the carried slot and bound).  `pipelineExit_run`
supplies the three control steps; `PipelineUnits.utf8` and `PipelineUnits.stage2`
supply the call outcomes and their posts; `positionsBytes` is where the escape
list's read becomes the post's witness.

Nothing here narrows a record or weakens a post: the tail's target is stated at
the same predicate the loop hands over, now with the caller's arguments in it.
-/
import LeanLLVM.Refinement.JsonStage2Contract
import LeanLLVM.Refinement.PipelineBodyStep

set_option autoImplicit false

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
    HasBytes m S.err 8 := by
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

  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
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

/-! ### The tail's target -/

/-- **The tail's target**: the field `PipelineBodyFacts.exit` states at
`pipelineLoopExit`, the predicate the loop hands over — at the caller's memory
*and* at the caller's argument list, which is what lets the target name the UTF-8
window, stage 2's staging and the post's frame at the caller's addresses.

The statement is the run's three steps and the record's own post.
`PipelineBodyStep.pipelineExit_run` supplies the steps once the two call
preconditions hold; this module does not yet supply them, so the target is a
*hypothesis* of `pipelineBodyFacts_of_exitStage2`, as it was before the retype.
What the retype changed is that the hypothesis is now statable: the predicate's
`exitArgs` identifies `S`'s addresses with the argument list's, and its document
read, escape-slot content and count bounds are the state facts the preconditions
are derived from.  The remaining obligation is the derivation itself, not a gap
in what the predicate names. -/
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
