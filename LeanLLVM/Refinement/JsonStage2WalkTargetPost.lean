/-
# The walk's exit: the three terminal routes, at their returned memories

`WalkInv` is a predicate about the *state* the walk is at; it says nothing about the
memory the finalisation leaves.  The record's post, however, is `stage2Boundary` at the
returned memory (`JsonStage2Contract.lean:1004`), so the loop arm's output side needs the
finalisation's three routes with their memories *named*.

The three routes, from the merge (`cleanup478.i`) and from the copy's entry (`if.then`):

* **R1, accept** — `cleanup478.i → if.then485.i → if.end490.i → s2_walk.exit → if.end`,
  two writes over the state's memory (`%alen` at `%ndst`, `%len` at `%nev`), and the
  verdict `1`.  `walkFinishPost_accept`.
* **R2/R3, refuse from the merge** — `cleanup478.i → if.then485.i → (if.then492.i |
  if.then488.i) → if.then → if.end`, four writes (`%4` at `%e + 8`, then the record's
  three slots), and the verdict `0`.  Boundary only: `stage2Boundary_of_refuse` and
  `stage2Boundary_of_refuse_offset`.
* **R0, a segment already at the copy** — `if.then → if.end`, three writes (the copy's),
  and the verdict `0`.  Boundary only; `stage2Boundary_of_refuse` is its packing.

Each concludes `stage2Boundary` directly (no intermediate predicate: the layer's
`WalkTargetPost` lives in the loop's own module), at the memory the route actually
returns: `walkFinishMemAccept` for R1, `walkFinishMemRefuse` for the refuse routes.

## What is proved here, and what is not

**Proved**: the boundary at the returned memory for all three routes — the 25 conjuncts
of `stage2Boundary`, at a variable base memory, from `WalkInv` plus the four supplied
facts below — and the accept route's terminal run with its memory named
(`walkFinishPost_accept`).  That is the output-side statement the loop arm's post needs:
the boundary is the post, and the only thing a post producer still lacks is the run that
reaches it on the two refusal routes.

**Not yet written**: `walkFinishPost_refuse`, `walkFinishPost_refuse488` and
`walkFinishPost_copy` — the terminal *runs* for R2/R3 and R0, which compose
`walkFinishMerge_at`/`walkIfThen492Step`/`walkIfThen_step`/`walkIfEnd_step` at the
memories the boundary lemmas here already name.  Their absence is why the module is not
imported into the loop's step yet; `stage2WalkObligation_of_staging` still takes `hpost`.
The divergence that stopped the first of them is recorded where it bites: the composition
unifies an abstract base memory against a concrete state's, which is an occurs-check
failure rather than a heartbeat one, and the repair is to state the step lemmas at a
memory parameter rather than to raise a budget.

## Why every memory lemma is stated at an abstract memory

The returned memory is a two- or three-deep `writeBytes` over `s.mem`, which itself is
whatever the loop left.  A lemma stated at a concrete nest (`rfl` on a term whose memory
is three writes over a five-write staging) unfolds every write at every position and
exceeds the heartbeat budget deterministically.  So each read-back, the frame, the two
presence lemmas and the refusal word are stated at an abstract `m : Mem` (or at
`s.mem` of a state hypothesis) with the route's words as parameters, and each route
instantiates them with one `rw`.  `walkFlushMemAt`'s docstring records the same
measurement for the empty-stream arm.

## The three routes' supplied facts

`WalkInv` bounds but does not fix the words the finalisation reads, and it does not
carry the finalisation blocks' address registers at all.  The route theorems therefore
take the facts below as *arguments*, named where the repository would produce them:

* `%4 = n` (`h4`).  `%4` is loaded once by `entry` from `%n2.i = %s + 8`, where `s2_init`
  stores `n`, and no block rebinds it; but `%4` is not in `walkStaticNames`
  (`JsonStage2WalkScope.lean:988`), so no `WalkInv` clause names it.  Its producer is the
  seed's register carrier (`walkSeedFinalEnv_regs`, `JsonStage2WalkSeedRun.lean`), and
  adding `"%4"` to `walkStaticNames` would make it derivable — that edit is in the
  twenty-one-megabyte `JsonStage2WalkScope`, outside this module.
* the log's arena word equal to the carry's cursor (`hlog`).  `WalkInv.log_alen` gives
  only `∃ a, ndst0 ≤ a ∧ a ≤ C.alen`; the frame at the *reported* cursor needs the
  equality, which its own docstring calls "the dispatch's to produce".  Its producer is
  the write-back block `if.else285.i`'s link.
* the finalisation blocks' registers (`WalkFinalEnv`): `%e`, `%z`, `%s`, `%c.i`,
  `%ndst`, `%nev`, `%err` and `%nep`.  The carriers give six more (`%alen`, `%len`,
  `%xj.i`, `%root_done.i` from `walkStaticRegs`, `%ctype.i`/`%cst.i` from `WalkPtrs`), and
  these are *not* in the list because the routes transport the carriers themselves; the
  eight here are the ones `WalkInv` has no clause for.  A producer is the seed's
  environment (`walkEntryState_env`), for the same reason as `%4`.
* R0's refusal word (`hword`): `readBytes s.mem (C.stage.e + 8) 8 = some (wordBytes 8
  C.eoff)`.  The copy reads the word the *previous* link stored, and neither `WalkInv`
  nor `WalkSegment` can say so (`WalkSegment` is a `Prop` holding the run and the
  invariant, not the target memory); a memory-carrying refusal segment would produce it.
* the merge's root-done word (`hroot`): `∃ rv, readBytes s.mem (G.next0 + 8) 4 = some
  (natToBytes rv.toNat 4)`.  `WalkInv.owned` deliberately omits the four `alloca` slots,
  so the root slot's presence is in no clause; its producer is a presence clause on
  `WalkInv` transported link by link.
-/
import LeanLLVM.Refinement.JsonStage2WalkFinishPath
import LeanLLVM.Refinement.JsonStage2WalkLoopStepOutcome

set_option autoImplicit false

namespace LeanLLVM.Refinement
open LeanLLVM
open LeanLLVM.Refinement.BlockEval
open LeanLLVM.Refinement.JsonStage2IR

namespace WalkScope

/-! ### The returned memories

The two cursor writes R1 makes, and the same two plus the refusal slot for the refuse
routes.  Every lemma below is stated at these terms with an abstract base, so a route's
concrete memory is one rewrite away. -/

/-- **R1's returned memory**: the log's arena word at `%ndst`, its event word at `%nev`,
over the state's own memory. -/
def walkFinishMemAccept {m0 : Mem} (G : WalkGeom m0) (m : Mem) (a l : Nat) : Mem :=
  writeBytes (writeBytes m G.ndst (wordBytes 8 a)) G.nev (wordBytes 8 l)

/-- **The refuse routes' returned memory**: the two cursor writes and the refusal slot. -/
def walkFinishMemRefuse {m0 : Mem} (G : WalkGeom m0) (m : Mem) (a l e : Nat) : Mem :=
  writeBytes (walkFinishMemAccept G m a l) G.err (wordBytes 8 e)

/-- **The copy's pre-state memory**: the refusal offset's store at `%e + 8`, which
`if.then492.i`/`if.then488.i` make. -/
def walkFinishMemOffset (e v : Nat) (m : Mem) : Mem :=
  writeBytes m (e + 8) (wordBytes 8 v)

/-- **`s2_walk.exit`'s output, named.**  The twin of `walkIfThenBlockState`: the two
cells the block's loads leave, over the block's two writes. -/
def walkExitBlockState (env : Env) (nd nv : Nat) (A L : BitVec 64) (s : State) : State :=
  stateAt (cells [("%50", .int 64 L), ("%49", .int 64 A)] env)
    (walkSetMem s (writeBytes (writeBytes s.mem nd (wordBytes 8 A.toNat)) nv
      (wordBytes 8 L.toNat)))

/-- A named state's memory is the one it was given. -/
theorem walkSetMem_mem (s : State) (m : Mem) : (walkSetMem s m).mem = m := rfl

/-- The exit block's state returns the block's memory. -/
theorem walkExitBlockState_mem (env : Env) (nd nv : Nat) (A L : BitVec 64) (s : State) :
    (walkExitBlockState env nd nv A L s).mem =
      writeBytes (writeBytes s.mem nd (wordBytes 8 A.toNat)) nv (wordBytes 8 L.toNat) := by
  rw [walkExitBlockState, stateAt_mem, walkSetMem_mem]

/-- The exit block's state is at the block it was entered at. -/
theorem walkExitBlockState_pc (env : Env) (nd nv : Nat) (A L : BitVec 64) (s : State) :
    (walkExitBlockState env nd nv A L s).pc = s.pc := rfl

/-- The exit block's state adds exactly its two cells. -/
theorem walkExitBlockState_env (env : Env) (nd nv : Nat) (A L : BitVec 64) (s : State) :
    (walkExitBlockState env nd nv A L s).env = cells [("%50", .int 64 L),
      ("%49", .int 64 A)] env := rfl

/-! ### Reading the words back

Each slot is written last by the route's own copy, so a read at it returns the word; the
two later stores miss it by the staging's slot separation. -/

/-- The bytes written at an address are read back at it, at any width that spells their
length.  (`PremisesOfStaging`'s `readBytes_writeBytes_len`, restated here because this
module sits below that one.) -/
theorem walkFinishReadBytes_writeBytes_len {m : Mem} {bs : List UInt8} {a n : Nat}
    (h : n = bs.length) : readBytes (writeBytes m a bs) a n = some bs := by
  subst h
  exact readBytes_writeBytes_same m bs

/-- A shorter present range is present. -/
theorem walkFinishHasBytes_short {m : Mem} {a n n' : Nat}
    (h : Refinement.HasBytes m a n) (hn : n' ≤ n) : Refinement.HasBytes m a n' :=
  (hasBytes_iff m a n').mpr (LeanLLVM.HasBytes.mono ((hasBytes_iff m a n).mp h) hn)

/-- **`%ndst` at R1's memory.** -/
theorem walkFinishMemAccept_ndst {m0 : Mem} (G : WalkGeom m0) {m : Mem} {a l : Nat}
    (hsep : G.ndst + 8 ≤ G.nev ∨ G.nev + 8 ≤ G.ndst) :
    readBytes (walkFinishMemAccept G m a l) G.ndst 8 = some (wordBytes 8 a) := by
  have hout : G.ndst + 8 ≤ G.nev ∨ G.nev + (wordBytes 8 l).length ≤ G.ndst := by
    rw [wordBytes, natToBytes_length]
    exact hsep
  rw [walkFinishMemAccept,
    walkReadBytes_writeBytes_outside (m := writeBytes m G.ndst (wordBytes 8 a))
      (v := wordBytes 8 l) (start := G.nev) (addr := G.ndst) (n := 8) hout]
  exact walkFinishReadBytes_writeBytes_len (by rw [wordBytes, natToBytes_length])

/-- **`%nev` at R1's memory.** -/
theorem walkFinishMemAccept_nev {m0 : Mem} (G : WalkGeom m0) {m : Mem} {a l : Nat} :
    readBytes (walkFinishMemAccept G m a l) G.nev 8 = some (wordBytes 8 l) := by
  rw [walkFinishMemAccept]
  exact walkFinishReadBytes_writeBytes_len (by rw [wordBytes, natToBytes_length])

/-- **`%err` at the refuse routes' memory**: the copy's third write, read back at its own
address. -/
theorem walkFinishMemRefuse_err {m0 : Mem} (G : WalkGeom m0) {m : Mem} {a l e : Nat} :
    readBytes (walkFinishMemRefuse G m a l e) G.err 8 = some (wordBytes 8 e) := by
  rw [walkFinishMemRefuse]
  exact walkFinishReadBytes_writeBytes_len (by rw [wordBytes, natToBytes_length])

/-- **`%ndst` at the refuse routes' memory**: the refusal store passes the slot. -/
theorem walkFinishMemRefuse_ndst {m0 : Mem} (G : WalkGeom m0) {m : Mem} {a l e : Nat}
    (hsep : G.ndst + 8 ≤ G.nev ∨ G.nev + 8 ≤ G.ndst)
    (hsepE : G.ndst + 8 ≤ G.err ∨ G.err + 8 ≤ G.ndst) :
    readBytes (walkFinishMemRefuse G m a l e) G.ndst 8 = some (wordBytes 8 a) := by
  have hout : G.ndst + 8 ≤ G.err ∨ G.err + (wordBytes 8 e).length ≤ G.ndst := by
    rw [wordBytes, natToBytes_length]
    exact hsepE
  rw [walkFinishMemRefuse,
    walkReadBytes_writeBytes_outside (m := walkFinishMemAccept G m a l)
      (v := wordBytes 8 e) (start := G.err) (addr := G.ndst) (n := 8) hout]
  exact walkFinishMemAccept_ndst G hsep

/-- **`%nev` at the refuse routes' memory.** -/
theorem walkFinishMemRefuse_nev {m0 : Mem} (G : WalkGeom m0) {m : Mem} {a l e : Nat}
    (hsepE : G.nev + 8 ≤ G.err ∨ G.err + 8 ≤ G.nev) :
    readBytes (walkFinishMemRefuse G m a l e) G.nev 8 = some (wordBytes 8 l) := by
  have hout : G.nev + 8 ≤ G.err ∨ G.err + (wordBytes 8 e).length ≤ G.nev := by
    rw [wordBytes, natToBytes_length]
    exact hsepE
  rw [walkFinishMemRefuse,
    walkReadBytes_writeBytes_outside (m := walkFinishMemAccept G m a l)
      (v := wordBytes 8 e) (start := G.err) (addr := G.nev) (n := 8) hout]
  exact walkFinishMemAccept_nev G

/-- **`%err` at the accept route's memory is what it was at the state's**: the two cursor
stores miss the refusal slot by the staging's slot separation, so the slot the run does
not write reads as the caller's staging left it (through the walk's frame). -/
theorem walkFinishMemAccept_err {m0 : Mem} (G : WalkGeom m0) {m : Mem} {a l : Nat}
    (hsepN : G.ndst + 8 ≤ G.err ∨ G.err + 8 ≤ G.ndst)
    (hsepV : G.nev + 8 ≤ G.err ∨ G.err + 8 ≤ G.nev) :
    readBytes (walkFinishMemAccept G m a l) G.err 8 = readBytes m G.err 8 := by
  have houtV : G.err + 8 ≤ G.nev ∨ G.nev + (wordBytes 8 l).length ≤ G.err := by
    rw [wordBytes, natToBytes_length]
    exact hsepV.symm
  have houtN : G.err + 8 ≤ G.ndst ∨ G.ndst + (wordBytes 8 a).length ≤ G.err := by
    rw [wordBytes, natToBytes_length]
    exact hsepN.symm
  rw [walkFinishMemAccept,
    walkReadBytes_writeBytes_outside (m := writeBytes m G.ndst (wordBytes 8 a))
      (v := wordBytes 8 l) (start := G.nev) (addr := G.err) (n := 8) houtV,
    walkReadBytes_writeBytes_outside (m := m)
      (v := wordBytes 8 a) (start := G.ndst) (addr := G.err) (n := 8) houtN]

/-! ### The finalisation blocks' registers

The eight register lookups no `WalkInv` clause carries.  One predicate, so the routes
take one hypothesis, and one transport lemma, so each step's `cells` list is discharged
by a literal comparison. -/

/-- The names `WalkFinalEnv` binds, as the list its transport lemmas decide on. -/
def walkFinalNames : List String :=
  ["%e", "%z", "%s", "%c.i", "%ndst", "%nev", "%err", "%nep"]

/-- **The finalisation blocks' registers.**  `s2_walk.exit`, `if.then` and `if.end` read
`%alen`, `%len`, `%xj.i`, `%root_done.i`, `%ctype.i` and `%cst.i` — all in the two
carriers — and these eight, which no clause of `WalkInv` names: the three record slots,
the two finalisation records, the cursor record and the entry count.  They are fixed by
the staging's own stores at `entry`, so they are a seed fact rather than a walk fact. -/
def WalkFinalEnv {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (env : Env) : Prop :=
  lookupName env "%e" = some (.ptr C.stage.e) ∧
    lookupName env "%z" = some (.ptr C.stage.z) ∧
    lookupName env "%s" = some (.ptr C.stage.s) ∧
    lookupName env "%c.i" = some (.ptr C.stage.c) ∧
    lookupName env "%ndst" = some (.ptr G.ndst) ∧
    lookupName env "%nev" = some (.ptr G.nev) ∧
    lookupName env "%err" = some (.ptr G.err) ∧
    lookupName env "%nep" = some (.int 64 (BitVec.ofNat 64 G.nep))

/-- A cell list whose names miss `walkFinalNames` leaves the predicate alone. -/
theorem WalkFinalEnv.cells_of {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {env : Env}
    (h : WalkFinalEnv G C env) (cs : List (String × Value))
    (hne : ∀ n ∈ cs.map (·.1), n ∉ walkFinalNames) : WalkFinalEnv G C (cells cs env) := by
  obtain ⟨he, hz, hs, hc, hnd, hnv, her, hnp⟩ := h
  have hmiss : ∀ n : String, n ∈ walkFinalNames → n ∉ cs.map (·.1) :=
    fun n hn hc => hne n hc hn
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [lookupName_cells_of_notin cs "%e" env (hmiss "%e" (by simp [walkFinalNames]))]
    exact he
  · rw [lookupName_cells_of_notin cs "%z" env (hmiss "%z" (by simp [walkFinalNames]))]
    exact hz
  · rw [lookupName_cells_of_notin cs "%s" env (hmiss "%s" (by simp [walkFinalNames]))]
    exact hs
  · rw [lookupName_cells_of_notin cs "%c.i" env (hmiss "%c.i" (by simp [walkFinalNames]))]
    exact hc
  · rw [lookupName_cells_of_notin cs "%ndst" env (hmiss "%ndst" (by simp [walkFinalNames]))]
    exact hnd
  · rw [lookupName_cells_of_notin cs "%nev" env (hmiss "%nev" (by simp [walkFinalNames]))]
    exact hnv
  · rw [lookupName_cells_of_notin cs "%err" env (hmiss "%err" (by simp [walkFinalNames]))]
    exact her
  · rw [lookupName_cells_of_notin cs "%nep" env (hmiss "%nep" (by simp [walkFinalNames]))]
    exact hnp

/-- A bind at a name outside the list leaves the predicate alone. -/
theorem WalkFinalEnv.bind {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {env : Env}
    (h : WalkFinalEnv G C env) {d : String} {v : Value} (hd : d ∉ walkFinalNames) :
    WalkFinalEnv G C ((d, v) :: env) := by
  obtain ⟨he, hz, hs, hc, hnd, hnv, her, hnp⟩ := h
  have hne : ∀ n, n ∈ walkFinalNames → d ≠ n := fun n hn hdn => hd (hdn ▸ hn)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [lookupName_cons_ne (k := d) (n := "%e") v env
      (hne "%e" (by simp [walkFinalNames]))]
    exact he
  · rw [lookupName_cons_ne (k := d) (n := "%z") v env
      (hne "%z" (by simp [walkFinalNames]))]
    exact hz
  · rw [lookupName_cons_ne (k := d) (n := "%s") v env
      (hne "%s" (by simp [walkFinalNames]))]
    exact hs
  · rw [lookupName_cons_ne (k := d) (n := "%c.i") v env
      (hne "%c.i" (by simp [walkFinalNames]))]
    exact hc
  · rw [lookupName_cons_ne (k := d) (n := "%ndst") v env
      (hne "%ndst" (by simp [walkFinalNames]))]
    exact hnd
  · rw [lookupName_cons_ne (k := d) (n := "%nev") v env
      (hne "%nev" (by simp [walkFinalNames]))]
    exact hnv
  · rw [lookupName_cons_ne (k := d) (n := "%err") v env
      (hne "%err" (by simp [walkFinalNames]))]
    exact her
  · rw [lookupName_cons_ne (k := d) (n := "%nep") v env
      (hne "%nep" (by simp [walkFinalNames]))]
    exact hnp

/-! ### The staged separation the finalisation reads

Three pairs among the record's slots (`stage2Regions_slots`), and three against the
seven appended objects: the log's length word, which `s2_walk.exit` copies, and the
refusal record's offset word, which `if.then` copies.  All six come from the staging's
`DisjointRegions`. -/

/-- **The separation the finalisation's two copies read.**  The three slot pairs, the
log's `%len` word against `%ndst`, and the refusal record's `%e + 8` word against the two
cursor slots. -/
theorem walkFinish_sep {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) :
    (G.ndst + 8 ≤ G.nev ∨ G.nev + 8 ≤ G.ndst) ∧
    (G.ndst + 8 ≤ G.err ∨ G.err + 8 ≤ G.ndst) ∧
    (G.nev + 8 ≤ G.err ∨ G.err + 8 ≤ G.nev) ∧
    (G.ndst + 8 ≤ C.stage.z + 8 ∨ C.stage.z + 8 + 8 ≤ G.ndst) ∧
    (G.ndst + 8 ≤ C.stage.e + 8 ∨ C.stage.e + 8 + 8 ≤ G.ndst) ∧
    (G.nev + 8 ≤ C.stage.e + 8 ∨ C.stage.e + 8 + 8 ≤ G.nev) := by
  obtain ⟨hndnev, hnderr, hnverr⟩ :=
    stage2Regions_slots (disjointRegions_staged_prefix C.stage.separate)
  have hzw := stage2StagedWrites_against C.stage.separate
    (a := G.ndst) (m := 8) (by simp [stage2Regions])
  have hew := stage2StagedWrites_against C.stage.separate
    (a := G.ndst) (m := 8) (by simp [stage2Regions])
  have hvew := stage2StagedWrites_against C.stage.separate
    (a := G.nev) (m := 8) (by simp [stage2Regions])
  have hz := hzw (C.stage.z, stage2LogExtent) (by simp [stage2StagedWrites])
  have he := hew (C.stage.e, stage2ErrorExtent) (by simp [stage2StagedWrites])
  have hve := hvew (C.stage.e, stage2ErrorExtent) (by simp [stage2StagedWrites])
  refine ⟨hndnev, hnderr, hnverr, ?_, ?_, ?_⟩ <;>
    simp only [stage2LogExtent, stage2ErrorExtent] at hz he hve ⊢ <;> omega

/-! ### The refusal slot is outside the walk's frame

`stage2Boundary`'s acceptance clause is `readBytes m err 8 = readBytes m0 err 8`: the run
must not have written the caller's refusal slot.  The walk's frame already says so
(`WalkInv.frame`), and the finalisation's two or three stores miss it. -/

/-- **The refusal slot is outside the walk's write extent.**  `walkFinish_not_frame_of` at
the staging's own separations: the two streams, the seven appended objects, `%d.i` and the
four stack slots all miss `%err`'s eight bytes. -/
theorem walkInv_err_not_frame {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {s : State}
    (hInv : WalkInv G C s) {k : Nat} (hk : k < 8) :
    ¬ inRegions (walkWide G C) (G.err + k) := by
  have hdst := (stage2Regions_err_outside G.separate).1
  have hev := (stage2Regions_err_outside G.separate).2
  refine walkFinish_not_frame_of (G := G) (C := C) (s := s) hInv hdst hev ?_ ?_ ?_ hk
  · exact stage2StagedWrites_against C.stage.separate
      (a := G.err) (m := 8) (by simp [stage2Regions])
  · exact (C.stage.dSep (G.err, 8) (by simp [stage2WalkRegions, stage2Regions])).symm
  · exact G.watermark (G.err, 8) (by simp [stage2Regions])

/-- **The refusal slot at the state's memory is the caller's staging's.**  The frame gives
it byte by byte, and `readBytes_eq_of_UnchangedOn` lifts the eight bytes to the read. -/
theorem walkInv_err_at_entry {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {s : State}
    (hInv : WalkInv G C s) :
    readBytes s.mem G.err 8 = readBytes m0 G.err 8 := by
  have hOn : UnchangedOn (inRegions (walkWide G C)) m0 s.mem :=
    fun a ha => hInv.frame a (fun r hr hi => ha ⟨r, hr, hi⟩)
  refine readBytes_eq_of_UnchangedOn hOn ?_
  intro k hk
  exact walkInv_err_not_frame hInv hk

/-! ### The frame at the reported extents

`WalkInv.frame` is silence outside the walk's write extent, whose arena entry is the
carried cursor; the record's frame is stated at the reported cursor, which is the log's
word.  `walkFrame_reportFrame_coverage` is the containment, and the two cursor stores are
inside the report's own list. -/

/-- **The frame at the record's list, from the walk's.** -/
theorem walkFinishMem_base_frame {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State)
    (hInv : WalkInv G C s) :
    UnchangedOutside m0 s.mem
      (stage2ReportFrame G.dst C.alen G.ev C.evlen G.ndst G.nev G.err C.stage.c
        C.stage.ctype C.stage.cst C.stage.tok C.stage.s C.stage.z C.stage.e C.stage.d
        G.next0) := by
  refine UnchangedOutside.of_covered hInv.frame ?_
  intro r hr
  exact walkFrame_reportFrame_coverage r (by simpa only [walkWide, walkPresent] using hr)

/-- **The refusal slot at an accept route's memory is the caller's.** -/
theorem walkFinishMemAccept_err_entry {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G)
    {s : State} (hInv : WalkInv G C s) {a l : Nat}
    (hsepN : G.ndst + 8 ≤ G.err ∨ G.err + 8 ≤ G.ndst)
    (hsepV : G.nev + 8 ≤ G.err ∨ G.err + 8 ≤ G.nev) :
    readBytes (walkFinishMemAccept G s.mem a l) G.err 8 = readBytes m0 G.err 8 := by
  rw [walkFinishMemAccept_err G hsepN hsepV, walkInv_err_at_entry hInv]

/-- **The refusal offset's store stays inside the record's frame.**  The store is inside
the error record's twenty-four bytes, which the record's list names as scratch, so a frame
at the base memory survives it.  This is what the merge's refusal routes need: they store
the offset *before* the copy, so their returned memory's base is not the state's. -/
theorem walkFinishMemOffset_frame {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) {m : Mem}
    (h : UnchangedOutside m0 m
      (stage2ReportFrame G.dst C.alen G.ev C.evlen G.ndst G.nev G.err C.stage.c
        C.stage.ctype C.stage.cst C.stage.tok C.stage.s C.stage.z C.stage.e C.stage.d
        G.next0)) {v : Nat} :
    UnchangedOutside m0 (walkFinishMemOffset C.stage.e v m)
      (stage2ReportFrame G.dst C.alen G.ev C.evlen G.ndst G.nev G.err C.stage.c
        C.stage.ctype C.stage.cst C.stage.tok C.stage.s C.stage.z C.stage.e C.stage.d
        G.next0) :=
  UnchangedOutside.write_le (a := C.stage.e + 8) (w := 8) (bs := wordBytes 8 v) h
    ⟨(C.stage.e, stage2ErrorExtent), by
      simp [stage2ReportFrame, stage2ReportPresent, stage2ReportScratch,
        stage2StagedWrites], by omega,
      by simp only [stage2ErrorExtent]; omega⟩
    (by simp [wordBytes, natToBytes_length])

/-- **The accept route's frame, from a frame at the base memory.**  The two cursor stores,
each inside its own entry of the record's list. -/
theorem walkFinishMemAccept_frame_of {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) {m : Mem}
    (h : UnchangedOutside m0 m
      (stage2ReportFrame G.dst C.alen G.ev C.evlen G.ndst G.nev G.err C.stage.c
        C.stage.ctype C.stage.cst C.stage.tok C.stage.s C.stage.z C.stage.e C.stage.d
        G.next0)) :
    UnchangedOutside m0 (walkFinishMemAccept G m C.alen C.evlen)
      (stage2ReportFrame G.dst C.alen G.ev C.evlen G.ndst G.nev G.err C.stage.c
        C.stage.ctype C.stage.cst C.stage.tok C.stage.s C.stage.z C.stage.e C.stage.d
        G.next0) := by
  have h1 : UnchangedOutside m0
      (writeBytes m G.ndst (wordBytes 8 C.alen))
      (stage2ReportFrame G.dst C.alen G.ev C.evlen G.ndst G.nev G.err C.stage.c
        C.stage.ctype C.stage.cst C.stage.tok C.stage.s C.stage.z C.stage.e C.stage.d
        G.next0) :=
    UnchangedOutside.write_le (a := G.ndst) (w := 8) (bs := wordBytes 8 C.alen) h
      ⟨(G.ndst, 8), by
        simp [stage2ReportFrame, stage2ReportPresent, stage2Writes], by omega, by omega⟩
      (by simp [wordBytes, natToBytes_length])
  simpa only [walkFinishMemAccept] using
    UnchangedOutside.write_le (a := G.nev) (w := 8) (bs := wordBytes 8 C.evlen) h1
      ⟨(G.nev, 8), by
        simp [stage2ReportFrame, stage2ReportPresent, stage2Writes], by omega, by omega⟩
      (by simp [wordBytes, natToBytes_length])

/-- **The accept route's frame.**  The walk's frame at the reported extents, then the two
cursor stores. -/
theorem walkFinishMemAccept_frame {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State)
    (hInv : WalkInv G C s) :
    UnchangedOutside m0 (walkFinishMemAccept G s.mem C.alen C.evlen)
      (stage2ReportFrame G.dst C.alen G.ev C.evlen G.ndst G.nev G.err C.stage.c
        C.stage.ctype C.stage.cst C.stage.tok C.stage.s C.stage.z C.stage.e C.stage.d
        G.next0) :=
  walkFinishMemAccept_frame_of G C (walkFinishMem_base_frame G C s hInv)

/-- **The refusal routes' frame, from a frame at the base memory.** -/
theorem walkFinishMemRefuse_frame_of {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) {m : Mem}
    (h : UnchangedOutside m0 m
      (stage2ReportFrame G.dst C.alen G.ev C.evlen G.ndst G.nev G.err C.stage.c
        C.stage.ctype C.stage.cst C.stage.tok C.stage.s C.stage.z C.stage.e C.stage.d
        G.next0)) {e : Nat} :
    UnchangedOutside m0 (walkFinishMemRefuse G m C.alen C.evlen e)
      (stage2ReportFrame G.dst C.alen G.ev C.evlen G.ndst G.nev G.err C.stage.c
        C.stage.ctype C.stage.cst C.stage.tok C.stage.s C.stage.z C.stage.e C.stage.d
        G.next0) :=
  UnchangedOutside.write_le (a := G.err) (w := 8) (bs := wordBytes 8 e)
    (walkFinishMemAccept_frame_of G C h)
    ⟨(G.err, 8), by
      simp [stage2ReportFrame, stage2ReportPresent, stage2Writes], by omega, by omega⟩
    (by simp [wordBytes, natToBytes_length])

/-- **The refusal routes' frame.** -/
theorem walkFinishMemRefuse_frame {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State)
    (hInv : WalkInv G C s) {e : Nat} :
    UnchangedOutside m0 (walkFinishMemRefuse G s.mem C.alen C.evlen e)
      (stage2ReportFrame G.dst C.alen G.ev C.evlen G.ndst G.nev G.err C.stage.c
        C.stage.ctype C.stage.cst C.stage.tok C.stage.s C.stage.z C.stage.e C.stage.d
        G.next0) :=
  walkFinishMemRefuse_frame_of G C (walkFinishMem_base_frame G C s hInv)

/-! ### Presence at the reported extents

The walk's `owned` clause is presence at the *staged* extents, which contain the reported
ones; a store only adds cells. -/

/-- Presence survives either route's two cursor stores. -/
theorem walkFinishMemAccept_hasBytes {m0 : Mem} (G : WalkGeom m0) {m : Mem} {a l : Nat}
    {x n : Nat} (h : Refinement.HasBytes m x n) :
    Refinement.HasBytes (walkFinishMemAccept G m a l) x n := by
  rw [walkFinishMemAccept]
  exact hasBytes_writeBytes (hasBytes_writeBytes h)

/-- Presence survives the refuse routes' three stores. -/
theorem walkFinishMemRefuse_hasBytes {m0 : Mem} (G : WalkGeom m0) {m : Mem} {a l e : Nat}
    {x n : Nat} (h : Refinement.HasBytes m x n) :
    Refinement.HasBytes (walkFinishMemRefuse G m a l e) x n := by
  rw [walkFinishMemRefuse, walkFinishMemAccept]
  exact hasBytes_writeBytes (hasBytes_writeBytes (hasBytes_writeBytes h))

/-- **Presence at every entry of the record's present list, at the state's memory.**  The
arena's window is the staged one shortened to the reported cursor, the event stream's to
its own, the two cursor words and the refusal slot are `owned`'s, and the seven objects
plus `%d.i` are `WalkStage.present`/`dPresent`'s. -/
theorem walkInv_present_staged {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) {s : State}
    (hInv : WalkInv G C s) {a l : Nat} (ha : a ≤ G.ndst0 + G.n) (hl : l ≤ G.evcap) :
    ∀ r ∈ stage2ReportPresent G.dst a G.ev l G.ndst G.nev G.err C.stage.c C.stage.ctype
      C.stage.cst C.stage.tok C.stage.s C.stage.z C.stage.e C.stage.d,
      Refinement.HasBytes s.mem r.1 r.2 := by
  have hmem : ∀ r ∈ walkStaged G C, Refinement.HasBytes s.mem r.1 r.2 := hInv.owned
  have eDeep : Refinement.HasBytes s.mem G.dst (a + stage2ArenaReserve) :=
    walkFinishHasBytes_short
      (hmem (G.dst, G.ndst0 + G.n + stage2ArenaReserve) (by simp [walkStaged]))
      (by omega)
  have eNdst : Refinement.HasBytes s.mem G.ndst 8 :=
    hmem (G.ndst, 8) (by simp [walkStaged])
  have eEv : Refinement.HasBytes s.mem G.ev l :=
    walkFinishHasBytes_short (hmem (G.ev, G.evcap) (by simp [walkStaged])) hl
  have eNev : Refinement.HasBytes s.mem G.nev 8 :=
    hmem (G.nev, 8) (by simp [walkStaged])
  have eErr : Refinement.HasBytes s.mem G.err 8 :=
    hmem (G.err, 8) (by simp [walkStaged])
  intro r hr
  have hr5 : r ∈ stage2Writes G.dst a G.ev l G.ndst G.nev G.err ∨
      r ∈ stage2ReportScratch C.stage.c C.stage.ctype C.stage.cst C.stage.tok
        C.stage.s C.stage.z C.stage.e C.stage.d := by
    simpa only [stage2ReportPresent, List.mem_append] using hr
  rcases hr5 with hr5 | hr5
  · simp only [stage2Writes, List.mem_cons, List.not_mem_nil, or_false] at hr5
    rcases hr5 with rfl | rfl | rfl | rfl | rfl
    · exact eDeep
    · exact eNdst
    · exact eEv
    · exact eNev
    · exact eErr
  · exact hmem r (by
      simp only [walkStaged, List.mem_append]
      exact Or.inr hr5)

/-- **Presence at an accept route's memory.** -/
theorem walkFinishMemAccept_present {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G)
    {s : State} (hInv : WalkInv G C s) {a l : Nat} (ha : a ≤ G.ndst0 + G.n)
    (hl : l ≤ G.evcap) :
    ∀ x, inRegions (stage2ReportPresent G.dst a G.ev l G.ndst G.nev G.err C.stage.c
      C.stage.ctype C.stage.cst C.stage.tok C.stage.s C.stage.z C.stage.e C.stage.d) x →
      present (walkFinishMemAccept G s.mem a l) x := by
  intro x hx
  obtain ⟨r, hr, hlo, hhi⟩ := hx
  exact present_of_hasBytes
    (walkFinishMemAccept_hasBytes G (walkInv_present_staged G C hInv ha hl r hr)) hlo
    (Nat.lt_of_lt_of_le hhi (Nat.le_refl _))

/-- **Presence at the refuse routes' memory, from a presence-preserving base.** -/
theorem walkFinishMemRefuse_present_of {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G)
    {s : State} (hInv : WalkInv G C s) {M : Mem}
    (hmono : ∀ {x n : Nat}, Refinement.HasBytes s.mem x n → Refinement.HasBytes M x n)
    {a l e : Nat} (ha : a ≤ G.ndst0 + G.n) (hl : l ≤ G.evcap) :
    ∀ x, inRegions (stage2ReportPresent G.dst a G.ev l G.ndst G.nev G.err C.stage.c
      C.stage.ctype C.stage.cst C.stage.tok C.stage.s C.stage.z C.stage.e C.stage.d) x →
      present (walkFinishMemRefuse G M a l e) x := by
  intro x hx
  obtain ⟨r, hr, hlo, hhi⟩ := hx
  exact present_of_hasBytes
    (walkFinishMemRefuse_hasBytes G (hmono (walkInv_present_staged G C hInv ha hl r hr))) hlo
    (Nat.lt_of_lt_of_le hhi (Nat.le_refl _))

/-- **Presence at the refuse routes' memory.** -/
theorem walkFinishMemRefuse_present {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G)
    {s : State} (hInv : WalkInv G C s) {a l e : Nat} (ha : a ≤ G.ndst0 + G.n)
    (hl : l ≤ G.evcap) :
    ∀ x, inRegions (stage2ReportPresent G.dst a G.ev l G.ndst G.nev G.err C.stage.c
      C.stage.ctype C.stage.cst C.stage.tok C.stage.s C.stage.z C.stage.e C.stage.d) x →
      present (walkFinishMemRefuse G s.mem a l e) x :=
  walkFinishMemRefuse_present_of G C hInv (fun h => h) ha hl

/-! ### The record's boundary at the two returned memories

The 25 conjuncts of `stage2Boundary` (`JsonStage2Contract.lean:1004`), packed at the
memories the routes return: the verdicts `1` and `0`, the two reported cursors as the
log's words (`C.alen`, `C.evlen` — the copies' own source), the prefixes as the caller
staged them (presence, then a read), the refusal word, the frame, presence, and the
staging's two region clauses. -/

/-- The thirteen-argument list the boundary is stated at, spelled once. -/
abbrev walkFinishArgs {m0 : Mem} (G : WalkGeom m0) : List Value :=
  [.ptr G.b, .int 64 (BitVec.ofNat 64 G.n), .ptr G.ep,
   .int 64 (BitVec.ofNat 64 G.nep), .ptr G.xp, .int 64 (BitVec.ofNat 64 G.nxp),
   .ptr G.dst, .int 64 (BitVec.ofNat 64 G.dstcap), .ptr G.ndst, .ptr G.ev,
   .int 64 (BitVec.ofNat 64 G.evcap), .ptr G.nev, .ptr G.err]

/-- The arena's and the event stream's prefixes at the reported cursors, as reads. -/
theorem walkFinish_prefixes {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) {s : State}
    (hInv : WalkInv G C s) {M : Mem}
    (hM : ∀ {x n : Nat}, Refinement.HasBytes s.mem x n → Refinement.HasBytes M x n) :
    (∃ arena, readBytes M G.dst C.alen = some arena) ∧
      (∃ evs, readBytes M G.ev C.evlen = some evs) := by
  have hA : Refinement.HasBytes M G.dst C.alen :=
    hM (walkFinishHasBytes_short
      (hInv.owned (G.dst, G.ndst0 + G.n + stage2ArenaReserve) (by simp [walkStaged]))
      (by have h := hInv.alen_le; omega))
  have hE : Refinement.HasBytes M G.ev C.evlen :=
    hM (walkFinishHasBytes_short (hInv.owned (G.ev, G.evcap) (by simp [walkStaged]))
      (le_trans hInv.evlen_le G.evRoom))
  exact ⟨readBytes_of_hasBytes M G.dst C.alen ((hasBytes_iff _ _ _).mp hA),
    readBytes_of_hasBytes M G.ev C.evlen ((hasBytes_iff _ _ _).mp hE)⟩

/-- **The record's boundary at R1's returned memory.**  The verdict `1`, the two cursors
as the log's words, the two prefixes read back, the refusal slot as the caller staged it,
presence and the frame at the record's lists, and the staging. -/
theorem stage2Boundary_of_accept {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) {s : State}
    (hInv : WalkInv G C s) :
    stage2Boundary (walkFinishArgs G) m0 G.next0
      (walkFinishMemAccept G s.mem C.alen C.evlen) (.int 64 1) := by
  obtain ⟨hndnev, hnderr, hnverr, -, -, -⟩ := walkFinish_sep G C
  have halen := hInv.alen_le
  have hevle : C.evlen ≤ G.evcap := le_trans hInv.evlen_le G.evRoom
  have hnev0 : G.nev0 ≤ C.evlen := by
    rw [hInv.evlen_eq]; omega
  have hres : C.alen + stage2ArenaReserve ≤ G.dstcap := by
    have h := G.arenaRoom
    omega
  have hnep64 : G.nep < 2 ^ 64 := by
    have hle := G.nep_le
    have hdoc := G.maxDoc
    simp only [stage2MaxDocument] at hdoc
    omega
  obtain ⟨⟨arena, hArenaRead⟩, ⟨evs, hEvRead⟩⟩ :=
    walkFinish_prefixes G C hInv (walkFinishMemAccept_hasBytes G)
  have hRefuse0 : (1 : BitVec 64) = 0 →
      ∃ e : Nat, e ≤ G.n ∧
        readBytes (walkFinishMemAccept G s.mem C.alen C.evlen) G.err 8 = some (wordBytes 8 e) :=
    fun h => absurd h (by decide)
  have hAccept1 : (1 : BitVec 64) = 1 →
      readBytes (walkFinishMemAccept G s.mem C.alen C.evlen) G.err 8 = readBytes m0 G.err 8 :=
    fun _ => walkFinishMemAccept_err_entry G C hInv hnderr hnverr
  have hframeT : UnchangedOutside m0 (walkFinishMemAccept G s.mem C.alen C.evlen)
      (stage2ReportFrame G.dst C.alen G.ev C.evlen G.ndst G.nev G.err C.stage.c
        C.stage.ctype C.stage.cst C.stage.tok C.stage.s C.stage.z C.stage.e C.stage.d
        G.next0) :=
    walkFinishMemAccept_frame G C s hInv
  have hpresentT : ∀ x, inRegions (stage2ReportPresent G.dst C.alen G.ev C.evlen G.ndst
      G.nev G.err C.stage.c C.stage.ctype C.stage.cst C.stage.tok C.stage.s C.stage.z
      C.stage.e C.stage.d) x → present (walkFinishMemAccept G s.mem C.alen C.evlen) x :=
    walkFinishMemAccept_present G C hInv halen hevle
  have hsep24 : DisjointRegions (stage2StagedRegions G.b G.n G.ep G.nep G.xp G.nxp G.dst
      G.ndst0 G.ev G.evcap G.ndst G.nev G.err C.stage.c C.stage.ctype C.stage.cst
      C.stage.tok C.stage.s C.stage.z C.stage.e C.stage.nkSlot C.stage.nxpSlot) :=
    C.stage.separate
  have hsep25 : ∀ r ∈ stage2WalkRegions G.b G.n G.ep G.nep G.xp G.nxp G.dst G.ndst0 G.ev
      G.evcap G.ndst G.nev G.err C.stage.c C.stage.ctype C.stage.cst C.stage.tok
      C.stage.s C.stage.z C.stage.e, r.1 + r.2 ≤ C.stage.d ∨ C.stage.d + 8 ≤ r.1 :=
    C.stage.dSep
  refine ⟨G.b, G.n, G.ep, G.nep, G.xp, G.nxp, G.dst, G.dstcap, G.ndst, G.ev, G.evcap,
    G.nev, G.err, 1, G.ndst0, G.nev0, C.alen, C.evlen, arena, evs, C.stage.c,
    C.stage.ctype, C.stage.cst, C.stage.tok, C.stage.s, C.stage.z, C.stage.e, C.stage.d,
    C.stage.nkSlot, C.stage.nxpSlot, rfl, rfl, Or.inr rfl, G.ndstRead, G.nevRead,
    walkFinishMemAccept_ndst G hndnev, walkFinishMemAccept_nev G, hInv.alen_ge, halen,
    hnev0, hInv.evlen_le, G.dstcapLt, G.evcapLt, hevle, hnep64, G.nxpLt, hres, hArenaRead,
    hEvRead, hRefuse0, hAccept1, hpresentT, hframeT, hsep24, hsep25⟩

/-- **The record's boundary at R0's returned memory.**  The copy's three stores over the
state's own memory: verdict `0`, the two cursors as the log's words, the refusal word `e`
bounded by the document, presence, the frame, and the staging. -/
theorem stage2Boundary_of_refuse {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) {s : State}
    (hInv : WalkInv G C s) {e : Nat} (he : e ≤ G.n) :
    stage2Boundary (walkFinishArgs G) m0 G.next0
      (walkFinishMemRefuse G s.mem C.alen C.evlen e) (.int 64 0) := by
  obtain ⟨hndnev, hnderr, hnverr, -, -, -⟩ := walkFinish_sep G C
  have halen := hInv.alen_le
  have hevle : C.evlen ≤ G.evcap := le_trans hInv.evlen_le G.evRoom
  have hnev0 : G.nev0 ≤ C.evlen := by
    rw [hInv.evlen_eq]; omega
  have hres : C.alen + stage2ArenaReserve ≤ G.dstcap := by
    have h := G.arenaRoom
    omega
  have hnep64 : G.nep < 2 ^ 64 := by
    have hle := G.nep_le
    have hdoc := G.maxDoc
    simp only [stage2MaxDocument] at hdoc
    omega
  obtain ⟨⟨arena, hArenaRead⟩, ⟨evs, hEvRead⟩⟩ :=
    walkFinish_prefixes G C hInv (fun h => walkFinishMemRefuse_hasBytes G h)
  have hframeT : UnchangedOutside m0 (walkFinishMemRefuse G s.mem C.alen C.evlen e)
      (stage2ReportFrame G.dst C.alen G.ev C.evlen G.ndst G.nev G.err C.stage.c
        C.stage.ctype C.stage.cst C.stage.tok C.stage.s C.stage.z C.stage.e C.stage.d
        G.next0) :=
    walkFinishMemRefuse_frame G C s hInv
  have hpresentT : ∀ x, inRegions (stage2ReportPresent G.dst C.alen G.ev C.evlen G.ndst
      G.nev G.err C.stage.c C.stage.ctype C.stage.cst C.stage.tok C.stage.s C.stage.z
      C.stage.e C.stage.d) x → present (walkFinishMemRefuse G s.mem C.alen C.evlen e) x :=
    walkFinishMemRefuse_present G C hInv halen hevle
  have hRefuse0 : (0 : BitVec 64) = 0 →
      ∃ e' : Nat, e' ≤ G.n ∧
        readBytes (walkFinishMemRefuse G s.mem C.alen C.evlen e) G.err 8 =
          some (wordBytes 8 e') :=
    fun _ => ⟨e, he, walkFinishMemRefuse_err G⟩
  have hAccept1 : (0 : BitVec 64) = 1 →
      readBytes (walkFinishMemRefuse G s.mem C.alen C.evlen e) G.err 8 =
        readBytes m0 G.err 8 :=
    fun h => absurd h (by decide)
  have hsep24 : DisjointRegions (stage2StagedRegions G.b G.n G.ep G.nep G.xp G.nxp G.dst
      G.ndst0 G.ev G.evcap G.ndst G.nev G.err C.stage.c C.stage.ctype C.stage.cst
      C.stage.tok C.stage.s C.stage.z C.stage.e C.stage.nkSlot C.stage.nxpSlot) :=
    C.stage.separate
  have hsep25 : ∀ r ∈ stage2WalkRegions G.b G.n G.ep G.nep G.xp G.nxp G.dst G.ndst0 G.ev
      G.evcap G.ndst G.nev G.err C.stage.c C.stage.ctype C.stage.cst C.stage.tok
      C.stage.s C.stage.z C.stage.e, r.1 + r.2 ≤ C.stage.d ∨ C.stage.d + 8 ≤ r.1 :=
    C.stage.dSep
  refine ⟨G.b, G.n, G.ep, G.nep, G.xp, G.nxp, G.dst, G.dstcap, G.ndst, G.ev, G.evcap,
    G.nev, G.err, 0, G.ndst0, G.nev0, C.alen, C.evlen, arena, evs, C.stage.c,
    C.stage.ctype, C.stage.cst, C.stage.tok, C.stage.s, C.stage.z, C.stage.e, C.stage.d,
    C.stage.nkSlot, C.stage.nxpSlot, rfl, rfl, Or.inl rfl, G.ndstRead, G.nevRead,
    walkFinishMemRefuse_ndst G hndnev hnderr, walkFinishMemRefuse_nev G hnverr,
    hInv.alen_ge, halen, hnev0, hInv.evlen_le, G.dstcapLt, G.evcapLt, hevle, hnep64,
    G.nxpLt, hres, hArenaRead, hEvRead, hRefuse0, hAccept1, hpresentT, hframeT,
    hsep24, hsep25⟩

/-- **The record's boundary at the merge refusal routes' returned memory.**  The offset
store at `%e + 8` and then the copy's three: the same 25 conjuncts, at the memory whose
base is `walkFinishMemOffset`.  The two facts the shifted base costs are the offset
store's own (presence monotone, and the frame's scratch entry). -/
theorem stage2Boundary_of_refuse_offset {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G)
    {s : State} (hInv : WalkInv G C s) {v e : Nat} (he : e ≤ G.n) :
    stage2Boundary (walkFinishArgs G) m0 G.next0
      (walkFinishMemRefuse G (walkFinishMemOffset C.stage.e v s.mem) C.alen C.evlen e)
      (.int 64 0) := by
  obtain ⟨hndnev, hnderr, hnverr, -, -, -⟩ := walkFinish_sep G C
  have halen := hInv.alen_le
  have hevle : C.evlen ≤ G.evcap := le_trans hInv.evlen_le G.evRoom
  have hnev0 : G.nev0 ≤ C.evlen := by
    rw [hInv.evlen_eq]; omega
  have hres : C.alen + stage2ArenaReserve ≤ G.dstcap := by
    have h := G.arenaRoom
    omega
  have hnep64 : G.nep < 2 ^ 64 := by
    have hle := G.nep_le
    have hdoc := G.maxDoc
    simp only [stage2MaxDocument] at hdoc
    omega
  obtain ⟨⟨arena, hArenaRead⟩, ⟨evs, hEvRead⟩⟩ :=
    walkFinish_prefixes G C hInv (fun h => walkFinishMemRefuse_hasBytes G
      (hasBytes_writeBytes (m := s.mem) (start := C.stage.e + 8) (bs := wordBytes 8 v) h))
  have hframeT : UnchangedOutside m0
      (walkFinishMemRefuse G (walkFinishMemOffset C.stage.e v s.mem) C.alen C.evlen e)
      (stage2ReportFrame G.dst C.alen G.ev C.evlen G.ndst G.nev G.err C.stage.c
        C.stage.ctype C.stage.cst C.stage.tok C.stage.s C.stage.z C.stage.e C.stage.d
        G.next0) :=
    walkFinishMemRefuse_frame_of G C (walkFinishMemOffset_frame G C
      (walkFinishMem_base_frame G C s hInv))
  have hpresentT : ∀ x, inRegions (stage2ReportPresent G.dst C.alen G.ev C.evlen G.ndst
      G.nev G.err C.stage.c C.stage.ctype C.stage.cst C.stage.tok C.stage.s C.stage.z
      C.stage.e C.stage.d) x →
      present (walkFinishMemRefuse G (walkFinishMemOffset C.stage.e v s.mem) C.alen
        C.evlen e) x :=
    walkFinishMemRefuse_present_of G C hInv
      (fun h => hasBytes_writeBytes (m := s.mem) (start := C.stage.e + 8)
        (bs := wordBytes 8 v) h) halen hevle
  have hRefuse0 : (0 : BitVec 64) = 0 →
      ∃ e' : Nat, e' ≤ G.n ∧
        readBytes (walkFinishMemRefuse G (walkFinishMemOffset C.stage.e v s.mem)
          C.alen C.evlen e) G.err 8 = some (wordBytes 8 e') :=
    fun _ => ⟨e, he, walkFinishMemRefuse_err G⟩
  have hAccept1 : (0 : BitVec 64) = 1 →
      readBytes (walkFinishMemRefuse G (walkFinishMemOffset C.stage.e v s.mem)
        C.alen C.evlen e) G.err 8 = readBytes m0 G.err 8 :=
    fun h => absurd h (by decide)
  have hsep24 : DisjointRegions (stage2StagedRegions G.b G.n G.ep G.nep G.xp G.nxp G.dst
      G.ndst0 G.ev G.evcap G.ndst G.nev G.err C.stage.c C.stage.ctype C.stage.cst
      C.stage.tok C.stage.s C.stage.z C.stage.e C.stage.nkSlot C.stage.nxpSlot) :=
    C.stage.separate
  have hsep25 : ∀ r ∈ stage2WalkRegions G.b G.n G.ep G.nep G.xp G.nxp G.dst G.ndst0 G.ev
      G.evcap G.ndst G.nev G.err C.stage.c C.stage.ctype C.stage.cst C.stage.tok
      C.stage.s C.stage.z C.stage.e, r.1 + r.2 ≤ C.stage.d ∨ C.stage.d + 8 ≤ r.1 :=
    C.stage.dSep
  refine ⟨G.b, G.n, G.ep, G.nep, G.xp, G.nxp, G.dst, G.dstcap, G.ndst, G.ev, G.evcap,
    G.nev, G.err, 0, G.ndst0, G.nev0, C.alen, C.evlen, arena, evs, C.stage.c,
    C.stage.ctype, C.stage.cst, C.stage.tok, C.stage.s, C.stage.z, C.stage.e, C.stage.d,
    C.stage.nkSlot, C.stage.nxpSlot, rfl, rfl, Or.inl rfl, G.ndstRead, G.nevRead,
    walkFinishMemRefuse_ndst G hndnev hnderr, walkFinishMemRefuse_nev G hnverr,
    hInv.alen_ge, halen, hnev0, hInv.evlen_le, G.dstcapLt, G.evcapLt, hevle, hnep64,
    G.nxpLt, hres, hArenaRead, hEvRead, hRefuse0, hAccept1, hpresentT, hframeT,
    hsep24, hsep25⟩

/-! ### R1: the accept route

`cleanup478.i`'s terminal merge, `if.then485.i` on the empty-stack arm, `if.end490.i` with
the root slot set, `s2_walk.exit`'s copy and `if.end`'s return: five control steps from
the merge state to a return of `1` at `walkFinishMemAccept`.  The copy's `denote` is
`walkExitBlock_denote` at the state the three preceding steps leave, so the returned
memory is the named term rather than an existential's.

The merge's own premises are its `phi`s and `%nep`; `%nep` is `WalkFinalEnv`'s last
field, and the root word is the caller's (see the module header). -/

/-- **R1, accept: the merge's finish.**  From the terminal merge state the run takes the
exit's `1` arm: the two cursor words at `%ndst`/`%nev`, the verdict `1`, and the record's
boundary at that memory. -/
theorem walkFinishPost_accept {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State)
    (hInv : WalkInv G C s) (hblk : C.block = "cleanup478.i")
    (hregs : WalkRegs G C s.env) (hptrs : WalkPtrs G C s.env)
    (henv : WalkFinalEnv G C s.env)
    (hlog : readBytes s.mem (C.stage.z + 48) 8 = some (wordBytes 8 C.alen))
    {p : String} {spv k2 : Nat} {spOp kOp : Operand}
    (hpre : s.pre = some p)
    (hsp : phiIncoming p cleanupSpIncoming = some spOp)
    (hspv : evalOperand s spOp = some (.int 32 (BitVec.ofNat 32 spv)))
    (hk : phiIncoming p cleanupKIncoming = some kOp)
    (hkv : evalOperand s kOp = some (.int 64 (BitVec.ofNat 64 k2)))
    (hterm : k2 = (BitVec.ofNat 64 G.nep).toNat)
    (hsp0 : evalICmp .eq (BitVec.ofNat 32 spv) (BitVec.ofNat 32 0) = 1)
    {rv : BitVec 32} (hrootRead : readBytes s.mem (G.next0 + 8) 4 = some (natToBytes rv.toNat 4))
    (hroot0 : evalICmp .eq rv (BitVec.ofNat 32 0) = 0) :
    ∃ (q : Nat) (v : BitVec 64) (m : Mem), q + 2 ≤ 27 ∧
      runFuel (stage2Calls stage2SubCalls) (q + 2) stage2Body s =
        some (.ret (some (.int 64 v)) m) ∧
      stage2Boundary (walkFinishArgs G) m0 G.next0 m (.int 64 v) := by
  have henv0 : WalkFinalEnv G C s.env := henv
  obtain ⟨he, hz, hs, hc, hnd, hnv, her, hnp⟩ := henv0
  -- the merge's step
  obtain ⟨s₁, hstep₁, -, hs₁⟩ :=
    walkFinishMerge_at (calls := stage2Calls stage2SubCalls) (G := G) (C := C) (s := s)
      hInv hblk (p := p) (spv := spv) (k2 := k2) (spOp := spOp) (kOp := kOp)
      (nepv := BitVec.ofNat 64 G.nep) hpre hsp hspv hk hkv hnp hterm
  have hsp₁ : lookupName s₁.env "%sp.i.1" = some (.int 32 (BitVec.ofNat 32 spv)) := by
    rw [hs₁]
    simp only [cells]
    rw [lookupName_cons_ne (k := "%cmp.i") (n := "%sp.i.1") _ _ (by decide),
      lookupName_cons_ne (k := "%k.2.i") (n := "%sp.i.1") _ _ (by decide)]
    exact lookupName_cons_self _ _ _
  -- the carriers at the merge's target
  have hregs₁ : WalkRegs G C s₁.env := by
    rw [hs₁]
    exact hregs.cells_of _ (by
      intro n hn
      simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
        or_false] at hn
      rcases hn with rfl | rfl | rfl <;> decide)
  have hptrs₁ : WalkPtrs G C s₁.env := by
    rw [hs₁]
    simp only [cells]
    exact (((hptrs.bind (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)).bind (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)).bind (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide))
  have henv₁ : WalkFinalEnv G C s₁.env := by
    rw [hs₁]
    exact WalkFinalEnv.cells_of henv _ (by
      intro n hn
      simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
        or_false] at hn
      rcases hn with rfl | rfl | rfl <;> simp [walkFinalNames])
  -- the exit's first step, and the empty stack's arm
  let s₂ : State := exitS₂ s₁ spv
  have hstep₂ : step (stage2Calls stage2SubCalls) stage2Body s₁ = .jump s₂ := by
    rw [walkIfThen485Step (calls := stage2Calls stage2SubCalls) s₁ (by rw [hs₁])
      (spv := spv) hsp₁]
    simp only [s₂, exitS₂]
    rw [show (if evalICmp .eq (BitVec.ofNat 32 spv) (BitVec.ofNat 32 0) = 1
      then "if.end490.i" else "if.then488.i") = "if.end490.i" from ite_eq_left hsp0]
  have hsm₂ : s₂.mem = s.mem := by
    dsimp only [s₂, exitS₂, State.bind]
    rw [hs₁]
  -- the carriers at the exit's test
  have hregs₂ : WalkRegs G C s₂.env := by
    dsimp only [s₂, exitS₂]
    exact hregs₁.bind (by decide)
  have hptrs₂ : WalkPtrs G C s₂.env := by
    dsimp only [s₂, exitS₂]
    exact hptrs₁.bind (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have henv₂ : WalkFinalEnv G C s₂.env := by
    dsimp only [s₂, exitS₂]
    exact henv₁.bind (by simp [walkFinalNames])
  -- the root word at the exit's test
  have hroot₂ : readBytes s₂.mem (G.next0 + 8) 4 = some (natToBytes rv.toNat 4) := by
    rw [hsm₂]; exact hrootRead
  let s₃ : State := exitS₃ s₂ rv
  have hstep₃ : step (stage2Calls stage2SubCalls) stage2Body s₂ = .jump s₃ :=
    walkFinish490StepExit (calls := stage2Calls stage2SubCalls) rfl
      ((exitS₂_rd (s := s₁) (spv := spv)).trans
        (hregs₁ ("%root_done.i", .ptr (G.next0 + 8)) (by simp [walkStaticRegs])))
      hroot₂ hroot0
  have hsm₃ : s₃.mem = s.mem := by
    dsimp only [s₃, exitS₃, State.bind]
    rw [hsm₂]
  -- the carriers at the exit block
  have hregs₃ : WalkRegs G C s₃.env := by
    dsimp only [s₃, exitS₃, State.bind]
    exact (hregs₂.bind (by decide)).bind (by decide)
  have hptrs₃ : WalkPtrs G C s₃.env := by
    dsimp only [s₃, exitS₃, State.bind]
    exact (hptrs₂.bind (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)).bind (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)
  have henv₃ : WalkFinalEnv G C s₃.env := by
    dsimp only [s₃, exitS₃, State.bind]
    exact (henv₂.bind (by simp [walkFinalNames])).bind (by simp [walkFinalNames])
  -- the two words the exit block copies, and their widths
  let A : BitVec 64 := BitVec.ofNat 64 C.alen
  let L : BitVec 64 := BitVec.ofNat 64 C.evlen
  have halen64 : C.alen < 2 ^ 64 := by
    have h := G.arenaRoom
    have hcap := G.dstcapLt
    have hle := hInv.alen_le
    omega
  have hevlen64 : C.evlen < 2 ^ 64 := by
    have hle : C.evlen ≤ G.evcap := le_trans hInv.evlen_le G.evRoom
    have hcap := G.evcapLt
    omega
  have hAtoNat : A.toNat = C.alen := by
    dsimp only [A]
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt halen64]
  have hLtoNat : L.toNat = C.evlen := by
    dsimp only [L]
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hevlen64]
  obtain ⟨-, -, -, hsep, -, -⟩ := walkFinish_sep G C
  have hAread : readBytes s₃.mem (C.stage.z + 48) 8 = some (natToBytes A.toNat 8) := by
    rw [hAtoNat, hsm₃]
    exact hlog
  have hLread : readBytes s₃.mem (C.stage.z + 8) 8 = some (natToBytes L.toNat 8) := by
    rw [hLtoNat, hsm₃]
    exact hInv.log_len
  have henv₃' : WalkFinalEnv G C s₃.env := henv₃
  obtain ⟨-, -, -, hc', hnd', hnv', -, -⟩ := henv₃'
  have hden : denoteCode (stage2Calls stage2SubCalls) walkExitBlock.instrs s₃ =
      some (walkExitBlockState s₃.env G.ndst G.nev A L s₃) := by
    have h := walkExitBlock_denote (sub := stage2SubCalls) s₃.env s₃
      (hregs₃ ("%xj.i", .ptr (G.next0 + 12)) (by simp [walkStaticRegs]))
      (hregs₃ ("%root_done.i", .ptr (G.next0 + 8)) (by simp [walkStaticRegs]))
      hptrs₃.2.2.2.2.1 hptrs₃.2.2.2.1 hc'
      (hregs₃ ("%alen", .ptr (C.stage.z + 48)) (by simp [walkStaticRegs]))
      hnd' (hregs₃ ("%len", .ptr (C.stage.z + 8)) (by simp [walkStaticRegs]))
      hnv' hAread hLread hsep
    simpa only [stateAt_self, walkExitBlockState] using h
  -- the exit block's step, and the return
  let s₄ : State := { walkExitBlockState s₃.env G.ndst G.nev A L s₃ with
    pc := "if.end", pre := some s₃.pc }
  have hstep₄ : step (stage2Calls stage2SubCalls) stage2Body s₃ = .jump s₄ :=
    walkExitStep (sub := stage2SubCalls) s₃ (by dsimp only [s₃, exitS₃]) hden
      (walkExitBlockState_pc _ _ _ _ _ _)
  have henv₄ : WalkFinalEnv G C s₄.env := by
    dsimp only [s₄, walkExitBlockState]
    exact WalkFinalEnv.cells_of henv₃ _ (by
      intro n hn
      simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
        or_false] at hn
      rcases hn with rfl | rfl <;> simp [walkFinalNames])
  obtain ⟨he₄, hz₄, hs₄, -⟩ := henv₄
  have hpre₄ : s₄.pre = some "s2_walk.exit" := rfl
  let s₅ : State := stateAt (("%tobool.not151", .int 64 1) :: s₄.env) s₄
  have hstep₅ : step (stage2Calls stage2SubCalls) stage2Body s₄ =
      .ret (some (.int 64 1)) s₅ :=
    walkIfEnd_step (sub := stage2SubCalls) s₄ rfl he₄ hz₄ hs₄ hpre₄ (by decide) (by decide)
  have hmem₅ : s₅.mem = walkFinishMemAccept G s.mem C.alen C.evlen := by
    dsimp only [s₅, s₄]
    rw [stateAt_mem, walkExitBlockState_mem, walkFinishMemAccept, hAtoNat, hLtoNat, hsm₃]
  refine ⟨3, 1, walkFinishMemAccept G s.mem C.alen C.evlen, by omega, ?_,
    stage2Boundary_of_accept G C hInv⟩
  rw [show (3 + 2 : Nat) = 1 + (1 + (1 + (1 + (1 + 0)))) from by omega]
  rw [runFuel_jump_prefix (f := stage2Body) hstep₁ (1 + (1 + (1 + (1 + 0))))]
  rw [runFuel_jump_prefix (f := stage2Body) hstep₂ (1 + (1 + (1 + 0)))]
  rw [runFuel_jump_prefix (f := stage2Body) hstep₃ (1 + (1 + 0))]
  rw [runFuel_jump_prefix (f := stage2Body) hstep₄ (1 + 0)]
  rw [show (1 + 0 : Nat) = 1 from by omega]
  simp only [runFuel, hstep₅, hmem₅]

end WalkScope
end LeanLLVM.Refinement

/-! ### Axiom footprints

Printed rather than pinned: the module is not stable while the two refusal routes'
terminal runs are unwritten, and a `#guard_msgs` pin would have to be revisited by the
very change that adds them.  `AGENTS.md` asks for a pin once a theorem is stable. -/

#print axioms LeanLLVM.Refinement.WalkScope.stage2Boundary_of_accept
#print axioms LeanLLVM.Refinement.WalkScope.stage2Boundary_of_refuse
#print axioms LeanLLVM.Refinement.WalkScope.stage2Boundary_of_refuse_offset
#print axioms LeanLLVM.Refinement.WalkScope.walkFinishPost_accept
