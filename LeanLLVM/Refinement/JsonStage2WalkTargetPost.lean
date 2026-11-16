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
  three slots), and the verdict `0`.  `walkFinishPost_refuse` (through `if.then492.i`) and
  `walkFinishPost_refuse488` (through `if.then488.i`).
* **R0, a segment already at the copy** — `if.then → if.end`, three writes (the copy's),
  and the verdict `0`.  `walkFinishPost_copy`.

Each concludes `stage2Boundary` at the memory the route actually returns
(`walkFinishMemAccept` for R1, `walkFinishMemRefuse` for the refusal routes), and each
concludes the run that reaches it: `walkFinishCopyTail` is the refusal arm's two steps,
shared by R2, R3 and R0, so a refusal route owes only the reaches of `if.then` and the
three words the copy reads.

## What is proved here

**Proved**: the boundary at the returned memory for all three routes — the 25 conjuncts of
`stage2Boundary`, at a variable base memory, from `WalkInv` plus the supplied facts below
— and each route's terminal run with its memory named.  That is the output-side statement
the loop arm's post needs, and it is exactly `WalkTargetPost` (`JsonStage2WalkTraverse`):
the loop's terminal disjunct carries the returned memory and the boundary there.

**Composed, not assumed.**  `walkFinishPost_merge` is the merge's three routes as one
statement — the depth's zero test and the root-done test select among R1, R2 and R3 — and
`WalkMergeWords`/`WalkRefuseWords` are the word bundles a caller supplies: one word, the
log's arena cursor.  The registers, `%4` and `%nep` are the carrier's, the root-done slot
is `WalkInv.root_slot` read as four bytes (`walkRootWord_of_hasBytes`), and the copy's
`%off` word is the refusal segment's own store (`WalkRefuseSegment`), so what
remains outside the proofs is the log's word alone:
`JsonStage2WalkPremisesOfStaging`'s `WalkLoopEnd` names its producer.

**The measurements that shaped it.**  The copy's steps are stated at *named* states
(`walkFinishCopyState`) rather than at inline record updates: a record update written
inline inside three step equations is re-elaborated at every place it is printed, and the
memory under it is a three-deep write, which times out at `whnf`.  And the refusal
routes' base memory is the offset store (`walkFinishMemOffset`), so every read the copy
takes is one `walkReadBytes_writeBytes_outside` across it — the log's two words by
`walkFinish_log_sep`, the refusal word by its own read-back.

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

`WalkInv` bounds but does not fix the words the finalisation reads.  The route theorems
therefore take the words below as *arguments*, one bundle per entry block
(`WalkMergeWords`, `WalkRefuseWords`), and each names where the repository would produce
it.  The registers the routes read are not among them: all seven names of `WalkFinalEnv`
and `%4` are `walkStaticRegs` entries, so `hInv.regs` answers them
(`walkFinalEnv_of_regs`, `walkMerge4_of_regs`).  `%nep` is not among them either: the
dispatch's outcome carries its value at every state the merge is read at, so
`hnp`/`hterm` are the outcome's own data, and `WalkLoopEnd.nepBound` bounds it from the
carrier.

* `%4 = n`: **derived.**  `%4` is an entry of `walkStaticRegs` (`("%4", .int 64
  (BitVec.ofNat 64 G.n))`), so `WalkInv.regs` names its cell and the routes read it
  through `walkMerge4_of_regs`; the bundle no longer carries it.
* the log's arena word equal to the carry's cursor (`log`).  `WalkInv.log_alen` gives
  only `∃ a, ndst0 ≤ a ∧ a ≤ C.alen`, and the equality is *false* at any state whose
  decoded prefix is shorter than the extent it reserved — an escaping string leaves the
  slot short of the carry at every later loop head (`JsonStage2WalkArenaWord`'s
  `not_arenaWord_of_lt`).  So it can be neither a clause nor a lemma, no producer of it
  exists to name, and the fix is a change to the statement the finalisation reports
  rather than a proof; it is supplied at the merge's own state, and `WalkMergeWords`'
  note records that.
* the finalisation blocks' registers (`WalkFinalEnv`): **derived.**  `%e`, `%z`, `%s`,
  `%c.i`, `%ndst`, `%nev` and `%err` are all entries of `walkStaticRegs`, so
  `walkFinalEnv_of_regs` reads the whole predicate off `WalkInv.regs`.  The carriers give
  six more (`%alen`, `%len`, `%xj.i`, `%root_done.i` from `walkStaticRegs`,
  `%ctype.i`/`%cst.i` from `WalkPtrs`).  `%nep` is the eighth finalisation register and is
  not supplied here either: the dispatch's outcome carries it (`hnepv`), so each merge
  route takes `hnp`/`hterm` from there, and `WalkLoopEnd.nepBound` bounds it at the
  carrier's value.
* the merge's root-done word: **derived.**  `WalkInv.root_slot` is presence over
  `G.next0 + 8`'s four bytes, and the root-done test reads them as an `i32`, so
  `walkRootWord_of_hasBytes` names the word from the clause — no bundle field.
* R0's refusal word: **the segment's own store.**  The copy loads `%e + 8`, which the
  refusing block wrote immediately before the edge, and `WalkSegment` keeps no memory, so
  the word travels with the segment as `WalkRefuseSegment`'s third field
  (`JsonStage2WalkTraverse`).  The copy's `hword` is that field, and the value is the
  branch's (`%idxprom.i`'s position, `%4`'s length), not the carry's `eoff`.
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

/-- **The copy's state at `if.end`**: `walkIfThenBlockState` with the copy's block and
its predecessor.  Named so the tail's second step and its returned memory are stated at
one term — a record update written inline inside a step's conclusion is re-elaborated at
every place it is printed, and the memory underneath it is a three-deep write. -/
def walkFinishCopyState (env : Env) (nd nv err e : Nat) (A L E : BitVec 64)
    (p : String) (s : State) : State :=
  { walkIfThenBlockState env nd nv err e A L E s with pc := "if.end", pre := some p }

/-- The copy state's memory is the copy's. -/
theorem walkFinishCopyState_mem (env : Env) (nd nv err e : Nat) (A L E : BitVec 64)
    (p : String) (s : State) :
    (walkFinishCopyState env nd nv err e A L E p s).mem =
      (walkIfThenBlockState env nd nv err e A L E s).mem := by
  simp only [walkFinishCopyState]

/-- **The copy's state is at the block it was entered at.**  The twin of
`walkExitBlockState_pc`, for the refusal arm's `walkIfThenBlockState`. -/
theorem walkFinishCopy_pc (env : Env) (nd nv err e : Nat) (A L E : BitVec 64)
    (s : State) : (walkIfThenBlockState env nd nv err e A L E s).pc = s.pc := by
  simp only [walkIfThenBlockState, stateAt, walkSetMem]

/-- **The copy's state returns the block's three writes.**  Stated by rewriting the
named state's three layers rather than by `rfl`: at a term whose memory is the
three-deep write, `rfl` unfolds the writes at every position. -/
theorem walkFinishCopy_mem (env : Env) (nd nv err e : Nat) (A L E : BitVec 64)
    (s : State) :
    (walkIfThenBlockState env nd nv err e A L E s).mem =
      writeBytes
        (writeBytes (writeBytes s.mem nd (wordBytes 8 A.toNat)) nv
          (wordBytes 8 L.toNat))
        err (wordBytes 8 E.toNat) := by
  rw [walkIfThenBlockState, stateAt_mem, walkSetMem_mem]

/-- **The copy's four cells leave `%e`, `%z` and `%s` alone.**  `if.end`'s three
markers read them, and the copy binds `%51`, `%52`, `%off` and `%53` instead. -/
theorem walkFinishCopy_cells (env : Env) (nd nv err e : Nat) (A L E : BitVec 64)
    (s : State) :
    lookupName (walkIfThenBlockState env nd nv err e A L E s).env "%e"
        = lookupName env "%e" ∧
    lookupName (walkIfThenBlockState env nd nv err e A L E s).env "%z"
        = lookupName env "%z" ∧
    lookupName (walkIfThenBlockState env nd nv err e A L E s).env "%s"
        = lookupName env "%s" := by
  refine ⟨?_, ?_, ?_⟩ <;>
    simp [walkIfThenBlockState, stateAt, cells, lookupName_cons_ne]

/-- **The log is separate from the error record.**  The two offsets the copy's reads
have to pass the refusal offset's store at: `%z`'s forty-eight- and eight-byte
windows against `%e`'s twenty-four bytes.  Both are `staged_pair`'s instance at the
two objects' extents. -/
theorem walkFinish_log_sep {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) :
    (C.stage.z + 48 + 8 ≤ C.stage.e + 8 ∨ C.stage.e + 8 + 8 ≤ C.stage.z + 48) ∧
    (C.stage.z + 8 + 8 ≤ C.stage.e + 8 ∨ C.stage.e + 8 + 8 ≤ C.stage.z + 8) := by
  have h := staged_pair (b := G.b) (n := G.n) (ep := G.ep) (nep := G.nep)
    (xp := G.xp) (nxp := G.nxp) (dst := G.dst) (ndst0 := G.ndst0) (ev := G.ev)
    (evcap := G.evcap) (ndst := G.ndst) (nev := G.nev) (err := G.err)
    (c := C.stage.c) (ctype := C.stage.ctype) (cst := C.stage.cst) (tok := C.stage.tok)
    (sv := C.stage.s) (z := C.stage.z) (e := C.stage.e) C.stage.separate
    (r := (C.stage.z, stage2LogExtent)) (by simp [stage2WalkRegions, stage2StagedWrites])
    (q := (C.stage.e, stage2ErrorExtent)) (by simp [stage2WalkRegions, stage2StagedWrites])
    (by
      intro hh
      have h2' : stage2LogExtent = stage2ErrorExtent := congrArg Prod.snd hh
      exact absurd h2' (by decide))
  simp only [stage2LogExtent, stage2ErrorExtent] at h
  exact ⟨by omega, by omega⟩

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

/-- **The offset store reads back at its own address.**  `if.then492.i` and
`if.then488.i` each write `wordBytes 8 v` at `%e + 8`, and the copy's `%off` load
reads exactly that. -/
theorem walkFinishMemOffset_read {m : Mem} {e v : Nat} :
    readBytes (walkFinishMemOffset e v m) (e + 8) 8 = some (wordBytes 8 v) := by
  rw [walkFinishMemOffset]
  exact walkFinishReadBytes_writeBytes_len (by rw [wordBytes, natToBytes_length])

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

The seven register lookups no `WalkInv` clause carries.  One predicate, so the routes
take one hypothesis, and one transport lemma, so each step's `cells` list is discharged
by a literal comparison.

`%nep` is deliberately absent: it *is* carried by the dispatch's outcome (`hnepv`) at
every state the merge is read at, so a route takes it from there rather than from a
second supply that would then have to be proved equal to the first. -/

/-- The names `WalkFinalEnv` binds, as the list its transport lemmas decide on. -/
def walkFinalNames : List String :=
  ["%e", "%z", "%s", "%c.i", "%ndst", "%nev", "%err"]

/-- **The finalisation blocks' registers.**  `s2_walk.exit`, `if.then` and `if.end` read
`%alen`, `%len`, `%xj.i`, `%root_done.i`, `%ctype.i` and `%cst.i` — all in the two
carriers — and these seven, which no clause of `WalkInv` names: the three record slots,
the two finalisation records and the cursor record.  They are fixed by
the staging's own stores at `entry`, so they are a seed fact rather than a walk fact. -/
def WalkFinalEnv {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (env : Env) : Prop :=
  lookupName env "%e" = some (.ptr C.stage.e) ∧
    lookupName env "%z" = some (.ptr C.stage.z) ∧
    lookupName env "%s" = some (.ptr C.stage.s) ∧
    lookupName env "%c.i" = some (.ptr C.stage.c) ∧
    lookupName env "%ndst" = some (.ptr G.ndst) ∧
    lookupName env "%nev" = some (.ptr G.nev) ∧
    lookupName env "%err" = some (.ptr G.err)

/-- A cell list whose names miss `walkFinalNames` leaves the predicate alone. -/
theorem WalkFinalEnv.cells_of {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {env : Env}
    (h : WalkFinalEnv G C env) (cs : List (String × Value))
    (hne : ∀ n ∈ cs.map (·.1), n ∉ walkFinalNames) : WalkFinalEnv G C (cells cs env) := by
  obtain ⟨he, hz, hs, hc, hnd, hnv, her⟩ := h
  have hmiss : ∀ n : String, n ∈ walkFinalNames → n ∉ cs.map (·.1) :=
    fun n hn hc => hne n hc hn
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
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

/-- A bind at a name outside the list leaves the predicate alone. -/
theorem WalkFinalEnv.bind {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {env : Env}
    (h : WalkFinalEnv G C env) {d : String} {v : Value} (hd : d ∉ walkFinalNames) :
    WalkFinalEnv G C ((d, v) :: env) := by
  obtain ⟨he, hz, hs, hc, hnd, hnv, her⟩ := h
  have hne : ∀ n, n ∈ walkFinalNames → d ≠ n := fun n hn hdn => hd (hdn ▸ hn)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
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
cursor's interval all miss `%err`'s eight bytes. -/
theorem walkInv_err_not_frame {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {s : State}
    (hInv : WalkInv G C s) {k : Nat} {n : Nat} (hk : k < 8) :
    ¬ inRegions (walkWideAt G C n) (G.err + k) := by
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
  have hOn : UnchangedOn (inRegions (walkWideAt G C (s.next - G.next0))) m0 s.mem :=
    fun a ha => hInv.frame a (fun r hr hi => ha ⟨r, hr, hi⟩)
  refine readBytes_eq_of_UnchangedOn hOn ?_
  intro k hk
  exact walkInv_err_not_frame hInv hk

/-! ### The frame at the reported extents

`WalkInv.frame` is silence outside the cursor's interval and the carried prefixes; the
record's frame is stated at the reported cursor, which is the log's word, and its stack
part is the interval from that cursor to the run's own end, `stage2StackEnd G.next0
s.next`.  The two are the same interval at two ends, so the derivation is one widening
and carries no hypothesis on the cursor. -/

/-- **The frame at the record's list, from the walk's.** -/
theorem walkFinishMem_base_frame {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State)
    (hInv : WalkInv G C s) :
    UnchangedOutside m0 s.mem
      (stage2ReportFrame G.dst C.alen G.ev C.evlen G.ndst G.nev G.err C.stage.c
        C.stage.ctype C.stage.cst C.stage.tok C.stage.s C.stage.z C.stage.e C.stage.d
        G.next0 (stage2StackEnd G.next0 s.next)) := by
  obtain ⟨-, -, -, -, -, -, -, hfr⟩ := WalkInv.report hInv
  exact hfr

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
    {nextEnd : Nat}
    (h : UnchangedOutside m0 m
      (stage2ReportFrame G.dst C.alen G.ev C.evlen G.ndst G.nev G.err C.stage.c
        C.stage.ctype C.stage.cst C.stage.tok C.stage.s C.stage.z C.stage.e C.stage.d
        G.next0 nextEnd)) {v : Nat} :
    UnchangedOutside m0 (walkFinishMemOffset C.stage.e v m)
      (stage2ReportFrame G.dst C.alen G.ev C.evlen G.ndst G.nev G.err C.stage.c
        C.stage.ctype C.stage.cst C.stage.tok C.stage.s C.stage.z C.stage.e C.stage.d
        G.next0 nextEnd) :=
  UnchangedOutside.write_le (a := C.stage.e + 8) (w := 8) (bs := wordBytes 8 v) h
    ⟨(C.stage.e, stage2ErrorExtent), by
      simp [stage2ReportFrame, stage2ReportPresent, stage2ReportScratch,
        stage2StagedWrites], by omega,
      by simp only [stage2ErrorExtent]; omega⟩
    (by simp [wordBytes, natToBytes_length])

/-- **The accept route's frame, from a frame at the base memory.**  The two cursor stores,
each inside its own entry of the record's list. -/
theorem walkFinishMemAccept_frame_of {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) {m : Mem}
    {nextEnd : Nat}
    (h : UnchangedOutside m0 m
      (stage2ReportFrame G.dst C.alen G.ev C.evlen G.ndst G.nev G.err C.stage.c
        C.stage.ctype C.stage.cst C.stage.tok C.stage.s C.stage.z C.stage.e C.stage.d
        G.next0 nextEnd)) :
    UnchangedOutside m0 (walkFinishMemAccept G m C.alen C.evlen)
      (stage2ReportFrame G.dst C.alen G.ev C.evlen G.ndst G.nev G.err C.stage.c
        C.stage.ctype C.stage.cst C.stage.tok C.stage.s C.stage.z C.stage.e C.stage.d
        G.next0 nextEnd) := by
  have h1 : UnchangedOutside m0
      (writeBytes m G.ndst (wordBytes 8 C.alen))
      (stage2ReportFrame G.dst C.alen G.ev C.evlen G.ndst G.nev G.err C.stage.c
        C.stage.ctype C.stage.cst C.stage.tok C.stage.s C.stage.z C.stage.e C.stage.d
        G.next0 nextEnd) :=
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
        G.next0 (stage2StackEnd G.next0 s.next)) :=
  walkFinishMemAccept_frame_of G C (walkFinishMem_base_frame G C s hInv)

/-- **The refusal routes' frame, from a frame at the base memory.** -/
theorem walkFinishMemRefuse_frame_of {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) {m : Mem}
    {nextEnd : Nat}
    (h : UnchangedOutside m0 m
      (stage2ReportFrame G.dst C.alen G.ev C.evlen G.ndst G.nev G.err C.stage.c
        C.stage.ctype C.stage.cst C.stage.tok C.stage.s C.stage.z C.stage.e C.stage.d
        G.next0 nextEnd)) {e : Nat} :
    UnchangedOutside m0 (walkFinishMemRefuse G m C.alen C.evlen e)
      (stage2ReportFrame G.dst C.alen G.ev C.evlen G.ndst G.nev G.err C.stage.c
        C.stage.ctype C.stage.cst C.stage.tok C.stage.s C.stage.z C.stage.e C.stage.d
        G.next0 nextEnd) :=
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
        G.next0 (stage2StackEnd G.next0 s.next)) :=
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
  have hframeT : ∃ nextEnd : Nat, G.next0 ≤ nextEnd ∧
      UnchangedOutside m0 (walkFinishMemAccept G s.mem C.alen C.evlen)
        (stage2ReportFrame G.dst C.alen G.ev C.evlen G.ndst G.nev G.err C.stage.c
          C.stage.ctype C.stage.cst C.stage.tok C.stage.s C.stage.z C.stage.e C.stage.d
          G.next0 nextEnd) :=
    ⟨stage2StackEnd G.next0 s.next, by
      have hmax := stage2StackEnd_static G.next0 s.next
      simp only [stage2BootstrapExtent] at hmax
      omega, walkFinishMemAccept_frame G C s hInv⟩
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
  obtain ⟨nendT, hnendT, hframeT⟩ := hframeT
  refine stage2Boundary_of_witness
    (w :=
      { b := G.b, n := G.n, ep := G.ep, nep := G.nep, xp := G.xp, nxp := G.nxp,
        dst := G.dst, dstcap := G.dstcap, ndst := G.ndst, ev := G.ev,
        evcap := G.evcap, nev := G.nev, err := G.err, verdict := 1,
        ndst0 := G.ndst0, nev0 := G.nev0, ndst' := C.alen, nev' := C.evlen,
        arena := arena, evs := evs, c := C.stage.c, ctype := C.stage.ctype,
        cst := C.stage.cst, tok := C.stage.tok, s := C.stage.s, z := C.stage.z,
        e := C.stage.e, d := C.stage.d, nkSlot := C.stage.nkSlot,
        nxpSlot := C.stage.nxpSlot, nextEnd := nendT })
    (h :=
      { args_eq := rfl, value_eq := rfl, verdict_range := Or.inr rfl,
        ndst0_read := G.ndstRead, nev0_read := G.nevRead,
        ndst_read := walkFinishMemAccept_ndst G hndnev,
        nev_read := walkFinishMemAccept_nev G, ndst0_le := hInv.alen_ge,
        ndst_le_n := halen, nev0_le := hnev0, nev_le := hInv.evlen_le,
        dstcap_lt := G.dstcapLt, evcap_lt := G.evcapLt, nev_le_evcap := hevle,
        nep_lt := hnep64, nxp_lt := G.nxpLt, reserve := hres,
        arena_read := hArenaRead, evs_read := hEvRead, refuse_word := hRefuse0,
        accept_word := hAccept1, present := hpresentT, next_le := hnendT,
        frame := hframeT, staged := hsep24, dSep := hsep25 })

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
  have hframeT : ∃ nextEnd : Nat, G.next0 ≤ nextEnd ∧
      UnchangedOutside m0 (walkFinishMemRefuse G s.mem C.alen C.evlen e)
        (stage2ReportFrame G.dst C.alen G.ev C.evlen G.ndst G.nev G.err C.stage.c
          C.stage.ctype C.stage.cst C.stage.tok C.stage.s C.stage.z C.stage.e C.stage.d
          G.next0 nextEnd) :=
    ⟨stage2StackEnd G.next0 s.next, by
      have hmax := stage2StackEnd_static G.next0 s.next
      simp only [stage2BootstrapExtent] at hmax
      omega, walkFinishMemRefuse_frame G C s hInv⟩
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
  obtain ⟨nendT, hnendT, hframeT⟩ := hframeT
  refine stage2Boundary_of_witness
    (w :=
      { b := G.b, n := G.n, ep := G.ep, nep := G.nep, xp := G.xp, nxp := G.nxp,
        dst := G.dst, dstcap := G.dstcap, ndst := G.ndst, ev := G.ev,
        evcap := G.evcap, nev := G.nev, err := G.err, verdict := 0,
        ndst0 := G.ndst0, nev0 := G.nev0, ndst' := C.alen, nev' := C.evlen,
        arena := arena, evs := evs, c := C.stage.c, ctype := C.stage.ctype,
        cst := C.stage.cst, tok := C.stage.tok, s := C.stage.s, z := C.stage.z,
        e := C.stage.e, d := C.stage.d, nkSlot := C.stage.nkSlot,
        nxpSlot := C.stage.nxpSlot, nextEnd := nendT })
    (h :=
      { args_eq := rfl, value_eq := rfl, verdict_range := Or.inl rfl,
        ndst0_read := G.ndstRead, nev0_read := G.nevRead,
        ndst_read := walkFinishMemRefuse_ndst G hndnev hnderr,
        nev_read := walkFinishMemRefuse_nev G hnverr, ndst0_le := hInv.alen_ge,
        ndst_le_n := halen, nev0_le := hnev0, nev_le := hInv.evlen_le,
        dstcap_lt := G.dstcapLt, evcap_lt := G.evcapLt, nev_le_evcap := hevle,
        nep_lt := hnep64, nxp_lt := G.nxpLt, reserve := hres,
        arena_read := hArenaRead, evs_read := hEvRead, refuse_word := hRefuse0,
        accept_word := hAccept1, present := hpresentT, next_le := hnendT,
        frame := hframeT, staged := hsep24, dSep := hsep25 })

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
  have hframeT : ∃ nextEnd : Nat, G.next0 ≤ nextEnd ∧
      UnchangedOutside m0
        (walkFinishMemRefuse G (walkFinishMemOffset C.stage.e v s.mem) C.alen C.evlen e)
        (stage2ReportFrame G.dst C.alen G.ev C.evlen G.ndst G.nev G.err C.stage.c
          C.stage.ctype C.stage.cst C.stage.tok C.stage.s C.stage.z C.stage.e C.stage.d
          G.next0 nextEnd) :=
    ⟨stage2StackEnd G.next0 s.next, by
      have hmax := stage2StackEnd_static G.next0 s.next
      simp only [stage2BootstrapExtent] at hmax
      omega,
      walkFinishMemRefuse_frame_of G C (walkFinishMemOffset_frame G C
        (walkFinishMem_base_frame G C s hInv))⟩
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
  obtain ⟨nendT, hnendT, hframeT⟩ := hframeT
  refine stage2Boundary_of_witness
    (w :=
      { b := G.b, n := G.n, ep := G.ep, nep := G.nep, xp := G.xp, nxp := G.nxp,
        dst := G.dst, dstcap := G.dstcap, ndst := G.ndst, ev := G.ev,
        evcap := G.evcap, nev := G.nev, err := G.err, verdict := 0,
        ndst0 := G.ndst0, nev0 := G.nev0, ndst' := C.alen, nev' := C.evlen,
        arena := arena, evs := evs, c := C.stage.c, ctype := C.stage.ctype,
        cst := C.stage.cst, tok := C.stage.tok, s := C.stage.s, z := C.stage.z,
        e := C.stage.e, d := C.stage.d, nkSlot := C.stage.nkSlot,
        nxpSlot := C.stage.nxpSlot, nextEnd := nendT })
    (h :=
      { args_eq := rfl, value_eq := rfl, verdict_range := Or.inl rfl,
        ndst0_read := G.ndstRead, nev0_read := G.nevRead,
        ndst_read := walkFinishMemRefuse_ndst G hndnev hnderr,
        nev_read := walkFinishMemRefuse_nev G hnverr, ndst0_le := hInv.alen_ge,
        ndst_le_n := halen, nev0_le := hnev0, nev_le := hInv.evlen_le,
        dstcap_lt := G.dstcapLt, evcap_lt := G.evcapLt, nev_le_evcap := hevle,
        nep_lt := hnep64, nxp_lt := G.nxpLt, reserve := hres,
        arena_read := hArenaRead, evs_read := hEvRead, refuse_word := hRefuse0,
        accept_word := hAccept1, present := hpresentT, next_le := hnendT,
        frame := hframeT, staged := hsep24, dSep := hsep25 })

/-! ### R1: the accept route

`cleanup478.i`'s terminal merge, `if.then485.i` on the empty-stack arm, `if.end490.i` with
the root slot set, `s2_walk.exit`'s copy and `if.end`'s return: five control steps from
the merge state to a return of `1` at `walkFinishMemAccept`.  The copy's `denote` is
`walkExitBlock_denote` at the state the three preceding steps leave, so the returned
memory is the named term rather than an existential's.

The merge's own premises are its `phi`s, its `%nep` cell and the index it selects
(`hterm`); the root word and the finalisation's words are the caller's (see the module
header). -/

/-- **R1, accept: the merge's finish.**  From the terminal merge state the run takes the
exit's `1` arm: the two cursor words at `%ndst`/`%nev`, the verdict `1`, and the record's
boundary at that memory. -/
theorem walkFinishPost_accept {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State)
    (hInv : WalkInv G C s)
    (hblk : C.block = "cleanup478.i")
    (hregs : WalkRegs G C s.env) (hptrs : WalkPtrs G C s.env)
    (henv : WalkFinalEnv G C s.env)
    (hlog : readBytes s.mem (C.stage.z + 48) 8 = some (wordBytes 8 C.alen))
    {p : String} {spv k2 : Nat} {spOp kOp : Operand}
    (hpre : s.pre = some p)
    (hsp : phiIncoming p cleanupSpIncoming = some spOp)
    (hspv : evalOperand s spOp = some (.int 32 (BitVec.ofNat 32 spv)))
    (hk : phiIncoming p cleanupKIncoming = some kOp)
    (hkv : evalOperand s kOp = some (.int 64 (BitVec.ofNat 64 k2)))
    {nepv : BitVec 64} (hnp : lookupName s.env "%nep" = some (.int 64 nepv))
    (hterm : k2 = nepv.toNat)
    (hsp0 : evalICmp .eq (BitVec.ofNat 32 spv) (BitVec.ofNat 32 0) = 1)
    {rv : BitVec 32} (hrootRead : readBytes s.mem (G.next0 + 8) 4 = some (natToBytes rv.toNat 4))
    (hroot0 : evalICmp .eq rv (BitVec.ofNat 32 0) = 0) :
    ∃ (q : Nat) (v : BitVec 64) (m : Mem), q + 2 ≤ 27 ∧
      runFuel (stage2Calls stage2SubCalls) (q + 2) stage2Body s =
        some (.ret (some (.int 64 v)) m) ∧
      stage2Boundary (walkFinishArgs G) m0 G.next0 m (.int 64 v) := by
  have henv0 : WalkFinalEnv G C s.env := henv
  obtain ⟨he, hz, hs, hc, hnd, hnv, her⟩ := henv0
  -- the merge's step
  obtain ⟨s₁, hstep₁, -, hs₁⟩ :=
    walkFinishMerge_at (calls := stage2Calls stage2SubCalls) (G := G) (C := C) (s := s)
      hInv hblk (p := p) (spv := spv) (k2 := k2) (spOp := spOp) (kOp := kOp)
      (nepv := nepv) hpre hsp hspv hk hkv hnp hterm
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
  obtain ⟨-, -, -, hc', hnd', hnv', -⟩ := henv₃'
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

/-! ### The refusal copy's tail, and R2's route

The refusal arm's last two steps are common to all three refusal routes: the copy
writes the record's three slots and jumps to `if.end`, which returns the refusal φ's
literal zero.  `walkFinishCopyTail` states them at any state at `if.then`, so a route
owes only the reaches of that state — and the three words the copy reads.

`walkFinishPost_refuse` is R2, the merge's empty-stack route through `if.then492.i`:
the root-done test's refusing arm stores the offset and the copy follows.  Its
returned memory is `walkFinishMemRefuse` at `walkFinishMemOffset`, which is what
`stage2Boundary_of_refuse_offset` is proved at. -/

/-- **The refusal copy and the return, from a state at `if.then`.**  The copy's
premise set at the state's own memory, its jump to `if.end`, and the refusal φ's
literal zero: two steps to a return at `walkFinishMemRefuse` over the state's
memory.  `%alen`'s word is the argument (`hlog`), because `WalkInv.log_alen` is an
existential; `%len`'s is `hlogL`, its equality; and `%err`'s is the offset the
route's own store wrote (`hE`). -/
theorem walkFinishCopyTail {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State)
    (hpc : s.pc = "if.then")
    (hregs : WalkRegs G C s.env) (hptrs : WalkPtrs G C s.env)
    (henv : WalkFinalEnv G C s.env)
    (hlog : readBytes s.mem (C.stage.z + 48) 8 = some (wordBytes 8 C.alen))
    (hlogL : readBytes s.mem (C.stage.z + 8) 8 = some (wordBytes 8 C.evlen))
    (halen64 : C.alen < 2 ^ 64) (hevlen64 : C.evlen < 2 ^ 64)
    {E : BitVec 64} (hE : readBytes s.mem (C.stage.e + 8) 8 = some (natToBytes E.toNat 8)) :
    runFuel (stage2Calls stage2SubCalls) 2 stage2Body s =
      some (.ret (some (.int 64 0))
        (walkFinishMemRefuse G s.mem C.alen C.evlen E.toNat)) := by
  obtain ⟨he, hz, hs, hc, hnd, hnv, her⟩ := henv
  have hxj : lookupName s.env "%xj.i" = some (.ptr (G.next0 + 12)) :=
    hregs ("%xj.i", .ptr (G.next0 + 12)) (by simp [walkStaticRegs])
  have hrd : lookupName s.env "%root_done.i" = some (.ptr (G.next0 + 8)) :=
    hregs ("%root_done.i", .ptr (G.next0 + 8)) (by simp [walkStaticRegs])
  have halen : lookupName s.env "%alen" = some (.ptr (C.stage.z + 48)) :=
    hregs ("%alen", .ptr (C.stage.z + 48)) (by simp [walkStaticRegs])
  have hlen : lookupName s.env "%len" = some (.ptr (C.stage.z + 8)) :=
    hregs ("%len", .ptr (C.stage.z + 8)) (by simp [walkStaticRegs])
  obtain ⟨-, -, -, hsep, hsepE1, hsepE2⟩ := walkFinish_sep G C
  let A : BitVec 64 := BitVec.ofNat 64 C.alen
  let L : BitVec 64 := BitVec.ofNat 64 C.evlen
  have hAtoNat : A.toNat = C.alen := by
    dsimp only [A]
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt halen64]
  have hLtoNat : L.toNat = C.evlen := by
    dsimp only [L]
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hevlen64]
  have hA : readBytes s.mem (C.stage.z + 48) 8 = some (natToBytes A.toNat 8) := by
    rw [hAtoNat]; exact hlog
  have hL : readBytes s.mem (C.stage.z + 8) 8 = some (natToBytes L.toNat 8) := by
    rw [hLtoNat]; exact hlogL
  have hden : denoteCode (stage2Calls stage2SubCalls) walkIfThenBlock.instrs s =
      some (walkIfThenBlockState s.env G.ndst G.nev G.err C.stage.e A L E s) := by
    have h := walkIfThenBlock_denote_named (sub := stage2SubCalls) (env := s.env) (s := s)
      hxj hrd hptrs.2.2.2.2.1 hptrs.2.2.2.1 hc halen hnd hlen hnv he her
      hA hL hE hsep hsepE1 hsepE2
    rwa [stateAt_self] at h
  -- the copy's state at `if.end`, named
  have hpc₁ : (walkIfThenBlockState s.env G.ndst G.nev G.err C.stage.e A L E s).pc = s.pc :=
    walkFinishCopy_pc _ _ _ _ _ _ _ _ _
  have hstep₁ : step (stage2Calls stage2SubCalls) stage2Body s =
      .jump (walkFinishCopyState s.env G.ndst G.nev G.err C.stage.e A L E s.pc s) :=
    walkIfThen_step (sub := stage2SubCalls) s hpc hden hpc₁
  have hcells : lookupName (walkFinishCopyState s.env G.ndst G.nev G.err C.stage.e A L E s.pc s).env
        "%e" = lookupName s.env "%e" ∧
      lookupName (walkFinishCopyState s.env G.ndst G.nev G.err C.stage.e A L E s.pc s).env
        "%z" = lookupName s.env "%z" ∧
      lookupName (walkFinishCopyState s.env G.ndst G.nev G.err C.stage.e A L E s.pc s).env
        "%s" = lookupName s.env "%s" :=
    walkFinishCopy_cells s.env G.ndst G.nev G.err C.stage.e A L E s
  have hstep₂ : step (stage2Calls stage2SubCalls) stage2Body
      (walkFinishCopyState s.env G.ndst G.nev G.err C.stage.e A L E s.pc s) =
      .ret (some (.int 64 0))
        (stateAt (("%tobool.not151", .int 64 0) ::
          (walkFinishCopyState s.env G.ndst G.nev G.err C.stage.e A L E s.pc s).env)
          (walkFinishCopyState s.env G.ndst G.nev G.err C.stage.e A L E s.pc s)) :=
    walkIfEnd_step (p := s.pc) (v := 0) (bit := 0) (pe := C.stage.e) (pz := C.stage.z)
      (ps := C.stage.s) (walkFinishCopyState s.env G.ndst G.nev G.err C.stage.e A L E s.pc s)
      rfl (hcells.1.trans he) (hcells.2.1.trans hz) (hcells.2.2.trans hs) rfl
      (by rw [hpc]; exact walkIfEnd_refusal_phi) rfl
  have hmem : (stateAt (("%tobool.not151", .int 64 0) ::
        (walkFinishCopyState s.env G.ndst G.nev G.err C.stage.e A L E s.pc s).env)
        (walkFinishCopyState s.env G.ndst G.nev G.err C.stage.e A L E s.pc s)).mem =
      walkFinishMemRefuse G s.mem C.alen C.evlen E.toNat := by
    rw [stateAt_mem, walkFinishCopyState_mem, walkFinishCopy_mem, hAtoNat, hLtoNat]
    rfl
  simp only [runFuel, hstep₁, hstep₂, hmem]

/-- **R2: the refusal from the merge through `if.then492.i`.**  The merge's empty-stack
arm, the root-done test's refusing arm, the offset's store, the copy and the return:
four steps to `if.then` and the copy's two.  The returned memory is
`walkFinishMemRefuse` at `walkFinishMemOffset`, and the boundary is
`stage2Boundary_of_refuse_offset` there.

The three words the copy reads are the route's own: the log's arena cursor is the
argument `hlog`, its event cursor `WalkInv.log_len`'s, and the offset the store just
wrote.  `%4` is an argument for the reason the module header gives. -/
theorem walkFinishPost_refuse {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State)
    (hInv : WalkInv G C s)
    (hblk : C.block = "cleanup478.i")
    (henv : WalkFinalEnv G C s.env)
    (hlog : readBytes s.mem (C.stage.z + 48) 8 = some (wordBytes 8 C.alen))
    {p : String} {spv k2 : Nat} {spOp kOp : Operand}
    (hpre : s.pre = some p)
    (hsp : phiIncoming p cleanupSpIncoming = some spOp)
    (hspv : evalOperand s spOp = some (.int 32 (BitVec.ofNat 32 spv)))
    (hk : phiIncoming p cleanupKIncoming = some kOp)
    (hkv : evalOperand s kOp = some (.int 64 (BitVec.ofNat 64 k2)))
    {nepv : BitVec 64} (hnp : lookupName s.env "%nep" = some (.int 64 nepv))
    (hterm : k2 = nepv.toNat)
    (hsp0 : evalICmp .eq (BitVec.ofNat 32 spv) (BitVec.ofNat 32 0) = 1)
    {rv : BitVec 32} (hrootRead : readBytes s.mem (G.next0 + 8) 4 = some (natToBytes rv.toNat 4))
    (hroot0 : evalICmp .eq rv (BitVec.ofNat 32 0) = 1)
    (h4 : lookupName s.env "%4" = some (.int 64 (BitVec.ofNat 64 G.n))) :
    ∃ (q : Nat) (v : BitVec 64) (m : Mem), q + 2 ≤ 27 ∧
      runFuel (stage2Calls stage2SubCalls) (q + 2) stage2Body s =
        some (.ret (some (.int 64 v)) m) ∧
      stage2Boundary (walkFinishArgs G) m0 G.next0 m (.int 64 v) := by
  have hn64 : G.n < 2 ^ 64 := by
    have h := G.maxDoc
    simp only [stage2MaxDocument] at h
    omega
  have henv0 : WalkFinalEnv G C s.env := henv
  obtain ⟨he, hz, hs, hc, hnd, hnv, her⟩ := henv0
  -- the merge's step
  obtain ⟨s₁, hstep₁, -, hs₁⟩ :=
    walkFinishMerge_at (calls := stage2Calls stage2SubCalls) (G := G) (C := C) (s := s)
      hInv hblk (p := p) (spv := spv) (k2 := k2) (spOp := spOp) (kOp := kOp)
      (nepv := nepv) hpre hsp hspv hk hkv hnp hterm
  have hsp₁ : lookupName s₁.env "%sp.i.1" = some (.int 32 (BitVec.ofNat 32 spv)) := by
    rw [hs₁]
    simp only [cells]
    rw [lookupName_cons_ne (k := "%cmp.i") (n := "%sp.i.1") _ _ (by decide),
      lookupName_cons_ne (k := "%k.2.i") (n := "%sp.i.1") _ _ (by decide)]
    exact lookupName_cons_self _ _ _
  have hmem₁ : s₁.mem = s.mem := by rw [hs₁]
  -- the carriers at the merge's target
  have hregs₁ : WalkRegs G C s₁.env := by
    rw [hs₁]
    exact hInv.regs.cells_of _ (by
      intro n hn
      simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
        or_false] at hn
      rcases hn with rfl | rfl | rfl <;> decide)
  have hptrs₁ : WalkPtrs G C s₁.env := by
    rw [hs₁]
    simp only [cells]
    exact (((hInv.ptrs.bind (by decide) (by decide) (by decide) (by decide) (by decide)
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
  -- the depth's zero test, on its empty-stack arm
  let s₂ : State := exitS₂ s₁ spv
  have hstep₂ : step (stage2Calls stage2SubCalls) stage2Body s₁ = .jump s₂ := by
    rw [walkIfThen485Step (calls := stage2Calls stage2SubCalls) s₁ (by rw [hs₁])
      (spv := spv) hsp₁]
    simp only [s₂, exitS₂]
    rw [show (if evalICmp .eq (BitVec.ofNat 32 spv) (BitVec.ofNat 32 0) = 1
      then "if.end490.i" else "if.then488.i") = "if.end490.i" from ite_eq_left hsp0]
  have hmem₂ : s₂.mem = s.mem := by
    dsimp only [s₂, exitS₂, State.bind]
    rw [hmem₁]
  -- the carriers at the depth's test
  have hregs₂ : WalkRegs G C s₂.env := by
    dsimp only [s₂, exitS₂]
    exact hregs₁.bind (by decide)
  have hptrs₂ : WalkPtrs G C s₂.env := by
    dsimp only [s₂, exitS₂]
    exact hptrs₁.bind (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have henv₂ : WalkFinalEnv G C s₂.env := by
    dsimp only [s₂, exitS₂]
    exact henv₁.bind (by simp [walkFinalNames])
  -- the root-done test, on its refusing arm
  let s₃ : State := exitS₃r s₂ rv
  have hstep₃ : step (stage2Calls stage2SubCalls) stage2Body s₂ = .jump s₃ := by
    rw [walkIfEnd490Step (calls := stage2Calls stage2SubCalls) s₂ rfl (v := rv)
      ((exitS₂_rd (s := s₁) (spv := spv)).trans
        (hregs₁ ("%root_done.i", .ptr (G.next0 + 8)) (by simp [walkStaticRegs])))
      (by rw [hmem₂]; exact hrootRead)]
    simp only [s₃, exitS₃r]
    rw [show (if evalICmp .eq rv (BitVec.ofNat 32 0) = 1 then "if.then492.i"
      else "s2_walk.exit") = "if.then492.i" from ite_eq_left hroot0]
  have hmem₃ : s₃.mem = s.mem := by
    dsimp only [s₃, exitS₃r, State.bind]
    rw [hmem₂]
  have hregs₃ : WalkRegs G C s₃.env := by
    dsimp only [s₃, exitS₃r, State.bind]
    exact (hregs₂.bind (by decide)).bind (by decide)
  have hptrs₃ : WalkPtrs G C s₃.env := by
    dsimp only [s₃, exitS₃r, State.bind]
    exact (hptrs₂.bind (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)).bind (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)
  have henv₃ : WalkFinalEnv G C s₃.env := by
    dsimp only [s₃, exitS₃r, State.bind]
    exact (henv₂.bind (by simp [walkFinalNames])).bind (by simp [walkFinalNames])
  -- the offset's store
  let s₄ : State := exitS₅ s₃ C.stage.e G.n
  have he₁ : lookupName s₁.env "%e" = some (.ptr C.stage.e) := henv₁.1
  have h4₁ : lookupName s₁.env "%4" = some (.int 64 (BitVec.ofNat 64 G.n)) := by
    rw [hs₁]
    simp only [cells]
    rw [lookupName_cons_ne (k := "%cmp.i") (n := "%4") _ _ (by decide),
      lookupName_cons_ne (k := "%k.2.i") (n := "%4") _ _ (by decide),
      lookupName_cons_ne (k := "%sp.i.1") (n := "%4") _ _ (by decide)]
    exact h4
  have he₃ : lookupName s₃.env "%e" = some (.ptr C.stage.e) :=
    (exitS₃r_env' (n := "%e") (by decide) (by decide)).trans
      ((exitS₂_env' (n := "%e") (by decide)).trans he₁)
  have h4₃ : lookupName s₃.env "%4" = some (.int 64 (BitVec.ofNat 64 G.n)) :=
    (exitS₃r_env' (n := "%4") (by decide) (by decide)).trans
      ((exitS₂_env' (n := "%4") (by decide)).trans h4₁)
  have hstep₄ : step (stage2Calls stage2SubCalls) stage2Body s₃ = .jump s₄ :=
    walkIfThen492Step (calls := stage2Calls stage2SubCalls) s₃ rfl he₃ h4₃ hn64
  have hmem₄ : s₄.mem = walkFinishMemOffset C.stage.e G.n s.mem := by
    dsimp only [s₄, exitS₅, walkFinishMemOffset]
    rw [hmem₃]
  have hregs₄ : WalkRegs G C s₄.env := by
    dsimp only [s₄, exitS₅]
    exact hregs₃.bind (by decide)
  have hptrs₄ : WalkPtrs G C s₄.env := by
    dsimp only [s₄, exitS₅]
    exact hptrs₃.bind (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have henv₄ : WalkFinalEnv G C s₄.env := by
    dsimp only [s₄, exitS₅]
    exact henv₃.bind (by simp [walkFinalNames])
  -- the copy's three words, at the offset store's memory
  have hlogA₄ : readBytes s₄.mem (C.stage.z + 48) 8 = some (wordBytes 8 C.alen) := by
    rw [hmem₄, walkFinishMemOffset]
    rw [walkReadBytes_writeBytes_outside (m := s.mem) (v := wordBytes 8 G.n)
      (start := C.stage.e + 8) (addr := C.stage.z + 48) (n := 8) (by
        rw [wordBytes, natToBytes_length]
        exact (walkFinish_log_sep G C).1)]
    exact hlog
  have hlogL₄ : readBytes s₄.mem (C.stage.z + 8) 8 = some (wordBytes 8 C.evlen) := by
    rw [hmem₄, walkFinishMemOffset]
    rw [walkReadBytes_writeBytes_outside (m := s.mem) (v := wordBytes 8 G.n)
      (start := C.stage.e + 8) (addr := C.stage.z + 8) (n := 8) (by
        rw [wordBytes, natToBytes_length]
        exact (walkFinish_log_sep G C).2)]
    exact hInv.log_len
  have hE₄ : readBytes s₄.mem (C.stage.e + 8) 8 =
      some (natToBytes (BitVec.ofNat 64 G.n).toNat 8) := by
    rw [hmem₄, walkFinishMemOffset_read]
    rw [show (BitVec.ofNat 64 G.n).toNat = G.n from by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn64]]
    rfl
  refine ⟨4, 0, walkFinishMemRefuse G s₄.mem C.alen C.evlen (BitVec.ofNat 64 G.n).toNat,
    by omega, ?_, ?_⟩
  · rw [show (4 + 2 : Nat) = 1 + (1 + (1 + (1 + 2))) from by omega]
    rw [runFuel_jump_prefix (f := stage2Body) hstep₁ (1 + (1 + (1 + 2)))]
    rw [runFuel_jump_prefix (f := stage2Body) hstep₂ (1 + (1 + 2))]
    rw [runFuel_jump_prefix (f := stage2Body) hstep₃ (1 + 2)]
    rw [runFuel_jump_prefix (f := stage2Body) hstep₄ 2]
    exact walkFinishCopyTail G C s₄ rfl hregs₄ hptrs₄ henv₄ hlogA₄ hlogL₄
      (by
        have h := G.arenaRoom
        have hcap := G.dstcapLt
        have hle := hInv.alen_le
        omega)
      (by
        have h := G.evRoom
        have hcap := G.evcapLt
        have hle : C.evlen ≤ G.evcap := le_trans hInv.evlen_le G.evRoom
        omega)
      hE₄
  · rw [hmem₄]
    rw [show (BitVec.ofNat 64 G.n).toNat = G.n from by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn64]]
    exact stage2Boundary_of_refuse_offset G C hInv (Nat.le_refl G.n)

/-- **R3: the refusal from the merge through `if.then488.i`.**  The depth's non-zero arm
takes the refusal copy without the root-done test, so the route is one step shorter than
R2's: the merge, the depth's test, the offset's store and the copy's two.  The returned
memory is the same shape — `walkFinishMemRefuse` at the offset store — and the boundary
is again `stage2Boundary_of_refuse_offset`'s.

The offset's store is at the same address on both routes (`%e + 8`), which is why the
copy's three reads are this route's in the same form as R2's: only the register the
block names (`%off1.i.i115` against `%off1.i.i117`) differs. -/
theorem walkFinishPost_refuse488 {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State)
    (hInv : WalkInv G C s)
    (hblk : C.block = "cleanup478.i")
    (henv : WalkFinalEnv G C s.env)
    (hlog : readBytes s.mem (C.stage.z + 48) 8 = some (wordBytes 8 C.alen))
    {p : String} {spv k2 : Nat} {spOp kOp : Operand}
    (hpre : s.pre = some p)
    (hsp : phiIncoming p cleanupSpIncoming = some spOp)
    (hspv : evalOperand s spOp = some (.int 32 (BitVec.ofNat 32 spv)))
    (hk : phiIncoming p cleanupKIncoming = some kOp)
    (hkv : evalOperand s kOp = some (.int 64 (BitVec.ofNat 64 k2)))
    {nepv : BitVec 64} (hnp : lookupName s.env "%nep" = some (.int 64 nepv))
    (hterm : k2 = nepv.toNat)
    (hspn : evalICmp .eq (BitVec.ofNat 32 spv) (BitVec.ofNat 32 0) = 0)
    (h4 : lookupName s.env "%4" = some (.int 64 (BitVec.ofNat 64 G.n))) :
    ∃ (q : Nat) (v : BitVec 64) (m : Mem), q + 2 ≤ 27 ∧
      runFuel (stage2Calls stage2SubCalls) (q + 2) stage2Body s =
        some (.ret (some (.int 64 v)) m) ∧
      stage2Boundary (walkFinishArgs G) m0 G.next0 m (.int 64 v) := by
  have hn64 : G.n < 2 ^ 64 := by
    have h := G.maxDoc
    simp only [stage2MaxDocument] at h
    omega
  have henv0 : WalkFinalEnv G C s.env := henv
  obtain ⟨he, hz, hs, hc, hnd, hnv, her⟩ := henv0
  -- the merge's step
  obtain ⟨s₁, hstep₁, -, hs₁⟩ :=
    walkFinishMerge_at (calls := stage2Calls stage2SubCalls) (G := G) (C := C) (s := s)
      hInv hblk (p := p) (spv := spv) (k2 := k2) (spOp := spOp) (kOp := kOp)
      (nepv := nepv) hpre hsp hspv hk hkv hnp hterm
  have hsp₁ : lookupName s₁.env "%sp.i.1" = some (.int 32 (BitVec.ofNat 32 spv)) := by
    rw [hs₁]
    simp only [cells]
    rw [lookupName_cons_ne (k := "%cmp.i") (n := "%sp.i.1") _ _ (by decide),
      lookupName_cons_ne (k := "%k.2.i") (n := "%sp.i.1") _ _ (by decide)]
    exact lookupName_cons_self _ _ _
  have hmem₁ : s₁.mem = s.mem := by rw [hs₁]
  have hregs₁ : WalkRegs G C s₁.env := by
    rw [hs₁]
    exact hInv.regs.cells_of _ (by
      intro n hn
      simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
        or_false] at hn
      rcases hn with rfl | rfl | rfl <;> decide)
  have hptrs₁ : WalkPtrs G C s₁.env := by
    rw [hs₁]
    simp only [cells]
    exact (((hInv.ptrs.bind (by decide) (by decide) (by decide) (by decide) (by decide)
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
  have h4₁ : lookupName s₁.env "%4" = some (.int 64 (BitVec.ofNat 64 G.n)) := by
    rw [hs₁]
    simp only [cells]
    rw [lookupName_cons_ne (k := "%cmp.i") (n := "%4") _ _ (by decide),
      lookupName_cons_ne (k := "%k.2.i") (n := "%4") _ _ (by decide),
      lookupName_cons_ne (k := "%sp.i.1") (n := "%4") _ _ (by decide)]
    exact h4
  -- the depth's zero test, on its non-empty-stack arm
  let s₂ : State := exitS₂r s₁ spv
  have hstep₂ : step (stage2Calls stage2SubCalls) stage2Body s₁ = .jump s₂ := by
    rw [walkIfThen485Step (calls := stage2Calls stage2SubCalls) s₁ (by rw [hs₁])
      (spv := spv) hsp₁]
    simp only [s₂, exitS₂r]
    rw [show (if evalICmp .eq (BitVec.ofNat 32 spv) (BitVec.ofNat 32 0) = 1
      then "if.end490.i" else "if.then488.i") = "if.then488.i" from
        ite_eq_right (by rw [hspn]; decide)]
  have hmem₂ : s₂.mem = s.mem := by
    dsimp only [s₂, exitS₂r, State.bind]
    rw [hmem₁]
  have hregs₂ : WalkRegs G C s₂.env := by
    dsimp only [s₂, exitS₂r]
    exact hregs₁.bind (by decide)
  have hptrs₂ : WalkPtrs G C s₂.env := by
    dsimp only [s₂, exitS₂r]
    exact hptrs₁.bind (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have henv₂ : WalkFinalEnv G C s₂.env := by
    dsimp only [s₂, exitS₂r]
    exact henv₁.bind (by simp [walkFinalNames])
  -- the offset's store
  let s₃ : State := exitS₅r s₂ C.stage.e G.n
  have he₂ : lookupName s₂.env "%e" = some (.ptr C.stage.e) :=
    (exitS₂r_env' (n := "%e") (by decide)).trans henv₁.1
  have h4₂ : lookupName s₂.env "%4" = some (.int 64 (BitVec.ofNat 64 G.n)) :=
    (exitS₂r_env' (n := "%4") (by decide)).trans h4₁
  have hstep₃ : step (stage2Calls stage2SubCalls) stage2Body s₂ = .jump s₃ :=
    walkIfThen488Step (calls := stage2Calls stage2SubCalls) s₂ rfl he₂ h4₂ hn64
  have hmem₃ : s₃.mem = walkFinishMemOffset C.stage.e G.n s.mem := by
    dsimp only [s₃, exitS₅r, walkFinishMemOffset]
    rw [hmem₂]
  have hregs₃ : WalkRegs G C s₃.env := by
    dsimp only [s₃, exitS₅r]
    exact hregs₂.bind (by decide)
  have hptrs₃ : WalkPtrs G C s₃.env := by
    dsimp only [s₃, exitS₅r]
    exact hptrs₂.bind (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have henv₃ : WalkFinalEnv G C s₃.env := by
    dsimp only [s₃, exitS₅r]
    exact henv₂.bind (by simp [walkFinalNames])
  -- the copy's three words, at the offset store's memory
  have hlogA₃ : readBytes s₃.mem (C.stage.z + 48) 8 = some (wordBytes 8 C.alen) := by
    rw [hmem₃, walkFinishMemOffset]
    rw [walkReadBytes_writeBytes_outside (m := s.mem) (v := wordBytes 8 G.n)
      (start := C.stage.e + 8) (addr := C.stage.z + 48) (n := 8) (by
        rw [wordBytes, natToBytes_length]
        exact (walkFinish_log_sep G C).1)]
    exact hlog
  have hlogL₃ : readBytes s₃.mem (C.stage.z + 8) 8 = some (wordBytes 8 C.evlen) := by
    rw [hmem₃, walkFinishMemOffset]
    rw [walkReadBytes_writeBytes_outside (m := s.mem) (v := wordBytes 8 G.n)
      (start := C.stage.e + 8) (addr := C.stage.z + 8) (n := 8) (by
        rw [wordBytes, natToBytes_length]
        exact (walkFinish_log_sep G C).2)]
    exact hInv.log_len
  have hE₃ : readBytes s₃.mem (C.stage.e + 8) 8 =
      some (natToBytes (BitVec.ofNat 64 G.n).toNat 8) := by
    rw [hmem₃, walkFinishMemOffset_read]
    rw [show (BitVec.ofNat 64 G.n).toNat = G.n from by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn64]]
    rfl
  refine ⟨3, 0, walkFinishMemRefuse G s₃.mem C.alen C.evlen (BitVec.ofNat 64 G.n).toNat,
    by omega, ?_, ?_⟩
  · rw [show (3 + 2 : Nat) = 1 + (1 + (1 + 2)) from by omega]
    rw [runFuel_jump_prefix (f := stage2Body) hstep₁ (1 + (1 + 2))]
    rw [runFuel_jump_prefix (f := stage2Body) hstep₂ (1 + 2)]
    rw [runFuel_jump_prefix (f := stage2Body) hstep₃ 2]
    exact walkFinishCopyTail G C s₃ rfl hregs₃ hptrs₃ henv₃ hlogA₃ hlogL₃
      (by
        have h := G.arenaRoom
        have hcap := G.dstcapLt
        have hle := hInv.alen_le
        omega)
      (by
        have h := G.evRoom
        have hcap := G.evcapLt
        have hle : C.evlen ≤ G.evcap := le_trans hInv.evlen_le G.evRoom
        omega)
      hE₃
  · rw [hmem₃]
    rw [show (BitVec.ofNat 64 G.n).toNat = G.n from by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn64]]
    exact stage2Boundary_of_refuse_offset G C hInv (Nat.le_refl G.n)

/-- **R0: the refusal already at the copy.**  A segment that ended at `if.then` — the
dispatch's refusal outcome — leaves the state the copy starts from, so the route is the
copy's two steps alone (`q = 0`).  The refusal word is the *previous* link's store, which
no clause carries: `WalkInv` names the offset the carry holds (`eoff_le`) but not the
bytes at `%e + 8`, and `WalkSegment` keeps no memory.  Its producer is therefore the
segment that made the store (`WalkRefuseSegment`'s `word`) and `hword` is that field
projected: the copy loads whatever word the store left, and the boundary asks of it only
that it lie inside the document (`k ≤ G.n`), which is `stage2Boundary`'s refusal clause. -/
theorem walkFinishPost_copy {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State)
    (hInv : WalkInv G C s)
    (hblk : C.block = "if.then")
    (henv : WalkFinalEnv G C s.env)
    (hlog : readBytes s.mem (C.stage.z + 48) 8 = some (wordBytes 8 C.alen))
    (hword : ∃ k, k ≤ G.n ∧ readBytes s.mem (C.stage.e + 8) 8 = some (wordBytes 8 k)) :
    ∃ (q : Nat) (v : BitVec 64) (m : Mem), q + 2 ≤ 27 ∧
      runFuel (stage2Calls stage2SubCalls) (q + 2) stage2Body s =
        some (.ret (some (.int 64 v)) m) ∧
      stage2Boundary (walkFinishArgs G) m0 G.next0 m (.int 64 v) := by
  obtain ⟨k, hk, hword⟩ := hword
  have hn64 : G.n < 2 ^ 64 := by
    have h := G.maxDoc
    simp only [stage2MaxDocument] at h
    omega
  have hk64 : k < 2 ^ 64 := by omega
  have hktoNat : (BitVec.ofNat 64 k).toNat = k := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk64]
  have hE : readBytes s.mem (C.stage.e + 8) 8 =
      some (natToBytes (BitVec.ofNat 64 k).toNat 8) := by
    rw [hktoNat]
    exact hword
  refine ⟨0, 0, walkFinishMemRefuse G s.mem C.alen C.evlen k, by omega, ?_,
    stage2Boundary_of_refuse G C hInv hk⟩
  have h := walkFinishCopyTail G C s (hpc := hInv.pc_eq.trans hblk) hInv.regs hInv.ptrs henv hlog
    hInv.log_len
    (by
      have h := G.arenaRoom
      have hcap := G.dstcapLt
      have hle := hInv.alen_le
      omega)
    (by
      have h := G.evRoom
      have hcap := G.evcapLt
      have hle : C.evlen ≤ G.evcap := le_trans hInv.evlen_le G.evRoom
      omega)
    hE
  simpa only [Nat.zero_add, hktoNat] using h

/-! ### The words the routes are supplied

`WalkInv` bounds the finalisation's reads but does not fix them, and it carries none of
the finalisation blocks' address registers.  Each bundle below is one route's supply, and
each field names its producer in the census (`JsonStage2WalkPremisesOfStaging`): the log's
arena word is the write-back block's, and the refusal word is the refusal segment's
(`WalkRefuseSegment`), which carries it from the store to the copy. -/

/-- **The merge's words: the log's arena word at the carry's cursor.**  One bundle, so a
route takes one hypothesis and the three routes that share the merge's state share its
supply.

**This word is false at an escaping input, and its correct producer is a design change.**
The field says the slot holds the carry's cursor; `JsonStage2WalkArenaWord` proves the
equality fails whenever the decoder's output is shorter than the document extent the
reserve charged — `if.else285.i` stores `%z + %outn.i` while `WalkInv.log_alen` relates
the two numbers only by `≤` — so an escaping string leaves `slot < C.alen` at every later
loop head (`not_arenaWord_of_lt`), and no lemma about the walk can produce the field.  It
is supplied, and what would make it true is a change to the statement this finalisation
reads — the record's cursor reported from the slot's own word (`log_alen`'s witness)
rather than from the carry's `C.alen` — not a proof.  Which of the two the post should
report is open; the boundary's clauses are stated at `C.alen` here and this bundle keeps
them there.

The rest of what the routes read is the invariant's, not this bundle's: the seven
finalisation registers are `WalkFinalEnv` at `hInv.regs` (`walkFinalEnv_of_regs`, all seven
names are `walkStaticRegs` entries), `%4` is `hInv.regs`' cell, and the root-done slot's
word is `hInv.root_slot` read as four bytes (`walkRootWord_of_hasBytes`). -/
structure WalkMergeWords {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State) : Prop where
  /-- The log's arena word is the carry's cursor.  **False at an escaping input**: the
  store's value is the decoder's output length, and `WalkInv.log_alen` only bounds the
  slot by the carry.  Supplied rather than produced; see the structure's note. -/
  log : readBytes s.mem (C.stage.z + 48) 8 = some (wordBytes 8 C.alen)

/-- **The refusal copy's words: the log's arena word at the carry's cursor.**  The
registers are `WalkFinalEnv` at `hInv.regs`, as in the merge's bundle, and the copy's
`%off` word is not here at all: it is the refusal segment's own store, carried by
`WalkRefuseSegment` from the branch that wrote it (`JsonStage2WalkTraverse`), so the copy
reads it from the segment rather than from a supply.

The log's word is the same false-at-an-escaping-input statement as the merge's, and it is
marked there. -/
structure WalkRefuseWords {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State) : Prop where
  /-- The log's arena word is the carry's cursor.  **False at an escaping input**: the
  store's value is the decoder's output length, and `WalkInv.log_alen` only bounds the
  slot by the carry.  Supplied rather than produced; see `WalkMergeWords`'s note. -/
  log : readBytes s.mem (C.stage.z + 48) 8 = some (wordBytes 8 C.alen)

/-- **A present four-byte slot is a word.**  `WalkInv.root_slot` is presence over
`G.next0 + 8`'s four bytes; the root-done test reads them as an `i32`, so the two are the
same statement once the bytes are named — `natToBytes_bytesToNat` at the read's own length
(`JsonEntrySteps`), with the value below `2 ^ 32` because four bytes are. -/
theorem walkRootWord_of_hasBytes {m : Mem} {a : Nat} {vs : List UInt8}
    (h : readBytes m a 4 = some vs) :
    ∃ rv : BitVec 32, readBytes m a 4 = some (natToBytes rv.toNat 4) := by
  have hlen : vs.length = 4 := walkReadBytes_length h
  refine ⟨BitVec.ofNat 32 (bytesToNat vs), ?_⟩
  rw [walkToNat_ofNat32 (bytesToNat_lt_32 hlen), ← hlen,
    JsonEntrySteps.natToBytes_bytesToNat, hlen]
  exact h

/-- **The finalisation's registers are the static carrier's.**  Each of the seven names
`WalkFinalEnv` binds is an entry of `walkStaticRegs`, so `WalkInv.regs` answers all seven
and no route needs a separate supply. -/
theorem walkFinalEnv_of_regs {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {env : Env}
    (h : WalkRegs G C env) : WalkFinalEnv G C env :=
  ⟨h ("%e", .ptr C.stage.e) (by simp [walkStaticRegs]),
   h ("%z", .ptr C.stage.z) (by simp [walkStaticRegs]),
   h ("%s", .ptr C.stage.s) (by simp [walkStaticRegs]),
   h ("%c.i", .ptr C.stage.c) (by simp [walkStaticRegs]),
   h ("%ndst", .ptr G.ndst) (by simp [walkStaticRegs]),
   h ("%nev", .ptr G.nev) (by simp [walkStaticRegs]),
   h ("%err", .ptr G.err) (by simp [walkStaticRegs])⟩

/-- **`%4`'s cell is the carrier's.**  The entry count's word is an entry of
`walkStaticRegs` (`%4`, `BitVec.ofNat 64 G.n`), so the merge's routes read it from the
invariant rather than from the bundle. -/
theorem walkMerge4_of_regs {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {env : Env}
    (h : WalkRegs G C env) :
    lookupName env "%4" = some (.int 64 (BitVec.ofNat 64 G.n)) :=
  h ("%4", .int 64 (BitVec.ofNat 64 G.n)) (by simp [walkStaticRegs])

/-- **The merge's post: one of the three routes, decided by the merge's own tests.**
The depth's zero test selects the exit's two tails and the root-done test selects the
refusal's, so the merge's three routes are one statement — `WalkTargetPost` — and the
case split is here rather than in the loop's step.  Nothing else about the finalisation
is assumed: the three runs are the routes' own. -/
theorem walkFinishPost_merge {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State)
    (hInv : WalkInv G C s)
    (hblk : C.block = "cleanup478.i")
    {p : String} {spv k2 : Nat} {spOp kOp : Operand}
    (hpre : s.pre = some p)
    (hsp : phiIncoming p cleanupSpIncoming = some spOp)
    (hspv : evalOperand s spOp = some (.int 32 (BitVec.ofNat 32 spv)))
    (hk : phiIncoming p cleanupKIncoming = some kOp)
    (hkv : evalOperand s kOp = some (.int 64 (BitVec.ofNat 64 k2)))
    {nepv : BitVec 64} (hnp : lookupName s.env "%nep" = some (.int 64 nepv))
    (hterm : k2 = nepv.toNat)
    (hw : WalkMergeWords G C s) :
    WalkTargetPost (stage2Calls stage2SubCalls) G C s := by
  obtain ⟨vs, hvs⟩ := hInv.root_slot
  obtain ⟨rv, hroot⟩ := walkRootWord_of_hasBytes hvs
  by_cases hsp0 : evalICmp .eq (BitVec.ofNat 32 spv) (BitVec.ofNat 32 0) = 1
  · by_cases hroot0 : evalICmp .eq rv (BitVec.ofNat 32 0) = 0
    · exact walkFinishPost_accept G C s hInv hblk hInv.regs hInv.ptrs
        (walkFinalEnv_of_regs hInv.regs) hw.log hpre
        hsp hspv hk hkv hnp hterm hsp0 hroot hroot0
    · exact walkFinishPost_refuse G C s hInv hblk (walkFinalEnv_of_regs hInv.regs) hw.log hpre
        hsp hspv hk hkv
        hnp hterm hsp0 hroot (by
          rcases walkBitVec1_zero_or_one (evalICmp .eq rv (BitVec.ofNat 32 0)) with h | h
          · exact absurd h hroot0
          · exact h) (walkMerge4_of_regs hInv.regs)
  · exact walkFinishPost_refuse488 G C s hInv hblk (walkFinalEnv_of_regs hInv.regs) hw.log
      hpre hsp hspv hk hkv
      hnp hterm (by
        rcases walkBitVec1_zero_or_one
          (evalICmp .eq (BitVec.ofNat 32 spv) (BitVec.ofNat 32 0)) with h | h
        · exact h
        · exact absurd h hsp0) (walkMerge4_of_regs hInv.regs)

/-- **The refusal copy's post, from the words.**  `WalkRefuseWords` at a state at
`if.then` supplies the log's word, and the copy's `%off` word is the refusal segment's
own (`WalkRefuseSegment`'s `word`), which is `hword` here.  `WalkLoopEnd.refuse`
(`JsonStage2WalkPremisesOfStaging`) is its consumer, at every state the dispatch's
refusal arm reaches. -/
theorem walkFinishPost_refuseOfWords {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G)
    (s : State) (hInv : WalkInv G C s)
    (hblk : C.block = "if.then")
    (hw : WalkRefuseWords G C s)
    (hword : ∃ k, k ≤ G.n ∧ readBytes s.mem (C.stage.e + 8) 8 = some (wordBytes 8 k)) :
    WalkTargetPost (stage2Calls stage2SubCalls) G C s :=
  walkFinishPost_copy G C s hInv hblk (walkFinalEnv_of_regs hInv.regs) hw.log hword

end WalkScope
end LeanLLVM.Refinement

/-! ### Axiom footprints -/

/-- info: 'LeanLLVM.Refinement.WalkScope.stage2Boundary_of_accept' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.WalkScope.stage2Boundary_of_accept

/-- info: 'LeanLLVM.Refinement.WalkScope.stage2Boundary_of_refuse' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.WalkScope.stage2Boundary_of_refuse

/-- info: 'LeanLLVM.Refinement.WalkScope.stage2Boundary_of_refuse_offset' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.WalkScope.stage2Boundary_of_refuse_offset

/-- info: 'LeanLLVM.Refinement.WalkScope.walkFinishCopyTail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.WalkScope.walkFinishCopyTail

/-- info: 'LeanLLVM.Refinement.WalkScope.walkFinishPost_accept' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.WalkScope.walkFinishPost_accept

/-- info: 'LeanLLVM.Refinement.WalkScope.walkFinishPost_refuse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.WalkScope.walkFinishPost_refuse

/-- info: 'LeanLLVM.Refinement.WalkScope.walkFinishPost_refuse488' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.WalkScope.walkFinishPost_refuse488

/-- info: 'LeanLLVM.Refinement.WalkScope.walkFinishPost_copy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.WalkScope.walkFinishPost_copy

/-- info: 'LeanLLVM.Refinement.WalkScope.walkFinishPost_merge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.WalkScope.walkFinishPost_merge

/-- info: 'LeanLLVM.Refinement.WalkScope.walkFinishPost_refuseOfWords' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.WalkScope.walkFinishPost_refuseOfWords

/-- info: 'LeanLLVM.Refinement.WalkScope.walkFinalEnv_of_regs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.WalkScope.walkFinalEnv_of_regs

/-- info: 'LeanLLVM.Refinement.WalkScope.walkMerge4_of_regs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.WalkScope.walkMerge4_of_regs
