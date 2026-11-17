/-
# The empty entry stream's post: its run, its returned memory, and the boundary

`walkFlushAt_of_staging` (`JsonStage2WalkPremisesOfStaging`) completes the
empty-stream arm's run but states only that *some* value is returned from *some*
memory: `WalkFlushAt` existentially quantifies the outcome's value, and
`WalkPremises` quantifies it again.  Nothing in the layer states the arm's
outcome at its own type, the words the arm leaves in the record's three slots,
the frame the arm keeps, or the six facts `stage2Boundary_of_parts` reads.  This
module supplies them, at the staging alone.

## The arm, and what it writes

The arm is four control steps at the staged memory: the entry block's zero arm,
the flush block, the refusal copy, and the return.  Its writes are

* the entry run's own (`walkEntryMemAt`: `s2_init`'s record, the log's fields,
  the two cursor loads, the cursor record's memset and five stores, and the
  four stack slots at the allocator's cursor), then
* the flush block's store of the document's length at `%e + 8`
  (`wordBytes 8 G.n`, the refusal offset), then
* the refusal copy's three stores into the record's slots: `%alen` (`ndst0`) at
  `%ndst`, `%len` (`nev0`) at `%nev`, and the offset just stored at `%err`.

`walkFlushMemAt` names that memory, so the arm's return, the three slot words,
the frame and the boundary are all stated at one term rather than at an
existential.

## The returned verdict

`if.end`'s `phi` takes the literal zero on the `if.then` edge
(`walkIfEnd_refusal_phi`, by `rfl`), so the returned word is `(0 : BitVec 64)`
and not a `Value` whose shape is guessed.  `walkFlushRun_of_staging` states the
run at that word and at `walkFlushMemAt`.

## The boundary, and the route it takes

`stage2Boundary_of_parts` is **not** applicable to this arm, and the reason is a
statement-level one rather than a missing lemma: its `walkFrame` is
`Stage2Run`'s, whose list omits the three record slots (`%ndst`, `%nev`, `%err`)
because the emitted loop never writes them — the wrapper's four statements do.
The flattening this layer runs puts those stores in the finalisation blocks, so
the flush arm's own run writes all three, and `stage2Boundary_of_parts`'s
`herrWalk` (the walk left the refusal slot as the caller staged it) is *false* of
it.  The arm therefore reaches the boundary the other way `stage2Boundary`
admits: the six facts at the returned memory (`stage2Boundary_of_flush`), not an
equality with `stage2Report`.  No equality holds either — the flush block's store
at `%e + 8` is a write `stage2Report` never performs, and the entry run's writes
to the log and the cursor record stay in memory — so the returned memory is
genuinely not `stage2Report m0 …`, and that is a fact about the record rather
than about this proof.  What the record *does* constrain is the report: the
cursor words, the refusal word's boundedness, the frame and presence.  Those are
what this module proves, and they are what `stage2Boundary` reads.
-/

import LeanLLVM.Refinement.JsonStage2WalkPremisesOfStaging

set_option autoImplicit false

namespace LeanLLVM.Refinement
open LeanLLVM
open LeanLLVM.Refinement.BlockEval
open LeanLLVM.Refinement.JsonStage2IR

namespace WalkScope

/-! ### The returned memory -/

/-- **The flush arm's returning memory.**  The entry run's memory, the flush
block's store of the document's length at `%e + 8` (the refusal offset the number
path's flat store leaves there), and the refusal copy's three stores into the
record's slots: `ndst0` at `%ndst`, `nev0` at `%nev`, and the offset at `%err`.
The copy's order is the block's (`%ndst`, `%nev`, `%err`), and the three slots are
pairwise separate by the staging, so the order does not matter to any read this
module states. -/
def walkFlushMemAt {m0 : Mem} (G : WalkGeom m0) (S : WalkStage G) : Mem :=
  writeBytes
    (writeBytes
      (writeBytes
        (writeBytes (walkEntryMemAt G S) (S.e + 8) (wordBytes 8 G.n))
        G.ndst (wordBytes 8 G.ndst0))
      G.nev (wordBytes 8 G.nev0))
    G.err (wordBytes 8 G.n)

/-- **The state the refusal copy's block leaves**: `if.then`'s jump target, the
copy's state with the block and its predecessor.  Named so the arm's last two
steps, and the memory the return carries, can be stated at one term. -/
def walkFlushPostCopyState (env : Env) (nd nv err e : Nat) (A L E : BitVec 64)
    (p : String) (s : State) : State :=
  { walkIfThenBlockState env nd nv err e A L E s with pc := "if.end", pre := some p }

/-- The post-copy state's memory is the copy's. -/
theorem walkFlushPostCopyState_mem (env : Env) (nd nv err e : Nat) (A L E : BitVec 64)
    (p : String) (s : State) :
    (walkFlushPostCopyState env nd nv err e A L E p s).mem =
      (walkIfThenBlockState env nd nv err e A L E s).mem := by
  simp only [walkFlushPostCopyState]

/-- The post-copy state's three pointer cells: the copy binds `%51`, `%52`, `%53`
and `%off`, so the refusal record, the log and the state record still read as
they did. -/
theorem walkFlushPostCopyState_cells (env : Env) (nd nv err e : Nat)
    (A L E : BitVec 64) (p : String) (s : State) :
    lookupName (walkFlushPostCopyState env nd nv err e A L E p s).env "%e"
        = lookupName env "%e" ∧
    lookupName (walkFlushPostCopyState env nd nv err e A L E p s).env "%z"
        = lookupName env "%z" ∧
    lookupName (walkFlushPostCopyState env nd nv err e A L E p s).env "%s"
        = lookupName env "%s" := by
  refine ⟨?_, ?_, ?_⟩ <;>
    simp [walkFlushPostCopyState, walkIfThenBlockState, stateAt, cells, lookupName_cons_ne]

/-- **The refusal copy's memory, at a state's own memory.**  The three stores in
the block's order, as `walkIfThenBlockState` performs them.  Stated by rewriting
the named state's three layers rather than by `rfl`: at a term whose memory is
the three-deep write, `rfl` unfolds the writes at every position and exceeds the
heartbeat budget, while the three projection rewrites are instant. -/
theorem walkIfThenBlockState_mem (env : Env) (nd nv err e : Nat) (A L E : BitVec 64)
    (s : State) :
    (walkIfThenBlockState env nd nv err e A L E s).mem =
      writeBytes
        (writeBytes (writeBytes s.mem nd (wordBytes 8 A.toNat)) nv
          (wordBytes 8 L.toNat))
        err (wordBytes 8 E.toNat) := by
  rw [walkIfThenBlockState, stateAt_mem, walkSetMem_mem]

/-- **The copy at the flush's own memory.**  The three words the copy writes are
the staging's numbers — `ndst0`, `nev0` and the document's length the flush block
stored — so the state the copy leaves carries `walkFlushMemAt`. -/
theorem walkFlushCopy_mem {m0 : Mem} (G : WalkGeom m0) (S : WalkStage G)
    (hndst0 : G.ndst0 < 2 ^ 64) (hnev0 : G.nev0 < 2 ^ 64) (hn64 : G.n < 2 ^ 64)
    {env : Env} {s : State}
    (hmem : s.mem = writeBytes (walkEntryMemAt G S) (S.e + 8) (wordBytes 8 G.n)) :
    (walkIfThenBlockState env G.ndst G.nev G.err S.e (BitVec.ofNat 64 G.ndst0)
      (BitVec.ofNat 64 G.nev0) (BitVec.ofNat 64 G.n) s).mem =
      walkFlushMemAt G S := by
  rw [walkIfThenBlockState_mem, hmem]
  have hA : (BitVec.ofNat 64 G.ndst0).toNat = G.ndst0 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hndst0]
  have hL : (BitVec.ofNat 64 G.nev0).toNat = G.nev0 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hnev0]
  have hE : (BitVec.ofNat 64 G.n).toNat = G.n := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn64]
  rw [hA, hL, hE]
  rfl

/-! ### The staged separation the copy's reads need

Three pairs, each read off the adapter's `DisjointRegions` through
`staged_pair`: the error record against the log, and the two cursor slots against
the error record.  The flush block's store is at `%e + 8`, inside the record's
twenty-four bytes, so the pairs are stated at the extents the reads and the store
reach. -/

/-- **The error record, the log, and the two cursor slots.**  The three pairs the
refusal copy's reads and its three stores read: the error record against the log,
and `%ndst` and `%nev` against the error record. -/
theorem walkFlush_sep {m0 : Mem} (G : WalkGeom m0) (S : WalkStage G) :
    (S.e + stage2ErrorExtent ≤ S.z ∨ S.z + stage2LogExtent ≤ S.e) ∧
    (G.ndst + 8 ≤ S.e + 8 ∨ S.e + 8 + 8 ≤ G.ndst) ∧
    (G.nev + 8 ≤ S.e + 8 ∨ S.e + 8 + 8 ≤ G.nev) ∧
    (G.ndst + 8 ≤ S.z + woff 8 ∨ S.z + woff 8 + 8 ≤ G.ndst) := by
  have hEZ : S.e + 24 ≤ S.z ∨ S.z + 64 ≤ S.e := by
    have h := staged_pair (b := G.b) (n := G.n) (ep := G.ep) (nep := G.nep)
      (xp := G.xp) (nxp := G.nxp) (dst := G.dst) (ndst0 := G.ndst0) (ev := G.ev)
      (evcap := G.evcap) (ndst := G.ndst) (nev := G.nev) (err := G.err)
      (c := S.c) (ctype := S.ctype) (cst := S.cst) (tok := S.tok) (sv := S.s)
      (z := S.z) (e := S.e) S.separate
      (r := (S.z, stage2LogExtent)) (by simp [stage2WalkRegions, stage2StagedWrites])
      (q := (S.e, stage2ErrorExtent)) (by simp [stage2WalkRegions, stage2StagedWrites])
      (by
        intro hh
        have h2' : stage2LogExtent = stage2ErrorExtent := congrArg Prod.snd hh
        exact absurd h2' (by decide))
    have h' : S.z + 64 ≤ S.e ∨ S.e + 24 ≤ S.z := h
    omega
  refine ⟨hEZ, ?_, ?_, ?_⟩
  · have h := walkRegion_against_writes S (r := (G.ndst, 8)) (by simp [stage2Regions])
      (q := (S.e, stage2ErrorExtent)) (by simp [stage2StagedWrites])
    have h' : G.ndst + 8 ≤ S.e ∨ S.e + 24 ≤ G.ndst := h
    omega
  · have h := walkRegion_against_writes S (r := (G.nev, 8)) (by simp [stage2Regions])
      (q := (S.e, stage2ErrorExtent)) (by simp [stage2StagedWrites])
    have h' : G.nev + 8 ≤ S.e ∨ S.e + 24 ≤ G.nev := h
    omega
  · have h := walkRegion_against_writes S (r := (G.ndst, 8)) (by simp [stage2Regions])
      (q := (S.z, stage2LogExtent)) (by simp [stage2StagedWrites])
    have h' : G.ndst + 8 ≤ S.z ∨ S.z + 64 ≤ G.ndst := h
    have hw : woff 8 = 8 := woff_8
    omega

/-! ### The copy's three reads, at the flush block's memory

The copy loads `%alen` and `%len` from the log's two cursor fields, and the
offset from `%e + 8` — the word the flush block has just stored.  The first two
pass the flush's store (the record is separate from the log), and the third is
the store itself. -/

/-- **The log's arena cursor at the flush block's memory.** -/
theorem walkFlushMem_alen {m0 : Mem} (G : WalkGeom m0) (S : WalkStage G)
    (hEZ : S.e + stage2ErrorExtent ≤ S.z ∨ S.z + stage2LogExtent ≤ S.e)
    (hndst0 : G.ndst0 < 2 ^ 64) :
    readBytes (writeBytes (walkEntryMemAt G S) (S.e + 8) (wordBytes 8 G.n))
      (S.z + woff 48) 8 = some (natToBytes (BitVec.ofNat 64 G.ndst0).toNat 8) := by
  have hz48 : S.z + woff 48 = S.z + 48 := by rw [woff_48]
  rw [hz48]
  have hout : S.z + 48 + 8 ≤ S.e + 8 ∨ S.e + 8 + (wordBytes 8 G.n).length ≤ S.z + 48 := by
    have hl : (wordBytes 8 G.n).length = 8 := by simp [wordBytes, natToBytes_length]
    simp only [stage2ErrorExtent, stage2LogExtent] at hEZ
    omega
  rw [walkReadBytes_writeBytes_outside (m := walkEntryMemAt G S) (v := wordBytes 8 G.n)
    (start := S.e + 8) (addr := S.z + 48) (n := 8) hout]
  rw [walkEntryMemAt_alen G S]
  rw [show (BitVec.ofNat 64 G.ndst0).toNat = G.ndst0 from by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hndst0]]
  rfl

/-- **The log's event cursor at the flush block's memory.** -/
theorem walkFlushMem_len {m0 : Mem} (G : WalkGeom m0) (S : WalkStage G)
    (hEZ : S.e + stage2ErrorExtent ≤ S.z ∨ S.z + stage2LogExtent ≤ S.e)
    (hnev0 : G.nev0 < 2 ^ 64) :
    readBytes (writeBytes (walkEntryMemAt G S) (S.e + 8) (wordBytes 8 G.n))
      (S.z + woff 8) 8 = some (natToBytes (BitVec.ofNat 64 G.nev0).toNat 8) := by
  have hz8 : S.z + woff 8 = S.z + 8 := by rw [woff_8]
  rw [hz8]
  have hout : S.z + 8 + 8 ≤ S.e + 8 ∨ S.e + 8 + (wordBytes 8 G.n).length ≤ S.z + 8 := by
    have hl : (wordBytes 8 G.n).length = 8 := by simp [wordBytes, natToBytes_length]
    simp only [stage2ErrorExtent, stage2LogExtent] at hEZ
    omega
  rw [walkReadBytes_writeBytes_outside (m := walkEntryMemAt G S) (v := wordBytes 8 G.n)
    (start := S.e + 8) (addr := S.z + 8) (n := 8) hout]
  rw [walkEntryMemAt_len G S]
  rw [show (BitVec.ofNat 64 G.nev0).toNat = G.nev0 from by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hnev0]]
  rfl

/-- **The refusal offset at the flush block's memory.**  The flush block's own
store, read back at its address and width. -/
theorem walkFlushMem_eoff {m0 : Mem} (G : WalkGeom m0) (S : WalkStage G)
    (hn64 : G.n < 2 ^ 64) :
    readBytes (writeBytes (walkEntryMemAt G S) (S.e + 8) (wordBytes 8 G.n))
      (S.e + 8) 8 = some (natToBytes (BitVec.ofNat 64 G.n).toNat 8) := by
  rw [readBytes_writeBytes_len (bs := wordBytes 8 G.n) (n := 8)
    (by simp [wordBytes, natToBytes_length])]
  rw [show (BitVec.ofNat 64 G.n).toNat = G.n from by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn64]]
  rfl

/-! ### The outcome, at its own word

The four steps `walkFlushAt_of_staging` composes, read at the returned memory and
at the refusal arm's literal verdict.  `walkFlushSteps12` supplies the two
control steps, the copy is `walkIfThenBlock_denote_named` at the state those two
leave, the jump is `walkIfThen_step`, and the return is `walkIfEnd_step` at
`walkIfEnd_refusal_phi`'s zero. -/

/-- **The empty entry stream's run, at the returned word and memory.**  At
`nep = 0` the entry block takes its zero arm, the flush block stores the document's
length as the refusal offset, the copy writes the record's three slots, and the
return carries the arm's literal zero — `(0 : BitVec 64)`, at the type the word
has, not a `Value` chosen to fit.  The memory is `walkFlushMemAt`, and the four
steps are inside `stage2FinalisationAllowance`. -/
theorem walkFlushRun_of_staging {mem : Mem} (G : WalkGeom mem) (S : WalkStage G)
    {d : Nat} (hzero : G.nep = 0) :
    ∃ q : Nat, q ≤ stage2FinalisationAllowance ∧
      runFuel (stage2Calls stage2SubCalls) q stage2Body
        (EntryState stage2Body
          (stage2Args [.ptr G.b, .int 64 (BitVec.ofNat 64 G.n), .ptr G.ep,
            .int 64 (BitVec.ofNat 64 G.nep), .ptr G.xp, .int 64 (BitVec.ofNat 64 G.nxp),
            .ptr G.dst, .int 64 (BitVec.ofNat 64 G.dstcap), .ptr G.ndst, .ptr G.ev,
            .int 64 (BitVec.ofNat 64 G.evcap), .ptr G.nev, .ptr G.err]
          d S.c S.ctype S.cst S.tok S.s S.z S.e) mem G.next0) =
        some (.ret (some (.int 64 0)) (walkFlushMemAt G S)) := by
  obtain ⟨s₁, s₂, h1, h2, hpc2, hxj, hrd, halen, hlen, hc, hctp, hcst, hnd, hnev, he,
    herr, hmem2, henv2⟩ := walkFlushSteps12 (mem := mem) (d := d) G S hzero
  obtain ⟨hEZ, hEd, hEn, hZd⟩ := walkFlush_sep G S
  have hn64 : G.n < 2 ^ 64 := WalkGeom.n_lt G
  have hndst0 : G.ndst0 < 2 ^ 64 := by
    have hroom := G.arenaRoom
    have hcap := G.dstcapLt
    simp only [stage2ArenaReserve] at hroom
    omega
  have hnev0 : G.nev0 < 2 ^ 64 := by
    have hroom := G.evRoom
    have hcap := G.evcapLt
    omega
  -- the copy's three reads, at the memory the flush block leaves
  have hA' := walkFlushMem_alen G S hEZ hndst0
  have hL' := walkFlushMem_len G S hEZ hnev0
  have hE' := walkFlushMem_eoff G S hn64
  have hmem := hmem2
  have hA : readBytes s₂.mem (S.z + woff 48) 8 =
      some (natToBytes (BitVec.ofNat 64 G.ndst0).toNat 8) := by
    rw [hmem]; exact hA'
  have hL : readBytes s₂.mem (S.z + woff 8) 8 =
      some (natToBytes (BitVec.ofNat 64 G.nev0).toNat 8) := by
    rw [hmem]; exact hL'
  have hE : readBytes s₂.mem (S.e + 8) 8 =
      some (natToBytes (BitVec.ofNat 64 G.n).toNat 8) := by
    rw [hmem]; exact hE'
  -- the copy, in its named state
  have hden : denoteCode (stage2Calls stage2SubCalls) walkIfThenBlock.instrs s₂ =
      some (walkIfThenBlockState s₂.env G.ndst G.nev G.err S.e
        (BitVec.ofNat 64 G.ndst0) (BitVec.ofNat 64 G.nev0) (BitVec.ofNat 64 G.n) s₂) := by
    have h := walkIfThenBlock_denote_named (sub := stage2SubCalls) (env := s₂.env) (s := s₂)
      hxj hrd hcst hctp hc halen hnd hlen hnev he herr hA hL hE hZd hEd hEn
    rwa [stateAt_self] at h
  have hpc₃ : (walkIfThenBlockState s₂.env G.ndst G.nev G.err S.e
      (BitVec.ofNat 64 G.ndst0) (BitVec.ofNat 64 G.nev0) (BitVec.ofNat 64 G.n) s₂).pc
      = s₂.pc := walkIfThenBlockState_pc _ _ _ _ _ _ _ _ _
  -- the jump to `if.end`
  let s₃ : State :=
    walkFlushPostCopyState s₂.env G.ndst G.nev G.err S.e
      (BitVec.ofNat 64 G.ndst0) (BitVec.ofNat 64 G.nev0) (BitVec.ofNat 64 G.n) s₂.pc s₂
  have hstep₃ : LeanLLVM.step (stage2Calls stage2SubCalls) stage2Body s₂ = .jump s₃ := by
    simpa only [s₃, walkFlushPostCopyState] using walkIfThen_step s₂ hpc2 hden hpc₃
  -- the return, at the refusal arm's zero
  have hz₂ : lookupName s₂.env "%z" = some (.ptr S.z) := by
    rw [henv2]
    simp [walkEntryEnv4, walkEntryEnv3, walkEntryEnv2, walkEntryEnv1, cells,
      lookupName_cons_ne, walkEntryState_env]
  have hs₂ : lookupName s₂.env "%s" = some (.ptr S.s) := by
    rw [henv2]
    simp [walkEntryEnv4, walkEntryEnv3, walkEntryEnv2, walkEntryEnv1, cells,
      lookupName_cons_ne, walkEntryState_env]
  have hphi : phiIncoming s₂.pc walkIfEndIncoming =
      some (Operand.imm (Const.int 64 (BitVec.ofNat 64 0))) := by
    rw [hpc2]
    exact walkIfEnd_refusal_phi
  have hcells₃ := walkFlushPostCopyState_cells s₂.env G.ndst G.nev G.err S.e
    (BitVec.ofNat 64 G.ndst0) (BitVec.ofNat 64 G.nev0) (BitVec.ofNat 64 G.n) s₂.pc s₂
  have hcells₃' : lookupName s₃.env "%e" = some (.ptr S.e) ∧
      lookupName s₃.env "%z" = some (.ptr S.z) ∧
      lookupName s₃.env "%s" = some (.ptr S.s) := by
    have hs : s₃ = walkFlushPostCopyState s₂.env G.ndst G.nev G.err S.e
        (BitVec.ofNat 64 G.ndst0) (BitVec.ofNat 64 G.nev0) (BitVec.ofNat 64 G.n)
        s₂.pc s₂ := rfl
    rw [hs]
    exact ⟨hcells₃.1.trans he, hcells₃.2.1.trans hz₂, hcells₃.2.2.trans hs₂⟩
  have hstep₄ : LeanLLVM.step (stage2Calls stage2SubCalls) stage2Body s₃ =
      .ret (some (.int 64 0))
        (stateAt (("%tobool.not151", .int 64 0) :: s₃.env) s₃) :=
    walkIfEnd_step (p := s₂.pc) (v := 0) (bit := 0) (pe := S.e) (pz := S.z) (ps := S.s)
      s₃ rfl hcells₃'.1 hcells₃'.2.1 hcells₃'.2.2 rfl hphi rfl
  -- the returned memory is the named one
  have hmem₄ : (stateAt (("%tobool.not151", .int 64 0) :: s₃.env) s₃).mem =
      walkFlushMemAt G S := by
    rw [stateAt_mem]
    show (walkFlushPostCopyState s₂.env G.ndst G.nev G.err S.e
      (BitVec.ofNat 64 G.ndst0) (BitVec.ofNat 64 G.nev0) (BitVec.ofNat 64 G.n)
      s₂.pc s₂).mem = walkFlushMemAt G S
    rw [walkFlushPostCopyState_mem]
    exact walkFlushCopy_mem G S hndst0 hnev0 hn64 hmem2
  refine ⟨4, by simp [stage2FinalisationAllowance], ?_⟩
  simp only [runFuel, h1, h2, hstep₃, hstep₄]
  rw [hmem₄]

/-! ### The record's three slots, at the returned memory

The copy's three stores are the last three writes, and the three slots are
pairwise separate by the staging, so each word reads back at its own slot.  The
refusal word is the document's length: the flush block stored it and the copy
copied it, so the arm's offset (`eoff`) is `G.n`. -/

/-- **The refusal word is the document's length.**  `%err`'s eight bytes at the
returned memory are `wordBytes 8 G.n`: the flush block's store of `%4`, loaded
and copied by the refusal arm.  This is the arm's `eoff`, and it is `≤ n` by
`le_rfl`. -/
theorem walkFlushMemAt_err {m0 : Mem} (G : WalkGeom m0) (S : WalkStage G) :
    readBytes (walkFlushMemAt G S) G.err 8 = some (wordBytes 8 G.n) := by
  rw [walkFlushMemAt]
  exact readBytes_writeBytes_len (bs := wordBytes 8 G.n) (n := 8)
    (by simp [wordBytes, natToBytes_length])

/-- **The event cursor's slot reports `nev0`.**  The arena's slot is separate from
it, and the refusal slot from both (`stage2Regions_slots`), so the two later
stores pass it. -/
theorem walkFlushMemAt_nev {m0 : Mem} (G : WalkGeom m0) (S : WalkStage G) :
    readBytes (walkFlushMemAt G S) G.nev 8 = some (wordBytes 8 G.nev0) := by
  obtain ⟨-, -, hslot3⟩ :=
    stage2Regions_slots (disjointRegions_staged_prefix S.separate)
  rw [walkFlushMemAt]
  rw [walkReadBytes_writeBytes_outside (m := writeBytes
      (writeBytes (writeBytes (walkEntryMemAt G S) (S.e + 8) (wordBytes 8 G.n))
        G.ndst (wordBytes 8 G.ndst0)) G.nev (wordBytes 8 G.nev0))
    (v := wordBytes 8 G.n) (start := G.err) (addr := G.nev) (n := 8) (by
      rcases hslot3 with h | h
      · exact Or.inl h
      · exact Or.inr (by simpa [wordBytes, natToBytes_length] using h))]
  exact readBytes_writeBytes_len (bs := wordBytes 8 G.nev0) (n := 8)
    (by simp [wordBytes, natToBytes_length])

/-- **The arena cursor's slot reports `ndst0`.**  The latest write at it is the
copy's own, and the two later stores miss it. -/
theorem walkFlushMemAt_ndst {m0 : Mem} (G : WalkGeom m0) (S : WalkStage G) :
    readBytes (walkFlushMemAt G S) G.ndst 8 = some (wordBytes 8 G.ndst0) := by
  obtain ⟨hslot1, hslot2, -⟩ :=
    stage2Regions_slots (disjointRegions_staged_prefix S.separate)
  rw [walkFlushMemAt]
  rw [walkReadBytes_writeBytes_outside (m := writeBytes
      (writeBytes (writeBytes (walkEntryMemAt G S) (S.e + 8) (wordBytes 8 G.n))
        G.ndst (wordBytes 8 G.ndst0)) G.nev (wordBytes 8 G.nev0))
    (v := wordBytes 8 G.n) (start := G.err) (addr := G.ndst) (n := 8) (by
      rcases hslot2 with h | h
      · exact Or.inl h
      · exact Or.inr (by simpa [wordBytes, natToBytes_length] using h))]
  rw [walkReadBytes_writeBytes_outside (m := writeBytes
      (writeBytes (walkEntryMemAt G S) (S.e + 8) (wordBytes 8 G.n))
      G.ndst (wordBytes 8 G.ndst0))
    (v := wordBytes 8 G.nev0) (start := G.nev) (addr := G.ndst) (n := 8) (by
      rcases hslot1 with h | h
      · exact Or.inl h
      · exact Or.inr (by simpa [wordBytes, natToBytes_length] using h))]
  exact readBytes_writeBytes_len (bs := wordBytes 8 G.ndst0) (n := 8)
    (by simp [wordBytes, natToBytes_length])


/-! ### The frame, and presence

`stage2Boundary` states silence over the run's whole touched extent
(`stage2ReportFrame`) and presence over the extents it writes
(`stage2ReportPresent`).  Neither is in the layer for this arm.  The frame is
`walkEntryMem_frame`'s four segment layers without the header's cursor store,
raised to the report's list; presence is the staging's own bytes, monotone
through the arm's four stores.
-/

/-- **The entry run's frame.**  `walkEntryMem_frame`'s chain at `walkEntryMemAt`:
the initialisation, the record's fields and the log, the cursor record, and the
two zeroed slots, without the header's cursor word.  The four layers compose and
the last is widened to `walkWide` through `walkEntryStores_covered`. -/
theorem walkEntryMemAt_frame {m0 : Mem} (G : WalkGeom m0) (S : WalkStage G) :
    UnchangedOutside m0 (walkEntryMemAt G S) (walkWide G (walkSeed G S)) := by
  have h0 := walkSeg2Init_frame G S (BitVec.ofNat 64 G.n)
    ((BitVec.ofNat 64 G.n + BitVec.ofNat 64 63) >>> 6)
  have h1 := walkSeg2_frame h0
  have h2 := walkSeg3_frame h1
  have h3 := walkSeg4_frame h2
  exact UnchangedOutside.of_covered h3 (walkEntryStores_covered G S)

/-- **The seed's frame covers the report's list.**  `walkWide` at the seed is the
arena's staged cursor, the event stream's, the seven appended objects, `%d.i` and
the five bootstrap slots; `stage2ReportFrame` is `stage2Writes` — the arena's
cursor plus the decoder's reserve, the event prefix, and the three slots — beside
the same scratch and a stack interval that covers the slots' window.  So the walk's
silence transfers to the record's wider list. -/
theorem walkSeedWide_covered {m0 : Mem} (G : WalkGeom m0) (S : WalkStage G) :
    ∀ r ∈ walkWide G (walkSeed G S),
      ∃ q ∈ stage2ReportFrame G.dst G.ndst0 G.ev G.nev0 G.ndst G.nev G.err S.c
        S.ctype S.cst S.tok S.s S.z S.e S.d G.next0 (G.next0 + (stage2BootstrapExtent + 8)),
        q.1 ≤ r.1 ∧ r.1 + r.2 ≤ q.1 + q.2 := by
  intro r hr
  have hal : (walkSeed G S).alen = G.ndst0 := rfl
  have hev : (walkSeed G S).evlen = G.nev0 := rfl
  simp only [walkWide, walkPresent] at hr
  rcases List.mem_append.mp hr with hr | hr
  · rcases List.mem_append.mp hr with hr | hr
    · rcases List.mem_cons.mp hr with rfl | hr1
      · exact ⟨(G.dst, G.ndst0 + stage2ArenaReserve),
          by simp [stage2ReportFrame, stage2ReportPresent, stage2Writes], by omega, by omega⟩
      · rcases List.mem_cons.mp hr1 with rfl | hnil
        · exact ⟨(G.ev, G.nev0),
            by simp [stage2ReportFrame, stage2ReportPresent, stage2Writes], by omega, by omega⟩
        · exact absurd hnil (by simp)
    · exact ⟨r, by
        simp only [stage2ReportFrame, stage2ReportPresent]
        exact List.mem_append_left _ (List.mem_append_right _ hr), le_rfl, le_rfl⟩
  · refine ⟨(G.next0, (G.next0 + (stage2BootstrapExtent + 8)) - G.next0), ?_, ?_, ?_⟩
    · simp only [stage2ReportFrame, stage2ReportPresent]
      exact List.mem_append_right _ (List.mem_cons_self ..)
    · exact stage2AllocaWrites_start hr
    · have h36 := stage2AllocaWrites_end hr
      simp only [stage2BootstrapExtent] at h36 ⊢
      omega

/-- **The entry run's frame at the record's list.** -/
theorem walkEntryMemAt_frame_report {m0 : Mem} (G : WalkGeom m0) (S : WalkStage G) :
    UnchangedOutside m0 (walkEntryMemAt G S)
      (stage2ReportFrame G.dst G.ndst0 G.ev G.nev0 G.ndst G.nev G.err S.c S.ctype
        S.cst S.tok S.s S.z S.e S.d G.next0 (G.next0 + (stage2BootstrapExtent + 8))) :=
  UnchangedOutside.of_covered (walkEntryMemAt_frame G S) (walkSeedWide_covered G S)

/-- **The arm's frame.**  The entry run's silence, then the arm's four stores: the
flush block's offset at `%e + 8` (inside the error record's twenty-four bytes) and
the copy's three slot words, each inside its own `stage2Writes` entry.  So the
returned memory is silent outside `stage2ReportFrame` at the numbers the run
reports — `ndst0` and `nev0`, because the arm appends to neither buffer. -/
theorem walkFlushMemAt_frame {m0 : Mem} (G : WalkGeom m0) (S : WalkStage G) :
    UnchangedOutside m0 (walkFlushMemAt G S)
      (stage2ReportFrame G.dst G.ndst0 G.ev G.nev0 G.ndst G.nev G.err S.c S.ctype
        S.cst S.tok S.s S.z S.e S.d G.next0 (G.next0 + (stage2BootstrapExtent + 8))) := by
  have h1 : UnchangedOutside m0
      (writeBytes (walkEntryMemAt G S) (S.e + 8) (wordBytes 8 G.n))
      (stage2ReportFrame G.dst G.ndst0 G.ev G.nev0 G.ndst G.nev G.err S.c S.ctype
        S.cst S.tok S.s S.z S.e S.d G.next0 (G.next0 + (stage2BootstrapExtent + 8))) :=
    UnchangedOutside.write_le (walkEntryMemAt_frame_report G S)
      ⟨(S.e, stage2ErrorExtent),
        by simp [stage2ReportFrame, stage2ReportPresent, stage2ReportScratch,
          stage2StagedWrites], by omega, by show S.e + 8 + 8 ≤ S.e + 24; omega⟩
      (w := 8) (bs := wordBytes 8 G.n) (by simp [wordBytes, natToBytes_length])
  have h2 : UnchangedOutside m0
      (writeBytes (writeBytes (walkEntryMemAt G S) (S.e + 8) (wordBytes 8 G.n))
        G.ndst (wordBytes 8 G.ndst0))
      (stage2ReportFrame G.dst G.ndst0 G.ev G.nev0 G.ndst G.nev G.err S.c S.ctype
        S.cst S.tok S.s S.z S.e S.d G.next0 (G.next0 + (stage2BootstrapExtent + 8))) :=
    UnchangedOutside.write_le h1
      ⟨(G.ndst, 8), by simp [stage2ReportFrame, stage2ReportPresent, stage2Writes],
        by omega, by omega⟩
      (w := 8) (bs := wordBytes 8 G.ndst0) (by simp [wordBytes, natToBytes_length])
  have h3 : UnchangedOutside m0
      (writeBytes (writeBytes (writeBytes (walkEntryMemAt G S) (S.e + 8)
        (wordBytes 8 G.n)) G.ndst (wordBytes 8 G.ndst0)) G.nev (wordBytes 8 G.nev0))
      (stage2ReportFrame G.dst G.ndst0 G.ev G.nev0 G.ndst G.nev G.err S.c S.ctype
        S.cst S.tok S.s S.z S.e S.d G.next0 (G.next0 + (stage2BootstrapExtent + 8))) :=
    UnchangedOutside.write_le h2
      ⟨(G.nev, 8), by simp [stage2ReportFrame, stage2ReportPresent, stage2Writes],
        by omega, by omega⟩
      (w := 8) (bs := wordBytes 8 G.nev0) (by simp [wordBytes, natToBytes_length])
  have h4 : UnchangedOutside m0
      (writeBytes (writeBytes (writeBytes (writeBytes (walkEntryMemAt G S) (S.e + 8)
        (wordBytes 8 G.n)) G.ndst (wordBytes 8 G.ndst0)) G.nev (wordBytes 8 G.nev0))
        G.err (wordBytes 8 G.n))
      (stage2ReportFrame G.dst G.ndst0 G.ev G.nev0 G.ndst G.nev G.err S.c S.ctype
        S.cst S.tok S.s S.z S.e S.d G.next0 (G.next0 + (stage2BootstrapExtent + 8))) :=
    UnchangedOutside.write_le h3
      ⟨(G.err, 8), by simp [stage2ReportFrame, stage2ReportPresent, stage2Writes],
        by omega, by omega⟩
      (w := 8) (bs := wordBytes 8 G.n) (by simp [wordBytes, natToBytes_length])
  simpa only [walkFlushMemAt] using h4

/-- **Presence survives the entry run.**  Every segment is a store fold or a pair
of stores, and a store only adds a cell. -/
theorem walkEntryMemAt_hasBytes {m0 : Mem} (G : WalkGeom m0) (S : WalkStage G)
    {a n : Nat} (h : Refinement.HasBytes m0 a n) :
    Refinement.HasBytes (walkEntryMemAt G S) a n := by
  have h1 : Refinement.HasBytes (walkSeg2InitMem S.s G.b G.ep (BitVec.ofNat 64 G.n)
      ((BitVec.ofNat 64 G.n + BitVec.ofNat 64 63) >>> 6) m0) a n := by
    rw [walkSeg2InitMem]
    exact hasBytes_stage2WriteStores h _
  have h2 : Refinement.HasBytes (walkSeg2PostMem S.s S.z G.nep G.xp G.nxp G.dst G.ndst0
      G.dstcap G.ev G.nev0 G.evcap (walkSeg2InitMem S.s G.b G.ep (BitVec.ofNat 64 G.n)
        ((BitVec.ofNat 64 G.n + BitVec.ofNat 64 63) >>> 6) m0)) a n := by
    rw [walkSeg2PostMem_eq]
    exact hasBytes_stage2WriteStores h1 _
  have h3 : Refinement.HasBytes (walkSeg3PostMem G.b G.n G.ep G.nep S.e S.c
      (walkSeg2PostMem S.s S.z G.nep G.xp G.nxp G.dst G.ndst0 G.dstcap G.ev G.nev0
        G.evcap (walkSeg2InitMem S.s G.b G.ep (BitVec.ofNat 64 G.n)
          ((BitVec.ofNat 64 G.n + BitVec.ofNat 64 63) >>> 6) m0))) a n := by
    rw [walkSeg3PostMem]
    exact hasBytes_stage2WriteStores h2 _
  have h4 : Refinement.HasBytes (walkSeg4PostMem (G.next0 + 8) (G.next0 + 12)
      (walkSeg3PostMem G.b G.n G.ep G.nep S.e S.c
        (walkSeg2PostMem S.s S.z G.nep G.xp G.nxp G.dst G.ndst0 G.dstcap G.ev G.nev0
          G.evcap (walkSeg2InitMem S.s G.b G.ep (BitVec.ofNat 64 G.n)
            ((BitVec.ofNat 64 G.n + BitVec.ofNat 64 63) >>> 6) m0)))) a n := by
    rw [walkSeg4PostMem]
    exact hasBytes_writeBytes (hasBytes_writeBytes h3)
  simpa only [walkEntryMemAt] using h4

/-- **Presence survives the arm.**  The entry run's bytes, then the flush block's
store and the copy's three, each of which adds cells and removes none. -/
theorem walkFlushMemAt_hasBytes {m0 : Mem} (G : WalkGeom m0) (S : WalkStage G)
    {a n : Nat} (h : Refinement.HasBytes m0 a n) :
    Refinement.HasBytes (walkFlushMemAt G S) a n := by
  have h0 := walkEntryMemAt_hasBytes G S h
  rw [walkFlushMemAt]
  exact hasBytes_writeBytes (hasBytes_writeBytes (hasBytes_writeBytes
    (hasBytes_writeBytes h0)))

/-- **Presence at the record's extents.**  Every entry of `stage2ReportPresent` was
staged by the caller or by the adapter: the arena's window and the event stream's
are `stage2Pre`'s, the two cursor words and the refusal slot its reads, and the
seven appended objects and `%d.i` are the adapter's (`WalkStage.present`,
`WalkStage.dPresent`). -/
theorem walkFlushMemAt_present_staged {m0 : Mem} (G : WalkGeom m0) (S : WalkStage G) :
    ∀ r ∈ stage2ReportPresent G.dst G.ndst0 G.ev G.nev0 G.ndst G.nev G.err S.c S.ctype
      S.cst S.tok S.s S.z S.e S.d, Refinement.HasBytes (walkFlushMemAt G S) r.1 r.2 := by
  have eDeep : Refinement.HasBytes (walkFlushMemAt G S) G.dst
      (G.ndst0 + stage2ArenaReserve) :=
    walkFlushMemAt_hasBytes G S (walkHasBytes_short G.arenaCap (by
      have h := G.arenaRoom
      omega))
  have eNdst : Refinement.HasBytes (walkFlushMemAt G S) G.ndst 8 :=
    walkFlushMemAt_hasBytes G S ((hasBytes_iff m0 G.ndst 8).mpr
      (fun k hk => readBytes_some_present m0 G.ndst 8 _ G.ndstRead k hk))
  have eEv : Refinement.HasBytes (walkFlushMemAt G S) G.ev G.nev0 :=
    walkFlushMemAt_hasBytes G S (walkHasBytes_short G.evCap (by
      have h := G.evRoom
      omega))
  have eNev : Refinement.HasBytes (walkFlushMemAt G S) G.nev 8 :=
    walkFlushMemAt_hasBytes G S ((hasBytes_iff m0 G.nev 8).mpr
      (fun k hk => readBytes_some_present m0 G.nev 8 _ G.nevRead k hk))
  have eErr : Refinement.HasBytes (walkFlushMemAt G S) G.err 8 :=
    walkFlushMemAt_hasBytes G S G.errBytes
  have eC : Refinement.HasBytes (walkFlushMemAt G S) S.c stage2CursorExtent :=
    walkFlushMemAt_hasBytes G S
      (S.present (S.c, stage2CursorExtent) (by simp [stage2StagedWrites]))
  have eCt : Refinement.HasBytes (walkFlushMemAt G S) S.ctype stage2StackExtent :=
    walkFlushMemAt_hasBytes G S
      (S.present (S.ctype, stage2StackExtent) (by simp [stage2StagedWrites]))
  have eCs : Refinement.HasBytes (walkFlushMemAt G S) S.cst stage2StackExtent :=
    walkFlushMemAt_hasBytes G S
      (S.present (S.cst, stage2StackExtent) (by simp [stage2StagedWrites]))
  have eTok : Refinement.HasBytes (walkFlushMemAt G S) S.tok stage2TokenExtent :=
    walkFlushMemAt_hasBytes G S
      (S.present (S.tok, stage2TokenExtent) (by simp [stage2StagedWrites]))
  have eS : Refinement.HasBytes (walkFlushMemAt G S) S.s stage2StateExtent :=
    walkFlushMemAt_hasBytes G S
      (S.present (S.s, stage2StateExtent) (by simp [stage2StagedWrites]))
  have eZ : Refinement.HasBytes (walkFlushMemAt G S) S.z stage2LogExtent :=
    walkFlushMemAt_hasBytes G S
      (S.present (S.z, stage2LogExtent) (by simp [stage2StagedWrites]))
  have eE : Refinement.HasBytes (walkFlushMemAt G S) S.e stage2ErrorExtent :=
    walkFlushMemAt_hasBytes G S
      (S.present (S.e, stage2ErrorExtent) (by simp [stage2StagedWrites]))
  have eD : Refinement.HasBytes (walkFlushMemAt G S) S.d 8 :=
    walkFlushMemAt_hasBytes G S S.dPresent
  intro r hr
  have hr5 : r ∈ stage2Writes G.dst G.ndst0 G.ev G.nev0 G.ndst G.nev G.err ∨
      r ∈ stage2ReportScratch S.c S.ctype S.cst S.tok S.s S.z S.e S.d := by
    simpa only [stage2ReportPresent, List.mem_append] using hr
  rcases hr5 with hr5 | hr5
  · simp only [stage2Writes, List.mem_cons, List.not_mem_nil, or_false] at hr5
    rcases hr5 with rfl | rfl | rfl | rfl | rfl
    · exact eDeep
    · exact eNdst
    · exact eEv
    · exact eNev
    · exact eErr
  · have hr7 : r ∈ stage2StagedWrites S.c S.ctype S.cst S.tok S.s S.z S.e ∨
        r = (S.d, 8) := by
      simpa only [stage2ReportScratch, List.mem_append, List.mem_cons,
        List.not_mem_nil, or_false] using hr5
    rcases hr7 with hr7 | rfl
    · simp only [stage2StagedWrites, List.mem_cons, List.not_mem_nil, or_false] at hr7
      rcases hr7 with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact eC
      · exact eCt
      · exact eCs
      · exact eTok
      · exact eS
      · exact eZ
      · exact eE
    · exact eD

/-- **Presence is monotone through the arm.**  A byte present at the staging is
present at the returned memory, at whatever address: a store replaces a cell or
adds one, so the arm never removes a byte. -/
theorem walkFlushMemAt_present_mono {m0 : Mem} (G : WalkGeom m0) (S : WalkStage G)
    {a : Nat} (h : present m0 a) : present (walkFlushMemAt G S) a := by
  have h1 : Refinement.HasBytes m0 a 1 :=
    (hasBytes_iff m0 a 1).mpr (fun k hk => by
      have hk0 : k = 0 := by omega
      subst hk0
      simpa using h)
  exact present_of_hasBytes (walkFlushMemAt_hasBytes G S h1) (Nat.le_refl _) (by omega)

/-- **Presence at the returned memory, pointwise.**  A byte inside one of the
record's present extents is present: the extent's bytes were staged and the arm
only writes. -/
theorem walkFlushMemAt_present {m0 : Mem} (G : WalkGeom m0) (S : WalkStage G) :
    ∀ a, inRegions (stage2ReportPresent G.dst G.ndst0 G.ev G.nev0 G.ndst G.nev G.err
      S.c S.ctype S.cst S.tok S.s S.z S.e S.d) a → present (walkFlushMemAt G S) a := by
  intro a ha
  obtain ⟨r, hr, hlo, hhi⟩ := ha
  exact present_of_hasBytes (walkFlushMemAt_present_staged G S r hr) hlo
    (Nat.lt_of_lt_of_le hhi (Nat.le_refl _))

/-! ### The boundary at the returned memory

`stage2Boundary`'s existential, packed at this arm: the returned word is `0`, the
two cursor words report the staged cursors, the two prefixes read back, the
the refusal word is the document's length, and the frame, presence and separation are
the lemmas above.  This is the route `stage2Boundary_of_parts` cannot take for
this arm — its `Stage2Run.walkFrame` omits the three slots the arm writes — so the
six facts are supplied at the returned memory directly.  The stack end is the
bootstrap window: no helper ran, so the five slots the initialisation's four
`alloca`s and the entry's own objects occupy are the whole stack.
-/

/-- **The flush arm's boundary.**  `stage2Boundary` at `walkFlushMemAt`: the
verdict `0`, `ndst0` at the arena's slot, `nev0` at the event stream's, `G.n` at
the refusal slot (which `≤ n` by `le_rfl`), the two prefixes as the caller staged
them, presence and the frame at the record's lists, and the staging's
separation. -/
theorem stage2Boundary_of_flush {args : List Value} {mem : Mem} {next : Nat}
    (G : WalkGeom mem) (S : WalkStage G) (hnext : G.next0 = next)
    (hargs : args = [.ptr G.b, .int 64 (BitVec.ofNat 64 G.n), .ptr G.ep,
      .int 64 (BitVec.ofNat 64 G.nep), .ptr G.xp, .int 64 (BitVec.ofNat 64 G.nxp),
      .ptr G.dst, .int 64 (BitVec.ofNat 64 G.dstcap), .ptr G.ndst, .ptr G.ev,
      .int 64 (BitVec.ofNat 64 G.evcap), .ptr G.nev, .ptr G.err]) :
    stage2Boundary args mem next (walkFlushMemAt G S) (.int 64 0) := by
  have hArena : Refinement.HasBytes (walkFlushMemAt G S) G.dst G.ndst0 :=
    walkFlushMemAt_hasBytes G S (walkHasBytes_short G.arenaCap (by have h := G.arenaRoom; omega))
  have hEv : Refinement.HasBytes (walkFlushMemAt G S) G.ev G.nev0 :=
    walkFlushMemAt_hasBytes G S (walkHasBytes_short G.evCap (by have h := G.evRoom; omega))
  obtain ⟨arena, hArenaRead⟩ :=
    readBytes_of_hasBytes (walkFlushMemAt G S) G.dst G.ndst0 ((hasBytes_iff _ _ _).mp hArena)
  obtain ⟨evs, hEvRead⟩ :=
    readBytes_of_hasBytes (walkFlushMemAt G S) G.ev G.nev0 ((hasBytes_iff _ _ _).mp hEv)
  have hnev0cap : G.nev0 ≤ G.evcap := by
    have h := G.evRoom
    omega
  have hnep64 : G.nep < 2 ^ 64 := by
    have hle := G.nep_le
    have hdoc := G.maxDoc
    simp only [stage2MaxDocument] at hdoc
    omega
  have hnendT : next ≤ next + (stage2BootstrapExtent + 8) := by omega
  have hframeT : UnchangedOutside mem (walkFlushMemAt G S)
      (stage2ReportFrame G.dst G.ndst0 G.ev G.nev0 G.ndst G.nev G.err S.c S.ctype
        S.cst S.tok S.s S.z S.e S.d next (next + (stage2BootstrapExtent + 8))) := by
    rw [← hnext]
    exact walkFlushMemAt_frame G S
  have hndstLe : G.ndst0 ≤ G.ndst0 + G.n := by omega
  have hnevLe : G.nev0 ≤ G.nev0 + stage2RecordBytes * G.n := by omega
  have hreserve : G.ndst0 + stage2ArenaReserve ≤ G.dstcap := by
    have h := G.arenaRoom
    omega
  have haccept : (0 : BitVec 64) = 1 →
      readBytes (walkFlushMemAt G S) G.err 8 = readBytes mem G.err 8 := by
    intro h
    exact absurd h (by decide)
  refine stage2Boundary_of_witness
    (w :=
      { b := G.b, n := G.n, ep := G.ep, nep := G.nep, xp := G.xp, nxp := G.nxp,
        dst := G.dst, dstcap := G.dstcap, ndst := G.ndst, ev := G.ev,
        evcap := G.evcap, nev := G.nev, err := G.err, verdict := 0,
        ndst0 := G.ndst0, nev0 := G.nev0, ndst' := G.ndst0, ndstU := G.ndst0,
        nev' := G.nev0,
        arena := arena, evs := evs, c := S.c, ctype := S.ctype, cst := S.cst,
        tok := S.tok, s := S.s, z := S.z, e := S.e, d := S.d,
        nkSlot := S.nkSlot, nxpSlot := S.nxpSlot,
        nextEnd := next + (stage2BootstrapExtent + 8) })
    (h :=
      { args_eq := hargs, value_eq := rfl, verdict_range := Or.inl rfl,
        ndst0_read := G.ndstRead, nev0_read := G.nevRead,
        ndstU_read := walkFlushMemAt_ndst G S, nev_read := walkFlushMemAt_nev G S,
        ndst0_le_U := Nat.le_refl G.ndst0, U_le_ndst := Nat.le_refl G.ndst0,
        ndst_le_n := hndstLe,
        nev0_le := Nat.le_refl G.nev0, nev_le := hnevLe,
        dstcap_lt := G.dstcapLt, evcap_lt := G.evcapLt,
        nev_le_evcap := hnev0cap, nep_lt := hnep64, nxp_lt := G.nxpLt,
        reserve := hreserve,
        arena_read := hArenaRead, evs_read := hEvRead,
        refuse_word := fun _ => ⟨G.n, Nat.le_refl _, walkFlushMemAt_err G S⟩,
        accept_word := haccept,
        present := walkFlushMemAt_present G S, next_le := hnendT,
        frame := hframeT, staged := S.separate, dSep := S.dSep })

/-! ### The post, for the empty entry stream

The completion and the boundary together are the record's post at the arm's
outcome: `stage2Post_of_completion` carries the boundary from the one outcome the
run produces to every behaviour, and the run's other outcomes are excluded by the
fuel's uniqueness.
-/

/-- **Every behaviour of the empty-stream run satisfies the record's post.**  The
completion is `walkFlushRun_of_staging` at the returned word and memory, and the
boundary at that outcome is `stage2Boundary_of_flush`; `stage2Post` is a match on
the outcome, so the two are the whole post. -/
theorem stage2Post_of_flush {a13 : List Value} {mem : Mem} {next : Nat}
    {d : Nat} (G : WalkGeom mem) (S : WalkStage G)
    (hargs : a13 = [.ptr G.b, .int 64 (BitVec.ofNat 64 G.n), .ptr G.ep,
      .int 64 (BitVec.ofNat 64 G.nep), .ptr G.xp, .int 64 (BitVec.ofNat 64 G.nxp),
      .ptr G.dst, .int 64 (BitVec.ofNat 64 G.dstcap), .ptr G.ndst, .ptr G.ev,
      .int 64 (BitVec.ofNat 64 G.evcap), .ptr G.nev, .ptr G.err])
    (hnext : G.next0 = next) (hzero : G.nep = 0) :
    ∀ o, BehFromState (stage2Calls stage2SubCalls) stage2Body
        (EntryState stage2Body (stage2Args a13 d S.c S.ctype S.cst S.tok S.s S.z S.e)
          mem next) o → stage2Post a13 mem next o := by
  obtain ⟨q, -, hrun⟩ := walkFlushRun_of_staging (d := d) G S hzero
  have hentry : EntryState stage2Body
      (stage2Args [.ptr G.b, .int 64 (BitVec.ofNat 64 G.n), .ptr G.ep,
        .int 64 (BitVec.ofNat 64 G.nep), .ptr G.xp, .int 64 (BitVec.ofNat 64 G.nxp),
        .ptr G.dst, .int 64 (BitVec.ofNat 64 G.dstcap), .ptr G.ndst, .ptr G.ev,
        .int 64 (BitVec.ofNat 64 G.evcap), .ptr G.nev, .ptr G.err]
      d S.c S.ctype S.cst S.tok S.s S.z S.e) mem G.next0 =
      EntryState stage2Body (stage2Args a13 d S.c S.ctype S.cst S.tok S.s S.z S.e)
        mem next := by
    rw [hargs, hnext]
  refine stage2Post_of_completion (B := q)
    (oGood := .ret (some (.int 64 0)) (walkFlushMemAt G S))
    (sE := EntryState stage2Body (stage2Args a13 d S.c S.ctype S.cst S.tok S.s S.z S.e)
      mem next) ?_ (stage2Boundary_of_flush G S hnext hargs)
  rwa [← hentry]

/-- **The all-whitespace case of the post, at the record's numbers.**  The arm's
post at a13: every behaviour of the run at the record's entry state satisfies
`Γ_stage2at`'s post, which is `stage2Post` at the thirteen arguments.  The
staging's fields are the record's (`hSc`…`hSe`), so the entry state the run was
stated at is the record's own. -/
theorem stage2Post_of_staging_flush {d c ctype cst tok s z e nkSlot nxpSlot : Nat}
    {a13 : List Value} {mem : Mem} {next : Nat} {G : WalkGeom mem} {S : WalkStage G}
    (hSc : S.c = c) (hSct : S.ctype = ctype) (hScs : S.cst = cst) (hStok : S.tok = tok)
    (hSs : S.s = s) (hSz : S.z = z) (hSe : S.e = e)
    (hargs : a13 = [.ptr G.b, .int 64 (BitVec.ofNat 64 G.n), .ptr G.ep,
      .int 64 (BitVec.ofNat 64 G.nep), .ptr G.xp, .int 64 (BitVec.ofNat 64 G.nxp),
      .ptr G.dst, .int 64 (BitVec.ofNat 64 G.dstcap), .ptr G.ndst, .ptr G.ev,
      .int 64 (BitVec.ofNat 64 G.evcap), .ptr G.nev, .ptr G.err])
    (hnext : G.next0 = next) (hzero : G.nep = 0) :
    ∀ o, BehFromState (stage2Calls stage2SubCalls) stage2Body
        (EntryState stage2Body (stage2Args a13 d c ctype cst tok s z e) mem next) o →
      (Γ_stage2at d c ctype cst tok s z e nkSlot nxpSlot).post
        (stage2Args a13 d c ctype cst tok s z e) mem next o := by
  have h := stage2Post_of_flush (d := d) G S hargs hnext hzero
  have hlen : a13.length = 13 := by rw [hargs]; rfl
  intro o hb
  show stage2Post ((stage2Args a13 d c ctype cst tok s z e).take 13) mem next o
  rw [stage2Args_take13 a13 hlen]
  refine h o ?_
  rw [hSc, hSct, hScs, hStok, hSs, hSz, hSe]
  exact hb

/-- **The walk's obligation at the two bundles — a conditional, not the closure claim.**

**Do not quote this as the closure claim.**  `Stage2WalkObligation` is `Satisfies` at
`Γ_stage2at`, and its two conjuncts are the completion (`stage2WalkCompletes_of_staging`)
and the post at every behaviour of the run.  The post's two arms are the record's empty
entry stream (`stage2Post_of_staging_flush`, above) and its loop
(`stage2Post_of_staging_loop`, `JsonStage2WalkPremisesOfStaging`), and the split is the
entry block's own test on the entry count.  That composition is real; its *premises* are
supplies no theorem of this tree builds.

**What the two bundles supply, and what they do not.**  `hcont` and `hend` are not supplied
facts, but neither is false.  `WalkLoopEnd`'s log word is `WalkInv.log_alen`'s witness,
which `walkMergeWords_of_inv` and `walkRefuseWords_of_inv` produce, so what the bundle still
supplies is the last entry's arm (`hlast`) — per-input dispatch evidence, not an invariant
consequence.  `WalkContinueFacts` is class data in the same sense: its per-state producers
take a tail `WalkSegment` and the scan's traversal hypotheses that are not `WalkInv`
consequences.  So `∀ G, WalkLoopEnd G` and `∀ G, WalkContinueFacts G` are producer
obligations rather than theorems — the tier that would build the arm and the class at every
`WalkGeom` is what is missing — and this implication is conditional on them.

**The closure claim** is `stage2WalkObligation_of_premises`
(`JsonStage2WalkAssembly`), whose premises are `WalkPremises` and the record's post rule
and no bundle.  `walkPremises_of_staging` (`JsonStage2WalkPremisesOfStaging`) is the
conditional that carries the two bundles into `WalkPremises`, and it is conditional on the
same two supplies.  The arm-level post theorems read here — `stage2Post_of_staging_flush`
above and `stage2Post_of_staging_loop` — carry content independently of the bundles.

**The lesson, recorded where the statement stands.**  A conditional on an unbuilt producer
reads exactly like a closure claim in a build log: `#print axioms` reports no `sorryAx`, and
the conclusion is reached through a hypothesis only a tier nobody wrote could meet.  That is
why the top-level statement has to carry its premises in the open — as `WalkPremises` does —
rather than behind a `∀ G` whose inhabitant is the thing in doubt.

The obligation is stated here rather than beside the completion because the two arms live
on either side of this module's import: the flush's post reads the returned memory this
module names (`walkFlushMemAt`), and the staging construction is the one below.  No
hypothesis of the post remains: the head state's two register cells are `WalkInv` clauses
read by `mergeHeadCells` (`JsonStage2WalkRevolutionSeg`), so they are not among the
premises. -/
theorem stage2WalkObligation_of_staging {d c ctype cst tok s z e nkSlot nxpSlot : Nat}
    (hcont : ∀ {m0 : Mem} (G : WalkGeom m0), WalkContinueFacts G)
    (hend : ∀ {m0 : Mem} (G : WalkGeom m0), WalkLoopEnd G) :
    Stage2WalkObligation d c ctype cst tok s z e nkSlot nxpSlot := by
  refine stage2WalkObligation_of_premises (walkPremises_of_staging hcont hend) ?_
  intro args mem next hpre o hb
  obtain ⟨a13, rfl, hpre13, hstaged⟩ := hpre
  obtain ⟨G, S, hnext, hSc, hSct, hScs, hStok, hSs, hSz, hSe, _hSd, hargs⟩ :=
    walkStage_at_pre_fields hpre13 hstaged
  by_cases hzero : G.nep = 0
  · exact stage2Post_of_staging_flush hSc hSct hScs hStok hSs hSz hSe hargs hnext hzero o hb
  · refine stage2Post_of_staging_loop (F := 27) hSc hSct hScs hStok hSs hSz hSe hargs hnext
      (Nat.pos_of_ne_zero hzero)
      (walkLoopStep_of_staging (G := G) (hcont G) (hend G)) o hb

/-! ### Axiom footprints -/

#print axioms LeanLLVM.Refinement.WalkScope.walkFlushRun_of_staging
#print axioms LeanLLVM.Refinement.WalkScope.walkFlushMemAt_err
#print axioms LeanLLVM.Refinement.WalkScope.walkFlushMemAt_ndst
#print axioms LeanLLVM.Refinement.WalkScope.walkFlushMemAt_nev
#print axioms LeanLLVM.Refinement.WalkScope.walkFlushMemAt_frame
#print axioms LeanLLVM.Refinement.WalkScope.walkFlushMemAt_present
#print axioms LeanLLVM.Refinement.WalkScope.walkFlushMemAt_present_mono
#print axioms LeanLLVM.Refinement.WalkScope.stage2Boundary_of_flush
#print axioms LeanLLVM.Refinement.WalkScope.stage2Post_of_flush
#print axioms LeanLLVM.Refinement.WalkScope.stage2Post_of_staging_flush
#print axioms LeanLLVM.Refinement.WalkScope.stage2WalkObligation_of_staging

end WalkScope
end LeanLLVM.Refinement
