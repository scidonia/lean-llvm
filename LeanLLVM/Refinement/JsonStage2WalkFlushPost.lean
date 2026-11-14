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

/-- A named state's memory is the one it was given. -/
theorem walkSetMem_mem (s : State) (m : Mem) : (walkSetMem s m).mem = m := rfl

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



/-! ### Axiom footprints -/

#print axioms LeanLLVM.Refinement.WalkScope.walkFlushRun_of_staging
#print axioms LeanLLVM.Refinement.WalkScope.walkFlushMemAt_err
#print axioms LeanLLVM.Refinement.WalkScope.walkFlushMemAt_ndst
#print axioms LeanLLVM.Refinement.WalkScope.walkFlushMemAt_nev

end WalkScope
end LeanLLVM.Refinement
