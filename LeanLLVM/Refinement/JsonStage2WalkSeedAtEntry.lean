/-
The seed's run at the ABI's entry state.

`JsonStage2WalkSeedRun` states the seed's three-step prefix as an equality between
runs, with the three blocks' `denoteCode` results as its hypotheses and the state
they leave as a hypothesis too.  This module discharges those hypotheses at the
state the record actually starts from:

* **the entry environment is the argument list.**  `walkEntryState_env` is the
  body's twenty-one parameters, each bound to its argument, so every register the
  three blocks read is a list projection of `stage2Args`'s thirteen ABI words and
  eight staging pointers.  `walkEntryState_nep` is the one the empty-stream branch
  of the completion reads.
* **the three blocks run.**  `walkEntry_denote` at that environment gives the
  entry block's run; the preheader's five `getelementptr`s and the header's first
  pass are `walkPreheader_denote` and `whileBodyFirst_denote`, whose premises are
  the run's own cells and its two loads.  The memory the loads read is the entry
  run's fold *before* the header's cursor store, so the two `readBytes` facts are
  transported across that one eight-byte write by its extent.
* **the state they leave is the seed's.**  The composite is
  `walkSeedFinalState`: the environment is `walkSeedFinalEnv` by definition, the
  memory is `walkEntryMem`, and the cursor is the entry run's `+ 28` — the four
  `alloca`s.  `walkSeedPrefix_entry` states the run at that state, field for
  field.
* **the loads are the geometry's.**  `walkSeedPrefix_entry_geometry` removes the
  read hypotheses: `WalkGeom.entries` fixes the lane at index zero, `WalkGeom.doc`
  the byte that lane selects, and `walkSeed_entry_read` transports both across
  the run's own writes, exactly as `walkSeedState_geometry` does for the state.

What is *not* here: the call selection.  The entry block calls `s2_init`, and
`walkEntry_denote` is stated at `stage2Calls stage2SubCalls` — the reference
selection.  A completion at `stage2Calls sub` for another `sub` therefore needs
that `sub`'s own `s2_init` outcome, which is the helper contract the walk reads at
its first block; the seed's run below is the statement at the reference selection.
-/
import LeanLLVM.Refinement.JsonStage2WalkSeedRun
import LeanLLVM.Refinement.JsonStage2WalkTraverse

set_option autoImplicit false

namespace LeanLLVM.Refinement
open LeanLLVM
open LeanLLVM.Refinement.JsonStage2IR
open LeanLLVM.Refinement.BlockEval

namespace WalkScope

/-! ### The entry state's environment -/

/-- The body enters at `entry`, and `EntryState` reads that from the block list. -/
theorem walkStage2Body_entry : stage2Body.entry? = some "entry" := by decide


theorem walkEntryState_env {b n ep nep xp nxp dst dstcap ndst ev evcap nev err : Nat}
    {mem : Mem} {next : Nat} {d c ctype cst tok s z e : Nat} :
    (EntryState stage2Body
      (stage2Args [.ptr b, .int 64 (BitVec.ofNat 64 n), .ptr ep,
        .int 64 (BitVec.ofNat 64 nep), .ptr xp, .int 64 (BitVec.ofNat 64 nxp),
        .ptr dst, .int 64 (BitVec.ofNat 64 dstcap), .ptr ndst, .ptr ev,
        .int 64 (BitVec.ofNat 64 evcap), .ptr nev, .ptr err] d c ctype cst tok s z e)
      mem next).env =
      [("%b", .ptr b), ("%n", .int 64 (BitVec.ofNat 64 n)), ("%ep", .ptr ep),
       ("%nep", .int 64 (BitVec.ofNat 64 nep)), ("%xp", .ptr xp),
       ("%nxp", .int 64 (BitVec.ofNat 64 nxp)), ("%dst", .ptr dst),
       ("%dstcap", .int 64 (BitVec.ofNat 64 dstcap)), ("%ndst", .ptr ndst),
       ("%ev", .ptr ev), ("%evcap", .int 64 (BitVec.ofNat 64 evcap)),
       ("%nev", .ptr nev), ("%err", .ptr err), ("%d.i", .ptr d), ("%c.i", .ptr c),
       ("%ctype.i", .ptr ctype), ("%cst.i", .ptr cst), ("%t352.i", .ptr tok),
       ("%s", .ptr s), ("%z", .ptr z), ("%e", .ptr e)] := by
  simp [EntryState, stage2Body, stage2Args, stage2StagingArgs, List.zip, List.map,
    List.zipWith]

/-- A region of the walk's own list, against one of the seven appended objects. -/
theorem walkRegion_against_writes {m0 : Mem} {G : WalkGeom m0} (S : WalkStage G)
    {r : Nat × Nat}
    (hr : r ∈ stage2Regions G.b G.n G.ep G.nep G.xp G.nxp G.dst G.ndst0 G.ev G.evcap
      G.ndst G.nev G.err)
    {q : Nat × Nat} (hq : q ∈ stage2StagedWrites S.c S.ctype S.cst S.tok S.s S.z S.e) :
    r.1 + r.2 ≤ q.1 ∨ q.1 + q.2 ≤ r.1 := by
  have h := S.walk_separate
  unfold DisjointRegions at h
  rw [stage2WalkRegions] at h
  obtain ⟨-, -, hcross⟩ := List.pairwise_append.mp h
  exact hcross r hr q hq

/-- The seed's three-step run, at the ABI's entry state. -/
theorem walkSeedPrefix_entry {mem : Mem} (G : WalkGeom mem) (S : WalkStage G)
    {a13 : List Value}
    (h13 : a13 = [.ptr G.b, .int 64 (BitVec.ofNat 64 G.n), .ptr G.ep,
      .int 64 (BitVec.ofNat 64 G.nep), .ptr G.xp, .int 64 (BitVec.ofNat 64 G.nxp),
      .ptr G.dst, .int 64 (BitVec.ofNat 64 G.dstcap), .ptr G.ndst, .ptr G.ev,
      .int 64 (BitVec.ofNat 64 G.evcap), .ptr G.nev, .ptr G.err])
    {next : Nat} {d : Nat}
    (hnext : next = G.next0) (hn : 0 < G.nep)
    {bs : List UInt8}
    (hread : readBytes (walkEntryMem G S) G.ep 4 = some bs)
    (hlane : bytesToNat bs = entryPos G 0)
    (hdoc : readBytes (walkEntryMem G S) (G.b + entryPos G 0) 1 = some [entryByte G 0]) :
    ∀ k : Nat,
      runFuel (stage2Calls stage2SubCalls) (3 + k) stage2Body
        (EntryState stage2Body (stage2Args a13 d S.c S.ctype S.cst S.tok S.s S.z S.e) mem next) =
      runFuel (stage2Calls stage2SubCalls) k stage2Body
        (walkSeedFinalState G S
          (EntryState stage2Body (stage2Args a13 d S.c S.ctype S.cst S.tok S.s S.z S.e) mem next)
          (entryPos G 0) (entryByte G 0)) := by
  subst a13
  subst next
  intro k
  let ent : State := EntryState stage2Body
    (stage2Args [.ptr G.b, .int 64 (BitVec.ofNat 64 G.n), .ptr G.ep,
      .int 64 (BitVec.ofNat 64 G.nep), .ptr G.xp, .int 64 (BitVec.ofNat 64 G.nxp),
      .ptr G.dst, .int 64 (BitVec.ofNat 64 G.dstcap), .ptr G.ndst, .ptr G.ev,
      .int 64 (BitVec.ofNat 64 G.evcap), .ptr G.nev, .ptr G.err]
      d S.c S.ctype S.cst S.tok S.s S.z S.e)
    mem G.next0
  let e1 : Env := walkEntryEnv1 ent.env ent.next G.n
  let e2 : Env := walkEntryEnv2 e1 S.s S.z G.nep G.xp G.nxp G.dst G.ndst0 G.nev0 G.ev
  let e3 : Env := walkEntryEnv3 e2 G.b G.n G.ep S.s S.c
  let e4 : Env := walkEntryEnv4 e3 G.b G.nep
  let m1 : Mem := walkSeg4PostMem (ent.next + 8) (ent.next + 12)
    (walkSeg3PostMem G.b G.n G.ep G.nep S.e S.c
      (walkSeg2PostMem S.s S.z G.nep G.xp G.nxp G.dst G.ndst0 G.dstcap G.ev G.nev0 G.evcap
        (walkSeg2InitMem S.s G.b G.ep (BitVec.ofNat 64 G.n)
          ((BitVec.ofNat 64 G.n + BitVec.ofNat 64 63) >>> 6) mem)))
  let s₁ : State := stateAt e4 (memAt { ent with next := ent.next + 28 } m1)
  let p5 : Env := ("%kind404.i", .ptr (S.tok + 16)) :: ("%end.i", .ptr (S.tok + 8)) ::
    ("%gap.i", .ptr (S.tok + 20)) :: ("%h1.i.i.i51", .ptr (S.z + 24)) ::
    ("%k11.i", .ptr (S.c + 32)) :: e4
  let s₂ : State := stateAt p5 (walkEntryJump s₁ G.nep)
  let sl : State := { s₂ with pc := "while.body.i", pre := some "while.body.i.lr.ph" }
  let s₃ : State := stateAt (whileBodyOut sl.env 0 0 G.b G.ep S.c (entryPos G 0) (entryByte G 0))
    { sl with mem := writeBytes sl.mem (S.c + 32) (wordBytes 8 1) }
  have hn64 : G.n < 2 ^ 64 := by
    have h := G.maxDoc
    simp only [stage2MaxDocument] at h
    omega
  have hnep64 : G.nep < 2 ^ 64 := by
    have h := G.nep_le
    have h2 := G.maxDoc
    simp only [stage2MaxDocument] at h2
    omega
  have hndst0 : G.ndst0 < 2 ^ 64 := by
    have hroom := G.arenaRoom
    have hcap := G.dstcapLt
    simp only [stage2ArenaReserve] at hroom
    omega
  have hnev0 : G.nev0 < 2 ^ 64 := by
    have hroom := G.evRoom
    have hcap := G.evcapLt
    omega
  have hentEnv : ent.env = [("%b", .ptr G.b), ("%n", .int 64 (BitVec.ofNat 64 G.n)),
      ("%ep", .ptr G.ep), ("%nep", .int 64 (BitVec.ofNat 64 G.nep)), ("%xp", .ptr G.xp),
      ("%nxp", .int 64 (BitVec.ofNat 64 G.nxp)), ("%dst", .ptr G.dst),
      ("%dstcap", .int 64 (BitVec.ofNat 64 G.dstcap)), ("%ndst", .ptr G.ndst),
      ("%ev", .ptr G.ev), ("%evcap", .int 64 (BitVec.ofNat 64 G.evcap)),
      ("%nev", .ptr G.nev), ("%err", .ptr G.err), ("%d.i", .ptr d), ("%c.i", .ptr S.c),
      ("%ctype.i", .ptr S.ctype), ("%cst.i", .ptr S.cst), ("%t352.i", .ptr S.tok),
      ("%s", .ptr S.s), ("%z", .ptr S.z), ("%e", .ptr S.e)] := by
    simp only [ent, walkEntryState_env]
  have hb : lookupName ent.env "%b" = some (.ptr G.b) := by rw [hentEnv]; rfl
  have hn' : lookupName ent.env "%n" = some (.int 64 (BitVec.ofNat 64 G.n)) := by
    rw [hentEnv]; rfl
  have hep' : lookupName ent.env "%ep" = some (.ptr G.ep) := by rw [hentEnv]; rfl
  have hnec : lookupName ent.env "%nep" = some (.int 64 (BitVec.ofNat 64 G.nep)) := by
    rw [hentEnv]; rfl
  have hxp : lookupName ent.env "%xp" = some (.ptr G.xp) := by rw [hentEnv]; rfl
  have hnxp : lookupName ent.env "%nxp" = some (.int 64 (BitVec.ofNat 64 G.nxp)) := by
    rw [hentEnv]; rfl
  have hdst : lookupName ent.env "%dst" = some (.ptr G.dst) := by rw [hentEnv]; rfl
  have hndst : lookupName ent.env "%ndst" = some (.ptr G.ndst) := by rw [hentEnv]; rfl
  have hdcap : lookupName ent.env "%dstcap" = some (.int 64 (BitVec.ofNat 64 G.dstcap)) := by
    rw [hentEnv]; rfl
  have hev : lookupName ent.env "%ev" = some (.ptr G.ev) := by rw [hentEnv]; rfl
  have hnev : lookupName ent.env "%nev" = some (.ptr G.nev) := by rw [hentEnv]; rfl
  have hevcap : lookupName ent.env "%evcap" = some (.int 64 (BitVec.ofNat 64 G.evcap)) := by
    rw [hentEnv]; rfl
  have hcAddr : lookupName ent.env "%c.i" = some (.ptr S.c) := by rw [hentEnv]; rfl
  have hct : lookupName ent.env "%ctype.i" = some (.ptr S.ctype) := by rw [hentEnv]; rfl
  have hcs : lookupName ent.env "%cst.i" = some (.ptr S.cst) := by rw [hentEnv]; rfl
  have hsAddr : lookupName ent.env "%s" = some (.ptr S.s) := by rw [hentEnv]; rfl
  have hzAddr : lookupName ent.env "%z" = some (.ptr S.z) := by rw [hentEnv]; rfl
  have heAddr : lookupName ent.env "%e" = some (.ptr S.e) := by rw [hentEnv]; rfl
  have htok : lookupName ent.env "%t352.i" = some (.ptr S.tok) := by rw [hentEnv]; rfl
  have hsepS : G.ndst + 8 ≤ S.s ∨ S.s + 120 ≤ G.ndst := by
    have h := walkRegion_against_writes S (r := (G.ndst, 8))
      (by simp [stage2Regions])
      (q := (S.s, stage2StateExtent)) (by simp [stage2StagedWrites])
    simp only [stage2StateExtent] at h
    simpa using h
  have hsepZ : G.ndst + 8 ≤ S.z ∨ S.z + 64 ≤ G.ndst := by
    have h := walkRegion_against_writes S (r := (G.ndst, 8))
      (by simp [stage2Regions])
      (q := (S.z, stage2LogExtent)) (by simp [stage2StagedWrites])
    simp only [stage2LogExtent] at h
    simpa using h
  have hsepS2 : G.nev + 8 ≤ S.s ∨ S.s + 120 ≤ G.nev := by
    have h := walkRegion_against_writes S (r := (G.nev, 8))
      (by simp [stage2Regions])
      (q := (S.s, stage2StateExtent)) (by simp [stage2StagedWrites])
    simp only [stage2StateExtent] at h
    simpa using h
  have hsepZ2 : G.nev + 8 ≤ S.z ∨ S.z + 64 ≤ G.nev := by
    have h := walkRegion_against_writes S (r := (G.nev, 8))
      (by simp [stage2Regions])
      (q := (S.z, stage2LogExtent)) (by simp [stage2StagedWrites])
    simp only [stage2LogExtent] at h
    simpa using h
  have hsepSZ : S.s + 120 ≤ S.z ∨ S.z + 64 ≤ S.s := by
    have h := disjointRegions_pair_of_mem (S.writes_separate)
      (r := (S.s, stage2StateExtent)) (t := (S.z, stage2LogExtent))
      (by simp [stage2StagedWrites]) (by simp [stage2StagedWrites])
      (by intro hh
          have h2 : stage2StateExtent = stage2LogExtent := congrArg Prod.snd hh
          simp only [stage2StateExtent, stage2LogExtent] at h2
          omega)
    simp only [stage2StateExtent, stage2LogExtent] at h
    exact h
  have hnd : readBytes mem G.ndst 8 = some (natToBytes G.ndst0 8) := by
    simpa only [wordBytes] using G.ndstRead
  have hnevR : readBytes mem G.nev 8 = some (natToBytes G.nev0 8) := by
    simpa only [wordBytes] using G.nevRead
  have hden₁ : denoteCode (stage2Calls stage2SubCalls) walkEntryInstrs ent = some s₁ := by
    have hs : stateAt ent.env (memAt ent mem) = ent := by
      simp only [ent, stateAt, memAt, EntryState]
    rw [← hs]
    rw [walkEntry_denote (env := ent.env) (s := ent) (m := mem)
      (n := G.n) (sAddr := S.s) (zAddr := S.z) (eAddr := S.e) (b := G.b) (ep := G.ep)
      (nep := G.nep) (xp := G.xp) (nxp := G.nxp) (dst := G.dst) (dstcap := G.dstcap)
      (ev := G.ev) (ndst := G.ndst) (nev := G.nev) (v1 := G.ndst0) (v2 := G.nev0)
      (evcap := G.evcap) (cAddr := S.c) (ctypeAddr := S.ctype) (cstAddr := S.cst)
      G.bLt hn64 G.epLt G.bPos hn' hsAddr hzAddr heAddr hb hep' hnec hxp
      hnxp hdst hndst hdcap hev hnev hevcap hcAddr hct hcs hnep64 G.nxpLt
      G.dstcapLt hndst0 hnev0 G.evcapLt hsepS hsepZ hsepS2 hsepZ2 hsepSZ hnd hnevR]
    simp only [s₁, stateAt, memAt, e1, e2, e3, e4, m1, denoteCode_nil]
  have hne : lookupName s₁.env "%cmp.i247.not" =
      some (.int 1 (evalICmp .eq (BitVec.ofNat 64 G.nep) (BitVec.ofNat 64 0))) := by
    simp only [s₁, stateAt, memAt, e4, walkEntryEnv4, cells]
    exact lookupName_cons_self _ _ _
  have hpc₁ : s₁.pc = ent.pc := by simp only [s₁, stateAt, memAt]
  have hc : lookupName (walkEntryJump s₁ G.nep).env "%c.i" = some (.ptr S.c) := by
    simp only [walkEntryJump, s₁, stateAt, memAt, e4, e3, e2, e1,
      walkEntryEnv4, walkEntryEnv3, walkEntryEnv2, walkEntryEnv1, cells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact hcAddr
  have hz : lookupName (walkEntryJump s₁ G.nep).env "%z" = some (.ptr S.z) := by
    simp only [walkEntryJump, s₁, stateAt, memAt, e4, e3, e2, e1,
      walkEntryEnv4, walkEntryEnv3, walkEntryEnv2, walkEntryEnv1, cells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact hzAddr
  have ht : lookupName (walkEntryJump s₁ G.nep).env "%t352.i" = some (.ptr S.tok) := by
    simp only [walkEntryJump, s₁, stateAt, memAt, e4, e3, e2, e1,
      walkEntryEnv4, walkEntryEnv3, walkEntryEnv2, walkEntryEnv1, cells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact htok
  have hden₂ : denoteCode (stage2Calls stage2SubCalls) walkPreheaderInstrs
      (walkEntryJump s₁ G.nep) = some s₂ := by
    rw [walkPreheader_denote (calls := stage2Calls stage2SubCalls)
      (s := walkEntryJump s₁ G.nep) (c := S.c) (z := S.z) (tok := S.tok) hc hz ht]
    simp only [s₂, p5, stateAt, walkEntryJump, State.bind]
    rfl
  have hpc₂ : s₂.pc = (walkEntryJump s₁ G.nep).pc := by simp only [s₂, stateAt]
  have h5 : lookupName sl.env "%5" = some (.ptr G.ep) := by
    simp only [sl, s₂, stateAt, p5, e4, e3, e2, e1,
      walkEntryEnv4, walkEntryEnv3, walkEntryEnv2, walkEntryEnv1, cells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact lookupName_cons_self _ _ _
  have h3 : lookupName sl.env "%3" = some (.ptr G.b) := by
    simp only [sl, s₂, stateAt, p5, e4, e3, e2, e1,
      walkEntryEnv4, walkEntryEnv3, walkEntryEnv2, walkEntryEnv1, cells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact lookupName_cons_self _ _ _
  have hK : lookupName sl.env "%k11.i" = some (.ptr (S.c + 32)) := by
    simp only [sl, s₂, stateAt, p5, e4, e3, e2, e1,
      walkEntryEnv4, walkEntryEnv3, walkEntryEnv2, walkEntryEnv1, cells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact lookupName_cons_self _ _ _
  have hmem1 : walkEntryMem G S = writeBytes m1 (S.c + 32) (wordBytes 8 1) := by
    simp only [walkEntryMem, m1, ent, EntryState]
  have hsepEp : G.ep + 4 ≤ S.c + 32 ∨ S.c + 32 + 8 ≤ G.ep := by
    have h := walkRegion_against_writes S (r := (G.ep, 4 * G.nep))
      (by simp [stage2Regions])
      (q := (S.c, stage2CursorExtent)) (by simp [stage2StagedWrites])
    simp only [stage2CursorExtent] at h
    omega
  have hsepDoc : (G.b + entryPos G 0) + 1 ≤ S.c + 32 ∨ S.c + 32 + 8 ≤ G.b + entryPos G 0 := by
    have h := walkRegion_against_writes S (r := (G.b, G.n + stage2ReadTail))
      (by simp [stage2Regions])
      (q := (S.c, stage2CursorExtent)) (by simp [stage2StagedWrites])
    have hqn : entryPos G 0 < G.n := entryPos_lt G hn
    simp only [stage2ReadTail, stage2CursorExtent] at h
    omega
  have hslMem : sl.mem = m1 := by
    simp only [sl, s₂, walkEntryJump, s₁, stateAt, memAt]
  have hread1 : readBytes sl.mem G.ep 4 = some bs := by
    have h1 : readBytes (walkEntryMem G S) G.ep 4 = readBytes m1 G.ep 4 := by
      rw [hmem1]
      exact walkReadBytes_writeBytes_outside (m := m1) (v := wordBytes 8 1)
        (start := S.c + 32) (addr := G.ep) (n := 4) hsepEp
    rw [hslMem, ← h1]
    exact hread
  have hdoc1 : readBytes sl.mem (G.b + entryPos G 0) 1 = some [entryByte G 0] := by
    have h1 : readBytes (walkEntryMem G S) (G.b + entryPos G 0) 1 =
        readBytes m1 (G.b + entryPos G 0) 1 := by
      rw [hmem1]
      exact walkReadBytes_writeBytes_outside (m := m1) (v := wordBytes 8 1)
        (start := S.c + 32) (addr := G.b + entryPos G 0) (n := 1) hsepDoc
    rw [hslMem, ← h1]
    exact hdoc
  have hq32 : entryPos G 0 < 2 ^ 32 := by
    have hdocm := G.maxDoc
    have hlt := entryPos_lt G hn
    simp only [stage2MaxDocument] at hdocm
    omega
  have hden₃ : denoteCode (stage2Calls stage2SubCalls) whileBodyInstrs sl = some s₃ := by
    have h := whileBodyFirst_denote (calls := stage2Calls stage2SubCalls) (env := sl.env)
      (s := sl) (ep := G.ep) (b := G.b) (c := S.c) (q := entryPos G 0) (bs := bs)
      (bt := entryByte G 0) h5 h3 hK rfl hread1 hlane hdoc1 hq32
    rw [stateAt_self] at h
    simpa only [s₃] using h
  have hpc₃ : s₃.pc = sl.pc := by simp only [s₃, stateAt]
  have hrun := walkSeedPrefix_runFuel (s := ent) (s₁ := s₁) (s₂ := s₂) (s₃ := s₃)
    (nep := G.nep) k rfl hden₁ hne hnep64 (by omega) hpc₁ hden₂ hpc₂
    hden₃ hpc₃
  have hfinal : { s₃ with pc := "NodeBlock21", pre := some "while.body.i" } =
      walkSeedFinalState G S ent (entryPos G 0) (entryByte G 0) := by
    simp only [walkSeedFinalState, walkSeedFinalEnv, s₃, sl, s₂, walkEntryJump, s₁,
      stateAt, memAt, p5, e4, e3, e2, e1, walkEntryMem, m1, ent, EntryState]
  rw [hrun, hfinal]

/-- **The seed's run from the staging alone.**  The two loads the run takes are the
header's first pass; `WalkGeom.entries` fixes the lane at index zero and
`WalkGeom.doc` the byte it selects, so the theorem above applies with no read
hypothesis beside the geometry. -/
theorem walkSeedPrefix_entry_geometry {mem : Mem} (G : WalkGeom mem) (S : WalkStage G)
    {a13 : List Value}
    (h13 : a13 = [.ptr G.b, .int 64 (BitVec.ofNat 64 G.n), .ptr G.ep,
      .int 64 (BitVec.ofNat 64 G.nep), .ptr G.xp, .int 64 (BitVec.ofNat 64 G.nxp),
      .ptr G.dst, .int 64 (BitVec.ofNat 64 G.dstcap), .ptr G.ndst, .ptr G.ev,
      .int 64 (BitVec.ofNat 64 G.evcap), .ptr G.nev, .ptr G.err])
    {next : Nat} {d : Nat} (hnext : next = G.next0) (hn : 0 < G.nep) :
    ∀ k : Nat,
      runFuel (stage2Calls stage2SubCalls) (3 + k) stage2Body
        (EntryState stage2Body (stage2Args a13 d S.c S.ctype S.cst S.tok S.s S.z S.e)
          mem next) =
      runFuel (stage2Calls stage2SubCalls) k stage2Body
        (walkSeedFinalState G S
          (EntryState stage2Body (stage2Args a13 d S.c S.ctype S.cst S.tok S.s S.z S.e)
            mem next) (entryPos G 0) (entryByte G 0)) := by
  obtain ⟨-, hget⟩ := readLanes32_nth (m := mem) (addr := G.ep) (n := G.nep)
    (l := G.ent) G.entries
  obtain ⟨q0, bs0, hmem, hread0, hval⟩ := hget 0 hn
  rw [show G.ep + 4 * 0 = G.ep from by omega] at hread0
  have hpos : q0 = entryPos G 0 := by
    cases h : G.ent with
    | nil => rw [h] at hmem; simp at hmem
    | cons x xs =>
        rw [h] at hmem
        have hx : x = q0 := by simpa using hmem
        simpa [entryPos, h] using hx.symm
  have hread : readBytes (walkEntryMem G S) G.ep 4 = some bs0 := by
    rw [walkSeed_entry_read G S hn]
    exact hread0
  have hlane : bytesToNat bs0 = entryPos G 0 := by
    rw [hval, hpos]
  have hqin : entryPos G 0 ∈ G.ent := by
    rw [← hpos]
    rw [List.mem_iff_getElem?]
    exact ⟨0, hmem⟩
  have hqn : entryPos G 0 < G.n := G.inside _ hqin
  have hbyte : readBytes (walkEntryMem G S) (G.b + entryPos G 0) 1 =
      some [G.bs.getD (entryPos G 0) 0] := by
    rw [readBytes_eq_of_UnchangedOn
      (unchangedOutside_iff_inRegions.mp (walkEntryMem_frame G S))
      (fun k hk => walkSeed_doc_out (G := G) (S := S) (e := G.b + entryPos G 0 + k)
        (by omega) (by omega))]
    exact walkReadBytes_one_of_readByte (readByte_of_readBytes G.doc hqn)
  have hdoc : readBytes (walkEntryMem G S) (G.b + entryPos G 0) 1 =
      some [entryByte G 0] := by
    rw [hbyte]
    rfl
  exact walkSeedPrefix_entry G S h13 hnext hn hread hlane hdoc

/-! ### The instrument -/

#print axioms LeanLLVM.Refinement.WalkScope.walkEntryState_env
#print axioms LeanLLVM.Refinement.WalkScope.walkRegion_against_writes
#print axioms LeanLLVM.Refinement.WalkScope.walkSeedPrefix_entry
#print axioms LeanLLVM.Refinement.WalkScope.walkSeedPrefix_entry_geometry

end WalkScope

end LeanLLVM.Refinement
