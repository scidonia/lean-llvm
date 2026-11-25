/-
The no-event walk's seed: the entry block's false arm, the preheader and the head
block, as one run from the seed's `EntryState` to the post-read head `NodeBlock5`.

The three steps are the approved blocks: the entry block (its instructions by
`entryBlock_denote`, its `nep ≠ 0` terminator by `entrySuffix_jump`), the
preheader (`preHeader_step`) and the head block (`link_loopHead`).  The reads the
head performs are the staging's: the entry block writes only `%xj`, `%e` and `%c`
(inside the run's regions and the stack interval), so the entry stream and the
document are as the record's precondition left them — the invariant's frame over
`stage2NoEventRunRegions` plus the interval is the transfer, and
`readLanes32_congr_bytes`/`readBytes_congr_bytes` are where it is read.

The head is `NodeBlock5` with `%k.0.ph1404 = 0`; the seed's invariant is the
entry block's, carried across the two write-free steps.  The run's conclusion is
the head's premise and its environment at the entry chain: the six read cells and
the nine `phi` cells at the seed's values over the entry chain, with the base
facts as lookups (`Stage2NoEventWalkBaseLookups`), so the head's model is the
entry chain and not a hand-built state.  The module ends
with `F2`: the seed's head binds none of the loop accumulator's four names, so no
`Stage2NoEventWalkAcc` is inhabitable there. -/
import LeanLLVM.Refinement.JsonStage2NoEventWalkSegment
import LeanLLVM.Refinement.JsonStage2NoEventWalkHead

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 800000

namespace LeanLLVM.Refinement

open LeanLLVM
open LeanLLVM.Refinement.JsonStage2NoEventIR
open LeanLLVM.Refinement.BlockEval
open LeanLLVM.Refinement.JsonEntryIR (readLanes32)
open LeanLLVM.Refinement.JsonEntrySteps (readBytes_congr_bytes readLanes32_congr_bytes
  readBytes_one readBytes_length)

/-! ### The lane and one-byte reads, restated locally -/

private theorem seed_natToBytes_one (b : UInt8) : natToBytes b.toNat 1 = [b] := by
  simp only [natToBytes, Nat.mod_eq_of_lt b.toNat_lt, UInt8.ofNat_toNat]

private theorem seed_bytesToNat_lt_32 {bs : List UInt8} (h : bs.length = 4) :
    bytesToNat bs < 2 ^ 32 := by
  have := bytesToNat_lt bs
  rw [h] at this
  calc bytesToNat bs < 256 ^ 4 := this
    _ = 2 ^ 32 := by decide

private theorem seed_readBytes_one_getD {m : Mem} {a n : Nat} {bs : List UInt8}
    (h : readBytes m a n = some bs) {k : Nat} (hk : k < n) :
    readBytes m (a + k) 1 = some [bs.getD k 0] := by
  rw [readBytes_one, readByte_of_readBytes h hk]
  rfl

private theorem seed_readLanes32_lane {m : Mem} {addr : Nat} :
    ∀ {n : Nat} {l : List Nat}, readLanes32 m addr n = some l →
      l.length = n ∧ ∀ j, j < n →
        ∃ q bs, l[j]? = some q ∧ readBytes m (addr + 4 * j) 4 = some bs ∧
          bytesToNat bs = q
  | 0, l, h => by
      simp only [readLanes32, Option.some.injEq] at h
      subst h
      exact ⟨rfl, fun j hj => absurd hj (Nat.not_lt_zero j)⟩
  | n + 1, l, h => by
      simp only [readLanes32] at h
      cases hb : readBytes m addr 4 with
      | none => rw [hb] at h; cases h
      | some bs =>
          rw [hb] at h
          cases hr : readLanes32 m (addr + 4) n with
          | none => rw [hr] at h; cases h
          | some tl =>
              rw [hr] at h
              simp only [Option.map_some, Option.bind_some, Option.some.injEq] at h
              subst h
              obtain ⟨hlen, hget⟩ := seed_readLanes32_lane (m := m) (addr := addr + 4) hr
              refine ⟨by simp [hlen], ?_⟩
              intro j hj
              cases j with
              | zero => exact ⟨bytesToNat bs, bs, by simp, by simpa using hb, rfl⟩
              | succ i =>
                  obtain ⟨q, bs', hq, hread, hval⟩ := hget i (by omega)
                  exact ⟨q, bs', by simp [hq], by
                    rw [show addr + 4 * (i + 1) = addr + 4 + 4 * i from by omega]
                    exact hread, hval⟩

/-! ### Lookups through the builder (restated privately) -/

private theorem seedCells_some :
    ∀ (cs : List (String × Value)) (n : String) (env : Env) {v : Value},
      lookupName cs n = some v → lookupName (cells cs env) n = some v
  | [], n, env, v, h => by simp only [lookupName_nil] at h; cases h
  | (k, w) :: cs, n, env, v, h => by
      by_cases hkn : k = n
      · subst hkn
        simp only [lookupName_cons_self] at h
        cases h
        exact lookupName_cons_self k w (cells cs env)
      · simp only [lookupName_cons_ne w cs hkn] at h
        simp only [cells, lookupName_cons_ne w (cells cs env) hkn]
        exact seedCells_some cs n env h

private theorem seedCells_notin :
    ∀ (cs : List (String × Value)) (n : String) (env : Env),
      n ∉ cs.map (·.1) → lookupName (cells cs env) n = lookupName env n
  | [], _, _, _ => rfl
  | (k, v) :: cs, n, env, h => by
      have hk : k ≠ n := by intro hkn; exact h (by subst hkn; simp)
      simp only [cells, lookupName_cons_ne v (cells cs env) hk]
      exact seedCells_notin cs n env (fun hc => h (List.mem_cons_of_mem _ hc))

/-! ### The frame: reads outside the run's regions -/

/-- **The second and fourth entries of a region list are separated.**  The
pairwise separation is read at the list's fixed positions, so the two entries do
not have to be shown distinct first: when their numbers coincide the disjunction
is itself the contradiction, and `omega` closes it from the regions' widths. -/
private theorem seedSep_second_fourth {a b c d : Nat × Nat} {rest : List (Nat × Nat)}
    (h : DisjointRegions ((a :: b :: c :: d :: []) ++ rest)) :
    b.1 + b.2 ≤ d.1 ∨ d.1 + d.2 ≤ b.1 := by
  unfold DisjointRegions at h
  rw [List.pairwise_append] at h
  obtain ⟨h1, -⟩ := h
  rw [List.pairwise_cons] at h1
  obtain ⟨-, h1⟩ := h1
  rw [List.pairwise_cons] at h1
  exact h1.1 d (by simp)

/-- **The first and fourth entries of a region list are separated.** -/
private theorem seedSep_first_fourth {a b c d : Nat × Nat} {rest : List (Nat × Nat)}
    (h : DisjointRegions ((a :: b :: c :: d :: []) ++ rest)) :
    a.1 + a.2 ≤ d.1 ∨ d.1 + d.2 ≤ a.1 := by
  unfold DisjointRegions at h
  rw [List.pairwise_append] at h
  obtain ⟨h1, -⟩ := h
  rw [List.pairwise_cons] at h1
  exact h1.1 d (by simp)

/-- **A read the run's frame leaves alone is the staging's read.** -/
theorem Stage2NoEventWalkInv.readBytes_off {K : Stage2NoEventWalkCarry} {mem : Mem}
    {s : State} (h : Stage2NoEventWalkInv K mem s) {a N : Nat} {bs : List UInt8}
    (hout : ∀ j, j < N → ¬ inRegions
      (stage2NoEventRunRegions K.scratch K.scratchcap K.stk K.e K.c K.d ++
        [(K.next0, K.nextEnd - K.next0)]) (a + j))
    (hr : readBytes mem a N = some bs) :
    readBytes s.mem a N = some bs := by
  have heq : readBytes s.mem a N = readBytes mem a N :=
    readBytes_congr_bytes (fun j hj => h.walkFrame (a + j) (fun r hr hi => hout j hj ⟨r, hr, hi⟩))
  rw [heq, hr]

/-- **A lane read the run's frame leaves alone is the staging's read.** -/
theorem Stage2NoEventWalkInv.readLanes_off {K : Stage2NoEventWalkCarry} {mem : Mem}
    {s : State} (h : Stage2NoEventWalkInv K mem s) {a k : Nat} {l : List Nat}
    (hout : ∀ j, j < 4 * k → ¬ inRegions
      (stage2NoEventRunRegions K.scratch K.scratchcap K.stk K.e K.c K.d ++
        [(K.next0, K.nextEnd - K.next0)]) (a + j))
    (hr : readLanes32 mem a k = some l) :
    readLanes32 s.mem a k = some l := by
  have heq : readLanes32 s.mem a k = readLanes32 mem a k :=
    readLanes32_congr_bytes (fun j hj => h.walkFrame (a + j) (fun r hr hi => hout j hj ⟨r, hr, hi⟩))
  rw [heq, hr]

/-! ### The hand-off states -/

/-- The entry block's false-arm hand-off: the preheader's entry state. -/
def entryPreheaderState (env : Env) (s : State) (b n ep nep c e : Nat) : State :=
  { env := entryFlushEnv env s b n ep nep c e,
    mem := entrySuffixMem (entryBootMem s.mem s.next e) b n ep nep c e,
    next := s.next + 32, pc := "if.end.peel.preheader", pre := some s.pc }

/-- The preheader's hand-off to the head block. -/
def entryHeadBlockState (env : Env) (s : State) (a b n ep nep c e : Nat) : State :=
  { env := cells (preHeaderCells a ++ entrySuffixCells b n ep nep c e)
      (entryBootEnv env s e),
    mem := entrySuffixMem (entryBootMem s.mem s.next e) b n ep nep c e,
    next := s.next + 32, pc := "if.end.peel", pre := some "if.end.peel.preheader" }

/-- The head's cell environment after its reads. -/
def entryHeadEnv (env : Env) (k : BitVec 64) (bs4 : List UInt8) (ep b : Nat)
    (bs1 : List UInt8) : Env :=
  ("%3", .int 8 (BitVec.ofNat 8 (bytesToNat bs1))) ::
    ("%arrayidx6.peel",
      .ptr (b + ((BitVec.ofNat 64 (bytesToNat bs4)).signExtend 64).toNat)) ::
    ("%idxprom.peel", .int 64 (BitVec.ofNat 64 (bytesToNat bs4))) ::
    ("%2", .int 32 (BitVec.ofNat 32 (bytesToNat bs4))) ::
    ("%arrayidx.peel", .ptr (ep + (k.signExtend 64).toNat * 4)) ::
    ("%inc.peel", .int 64 (k + BitVec.ofNat 64 1)) ::
    cells loopHeadPhiCells env

/-- The post-read head `NodeBlock5`. -/
def entryHeadState (s : State) (k : BitVec 64) (bs4 : List UInt8) (ep b : Nat)
    (bs1 : List UInt8) : State :=
  { env := entryHeadEnv s.env k bs4 ep b bs1, mem := s.mem, next := s.next,
    pc := "NodeBlock5", pre := some s.pc }

/-- The head state is the head block's hand-off: the block name, memory, cursor
and predecessor are the state's, and the environment is `entryHeadEnv`'s list. -/
theorem entryHeadState_eq (s : State) (k : BitVec 64) (bs4 : List UInt8)
    (ep b : Nat) (bs1 : List UInt8) :
    entryHeadState s k bs4 ep b bs1 =
      stage2NoEventWalkNext (entryHeadEnv s.env k bs4 ep b bs1) s "NodeBlock5" := rfl

/-- The head state keeps the state's memory: the projection is the structure
literal's field, read before any of the state's own data is unfolded. -/
theorem entryHeadState_mem (s : State) (k : BitVec 64) (bs4 : List UInt8)
    (ep b : Nat) (bs1 : List UInt8) :
    (entryHeadState s k bs4 ep b bs1).mem = s.mem := rfl

/-! ### The three steps -/

/-- **The entry block's false arm**, as one step to the preheader. -/
theorem entryBlock_step_preheader {gap : Calls} (env : Env) (s : State)
    {b n ep nep c e stk : Nat}
    (hb : lookupName env "%b" = some (.ptr b))
    (hn : lookupName env "%n" = some (.int 64 (BitVec.ofNat 64 n)))
    (hep : lookupName env "%ep" = some (.ptr ep))
    (hnep : lookupName env "%nep" = some (.int 64 (BitVec.ofNat 64 nep)))
    (hc : lookupName env "%c" = some (.ptr c))
    (he : lookupName env "%e" = some (.ptr e))
    (hstk : lookupName env "%stk" = some (.ptr stk))
    (hb1 : 1 ≤ b) (hpc : s.pc = "entry")
    (hbit : evalICmp .eq (BitVec.ofNat 64 nep) (BitVec.ofNat 64 0) =
      BitVec.ofNat 1 0) :
    step (stage2NoEventCalls gap) stage2NoEventBody (stateAt env s) =
      .jump (entryPreheaderState env s b n ep nep c e) := by
  unfold step
  rw [show (stateAt env s).pc = "entry" from hpc]
  simp only [entryBlock_find]
  rw [entryBlock_denote (gap := gap) (env := env) (s := s) hb hn hep hnep hc he hstk hb1]
  have hterm := entrySuffix_jump (gap := gap) (env := entryBootEnv env s e)
    (s := entryBootState s e) (b := b) (n := n) (ep := ep)
    (nep := nep) (c := c) (e := e)
    (mem := entrySuffixMem (entryBootMem s.mem s.next e) b n ep nep c e) hbit
  simpa only [entryPreheaderState, entryBlockPost, entrySuffixMem, entryFlushEnv,
    entrySuffixCells, entryCells5, cells, stateAt, stage2NoEventStepState,
    entryBootState, entryBlock, List.cons_append, List.nil_append, hbit] using hterm

/-- **The preheader's step** at the entry block's hand-off. -/
theorem entryPreheader_step {gap : Calls} (env : Env) (s : State)
    {a b n ep nep c e : Nat}
    (hs : lookupName env "%scratch" = some (.ptr a)) :
    step (stage2NoEventCalls gap) stage2NoEventBody (entryPreheaderState env s b n ep nep c e) =
      .jump (entryHeadBlockState env s a b n ep nep c e) := by
  have hs' : lookupName (entryBootEnv env s e) "%scratch" = some (.ptr a) := by
    rw [entryBootEnv, seedCells_notin (cs := entryBootCells s e) (n := "%scratch")
      (env := env) (by simp [entryBootCells])]
    exact hs
  have hstep := preHeader_step (gap := gap) (env := entryBootEnv env s e)
    (s := entryPreheaderState env s b n ep nep c e) (a := a) (b := b) (n := n)
    (ep := ep) (nep := nep) (c := c) (e := e) hs' rfl
  simpa only [entryHeadBlockState, entryPreheaderState, entryFlushEnv, entrySuffixCells,
    stage2NoEventJumpState, stateAt, List.append_assoc] using hstep

/-! ### The seed run

The head state's reads are the staging's, and the first lane and the first
document byte are the entry stream's and the document's. -/


/-! ### The head's premise at the seed

The seed's head state has the head block's cells over the preheader's `phi`
cells, which in turn sit over the entry block's own cells.  `Params` only reads
the environment, so it transports through each layer by the cell-name check:
`seedParams_cells` reads the names' absence as a `Bool` list check, which is what
makes the transport a `decide` at each layer rather than sixteen membership
proofs.

The nine `phi` cells are the preheader's, at exactly the values the seed's three
steps install: the zero counters, the zero depth and frame, the `520` budget, and
the index at zero.
-/

/-- The head block's six read cells, at the seed's index and lane. -/
private def seedHeadReadCells (bs4 bs1 : List UInt8) (ep b : Nat) :
    List (String × Value) :=
  [("%3", .int 8 (BitVec.ofNat 8 (bytesToNat bs1))),
   ("%arrayidx6.peel", .ptr (b + ((BitVec.ofNat 64 (bytesToNat bs4)).signExtend 64).toNat)),
   ("%idxprom.peel", .int 64 (BitVec.ofNat 64 (bytesToNat bs4))),
   ("%2", .int 32 (BitVec.ofNat 32 (bytesToNat bs4))),
   ("%arrayidx.peel", .ptr (ep + ((BitVec.ofNat 64 0).signExtend 64).toNat * 4)),
   ("%inc.peel", .int 64 (BitVec.ofNat 64 0 + BitVec.ofNat 64 1))]

/-- **The entry block's five allocation cells at a cursor.** -/
private theorem entryBootCells_literal (s : State) (e xj : Nat) (hnext : s.next = xj) :
    entryBootCells s e =
      [("%off", .ptr (e + 8)), ("%ei", .ptr (xj + 24)),
       ("%outn205", .ptr (xj + 16)), ("%outn", .ptr (xj + 8)),
       ("%xj", .ptr xj)] := by
  simp only [entryBootCells]
  rw [hnext]

/-- **The preheader's hand-off environment, as the base cells at the cursor.** -/
private theorem entryHeadBlockState_env (env : Env) (s : State)
    {a b n ep nep c e xj : Nat} (hnext : s.next = xj) :
    (entryHeadBlockState env s a b n ep nep c e).env =
      cells (preHeaderCells a ++ entrySuffixCells b n ep nep c e ++
        [("%off", .ptr (e + 8)), ("%ei", .ptr (xj + 24)),
         ("%outn205", .ptr (xj + 16)), ("%outn", .ptr (xj + 8)),
         ("%xj", .ptr xj)]) env := by
  show cells (preHeaderCells a ++ entrySuffixCells b n ep nep c e)
      (cells (entryBootCells s e) env) = _
  rw [← cells_append, entryBootCells_literal s e xj hnext]

/-- **The entry's zero test is false on the seed's branch.** -/
private theorem stage2NoEventSeed_cmp_zero {K : Stage2NoEventWalkCarry} {mem : Mem}
    {s0 : State} (h : Stage2NoEventWalkInv K mem s0) (_hnepos : 0 < K.nep) :
    evalICmp .eq (BitVec.ofNat 64 K.nep) (BitVec.ofNat 64 0) = BitVec.ofNat 1 0 := by
  have hne : (BitVec.ofNat 64 K.nep) ≠ (0 : BitVec 64) := by
    intro h0
    have h1 := congrArg BitVec.toNat h0
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h.nepLt,
      show (0 : BitVec 64).toNat = 0 from by decide] at h1
    omega
  show BitVec.ofBool (decide (BitVec.ofNat 64 K.nep = 0#64)) = 0#1
  rw [show decide (BitVec.ofNat 64 K.nep = 0#64) = false from by
    simp only [decide_eq_false_iff_not]
    exact hne]
  rfl

/-- **The entry chain as the base lookup table's cells.**  The preheader env is
the table's cells over the entry state: the suffix's zero test is the table's
literal zero on the seed's branch. -/
private theorem entryHeadBlockState_baseCells {K : Stage2NoEventWalkCarry} {mem : Mem}
    {s0 : State} (h : Stage2NoEventWalkInv K mem s0) (hnext : s0.next = K.next0)
    (hnepos : 0 < K.nep) :
    (entryHeadBlockState s0.env s0 K.scratch K.b K.n K.ep K.nep K.c K.e).env =
      cells (stage2NoEventWalkBaseCellValues K) s0.env := by
  rw [entryHeadBlockState_env s0.env s0 hnext]
  congr 1
  simp [stage2NoEventWalkBaseCellValues, entrySuffixCells, entryCells5,
    stage2NoEventSeed_cmp_zero h hnepos]

/-- **The head's cell environment, as the builder's two layers.** -/
private theorem entryHeadEnv_cells (env : Env) (bs4 : List UInt8)
    (ep b : Nat) (bs1 : List UInt8) :
    entryHeadEnv env (BitVec.ofNat 64 0) bs4 ep b bs1 =
      cells (seedHeadReadCells bs4 bs1 ep b) (cells loopHeadPhiCells env) := rfl

set_option maxHeartbeats 4000000
/-- **The seed's three-step run to the head, with the head's index at zero,**
and the head's premise and output evidence at it.** -/
theorem stage2NoEventWalkSeedRun {gap : Calls} {K : Stage2NoEventWalkCarry}
    {mem : Mem} {s0 : State}
    (h : Stage2NoEventWalkInv K mem s0) (hpar : Stage2NoEventWalkParams K s0)
    (hpc : s0.pc = "entry") (hnext : s0.next = K.next0) (hxj : K.xj = K.next0)
    (hb1 : 1 ≤ K.b) (hnepos : 0 < K.nep)
    (hKtok : K.tok = 0) (hKterms : K.terms = 0) (hKarena : K.arena = []) :
    ∃ (sHead : State) (lane : Nat) (byte : UInt8),
      (∀ n, runFuel (stage2NoEventCalls gap) (3 + n) stage2NoEventBody s0 =
        runFuel (stage2NoEventCalls gap) n stage2NoEventBody sHead) ∧
      Stage2NoEventWalkHead K mem 0 sHead ∧ Stage2NoEventWalkTrace K sHead ∧
      sHead.env = cells (loopHeadReadCellsAt K 0 0 0 0 520 lane byte)
        (cells (loopHeadPhiCellsAt K 0 0 0 0 520)
          (entryHeadBlockState s0.env s0 K.scratch K.b K.n K.ep K.nep K.c K.e).env) := by
  -- the entry block's false arm
  have hbit := stage2NoEventSeed_cmp_zero h hnepos
  have hstep1 : step (stage2NoEventCalls gap) stage2NoEventBody s0 =
      .jump (entryPreheaderState s0.env s0 K.b K.n K.ep K.nep K.c K.e) := by
    simpa only [stateAt] using
      (entryBlock_step_preheader (gap := gap) (env := s0.env) (s := s0)
        hpar.b hpar.n hpar.ep hpar.nep hpar.c hpar.e hpar.stk hb1 hpc hbit)
  -- the preheader
  have hstep2 : step (stage2NoEventCalls gap) stage2NoEventBody
        (entryPreheaderState s0.env s0 K.b K.n K.ep K.nep K.c K.e) =
      .jump (entryHeadBlockState s0.env s0 K.scratch K.b K.n K.ep K.nep K.c K.e) :=
    entryPreheader_step (gap := gap) (env := s0.env) (s := s0) hpar.scratch
  -- the region list's four ABI entries, with the staged objects appended
  have hfour : DisjointRegions
      ([(K.b, K.n + stage2ReadTail), (K.ep, 4 * K.nep), (K.xp, 4 * K.nxp),
        (K.scratch, K.scratchcap)] ++
        (stage2NoEventWrites K.tokensOut K.valuesOut K.sumOut K.err ++
          stage2NoEventStagedRegions K.stk K.e K.c K.d)) := by
    simpa only [Stage2NoEventWalkSep, stage2NoEventRegions, List.append_assoc] using h.sep
  -- the entry block's writes, carried to the preheader's hand-off
  have hinvHead : Stage2NoEventWalkInv K mem
      (entryHeadBlockState s0.env s0 K.scratch K.b K.n K.ep K.nep K.c K.e) :=
    (entryBlock_inv h hnext).mem_congr (by
      simp only [entryHeadBlockState, entryFlushState, entrySuffixMem, entryBootMem])
  -- the head's reads from the staging
  have houtLane : ∀ j, j < 4 * K.nep → ¬ inRegions
      (stage2NoEventRunRegions K.scratch K.scratchcap K.stk K.e K.c K.d ++
        [(K.next0, K.nextEnd - K.next0)]) (K.ep + j) := by
    intro j hj hin
    obtain ⟨r, hr, hlo, hhi⟩ := hin
    rcases List.mem_append.mp hr with hr | hr
    · -- the run's regions: the scratch or a staged object
      rcases List.mem_cons.mp hr with hsc | hst
      · -- ep against the scratch: both are entries of the region list
        subst hsc
        rcases seedSep_second_fourth hfour with h | h <;> omega
      · -- ep against a staged object, through the one separation surface
        have hep : (K.ep, 4 * K.nep) ∈ stage2NoEventRegions K.b K.n K.ep K.nep K.xp
            K.nxp K.scratch K.scratchcap K.tokensOut K.valuesOut K.sumOut K.err := by
          simp [stage2NoEventRegions]
        rcases disjointRegions_against
          (rs := stage2NoEventRegions K.b K.n K.ep K.nep K.xp K.nxp K.scratch
            K.scratchcap K.tokensOut K.valuesOut K.sumOut K.err)
          (ss := stage2NoEventStagedRegions K.stk K.e K.c K.d) h.sep hep r hst with h | h <;> omega
    · -- the interval: the watermark puts the entry stream below it
      have hle : K.ep + 4 * K.nep ≤ K.next0 :=
        h.watermark (K.ep, 4 * K.nep) (by simp [stage2NoEventRegions])
      have hr' : r = (K.next0, K.nextEnd - K.next0) := by
        simpa only [List.mem_singleton] using hr
      subst hr'
      simp only at hlo hhi
      omega
  have hlanes : readLanes32 (entryHeadBlockState s0.env s0 K.scratch K.b K.n K.ep
      K.nep K.c K.e).mem K.ep K.nep = some K.ent :=
    hinvHead.readLanes_off (K := K) (a := K.ep) (k := K.nep) (l := K.ent)
      houtLane h.entries
  obtain ⟨-, hlaneGet⟩ := seed_readLanes32_lane
    (m := (entryHeadBlockState s0.env s0 K.scratch K.b K.n K.ep K.nep K.c K.e).mem)
    (addr := K.ep) hlanes
  obtain ⟨q, bs4H, hlaneH0, hbyte4, hb4⟩ := hlaneGet 0 (by omega)
  have hb4lt : bytesToNat bs4H < 2 ^ 32 := by
    have hlen : bs4H.length = 4 := readBytes_length _ _ _ hbyte4
    exact seed_bytesToNat_lt_32 hlen
  have hqlt : q < K.n := by
    have : q ∈ K.ent := List.mem_of_getElem? hlaneH0
    exact h.inside q this
  have houtDoc : ∀ j, j < 1 → ¬ inRegions
      (stage2NoEventRunRegions K.scratch K.scratchcap K.stk K.e K.c K.d ++
        [(K.next0, K.nextEnd - K.next0)]) (K.b + q + j) := by
    intro j hj hin
    obtain ⟨r, hr, hlo, hhi⟩ := hin
    rcases List.mem_append.mp hr with hr | hr
    · rcases List.mem_cons.mp hr with hsc | hst
      · -- the document against the scratch: both are entries of the region list
        subst hsc
        rcases seedSep_first_fourth hfour with h | h <;> omega
      · have hdoc : (K.b, K.n + stage2ReadTail) ∈ stage2NoEventRegions K.b K.n K.ep K.nep
            K.xp K.nxp K.scratch K.scratchcap K.tokensOut K.valuesOut K.sumOut K.err := by
          simp [stage2NoEventRegions]
        rcases disjointRegions_against
          (rs := stage2NoEventRegions K.b K.n K.ep K.nep K.xp K.nxp K.scratch
            K.scratchcap K.tokensOut K.valuesOut K.sumOut K.err)
          (ss := stage2NoEventStagedRegions K.stk K.e K.c K.d) h.sep hdoc r hst with h | h <;> omega
    · have hle : K.b + (K.n + stage2ReadTail) ≤ K.next0 :=
        h.watermark (K.b, K.n + stage2ReadTail) (by simp [stage2NoEventRegions])
      have hr' : r = (K.next0, K.nextEnd - K.next0) := by
        simpa only [List.mem_singleton] using hr
      subst hr'
      simp only at hlo hhi
      omega
  have hbytemem : readBytes mem (K.b + q) 1 = some (natToBytes (K.bs.getD q 0).toNat 1) := by
    simpa only [seed_natToBytes_one] using seed_readBytes_one_getD h.doc (by omega)
  have hbyteH : readBytes (entryHeadBlockState s0.env s0 K.scratch K.b K.n K.ep K.nep
      K.c K.e).mem (K.b + q) 1 = some (natToBytes (K.bs.getD q 0).toNat 1) :=
    hinvHead.readBytes_off (K := K) (a := K.b + q) (N := 1)
      (bs := natToBytes (K.bs.getD q 0).toNat 1) houtDoc hbytemem
  have hsign : ((BitVec.ofNat 64 (bytesToNat bs4H)).signExtend 64).toNat = q := by
    rw [BitVec.signExtend_eq, hb4, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega)]
  have hk0 : (((BitVec.ofNat 64 0 : BitVec 64)).signExtend 64).toNat = 0 := by decide
  have hlink := link_loopHead (calls := stage2NoEventCalls gap) (K := K) (mem := mem)
    (s := entryHeadBlockState s0.env s0 K.scratch K.b K.n K.ep K.nep K.c K.e)
    (k := BitVec.ofNat 64 0) (ep := K.ep) (b := K.b) (bs4 := bs4H)
    (bs1 := natToBytes (K.bs.getD q 0).toNat 1)
    hinvHead rfl rfl
    (by
      -- %k.0.ph1404 at the phi cells
      show lookupName (cells loopHeadPhiCells
        (cells (preHeaderCells K.scratch ++ entrySuffixCells K.b K.n K.ep K.nep K.c K.e)
          (entryBootEnv s0.env s0 K.e))) "%k.0.ph1404" = some (.int 64 0)
      rw [seedCells_some (cs := loopHeadPhiCells) (n := "%k.0.ph1404") (env := _)
        (v := .int 64 0)]
      decide)
    (by
      show lookupName (cells loopHeadPhiCells
        (cells (preHeaderCells K.scratch ++ entrySuffixCells K.b K.n K.ep K.nep K.c K.e)
          (entryBootEnv s0.env s0 K.e))) "%ep" = some (.ptr K.ep)
      rw [seedCells_notin (cs := loopHeadPhiCells) (n := "%ep") (env := _) (by simp [loopHeadPhiCells])]
      rw [seedCells_notin (cs := preHeaderCells K.scratch ++ entrySuffixCells K.b K.n K.ep K.nep K.c K.e)
        (n := "%ep") (env := _) (by simp [preHeaderCells, entrySuffixCells, entryCells1,
          entryCells2, entryCells3, entryCells4, entryCells5])]
      rw [entryBootEnv, seedCells_notin (cs := entryBootCells s0 K.e) (n := "%ep") (env := _)
        (by simp [entryBootCells])]
      exact hpar.ep)
    (by
      show lookupName (cells loopHeadPhiCells
        (cells (preHeaderCells K.scratch ++ entrySuffixCells K.b K.n K.ep K.nep K.c K.e)
          (entryBootEnv s0.env s0 K.e))) "%b" = some (.ptr K.b)
      rw [seedCells_notin (cs := loopHeadPhiCells) (n := "%b") (env := _) (by simp [loopHeadPhiCells])]
      rw [seedCells_notin (cs := preHeaderCells K.scratch ++ entrySuffixCells K.b K.n K.ep K.nep K.c K.e)
        (n := "%b") (env := _) (by simp [preHeaderCells, entrySuffixCells, entryCells1,
          entryCells2, entryCells3, entryCells4, entryCells5])]
      rw [entryBootEnv, seedCells_notin (cs := entryBootCells s0 K.e) (n := "%b") (env := _)
        (by simp [entryBootCells])]
      exact hpar.b)
    (by decide)
    (by rw [hk0]; exact hbyte4)
    hb4lt
    (by rw [hsign]; exact hbyteH)
  -- the head's read cells, at the seed's index and lane
  have hb1v : bytesToNat (natToBytes (K.bs.getD q 0).toNat 1) =
      (K.bs.getD q 0).toNat := by
    rw [seed_natToBytes_one]; simp [bytesToNat]
  have hreadCells : seedHeadReadCells bs4H (natToBytes (K.bs.getD q 0).toNat 1) K.ep K.b =
      loopHeadReadCells 0 q (K.bs.getD q 0) K.ep K.b := by
    have hinc : (BitVec.ofNat 64 0 + BitVec.ofNat 64 1 : BitVec 64) =
        BitVec.ofNat 64 (0 + 1) := by decide
    have hsignq : (BitVec.signExtend 64 (BitVec.ofNat 64 q)).toNat = q := by
      rw [BitVec.signExtend_eq, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega : q < 2 ^ 64)]
    simp only [seedHeadReadCells, loopHeadReadCells, hb4, hb1v, hsignq, hk0,
      hinc, Nat.zero_mul, Nat.mul_zero, Nat.add_zero]
  -- the entry chain, as the base lookup table's cells
  have hbaseCellsEq :
      (entryHeadBlockState s0.env s0 K.scratch K.b K.n K.ep K.nep K.c K.e).env =
        cells (stage2NoEventWalkBaseCellValues K) s0.env :=
    entryHeadBlockState_baseCells h hnext hnepos
  have hlen : K.bs.length = K.n := by
    simpa using readBytes_length mem K.b K.n (bs := K.bs) h.doc
  have hw : K.arenaWord = 0 := by
    rw [← h.arenaEq, hKarena]; rfl
  have hblen : K.arena.length = 0 := by rw [hKarena]; rfl
  have hreadCellsAt : seedHeadReadCells bs4H (natToBytes (K.bs.getD q 0).toNat 1) K.ep K.b =
      loopHeadReadCellsAt K 0 0 0 0 520 q (K.bs.getD q 0) := by
    simpa only [loopHeadReadCellsAt] using hreadCells
  have hphiCells : loopHeadPhiCellsAt K 0 0 0 0 520 = loopHeadPhiCells := by
    simp only [loopHeadPhiCellsAt, loopHeadPhiCells, hKtok, hKterms, hw, hblen,
      List.cons.injEq, and_true, true_and, Prod.mk.injEq, BitVec.ofNat_eq_ofNat]
  have hreadAndPhi :
      (entryHeadState (entryHeadBlockState s0.env s0 K.scratch K.b K.n K.ep K.nep K.c K.e)
        (BitVec.ofNat 64 0) bs4H K.ep K.b
        (natToBytes (K.bs.getD q 0).toNat 1)).env =
        cells (loopHeadReadCellsAt K 0 0 0 0 520 q (K.bs.getD q 0))
          (cells (loopHeadPhiCellsAt K 0 0 0 0 520)
            (entryHeadBlockState s0.env s0 K.scratch K.b K.n K.ep K.nep K.c K.e).env) := by
    show entryHeadEnv
        (entryHeadBlockState s0.env s0 K.scratch K.b K.n K.ep K.nep K.c K.e).env
        (BitVec.ofNat 64 0) bs4H K.ep K.b
        (natToBytes (K.bs.getD q 0).toNat 1) = _
    rw [entryHeadEnv_cells, hreadCellsAt, ← hphiCells]
  -- the base lookups at the seed's entry chain
  have hbaseRest : ∀ n v, (n, v) ∈ stage2NoEventWalkBaseValues K →
      lookupName (entryHeadBlockState s0.env s0 K.scratch K.b K.n K.ep K.nep K.c K.e).env n =
        some v := by
    intro n v hv
    rcases List.mem_append.mp hv with hparam | hcell
    · have hn : n ∈ stage2NoEventWalkHeadParamNames := by
        have hmem : n ∈ (stage2NoEventWalkParamEntries K).map (·.1) :=
          List.mem_map.mpr ⟨(n, v), hparam, rfl⟩
        simpa only [stage2NoEventWalkParamEntries_names] using hmem
      have hnotin : n ∉ (stage2NoEventWalkBaseCellValues K).map (·.1) := by
        rw [stage2NoEventWalkBaseCellValues_names]
        intro hm
        have hdisj : (stage2NoEventWalkHeadParamNames ++
            stage2NoEventWalkBaseCellNames).Nodup := by decide
        exact (List.nodup_append.mp hdisj).2.2 n hn n hm rfl
      rw [hbaseCellsEq, cells_lookup_of_notin _ _ hnotin]
      exact Stage2NoEventWalkParams.lookup_entry hpar n v hparam
    · rw [hbaseCellsEq]
      exact cells_lookup_of_mem _ _ hcell (by
        rw [stage2NoEventWalkBaseCellValues_names]; decide)
  -- and through the head's exact layers
  have hbaseHead : Stage2NoEventWalkBaseLookups K
      (entryHeadState (entryHeadBlockState s0.env s0 K.scratch K.b K.n K.ep K.nep K.c K.e)
        (BitVec.ofNat 64 0) bs4H K.ep K.b
        (natToBytes (K.bs.getD q 0).toNat 1)) := by
    intro n v hv
    have hn : n ∈ stage2NoEventWalkBaseNames := by
      have hmem : n ∈ (stage2NoEventWalkBaseValues K).map (·.1) :=
        List.mem_map.mpr ⟨(n, v), hv, rfl⟩
      simpa only [stage2NoEventWalkBaseValues_names] using hmem
    have hnotin : n ∉ (loopHeadReadCellNames ++ loopHeadPhiCellNames) := by
      intro hm
      exact (List.nodup_append.mp stage2NoEventWalkHeadRegs_nodup).2.2 n hn n hm rfl
    rw [hreadAndPhi]
    rw [cells_lookup_of_notin _ _ (by
      rw [loopHeadReadCellsAt_names]
      exact fun hm => hnotin (List.mem_append_left _ hm))]
    rw [cells_lookup_of_notin _ _ (by
      rw [loopHeadPhiCellsAt_names]
      exact fun hm => hnotin (List.mem_append_right _ hm))]
    exact hbaseRest n v hv
  refine ⟨entryHeadState (entryHeadBlockState s0.env s0 K.scratch K.b K.n K.ep K.nep K.c K.e)
      (BitVec.ofNat 64 0) bs4H K.ep K.b (natToBytes (K.bs.getD q 0).toNat 1), q,
      K.bs.getD q 0, ?_, ?_, ?_, ?_⟩
  · -- the three-step run
    intro n
    have e1 : runFuel (stage2NoEventCalls gap) (3 + n) stage2NoEventBody s0 =
        runFuel (stage2NoEventCalls gap) (2 + n) stage2NoEventBody
          (entryPreheaderState s0.env s0 K.b K.n K.ep K.nep K.c K.e) := by
      rw [show 3 + n = (2 + n) + 1 from by omega]
      simp only [runFuel, hstep1]
    rw [e1]
    have e2 : runFuel (stage2NoEventCalls gap) (2 + n) stage2NoEventBody
          (entryPreheaderState s0.env s0 K.b K.n K.ep K.nep K.c K.e) =
        runFuel (stage2NoEventCalls gap) (1 + n) stage2NoEventBody
          (entryHeadBlockState s0.env s0 K.scratch K.b K.n K.ep K.nep K.c K.e) := by
      rw [show 2 + n = (1 + n) + 1 from by omega]
      simp only [runFuel, hstep2]
    rw [e2]
    have e3 : runFuel (stage2NoEventCalls gap) (1 + n) stage2NoEventBody
          (entryHeadBlockState s0.env s0 K.scratch K.b K.n K.ep K.nep K.c K.e) =
        runFuel (stage2NoEventCalls gap) n stage2NoEventBody
          (entryHeadState (entryHeadBlockState s0.env s0 K.scratch K.b K.n K.ep K.nep K.c K.e)
            (BitVec.ofNat 64 0) bs4H K.ep K.b (natToBytes (K.bs.getD q 0).toNat 1)) := by
      rw [show 1 + n = n + 1 from by omega]
      simp only [runFuel, hlink.step]
      rw [entryHeadState_eq]
      rfl
    rw [e3]
  · -- the head: the invariant, the exact layers, and the base lookups
    refine
      { inv := hinvHead.mem_congr (entryHeadState_mem _ _ _ _ _ _)
        pc := rfl
        klt := hnepos
        bPos := hb1
        layers := ?_
        baseLookups := hbaseHead }
    refine ⟨(entryHeadBlockState s0.env s0 K.scratch K.b K.n K.ep K.nep K.c K.e).env,
      0, 0, 0, 520, q, K.bs.getD q 0, hreadAndPhi, hlaneH0,
      (by rw [← hb4]; exact hb4lt), ?_, ?_, ?_, ?_, rfl, ?_⟩
    · -- the entry's byte at the lane
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some]
    · -- the byte read at the lane
      rw [entryHeadState_mem, hbyteH, seed_natToBytes_one]
    · -- the depth is a 32-bit word
      decide
    · -- the frame is an 8-bit word
      decide
    · -- the trip count's budget
      decide
  · -- the output evidence: the empty prefix
    exact Stage2NoEventWalkTrace.intro [] [] .nil (by rw [hKtok]; rfl)
      (by rw [hKterms]; rfl) (by intro e he; simp at he)
  · -- the head's environment, at the seed's entry chain
    exact hreadAndPhi

/-! ### F2 — the loop's accumulator is not inhabitable at the seed's head

The old exit required the loop's `Stage2NoEventWalkAcc` at the head the row was
stated at.  That structure's cells are the loop-exit merge's
(`%idxprom.lcssa`, `%tokens.8`, `%terms.8`, `%arena.10`); the seed's first head
binds none of them — its environment is the six read cells over the nine `phi`
cells over the entry chain, and none of the four names is in any of those layers
or in the entry environment.  So no accumulator is inhabitable at the seed's own
head, and an exit stated at the head cannot be filled from it; the acceptance's
three words and the refusal's own registers are read at the terminal state
instead. -/

/-- **F2: the seed's head has no loop accumulator.**  At any state the seed runs
from, whose environment binds none of the accumulator's four names, the run's
`NodeBlock5` head carries the index at zero and none of `%idxprom.lcssa`,
`%tokens.8`, `%terms.8`, `%arena.10`; hence no `Stage2NoEventWalkAcc` is
inhabitable there. -/
theorem stage2NoEventWalkF2_witness {gap : Calls} {K : Stage2NoEventWalkCarry}
    {mem : Mem} {s0 : State}
    (h : Stage2NoEventWalkInv K mem s0) (hpar : Stage2NoEventWalkParams K s0)
    (hpc : s0.pc = "entry") (hnext : s0.next = K.next0) (hxj : K.xj = K.next0)
    (hb1 : 1 ≤ K.b) (hnepos : 0 < K.nep)
    (hKtok : K.tok = 0) (hKterms : K.terms = 0) (hKarena : K.arena = [])
    (hclean : lookupName s0.env "%idxprom.lcssa" = none ∧
      lookupName s0.env "%tokens.8" = none ∧
      lookupName s0.env "%terms.8" = none ∧
      lookupName s0.env "%arena.10" = none) :
    ∃ sHead : State,
      Stage2NoEventWalkHead K mem 0 sHead ∧
      sHead.pc = "NodeBlock5" ∧
      lookupName sHead.env "%k.0.ph1404" = some (.int 64 0) ∧
      lookupName sHead.env "%idxprom.lcssa" = none ∧
      lookupName sHead.env "%tokens.8" = none ∧
      lookupName sHead.env "%terms.8" = none ∧
      lookupName sHead.env "%arena.10" = none ∧
      ∀ K', ¬ Stage2NoEventWalkAcc K' sHead := by
  obtain ⟨sHead, lane, byte, -, hhead, -, henvEq⟩ :=
    stage2NoEventWalkSeedRun (gap := gap) h hpar hpc hnext hxj hb1 hnepos
      hKtok hKterms hKarena
  -- the four names are not names of the head's cell layers or its base cells
  have hfour : (["%idxprom.lcssa", "%tokens.8", "%terms.8", "%arena.10"] ++
      (loopHeadReadCellNames ++ loopHeadPhiCellNames ++
        stage2NoEventWalkBaseCellNames)).Nodup := by decide
  have habs : ∀ n, n ∈ ["%idxprom.lcssa", "%tokens.8", "%terms.8", "%arena.10"] →
      lookupName sHead.env n = none := by
    intro n hn
    have hrest : n ∉ (loopHeadReadCellNames ++ loopHeadPhiCellNames ++
        stage2NoEventWalkBaseCellNames) := by
      intro hm
      exact (List.nodup_append.mp hfour).2.2 n hn n hm rfl
    have hnread : n ∉ loopHeadReadCellNames :=
      fun hm => hrest (List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl hm))))
    have hnphi : n ∉ loopHeadPhiCellNames :=
      fun hm => hrest (List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr hm))))
    have hnbase : n ∉ stage2NoEventWalkBaseCellNames :=
      fun hm => hrest (List.mem_append.mpr (Or.inr hm))
    have hnone : lookupName s0.env n = none := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
      rcases hn with rfl | rfl | rfl | rfl
      · exact hclean.1
      · exact hclean.2.1
      · exact hclean.2.2.1
      · exact hclean.2.2.2
    rw [henvEq]
    rw [cells_lookup_of_notin _ _ (by rw [loopHeadReadCellsAt_names]; exact hnread)]
    rw [cells_lookup_of_notin _ _ (by rw [loopHeadPhiCellsAt_names]; exact hnphi)]
    rw [entryHeadBlockState_baseCells h hnext hnepos]
    rw [cells_lookup_of_notin _ _ (by
      rw [stage2NoEventWalkBaseCellValues_names]; exact hnbase)]
    exact hnone
  have hpos := habs "%idxprom.lcssa" (by simp)
  have htok := habs "%tokens.8" (by simp)
  have hterms := habs "%terms.8" (by simp)
  have harena := habs "%arena.10" (by simp)
  refine ⟨sHead, hhead, hhead.pc, hhead.kEq, hpos, htok, hterms, harena, ?_⟩
  intro K' hacc
  have ht : lookupName sHead.env "%tokens.8" =
      some (.int 64 (BitVec.ofNat 64 K'.tok)) := hacc.tokens
  rw [htok] at ht
  cases ht

/-- **A name outside a parameter list is absent from its zip with the
arguments.**  `EntryState`'s environment is exactly that zip, so this is the
entry state's absence fact. -/
theorem lookupName_zip_map_none :
    ∀ (ps : List (String × Ty)) (args : List Value) {n : String},
      n ∉ ps.map (·.1) →
      lookupName ((ps.zip args).map (fun (v, a) => (v.1, a))) n = none
  | [], _, _, _ => rfl
  | p :: ps, args, n, h => by
      cases args with
      | nil => rfl
      | cons a as =>
          simp only [List.zip_cons_cons, List.map_cons, lookupName]
          have hp : p.1 ≠ n := by
            intro hpn
            exact h (by simp [hpn])
          rw [if_neg hp]
          exact lookupName_zip_map_none ps as (fun hmem => h (by simp [hmem]))

/-- **A name outside a function's parameter list is absent at its entry
state.** -/
theorem lookupName_entryState_none {f : Function} {args : List Value} {mem : Mem}
    {next : Nat} {n : String} (h : n ∉ f.params.map (·.1)) :
    lookupName (EntryState f args mem next).env n = none :=
  lookupName_zip_map_none f.params args h

/-- **F2 at the record's own entry state**: the seed's head there binds none of
the loop accumulator's four names, because none of them is a parameter. -/
theorem stage2NoEventWalkF2_atEntry {gap : Calls} {a12 : List Value}
    {stk e c d : Nat} {K : Stage2NoEventWalkCarry} {mem : Mem} {next : Nat}
    (h : Stage2NoEventWalkInv K mem
      (EntryState stage2NoEventBody (stage2NoEventArgs a12 stk e c d) mem next))
    (hpar : Stage2NoEventWalkParams K
      (EntryState stage2NoEventBody (stage2NoEventArgs a12 stk e c d) mem next))
    (hnext : next = K.next0) (hxj : K.xj = K.next0) (hb1 : 1 ≤ K.b)
    (hnepos : 0 < K.nep)
    (hKtok : K.tok = 0) (hKterms : K.terms = 0) (hKarena : K.arena = []) :
    ∃ sHead : State,
      Stage2NoEventWalkHead K mem 0 sHead ∧
      sHead.pc = "NodeBlock5" ∧
      lookupName sHead.env "%k.0.ph1404" = some (.int 64 0) ∧
      lookupName sHead.env "%idxprom.lcssa" = none ∧
      lookupName sHead.env "%tokens.8" = none ∧
      lookupName sHead.env "%terms.8" = none ∧
      lookupName sHead.env "%arena.10" = none ∧
      ∀ K', ¬ Stage2NoEventWalkAcc K' sHead := by
  refine stage2NoEventWalkF2_witness (gap := gap) (s0 := EntryState stage2NoEventBody
    (stage2NoEventArgs a12 stk e c d) mem next) h hpar rfl ?_ hxj hb1 hnepos
    hKtok hKterms hKarena ⟨?_, ?_, ?_, ?_⟩
  · simpa only [EntryState] using hnext
  · exact lookupName_entryState_none (by simp [stage2NoEventBody])
  · exact lookupName_entryState_none (by simp [stage2NoEventBody])
  · exact lookupName_entryState_none (by simp [stage2NoEventBody])
  · exact lookupName_entryState_none (by simp [stage2NoEventBody])

/-! ### Axiom footprints -/

#print axioms Stage2NoEventWalkInv.readBytes_off
#print axioms Stage2NoEventWalkInv.readLanes_off
#print axioms entryBlock_step_preheader
#print axioms entryPreheader_step
#print axioms stage2NoEventWalkSeedRun
#print axioms stage2NoEventWalkF2_witness
#print axioms lookupName_zip_map_none
#print axioms lookupName_entryState_none
#print axioms stage2NoEventWalkF2_atEntry

end LeanLLVM.Refinement
