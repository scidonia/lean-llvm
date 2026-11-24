/-
The no-event walk's counted segments, its credit, and the flush route.

`JsonStage2NoEventWalkLoop`/`WalkClose` prove the loop's rows block by block, each
ending at a named state; the walk's completion consumes chains of those rows.  This
module states the counted unit the completion is built from — the analogue of the
certified walk's `WalkSegment` — and the empty-document route end to end:

* a **segment** is a count and the `runFuel` equality at that count, from one
  invariant-carrying state to another.  It is weaker than a chain (nothing about
  the links survives) and it is what a loop step's continuing branch and the base
  step state; `of_chain` is where a chain of links re-enters, `trans` adds counts,
  and `ret` completes at the count plus the returning step;
* a **priced segment** adds the potential's credit: `p + Φ(K′, k′) ≤ Φ(K, k)`.
  `Φ` is the walk's remaining budget read as credit at the state's head index `k`
  (`ent.getD k 0`, no new invariant field).  The flush route does
  not consume the credit — it leaves the loop — but the loop step's
  `Stage2NoEventWalkStep` produces priced segments, so the shape and its
  arithmetic live here;
* the **flush route** is the `nep = 0` arm: the entry block's test takes its true
  arm straight to `if.then`, and the terminal module's flush run completes there.
  The route is priced at the entry block's one step plus the flush arm's two,
  `stage2NoEventFlushSteps`.

**The entry block is composed, not re-derived.**  The bootstrap's twelve
instructions are the terminal module's atomic rows by its own proof's shape; the
suffix is the five sub-rows `WalkClose` proves, composed by
`denoteCode_append_apply`.  The two are joined once (`entryBlock_denote`) and the
block's terminator runs as `execTerm`, which is the tree's one-step contract
(`step`).  The invariant is carried across each write by
`Stage2NoEventWalkInv.stack_write`, whose region list is the run's own regions
plus the stack interval — the bootstrap's `%xj` write is the interval's.

**What this module does not do.**  It does not state the loop step at the head,
the potential's consumption across a revolution, or the completion from the
seed — the segment, the potential and the flush route are the vocabulary those
consume.  The exit evidence the acceptance arm needs is not part of the segment
interface: `Stage2NoEventWalkAcc`'s three accumulators, the parse relation and the
fold facts are supplied by the exit tier, beside the `Inv`, `Params` and `Locals`
the flush route reads.  The count class's return to the head is likewise not
stated here; `of_chain` and the priced segment's credit are the interface it
composes into, and the cycle-closing row is where a chain's count becomes a
segment's price.  The counts this module names — `stage2NoEventEntrySteps`,
`stage2NoEventFlushArmSteps`, `stage2NoEventFlushSteps` — are the base prices the
loop's budget arithmetic reads.

**`1 ≤ b`.**  The entry suffix computes `%invariant.gep1068 = %b - 1`; modelling
that instruction at the Nat address it delivers needs the base at least one, since
at `b = 0` the LLVM address wraps.  The suffix row already takes the
premise (`entryA4_denote`), and the record's `pre` does not state it, so the route
carries it visibly as a hypothesis rather than hiding it inside an unfolding. -/
import LeanLLVM.Refinement.JsonStage2NoEventWalkClose

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 800000

namespace LeanLLVM.Refinement

open LeanLLVM
open LeanLLVM.Refinement.JsonStage2NoEventIR
open LeanLLVM.Refinement.BlockEval

/-! ### Lookups through the builder

`cells` is a right fold whose cons equation is definitional.  The two lemmas
below are restated here (the canonical copies are `PipelineBodyStep`'s and
`JsonStage2WalkScopeGeom`'s) so this module depends on no unrelated import for
them; both are private, so the family's public names are not shadowed. -/

private theorem stage2NoEventSegCells_some :
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
        exact stage2NoEventSegCells_some cs n env h

private theorem stage2NoEventSegCells_notin :
    ∀ (cs : List (String × Value)) (n : String) (env : Env),
      n ∉ cs.map (·.1) → lookupName (cells cs env) n = lookupName env n
  | [], _, _, _ => rfl
  | (k, v) :: cs, n, env, h => by
      have hk : k ≠ n := by intro hkn; exact h (by subst hkn; simp)
      simp only [cells, lookupName_cons_ne v (cells cs env) hk]
      exact stage2NoEventSegCells_notin cs n env (fun hc => h (List.mem_cons_of_mem _ hc))

/-! ### A counted segment -/

/-- **A counted segment of the walk's run**: `j` steps from `s` reach `s'` and
leave it exactly (for every further fuel), and the invariant holds at the target.

The count is the segment's own index, not an existential: a chain's step count is
always *some* `k` and cannot be projected (the chain is a `Prop`), so the price a
loop step states is a segment's index and `of_chain` is where a chain becomes
one.  This is the no-event `WalkSegment`: its carry is the invariant's own index,
so there is no staging field to keep equal. -/
structure Stage2NoEventWalkSegment (calls : Calls) (mem : Mem)
    (K : Stage2NoEventWalkCarry) (s : State)
    (K' : Stage2NoEventWalkCarry) (s' : State) (j : Nat) : Prop where
  /-- The run, at the segment's own count and every continuation. -/
  run : ∀ n, runFuel calls (j + n) stage2NoEventBody s =
    runFuel calls n stage2NoEventBody s'
  /-- The invariant at the segment's target. -/
  inv' : Stage2NoEventWalkInv K' mem s'

/-- **Segments compose**, and their counts add: the first's equality at the
second's count is the second's source. -/
theorem Stage2NoEventWalkSegment.trans {calls : Calls} {mem : Mem}
    {K K' K'' : Stage2NoEventWalkCarry} {s s' s'' : State} {j k : Nat}
    (h₁ : Stage2NoEventWalkSegment calls mem K s K' s' j)
    (h₂ : Stage2NoEventWalkSegment calls mem K' s' K'' s'' k) :
    Stage2NoEventWalkSegment calls mem K s K'' s'' (j + k) where
  run n := by
    rw [show j + k + n = j + (k + n) from by omega, h₁.run (k + n), h₂.run n]
  inv' := h₂.inv'

/-- **A chain is a segment, at the count `Stage2NoEventWalkChain.steps` names.** -/
theorem Stage2NoEventWalkSegment.of_chain {calls : Calls} {mem : Mem}
    {K K' : Stage2NoEventWalkCarry} {s s' : State}
    (h : Stage2NoEventWalkChain calls mem K s K' s') :
    ∃ j, Stage2NoEventWalkSegment calls mem K s K' s' j := by
  obtain ⟨j, hj⟩ := h.steps
  exact ⟨j, ⟨hj, Stage2NoEventWalkChain.inv h⟩⟩

/-- **A counted run that ends in a return.**  At a state whose step returns, the
segment's count plus one is the run's fuel, and every budget at least that
produces the outcome. -/
theorem Stage2NoEventWalkSegment.ret {calls : Calls} {mem : Mem}
    {K K' : Stage2NoEventWalkCarry} {s s' sret : State} {j : Nat} {v : Value}
    (h : Stage2NoEventWalkSegment calls mem K s K' s' j)
    (hret : step calls stage2NoEventBody s' = .ret v sret) :
    ∀ N, j + 1 ≤ N → runFuel calls N stage2NoEventBody s = some (.ret v sret.mem) := by
  intro N hN
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hN
  have hfin : runFuel calls (j + 1) stage2NoEventBody s = some (.ret v sret.mem) := by
    rw [h.run 1]
    simp only [runFuel, hret]
  exact runFuel_mono (d := d) hfin

/-! ### The credit

The walk's remaining budget at a head is one entry allowance for each entry not
yet dispatched and one byte allowance for each document byte not yet reached.  It
is read at the head index the state's `%k.0.ph1404` carries, so no
field is added to the frozen carry or invariant: `ent.getD k 0` is the entry
position at `k`, and `K.n - …` is the document left to reach. -/

/-- **The walk's credit at a head index.** -/
def stage2NoEventWalkPotential (K : Stage2NoEventWalkCarry) (k : Nat) : Nat :=
  32 * (K.nep - k) + 8 * (K.n - K.ent.getD k 0)

/-- The potential is monotone in the count, given that the entry positions do not
decrease — which the invariant's `order` supplies below the entry stream: a larger
`k` has less entry credit and has reached at least as many document bytes. -/
theorem stage2NoEventWalkPotential_le_of_le {K : Stage2NoEventWalkCarry} {k k' : Nat}
    (hk : k ≤ k') (hne : k' ≤ K.nep)
    (hent : K.ent.getD k 0 ≤ K.ent.getD k' 0) :
    stage2NoEventWalkPotential K k' ≤ stage2NoEventWalkPotential K k := by
  unfold stage2NoEventWalkPotential
  have h₁ : K.nep - k' ≤ K.nep - k := by omega
  have h₂ : 32 * (K.nep - k') ≤ 32 * (K.nep - k) := Nat.mul_le_mul_left 32 h₁
  have h₃ : K.n - K.ent.getD k' 0 ≤ K.n - K.ent.getD k 0 := by omega
  have h₄ : 8 * (K.n - K.ent.getD k' 0) ≤ 8 * (K.n - K.ent.getD k 0) :=
    Nat.mul_le_mul_left 8 h₃
  omega

/-- **A priced segment**: a counted segment with the potential's credit.  The
price `p` is the run's own count, and the credit is what the loop step's
arithmetic reads when it composes revolutions. -/
structure Stage2NoEventWalkPricedSegment (calls : Calls) (mem : Mem)
    (K : Stage2NoEventWalkCarry) (k : Nat) (s : State)
    (K' : Stage2NoEventWalkCarry) (k' : Nat) (s' : State) (p : Nat) : Prop where
  /-- The run, its count, and the invariant at its target. -/
  seg : Stage2NoEventWalkSegment calls mem K s K' s' p
  /-- The price is payable from the credit. -/
  credit : p + stage2NoEventWalkPotential K' k' ≤ stage2NoEventWalkPotential K k

/-- **Priced segments compose**, and so do their credits. -/
theorem Stage2NoEventWalkPricedSegment.trans {calls : Calls} {mem : Mem}
    {K K' K'' : Stage2NoEventWalkCarry} {k k' k'' : Nat} {s s' s'' : State}
    {p q : Nat}
    (h₁ : Stage2NoEventWalkPricedSegment calls mem K k s K' k' s' p)
    (h₂ : Stage2NoEventWalkPricedSegment calls mem K' k' s' K'' k'' s'' q) :
    Stage2NoEventWalkPricedSegment calls mem K k s K'' k'' s'' (p + q) where
  seg := h₁.seg.trans h₂.seg
  credit := by
    have := h₁.credit
    have := h₂.credit
    omega

/-! ### Lookups through the builder

`cells` is a right fold whose cons equation is definitional.  The canonical
copies are `PipelineBodyStep`'s (`:1702`) and `JsonStage2WalkScopeGeom`'s
(`:989`); this module restates the one it uses rather than importing either. -/

/-! ### The entry block

The block is the bootstrap's twelve instructions followed by the suffix's
seventeen; the terminal module's bootstrap and `WalkClose`'s five suffix sub-rows
are the pieces.  The bootstrap is re-stated at the state it concretely delivers —
the terminal module's own statement is existential in the target — so the
invariant can be carried across its writes. -/

/-- The bootstrap's cells: `%off`, `%ei`, `%outn205`, `%outn`, `%xj`. -/
def entryBootCells (s : State) (e : Nat) : List (String × Value) :=
  [("%off", .ptr (e + 8)), ("%ei", .ptr (s.next + 24)),
   ("%outn205", .ptr (s.next + 16)), ("%outn", .ptr (s.next + 8)),
   ("%xj", .ptr s.next)]

/-- The bootstrap's environment, over the environment the block was entered from. -/
def entryBootEnv (env : Env) (s : State) (e : Nat) : Env := cells (entryBootCells s e) env

/-- The bootstrap's memory: the `%xj` word, the record's kind, and `%off`. -/
def entryBootMem (m : Mem) (xj e : Nat) : Mem :=
  writeBytes
    (writeBytes
      (writeBytes m xj (natToBytes (BitVec.ofNat 64 0).toNat 8))
      e (natToBytes (BitVec.ofNat 32 1).toNat 4))
    (e + 8) (natToBytes (BitVec.ofNat 64 0).toNat 8)

/-- The bootstrap's state: the environment and memory above, the allocations'
thirty-two bytes, and the caller's block and predecessor. -/
def entryBootState (s : State) (e : Nat) : State :=
  { env := entryBootEnv s.env s e, mem := entryBootMem s.mem s.next e,
    next := s.next + 32, pc := s.pc, pre := s.pre }

/-- **The bootstrap's run, at the state it concretely delivers.** -/
theorem entryBootstrap_run {gap : Calls} (env : Env) (s : State) {stk e c : Nat}
    (hstk : lookupName env "%stk" = some (.ptr stk))
    (he : lookupName env "%e" = some (.ptr e))
    (hc : lookupName env "%c" = some (.ptr c)) :
    denoteCode (stage2NoEventCalls gap) entryBootstrapInstrs (stateAt env s) =
      some (stateAt (entryBootEnv env s e) (entryBootState s e)) := by
  unfold entryBootstrapInstrs
  rw [stage2NoEventWalk_denote_alloca (calls := stage2NoEventCalls gap)
    (env := env) (s := s) "%xj" (Ty.int 64) 0 8 (by decide)]
  generalize hS1 : stage2NoEventStepState s s.mem (s.next + 8) = S1
  rw [stage2NoEventWalk_denote_alloca (calls := stage2NoEventCalls gap)
    (env := ("%xj", .ptr s.next) :: env) (s := S1) "%outn" (Ty.int 64) 0 8
    (by decide)]
  generalize hS2 : stage2NoEventStepState S1 S1.mem (S1.next + 8) = S2
  rw [stage2NoEventWalk_denote_alloca (calls := stage2NoEventCalls gap)
    (env := ("%outn", .ptr S1.next) :: ("%xj", .ptr s.next) :: env) (s := S2)
    "%outn205" (Ty.int 64) 0 8 (by decide)]
  generalize hS3 : stage2NoEventStepState S2 S2.mem (S2.next + 8) = S3
  rw [stage2NoEventWalk_denote_alloca (calls := stage2NoEventCalls gap)
    (env := ("%outn205", .ptr S2.next) :: ("%outn", .ptr S1.next) ::
      ("%xj", .ptr s.next) :: env) (s := S3) "%ei" (Ty.int 64) 0 8
    (by decide)]
  generalize hS4 : stage2NoEventStepState S3 S3.mem (S3.next + 8) = S4
  rw [stage2NoEventWalk_denote_lifetimeStart (gap := gap)
    (env := ("%ei", .ptr S3.next) :: ("%outn205", .ptr S2.next) ::
      ("%outn", .ptr S1.next) :: ("%xj", .ptr s.next) :: env) (s := S4)
    "%xj" (sz := 8) (a := s.next)
    (lookupName_entryEnv_xj env S3.next S2.next S1.next s.next)]
  rw [stage2NoEventWalk_denote_store64_imm (calls := stage2NoEventCalls gap)
    (env := ("%ei", .ptr S3.next) :: ("%outn205", .ptr S2.next) ::
      ("%outn", .ptr S1.next) :: ("%xj", .ptr s.next) :: env) (s := S4)
    (x := (BitVec.ofNat 64 0)) (p := "%xj")
    (hp := lookupName_entryEnv_xj env S3.next S2.next S1.next s.next)]
  generalize hS5 : ({ env := S4.env, mem := writeBytes S4.mem s.next (natToBytes (BitVec.ofNat 64 0).toNat 8), next := S4.next, pc := S4.pc, pre := S4.pre } : State) = S5
  rw [stage2NoEventWalk_denote_lifetimeStart (gap := gap)
    (env := ("%ei", .ptr S3.next) :: ("%outn205", .ptr S2.next) ::
      ("%outn", .ptr S1.next) :: ("%xj", .ptr s.next) :: env) (s := S5)
    "%stk" (sz := 520) (a := stk)
    (lookupName_entryEnv_stk env S3.next S2.next S1.next s.next stk hstk)]
  rw [stage2NoEventWalk_denote_lifetimeStart (gap := gap)
    (env := ("%ei", .ptr S3.next) :: ("%outn205", .ptr S2.next) ::
      ("%outn", .ptr S1.next) :: ("%xj", .ptr s.next) :: env) (s := S5)
    "%e" (sz := 24) (a := e)
    (lookupName_entryEnv_e env S3.next S2.next S1.next s.next e he)]
  rw [stage2NoEventWalk_denote_lifetimeStart (gap := gap)
    (env := ("%ei", .ptr S3.next) :: ("%outn205", .ptr S2.next) ::
      ("%outn", .ptr S1.next) :: ("%xj", .ptr s.next) :: env) (s := S5)
    "%c" (sz := 1192) (a := c)
    (lookupName_entryEnv_c env S3.next S2.next S1.next s.next c hc)]
  rw [stage2NoEventWalk_denote_store32_imm (calls := stage2NoEventCalls gap)
    (env := ("%ei", .ptr S3.next) :: ("%outn205", .ptr S2.next) ::
      ("%outn", .ptr S1.next) :: ("%xj", .ptr s.next) :: env) (s := S5)
    (x := (BitVec.ofNat 32 1)) (p := "%e")
    (hp := lookupName_entryEnv_e env S3.next S2.next S1.next s.next e he)]
  generalize hS6 : stage2NoEventStepState S5
    (writeBytes S5.mem e (natToBytes (BitVec.ofNat 32 1).toNat 4)) S5.next = S6
  rw [stage2NoEventWalk_denote_gep8_imm (calls := stage2NoEventCalls gap)
    (env := ("%ei", .ptr S3.next) :: ("%outn205", .ptr S2.next) ::
      ("%outn", .ptr S1.next) :: ("%xj", .ptr s.next) :: env) (s := S6)
    "%off" "%e" (BitVec.ofNat 64 8) (a := e) (bytes := 8)
    (lookupName_entryEnv_e env S3.next S2.next S1.next s.next e he)
    (by decide) (by decide)]
  rw [stage2NoEventWalk_denote_store64_imm (calls := stage2NoEventCalls gap)
    (env := ("%off", .ptr (e + 8)) ::
      ("%ei", .ptr S3.next) :: ("%outn205", .ptr S2.next) ::
      ("%outn", .ptr S1.next) :: ("%xj", .ptr s.next) :: env) (s := S6)
    (x := (BitVec.ofNat 64 0)) (p := "%off") (a := e + 8)
    (hp := by simp only [lookupName_cons_self])]
  generalize hS7 : ({ env := S6.env, mem := writeBytes S6.mem (e + 8) (natToBytes (BitVec.ofNat 64 0).toNat 8), next := S6.next, pc := S6.pc, pre := S6.pre } : State) = S7
  rw [denoteCode_nil]
  rw [← hS7, ← hS6, ← hS5, ← hS4, ← hS3, ← hS2, ← hS1]
  simp only [stage2NoEventStepState, entryBootState, entryBootEnv, entryBootCells,
    entryBootMem, cells, stateAt]

/-! ### The entry block pinned and composed

The block's instruction list is the bootstrap's twelve and the suffix's seventeen;
the suffix's five sub-rows are `WalkClose`'s, the bootstrap's twelve this module's
concrete run.  The two are joined by `denoteCode_append` once, and the terminator
runs as `execTerm`, which is `step`'s contract. -/

/-- The entry block's own instruction list. -/
def entryBlock : Block :=
  { name := "entry", instrs := entryBootstrapInstrs ++ entrySuffixInstrs,
    term := Term.condbr (Operand.reg "%cmp.not.peel1401.not") "if.then"
      "if.end.peel.preheader" }

theorem entryBlock_find :
    stage2NoEventBody.findBlock "entry" = some entryBlock := by
  decide

/-- The suffix's cells. -/
def entrySuffixCells (b _n ep nep c e : Nat) : List (String × Value) :=
  entryCells5 nep ++ entryCells4 b c ++ entryCells3 ep c ++ entryCells2 b c ++
    entryCells1 c e

/-- The suffix's memory, over the bootstrap's. -/
def entrySuffixMem (m : Mem) (b n ep nep c e : Nat) : Mem :=
  writeBytes
    (writeBytes
      (writeBytes
        (writeBytes
          (writeBytes (entryMem1 c e m) c (natToBytes b 8))
          (c + 8) (natToBytes (BitVec.ofNat 64 n).toNat 8))
        (c + 16) (natToBytes ep 8))
      (c + 24) (natToBytes (BitVec.ofNat 64 nep).toNat 8))
    (c + 1112) (natToBytes e 8)

/-- The entry block's state after its instructions, before its terminator. -/
def entryBlockPost (env : Env) (s : State) (b n ep nep c e : Nat) : State :=
  { env := cells (entrySuffixCells b n ep nep c e) (entryBootEnv env s e),
    mem := entrySuffixMem (entryBootMem s.mem s.next e) b n ep nep c e,
    next := s.next + 32, pc := s.pc, pre := s.pre }

/-- **The entry block's instructions, as one denotation.** -/
theorem entryBlock_denote {gap : Calls} (env : Env) (s : State)
    {b n ep nep c e stk : Nat}
    (hb : lookupName env "%b" = some (.ptr b))
    (hn : lookupName env "%n" = some (.int 64 (BitVec.ofNat 64 n)))
    (hep : lookupName env "%ep" = some (.ptr ep))
    (hnep : lookupName env "%nep" = some (.int 64 (BitVec.ofNat 64 nep)))
    (hc : lookupName env "%c" = some (.ptr c))
    (he : lookupName env "%e" = some (.ptr e))
    (hstk : lookupName env "%stk" = some (.ptr stk))
    (hb1 : 1 ≤ b) :
    denoteCode (stage2NoEventCalls gap) entryBlock.instrs (stateAt env s) =
      some (stateAt (cells (entrySuffixCells b n ep nep c e) (entryBootEnv env s e))
        (entryBlockPost env s b n ep nep c e)) := by
  have hb' : lookupName (entryBootEnv env s e) "%b" = some (.ptr b) := by
    rw [entryBootEnv, stage2NoEventSegCells_notin (cs := entryBootCells s e)
      (n := "%b") (env := env) (by simp [entryBootCells])]
    exact hb
  have hn' : lookupName (entryBootEnv env s e) "%n" =
      some (.int 64 (BitVec.ofNat 64 n)) := by
    rw [entryBootEnv, stage2NoEventSegCells_notin (cs := entryBootCells s e)
      (n := "%n") (env := env) (by simp [entryBootCells])]
    exact hn
  have hep' : lookupName (entryBootEnv env s e) "%ep" = some (.ptr ep) := by
    rw [entryBootEnv, stage2NoEventSegCells_notin (cs := entryBootCells s e)
      (n := "%ep") (env := env) (by simp [entryBootCells])]
    exact hep
  have hnep' : lookupName (entryBootEnv env s e) "%nep" =
      some (.int 64 (BitVec.ofNat 64 nep)) := by
    rw [entryBootEnv, stage2NoEventSegCells_notin (cs := entryBootCells s e)
      (n := "%nep") (env := env) (by simp [entryBootCells])]
    exact hnep
  have hc' : lookupName (entryBootEnv env s e) "%c" = some (.ptr c) := by
    rw [entryBootEnv, stage2NoEventSegCells_notin (cs := entryBootCells s e)
      (n := "%c") (env := env) (by simp [entryBootCells])]
    exact hc
  have he' : lookupName (entryBootEnv env s e) "%e" = some (.ptr e) := by
    rw [entryBootEnv, stage2NoEventSegCells_notin (cs := entryBootCells s e)
      (n := "%e") (env := env) (by simp [entryBootCells])]
    exact he
  have hentry := entryBlock
  rw [show entryBlock.instrs = entryBootstrapInstrs ++ entrySuffixInstrs from rfl]
  rw [LeanLLVM.Refinement.JsonEntrySteps.denoteCode_append (calls := stage2NoEventCalls gap)
    (a := entryBootstrapInstrs) (b := entrySuffixInstrs) (s := stateAt env s)
    (hb := by decide)]
  rw [entryBootstrap_run (gap := gap) (env := env) (s := s) hstk he hc]
  simp only [Option.bind]
  rw [entrySuffix_denote (gap := gap) (env := entryBootEnv env s e)
    (s := entryBootState s e) hb' hn' hep' hnep' hc' he' hb1]
  simp only [stateAt, entryBlockPost, entrySuffixCells, entrySuffixMem,
    entryBootState, entryBootMem, stage2NoEventStepState]

/-- The entry block's hand-off environment: the suffix's own, which already binds
the terminator's condition cell.  `execTerm` reads it and leaves the environment
as the block's run did. -/
def entryFlushEnv (env : Env) (s : State) (b n ep nep c e : Nat) : Env :=
  cells (entrySuffixCells b n ep nep c e) (entryBootEnv env s e)

/-- The entry block's terminator, at the empty document: the true arm. -/
theorem entryBlock_term_flush (env : Env) (s : State)
    {b n ep nep c e : Nat}
    (hnep0 : nep = 0) :
    execTerm
        (stateAt (cells (entrySuffixCells b n ep nep c e) (entryBootEnv env s e))
          (entryBlockPost env s b n ep nep c e))
        (.condbr (.reg "%cmp.not.peel1401.not") "if.then" "if.end.peel.preheader") =
      .jump
        { env := entryFlushEnv env s b n ep nep c e,
          mem := entrySuffixMem (entryBootMem s.mem s.next e) b n ep nep c e,
          next := s.next + 32, pc := "if.then", pre := some s.pc } := by
  subst hnep0
  simp only [execTerm, stateAt, evalOperand, entrySuffixCells, entryCells5, cells,
    List.cons_append, List.nil_append, lookupName_cons_self,
    show evalICmp .eq (BitVec.ofNat 64 0) (BitVec.ofNat 64 0) =
      BitVec.ofNat 1 1 from by decide]
  rw [ite_eq_left (by decide)]
  simp only [entryBlockPost, entryFlushEnv, entrySuffixCells, entrySuffixMem,
    entryCells5, cells, List.cons_append, List.nil_append,
    show evalICmp .eq (BitVec.ofNat 64 0) (BitVec.ofNat 64 0) =
      BitVec.ofNat 1 1 from by decide]

/-- The state the entry block hands the flush arm. -/
def entryFlushState (env : Env) (s : State) (b n ep nep c e : Nat) : State :=
  { env := entryFlushEnv env s b n ep nep c e,
    mem := entrySuffixMem (entryBootMem s.mem s.next e) b n ep nep c e,
    next := s.next + 32, pc := "if.then", pre := some s.pc }

/-- **One entry step to `if.then`**, at `nep = 0`. -/
theorem entryBlock_step {gap : Calls} (env : Env) (s : State)
    {b n ep nep c e stk : Nat}
    (hb : lookupName env "%b" = some (.ptr b))
    (hn : lookupName env "%n" = some (.int 64 (BitVec.ofNat 64 n)))
    (hep : lookupName env "%ep" = some (.ptr ep))
    (hnep : lookupName env "%nep" = some (.int 64 (BitVec.ofNat 64 nep)))
    (hc : lookupName env "%c" = some (.ptr c))
    (he : lookupName env "%e" = some (.ptr e))
    (hstk : lookupName env "%stk" = some (.ptr stk))
    (hb1 : 1 ≤ b) (hpc : s.pc = "entry") (hnep0 : nep = 0) :
    step (stage2NoEventCalls gap) stage2NoEventBody (stateAt env s) =
      .jump (entryFlushState env s b n ep nep c e) := by
  unfold step
  rw [show (stateAt env s).pc = "entry" from hpc]
  simp only [entryBlock_find]
  rw [entryBlock_denote (gap := gap) (env := env) (s := s) hb hn hep hnep hc he hstk hb1]
  exact entryBlock_term_flush (env := env) (s := s) hnep0

/-! ### Carrying the invariant across the entry block -/

/-- **A write inside the run's own regions.**  `stack_write` at the state the
write leaves; the state's cursor, environment and predecessor are not the
invariant's business. -/
theorem Stage2NoEventWalkInv.write {K : Stage2NoEventWalkCarry} {mem : Mem} {s : State}
    (h : Stage2NoEventWalkInv K mem s) {a : Nat} {bs : List UInt8}
    (hw : ∀ k, k < bs.length → inRegions
      (stage2NoEventRunRegions K.scratch K.scratchcap K.stk K.e K.c K.d ++
        [(K.next0, K.nextEnd - K.next0)]) (a + k)) :
    Stage2NoEventWalkInv K mem
      (stage2NoEventStepState s (writeBytes s.mem a bs) s.next) :=
  (Stage2NoEventWalkInv.stack_write h hw).mem_congr rfl

private theorem inRunRegions_of_mem {K : Stage2NoEventWalkCarry} {r : Nat × Nat}
    (hr : r ∈ stage2NoEventRunRegions K.scratch K.scratchcap K.stk K.e K.c K.d)
    {a len : Nat} (hlo : r.1 ≤ a) (hhi : a + len ≤ r.1 + r.2) :
    ∀ k, k < len → inRegions
      (stage2NoEventRunRegions K.scratch K.scratchcap K.stk K.e K.c K.d ++
        [(K.next0, K.nextEnd - K.next0)]) (a + k) := by
  intro k hk
  exact ⟨r, List.mem_append_left _ hr, by omega, by omega⟩

private theorem inRunRegions_interval {K : Stage2NoEventWalkCarry} {a len : Nat}
    (hlo : K.next0 ≤ a) (hhi : a + len ≤ K.nextEnd) :
    ∀ k, k < len → inRegions
      (stage2NoEventRunRegions K.scratch K.scratchcap K.stk K.e K.c K.d ++
        [(K.next0, K.nextEnd - K.next0)]) (a + k) := by
  intro k hk
  exact ⟨(K.next0, K.nextEnd - K.next0), List.mem_append_right _ (by simp),
    by omega, by omega⟩

/-- **The invariant survives the entry block.**  The bootstrap's three stores and
the suffix's seven are each inside the run's regions or the stack interval, so
`stack_write` carries the frame and the presence across them in order. -/
theorem entryBlock_inv {K : Stage2NoEventWalkCarry} {mem : Mem} {s : State}
    (h : Stage2NoEventWalkInv K mem s) (hnext : s.next = K.next0) :
    Stage2NoEventWalkInv K mem
      (entryFlushState s.env s K.b K.n K.ep K.nep K.c K.e) := by
  have hstat : K.next0 + 8 ≤ K.nextEnd := by
    have := h.nextEnd_static
    simp only [stage2BootstrapExtent] at this
    omega
  have hxj : ∀ k, k < (natToBytes (BitVec.ofNat 64 0).toNat 8).length →
      inRegions (stage2NoEventRunRegions K.scratch K.scratchcap K.stk K.e K.c K.d ++
        [(K.next0, K.nextEnd - K.next0)]) (s.next + k) := by
    simpa only [natToBytes_length] using
      (inRunRegions_interval (K := K) (a := s.next) (len := 8)
        (by omega) (by omega))
  have he4 : ∀ k, k < (natToBytes (BitVec.ofNat 32 1).toNat 4).length →
      inRegions (stage2NoEventRunRegions K.scratch K.scratchcap K.stk K.e K.c K.d ++
        [(K.next0, K.nextEnd - K.next0)]) (K.e + k) := by
    simpa only [natToBytes_length] using
      (inRunRegions_of_mem (K := K) (r := (K.e, stage2NoEventErrorExtent))
        (by simp [stage2NoEventRunRegions, stage2NoEventStagedRegions])
        (a := K.e) (len := 4) (by omega) (by simp [stage2NoEventErrorExtent]))
  have he8 : ∀ k, k < (natToBytes (BitVec.ofNat 64 0).toNat 8).length →
      inRegions (stage2NoEventRunRegions K.scratch K.scratchcap K.stk K.e K.c K.d ++
        [(K.next0, K.nextEnd - K.next0)]) (K.e + 8 + k) := by
    simpa only [natToBytes_length] using
      (inRunRegions_of_mem (K := K) (r := (K.e, stage2NoEventErrorExtent))
        (by simp [stage2NoEventRunRegions, stage2NoEventStagedRegions])
        (a := K.e + 8) (len := 8) (by omega) (by simp [stage2NoEventErrorExtent]))
  have he16 : ∀ k, k < (natToBytes 0 8).length →
      inRegions (stage2NoEventRunRegions K.scratch K.scratchcap K.stk K.e K.c K.d ++
        [(K.next0, K.nextEnd - K.next0)]) (K.e + 16 + k) := by
    simpa only [natToBytes_length] using
      (inRunRegions_of_mem (K := K) (r := (K.e, stage2NoEventErrorExtent))
        (by simp [stage2NoEventRunRegions, stage2NoEventStagedRegions])
        (a := K.e + 16) (len := 8) (by omega) (by simp [stage2NoEventErrorExtent]))
  have hc1160 : ∀ k, k < (List.replicate 1160 (0 : UInt8)).length →
      inRegions (stage2NoEventRunRegions K.scratch K.scratchcap K.stk K.e K.c K.d ++
        [(K.next0, K.nextEnd - K.next0)]) (K.c + 32 + k) := by
    simpa only [List.length_replicate] using
      (inRunRegions_of_mem (K := K) (r := (K.c, stage2NoEventCursorExtent))
        (by simp [stage2NoEventRunRegions, stage2NoEventStagedRegions])
        (a := K.c + 32) (len := 1160) (by omega)
        (by simp [stage2NoEventCursorExtent]))
  have hc8 : ∀ k, k < (natToBytes K.b 8).length →
      inRegions (stage2NoEventRunRegions K.scratch K.scratchcap K.stk K.e K.c K.d ++
        [(K.next0, K.nextEnd - K.next0)]) (K.c + k) := by
    simpa only [natToBytes_length] using
      (inRunRegions_of_mem (K := K) (r := (K.c, stage2NoEventCursorExtent))
        (by simp [stage2NoEventRunRegions, stage2NoEventStagedRegions])
        (a := K.c) (len := 8) (by omega) (by simp [stage2NoEventCursorExtent]))
  have hcn : ∀ k, k < (natToBytes (BitVec.ofNat 64 K.n).toNat 8).length →
      inRegions (stage2NoEventRunRegions K.scratch K.scratchcap K.stk K.e K.c K.d ++
        [(K.next0, K.nextEnd - K.next0)]) (K.c + 8 + k) := by
    simpa only [natToBytes_length] using
      (inRunRegions_of_mem (K := K) (r := (K.c, stage2NoEventCursorExtent))
        (by simp [stage2NoEventRunRegions, stage2NoEventStagedRegions])
        (a := K.c + 8) (len := 8) (by omega) (by simp [stage2NoEventCursorExtent]))
  have hcep : ∀ k, k < (natToBytes K.ep 8).length →
      inRegions (stage2NoEventRunRegions K.scratch K.scratchcap K.stk K.e K.c K.d ++
        [(K.next0, K.nextEnd - K.next0)]) (K.c + 16 + k) := by
    simpa only [natToBytes_length] using
      (inRunRegions_of_mem (K := K) (r := (K.c, stage2NoEventCursorExtent))
        (by simp [stage2NoEventRunRegions, stage2NoEventStagedRegions])
        (a := K.c + 16) (len := 8) (by omega) (by simp [stage2NoEventCursorExtent]))
  have hcnep : ∀ k, k < (natToBytes (BitVec.ofNat 64 K.nep).toNat 8).length →
      inRegions (stage2NoEventRunRegions K.scratch K.scratchcap K.stk K.e K.c K.d ++
        [(K.next0, K.nextEnd - K.next0)]) (K.c + 24 + k) := by
    simpa only [natToBytes_length] using
      (inRunRegions_of_mem (K := K) (r := (K.c, stage2NoEventCursorExtent))
        (by simp [stage2NoEventRunRegions, stage2NoEventStagedRegions])
        (a := K.c + 24) (len := 8) (by omega) (by simp [stage2NoEventCursorExtent]))
  have hce : ∀ k, k < (natToBytes K.e 8).length →
      inRegions (stage2NoEventRunRegions K.scratch K.scratchcap K.stk K.e K.c K.d ++
        [(K.next0, K.nextEnd - K.next0)]) (K.c + 1112 + k) := by
    simpa only [natToBytes_length] using
      (inRunRegions_of_mem (K := K) (r := (K.c, stage2NoEventCursorExtent))
        (by simp [stage2NoEventRunRegions, stage2NoEventStagedRegions])
        (a := K.c + 1112) (len := 8) (by omega) (by simp [stage2NoEventCursorExtent]))
  have h1 := h.write (a := s.next) (bs := natToBytes (BitVec.ofNat 64 0).toNat 8) hxj
  have h2 := h1.write (a := K.e) (bs := natToBytes (BitVec.ofNat 32 1).toNat 4) he4
  have h3 := h2.write (a := K.e + 8) (bs := natToBytes (BitVec.ofNat 64 0).toNat 8) he8
  have h4 := h3.write (a := K.e + 16) (bs := natToBytes 0 8) he16
  have h5 := h4.write (a := K.c + 32) (bs := List.replicate 1160 (0 : UInt8)) hc1160
  have h6 := h5.write (a := K.c) (bs := natToBytes K.b 8) hc8
  have h7 := h6.write (a := K.c + 8) (bs := natToBytes (BitVec.ofNat 64 K.n).toNat 8) hcn
  have h8 := h7.write (a := K.c + 16) (bs := natToBytes K.ep 8) hcep
  have h9 := h8.write (a := K.c + 24) (bs := natToBytes (BitVec.ofNat 64 K.nep).toNat 8) hcnep
  have h10 := h9.write (a := K.c + 1112) (bs := natToBytes K.e 8) hce
  refine h10.mem_congr ?_
  simp only [entryFlushState, entrySuffixMem, entryBootMem, entryMem1,
    stage2NoEventStepState]

/-! ### The register facts at the hand-off

The entry block's cells do not shadow a parameter, so `Params` transports through
them; `Locals` is re-read at the hand-off's own cells (the bootstrap bound `%xj`
and `%off`). -/

private theorem lookupName_entryFlush {env : Env} {s : State} {b n ep nep c e : Nat}
    {v : Value} (name : String)
    (hsuf : name ∉ (entrySuffixCells b n ep nep c e).map (·.1))
    (hboot : name ∉ (entryBootCells s e).map (·.1))
    (h : lookupName env name = some v) :
    lookupName (entryFlushEnv env s b n ep nep c e) name = some v := by
  rw [entryFlushEnv,
    stage2NoEventSegCells_notin (cs := entrySuffixCells b n ep nep c e)
      (n := name) (env := entryBootEnv env s e) hsuf]
  rw [entryBootEnv,
    stage2NoEventSegCells_notin (cs := entryBootCells s e) (n := name) (env := env) hboot]
  exact h

/-- The suffix's cells do not contain any of the flattened body's parameters. -/
private theorem entrySuffixCells_notin_param {b n ep nep c e : Nat} {name : String}
    (h0 : name ≠ "%0") (hm : name ≠ "%msg") (hix : name ≠ "%ix")
    (hn2 : name ≠ "%n2") (he3 : name ≠ "%e3") (hnix : name ≠ "%nix")
    (hk : name ≠ "%k219") (hig : name ≠ "%invariant.gep")
    (hig2 : name ≠ "%invariant.gep1068") (hc : name ≠ "%cmp.not.peel1401.not") :
    name ∉ (entrySuffixCells b n ep nep c e).map (·.1) := by
  intro hmem
  simp only [entrySuffixCells, entryCells1, entryCells2, entryCells3, entryCells4,
    entryCells5, List.map_append, List.map_cons, List.map_nil, List.mem_append,
    List.mem_cons, List.not_mem_nil, or_false] at hmem
  tauto

/-- The bootstrap's cells do not contain a parameter. -/
private theorem entryBootCells_notin_param {s : State} {e : Nat} {name : String}
    (hoff : name ≠ "%off") (hei : name ≠ "%ei") (ho2 : name ≠ "%outn205")
    (ho1 : name ≠ "%outn") (hxj : name ≠ "%xj") :
    name ∉ (entryBootCells s e).map (·.1) := by
  intro hmem
  simp only [entryBootCells, List.map_cons, List.map_nil, List.mem_cons,
    List.not_mem_nil, or_false] at hmem
  tauto

/-- The parameters at the entry block's hand-off. -/
theorem entryFlush_params {K : Stage2NoEventWalkCarry} {s : State}
    (h : Stage2NoEventWalkParams K s) :
    Stage2NoEventWalkParams K
      (entryFlushState s.env s K.b K.n K.ep K.nep K.c K.e) := by
  have hsuf : ∀ {name : String}, name ≠ "%0" → name ≠ "%msg" → name ≠ "%ix" →
      name ≠ "%n2" → name ≠ "%e3" → name ≠ "%nix" → name ≠ "%k219" →
      name ≠ "%invariant.gep" → name ≠ "%invariant.gep1068" →
      name ≠ "%cmp.not.peel1401.not" →
      name ∉ (entrySuffixCells K.b K.n K.ep K.nep K.c K.e).map (·.1) :=
    fun h0 hm hix hn2 he3 hnix hk hig hig2 hcmp =>
      entrySuffixCells_notin_param h0 hm hix hn2 he3 hnix hk hig hig2 hcmp
  have hboot : ∀ {name : String}, name ≠ "%off" → name ≠ "%ei" → name ≠ "%outn205" →
      name ≠ "%outn" → name ≠ "%xj" →
      name ∉ (entryBootCells s K.e).map (·.1) :=
    fun hoff hei ho2 ho1 hxj => entryBootCells_notin_param hoff hei ho2 ho1 hxj
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (apply lookupName_entryFlush (env := s.env) (s := s)
      (b := K.b) (n := K.n) (ep := K.ep) (nep := K.nep) (c := K.c) (e := K.e))
  · exact hsuf (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)
  · exact hboot (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact h.b
  · exact hsuf (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)
  · exact hboot (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact h.n
  · exact hsuf (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)
  · exact hboot (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact h.ep
  · exact hsuf (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)
  · exact hboot (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact h.nep
  · exact hsuf (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)
  · exact hboot (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact h.xp
  · exact hsuf (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)
  · exact hboot (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact h.nxp
  · exact hsuf (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)
  · exact hboot (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact h.scratch
  · exact hsuf (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)
  · exact hboot (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact h.scratchcap
  · exact hsuf (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)
  · exact hboot (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact h.tokensOut
  · exact hsuf (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)
  · exact hboot (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact h.valuesOut
  · exact hsuf (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)
  · exact hboot (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact h.sumOut
  · exact hsuf (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)
  · exact hboot (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact h.err
  · exact hsuf (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)
  · exact hboot (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact h.stk
  · exact hsuf (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)
  · exact hboot (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact h.e
  · exact hsuf (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)
  · exact hboot (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact h.c
  · exact hsuf (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)
  · exact hboot (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact h.d

/-- The two local facts at the entry block's hand-off. -/
theorem entryFlush_locals {K : Stage2NoEventWalkCarry} {s : State}
    (hxj : K.xj = s.next) :
    Stage2NoEventWalkLocals K
      (entryFlushState s.env s K.b K.n K.ep K.nep K.c K.e) := by
  have hsuf : "%xj" ∉ (entrySuffixCells K.b K.n K.ep K.nep K.c K.e).map (·.1) :=
    entrySuffixCells_notin_param (name := "%xj") (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have hsufoff : "%off" ∉ (entrySuffixCells K.b K.n K.ep K.nep K.c K.e).map (·.1) :=
    entrySuffixCells_notin_param (name := "%off") (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have hlook : lookupName (entryBootCells s K.e) "%xj" = some (.ptr s.next) := by
    simp only [entryBootCells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    rw [lookupName_cons_self]
  have hlookoff : lookupName (entryBootCells s K.e) "%off" = some (.ptr (K.e + 8)) := by
    simp only [entryBootCells]
    rw [lookupName_cons_self]
  refine ⟨?_, ?_⟩
  · show lookupName (entryFlushEnv s.env s K.b K.n K.ep K.nep K.c K.e) "%xj" =
      some (.ptr K.xj)
    rw [entryFlushEnv, stage2NoEventSegCells_notin (cs := entrySuffixCells K.b K.n K.ep
      K.nep K.c K.e) (n := "%xj") (env := entryBootEnv s.env s K.e) hsuf]
    rw [entryBootEnv, stage2NoEventSegCells_some (cs := entryBootCells s K.e)
      (n := "%xj") (env := s.env) hlook]
    exact congrArg some (congrArg Value.ptr hxj.symm)
  · show lookupName (entryFlushEnv s.env s K.b K.n K.ep K.nep K.c K.e) "%off" =
      some (.ptr (K.e + 8))
    rw [entryFlushEnv, stage2NoEventSegCells_notin (cs := entrySuffixCells K.b K.n K.ep
      K.nep K.c K.e) (n := "%off") (env := entryBootEnv s.env s K.e) hsufoff]
    rw [entryBootEnv, stage2NoEventSegCells_some (cs := entryBootCells s K.e)
      (n := "%off") (env := s.env) hlookoff]

/-! ### The flush route

The empty document's route is the entry block's true arm to `if.then` and the
terminal module's flush run.  The three counts are named: the entry block's one
step, the arm's two, and the route's total, which is the quantity the loop's
budget arithmetic reads. -/

/-- The entry block's step count to `if.then`. -/
def stage2NoEventEntrySteps : Nat := 1

/-- The flush arm's step count (the terminal module's two-step run). -/
def stage2NoEventFlushArmSteps : Nat := 2

/-- The flush route's total step count, from the entry state to the flushed
return.  This is the named quantity the loop's budget arithmetic reads. -/
def stage2NoEventFlushSteps : Nat := 3

theorem stage2NoEventFlushSteps_eq :
    stage2NoEventFlushSteps =
      stage2NoEventEntrySteps + stage2NoEventFlushArmSteps := rfl

/-- **The flush route's price fits the finalisation allowance**, which is the term
the record's budget adds for a terminal route. -/
theorem stage2NoEventFlushSteps_le_finalisation :
    stage2NoEventFlushSteps ≤ stage2NoEventFinalisationAllowance := by decide

/-- **A one-step segment**, stated at an abstract target: the match on `runFuel`
never sees the step's concrete state. -/
theorem stage2NoEventWalkSegment_of_step {calls : Calls}
    {K K' : Stage2NoEventWalkCarry} {mem : Mem} {s s' : State}
    (h' : Stage2NoEventWalkInv K' mem s')
    (hstep : step calls stage2NoEventBody s = .jump s') :
    Stage2NoEventWalkSegment calls mem K s K' s' 1 := by
  refine ⟨?_, h'⟩
  intro n
  rw [show 1 + n = n + 1 from by omega]
  simp only [runFuel, hstep]

/-- **The flush segment**: one entry step to `if.then`, the carry unchanged. -/
theorem Stage2NoEventWalkSegment.flush {K : Stage2NoEventWalkCarry} {mem : Mem}
    {s : State}
    (h : Stage2NoEventWalkInv K mem s) (hpar : Stage2NoEventWalkParams K s)
    (hpc : s.pc = "entry") (hnext : s.next = K.next0)
    (hb1 : 1 ≤ K.b) (hnep0 : K.nep = 0) :
    Stage2NoEventWalkSegment (stage2NoEventCalls stage2GapRecover) mem K s K
      (entryFlushState s.env s K.b K.n K.ep K.nep K.c K.e)
      stage2NoEventEntrySteps := by
  have hstep : step (stage2NoEventCalls stage2GapRecover) stage2NoEventBody s =
      .jump (entryFlushState s.env s K.b K.n K.ep K.nep K.c K.e) := by
    simpa only [stateAt] using
      (entryBlock_step (gap := stage2GapRecover) (env := s.env) (s := s)
        hpar.b hpar.n hpar.ep hpar.nep hpar.c hpar.e hpar.stk hb1 hpc hnep0)
  exact stage2NoEventWalkSegment_of_step (entryBlock_inv h hnext) hstep

/-- **The flush arm at an abstract hand-off state**: the terminal module's run
and the record's boundary, without the entry block's state in the term. -/
theorem stage2NoEventWalkFlushRoute_of_segment {K : Stage2NoEventWalkCarry}
    {mem : Mem} {s sf : State}
    (hseg : Stage2NoEventWalkSegment (stage2NoEventCalls stage2GapRecover) mem K s K sf
      stage2NoEventEntrySteps)
    (hinv : Stage2NoEventWalkInv K mem sf) (hpar : Stage2NoEventWalkParams K sf)
    (hloc : Stage2NoEventWalkLocals K sf) (hpc : sf.pc = "if.then") :
    ∃ m, runFuel (stage2NoEventCalls stage2GapRecover) stage2NoEventFlushSteps
        stage2NoEventBody s = some (.ret (some (.int 64 0)) m) ∧
      stage2NoEventBoundary K.a12 mem K.next0 m (.int 64 0) := by
  obtain ⟨m, hrun, hb⟩ :=
    stage2NoEventFlush_run (K := K) (mem := mem) (s := sf) hinv hpar hloc hpc
  refine ⟨m, ?_, hb⟩
  rw [show stage2NoEventFlushSteps = stage2NoEventEntrySteps + 2 from rfl,
    hseg.run 2]
  simpa only [stateAt] using hrun

/-- **The flush route to the boundary.**  From an invariant-carrying entry state
whose entry stream is empty, the run reaches `if.then`, the flush arm writes the
three zeros and the document's length, and the record's boundary holds at the
returned memory.  The route's count is `stage2NoEventFlushSteps`. -/
theorem stage2NoEventWalkFlushRoute {K : Stage2NoEventWalkCarry} {mem : Mem}
    {s : State}
    (h : Stage2NoEventWalkInv K mem s) (hpar : Stage2NoEventWalkParams K s)
    (hpc : s.pc = "entry") (hnext : s.next = K.next0) (hxj : K.xj = K.next0)
    (hb1 : 1 ≤ K.b) (hnep0 : K.nep = 0) :
    ∃ m, runFuel (stage2NoEventCalls stage2GapRecover) stage2NoEventFlushSteps
        stage2NoEventBody s = some (.ret (some (.int 64 0)) m) ∧
      stage2NoEventBoundary K.a12 mem K.next0 m (.int 64 0) :=
  stage2NoEventWalkFlushRoute_of_segment
    (K := K) (mem := mem) (s := s)
    (sf := entryFlushState s.env s K.b K.n K.ep K.nep K.c K.e)
    (Stage2NoEventWalkSegment.flush (K := K) (mem := mem) (s := s)
      h hpar hpc hnext hb1 hnep0)
    (entryBlock_inv h hnext) (entryFlush_params hpar)
    (entryFlush_locals (K := K) (s := s) (hxj.trans hnext.symm)) rfl

/-! ### Axiom footprints -/

#print axioms Stage2NoEventWalkSegment.trans
#print axioms Stage2NoEventWalkSegment.of_chain
#print axioms Stage2NoEventWalkSegment.ret
#print axioms stage2NoEventWalkPotential_le_of_le
#print axioms Stage2NoEventWalkPricedSegment.trans
#print axioms stage2NoEventFlushSteps_le_finalisation
#print axioms stage2NoEventWalkSegment_of_step
#print axioms Stage2NoEventWalkInv.write
#print axioms entryBootstrap_run
#print axioms entryBlock_denote
#print axioms entryBlock_term_flush
#print axioms entryBlock_inv
#print axioms entryFlush_params
#print axioms entryFlush_locals
#print axioms Stage2NoEventWalkSegment.flush
#print axioms stage2NoEventWalkFlushRoute

end LeanLLVM.Refinement
