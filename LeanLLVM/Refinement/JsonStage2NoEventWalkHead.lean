/-
The no-event walk's head premise, its class tables, and its head segments.

The walk's loop enters `NodeBlock5` after the head block has read the entry's
lane and the document's byte there.  The step the dispatch produces is stated at
what that read leaves in the state, so this module names it: `Stage2NoEventWalkHead`
carries the invariant, the entry's parameters (through the base lookups), the
carry's index below the entry count, `1 ≤ b` (the report's base, which the
invariant does not state), and **the head block's run equation** — the six read
cells over the nine `phi` cells over an incoming environment that binds the entry's
stable live-ins at the carry's numbers.  Both cell layers are parameterised by the
head's own values (`loopHeadReadCellsAt`/`loopHeadPhiCellsAt`), so the equation
determines the environment and no cell is pinned to a stale zero: a continuation
head at `k' > 0` inhabits the premise, and only the seed instantiates the layers
at the zeros.  The six read values (`%3`, `%arrayidx6.peel`, `%idxprom.peel`, `%2`,
`%arrayidx.peel`, `%inc.peel`) and the lane/document facts are projections of that
equation, not separate fields, so a register the class rows read is present by
construction.

`Stage2NoEventWalkBaseValues` names the entry chain's stable live-ins at the
carry's numbers — the sixteen parameters, the entry block's four allocations, the
suffix's records, the zero test, and the preheader's fourteen scratch geps — and
`Stage2NoEventWalkBaseLookups` says the state binds each of them.  A lookup
predicate is what a continuation head satisfies, because the backedge's conses do
not shadow those names; a structural chain in the environment is not (F4).
`stage2NoEventWalkHeadRegs` is the union of the base names, the six read names and
the nine `phi` names, and `stage2NoEventWalkArmLiveIns` is the `#guard` census:
each arm's head-live-in names are head registers.
`stage2NoEventWalkHead_closure` is the census's proof: every register in it
resolves at a head.  The closure is what makes `Rows` inhabitable: the class rows
take their reads from the equation (or a projection of it), so a register absent
from the head is a compile error at the row rather than an unprovable premise.

The trace vocabulary and the acceptance's three-word reading sit with the
invariant (`JsonStage2NoEventWalkInv`): both are about the carry and the state,
not about the segment tier, and `JsonStage2NoEventWalkTerminal` reads them.

The five class tables name the body's dispatch pivots, one per dispatch site, and
each comes with a `complete` theorem: every byte (and, for the after-value table,
every depth) falls in one of the table's classes.  The tables exist so the
per-class rows of the dispatch tier can be stated against a closed vocabulary; the
staging projection of the head table is a projection of `Stage2NoEventWalkHead`,
while the other four project their own pivot reads.

The segment wrappers re-point the counted segment at a head: `HeadSegment` adds
the target's `Head` and `Trace` to a `Segment`, and `HeadPricedSegment` adds the
credit.  The plain `Segment`/`PricedSegment` and their lemmas are unchanged.

The two uninhabitability witnesses are stated at the end: `F1` exhibits a state
inside the old premise's quantifier — invariant, `NodeBlock5`, `%k.0.ph1404 = 0`,
`0 < nep` — whose `%3` is absent, so the head term cannot run; the state is
outside `Stage2NoEventWalkHead`, no row is inhabitable there, and the old
`Rows` statement (quantified over the invariant) is therefore refutable.  `F2`
lives in `JsonStage2NoEventWalkSeed` (it needs the seed's head): it takes that head
and shows the loop's `Stage2NoEventWalkAcc` is not inhabitable there, which is what
the old single-`Acc` exit required.
-/
import LeanLLVM.Refinement.JsonStage2NoEventWalkSegment

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 800000

namespace LeanLLVM.Refinement

open LeanLLVM
open LeanLLVM.JSON
open LeanLLVM.Refinement.JsonStage2NoEventIR
open LeanLLVM.Refinement.JsonEntryIR (readLanes32)
open LeanLLVM.Refinement.BlockEval (cells)

/-! ### The base lookups and the head's layers

The head block's environment is its six read cells over the nine `phi` cells over
the entry chain's environment.  The read and `phi` layers are **exact**: they are
the head block's own conses (`loopHeadReadCellsAt`/`loopHeadPhiCellsAt`, at the
head's values), so the equation below is the form every real head has — at the
seed the tail is the entry chain, at a continuation head it is the
`value.outer.backedge` environment.  The entry chain's stable live-ins are **not**
a structural list: `Stage2NoEventWalkBaseLookups K s` says, per name, that the
state's environment binds it at the carry's value.  A lookup predicate is what a
continuation head can satisfy, because the backedge's conses do not shadow those
names; a structural chain is exactly what it cannot have (F4).
-/

/-- The sixteen parameter names. -/
def stage2NoEventWalkHeadParamNames : List String :=
  ["%b", "%n", "%ep", "%nep", "%xp", "%nxp", "%scratch", "%scratchcap",
   "%tokens_out", "%values_out", "%sum_out", "%err", "%stk", "%e", "%c", "%d"]

/-- **The sixteen parameters at the carry's numbers**, as a name/value table. -/
def stage2NoEventWalkParamEntries (K : Stage2NoEventWalkCarry) :
    List (String × Value) :=
  [("%b", .ptr K.b), ("%n", .int 64 (BitVec.ofNat 64 K.n)), ("%ep", .ptr K.ep),
   ("%nep", .int 64 (BitVec.ofNat 64 K.nep)), ("%xp", .ptr K.xp),
   ("%nxp", .int 64 (BitVec.ofNat 64 K.nxp)), ("%scratch", .ptr K.scratch),
   ("%scratchcap", .int 64 (BitVec.ofNat 64 K.scratchcap)),
   ("%tokens_out", .ptr K.tokensOut), ("%values_out", .ptr K.valuesOut),
   ("%sum_out", .ptr K.sumOut), ("%err", .ptr K.err), ("%stk", .ptr K.stk),
   ("%e", .ptr K.e), ("%c", .ptr K.c), ("%d", .ptr K.d)]

/-- **The parameters' names, as the table maps them.** -/
theorem stage2NoEventWalkParamEntries_names (K : Stage2NoEventWalkCarry) :
    (stage2NoEventWalkParamEntries K).map (·.1) = stage2NoEventWalkHeadParamNames := by
  simp [stage2NoEventWalkParamEntries, stage2NoEventWalkHeadParamNames]

/-- The entry chain's stable cell names (the parameters are the table's head). -/
def stage2NoEventWalkBaseCellNames : List String :=
  ["%invariant.gep1676", "%invariant.gep1674", "%invariant.gep1672",
   "%invariant.gep1670", "%invariant.gep1668", "%invariant.gep1666",
   "%invariant.gep1664", "%invariant.gep1662", "%invariant.gep1660",
   "%invariant.gep1658", "%invariant.gep1656", "%invariant.gep1654",
   "%invariant.gep1652", "%invariant.gep1650", "%cmp.not.peel1401.not",
   "%k219", "%invariant.gep1068", "%invariant.gep", "%e3", "%nix", "%ix", "%n2",
   "%0", "%msg", "%off", "%ei", "%outn205", "%outn", "%xj"]

/-- **The entry chain's stable cells at the carry's numbers**, in the order the
chain installs them: the preheader's fourteen geps, the suffix's zero test and
cells, and the entry block's five allocation cells. -/
def stage2NoEventWalkBaseCellValues (K : Stage2NoEventWalkCarry) :
    List (String × Value) :=
  preHeaderCells K.scratch ++
    [("%cmp.not.peel1401.not", .int 1 0)] ++
    entryCells4 K.b K.c ++ entryCells3 K.ep K.c ++ entryCells2 K.b K.c ++
    entryCells1 K.c K.e ++
    [("%off", .ptr (K.e + 8)), ("%ei", .ptr (K.next0 + 24)),
     ("%outn205", .ptr (K.next0 + 16)), ("%outn", .ptr (K.next0 + 8)),
     ("%xj", .ptr K.next0)]

/-- **The base cells' names, as the table maps them.** -/
theorem stage2NoEventWalkBaseCellValues_names (K : Stage2NoEventWalkCarry) :
    (stage2NoEventWalkBaseCellValues K).map (·.1) = stage2NoEventWalkBaseCellNames := by
  simp [stage2NoEventWalkBaseCellValues, stage2NoEventWalkBaseCellNames,
    preHeaderCells, entryCells1, entryCells2, entryCells3, entryCells4]

/-- The head's base names: the parameters and the entry chain's stable cells. -/
def stage2NoEventWalkBaseNames : List String :=
  stage2NoEventWalkHeadParamNames ++ stage2NoEventWalkBaseCellNames

/-- **The base facts at the carry's numbers**, as one table. -/
def stage2NoEventWalkBaseValues (K : Stage2NoEventWalkCarry) :
    List (String × Value) :=
  stage2NoEventWalkParamEntries K ++ stage2NoEventWalkBaseCellValues K

/-- **The base names, as the table maps them.** -/
theorem stage2NoEventWalkBaseValues_names (K : Stage2NoEventWalkCarry) :
    (stage2NoEventWalkBaseValues K).map (·.1) = stage2NoEventWalkBaseNames := by
  simp only [stage2NoEventWalkBaseValues, stage2NoEventWalkBaseNames, List.map_append,
    stage2NoEventWalkParamEntries_names, stage2NoEventWalkBaseCellValues_names]

/-- **The entry's stable live-ins, as lookups over the whole environment.**  Per
name in `stage2NoEventWalkBaseNames`, the state binds the carry's value.  The
predicate is over the raw environment, so it holds at the backedge's list as well
as at the seed's chain; a structural position is not required. -/
def Stage2NoEventWalkBaseLookups (K : Stage2NoEventWalkCarry) (s : State) : Prop :=
  ∀ n v, (n, v) ∈ stage2NoEventWalkBaseValues K → lookupName s.env n = some v

/-- **The parameters resolve at any state that carries them**, from the table. -/
theorem Stage2NoEventWalkParams.lookup_entry {K : Stage2NoEventWalkCarry}
    {s : State} (h : Stage2NoEventWalkParams K s) :
    ∀ n v, (n, v) ∈ stage2NoEventWalkParamEntries K → lookupName s.env n = some v := by
  intro n v hv
  simp only [stage2NoEventWalkParamEntries, List.mem_cons, List.not_mem_nil, or_false,
    Prod.mk.injEq] at hv
  rcases hv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact h.b
  · exact h.n
  · exact h.ep
  · exact h.nep
  · exact h.xp
  · exact h.nxp
  · exact h.scratch
  · exact h.scratchcap
  · exact h.tokensOut
  · exact h.valuesOut
  · exact h.sumOut
  · exact h.err
  · exact h.stk
  · exact h.e
  · exact h.c
  · exact h.d

/-- **The head block's six read cells**, in the order the block writes them at an
index, lane and document byte. -/
def loopHeadReadCells (k lane : Nat) (byte : UInt8) (ep b : Nat) :
    List (String × Value) :=
  [("%3", .int 8 (BitVec.ofNat 8 byte.toNat)),
   ("%arrayidx6.peel", .ptr (b + lane)),
   ("%idxprom.peel", .int 64 (BitVec.ofNat 64 lane)),
   ("%2", .int 32 (BitVec.ofNat 32 lane)),
   ("%arrayidx.peel", .ptr (ep + 4 * k)),
   ("%inc.peel", .int 64 (BitVec.ofNat 64 (k + 1)))]

/-- **The head block's six read cells at the head's values.**  The stack words are
part of the head's uniform parameter list (the `phi` layer's values); the head
block does not read them, so the read layer is the delivered one at `k`, `lane`
and `byte`. -/
def loopHeadReadCellsAt (K : Stage2NoEventWalkCarry) (k : Nat)
    (_sp _fr _one _wide : Nat) (lane : Nat) (byte : UInt8) :
    List (String × Value) :=
  loopHeadReadCells k lane byte K.ep K.b

/-- The read cells' names. -/
def loopHeadReadCellNames : List String :=
  ["%3", "%arrayidx6.peel", "%idxprom.peel", "%2", "%arrayidx.peel", "%inc.peel"]

/-- **The read cells' names, as the list maps them.** -/
theorem loopHeadReadCells_names (k lane : Nat) (byte : UInt8) (ep b : Nat) :
    (loopHeadReadCells k lane byte ep b).map (·.1) = loopHeadReadCellNames := rfl

/-- **The read layer's names at the head's values.** -/
theorem loopHeadReadCellsAt_names (K : Stage2NoEventWalkCarry) (k : Nat)
    (sp fr one wide lane : Nat) (byte : UInt8) :
    (loopHeadReadCellsAt K k sp fr one wide lane byte).map (·.1) =
      loopHeadReadCellNames :=
  loopHeadReadCells_names k lane byte K.ep K.b

/-- **The nine `phi` cells at the head's values**, newest first: the preheader's
merge at the head, with the stack words at the values the projections name. -/
def loopHeadPhiCellsAt (K : Stage2NoEventWalkCarry) (k sp fr one wide : Nat) :
    List (String × Value) :=
  [("%frame.0.ph1402", .int 8 (BitVec.ofNat 8 fr)),
   ("%sp.0.ph1403", .int 32 (BitVec.ofNat 32 sp)),
   ("%k.0.ph1404", .int 64 (BitVec.ofNat 64 k)),
   ("%alen.0.ph1405", .int 64 (BitVec.ofNat 64 K.arena.length)),
   ("%arena.0.ph1406", .int 64 (BitVec.ofNat 64 K.arenaWord)),
   ("%terms.0.ph1407", .int 64 (BitVec.ofNat 64 K.terms)),
   ("%tokens.0.ph1408", .int 64 (BitVec.ofNat 64 K.tok)),
   ("%1", .int 64 (BitVec.ofNat 64 one)),
   ("%wide.trip.count1409", .int 64 (BitVec.ofNat 64 wide))]

/-- The nine `phi` cells' names. -/
def loopHeadPhiCellNames : List String :=
  ["%frame.0.ph1402", "%sp.0.ph1403", "%k.0.ph1404", "%alen.0.ph1405",
   "%arena.0.ph1406", "%terms.0.ph1407", "%tokens.0.ph1408", "%1",
   "%wide.trip.count1409"]

/-- **The `phi` layer's names at the head's values.** -/
theorem loopHeadPhiCellsAt_names (K : Stage2NoEventWalkCarry) (k sp fr one wide : Nat) :
    (loopHeadPhiCellsAt K k sp fr one wide).map (·.1) = loopHeadPhiCellNames := rfl

/-- **The head's register census**: the base names, the six read cells and the
nine `phi` cells.  A class row may read a register from the head only if it is
here. -/
def stage2NoEventWalkHeadRegs : List String :=
  stage2NoEventWalkBaseNames ++ (loopHeadReadCellNames ++ loopHeadPhiCellNames)

/-- **The census has no repeated name**, so a member resolves at the first layer
that binds it. -/
theorem stage2NoEventWalkHeadRegs_nodup :
    (stage2NoEventWalkBaseNames ++ (loopHeadReadCellNames ++
      loopHeadPhiCellNames)).Nodup := by
  decide

/-- The arm-live-in census: each dispatch arm lists the head registers it reads
and does not itself bind; the guard below checks every name is in the head's
register census.  The route-bound names (`%cond`, `%idxprom.lcssa`, `%ee.1`,
`%k219`) stay with the arms.  L1–L4 extend the table as their arms land; the
head's four classes are the arms at the head. -/
def stage2NoEventWalkArmLiveIns : List (String × List String) :=
  [("head-string", ["%3", "%ep", "%b"]),
   ("head-bracket", ["%3", "%ep", "%b"]),
   ("head-brace", ["%3", "%ep", "%b"]),
   ("head-value", ["%3", "%ep", "%b", "%invariant.gep1068"])]

/-- **Every arm's head-live-in name is a head register.** -/
def stage2NoEventWalkHeadLiveInCensus : Bool :=
  stage2NoEventWalkArmLiveIns.all fun arm =>
    arm.2.all fun n => decide (n ∈ stage2NoEventWalkHeadRegs)

#guard stage2NoEventWalkArmLiveIns.length = 4
#guard stage2NoEventWalkHeadLiveInCensus

/-! ### The builder's lookups

Two inductions the closure and the projections both read: a name the cell list
binds resolves to that cell when the list has no repeated name, and a name the
list does not mention is the incoming environment's. -/

/-- **A cell list with distinct names resolves every name it binds.** -/
theorem cells_lookup_of_mem :
    ∀ (cs : List (String × Value)) (env : Env) {n : String} {v : Value},
      (n, v) ∈ cs → (cs.map (·.1)).Nodup → lookupName (cells cs env) n = some v
  | [], _, _, _, h, _ => by simp at h
  | (k, w) :: cs, env, n, v, h, hnd => by
      rw [List.mem_cons] at h
      rcases h with hh | ht
      · obtain ⟨rfl, rfl⟩ := Prod.mk.injEq n v k w |>.mp hh
        simp only [cells, lookupName_cons_self]
      · have hkn : k ≠ n := by
          intro hkn
          exact (List.nodup_cons.mp hnd).1
            (hkn ▸ List.mem_map.mpr ⟨(n, v), ht, rfl⟩)
        simp only [cells, lookupName_cons_ne w (cells cs env) hkn]
        exact cells_lookup_of_mem cs env ht (List.nodup_cons.mp hnd).2

/-- **A name the cell list does not mention is the incoming environment's.** -/
theorem cells_lookup_of_notin :
    ∀ (cs : List (String × Value)) (env : Env) {n : String},
      n ∉ cs.map (·.1) → lookupName (cells cs env) n = lookupName env n
  | [], _, _, _ => rfl
  | (k, w) :: cs, env, n, h => by
      have hk : k ≠ n := by
        intro hkn
        exact h (by subst hkn; simp)
      simp only [cells, lookupName_cons_ne w (cells cs env) hk]
      exact cells_lookup_of_notin cs env (fun hc => h (List.mem_cons_of_mem _ hc))

/-- **A bound name resolves**, in the form the closure states. -/
theorem cells_lookup_of_name_mem (cs : List (String × Value)) (env : Env)
    {n : String} (h : n ∈ cs.map (·.1)) (hnd : (cs.map (·.1)).Nodup) :
    ∃ v, lookupName (cells cs env) n = some v := by
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp h
  exact ⟨p.2, cells_lookup_of_mem cs env hp hnd⟩

/-! ### The head premise -/

/-- **The state the dispatch's step is stated at.**  The head block's read has
run, so the state is at `NodeBlock5` with the entry's lane and the document's byte
there.  The environment is the six read cells over the nine `phi` cells over an
existential tail — the exact layers the block conses — and the entry chain's
stable live-ins are the lookup predicate `Stage2NoEventWalkBaseLookups`, not a
position in that tail.  The read and `phi` layers are parameterised by the head's
own values, so a continuation head at `k' > 0` inhabits the premise; only the seed
instantiates the layers at the zeros. -/
structure Stage2NoEventWalkHead (K : Stage2NoEventWalkCarry) (mem : Mem) (k : Nat)
    (s : State) : Prop where
  /-- The loop's invariant. -/
  inv : Stage2NoEventWalkInv K mem s
  /-- The head block has handed off to the dispatch root. -/
  pc : s.pc = "NodeBlock5"
  /-- The index is a real entry index. -/
  klt : k < K.nep
  /-- The report's base is at least one. -/
  bPos : 1 ≤ K.b
  /-- **The head block's run equation**: the six read cells over the nine `phi`
  cells over an existential tail, at the head's values, and the lane and byte the
  read saw at the document. -/
  layers : ∃ (rest : Env) (sp fr one wide lane : Nat) (byte : UInt8),
    s.env = cells (loopHeadReadCellsAt K k sp fr one wide lane byte)
      (cells (loopHeadPhiCellsAt K k sp fr one wide) rest) ∧
    K.ent[k]? = some lane ∧ lane < 2 ^ 32 ∧ K.bs[lane]? = some byte ∧
    readBytes s.mem (K.b + lane) 1 = some [byte] ∧
    sp < 2 ^ 32 ∧ fr < 2 ^ 8 ∧ one = sp ∧ wide = max sp 520
  /-- The entry chain's stable live-ins, as lookups over the whole environment. -/
  baseLookups : Stage2NoEventWalkBaseLookups K s

/-- **The head's layer equation**, as the existential the accessors project. -/
theorem Stage2NoEventWalkHead.env_form {K : Stage2NoEventWalkCarry} {mem : Mem}
    {k : Nat} {s : State} (h : Stage2NoEventWalkHead K mem k s) :
    ∃ (rest : Env) (sp fr one wide lane : Nat) (byte : UInt8),
      s.env = cells (loopHeadReadCellsAt K k sp fr one wide lane byte)
        (cells (loopHeadPhiCellsAt K k sp fr one wide) rest) ∧
      K.ent[k]? = some lane ∧ lane < 2 ^ 32 ∧ K.bs[lane]? = some byte ∧
      readBytes s.mem (K.b + lane) 1 = some [byte] ∧
      sp < 2 ^ 32 ∧ fr < 2 ^ 8 ∧ one = sp ∧ wide = max sp 520 :=
  h.layers

/-- **The head's read hypothesis**: the exact layers and the base lookups, as one
pair. -/
theorem Stage2NoEventWalkHead.readAndEnv {K : Stage2NoEventWalkCarry} {mem : Mem}
    {k : Nat} {s : State} (h : Stage2NoEventWalkHead K mem k s) :
    (∃ (rest : Env) (sp fr one wide lane : Nat) (byte : UInt8),
      s.env = cells (loopHeadReadCellsAt K k sp fr one wide lane byte)
        (cells (loopHeadPhiCellsAt K k sp fr one wide) rest) ∧
      K.ent[k]? = some lane ∧ lane < 2 ^ 32 ∧ K.bs[lane]? = some byte ∧
      readBytes s.mem (K.b + lane) 1 = some [byte] ∧
      sp < 2 ^ 32 ∧ fr < 2 ^ 8 ∧ one = sp ∧ wide = max sp 520) ∧
    Stage2NoEventWalkBaseLookups K s :=
  ⟨h.layers, h.baseLookups⟩

/-- **The index cell**, a projection of the `phi` layer. -/
theorem Stage2NoEventWalkHead.kEq {K : Stage2NoEventWalkCarry} {mem : Mem} {k : Nat}
    {s : State} (h : Stage2NoEventWalkHead K mem k s) :
    lookupName s.env "%k.0.ph1404" = some (.int 64 (BitVec.ofNat 64 k)) := by
  obtain ⟨rest, sp, fr, one, wide, lane, byte, henv, -⟩ := h.layers
  rw [henv, cells_lookup_of_notin _ _ (by rw [loopHeadReadCellsAt_names]; decide)]
  exact cells_lookup_of_mem _ _ (by simp [loopHeadPhiCellsAt]) (by
    rw [loopHeadPhiCellsAt_names]; decide)

/-- **The token count's `phi`.** -/
theorem Stage2NoEventWalkHead.tokensPhi {K : Stage2NoEventWalkCarry} {mem : Mem}
    {k : Nat} {s : State} (h : Stage2NoEventWalkHead K mem k s) :
    lookupName s.env "%tokens.0.ph1408" =
      some (.int 64 (BitVec.ofNat 64 K.tok)) := by
  obtain ⟨rest, sp, fr, one, wide, lane, byte, henv, -⟩ := h.layers
  rw [henv, cells_lookup_of_notin _ _ (by rw [loopHeadReadCellsAt_names]; decide)]
  exact cells_lookup_of_mem _ _ (by simp [loopHeadPhiCellsAt]) (by
    rw [loopHeadPhiCellsAt_names]; decide)

/-- **The terms count's `phi`.** -/
theorem Stage2NoEventWalkHead.termsPhi {K : Stage2NoEventWalkCarry} {mem : Mem}
    {k : Nat} {s : State} (h : Stage2NoEventWalkHead K mem k s) :
    lookupName s.env "%terms.0.ph1407" =
      some (.int 64 (BitVec.ofNat 64 K.terms)) := by
  obtain ⟨rest, sp, fr, one, wide, lane, byte, henv, -⟩ := h.layers
  rw [henv, cells_lookup_of_notin _ _ (by rw [loopHeadReadCellsAt_names]; decide)]
  exact cells_lookup_of_mem _ _ (by simp [loopHeadPhiCellsAt]) (by
    rw [loopHeadPhiCellsAt_names]; decide)

/-- **The arena word's `phi`.** -/
theorem Stage2NoEventWalkHead.arenaPhi {K : Stage2NoEventWalkCarry} {mem : Mem}
    {k : Nat} {s : State} (h : Stage2NoEventWalkHead K mem k s) :
    lookupName s.env "%arena.0.ph1406" =
      some (.int 64 (BitVec.ofNat 64 K.arenaWord)) := by
  obtain ⟨rest, sp, fr, one, wide, lane, byte, henv, -⟩ := h.layers
  rw [henv, cells_lookup_of_notin _ _ (by rw [loopHeadReadCellsAt_names]; decide)]
  exact cells_lookup_of_mem _ _ (by simp [loopHeadPhiCellsAt]) (by
    rw [loopHeadPhiCellsAt_names]; decide)

/-- **The arena length's `phi`.** -/
theorem Stage2NoEventWalkHead.alenPhi {K : Stage2NoEventWalkCarry} {mem : Mem}
    {k : Nat} {s : State} (h : Stage2NoEventWalkHead K mem k s) :
    lookupName s.env "%alen.0.ph1405" =
      some (.int 64 (BitVec.ofNat 64 K.arena.length)) := by
  obtain ⟨rest, sp, fr, one, wide, lane, byte, henv, -⟩ := h.layers
  rw [henv, cells_lookup_of_notin _ _ (by rw [loopHeadReadCellsAt_names]; decide)]
  exact cells_lookup_of_mem _ _ (by simp [loopHeadPhiCellsAt]) (by
    rw [loopHeadPhiCellsAt_names]; decide)

/-- **The stack group**: the depth, the frame, its 64-bit extension, and the
`520`-budgeted trip count, with the edge relation. -/
theorem Stage2NoEventWalkHead.spPhi {K : Stage2NoEventWalkCarry} {mem : Mem}
    {k : Nat} {s : State} (h : Stage2NoEventWalkHead K mem k s) :
    ∃ (sp fr one wide : Nat),
      lookupName s.env "%sp.0.ph1403" = some (.int 32 (BitVec.ofNat 32 sp)) ∧
      lookupName s.env "%frame.0.ph1402" = some (.int 8 (BitVec.ofNat 8 fr)) ∧
      lookupName s.env "%1" = some (.int 64 (BitVec.ofNat 64 one)) ∧
      lookupName s.env "%wide.trip.count1409" =
        some (.int 64 (BitVec.ofNat 64 wide)) ∧
      one = sp ∧ wide = max sp 520 := by
  obtain ⟨rest, sp, fr, one, wide, lane, byte, henv, -, -, -, -, -, -, hone, hwide⟩ :=
    h.layers
  have hsp : lookupName s.env "%sp.0.ph1403" =
      some (.int 32 (BitVec.ofNat 32 sp)) := by
    rw [henv, cells_lookup_of_notin _ _ (by rw [loopHeadReadCellsAt_names]; decide)]
    exact cells_lookup_of_mem _ _ (by simp [loopHeadPhiCellsAt]) (by
      rw [loopHeadPhiCellsAt_names]; decide)
  have hfr : lookupName s.env "%frame.0.ph1402" =
      some (.int 8 (BitVec.ofNat 8 fr)) := by
    rw [henv, cells_lookup_of_notin _ _ (by rw [loopHeadReadCellsAt_names]; decide)]
    exact cells_lookup_of_mem _ _ (by simp [loopHeadPhiCellsAt]) (by
      rw [loopHeadPhiCellsAt_names]; decide)
  have hone' : lookupName s.env "%1" =
      some (.int 64 (BitVec.ofNat 64 one)) := by
    rw [henv, cells_lookup_of_notin _ _ (by rw [loopHeadReadCellsAt_names]; decide)]
    exact cells_lookup_of_mem _ _ (by simp [loopHeadPhiCellsAt]) (by
      rw [loopHeadPhiCellsAt_names]; decide)
  have hwide' : lookupName s.env "%wide.trip.count1409" =
      some (.int 64 (BitVec.ofNat 64 wide)) := by
    rw [henv, cells_lookup_of_notin _ _ (by rw [loopHeadReadCellsAt_names]; decide)]
    exact cells_lookup_of_mem _ _ (by simp [loopHeadPhiCellsAt]) (by
      rw [loopHeadPhiCellsAt_names]; decide)
  exact ⟨sp, fr, one, wide, hsp, hfr, hone', hwide', hone, hwide⟩

/-- **The frame's `phi`.** -/
theorem Stage2NoEventWalkHead.framePhi {K : Stage2NoEventWalkCarry} {mem : Mem}
    {k : Nat} {s : State} (h : Stage2NoEventWalkHead K mem k s) :
    ∃ fr, lookupName s.env "%frame.0.ph1402" = some (.int 8 (BitVec.ofNat 8 fr)) := by
  obtain ⟨rest, sp, fr, one, wide, lane, byte, henv, -⟩ := h.layers
  refine ⟨fr, ?_⟩
  rw [henv, cells_lookup_of_notin _ _ (by rw [loopHeadReadCellsAt_names]; decide)]
  exact cells_lookup_of_mem _ _ (by simp [loopHeadPhiCellsAt]) (by
    rw [loopHeadPhiCellsAt_names]; decide)

/-- **The depth's zero extension's `phi`.** -/
theorem Stage2NoEventWalkHead.onePhi {K : Stage2NoEventWalkCarry} {mem : Mem}
    {k : Nat} {s : State} (h : Stage2NoEventWalkHead K mem k s) :
    ∃ one, lookupName s.env "%1" = some (.int 64 (BitVec.ofNat 64 one)) := by
  obtain ⟨rest, sp, fr, one, wide, lane, byte, henv, -⟩ := h.layers
  refine ⟨one, ?_⟩
  rw [henv, cells_lookup_of_notin _ _ (by rw [loopHeadReadCellsAt_names]; decide)]
  exact cells_lookup_of_mem _ _ (by simp [loopHeadPhiCellsAt]) (by
    rw [loopHeadPhiCellsAt_names]; decide)

/-- **The `520`-budgeted trip count's `phi`.** -/
theorem Stage2NoEventWalkHead.widePhi {K : Stage2NoEventWalkCarry} {mem : Mem}
    {k : Nat} {s : State} (h : Stage2NoEventWalkHead K mem k s) :
    ∃ wide, lookupName s.env "%wide.trip.count1409" =
      some (.int 64 (BitVec.ofNat 64 wide)) := by
  obtain ⟨rest, sp, fr, one, wide, lane, byte, henv, -⟩ := h.layers
  refine ⟨wide, ?_⟩
  rw [henv, cells_lookup_of_notin _ _ (by rw [loopHeadReadCellsAt_names]; decide)]
  exact cells_lookup_of_mem _ _ (by simp [loopHeadPhiCellsAt]) (by
    rw [loopHeadPhiCellsAt_names]; decide)

/-- **The six read values at a head**, projected from the run equation. -/
theorem Stage2NoEventWalkHead.laneRead {K : Stage2NoEventWalkCarry} {mem : Mem}
    {k : Nat} {s : State} (h : Stage2NoEventWalkHead K mem k s) :
    ∃ (lane : Nat) (byte : UInt8),
      K.ent[k]? = some lane ∧ lane < 2 ^ 32 ∧ K.bs[lane]? = some byte ∧
      readBytes s.mem (K.b + lane) 1 = some [byte] ∧
      lookupName s.env "%2" = some (.int 32 (BitVec.ofNat 32 lane)) ∧
      lookupName s.env "%idxprom.peel" = some (.int 64 (BitVec.ofNat 64 lane)) ∧
      lookupName s.env "%inc.peel" = some (.int 64 (BitVec.ofNat 64 (k + 1))) ∧
      lookupName s.env "%arrayidx.peel" = some (.ptr (K.ep + 4 * k)) ∧
      lookupName s.env "%arrayidx6.peel" = some (.ptr (K.b + lane)) ∧
      lookupName s.env "%3" = some (.int 8 (BitVec.ofNat 8 byte.toNat)) := by
  obtain ⟨rest, sp, fr, one, wide, lane, byte, henv, hent, hlt, hbs, hread,
    -, -, -, -⟩ := h.layers
  have hreadLookup : ∀ (n : String) (v : Value),
      (n, v) ∈ loopHeadReadCellsAt K k sp fr one wide lane byte →
      lookupName s.env n = some v := by
    intro n v hv
    rw [henv]
    exact cells_lookup_of_mem _ _ hv (by
      rw [loopHeadReadCellsAt_names]; decide)
  exact ⟨lane, byte, hent, hlt, hbs, hread,
    hreadLookup "%2" _ (by simp [loopHeadReadCellsAt, loopHeadReadCells]),
    hreadLookup "%idxprom.peel" _ (by simp [loopHeadReadCellsAt, loopHeadReadCells]),
    hreadLookup "%inc.peel" _ (by simp [loopHeadReadCellsAt, loopHeadReadCells]),
    hreadLookup "%arrayidx.peel" _ (by simp [loopHeadReadCellsAt, loopHeadReadCells]),
    hreadLookup "%arrayidx6.peel" _ (by simp [loopHeadReadCellsAt, loopHeadReadCells]),
    hreadLookup "%3" _ (by simp [loopHeadReadCellsAt, loopHeadReadCells])⟩

/-- **The head's byte is present.**  The read's `%3` cell is the only condition
the dispatch root has on the state. -/
theorem Stage2NoEventWalkHead.bytePresent {K : Stage2NoEventWalkCarry} {mem : Mem}
    {k : Nat} {s : State} (h : Stage2NoEventWalkHead K mem k s) :
    ∃ v, lookupName s.env "%3" = some v := by
  obtain ⟨lane, byte, -, -, -, -, -, -, -, -, -, h3⟩ := h.laneRead
  exact ⟨_, h3⟩

/-- **The head's class.**  The class table's staging is a projection of the head:
the byte the dispatch reads is the document's byte at the entry's lane. -/
theorem Stage2NoEventWalkHead.classStage {K : Stage2NoEventWalkCarry} {mem : Mem}
    {k : Nat} {s : State} (h : Stage2NoEventWalkHead K mem k s) :
    ∃ lane byte, K.ent[k]? = some lane ∧ K.bs[lane]? = some byte ∧
      readBytes s.mem (K.b + lane) 1 = some [byte] := by
  obtain ⟨lane, byte, hent, -, hbyte, hread, -⟩ := h.laneRead
  exact ⟨lane, byte, hent, hbyte, hread⟩

/-- **The head's closure, as a census.**  Every register the class rows may read
resolves at a head: the base names are `Head.baseLookups`, the read and `phi`
cells the layer equation.  A register absent from the census is not in the
head. -/
theorem stage2NoEventWalkHead_closure {K : Stage2NoEventWalkCarry} {mem : Mem}
    {k : Nat} {s : State} (h : Stage2NoEventWalkHead K mem k s) :
    ∀ r ∈ stage2NoEventWalkHeadRegs, ∃ v, lookupName s.env r = some v := by
  obtain ⟨rest, sp, fr, one, wide, lane, byte, henv, -, -, -, -, -, -, -, -⟩ :=
    h.layers
  intro r hr
  rw [stage2NoEventWalkHeadRegs, List.mem_append] at hr
  rcases hr with hbase | hcells
  · -- a base name, from the lookup predicate
    have hmem : r ∈ (stage2NoEventWalkBaseValues K).map (·.1) := by
      rw [stage2NoEventWalkBaseValues_names]
      exact hbase
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hmem
    exact ⟨p.2, h.baseLookups p.1 p.2 hp⟩
  · -- a read or `phi` cell, from the layer equation
    have hnd : ((loopHeadReadCellsAt K k sp fr one wide lane byte ++
        loopHeadPhiCellsAt K k sp fr one wide).map (·.1)).Nodup := by
      rw [List.map_append, loopHeadReadCellsAt_names, loopHeadPhiCellsAt_names]
      exact (List.nodup_append.mp stage2NoEventWalkHeadRegs_nodup).2.1
    rw [henv, ← cells_append]
    exact cells_lookup_of_name_mem _ _
      (by
        simpa only [List.map_append, loopHeadReadCellsAt_names,
          loopHeadPhiCellsAt_names] using hcells)
      hnd

/-! ### The entry stream's monotonicity

The potential's byte term reads the entry at the head index and the index only
rises, so the entry positions do not fall.  The certified walk reads the same
fact from its own geometry (`JsonStage2WalkTraverse`'s `pairwise_lt_getD_le`);
here it is stated at the invariant's `order`. -/

/-- **A strictly increasing entry stream does not fall as the index rises.** -/
theorem stage2NoEventEnt_getD_le {l : List Nat} (hs : l.Pairwise (· < ·)) {d : Nat}
    {i j : Nat} (hij : i ≤ j) (hj : j < l.length) : l.getD i d ≤ l.getD j d := by
  have hi : i < l.length := lt_of_le_of_lt hij hj
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hj]
  simp only [Option.getD_some]
  rcases Nat.lt_or_eq_of_le hij with h | h
  · exact le_of_lt ((List.pairwise_iff_getElem.mp hs) i j hi hj h)
  · subst h
    exact le_rfl

/-! ### The class tables

Each table is the body's dispatch pivot at one block, as a closed vocabulary: a
constructor per class, carrying the pivot's guard.  `complete` says the classes
cover the pivot's domain, so a row may `cases` the class and need no fallthrough
guard of its own.  The guards are the body's comparisons, written on the byte's
`Nat` value; the head's `%3` cell is an `i8`, so "byte" means `byte.toNat < 256`.
-/

/-- The head block's dispatch (`NodeBlock5` and its tree, at `%3`): a string
starts on `"` (34), a bracketed value on `[` (91), a braced one on `{` (123), and
every other byte is a scalar value. -/
inductive Stage2NoEventHeadClass (x : Nat) : Type
  /-- `"` — a string. -/
  | string (h : x = 34)
  /-- `[` — an array. -/
  | bracket (h : x = 91)
  /-- `{` — an object. -/
  | brace (h : x = 123)
  /-- Anything else — a scalar value. -/
  | value (h34 : x ≠ 34) (h91 : x ≠ 91) (h123 : x ≠ 123)

/-- **The head table is exhaustive.** -/
def stage2NoEventHeadClass_complete (x : Nat) : Stage2NoEventHeadClass x := by
  by_cases h34 : x = 34
  · exact .string h34
  by_cases h91 : x = 91
  · exact .bracket h91
  by_cases h123 : x = 123
  · exact .brace h123
  · exact .value h34 h91 h123

/-- The continuation block's dispatch (`NodeBlock15` at `%7`): the same four
classes, at the byte the next iteration read. -/
inductive Stage2NoEventContinuationClass (x : Nat) : Type
  /-- `"` — a string. -/
  | string (h : x = 34)
  /-- `[` — an array. -/
  | bracket (h : x = 91)
  /-- `{` — an object. -/
  | brace (h : x = 123)
  /-- Anything else — a scalar value. -/
  | value (h34 : x ≠ 34) (h91 : x ≠ 91) (h123 : x ≠ 123)

/-- **The continuation table is exhaustive.** -/
def stage2NoEventContinuationClass_complete (x : Nat) :
    Stage2NoEventContinuationClass x := by
  by_cases h34 : x = 34
  · exact .string h34
  by_cases h91 : x = 91
  · exact .bracket h91
  by_cases h123 : x = 123
  · exact .brace h123
  · exact .value h34 h91 h123

/-- The value dispatch (`scalar`/`cond.end`/`land.lhs.true`/`if.end457` at
`%.lcssa`): whitespace, a number or a leading minus, a literal, or a refusal.
The number class's guard is the body's `eq 45 || ult (x + 208) 10`, which for a
byte is `-` or a decimal digit (`48 ≤ x ≤ 57`). -/
inductive Stage2NoEventValueClass (x : Nat) : Type
  /-- A space, a horizontal tab, a line feed or a carriage return. -/
  | ws (h : x = 9 ∨ x = 10 ∨ x = 13 ∨ x = 32)
  /-- `-` or a decimal digit. -/
  | numberOrMinus (h : x = 45 ∨ (48 ≤ x ∧ x ≤ 57))
  /-- `f` (false), `n` (null) or `t` (true). -/
  | literal (h : x = 102 ∨ x = 110 ∨ x = 116)
  /-- Anything else — a refusal. -/
  | other (hws : ¬ (x = 9 ∨ x = 10 ∨ x = 13 ∨ x = 32))
      (hnum : ¬ (x = 45 ∨ (48 ≤ x ∧ x ≤ 57)))
      (hlit : ¬ (x = 102 ∨ x = 110 ∨ x = 116))

/-- **The value table is exhaustive.** -/
def stage2NoEventValueClass_complete (x : Nat) : Stage2NoEventValueClass x := by
  by_cases hws : (x = 9 ∨ x = 10 ∨ x = 13 ∨ x = 32)
  · exact .ws hws
  by_cases hnum : (x = 45 ∨ (48 ≤ x ∧ x ≤ 57))
  · exact .numberOrMinus hnum
  by_cases hlit : (x = 102 ∨ x = 110 ∨ x = 116)
  · exact .literal hlit
  · exact .other hws hnum hlit

/-- The after-value dispatch (`after_value`/`if.end378`/`if.end410`/`NodeBlock41`
at `%frame.6` and the next byte): the frame's zero test splits the closers and the
commas, and everything else refuses. -/
inductive Stage2NoEventAfterValueClass (frame x : Nat) : Type
  /-- A `}` at depth zero. -/
  | closeBrace (hf : frame = 0) (h : x = 125)
  /-- A `,` at depth zero. -/
  | commaZero (hf : frame = 0) (h : x = 44)
  /-- A `]` at nonzero depth. -/
  | closeBracket (hf : frame ≠ 0) (h : x = 93)
  /-- A `,` at nonzero depth. -/
  | commaDeep (hf : frame ≠ 0) (h : x = 44)
  /-- Anything else — a refusal. -/
  | other (h : ¬ ((frame = 0 ∧ x = 125) ∨ (frame = 0 ∧ x = 44) ∨
      (frame ≠ 0 ∧ x = 93) ∨ (frame ≠ 0 ∧ x = 44)))

/-- **The after-value table is exhaustive.** -/
def stage2NoEventAfterValueClass_complete (frame x : Nat) :
    Stage2NoEventAfterValueClass frame x := by
  by_cases hf : frame = 0
  · by_cases h125 : x = 125
    · exact .closeBrace hf h125
    by_cases h44 : x = 44
    · exact .commaZero hf h44
    · exact .other (by
        rintro (⟨-, h⟩ | ⟨-, h⟩ | ⟨hn, -⟩ | ⟨hn, -⟩)
        · exact h125 h
        · exact h44 h
        · exact hn hf
        · exact hn hf)
  · by_cases h93 : x = 93
    · exact .closeBracket hf h93
    by_cases h44 : x = 44
    · exact .commaDeep hf h44
    · exact .other (by
        rintro (⟨h0, -⟩ | ⟨h0, h⟩ | ⟨-, h⟩ | ⟨-, h⟩)
        · exact hf h0
        · exact hf h0
        · exact h93 h
        · exact h44 h)

/-- The pair dispatch (`expect_colon`/`if.end303` at the byte after the key): a
colon continues to the value, anything else refuses. -/
inductive Stage2NoEventPairClass (x : Nat) : Type
  /-- `:` — the value follows. -/
  | colon (h : x = 58)
  /-- Anything else — a refusal. -/
  | other (h : x ≠ 58)

/-- **The pair table is exhaustive.** -/
def stage2NoEventPairClass_complete (x : Nat) : Stage2NoEventPairClass x := by
  by_cases h : x = 58
  · exact .colon h
  · exact .other h

/-! ### The head segment

The plain segment and its lemmas are unchanged; the head segment adds the target's
`Head` and `Trace`, which is what the loop's next visit and the row's continuing
branch need.  The target facts are the route's own final steps' — the head read's
binding and the trace's append — not projections of a chain. -/

/-- **A counted segment whose target is a head.**  The segment's own run and
invariant, and the target's `Head` and `Trace`. -/
structure Stage2NoEventWalkHeadSegment (calls : Calls) (mem : Mem)
    (K : Stage2NoEventWalkCarry) (k : Nat) (s : State)
    (K' : Stage2NoEventWalkCarry) (k' : Nat) (s' : State) (j : Nat) : Prop where
  /-- The counted segment. -/
  seg : Stage2NoEventWalkSegment calls mem K s K' s' j
  /-- The target's head. -/
  head' : Stage2NoEventWalkHead K' mem k' s'
  /-- The target's output evidence. -/
  trace' : Stage2NoEventWalkTrace K'

/-- **Head segments compose**, at the counts' sum; the target's head and trace
are the second's. -/
theorem Stage2NoEventWalkHeadSegment.trans {calls : Calls} {mem : Mem}
    {K K' K'' : Stage2NoEventWalkCarry} {k k' k'' : Nat} {s s' s'' : State} {j kk : Nat}
    (h₁ : Stage2NoEventWalkHeadSegment calls mem K k s K' k' s' j)
    (h₂ : Stage2NoEventWalkHeadSegment calls mem K' k' s' K'' k'' s'' kk) :
    Stage2NoEventWalkHeadSegment calls mem K k s K'' k'' s'' (j + kk) where
  seg := h₁.seg.trans h₂.seg
  head' := h₂.head'
  trace' := h₂.trace'

/-- **A head segment that ends in a return.**  The segment's count plus one is
the run's fuel at every larger budget. -/
theorem Stage2NoEventWalkHeadSegment.ret {calls : Calls} {mem : Mem}
    {K K' : Stage2NoEventWalkCarry} {k k' : Nat} {s s' sret : State} {j : Nat} {v : Value}
    (h : Stage2NoEventWalkHeadSegment calls mem K k s K' k' s' j)
    (hret : step calls stage2NoEventBody s' = .ret v sret) :
    ∀ N, j + 1 ≤ N → runFuel calls N stage2NoEventBody s = some (.ret v sret.mem) :=
  h.seg.ret hret

/-- **A chain to a head is a head segment.**  `of_chain` supplies the segment;
the target's `Head` and `Trace` are the route's own final-state facts. -/
theorem Stage2NoEventWalkHeadSegment.of_head_chain {calls : Calls} {mem : Mem}
    {K K' : Stage2NoEventWalkCarry} {k k' : Nat} {s s' : State}
    (h : Stage2NoEventWalkChain calls mem K s K' s')
    (head' : Stage2NoEventWalkHead K' mem k' s')
    (trace' : Stage2NoEventWalkTrace K') :
    ∃ j, Stage2NoEventWalkHeadSegment calls mem K k s K' k' s' j := by
  obtain ⟨j, hj⟩ := h.steps
  exact ⟨j, ⟨hj, Stage2NoEventWalkChain.inv h⟩, head', trace'⟩

/-- **A priced head segment**: the head segment and the potential's credit. -/
structure Stage2NoEventWalkHeadPricedSegment (calls : Calls) (mem : Mem)
    (K : Stage2NoEventWalkCarry) (k : Nat) (s : State)
    (K' : Stage2NoEventWalkCarry) (k' : Nat) (s' : State) (p : Nat) : Prop where
  /-- The head segment, its run and its target's facts. -/
  seg : Stage2NoEventWalkHeadSegment calls mem K k s K' k' s' p
  /-- The price is payable from the credit. -/
  credit : p + stage2NoEventWalkPotential K' k' ≤ stage2NoEventWalkPotential K k

/-- **Priced head segments compose**, and so do their credits. -/
theorem Stage2NoEventWalkHeadPricedSegment.trans {calls : Calls} {mem : Mem}
    {K K' K'' : Stage2NoEventWalkCarry} {k k' k'' : Nat} {s s' s'' : State}
    {p q : Nat}
    (h₁ : Stage2NoEventWalkHeadPricedSegment calls mem K k s K' k' s' p)
    (h₂ : Stage2NoEventWalkHeadPricedSegment calls mem K' k' s' K'' k'' s'' q) :
    Stage2NoEventWalkHeadPricedSegment calls mem K k s K'' k'' s'' (p + q) where
  seg := h₁.seg.trans h₂.seg
  credit := by
    have := h₁.credit
    have := h₂.credit
    omega

/-! ### F1 — the fixed premise does not run without the head's byte

The state below is inside the old premise's quantifier: an invariant, the head
block's `pc`, the index cell, and `0 < nep`.  Its environment binds the index and
nothing else, so the head block's `%3` read is absent; the dispatch root's
comparison cannot evaluate and the step is `.ub`.  The entry count is one, so no
continuing target index exists either, and `.ub` never produces a return.  The
state is therefore outside the new premise — the head's read is what the premise
adds — and no row is inhabitable at it, which is why the old `Rows` statement
(quantified over the invariant alone) was refutable.

The memory is a zero block, wide enough for every region the invariant names; the
witness is deliberately reach-ability-free (the invariant does not constrain the
environment), which is the point: the old premise admitted it.
-/
set_option maxRecDepth 32768


def stage2NoEventWalkF1Mem : Mem := writeBytes [] 4096 (List.replicate 4200 (0 : UInt8))
theorem stage2NoEventWalkF1_getD {k : Nat} (hk : k < 4200) : (List.replicate 4200 (0:UInt8)).getD k 0 = 0 := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_replicate]; simp [hk]
theorem stage2NoEventWalkF1_readByte {a : Nat} (h1 : 4096 ≤ a) (h2 : a < 8296) : readByte stage2NoEventWalkF1Mem a = some 0 := by
  unfold stage2NoEventWalkF1Mem
  rw [show a = 4096 + (a - 4096) from by omega]
  rw [readByte_writeBytes_at [] _ 4096 (a - 4096) (by rw [List.length_replicate]; omega)]
  rw [stage2NoEventWalkF1_getD (by omega)]
theorem stage2NoEventWalkF1_present {a : Nat} (h1 : 4096 ≤ a) (h2 : a < 8296) : present stage2NoEventWalkF1Mem a := ⟨0, stage2NoEventWalkF1_readByte h1 h2⟩
theorem stage2NoEventWalkF1_readBytes_zeros {a n : Nat} (h1 : 4096 ≤ a) (h2 : a + n ≤ 8296) :
    readBytes stage2NoEventWalkF1Mem a n = some (List.replicate n 0) := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih =>
      simp only [readBytes, List.replicate_succ]
      rw [stage2NoEventWalkF1_readByte h1 (by omega)]
      rw [ih (by omega) (by omega)]
theorem stage2NoEventWalkF1_hasBytes {a n : Nat} (h1 : 4096 ≤ a) (h2 : a + n ≤ 8296) : HasBytes stage2NoEventWalkF1Mem a n :=
  ⟨_, stage2NoEventWalkF1_readBytes_zeros h1 h2⟩
theorem stage2NoEventWalkF1_doc : readBytes stage2NoEventWalkF1Mem 4096 1 = some [0] := by
  have := stage2NoEventWalkF1_readBytes_zeros (a := 4096) (n := 1) (by omega) (by omega)
  simpa using this
theorem stage2NoEventWalkF1_bytes4 (a : Nat) (h1 : 4096 ≤ a) (h2 : a + 4 ≤ 8296) : readBytes stage2NoEventWalkF1Mem a 4 = some [0,0,0,0] := by
  have := stage2NoEventWalkF1_readBytes_zeros (a := a) (n := 4) h1 h2
  simpa using this
theorem stage2NoEventWalkF1_entries : readLanes32 stage2NoEventWalkF1Mem 4160 1 = some [0] := by
  simp only [readLanes32, stage2NoEventWalkF1_bytes4 4160 (by omega) (by omega)]
  rfl

def stage2NoEventWalkF1K : Stage2NoEventWalkCarry :=
  { a12 := [.ptr 4096, .int 64 (BitVec.ofNat 64 1), .ptr 4160,
      .int 64 (BitVec.ofNat 64 1), .ptr 4200, .int 64 (BitVec.ofNat 64 0),
      .ptr 4224, .int 64 (BitVec.ofNat 64 65), .ptr 4300, .ptr 4312, .ptr 4324,
      .ptr 4336]
    next0 := 8192, b := 4096, n := 1, ep := 4160, nep := 1, xp := 4200, nxp := 0,
    scratch := 4224, scratchcap := 65, tokensOut := 4300, valuesOut := 4312,
    sumOut := 4324, err := 4336, bs := [0], ent := [0], stk := 4352, d := 6112,
    xj := 8192, e := 4880, c := 4912, tok := 0, terms := 0, arena := [],
    arenaWord := 0, nextEnd := 8228 }

def stage2NoEventWalkF1S : State :=
  { env := [("%k.0.ph1404", .int 64 (BitVec.ofNat 64 0))], mem := stage2NoEventWalkF1Mem, next := 0,
    pc := "NodeBlock5", pre := none }

theorem stage2NoEventWalkF1_inv : Stage2NoEventWalkInv stage2NoEventWalkF1K stage2NoEventWalkF1Mem stage2NoEventWalkF1S := by
  refine
    { args_eq := rfl
      doc := stage2NoEventWalkF1_doc
      tail := stage2NoEventWalkF1_hasBytes (a := 4097) (n := 32) (by omega) (by omega)
      entries := stage2NoEventWalkF1_entries
      order := by decide
      inside := by intro q hq; simp only [stage2NoEventWalkF1K, List.mem_cons, List.not_mem_nil, or_false] at hq; show q < 1; omega
      esc := stage2NoEventWalkF1_hasBytes (a := 4200) (n := 0) (by omega) (by omega)
      scratchBytes := stage2NoEventWalkF1_hasBytes (a := 4224) (n := 65) (by omega) (by omega)
      scratchRoom := by decide
      tokensBytes := stage2NoEventWalkF1_hasBytes (a := 4300) (n := 8) (by omega) (by omega)
      valuesBytes := stage2NoEventWalkF1_hasBytes (a := 4312) (n := 8) (by omega) (by omega)
      sumBytes := stage2NoEventWalkF1_hasBytes (a := 4324) (n := 8) (by omega) (by omega)
      errBytes := stage2NoEventWalkF1_hasBytes (a := 4336) (n := 8) (by omega) (by omega)
      maxDoc := by decide
      nLt := by decide
      scratchcapLt := by decide
      nepLt := by decide
      nxpLt := by decide
      separate := by
        unfold DisjointRegions
        simp only [stage2NoEventWalkF1K, stage2NoEventRegions, stage2NoEventWrites, stage2ReadTail]
        decide
      watermark := ?_
      stagedBytes := ?_
      stagedEnd := ?_
      sep := by
        unfold Stage2NoEventWalkSep DisjointRegions
        simp only [stage2NoEventWalkF1K, stage2NoEventRegions, stage2NoEventWrites, stage2ReadTail,
          stage2NoEventStagedRegions, stage2NoEventStackExtent, stage2NoEventErrorExtent,
          stage2NoEventCursorExtent, stage2NoEventNumExtent]
        decide
      arenaEq := by decide
      tokLe := by decide
      nextEnd_static := by decide
      walkPresent := ?_
      walkFrame := by intro a ha; rfl }
  · intro r hr
    simp only [stage2NoEventWalkF1K, stage2NoEventRegions, stage2NoEventWrites, stage2ReadTail,
      List.mem_append, List.mem_cons, List.mem_singleton, List.not_mem_nil,
      or_false] at hr
    rcases hr with (rfl | rfl | rfl | rfl) | rfl | rfl | rfl | rfl <;> decide
  · intro r hr
    simp only [stage2NoEventWalkF1K, stage2NoEventStagedRegions, stage2NoEventStackExtent,
      stage2NoEventErrorExtent, stage2NoEventCursorExtent, stage2NoEventNumExtent,
      List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;>
      exact stage2NoEventWalkF1_hasBytes (by omega) (by omega)
  · intro r hr
    simp only [stage2NoEventWalkF1K, stage2NoEventStagedRegions, stage2NoEventStackExtent,
      stage2NoEventErrorExtent, stage2NoEventCursorExtent, stage2NoEventNumExtent,
      List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> decide
  · intro a ha
    obtain ⟨r, hr, hlo, hhi⟩ := ha
    simp only [stage2NoEventWalkF1K, stage2NoEventRunRegions, stage2NoEventStagedRegions,
      stage2NoEventStackExtent, stage2NoEventErrorExtent, stage2NoEventCursorExtent,
      stage2NoEventNumExtent, List.mem_cons, List.mem_singleton, List.not_mem_nil,
      List.mem_append, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact stage2NoEventWalkF1_present (by omega) (by omega)

theorem stage2NoEventWalkF1_three : lookupName stage2NoEventWalkF1S.env "%3" = none := by
  show lookupName [("%k.0.ph1404", Value.int 64 (BitVec.ofNat 64 0))] "%3" = none
  rw [lookupName_cons_ne _ _ (by decide)]
  rfl

theorem stage2NoEventWalkF1_step (calls : Calls) :
    step calls stage2NoEventBody stage2NoEventWalkF1S = .ub := by
  have hnone : evalOperand stage2NoEventWalkF1S (Operand.reg "%3") = none := by
    simp only [evalOperand, stage2NoEventWalkF1_three]
  have hicmp : evalInstr calls stage2NoEventWalkF1S
      (Instr.icmp "%Pivot6" IPred.slt 8 (Operand.reg "%3")
        (Operand.imm (.int 8 (BitVec.ofNat 8 91)))) = none := by
    simp only [evalInstr, hnone]
  unfold step
  rw [show stage2NoEventWalkF1S.pc = "NodeBlock5" from rfl, nodeBlock5Block_find]
  simp only [nodeBlock5Block, nodeBlock5Instrs, hicmp, denoteRun, denoteCode,
    State.bindAll, State.bind]

theorem stage2NoEventWalkF1_noRet {calls : Calls} {s : State}
    (h : step calls stage2NoEventBody s = .ub) (n : Nat) :
    runFuel calls (n + 1) stage2NoEventBody s = some .ub := by
  simp only [runFuel, h]

theorem stage2NoEventWalkF1_witness :
    Stage2NoEventWalkInv stage2NoEventWalkF1K stage2NoEventWalkF1Mem stage2NoEventWalkF1S ∧ stage2NoEventWalkF1S.pc = "NodeBlock5" ∧
      lookupName stage2NoEventWalkF1S.env "%k.0.ph1404" = some (.int 64 (BitVec.ofNat 64 0)) ∧
      0 < stage2NoEventWalkF1K.nep ∧ lookupName stage2NoEventWalkF1S.env "%3" = none ∧
      step (stage2NoEventCalls stage2GapRecover) stage2NoEventBody stage2NoEventWalkF1S = .ub ∧
      (∀ k', ¬ (0 < k' ∧ k' < stage2NoEventWalkF1K.nep)) ∧
      (∀ N, 1 ≤ N → ¬ ∃ (q : Nat) (v : BitVec 64) (m : Mem),
        runFuel (stage2NoEventCalls stage2GapRecover) N stage2NoEventBody stage2NoEventWalkF1S =
          some (.ret (some (.int 64 v)) m)) ∧
      ¬ Stage2NoEventWalkHead stage2NoEventWalkF1K stage2NoEventWalkF1Mem 0 stage2NoEventWalkF1S := by
  refine ⟨stage2NoEventWalkF1_inv, rfl, ?_, by decide, stage2NoEventWalkF1_three,
    stage2NoEventWalkF1_step (stage2NoEventCalls stage2GapRecover), ?_, ?_, ?_⟩
  · show lookupName [("%k.0.ph1404", Value.int 64 (BitVec.ofNat 64 0))] "%k.0.ph1404"
        = some (.int 64 (BitVec.ofNat 64 0))
    rw [lookupName_cons_self]
  · intro k' h
    obtain ⟨h1, h2⟩ := h
    have hnep : stage2NoEventWalkF1K.nep = 1 := by decide
    omega
  · intro N hN h
    obtain ⟨q, v, m, hrun⟩ := h
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : N ≠ 0)
    rw [stage2NoEventWalkF1_noRet (stage2NoEventWalkF1_step (stage2NoEventCalls stage2GapRecover)) n] at hrun
    cases hrun
  · intro hh
    obtain ⟨v, hv⟩ := hh.bytePresent
    rw [stage2NoEventWalkF1_three] at hv
    cases hv



/-! ### A name the head's cell layers do not bind

The head's environment is the read cells over the `phi` cells over the base cells
over the entry chain; a name absent from all three layers is the incoming
environment's.  This is what `F2` (in `JsonStage2NoEventWalkSeed`, where the seed's
head is in scope) uses to show the loop's accumulator is not inhabitable at the
seed's head. -/

/-! ### Axiom footprints -/

#print axioms Stage2NoEventWalkHead.bytePresent
#print axioms Stage2NoEventWalkHead.classStage
#print axioms Stage2NoEventWalkHead.laneRead
#print axioms stage2NoEventWalkHead_closure
#print axioms stage2NoEventEnt_getD_le
#print axioms stage2NoEventHeadClass_complete
#print axioms stage2NoEventContinuationClass_complete
#print axioms stage2NoEventValueClass_complete
#print axioms stage2NoEventAfterValueClass_complete
#print axioms stage2NoEventPairClass_complete
#print axioms Stage2NoEventWalkHeadSegment.trans
#print axioms Stage2NoEventWalkHeadSegment.ret
#print axioms Stage2NoEventWalkHeadSegment.of_head_chain
#print axioms Stage2NoEventWalkHeadPricedSegment.trans
#print axioms stage2NoEventWalkF1_witness

end LeanLLVM.Refinement
