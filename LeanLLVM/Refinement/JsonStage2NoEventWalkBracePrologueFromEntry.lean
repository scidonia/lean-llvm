/-
The no-event walk's `{` prologue assembled at `if.end19`, and the brace class's
inner route from there to the pair.

`JsonStage2NoEventWalkEntryRooted` re-roots the `{` class at
`if.then9.loopexit`: the exit stub computes the entry index and the depth word,
and `if.then9`'s seven `phi`s select the edge's operands, leaving a state at
`if.end19` with `%sp.0.lcssa1092.wide` the entry's depth, `%frame.0.lcssa1098`
the constant `1`, and the loop's index and counts unchanged.
`JsonStage2NoEventWalkRowsBrace` then exports the *eight*-block prologue from a
`Stage2NoEventWalkHead` — from the class's head block, at that head's readings —
and `JsonStage2NoEventWalkKeyRoute` consumes the prologue's cells as
`Stage2NoEventWalkEntryAPrologue` at `NodeBlock21`.  Neither states the four
blocks in between: `if.end19` (the depth test), `if.then20` (the push),
`if.end23` (the live test) and `if.end74` (the next entry's read).

This module states them from a generic `if.end19` state.  The four links are
committed (`link_ifEnd19`, `link_ifThen20`, `link_ifEnd23`, `link_ifEnd74`); the
work is the cell assembly — the prologue's cells read back at the entry's own
registers instead of a head's — and the composition with the key route, which
lands at the pair endpoint fourteen steps from `if.end19`.

The four states are named (`braceTestState`, `bracePushState`, `braceLiveState`,
`braceEnd74State`) so a caller can state the key route's call supplies at the
prologue's own memory and environment: the push has written the stack by the
time entry A reads it, so those supplies cannot be stated at `if.end19`.

**What `if.end19` must already carry.**  The assembly takes the seven cells the
entry head states there, and two more: `%alen.0.ph1405` and `%arena.0.ph1406`,
the loop head's carried arena readings, which `key_body`'s `phi`s select at the
pair.  They are loop-carried values, not base cells, and the entry head's
statement omits them, so they enter the assembly as supplies at `if.end19`; the
`.loopexit`-to-`if.end19` hop is where a caller keeps them, and the assembly does
not claim them from the head.
-/
import LeanLLVM.Refinement.JsonStage2NoEventWalkKeyRoute
import LeanLLVM.Refinement.JsonStage2NoEventWalkEntryRooted

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 1600000
set_option pp.maxSteps 200000

namespace LeanLLVM.Refinement

open LeanLLVM
open LeanLLVM.JSON
open LeanLLVM.Refinement.JsonStage2NoEventIR
open LeanLLVM.Refinement.BlockEval

/-! ### The four prologue states

Each is the state its block's link delivers, at the entry's depth `sp` and frame
`fr`: the depth test, the push, the live test, and the next entry's read.  They
are definitions, not existentials, so the key route's supplies can be stated at
`braceEnd74State`'s memory and environment directly.
-/

/-- `if.end19`'s false arm, at the entry's depth: the `%tobool.not` test. -/
def braceTestState (s : State) (sp : Nat) : State :=
  stage2NoEventWalkNext
    (("%tobool.not", .int 1 (evalICmp .eq (BitVec.ofNat 32 sp) (BitVec.ofNat 32 0)))
      :: s.env) s "if.then20"

/-- `if.then20`'s push: the frame byte written at `bracePushAddr`. -/
def bracePushState (K : Stage2NoEventWalkCarry) (s : State) (sp fr : Nat) : State :=
  stage2NoEventWalkStored
    (("%arrayidx22", .ptr (bracePushAddr K (BitVec.ofNat 32 sp))) ::
      ("%idxprom21", .int 64 (BitVec.ofNat 64
        ((BitVec.ofNat 32 sp + BitVec.ofNat 32 4294967295).toNat))) ::
      ("%sub", .int 32 (BitVec.ofNat 32 sp + BitVec.ofNat 32 4294967295)) ::
      (braceTestState s sp).env)
    (braceTestState s sp)
    (writeBytes (braceTestState s sp).mem (bracePushAddr K (BitVec.ofNat 32 sp))
      (natToBytes ((BitVec.ofNat 8 fr).toNat) 1)) "if.end23"

/-- `if.end23`'s live test: the depth one above the push's. -/
def braceLiveState (K : Stage2NoEventWalkCarry) (s : State) (sp fr : Nat) : State :=
  stage2NoEventWalkNext
    (("%cmp66.not", .int 1 1) ::
      ("%inc24", .int 32 (BitVec.ofNat 32 sp + BitVec.ofNat 32 1)) ::
      (bracePushState K s sp fr).env) (bracePushState K s sp fr) "if.end74"

/-- `if.end74`'s next-entry read, landing at `NodeBlock21`'s entry. -/
def braceEnd74State (K : Stage2NoEventWalkCarry) (s : State) (sp fr : Nat)
    (inc : BitVec 64) (bs4 : List UInt8) (nextByte : UInt8) : State :=
  stage2NoEventWalkNext
    (ifEnd74Out (braceLiveState K s sp fr).env K.ep K.b
      (BitVec.ofNat 64 K.terms) (BitVec.ofNat 64 K.tok) inc bs4 [nextByte])
    (braceLiveState K s sp fr) "NodeBlock21"

/-! ### `{`: the four prologue blocks from `if.end19`

From the entry head's conclusion — the depth test's state — the test's false arm
writes `%tobool.not`, `if.then20` pushes the frame and writes the stack byte,
`if.end23` adds `%inc24` at a live depth, and `if.end74` reads the next entry's
lane and byte and the two dead counts.  The link at each block is committed; the
theorem below runs them and reads back the prologue cells at `NodeBlock21`. -/

/-- **The `{` prologue's cells from `if.end19`**: four blocks from the entry
head's conclusion to `NodeBlock21`'s entry, with the cells the key route's entry A
needs at the state's own lane, byte and depth. -/
theorem stage2NoEventWalkBracePrologueFromEnd19 {calls : Calls}
    {K : Stage2NoEventWalkCarry} {mem : Mem} {k : Nat} {s : State}
    (h : Stage2NoEventWalkInv K mem s) (hpc : s.pc = "if.end19")
    {sp fr : Nat}
    (hspH : lookupName s.env "%sp.0.lcssa1092.wide" =
      some (.int 32 (BitVec.ofNat 32 sp)))
    (hfrH : lookupName s.env "%frame.0.lcssa1098" =
      some (.int 8 (BitVec.ofNat 8 fr)))
    (hkH : lookupName s.env "%k.0.lcssa1086" =
      some (.int 64 (BitVec.ofNat 64 k)))
    (htrH : lookupName s.env "%terms.0.lcssa1080" =
      some (.int 64 (BitVec.ofNat 64 K.terms)))
    (htokH : lookupName s.env "%tokens.0.lcssa1074" =
      some (.int 64 (BitVec.ofNat 64 K.tok)))
    {inc : BitVec 64}
    (hincH : lookupName s.env "%inc.lcssa1129" = some (.int 64 inc))
    (halenH : lookupName s.env "%alen.0.ph1405" =
      some (.int 64 (BitVec.ofNat 64 K.arena.length)))
    (harenaH : lookupName s.env "%arena.0.ph1406" =
      some (.int 64 (BitVec.ofNat 64 K.arenaWord)))
    (hbase : Stage2NoEventWalkBaseLookups K s)
    (hspPos : 1 ≤ sp) (hspLe : sp ≤ 519) (hspLt : sp < 2 ^ 32)
    (hincLt : inc.toNat < 2 ^ 63)
    (hult : BitVec.ult inc (BitVec.ofNat 64 K.nep) = true)
    (bPos : 1 ≤ K.b) (count : Stage2NoEventWalkCount K k)
    {bs4 : List UInt8}
    (hlaneW : readBytes (writeBytes s.mem (bracePushAddr K (BitVec.ofNat 32 sp))
      (natToBytes ((BitVec.ofNat 8 fr).toNat) 1))
      (K.ep + inc.toNat * 4) 4 = some bs4)
    (hval4lt : bytesToNat bs4 < 2 ^ 32)
    {nextByte : UInt8}
    (hbyte1W : readBytes (writeBytes s.mem (bracePushAddr K (BitVec.ofNat 32 sp))
      (natToBytes ((BitVec.ofNat 8 fr).toNat) 1))
      (K.b + (BitVec.signExtend 64 (BitVec.ofNat 64 (bytesToNat bs4))).toNat) 1
      = some [nextByte]) :
    Stage2NoEventWalkSegment calls mem K s K
        (braceEnd74State K s sp fr inc bs4 nextByte) 4 ∧
      Nonempty (Stage2NoEventWalkBracePrologueCells K mem k
        (braceEnd74State K s sp fr inc bs4 nextByte) (bytesToNat [nextByte])
        (bytesToNat bs4) (sp + 1)) := by
  classical
  have hspvToNat : (BitVec.ofNat 32 sp).toNat = sp := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hspLt]
  have hspvPos : 1 ≤ (BitVec.ofNat 32 sp).toNat := by rw [hspvToNat]; exact hspPos
  have hspvLe : (BitVec.ofNat 32 sp).toNat ≤ 519 := by rw [hspvToNat]; exact hspLe
  -- the base table's four parameters the prologue reads
  have hstkH : lookupName s.env "%stk" = some (.ptr K.stk) :=
    hbase "%stk" (.ptr K.stk) (by
      simp only [stage2NoEventWalkBaseValues, stage2NoEventWalkParamEntries]
      exact List.mem_append_left _ (by simp))
  have hnepH : lookupName s.env "%nep" =
      some (.int 64 (BitVec.ofNat 64 K.nep)) :=
    hbase "%nep" (.int 64 (BitVec.ofNat 64 K.nep)) (by
      simp only [stage2NoEventWalkBaseValues, stage2NoEventWalkParamEntries]
      exact List.mem_append_left _ (by simp))
  have hepH : lookupName s.env "%ep" = some (.ptr K.ep) :=
    hbase "%ep" (.ptr K.ep) (by
      simp only [stage2NoEventWalkBaseValues, stage2NoEventWalkParamEntries]
      exact List.mem_append_left _ (by simp))
  have hbH : lookupName s.env "%b" = some (.ptr K.b) :=
    hbase "%b" (.ptr K.b) (by
      simp only [stage2NoEventWalkBaseValues, stage2NoEventWalkParamEntries]
      exact List.mem_append_left _ (by simp))
  -- `if.end19`: the depth test's false arm
  have L5 : Stage2NoEventWalkLink calls K mem s K (braceTestState s sp) :=
    link_ifEnd19 h hpc hspH (by rw [hspvToNat]; omega)
  have hsp5 : lookupName (braceTestState s sp).env "%sp.0.lcssa1092.wide" =
      some (.int 32 (BitVec.ofNat 32 sp)) := by
    simp only [braceTestState, stage2NoEventWalkNext]
    rw [lookupName_cons_ne _ _ (by decide)]
    exact hspH
  have hfr5 : lookupName (braceTestState s sp).env "%frame.0.lcssa1098" =
      some (.int 8 (BitVec.ofNat 8 fr)) := by
    simp only [braceTestState, stage2NoEventWalkNext]
    rw [lookupName_cons_ne _ _ (by decide)]
    exact hfrH
  have hstk5 : lookupName (braceTestState s sp).env "%stk" = some (.ptr K.stk) := by
    simp only [braceTestState, stage2NoEventWalkNext]
    rw [lookupName_cons_ne _ _ (by decide)]
    exact hstkH
  -- `if.then20`: the push
  have L6 : Stage2NoEventWalkLink calls K mem (braceTestState s sp) K
      (bracePushState K s sp fr) :=
    link_ifThen20 L5.inv' rfl hsp5 hfr5 hstk5 hspvPos hspvLe
  have hsp6 : lookupName (bracePushState K s sp fr).env "%sp.0.lcssa1092.wide" =
      some (.int 32 (BitVec.ofNat 32 sp)) := by
    simp only [bracePushState, braceTestState, stage2NoEventWalkNext,
      stage2NoEventWalkStored]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact hspH
  have hinc6 : lookupName (bracePushState K s sp fr).env "%inc.lcssa1129" =
      some (.int 64 inc) := by
    simp only [bracePushState, braceTestState, stage2NoEventWalkNext,
      stage2NoEventWalkStored]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact hincH
  have hnep6 : lookupName (bracePushState K s sp fr).env "%nep" =
      some (.int 64 (BitVec.ofNat 64 K.nep)) := by
    simp only [bracePushState, braceTestState, stage2NoEventWalkNext,
      stage2NoEventWalkStored]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact hnepH
  -- `if.end23`: the live test's true arm
  have L7 : Stage2NoEventWalkLink calls K mem (bracePushState K s sp fr) K
      (braceLiveState K s sp fr) :=
    link_ifEnd23 L6.inv' rfl hsp6 hinc6 hnep6 hult
  have hterms7 : lookupName (braceLiveState K s sp fr).env "%terms.0.lcssa1080" =
      some (.int 64 (BitVec.ofNat 64 K.terms)) := by
    simp only [braceLiveState, bracePushState, braceTestState, stage2NoEventWalkNext,
      stage2NoEventWalkStored]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact htrH
  have htok7 : lookupName (braceLiveState K s sp fr).env "%tokens.0.lcssa1074" =
      some (.int 64 (BitVec.ofNat 64 K.tok)) := by
    simp only [braceLiveState, bracePushState, braceTestState, stage2NoEventWalkNext,
      stage2NoEventWalkStored]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact htokH
  have hep7 : lookupName (braceLiveState K s sp fr).env "%ep" = some (.ptr K.ep) := by
    simp only [braceLiveState, bracePushState, braceTestState, stage2NoEventWalkNext,
      stage2NoEventWalkStored]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact hepH
  have hb7 : lookupName (braceLiveState K s sp fr).env "%b" = some (.ptr K.b) := by
    simp only [braceLiveState, bracePushState, braceTestState, stage2NoEventWalkNext,
      stage2NoEventWalkStored]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact hbH
  have hinc7 : lookupName (braceLiveState K s sp fr).env "%inc.lcssa1129" =
      some (.int 64 inc) := by
    simp only [braceLiveState, bracePushState, braceTestState, stage2NoEventWalkNext,
      stage2NoEventWalkStored]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact hincH
  -- `if.end74`: the next entry's read
  have L8 : Stage2NoEventWalkLink calls K mem (braceLiveState K s sp fr) K
      (braceEnd74State K s sp fr inc bs4 nextByte) :=
    link_ifEnd74 L7.inv' rfl hterms7 htok7 hep7 hb7 hinc7 hincLt hlaneW hval4lt hbyte1W
  -- the prologue's cells at `NodeBlock21`'s entry
  have h11 : lookupName (braceEnd74State K s sp fr inc bs4 nextByte).env "%11" =
      some (.int 8 (BitVec.ofNat 8 (bytesToNat [nextByte]))) := by
    simp only [braceEnd74State, stage2NoEventWalkNext, ifEnd74Out, ifEnd74Cells,
      cells, stage2NoEventWalkBytesToNat_single]
    rw [lookupName_cons_self]
  have h10c : lookupName (braceEnd74State K s sp fr inc bs4 nextByte).env "%10" =
      some (.int 32 (BitVec.ofNat 32 (bytesToNat bs4))) := by
    simp only [braceEnd74State, stage2NoEventWalkNext, ifEnd74Out, ifEnd74Cells, cells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    rw [lookupName_cons_self]
  have hinc24 : lookupName (braceEnd74State K s sp fr inc bs4 nextByte).env "%inc24" =
      some (.int 32 (BitVec.ofNat 32 (sp + 1))) := by
    simp only [braceEnd74State, braceLiveState, bracePushState, braceTestState,
      stage2NoEventWalkNext, stage2NoEventWalkStored, ifEnd74Out, ifEnd74Cells, cells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    rw [lookupName_cons_self]
    simp only [stage2NoEventWalkOfNat_add]
  have hk8 : lookupName (braceEnd74State K s sp fr inc bs4 nextByte).env
      "%k.0.lcssa1086" = some (.int 64 (BitVec.ofNat 64 k)) := by
    simp only [braceEnd74State, braceLiveState, bracePushState, braceTestState,
      stage2NoEventWalkNext, stage2NoEventWalkStored, ifEnd74Out, ifEnd74Cells, cells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact hkH
  have htrPhi : lookupName (braceEnd74State K s sp fr inc bs4 nextByte).env
      "%terms.0.lcssa1080" = some (.int 64 (BitVec.ofNat 64 K.terms)) := by
    simp only [braceEnd74State, braceLiveState, bracePushState, braceTestState,
      stage2NoEventWalkNext, stage2NoEventWalkStored, ifEnd74Out, ifEnd74Cells, cells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact htrH
  have htokPhi : lookupName (braceEnd74State K s sp fr inc bs4 nextByte).env
      "%tokens.0.lcssa1074" = some (.int 64 (BitVec.ofNat 64 K.tok)) := by
    simp only [braceEnd74State, braceLiveState, bracePushState, braceTestState,
      stage2NoEventWalkNext, stage2NoEventWalkStored, ifEnd74Out, ifEnd74Cells, cells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact htokH
  have halen8 : lookupName (braceEnd74State K s sp fr inc bs4 nextByte).env
      "%alen.0.ph1405" = some (.int 64 (BitVec.ofNat 64 K.arena.length)) := by
    simp only [braceEnd74State, braceLiveState, bracePushState, braceTestState,
      stage2NoEventWalkNext, stage2NoEventWalkStored, ifEnd74Out, ifEnd74Cells, cells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact halenH
  have harena8 : lookupName (braceEnd74State K s sp fr inc bs4 nextByte).env
      "%arena.0.ph1406" = some (.int 64 (BitVec.ofNat 64 K.arenaWord)) := by
    simp only [braceEnd74State, braceLiveState, bracePushState, braceTestState,
      stage2NoEventWalkNext, stage2NoEventWalkStored, ifEnd74Out, ifEnd74Cells, cells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact harenaH
  have hadd : lookupName (braceEnd74State K s sp fr inc bs4 nextByte).env "%add" =
      some (.int 64 (BitVec.ofNat 64 (K.terms + 1))) := by
    simp only [braceEnd74State, stage2NoEventWalkNext, ifEnd74Out, ifEnd74Cells, cells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    rw [lookupName_cons_self]
    simp only [stage2NoEventWalkOfNat_add]
  have hinc26 : lookupName (braceEnd74State K s sp fr inc bs4 nextByte).env "%inc26" =
      some (.int 64 (BitVec.ofNat 64 (K.tok + 1))) := by
    simp only [braceEnd74State, stage2NoEventWalkNext, ifEnd74Out, ifEnd74Cells, cells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    rw [lookupName_cons_self]
    simp only [stage2NoEventWalkOfNat_add]
  -- the base table through the four links' cell layers
  have hbase8 : Stage2NoEventWalkBaseLookups K
      (braceEnd74State K s sp fr inc bs4 nextByte) := by
    have hb0 : ∀ n v, (n, v) ∈ stage2NoEventWalkBaseValues K →
        lookupName s.env n = some v := hbase
    have b1 := stage2NoEventCycleBase (K := K) (env := s.env) hb0
      (cs := [("%tobool.not", .int 1 (evalICmp .eq (BitVec.ofNat 32 sp)
        (BitVec.ofNat 32 0)))]) (names := ["%tobool.not"]) rfl (by decide)
    have b2 := stage2NoEventCycleBase (K := K) b1
      (cs := [("%arrayidx22", .ptr (bracePushAddr K (BitVec.ofNat 32 sp))),
        ("%idxprom21", .int 64 (BitVec.ofNat 64
          ((BitVec.ofNat 32 sp + BitVec.ofNat 32 4294967295).toNat))),
        ("%sub", .int 32 (BitVec.ofNat 32 sp + BitVec.ofNat 32 4294967295))])
      (names := ["%arrayidx22", "%idxprom21", "%sub"]) rfl (by decide)
    have b3 := stage2NoEventCycleBase (K := K) b2
      (cs := [("%cmp66.not", .int 1 1),
        ("%inc24", .int 32 (BitVec.ofNat 32 sp + BitVec.ofNat 32 1))])
      (names := ["%cmp66.not", "%inc24"]) rfl (by decide)
    have b4 := stage2NoEventCycleBase (K := K) b3
      (cs := ifEnd74Cells K.ep K.b (BitVec.ofNat 64 K.terms) (BitVec.ofNat 64 K.tok)
        inc bs4 [nextByte])
      (names := ["%11", "%arrayidx77", "%idxprom76", "%10", "%arrayidx75",
        "%inc26", "%add"]) rfl (by decide)
    intro n v hv
    exact b4 n v hv
  -- the run, at the four links' own fuel
  have hrun : ∀ n, runFuel calls (4 + n) stage2NoEventBody s =
      runFuel calls n stage2NoEventBody
        (braceEnd74State K s sp fr inc bs4 nextByte) := by
    intro n
    rw [show 4 + n = 1 + (1 + (1 + (1 + n))) from by omega]
    rw [stage2NoEventWalkLink_runFuel L5, stage2NoEventWalkLink_runFuel L6,
      stage2NoEventWalkLink_runFuel L7, stage2NoEventWalkLink_runFuel L8]
  refine ⟨⟨hrun, L8.inv'⟩, ⟨?_⟩⟩
  exact
    { inv := L8.inv'
      pc := rfl
      laneLt := hval4lt
      spLt := by omega
      h11 := h11
      h10 := h10c
      hinc24 := hinc24
      hk := hk8
      htermsPhi := htrPhi
      htokPhi := htokPhi
      halen := halen8
      harena := harena8
      hadd := hadd
      hinc26 := hinc26
      hbase := hbase8
      bPos := bPos
      count := count }

/-- **The `{` prologue's entry-A predicate from `if.end19`**: the same four
blocks, with the next entry's byte at the member's opening quote. -/
theorem stage2NoEventWalkEntryAPrologueFromEnd19 {calls : Calls}
    {K : Stage2NoEventWalkCarry} {mem : Mem} {k : Nat} {s : State}
    (h : Stage2NoEventWalkInv K mem s) (hpc : s.pc = "if.end19")
    {sp fr : Nat}
    (hspH : lookupName s.env "%sp.0.lcssa1092.wide" =
      some (.int 32 (BitVec.ofNat 32 sp)))
    (hfrH : lookupName s.env "%frame.0.lcssa1098" =
      some (.int 8 (BitVec.ofNat 8 fr)))
    (hkH : lookupName s.env "%k.0.lcssa1086" =
      some (.int 64 (BitVec.ofNat 64 k)))
    (htrH : lookupName s.env "%terms.0.lcssa1080" =
      some (.int 64 (BitVec.ofNat 64 K.terms)))
    (htokH : lookupName s.env "%tokens.0.lcssa1074" =
      some (.int 64 (BitVec.ofNat 64 K.tok)))
    {inc : BitVec 64}
    (hincH : lookupName s.env "%inc.lcssa1129" = some (.int 64 inc))
    (halenH : lookupName s.env "%alen.0.ph1405" =
      some (.int 64 (BitVec.ofNat 64 K.arena.length)))
    (harenaH : lookupName s.env "%arena.0.ph1406" =
      some (.int 64 (BitVec.ofNat 64 K.arenaWord)))
    (hbase : Stage2NoEventWalkBaseLookups K s)
    (hspPos : 1 ≤ sp) (hspLe : sp ≤ 519) (hspLt : sp < 2 ^ 32)
    (hincLt : inc.toNat < 2 ^ 63)
    (hult : BitVec.ult inc (BitVec.ofNat 64 K.nep) = true)
    (bPos : 1 ≤ K.b) (count : Stage2NoEventWalkCount K k)
    {bs4 : List UInt8}
    (hlaneW : readBytes (writeBytes s.mem (bracePushAddr K (BitVec.ofNat 32 sp))
      (natToBytes ((BitVec.ofNat 8 fr).toNat) 1))
      (K.ep + inc.toNat * 4) 4 = some bs4)
    (hval4lt : bytesToNat bs4 < 2 ^ 32)
    {nextByte : UInt8}
    (hbyte1W : readBytes (writeBytes s.mem (bracePushAddr K (BitVec.ofNat 32 sp))
      (natToBytes ((BitVec.ofNat 8 fr).toNat) 1))
      (K.b + (BitVec.signExtend 64 (BitVec.ofNat 64 (bytesToNat bs4))).toNat) 1
      = some [nextByte])
    (hbyte : nextByte.toNat = 34) :
    Stage2NoEventWalkSegment calls mem K s K
        (braceEnd74State K s sp fr inc bs4 nextByte) 4 ∧
      Nonempty (Stage2NoEventWalkEntryAPrologue K mem k
        (braceEnd74State K s sp fr inc bs4 nextByte)) := by
  obtain ⟨hseg, ⟨C⟩⟩ :=
    stage2NoEventWalkBracePrologueFromEnd19 (calls := calls) h hpc hspH hfrH
      hkH htrH htokH hincH halenH harenaH hbase hspPos hspLe hspLt hincLt hult
      bPos count hlaneW hval4lt hbyte1W
  have hb : bytesToNat [nextByte] = 34 := by
    rw [stage2NoEventWalkBytesToNat_single]; exact hbyte
  exact ⟨hseg, ⟨C.toEntryA hb⟩⟩

/-- **The brace class's inner route from `if.end19`**: the four prologue blocks
and the key route's ten, to the pair endpoint with the opener's `d = 1`.  The
prologue's cells are the assembly's, and the call supplies are stated at the
prologue's own memory (`braceEnd74State`) because the push has written the stack
by the time entry A reads it. -/
theorem stage2NoEventWalkBraceRouteFromEnd19 {calls : Calls} {mem : Mem}
    {K : Stage2NoEventWalkCarry} {k : Nat} {s : State}
    (h : Stage2NoEventWalkInv K mem s) (hpc : s.pc = "if.end19")
    {sp fr : Nat}
    (hspH : lookupName s.env "%sp.0.lcssa1092.wide" =
      some (.int 32 (BitVec.ofNat 32 sp)))
    (hfrH : lookupName s.env "%frame.0.lcssa1098" =
      some (.int 8 (BitVec.ofNat 8 fr)))
    (hkH : lookupName s.env "%k.0.lcssa1086" =
      some (.int 64 (BitVec.ofNat 64 k)))
    (htrH : lookupName s.env "%terms.0.lcssa1080" =
      some (.int 64 (BitVec.ofNat 64 K.terms)))
    (htokH : lookupName s.env "%tokens.0.lcssa1074" =
      some (.int 64 (BitVec.ofNat 64 K.tok)))
    {inc : BitVec 64}
    (hincH : lookupName s.env "%inc.lcssa1129" = some (.int 64 inc))
    (halenH : lookupName s.env "%alen.0.ph1405" =
      some (.int 64 (BitVec.ofNat 64 K.arena.length)))
    (harenaH : lookupName s.env "%arena.0.ph1406" =
      some (.int 64 (BitVec.ofNat 64 K.arenaWord)))
    (hbase : Stage2NoEventWalkBaseLookups K s)
    (hspPos : 1 ≤ sp) (hspLe : sp ≤ 519) (hspLt : sp < 2 ^ 32)
    (hincLt : inc.toNat < 2 ^ 63)
    (hult : BitVec.ult inc (BitVec.ofNat 64 K.nep) = true)
    (bPos : 1 ≤ K.b) (count : Stage2NoEventWalkCount K k)
    {bs4 : List UInt8}
    (hlaneW : readBytes (writeBytes s.mem (bracePushAddr K (BitVec.ofNat 32 sp))
      (natToBytes ((BitVec.ofNat 8 fr).toNat) 1))
      (K.ep + inc.toNat * 4) 4 = some bs4)
    (hval4lt : bytesToNat bs4 < 2 ^ 32)
    {nextByte : UInt8}
    (hbyte1W : readBytes (writeBytes s.mem (bracePushAddr K (BitVec.ofNat 32 sp))
      (natToBytes ((BitVec.ofNat 8 fr).toNat) 1))
      (K.b + (BitVec.signExtend 64 (BitVec.ofNat 64 (bytesToNat bs4))).toNat) 1
      = some [nextByte])
    (hbyte : nextByte.toNat = 34)
    (hvAddr : k + 4 < 2 ^ 63) (hvNext : k + 4 < K.nep)
    (hscratch : evalICmp .ugt
      (BitVec.ofNat 64 (K.ent.getD (k + 2) 0) +
        (BitVec.ofNat 64 (BitVec.ofNat 32 (bytesToNat bs4)).toNat ^^^
          BitVec.ofNat 64 18446744073709551615) + BitVec.ofNat 64 64)
      (BitVec.ofNat 64 K.scratchcap) = 0)
    (r0 : CallOutcome)
    (hstart : calls "llvm.lifetime.start.p0"
      [.int 64 (BitVec.ofNat 64 8), .ptr (K.next0 + 8)]
      (braceEnd74State K s sp fr inc bs4 nextByte).mem
      (braceEnd74State K s sp fr inc bs4 nextByte).next = some r0)
    (hstartMem : r0.mem = (braceEnd74State K s sp fr inc bs4 nextByte).mem)
    (hstartNext : r0.next = (braceEnd74State K s sp fr inc bs4 nextByte).next)
    (r : CallOutcome)
    (hcall : calls "s2_string_body"
      [.ptr K.c, .ptr (K.b + 1 + bytesToNat bs4),
       .int 64 (keySub (bytesToNat bs4) (K.ent.getD (k + 2) 0)),
       .ptr K.scratch, .ptr (K.next0 + 8), .ptr K.xp, .ptr K.next0,
       .int 64 (BitVec.ofNat 64 K.nxp)]
      (writeBytes (writeBytes (braceEnd74State K s sp fr inc bs4 nextByte).mem
        (K.c + 32) (natToBytes (BitVec.ofNat 64 (k + 3)).toNat 8))
        (K.next0 + 8) (natToBytes 0 8))
      (braceEnd74State K s sp fr inc bs4 nextByte).next = some r)
    (hrRet : r.ret = .int 32 (BitVec.ofNat 32 1))
    (hcallInv : Stage2NoEventWalkInv K mem
      { braceEnd74State K s sp fr inc bs4 nextByte with mem := r.mem, next := r.next })
    (lend : CallOutcome)
    (hlend : calls "llvm.lifetime.end.p0"
      [.int 64 (BitVec.ofNat 64 8), .ptr (K.next0 + 8)] r.mem r.next
      = some lend)
    (hlendMem : lend.mem = r.mem)
    (htraceEnd : Stage2NoEventWalkTrace
      (keyCarry K (bytesToNat bs4) (K.ent.getD (k + 2) 0) (K.terms + 1)
        (K.tok + 1)))
    (hcolon : ∀ lane, K.ent[k + 3]? = some lane → K.bs.getD lane 0 = 58) :
    ∃ s' : State,
      Stage2NoEventWalkSegment calls mem K s
          (keyCarry K (bytesToNat bs4) (K.ent.getD (k + 2) 0) (K.terms + 1)
            (K.tok + 1)) s' 14 ∧
      Nonempty (Stage2NoEventWalkPairSrc calls mem
        (keyCarry K (bytesToNat bs4) (K.ent.getD (k + 2) 0) (K.terms + 1)
          (K.tok + 1)) k s') := by
  obtain ⟨hseg4, ⟨C⟩⟩ :=
    stage2NoEventWalkBracePrologueFromEnd19 (calls := calls) h hpc hspH hfrH hkH
      htrH htokH hincH halenH harenaH hbase hspPos hspLe hspLt hincLt hult bPos
      count hlaneW hval4lt hbyte1W
  have hb : bytesToNat [nextByte] = 34 := by
    rw [stage2NoEventWalkBytesToNat_single]; exact hbyte
  -- entry A's predicate at the entry's own lane and depth; the literal keeps
  -- `lane` reducible to `bytesToNat bs4` for the key route's read accesses
  let P : Stage2NoEventWalkEntryAPrologue K mem k
      (braceEnd74State K s sp fr inc bs4 nextByte) :=
    { inv := C.inv
      pc := C.pc
      lane := bytesToNat bs4
      sp := sp + 1
      laneLt := C.laneLt
      spLt := C.spLt
      h11 := by simpa only [hb] using C.h11
      h10 := C.h10
      hinc24 := C.hinc24
      hk := C.hk
      halen := C.halen
      harena := C.harena
      hadd := C.hadd
      hinc26 := C.hinc26
      hbase := C.hbase
      bPos := C.bPos
      count := C.count }
  have hlaneP : P.lane = bytesToNat bs4 := rfl
  obtain ⟨s', hseg10, hpair⟩ :=
    stage2NoEventWalkKeyRoute_of_leafBlock17 (calls := calls) (mem := mem)
      (K := K) (k := k) (s := braceEnd74State K s sp fr inc bs4 nextByte) P
      hvAddr hvNext hscratch r0 hstart hstartMem hstartNext r hcall hrRet hcallInv
      lend hlend hlendMem htraceEnd hcolon
  exact ⟨s', by simpa only [hlaneP] using hseg4.trans hseg10,
    by simpa only [hlaneP] using hpair⟩

#print axioms stage2NoEventWalkBracePrologueFromEnd19
#print axioms stage2NoEventWalkEntryAPrologueFromEnd19
#print axioms stage2NoEventWalkBraceRouteFromEnd19

end LeanLLVM.Refinement
