/-
The no-event walk's string class, from its entry: the call leg and the row.

`JsonStage2NoEventWalkRowsString` proves the head-to-`LeafBlock27` run
(`stage2NoEventWalkStringHeadToLeaf27`) as one seven-block segment stated with a
`Stage2NoEventWalkHead`; `JsonStage2NoEventWalkEntryRooted` proves the two-block
head from `string_value.loopexit` to `if.end216`'s entry and states the string
row over a consumed-count supply instead of a head.  What neither exports is:

* the **four-block call leg** from a generic `if.end216` entry to `LeafBlock27`'s
  entry — `if.end216`, `if.end230`, the `s2_string_body` call in `if.end239`, and
  the result dispatch in `NodeBlock29` — taking the registers the entry's `phi`s
  leave and the callee's outcome and frame as the caller's supplies;
* **`LeafBlock27`'s own step** to the arm's entry (`for.cond266.preheader` for a
  form of two, `do.body254` for the empty string).

This module states both without a head, and composes them with the entry head to
state the string class's row at the `.loopexit` entry, end to end.

**What is proved here and what is the caller's.**  The leg's premises are the
invariant, the entry block's three fields, the base table, the ten `phi` readings
`if.end216` inherits, the two entry positions, the body's guard, and the call's
observed outcome with its write frame.  Everything a head supplied is either an
`Stage2NoEventWalkInv` projection (`Stage2NoEventWalkInv_laneAt`, the entry
order, the document bounds), one of the ten readings, or the base table — none of
them a head.  The arm's slice after `LeafBlock27` and its endpoint are the
committed head-free producers (`stage2NoEventWalkStringArenaArm`,
`stage2NoEventWalkStringPlainTail`); the trace, the decode facts and the memory
reads at the call's returned memory are the caller's.

**The one staging the entry head omits.**  `stage2NoEventWalkStringEntryHead`
returns the two-block segment and its registers but not the base table at its
target; the leg needs the base table there (for `%ep`, `%k219`, `%n`,
`%scratchcap` and the seven `s2_string_body` arguments).  `string_value`'s two
entry links bind only `%28`, `%idxprom.le1287` and the nine `stringValueCells`,
none of them a base name, so the table transports from the entry state by
`Stage2NoEventWalkBaseLookups.consOne`.  `stage2NoEventWalkStringEntryBase`
restates the entry head with that transport in its conclusion; it is the entry
head's two links and cells, plus the table **and** the two loop-carried readings
`%alen.0.ph1405`/`%arena.0.ph1406` (which the head's statement omits and the row
needs at the entry), and minus `%cmp207.not` (the merge link consumes that
internally).
-/
import LeanLLVM.Refinement.JsonStage2NoEventWalkEntryRooted

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 6000000
set_option pp.maxSteps 200000

namespace LeanLLVM.Refinement

open LeanLLVM
open LeanLLVM.JSON
open LeanLLVM.Refinement.JsonStage2NoEventIR
open LeanLLVM.Refinement.JsonEntryIR (readLanes32)
open LeanLLVM.Refinement.BlockEval

/-! ### The lane word at a state, from the invariant

`Stage2NoEventWalkHead.laneAt` reads the entry's position and the four bytes it
was read from using `head.inv` and nothing else.  The leg starts at a state that
carries no head, so the same content is restated at the invariant. -/

/-- **The lane word at an index, from the invariant alone.**  The entry stream
gives the entry's position and the four bytes read at the state's own memory. -/
theorem stage2NoEventWalkInv_laneAt {K : Stage2NoEventWalkCarry} {mem : Mem}
    {s : State} (h : Stage2NoEventWalkInv K mem s) {i : Nat} (hi : i < K.nep) :
    ∃ q bs, K.ent[i]? = some q ∧ q < 2 ^ 32 ∧
      readBytes s.mem (K.ep + 4 * i) 4 = some bs ∧ bytesToNat bs = q := by
  obtain ⟨-, hget⟩ := readLanes32_lane (m := s.mem) (addr := K.ep)
    (n := K.nep) (l := K.ent) h.entriesAt
  obtain ⟨q, bs, hq, hread, hval⟩ := hget i hi
  have hqlt : q < 2 ^ 32 := by
    have hinside := h.inside q (List.mem_of_getElem? hq)
    have := h.maxDoc
    simp only [stage2MaxDocument] at this
    omega
  exact ⟨q, bs, hq, hqlt, hread, hval⟩

/-! ### The entry's base table

`string_value`'s two entry links cons `%28`, `%idxprom.le1287` and the nine
`stringValueCells`.  None is a base name, so `Stage2NoEventWalkBaseLookups`
reaches the entry's target unchanged.  The transport is per-cell. -/

/-- **The base table survives `stringValueCells`.** -/
theorem Stage2NoEventWalkBaseLookups.stringValueCells {K : Stage2NoEventWalkCarry}
    {s : State} {inc : BitVec 64} {lc : BitVec 32} {idx : BitVec 64}
    {sp28 : BitVec 32} {k terms tok nep : BitVec 64}
    (h : Stage2NoEventWalkBaseLookups K s) :
    Stage2NoEventWalkBaseLookups K
      { s with env := stringValueCells s.env inc lc idx sp28 k terms tok nep } := by
  show Stage2NoEventWalkBaseLookups K
    { s with env :=
        ("%cmp207.not", Value.int 1 (evalICmp .ult inc nep)) ::
        ("%tokens.0.lcssa1075", Value.int 64 tok) ::
        ("%terms.0.lcssa1081", Value.int 64 terms) ::
        ("%k.0.lcssa1087", Value.int 64 k) ::
        ("%sp.0.lcssa1093.wide", Value.int 32 sp28) ::
        ("%frame.0.lcssa1099", Value.int 8 1) ::
        ("%idxprom.lcssa1109", Value.int 64 idx) ::
        ("%.lcssa1125", Value.int 32 lc) ::
        ("%inc.lcssa1130", Value.int 64 inc) :: s.env }
  exact ((((((((h.consOne (n := "%inc.lcssa1130") (v := Value.int 64 inc) (by decide))
    |>.consOne (n := "%.lcssa1125") (v := Value.int 32 lc) (by decide))
    |>.consOne (n := "%idxprom.lcssa1109") (v := Value.int 64 idx) (by decide))
    |>.consOne (n := "%frame.0.lcssa1099") (v := Value.int 8 1) (by decide))
    |>.consOne (n := "%sp.0.lcssa1093.wide") (v := Value.int 32 sp28) (by decide))
    |>.consOne (n := "%k.0.lcssa1087") (v := Value.int 64 k) (by decide))
    |>.consOne (n := "%terms.0.lcssa1081") (v := Value.int 64 terms) (by decide))
    |>.consOne (n := "%tokens.0.lcssa1075") (v := Value.int 64 tok) (by decide))
    |>.consOne (n := "%cmp207.not") (v := Value.int 1 (evalICmp .ult inc nep)) (by decide)

/-- **`"`'s entry head, with the base table.**  The same two links and cells as
`JsonStage2NoEventWalkEntryRooted`'s `stage2NoEventWalkStringEntryHead`, restated
with the target's base table (the leg needs it) and the source's `pre` (the
`if.end216` link reads it).  The lifetime marker's outcome is the caller's
supply. -/
theorem stage2NoEventWalkStringEntryBase {calls : Calls}
    {K : Stage2NoEventWalkCarry} {mem : Mem} {s : State}
    (h : Stage2NoEventWalkInv K mem s) (hpc : s.pc = "string_value.loopexit")
    {w : BitVec 32} {iv : BitVec 64}
    (h8 : lookupName s.env "%8" = some (.int 32 w))
    (hiv : lookupName s.env "%indvars.iv" = some (.int 64 iv))
    {inc : BitVec 64} {k terms tok nep : BitVec 64}
    (hinc : lookupName s.env "%inc" = some (.int 64 inc))
    (hk : lookupName s.env "%k.0" = some (.int 64 k))
    (htr : lookupName s.env "%terms.0" = some (.int 64 terms))
    (htok : lookupName s.env "%tokens.0" = some (.int 64 tok))
    {o : Nat}
    (houtn : lookupName s.env "%outn205" = some (.ptr o))
    (hnep : lookupName s.env "%nep" = some (.int 64 nep))
    {r : CallOutcome}
    (hcall : calls "llvm.lifetime.start.p0"
      [.int 64 (BitVec.ofNat 64 8), .ptr o] s.mem s.next = some r)
    (hmem : r.mem = s.mem) (hnext : r.next = s.next)
    (hguard : evalICmp .ult inc nep = 1)
    {alen arenaWord : Nat}
    (halen : lookupName s.env "%alen.0.ph1405" = some (.int 64 (BitVec.ofNat 64 alen)))
    (harena : lookupName s.env "%arena.0.ph1406" =
      some (.int 64 (BitVec.ofNat 64 arenaWord)))
    (hbase : Stage2NoEventWalkBaseLookups K s) :
    ∃ sE : State,
      Stage2NoEventWalkSegment calls mem K s K sE 2 ∧
      sE.pc = "if.end216" ∧
      sE.mem = r.mem ∧ sE.next = s.next ∧
      lookupName sE.env "%inc.lcssa1130" = some (.int 64 inc) ∧
      lookupName sE.env "%.lcssa1125" = some (.int 32 w) ∧
      lookupName sE.env "%idxprom.lcssa1109" =
        some (.int 64 (BitVec.ofNat 64 w.toNat)) ∧
      lookupName sE.env "%frame.0.lcssa1099" = some (.int 8 1) ∧
      lookupName sE.env "%sp.0.lcssa1093.wide" =
        some (.int 32 (BitVec.ofNat 32 (iv.toNat % 2 ^ 32))) ∧
      lookupName sE.env "%k.0.lcssa1087" = some (.int 64 k) ∧
      lookupName sE.env "%terms.0.lcssa1081" = some (.int 64 terms) ∧
      lookupName sE.env "%tokens.0.lcssa1075" = some (.int 64 tok) ∧
      lookupName sE.env "%alen.0.ph1405" = some (.int 64 (BitVec.ofNat 64 alen)) ∧
      lookupName sE.env "%arena.0.ph1406" =
        some (.int 64 (BitVec.ofNat 64 arenaWord)) ∧
      Stage2NoEventWalkBaseLookups K sE := by
  let sp28 : BitVec 32 := BitVec.ofNat 32 (iv.toNat % 2 ^ 32)
  let idx : BitVec 64 := BitVec.ofNat 64 w.toNat
  let S1 : State := stage2NoEventWalkNext
    (("%28", .int 32 sp28) :: ("%idxprom.le1287", .int 64 idx) :: s.env)
    s "string_value"
  have L1 : Stage2NoEventWalkLink calls K mem s K S1 :=
    link_stringValueLoopexitEntry h hpc h8 hiv
  have hpc1 : S1.pc = "string_value" := by simp only [S1, stage2NoEventWalkNext]
  have hpre1 : S1.pre = some "string_value.loopexit" := by
    simp only [S1, stage2NoEventWalkNext, hpc]
  have hinc1 : lookupName S1.env "%inc" = some (.int 64 inc) := by
    simp only [S1, stage2NoEventWalkNext]
    rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide)]
    exact hinc
  have h8_1 : lookupName S1.env "%8" = some (.int 32 w) := by
    simp only [S1, stage2NoEventWalkNext]
    rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide)]
    exact h8
  have hidx1 : lookupName S1.env "%idxprom.le1287" = some (.int 64 idx) := by
    simp only [S1, stage2NoEventWalkNext, idx]
    rw [lookupName_cons_ne _ _ (by decide)]
    simp only [lookupName_cons_self]
  have hsp1 : lookupName S1.env "%28" = some (.int 32 sp28) := by
    simp only [S1, stage2NoEventWalkNext, sp28]
    simp only [lookupName_cons_self]
  have hk1 : lookupName S1.env "%k.0" = some (.int 64 k) := by
    simp only [S1, stage2NoEventWalkNext]
    rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide)]
    exact hk
  have htr1 : lookupName S1.env "%terms.0" = some (.int 64 terms) := by
    simp only [S1, stage2NoEventWalkNext]
    rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide)]
    exact htr
  have htok1 : lookupName S1.env "%tokens.0" = some (.int 64 tok) := by
    simp only [S1, stage2NoEventWalkNext]
    rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide)]
    exact htok
  have houtn1 : lookupName S1.env "%outn205" = some (.ptr o) := by
    simp only [S1, stage2NoEventWalkNext]
    rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide)]
    exact houtn
  have hnep1 : lookupName S1.env "%nep" = some (.int 64 nep) := by
    simp only [S1, stage2NoEventWalkNext]
    rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide)]
    exact hnep
  have hcall' : calls "llvm.lifetime.start.p0"
      [.int 64 (BitVec.ofNat 64 8), .ptr o] S1.mem S1.next = some r := by
    simp only [S1, stage2NoEventWalkNext]
    exact hcall
  have hmem' : r.mem = S1.mem := by
    simp only [S1, stage2NoEventWalkNext]; exact hmem
  have hnext' : r.next = S1.next := by
    simp only [S1, stage2NoEventWalkNext]; exact hnext
  let L2 : Stage2NoEventWalkLink calls K mem S1 K
      (stage2NoEventWalkNext
        (stringValueCells S1.env inc w idx sp28 k terms tok nep) S1 "if.end216") :=
    link_stringValue_true (calls := calls) L1.inv' hpc1 hpre1 hinc1 h8_1 hidx1
      hsp1 hk1 htr1 htok1 houtn1 hnep1 hcall' hmem' hnext' hguard
  let sE : State := stage2NoEventWalkNext
    (stringValueCells S1.env inc w idx sp28 k terms tok nep) S1 "if.end216"
  have hmemE : sE.mem = r.mem := by
    simp only [sE, stage2NoEventWalkNext]; exact hmem.symm
  have hnextE : sE.next = s.next := by
    simp only [sE, S1, stage2NoEventWalkNext]
  have hincE : lookupName sE.env "%inc.lcssa1130" = some (.int 64 inc) := by
    simp only [sE, stage2NoEventWalkNext, stringValueCells, sp28, idx]
    rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide)]
    simp only [lookupName_cons_self]
  have hlcE : lookupName sE.env "%.lcssa1125" = some (.int 32 w) := by
    simp only [sE, stage2NoEventWalkNext, stringValueCells, sp28, idx]
    rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide)]
    simp only [lookupName_cons_self]
  have hidxE : lookupName sE.env "%idxprom.lcssa1109" = some (.int 64 idx) := by
    simp only [sE, stage2NoEventWalkNext, stringValueCells, sp28, idx]
    rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide)]
    simp only [lookupName_cons_self]
  have hfrE : lookupName sE.env "%frame.0.lcssa1099" = some (.int 8 1) := by
    simp only [sE, stage2NoEventWalkNext, stringValueCells, sp28, idx]
    rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide)]
    simp only [lookupName_cons_self]
  have hspE : lookupName sE.env "%sp.0.lcssa1093.wide" = some (.int 32 sp28) := by
    simp only [sE, stage2NoEventWalkNext, stringValueCells, sp28, idx]
    rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide)]
    simp only [lookupName_cons_self]
  have hkE : lookupName sE.env "%k.0.lcssa1087" = some (.int 64 k) := by
    simp only [sE, stage2NoEventWalkNext, stringValueCells, sp28, idx]
    rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide)]
    simp only [lookupName_cons_self]
  have htrE : lookupName sE.env "%terms.0.lcssa1081" = some (.int 64 terms) := by
    simp only [sE, stage2NoEventWalkNext, stringValueCells, sp28, idx]
    rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide)]
    simp only [lookupName_cons_self]
  have htokE : lookupName sE.env "%tokens.0.lcssa1075" = some (.int 64 tok) := by
    simp only [sE, stage2NoEventWalkNext, stringValueCells, sp28, idx]
    rw [lookupName_cons_ne _ _ (by decide)]
    simp only [lookupName_cons_self]
  have hbase1 : Stage2NoEventWalkBaseLookups K S1 := by
    have h1 : Stage2NoEventWalkBaseLookups K
        { s with env := ("%idxprom.le1287", .int 64 idx) :: s.env } :=
      hbase.consOne (n := "%idxprom.le1287") (v := .int 64 idx) (by decide)
    have h2 : Stage2NoEventWalkBaseLookups K
        { { s with env := ("%idxprom.le1287", .int 64 idx) :: s.env } with
          env := ("%28", .int 32 sp28) ::
            ("%idxprom.le1287", .int 64 idx) :: s.env } :=
      h1.consOne (n := "%28") (v := .int 32 sp28) (by decide)
    exact h2.congr_env (by simp only [S1, stage2NoEventWalkNext])
  have hbaseE : Stage2NoEventWalkBaseLookups K sE :=
    (hbase1.stringValueCells (inc := inc) (lc := w) (idx := idx) (sp28 := sp28)
      (k := k) (terms := terms) (tok := tok) (nep := nep)).congr_env
      (by simp only [sE, stage2NoEventWalkNext, stringValueCells])
  have halenE : lookupName sE.env "%alen.0.ph1405" =
      some (.int 64 (BitVec.ofNat 64 alen)) := by
    simp only [sE, S1, stage2NoEventWalkNext, stringValueCells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact halen
  have harenaE : lookupName sE.env "%arena.0.ph1406" =
      some (.int 64 (BitVec.ofNat 64 arenaWord)) := by
    simp only [sE, S1, stage2NoEventWalkNext, stringValueCells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact harena
  exact ⟨sE, (stage2NoEventWalkStringRowLinkSegment L1).trans
      (stage2NoEventWalkStringRowLinkSegment L2), rfl, hmemE, hnextE, hincE, hlcE,
    hidxE, hfrE, hspE, hkE, htrE, htokE, halenE, harenaE, hbaseE⟩

/-! ### The four-block call leg

`if.end216` reads the closing entry's lane word and takes its store-and-test edge,
`if.end230` forms the body's length and checks the scratch reserve, `if.end239`
calls `s2_string_body`, and `NodeBlock29` dispatches the result.  The source is
any state at `if.end216`'s entry with the `phi` registers the entry block leaves;
there is no head. -/

/-- **The string call leg, from a generic `if.end216` entry**: `if.end216`,
`if.end230`, the call in `if.end239`, and `NodeBlock29`, four blocks to
`LeafBlock27`'s entry.  The endpoint carries the source invariant, the base
table, the result's form and the registers the two arms read. -/
theorem stage2NoEventWalkStringCallLeg {gap : Calls} {K : Stage2NoEventWalkCarry}
    {mem : Mem} {k : Nat} {s : State} {fr sp : Nat} {lane next : Nat}
    (hinv : Stage2NoEventWalkInv K mem s)
    (hpc : s.pc = "if.end216")
    (hbase : Stage2NoEventWalkBaseLookups K s)
    (hk : K.ent[k]? = some lane)
    (hk216 : lookupName s.env "%k.0.lcssa1087" = some (.int 64 (BitVec.ofNat 64 k)))
    (hinc216 : lookupName s.env "%inc.lcssa1130" =
      some (.int 64 (BitVec.ofNat 64 (k + 1))))
    (hlc216 : lookupName s.env "%.lcssa1125" = some (.int 32 (BitVec.ofNat 32 lane)))
    (hidx216 : lookupName s.env "%idxprom.lcssa1109" =
      some (.int 64 (BitVec.ofNat 64 lane)))
    (hfr216 : lookupName s.env "%frame.0.lcssa1099" = some (.int 8 (BitVec.ofNat 8 fr)))
    (hsp216 : lookupName s.env "%sp.0.lcssa1093.wide" =
      some (.int 32 (BitVec.ofNat 32 sp)))
    (htok216 : lookupName s.env "%tokens.0.lcssa1075" =
      some (.int 64 (BitVec.ofNat 64 K.tok)))
    (hterms216 : lookupName s.env "%terms.0.lcssa1081" =
      some (.int 64 (BitVec.ofNat 64 K.terms)))
    (halen216 : lookupName s.env "%alen.0.ph1405" =
      some (.int 64 (BitVec.ofNat 64 K.arena.length)))
    (harena216 : lookupName s.env "%arena.0.ph1406" =
      some (.int 64 (BitVec.ofNat 64 K.arenaWord)))
    (hk1 : K.ent[k + 1]? = some next)
    (hklt : k + 3 < K.nep)
    {form : Nat} {r : CallOutcome}
    (hret : r.ret = .int 32 (BitVec.ofNat 32 form))
    (hforms : form = 1 ∨ form = 2)
    (hscratch : next - lane - 1 + 64 ≤ K.scratchcap)
    {foot : List (Nat × Nat)}
    (hcall : stage2NoEventCalls gap "s2_string_body"
      (stage2NoEventWalkStringArgs K lane (BitVec.ofNat 64 (next - lane - 1)))
      (writeBytes (writeBytes s.mem (K.c + 32) (natToBytes (k + 2) 8))
        (K.next0 + 16) (natToBytes 0 8)) s.next = some r)
    (hframe : UnchangedOutside
      (writeBytes (writeBytes s.mem (K.c + 32) (natToBytes (k + 2) 8))
        (K.next0 + 16) (natToBytes 0 8)) r.mem foot)
    (hfoot : ∀ q ∈ foot,
      ∃ r' ∈ stage2NoEventRunRegions K.scratch K.scratchcap K.stk K.e K.c K.d ++
        [(K.next0, K.nextEnd - K.next0)], r'.1 ≤ q.1 ∧ q.1 + q.2 ≤ r'.1 + r'.2)
    (hpresent : ∀ a, inRegions
      (stage2NoEventRunRegions K.scratch K.scratchcap K.stk K.e K.c K.d) a →
        present r.mem a) :
    ∃ s27, Stage2NoEventWalkSegment (stage2NoEventCalls gap) mem K s K s27 4 ∧
      Stage2NoEventWalkInv K mem s27 ∧
      Stage2NoEventWalkBaseLookups K s27 ∧
      s27.pc = "LeafBlock27" ∧ s27.mem = r.mem ∧
      lookupName s27.env "%call243" = some (.int 32 (BitVec.ofNat 32 form)) ∧
      lookupName s27.env "%alen.0.ph1405" =
        some (.int 64 (BitVec.ofNat 64 K.arena.length)) ∧
      lookupName s27.env "%arena.0.ph1406" =
        some (.int 64 (BitVec.ofNat 64 K.arenaWord)) ∧
      lookupName s27.env "%tokens.0.lcssa1075" =
        some (.int 64 (BitVec.ofNat 64 K.tok)) ∧
      lookupName s27.env "%terms.0.lcssa1081" =
        some (.int 64 (BitVec.ofNat 64 K.terms)) ∧
      lookupName s27.env "%inc217" = some (.int 64 (BitVec.ofNat 64 (k + 2))) ∧
      lookupName s27.env "%frame.0.lcssa1099" = some (.int 8 (BitVec.ofNat 8 fr)) ∧
      lookupName s27.env "%sp.0.lcssa1093.wide" = some (.int 32 (BitVec.ofNat 32 sp)) ∧
      lookupName s27.env "%sub234" = some (.int 64 (BitVec.ofNat 64 (next - lane - 1))) ∧
      lookupName s27.env "%.lcssa1125" = some (.int 32 (BitVec.ofNat 32 lane)) := by
  classical
  have hk1lt : k + 1 < K.nep := by omega
  -- the closing entry's lane word, from the invariant
  obtain ⟨q, bs4, hentq, -, hread4, hval⟩ :=
    stage2NoEventWalkInv_laneAt hinv (i := k + 1) hk1lt
  have hqnext : q = next := Option.some.inj (by rw [← hentq, hk1])
  have hbs4next : bytesToNat bs4 = next := by rw [hval, hqnext]
  -- the class's numbers
  have hlane32 : lane < 2 ^ 32 := by
    have h1 := hinv.inside lane (List.mem_of_getElem? hk)
    have h2 := hinv.maxDoc
    simp only [stage2MaxDocument] at h2
    omega
  have hnext32 : next < 2 ^ 32 := by
    have h1 := hinv.inside next (List.mem_of_getElem? hk1)
    have h2 := hinv.maxDoc
    simp only [stage2MaxDocument] at h2
    omega
  have hlaneNext : lane < next := by
    obtain ⟨hkltL, hkval⟩ := List.getElem?_eq_some_iff.mp hk
    obtain ⟨hqltL, hqval⟩ := List.getElem?_eq_some_iff.mp hk1
    have hord := (List.pairwise_iff_getElem.mp hinv.order) k (k + 1) hkltL hqltL (by omega)
    rw [hkval, hqval] at hord
    exact hord
  have hnextN : next < K.n := hinv.inside next (List.mem_of_getElem? hk1)
  have hk2lt : k + 2 < 2 ^ 64 := by
    have h1 := hinv.nepLe
    have h2 := hinv.maxDoc
    simp only [stage2MaxDocument] at h2
    have h3 := hinv.nLt
    omega
  -- the `if.end216` instance
  let kv : BitVec 64 := BitVec.ofNat 64 k
  let incv : BitVec 64 := BitVec.ofNat 64 (k + 1)
  let nv : BitVec 64 := BitVec.ofNat 64 K.n
  have hincpos : (incv.signExtend 64).toNat = k + 1 := by
    show ((BitVec.ofNat 64 (k + 1)).signExtend 64).toNat = k + 1
    rw [stage2NoEventSignExtend_self, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hpos216 : (incv.signExtend 64).toNat < 2 ^ 63 := by
    rw [hincpos]
    have h1 := hinv.nepLe
    have h2 := hinv.maxDoc
    simp only [stage2MaxDocument] at h2
    omega
  have hread216 : readBytes s.mem (K.ep + (incv.signExtend 64).toNat * 4) 4 =
      some bs4 := by
    simpa only [hincpos, Nat.mul_comm] using hread4
  have hlanelt : bytesToNat bs4 < 2 ^ 32 := by rw [hbs4next]; exact hnext32
  have hk219216 : lookupName s.env "%k219" = some (.ptr (K.c + 32)) :=
    hbase "%k219" (.ptr (K.c + 32)) (by
      simp [stage2NoEventWalkBaseValues, stage2NoEventWalkBaseCellValues, entryCells4])
  have hn216 : lookupName s.env "%n" =
      some (.int 64 (BitVec.ofNat 64 K.n)) :=
    hbase "%n" (.int 64 (BitVec.ofNat 64 K.n)) (by
      simp [stage2NoEventWalkBaseValues, stage2NoEventWalkParamEntries])
  have hy216 : evalICmp .ugt nv (BitVec.ofNat 64 (bytesToNat bs4)) = 1 := by
    rw [hbs4next]
    exact stage2NoEventWalkStringRowUgt_one hinv.nLt (by omega) hnextN
  have hw219 : ∀ j, j < (natToBytes (kv + BitVec.ofNat 64 2).toNat 8).length →
      inRegions (stage2NoEventRunRegions K.scratch K.scratchcap K.stk K.e K.c K.d ++
        [(K.next0, K.nextEnd - K.next0)]) (K.c + 32 + j) := by
    intro j hj
    rw [natToBytes_length] at hj
    refine ⟨(K.c, stage2NoEventCursorExtent), ?_, ?_, ?_⟩
    · simp [stage2NoEventRunRegions, stage2NoEventStagedRegions]
    · simp only [stage2NoEventCursorExtent]; omega
    · simp only [stage2NoEventCursorExtent]; omega
  have L216 := link_ifEnd216_true (calls := stage2NoEventCalls gap) (K := K) (mem := mem)
    (s := s) (k := kv) (ep := K.ep) (inc := incv) (a := K.c + 32) (bs4 := bs4)
    (n := nv) hinv hpc hk216 (by
      rw [show lookupName s.env "%ep" = some (.ptr K.ep) from
        hbase "%ep" (.ptr K.ep) (by
          simp [stage2NoEventWalkBaseValues, stage2NoEventWalkParamEntries])]) hinc216
    hpos216 hread216 hlanelt hk219216 hn216 hw219 hy216
  let s217 : State := stage2NoEventWalkStored
    (ifEnd216Cells s.env kv K.ep incv bs4 nv) s
    (writeBytes s.mem (K.c + 32) (natToBytes (kv + BitVec.ofNat 64 2).toNat 8))
    "if.end230"
  have hstep217 : step (stage2NoEventCalls gap) stage2NoEventBody s = .jump s217 := by
    simpa only [s217] using L216.step
  have hpc217 : s217.pc = "if.end230" := by
    simp only [s217, stage2NoEventWalkStored]
  -- the `if.end230` instance
  have hidx217 : lookupName s217.env "%idxprom.lcssa1109" =
      some (.int 64 (BitVec.ofNat 64 lane)) := by
    simp only [s217, stage2NoEventWalkStored, ifEnd216Cells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact hidx216
  have hv217 : lookupName s217.env "%conv220" = some (.int 64 (BitVec.ofNat 64 next)) := by
    simp only [s217, stage2NoEventWalkStored, ifEnd216Cells]
    rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_self]
    rw [hbs4next]
  have hcap217 : lookupName s217.env "%scratchcap" =
      some (.int 64 (BitVec.ofNat 64 K.scratchcap)) := by
    simp only [s217, stage2NoEventWalkStored, ifEnd216Cells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact hbase "%scratchcap" (.int 64 (BitVec.ofNat 64 K.scratchcap)) (by
      simp [stage2NoEventWalkBaseValues, stage2NoEventWalkParamEntries])
  have hcapLt : K.scratchcap < 2 ^ 64 := hinv.scratchcapLt
  have hy230 : evalICmp .ugt
      ((BitVec.ofNat 64 next +
        (BitVec.ofNat 64 lane ^^^ BitVec.ofNat 64 18446744073709551615)) +
        BitVec.ofNat 64 64) (BitVec.ofNat 64 K.scratchcap) = 0 :=
    stage2NoEventWalkStringRowGuard230 hlaneNext (by omega) hscratch hcapLt
  have L230 := link_ifEnd230_false (calls := stage2NoEventCalls gap) (K := K) (mem := mem)
    (s := s217) (idx := BitVec.ofNat 64 lane) (v := BitVec.ofNat 64 next)
    (cap := BitVec.ofNat 64 K.scratchcap) L216.inv' hpc217 hidx217 hv217 hcap217 hy230
  let s218 : State := stage2NoEventWalkNext
    (ifEnd230Cells s217.env (BitVec.ofNat 64 lane) (BitVec.ofNat 64 next)
      (BitVec.ofNat 64 K.scratchcap)) s217 "if.end239"
  have hstep218 : step (stage2NoEventCalls gap) stage2NoEventBody s217 = .jump s218 := by
    simpa only [s218] using L230.step
  have hpc218 : s218.pc = "if.end239" := by
    simp only [s218, stage2NoEventWalkNext]
  have hs218env : s218.env = cells
      [("%cmp236", .int 1 (evalICmp .ugt
          ((BitVec.ofNat 64 next + (BitVec.ofNat 64 lane ^^^
            BitVec.ofNat 64 18446744073709551615)) + BitVec.ofNat 64 64)
          (BitVec.ofNat 64 K.scratchcap))),
        ("%add235", .int 64 ((BitVec.ofNat 64 next + (BitVec.ofNat 64 lane ^^^
            BitVec.ofNat 64 18446744073709551615)) + BitVec.ofNat 64 64)),
        ("%sub234", .int 64 (BitVec.ofNat 64 next + (BitVec.ofNat 64 lane ^^^
          BitVec.ofNat 64 18446744073709551615))),
        ("%30", .int 64 (BitVec.ofNat 64 lane ^^^
          BitVec.ofNat 64 18446744073709551615)),
        ("%cmp221.not", .int 1 (evalICmp .ugt nv (BitVec.ofNat 64 (bytesToNat bs4)))),
        ("%conv220", .int 64 (BitVec.ofNat 64 (bytesToNat bs4))),
        ("%29", .int 32 (BitVec.ofNat 32 (bytesToNat bs4))),
        ("%arrayidx218", .ptr (K.ep + (incv.signExtend 64).toNat * 4)),
        ("%inc217", .int 64 (kv + BitVec.ofNat 64 2))] s.env := by
    simp only [s218, s217, stage2NoEventWalkNext, stage2NoEventWalkStored,
      ifEnd230Cells, ifEnd216Cells, cells]
  -- the base table at the two links' targets
  have hb218 : Stage2NoEventWalkBaseLookups K s218 := by
    have hh := stage2NoEventCycleBase (K := K) (env := s.env) hbase
      (cs := [("%cmp236", .int 1 (evalICmp .ugt
          ((BitVec.ofNat 64 next + (BitVec.ofNat 64 lane ^^^
            BitVec.ofNat 64 18446744073709551615)) + BitVec.ofNat 64 64)
          (BitVec.ofNat 64 K.scratchcap))),
        ("%add235", .int 64 ((BitVec.ofNat 64 next + (BitVec.ofNat 64 lane ^^^
            BitVec.ofNat 64 18446744073709551615)) + BitVec.ofNat 64 64)),
        ("%sub234", .int 64 (BitVec.ofNat 64 next + (BitVec.ofNat 64 lane ^^^
          BitVec.ofNat 64 18446744073709551615))),
        ("%30", .int 64 (BitVec.ofNat 64 lane ^^^
          BitVec.ofNat 64 18446744073709551615)),
        ("%cmp221.not", .int 1 (evalICmp .ugt nv (BitVec.ofNat 64 (bytesToNat bs4)))),
        ("%conv220", .int 64 (BitVec.ofNat 64 (bytesToNat bs4))),
        ("%29", .int 32 (BitVec.ofNat 32 (bytesToNat bs4))),
        ("%arrayidx218", .ptr (K.ep + (incv.signExtend 64).toNat * 4)),
        ("%inc217", .int 64 (kv + BitVec.ofNat 64 2))])
      (names := ["%cmp236", "%add235", "%sub234", "%30", "%cmp221.not", "%conv220",
        "%29", "%arrayidx218", "%inc217"]) rfl (by decide)
    intro n v hv
    have h2 := hh n v hv
    rw [hs218env]
    exact h2
  -- the call
  have hmem218 : s218.mem =
      writeBytes s.mem (K.c + 32) (natToBytes (k + 2) 8) := by
    have hkv : (kv + BitVec.ofNat 64 2).toNat = k + 2 := by
      show ((BitVec.ofNat 64 k) + BitVec.ofNat 64 2).toNat = k + 2
      rw [stage2NoEventWalkOfNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    simp only [s218, s217, stage2NoEventWalkNext, stage2NoEventWalkStored, hkv]
  have hidx218 : lookupName s218.env "%idxprom.lcssa1109" =
      some (.int 64 (BitVec.ofNat 64 lane)) := by
    simp only [s218, stage2NoEventWalkNext, ifEnd230Cells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact hidx217
  have hnext218 : s218.next = s.next := by
    simp only [s218, s217, stage2NoEventWalkNext, stage2NoEventWalkStored]
  have hsub218 : lookupName s218.env "%sub234" =
      some (.int 64 (BitVec.ofNat 64 (next - lane - 1))) := by
    simp only [s218, stage2NoEventWalkNext, ifEnd230Cells]
    rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
      lookupName_cons_self]
    rw [show (BitVec.ofNat 64 next +
        (BitVec.ofNat 64 lane ^^^ BitVec.ofNat 64 18446744073709551615)) =
        BitVec.ofNat 64 (next - lane - 1) from by
      rw [stage2NoEventWalkStringRowXor lane (by omega), stage2NoEventWalkOfNat_add]
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat,
        show next + (2 ^ 64 - 1 - lane) = 2 ^ 64 + (next - lane - 1) from by omega,
        Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]]
  have hcall' : stage2NoEventCalls gap "s2_string_body"
      (stage2NoEventWalkStringArgs K lane (BitVec.ofNat 64 (next - lane - 1)))
      (writeBytes s218.mem (K.next0 + 16) (natToBytes 0 8)) s218.next = some r := by
    rw [hmem218, hnext218]
    exact hcall
  have hpos239 : ((BitVec.ofNat 64 lane).signExtend 64).toNat < 2 ^ 63 :=
    stage2NoEventLane_signExtend_lt hlane32
  have hstepCall : step (stage2NoEventCalls gap) stage2NoEventBody s218 = .jump
      { env := ifEnd239Cells s218.env (K.b + 1) (BitVec.ofNat 64 lane) r,
        mem := r.mem, next := r.next, pc := "NodeBlock29", pre := some s218.pc } :=
    ifEnd239_step (calls := stage2NoEventCalls gap) (s := s218) hpc218
      (hb218 "%outn205" (.ptr (K.next0 + 16)) (by
        simp [stage2NoEventWalkBaseValues, stage2NoEventWalkBaseCellValues, entryCells1,
          entryCells2, entryCells3, entryCells4, preHeaderCells]))
      (hb218 "%invariant.gep" (.ptr (K.b + 1)) (by
        simp [stage2NoEventWalkBaseValues, stage2NoEventWalkBaseCellValues, entryCells4]))
      hidx218 hpos239
      (hb218 "%c" (.ptr K.c) (by
        simp [stage2NoEventWalkBaseValues, stage2NoEventWalkParamEntries]))
      hsub218
      (hb218 "%scratch" (.ptr K.scratch) (by
        simp [stage2NoEventWalkBaseValues, stage2NoEventWalkParamEntries]))
      (hb218 "%xp" (.ptr K.xp) (by
        simp [stage2NoEventWalkBaseValues, stage2NoEventWalkParamEntries]))
      (hb218 "%xj" (.ptr K.next0) (by
        simp [stage2NoEventWalkBaseValues, stage2NoEventWalkBaseCellValues, entryCells1,
          entryCells2, entryCells3, entryCells4, preHeaderCells]))
      (hb218 "%nxp" (.int 64 (BitVec.ofNat 64 K.nxp)) (by
        simp [stage2NoEventWalkBaseValues, stage2NoEventWalkParamEntries]))
      hcall'
  let sCall : State :=
    { env := ifEnd239Cells s218.env (K.b + 1) (BitVec.ofNat 64 lane) r,
      mem := r.mem, next := r.next, pc := "NodeBlock29", pre := some s218.pc }
  -- the invariant across the two stores and the call
  let R : List (Nat × Nat) :=
    stage2NoEventRunRegions K.scratch K.scratchcap K.stk K.e K.c K.d ++
      [(K.next0, K.nextEnd - K.next0)]
  have hkvN : (kv + BitVec.ofNat 64 2).toNat = k + 2 := by
    show ((BitVec.ofNat 64 k) + BitVec.ofNat 64 2).toNat = k + 2
    rw [stage2NoEventWalkOfNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hf0 : UnchangedOutside s.mem s.mem R := fun a _ => rfl
  have hf1 : UnchangedOutside s.mem
      (writeBytes s.mem (K.c + 32) (natToBytes (k + 2) 8)) R := by
    have hh := UnchangedOutside.write_inside (m := s.mem) hf0
      (a := K.c + 32) (bs := natToBytes (kv + BitVec.ofNat 64 2).toNat 8) hw219
    simpa only [hkvN] using hh
  have hwOut : ∀ j, j < (natToBytes 0 8).length →
      inRegions R (K.next0 + 16 + j) := by
    intro j hj
    rw [natToBytes_length] at hj
    refine ⟨(K.next0, K.nextEnd - K.next0), ?_, ?_, ?_⟩
    · exact List.mem_append_right _ (by simp)
    · omega
    · have h1 := hinv.nextEnd_static
      simp only [stage2BootstrapExtent] at h1
      omega
  have hf2 : UnchangedOutside
      (writeBytes s.mem (K.c + 32) (natToBytes (k + 2) 8))
      (writeBytes (writeBytes s.mem (K.c + 32) (natToBytes (k + 2) 8))
        (K.next0 + 16) (natToBytes 0 8)) R :=
    UnchangedOutside.write_inside (m := writeBytes s.mem (K.c + 32) (natToBytes (k + 2) 8))
      (fun a _ => rfl) (a := K.next0 + 16) (bs := natToBytes 0 8) hwOut
  have hfCall : UnchangedOutside
      (writeBytes (writeBytes s.mem (K.c + 32) (natToBytes (k + 2) 8))
        (K.next0 + 16) (natToBytes 0 8)) r.mem R :=
    UnchangedOutside.of_covered hframe hfoot
  have hf012 : UnchangedOutside s.mem
      (writeBytes (writeBytes s.mem (K.c + 32) (natToBytes (k + 2) 8))
        (K.next0 + 16) (natToBytes 0 8)) R :=
    stage2NoEventWalkStringRowFrameTrans hf1 hf2
  have hf : UnchangedOutside s.mem r.mem R :=
    stage2NoEventWalkStringRowFrameTrans hf012 hfCall
  have hfm : UnchangedOutside mem r.mem R :=
    stage2NoEventWalkStringRowFrameTrans hinv.walkFrame hf
  have hinvCall : Stage2NoEventWalkInv K mem sCall :=
    Stage2NoEventWalkInv.of_frame (K := K) (mem := mem) (s := s) (s' := sCall)
      hinv hpresent hfm
  -- the result's dispatch
  have hcall243 : lookupName sCall.env "%call243" =
      some (.int 32 (BitVec.ofNat 32 form)) := by
    simp only [sCall, ifEnd239Cells]
    rw [lookupName_cons_self, hret]
  have hpcCall : sCall.pc = "NodeBlock29" := rfl
  have hy29 : evalICmp .slt (BitVec.ofNat 32 form) (BitVec.ofNat 32 1) = 0 :=
    stage2NoEventWalkStringRowSlt_one_zero hforms
  have L29 := link_nodeBlock29_false (calls := stage2NoEventCalls gap) (K := K) (mem := mem)
    (s := sCall) (v := BitVec.ofNat 32 form) hinvCall hpcCall hcall243 hy29
  let s29 : State := stage2NoEventWalkNext
    (("%Pivot30", .int 1 0) :: sCall.env) sCall "LeafBlock27"
  have hstep29 : step (stage2NoEventCalls gap) stage2NoEventBody sCall = .jump s29 := by
    simpa only [s29] using L29.step
  have hseg29 := stage2NoEventWalkStringRowLinkSegment L29
  have hsegCall := stage2NoEventWalkStringRowStepSegment
    (K := K) (mem := mem) (s := s218) (s' := sCall) hstepCall hinvCall
  have hseg217 := stage2NoEventWalkStringRowLinkSegment L216
  have hseg218 := stage2NoEventWalkStringRowLinkSegment L230
  have hseg2 : Stage2NoEventWalkSegment (stage2NoEventCalls gap) mem K s K s218 2 :=
    hseg217.trans hseg218
  have hseg3 : Stage2NoEventWalkSegment (stage2NoEventCalls gap) mem K s K sCall 3 :=
    hseg2.trans hsegCall
  have hseg4 : Stage2NoEventWalkSegment (stage2NoEventCalls gap) mem K s K s29 4 :=
    hseg3.trans hseg29
  have hb29 : Stage2NoEventWalkBaseLookups K s29 := by
    have hbCall : Stage2NoEventWalkBaseLookups K sCall := by
      have h1 : Stage2NoEventWalkBaseLookups K
          { s218 with env := ("%gep", .ptr ((K.b + 1) +
            ((BitVec.ofNat 64 lane).signExtend 64).toNat)) :: s218.env } :=
        hb218.consOne (n := "%gep")
          (v := .ptr ((K.b + 1) + ((BitVec.ofNat 64 lane).signExtend 64).toNat)) (by decide)
      have h2 : Stage2NoEventWalkBaseLookups K
          { { s218 with env := ("%gep", .ptr ((K.b + 1) +
              ((BitVec.ofNat 64 lane).signExtend 64).toNat)) :: s218.env } with
            env := ("%call243", r.ret)
              :: ("%gep", .ptr ((K.b + 1) + ((BitVec.ofNat 64 lane).signExtend 64).toNat))
              :: s218.env } :=
        h1.consOne (n := "%call243") (v := r.ret) (by decide)
      exact h2.congr_env (by simp only [sCall, ifEnd239Cells, cells])
    have hh : Stage2NoEventWalkBaseLookups K
        { sCall with env := ("%Pivot30", .int 1 0) :: sCall.env } :=
      hbCall.consOne (n := "%Pivot30") (v := .int 1 0) (by decide)
    exact hh.congr_env (by simp only [s29, stage2NoEventWalkNext, cells])
  -- the surviving readings
  have hs29env : s29.env = ("%Pivot30", .int 1 0) :: ("%call243", r.ret) ::
      ("%gep", .ptr ((K.b + 1) + ((BitVec.ofNat 64 lane).signExtend 64).toNat)) ::
      cells
        [("%cmp236", .int 1 (evalICmp .ugt
            ((BitVec.ofNat 64 next + (BitVec.ofNat 64 lane ^^^
              BitVec.ofNat 64 18446744073709551615)) + BitVec.ofNat 64 64)
            (BitVec.ofNat 64 K.scratchcap))),
          ("%add235", .int 64 ((BitVec.ofNat 64 next + (BitVec.ofNat 64 lane ^^^
              BitVec.ofNat 64 18446744073709551615)) + BitVec.ofNat 64 64)),
          ("%sub234", .int 64 (BitVec.ofNat 64 next + (BitVec.ofNat 64 lane ^^^
            BitVec.ofNat 64 18446744073709551615))),
          ("%30", .int 64 (BitVec.ofNat 64 lane ^^^
            BitVec.ofNat 64 18446744073709551615)),
          ("%cmp221.not", .int 1 (evalICmp .ugt nv (BitVec.ofNat 64 (bytesToNat bs4)))),
          ("%conv220", .int 64 (BitVec.ofNat 64 (bytesToNat bs4))),
          ("%29", .int 32 (BitVec.ofNat 32 (bytesToNat bs4))),
          ("%arrayidx218", .ptr (K.ep + (incv.signExtend 64).toNat * 4)),
          ("%inc217", .int 64 (kv + BitVec.ofNat 64 2))] s.env := by
    simp only [s29, sCall, stage2NoEventWalkNext, ifEnd239Cells, hs218env]
  have hsurv (n : String) (hn1 : n ∉ ["%Pivot30", "%call243", "%gep"])
      (hn2 : n ∉ ["%cmp236", "%add235", "%sub234", "%30", "%cmp221.not", "%conv220",
        "%29", "%arrayidx218", "%inc217"]) (v : Value)
      (hv : lookupName s.env n = some v) :
      lookupName s29.env n = some v := by
    rw [hs29env]
    rw [lookupName_cons_ne _ _ (fun e => hn1 (by simp [e])),
        lookupName_cons_ne _ _ (fun e => hn1 (by simp [e])),
        lookupName_cons_ne _ _ (fun e => hn1 (by simp [e]))]
    rw [stage2NoEventWalkStringRowCellsNotin
      (cs := [("%cmp236", .int 1 (evalICmp .ugt
            ((BitVec.ofNat 64 next + (BitVec.ofNat 64 lane ^^^
              BitVec.ofNat 64 18446744073709551615)) + BitVec.ofNat 64 64)
            (BitVec.ofNat 64 K.scratchcap))),
          ("%add235", .int 64 ((BitVec.ofNat 64 next + (BitVec.ofNat 64 lane ^^^
              BitVec.ofNat 64 18446744073709551615)) + BitVec.ofNat 64 64)),
          ("%sub234", .int 64 (BitVec.ofNat 64 next + (BitVec.ofNat 64 lane ^^^
            BitVec.ofNat 64 18446744073709551615))),
          ("%30", .int 64 (BitVec.ofNat 64 lane ^^^
            BitVec.ofNat 64 18446744073709551615)),
          ("%cmp221.not", .int 1 (evalICmp .ugt nv (BitVec.ofNat 64 (bytesToNat bs4)))),
          ("%conv220", .int 64 (BitVec.ofNat 64 (bytesToNat bs4))),
          ("%29", .int 32 (BitVec.ofNat 32 (bytesToNat bs4))),
          ("%arrayidx218", .ptr (K.ep + (incv.signExtend 64).toNat * 4)),
          ("%inc217", .int 64 (kv + BitVec.ofNat 64 2))]) (n := n) (fun hc => hn2 (by
      simpa using hc))]
    exact hv
  have hcall29 : lookupName s29.env "%call243" =
      some (.int 32 (BitVec.ofNat 32 form)) := by
    simp only [s29, sCall, stage2NoEventWalkNext, ifEnd239Cells]
    rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_self, hret]
  have hpc29 : s29.pc = "LeafBlock27" := by simp only [s29, stage2NoEventWalkNext]
  have hmem29 : s29.mem = r.mem := by
    simp only [s29, sCall, stage2NoEventWalkNext]
  have hinc29 : lookupName s29.env "%inc217" =
      some (.int 64 (BitVec.ofNat 64 (k + 2))) := by
    simp only [s29, sCall, s218, s217, stage2NoEventWalkNext, stage2NoEventWalkStored,
      ifEnd239Cells, ifEnd230Cells, ifEnd216Cells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    rw [lookupName_cons_self]
    rw [show (kv + BitVec.ofNat 64 2) = BitVec.ofNat 64 (k + 2) from by
      show ((BitVec.ofNat 64 k) + BitVec.ofNat 64 2) = BitVec.ofNat 64 (k + 2)
      exact stage2NoEventWalkOfNat_add 64 k 2]
  have hsub29 : lookupName s29.env "%sub234" =
      some (.int 64 (BitVec.ofNat 64 (next - lane - 1))) := by
    simp only [s29, sCall, s218, s217, stage2NoEventWalkNext, stage2NoEventWalkStored,
      ifEnd239Cells, ifEnd230Cells, ifEnd216Cells]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    rw [lookupName_cons_self]
    rw [show (BitVec.ofNat 64 next +
        (BitVec.ofNat 64 lane ^^^ BitVec.ofNat 64 18446744073709551615)) =
        BitVec.ofNat 64 (next - lane - 1) from by
      rw [stage2NoEventWalkStringRowXor lane (by omega), stage2NoEventWalkOfNat_add]
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat,
        show next + (2 ^ 64 - 1 - lane) = 2 ^ 64 + (next - lane - 1) from by omega,
        Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]]
  exact ⟨s29, hseg4, hseg29.inv', hb29, hpc29, hmem29, hcall29,
    hsurv _ (by decide) (by decide) _ halen216, hsurv _ (by decide) (by decide) _ harena216,
    hsurv _ (by decide) (by decide) _ htok216, hsurv _ (by decide) (by decide) _ hterms216,
    hinc29, hsurv _ (by decide) (by decide) _ hfr216, hsurv _ (by decide) (by decide) _ hsp216,
    hsub29, hsurv _ (by decide) (by decide) _ hlc216⟩

/-! ### `LeafBlock27`'s step

The block compares the callee's form word with one and takes the empty string's
edge at one, the arena's otherwise.  The step is head-free: the invariant, the
block's `pc` and the form word are the whole premise. -/

/-- **`LeafBlock27` at a form of two**: one block to `for.cond266.preheader`,
with the base table carried across the `%SwitchLeaf28` cell. -/
theorem stage2NoEventWalkStringLeaf27StepArena {gap : Calls}
    {K : Stage2NoEventWalkCarry} {mem : Mem} {s : State}
    (hinv : Stage2NoEventWalkInv K mem s) (hpc : s.pc = "LeafBlock27")
    (hbase : Stage2NoEventWalkBaseLookups K s)
    (hcall243 : lookupName s.env "%call243" = some (.int 32 (BitVec.ofNat 32 2))) :
    ∃ sMid, Stage2NoEventWalkSegment (stage2NoEventCalls gap) mem K s K sMid 1 ∧
      sMid.pc = "for.cond266.preheader" ∧ sMid.mem = s.mem ∧
      Stage2NoEventWalkBaseLookups K sMid ∧
      (∀ (n : String) (v : Value), "%SwitchLeaf28" ≠ n →
        lookupName s.env n = some v → lookupName sMid.env n = some v) := by
  have hy27 : evalICmp .eq (BitVec.ofNat 32 2) (BitVec.ofNat 32 1) = 0 := by decide
  have L27 := link_leafBlock27_false (calls := stage2NoEventCalls gap) (K := K) (mem := mem)
    (s := s) (v := BitVec.ofNat 32 2) hinv hpc hcall243 hy27
  let sMid : State := stage2NoEventWalkNext
    (("%SwitchLeaf28", .int 1 0) :: s.env) s "for.cond266.preheader"
  have hstep : step (stage2NoEventCalls gap) stage2NoEventBody s = .jump sMid := by
    simpa only [sMid] using L27.step
  have hbaseMid : Stage2NoEventWalkBaseLookups K sMid := by
    have hh : Stage2NoEventWalkBaseLookups K
        { s with env := ("%SwitchLeaf28", .int 1 0) :: s.env } :=
      hbase.consOne (n := "%SwitchLeaf28") (v := .int 1 0) (by decide)
    exact hh.congr_env (by simp only [sMid, stage2NoEventWalkNext])
  refine ⟨sMid, stage2NoEventWalkStringRowStepSegment hstep L27.inv', ?_, ?_,
    hbaseMid, ?_⟩
  · simp only [sMid, stage2NoEventWalkNext]
  · simp only [sMid, stage2NoEventWalkNext]
  · intro n v hne hv
    simp only [sMid, stage2NoEventWalkNext]
    rw [lookupName_cons_ne _ _ hne]
    exact hv

/-- **`LeafBlock27` at a form of one**: one block to `do.body254` (the empty
string's `strPlain` step). -/
theorem stage2NoEventWalkStringLeaf27StepPlain {gap : Calls}
    {K : Stage2NoEventWalkCarry} {mem : Mem} {s : State}
    (hinv : Stage2NoEventWalkInv K mem s) (hpc : s.pc = "LeafBlock27")
    (hbase : Stage2NoEventWalkBaseLookups K s)
    (hcall243 : lookupName s.env "%call243" = some (.int 32 (BitVec.ofNat 32 1))) :
    ∃ sMid, Stage2NoEventWalkSegment (stage2NoEventCalls gap) mem K s K sMid 1 ∧
      sMid.pc = "do.body254" ∧ sMid.mem = s.mem ∧
      Stage2NoEventWalkBaseLookups K sMid ∧
      (∀ (n : String) (v : Value), "%SwitchLeaf28" ≠ n →
        lookupName s.env n = some v → lookupName sMid.env n = some v) := by
  have hy27 : evalICmp .eq (BitVec.ofNat 32 1) (BitVec.ofNat 32 1) = 1 :=
    stage2NoEventWalkStringRowEq_one rfl
  have L27 := link_leafBlock27_true (calls := stage2NoEventCalls gap) (K := K) (mem := mem)
    (s := s) (v := BitVec.ofNat 32 1) hinv hpc hcall243 hy27
  let sMid : State := stage2NoEventWalkNext
    (("%SwitchLeaf28", .int 1 1) :: s.env) s "do.body254"
  have hstep : step (stage2NoEventCalls gap) stage2NoEventBody s = .jump sMid := by
    simpa only [sMid] using L27.step
  have hbaseMid : Stage2NoEventWalkBaseLookups K sMid := by
    have hh : Stage2NoEventWalkBaseLookups K
        { s with env := ("%SwitchLeaf28", .int 1 1) :: s.env } :=
      hbase.consOne (n := "%SwitchLeaf28") (v := .int 1 1) (by decide)
    exact hh.congr_env (by simp only [sMid, stage2NoEventWalkNext])
  refine ⟨sMid, stage2NoEventWalkStringRowStepSegment hstep L27.inv', ?_, ?_,
    hbaseMid, ?_⟩
  · simp only [sMid, stage2NoEventWalkNext]
  · simp only [sMid, stage2NoEventWalkNext]
  · intro n v hne hv
    simp only [sMid, stage2NoEventWalkNext]
    rw [lookupName_cons_ne _ _ hne]
    exact hv

/-! ### The row at the entry, end to end

The entry head (two blocks), the leg (four), `LeafBlock27`'s step (one) compose
to a seven-block `segHead` at the class's own index.  The arm's slice is the
committed head-free producer.  The row is the head-free
`stage2NoEventWalkStringRow_cont_of_route_count` at the consumed-count supply.

The `fr` the entry head fixes is `1` (`stringValueCells` writes it), and the
depth is the entry's `%indvars.iv` word; `sp ≠ 0` is the class's nestedness and
stays the caller's. -/

/-- **The string class's continuing row at `string_value.loopexit`, arena arm**:
the entry head, the four-block call leg, `LeafBlock27`'s step, the arena slice at
either length case, and the shared cycle. -/
noncomputable def stage2NoEventWalkStringRow_of_entry_arena {gap : Calls} {F : Nat}
    {K : Stage2NoEventWalkCarry} {mem : Mem} {k : Nat} {s0 : State}
    (hinv0 : Stage2NoEventWalkInv K mem s0)
    (hpc0 : s0.pc = "string_value.loopexit")
    (hbase0 : Stage2NoEventWalkBaseLookups K s0)
    {iv : BitVec 64} {lane : Nat}
    (h8 : lookupName s0.env "%8" = some (.int 32 (BitVec.ofNat 32 lane)))
    (hiv : lookupName s0.env "%indvars.iv" = some (.int 64 iv))
    (hinc0 : lookupName s0.env "%inc" = some (.int 64 (BitVec.ofNat 64 (k + 1))))
    (hk0 : lookupName s0.env "%k.0" = some (.int 64 (BitVec.ofNat 64 k)))
    (htr0 : lookupName s0.env "%terms.0" = some (.int 64 (BitVec.ofNat 64 K.terms)))
    (htok0 : lookupName s0.env "%tokens.0" = some (.int 64 (BitVec.ofNat 64 K.tok)))
    {o : Nat} (houtn0 : lookupName s0.env "%outn205" = some (.ptr o))
    {nepv : BitVec 64}
    (hnep0 : lookupName s0.env "%nep" = some (.int 64 nepv))
    {r0 : CallOutcome}
    (hlife : stage2NoEventCalls gap "llvm.lifetime.start.p0"
      [.int 64 (BitVec.ofNat 64 8), .ptr o] s0.mem s0.next = some r0)
    (hmemLife : r0.mem = s0.mem) (hnextLife : r0.next = s0.next)
    (hguard0 : evalICmp .ult (BitVec.ofNat 64 (k + 1)) nepv = 1)
    (halen0 : lookupName s0.env "%alen.0.ph1405" =
      some (.int 64 (BitVec.ofNat 64 K.arena.length)))
    (harena0 : lookupName s0.env "%arena.0.ph1406" =
      some (.int 64 (BitVec.ofNat 64 K.arenaWord)))
    {next comma : Nat} {byte : UInt8}
    (hk : K.ent[k]? = some lane) (hbs : K.bs[lane]? = some byte) (hb : byte.toNat = 34)
    (hk1 : K.ent[k + 1]? = some next)
    (hcommaEnt : K.ent[k + 2]? = some comma)
    (hcomma : ∀ q, K.ent[k + 2]? = some q → K.bs.getD q 0 = 44)
    (hklt : k + 3 < K.nep)
    (hspNe : iv.toNat % 2 ^ 32 ≠ 0)
    {len : Nat} {body : List UInt8} {cs : List Nat}
    {r : CallOutcome}
    (hret : r.ret = .int 32 (BitVec.ofNat 32 2))
    (hscratch : next - lane - 1 + 64 ≤ K.scratchcap)
    {foot : List (Nat × Nat)}
    (hcall : stage2NoEventCalls gap "s2_string_body"
      (stage2NoEventWalkStringArgs K lane (BitVec.ofNat 64 (next - lane - 1)))
      (writeBytes (writeBytes s0.mem (K.c + 32) (natToBytes (k + 2) 8))
        (K.next0 + 16) (natToBytes 0 8)) s0.next = some r)
    (hframe : UnchangedOutside
      (writeBytes (writeBytes s0.mem (K.c + 32) (natToBytes (k + 2) 8))
        (K.next0 + 16) (natToBytes 0 8)) r.mem foot)
    (hfoot : ∀ q ∈ foot,
      ∃ r' ∈ stage2NoEventRunRegions K.scratch K.scratchcap K.stk K.e K.c K.d ++
        [(K.next0, K.nextEnd - K.next0)], r'.1 ≤ q.1 ∧ q.1 + q.2 ≤ r'.1 + r'.2)
    (hpresent : ∀ a, inRegions
      (stage2NoEventRunRegions K.scratch K.scratchcap K.stk K.e K.c K.d) a →
        present r.mem a)
    (hcode : bodyCodePoints K.bs ⟨lane, next + 1⟩ = some cs)
    (hdecode : escapeCodePoints (((K.arena ++ body).drop K.arena.length).take len) =
      some cs)
    (hbodyLen : body.length = len)
    (hreadOutn : readBytes r.mem (K.next0 + 16) 8 = some (natToBytes len 8))
    (hbodyRead : readBytes r.mem K.scratch len = some body)
    (hlen0 : len ≠ 0) (hlenSpan : len + 1 ≤ next - lane)
    (hbelow : K.arena.length < 2 ^ 63)
    (hbPos : 1 ≤ K.b)
    (htrace : Stage2NoEventWalkTrace K)
    (count : Stage2NoEventWalkCount K k) :
    Stage2NoEventWalkRow (stage2NoEventCalls gap) mem F K k s0 := by
  classical
  refine Classical.choice (show Nonempty
    (Stage2NoEventWalkRow (stage2NoEventCalls gap) mem F K k s0) from ?_)
  -- the entry head
  have hwLt : lane < 2 ^ 32 := by
    have h0 := hinv0.inside lane (List.mem_of_getElem? hk)
    have h1 := hinv0.maxDoc
    simp only [stage2MaxDocument] at h1
    omega
  obtain ⟨sE, hsegE, hpcE, hmemE, hnextE, hincE, hlcE, hidxE, hfrE, hspE, hkE,
    htrE, htokE, halenE, harenaE, hbaseE⟩ :=
    stage2NoEventWalkStringEntryBase (calls := stage2NoEventCalls gap)
      (K := K) (mem := mem) (s := s0) hinv0 hpc0 (w := BitVec.ofNat 32 lane) h8 hiv
      (inc := BitVec.ofNat 64 (k + 1)) (k := BitVec.ofNat 64 k)
      (terms := BitVec.ofNat 64 K.terms) (tok := BitVec.ofNat 64 K.tok) hinc0 hk0 htr0 htok0
      houtn0 hnep0 hlife hmemLife hnextLife hguard0
      (alen := K.arena.length) (arenaWord := K.arenaWord) halen0 harena0 hbase0
  have hidxE' : lookupName sE.env "%idxprom.lcssa1109" =
      some (.int 64 (BitVec.ofNat 64 lane)) := by
    simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hwLt] using hidxE
  -- the leg
  have hcallE : stage2NoEventCalls gap "s2_string_body"
      (stage2NoEventWalkStringArgs K lane (BitVec.ofNat 64 (next - lane - 1)))
      (writeBytes (writeBytes sE.mem (K.c + 32) (natToBytes (k + 2) 8))
        (K.next0 + 16) (natToBytes 0 8)) sE.next = some r := by
    rw [hmemE, hmemLife, hnextE]
    exact hcall
  have hframeE : UnchangedOutside
      (writeBytes (writeBytes sE.mem (K.c + 32) (natToBytes (k + 2) 8))
        (K.next0 + 16) (natToBytes 0 8)) r.mem foot := by
    rw [hmemE, hmemLife]
    exact hframe
  obtain ⟨s27, hseg4, hinv27, hbase27, hpc27, hmem27, hcall243, halen27, harena27, htok27,
    hterms27, hinc27, hfr27, hsp27, hsub27, hlc27⟩ :=
    stage2NoEventWalkStringCallLeg (gap := gap) (K := K) (mem := mem) (k := k) (s := sE)
      (fr := 1) (sp := iv.toNat % 2 ^ 32) (lane := lane) (next := next)
      hsegE.inv' hpcE hbaseE hk hkE hincE hlcE hidxE' hfrE hspE htokE htrE
      halenE harenaE
      hk1 hklt (form := 2) hret (Or.inr rfl) hscratch hcallE hframeE hfoot hpresent
  -- `LeafBlock27`'s step
  obtain ⟨sMid, hseg1, hpcMid, hmemMid27, hbaseMid, hlift⟩ :=
    stage2NoEventWalkStringLeaf27StepArena (gap := gap) (K := K) (mem := mem) (s := s27)
      hinv27 hpc27 hbase27 hcall243
  have hmemMid : sMid.mem = r.mem := by rw [hmemMid27, hmem27]
  have hseg7 : Stage2NoEventWalkSegment (stage2NoEventCalls gap) mem K s0 K sMid 7 :=
    hsegE.trans ((hseg4.trans hseg1))
  -- the class's order and span facts
  have hlaneNext : lane < next := by
    obtain ⟨hkltL, hkval⟩ := List.getElem?_eq_some_iff.mp hk
    obtain ⟨hqltL, hqval⟩ := List.getElem?_eq_some_iff.mp hk1
    have hord := (List.pairwise_iff_getElem.mp hinv0.order) k (k + 1) hkltL hqltL (by omega)
    rw [hkval, hqval] at hord
    exact hord
  have hnextComma : next < comma := by
    obtain ⟨h1, h1v⟩ := List.getElem?_eq_some_iff.mp hk1
    obtain ⟨h2, h2v⟩ := List.getElem?_eq_some_iff.mp hcommaEnt
    have hh := (List.pairwise_iff_getElem.mp hinv0.order) (k + 1) (k + 2) h1 h2 (by omega)
    rw [h1v, h2v] at hh
    exact hh
  have hlq : lane ≤ comma := by omega
  have hqN : comma ≤ K.n := le_of_lt (hinv0.inside comma (List.mem_of_getElem? hcommaEnt))
  have hdelta : len + 2 ≤ comma - lane := by omega
  have hspan : lane + 2 ≤ next + 1 := by omega
  have hkAddr : k + 3 < 2 ^ 63 := by
    have h1 := hinv0.maxDoc
    have h2 := hinv0.nepLe
    simp only [stage2MaxDocument] at h1
    omega
  have hquote : K.bs[lane]? = some (34 : UInt8) := by
    have hbyte34 : byte = (34 : UInt8) := by
      apply UInt8.toNat_inj.mp
      simpa using hb
    rw [hbs, hbyte34]
  have htokN : K.tok + 1 ≤ K.n := by
    unfold Stage2NoEventWalkCount at count
    have h1 : K.nep ≤ K.n := hinv0.nepLe
    omega
  have hinvMidKc : Stage2NoEventWalkInv (stage2NoEventWalkStringCarry K len body) mem sMid :=
    Stage2NoEventWalkInv.stringArena hseg1.inv' htokN
  have hlen63 : len < 2 ^ 63 := by
    have h0 := hinv0.inside next (List.mem_of_getElem? hk1)
    have h1 := hinv0.maxDoc
    simp only [stage2MaxDocument] at h1
    omega
  have hlenLt64 : len < 2 ^ 64 := by omega
  have hbL (n : String) (v : Value) (hv : (n, v) ∈ stage2NoEventWalkBaseValues K) :
      lookupName sMid.env n = some v := hbaseMid n v hv
  -- the arena slice
  obtain ⟨sA, jA, hjA, hrunA, hpcA, hpreA, hmemA, hAalen, hAarena, hAtok, hAterms, hAfr,
    hAsp, hAinc, hbaseA⟩ :=
    stage2NoEventWalkStringArenaArm (gap := gap) (K := K) (s := sMid) (mem := r.mem)
      (sc := K.scratch) (arenaWord := K.arenaWord) (alen := K.arena.length) (len := len)
      (tokens := K.tok) (terms := K.terms) (outn := K.next0 + 16)
      (spv := iv.toNat % 2 ^ 32) (body := body) (inc217 := BitVec.ofNat 64 (k + 2))
      (fr := BitVec.ofNat 8 1)
      hpcMid hmemMid
      (hbL "%outn205" (.ptr (K.next0 + 16)) (by
        simp [stage2NoEventWalkBaseValues, stage2NoEventWalkBaseCellValues, entryCells1,
          entryCells2, entryCells3, entryCells4, preHeaderCells]))
      hreadOutn hlenLt64 hlen0 hlen63
      (hbL "%scratch" (.ptr K.scratch) (by
        simp [stage2NoEventWalkBaseValues, stage2NoEventWalkParamEntries]))
      (hbL "%invariant.gep1650" (.ptr (K.scratch + 1)) (by
        simp [stage2NoEventWalkBaseValues, stage2NoEventWalkBaseCellValues, preHeaderCells]))
      (hbL "%invariant.gep1652" (.ptr (K.scratch + 2)) (by
        simp [stage2NoEventWalkBaseValues, stage2NoEventWalkBaseCellValues, preHeaderCells]))
      (hbL "%invariant.gep1654" (.ptr (K.scratch + 3)) (by
        simp [stage2NoEventWalkBaseValues, stage2NoEventWalkBaseCellValues, preHeaderCells]))
      (hbL "%invariant.gep1656" (.ptr (K.scratch + 4)) (by
        simp [stage2NoEventWalkBaseValues, stage2NoEventWalkBaseCellValues, preHeaderCells]))
      (hbL "%invariant.gep1658" (.ptr (K.scratch + 5)) (by
        simp [stage2NoEventWalkBaseValues, stage2NoEventWalkBaseCellValues, preHeaderCells]))
      (hbL "%invariant.gep1660" (.ptr (K.scratch + 6)) (by
        simp [stage2NoEventWalkBaseValues, stage2NoEventWalkBaseCellValues, preHeaderCells]))
      (hbL "%invariant.gep1662" (.ptr (K.scratch + 7)) (by
        simp [stage2NoEventWalkBaseValues, stage2NoEventWalkBaseCellValues, preHeaderCells]))
      (hlift "%alen.0.ph1405" _ (by decide) halen27)
      (hlift "%tokens.0.lcssa1075" _ (by decide) htok27)
      (hlift "%terms.0.lcssa1081" _ (by decide) hterms27)
      (hlift "%inc217" _ (by decide) hinc27)
      (hlift "%sp.0.lcssa1093.wide" _ (by decide) hsp27)
      (hlift "%frame.0.lcssa1099" _ (by decide) hfr27) hbaseMid
      (hlift "%arena.0.ph1406" _ (by decide) harena27) hbodyRead hbodyLen
      (Nat.lt_or_ge len 8)
  have hlenEq : len + K.arena.length =
      (stage2NoEventWalkStringCarry K len body).arena.length := by
    rw [stage2NoEventWalkStringCarry_arena, List.length_append, hbodyLen]
    omega
  have htermsEq : ((K.arena.length + 6) + len) + K.terms =
      (stage2NoEventWalkStringCarry K len body).terms := by
    show ((K.arena.length + 6) + len) + K.terms =
      K.terms + (EventRecord.tagStr + len + K.arena.length)
    rw [EventRecord.tagStr]
    omega
  have hInvA : Stage2NoEventWalkInv (stage2NoEventWalkStringCarry K len body) mem sA :=
    hinvMidKc.mem_congr (by rw [hmemA, hmemMid])
  have hafter : Stage2NoEventWalkStringAfter
      (stage2NoEventWalkStringCarry K len body) (k + 2) 1 (iv.toNat % 2 ^ 32) sA :=
    stage2NoEventWalkStringAfter_of_lookups (Kc := stage2NoEventWalkStringCarry K len body)
      (kc := k + 2) hpreA hAfr hAsp
      (by rw [hAinc]) (by rw [hAalen, hlenEq]) hAarena
      (by rw [hAterms, htermsEq]) hAtok
  let route : Stage2NoEventWalkStringRoute (stage2NoEventCalls gap) mem K k s0 :=
    stage2NoEventWalkStringRoute_arena (calls := stage2NoEventCalls gap) (mem := mem)
      (K := K) (k := k) (s := s0) htrace
      (sMid := sMid) (sA := sA) (jHead := 7) (jTail := jA) (lane := lane) (len := len)
      (q := comma) (frame := 1) (sp := iv.toNat % 2 ^ 32) (body := body) (cs := cs)
      (nextLane := next) hseg7 ⟨hrunA, hInvA⟩ hpcA hafter (by decide) (by decide)
      (Nat.mod_lt _ (by decide)) hspNe hkAddr
      (by rw [stage2NoEventWalkStringCarry]; exact hklt)
      hk hcommaEnt hlq hqN (by omega) hdelta (by
        show Stage2NoEventWalkBaseLookups (stage2NoEventWalkStringCarry K len body) sA
        exact hbaseA) hbPos hcomma hquote hspan hcode hbelow hbodyLen hdecode
  refine ⟨stage2NoEventWalkStringRow_cont_of_route_count count route ?_⟩
  have hjTail : route.jTail ≤ 3 + (route.len + 1) + 2 ∨
      route.jTail ≤ route.len / 8 + route.len % 8 + 8 := hjA
  have hpot := stage2NoEventWalkStringPotential (K := K) (Kc := route.Kc)
    (k := k) (lane := route.lane) (q := route.q)
    (by have := route.klt; rw [route.nepEq] at this; omega)
    route.laneEq route.qEq route.laneLeQ route.qLeN
    route.nepEq route.nEq route.entEq
  have hheadBound := route.headBound
  have hdelta' := route.deltaLe
  rcases hjTail with hj | hj
  · omega
  · have hdm := Nat.div_add_mod route.len 8
    have hle : route.len / 8 + route.len % 8 ≤ route.len := by omega
    omega

/-- **The string class's continuing row at `string_value.loopexit`, empty-string
arm**: the entry head, the leg, `LeafBlock27`'s step at form one, the two-block
plain handoff, and the shared cycle. -/
noncomputable def stage2NoEventWalkStringRow_of_entry_plain {gap : Calls} {F : Nat}
    {K : Stage2NoEventWalkCarry} {mem : Mem} {k : Nat} {s0 : State}
    (hinv0 : Stage2NoEventWalkInv K mem s0)
    (hpc0 : s0.pc = "string_value.loopexit")
    (hbase0 : Stage2NoEventWalkBaseLookups K s0)
    {iv : BitVec 64} {lane : Nat}
    (h8 : lookupName s0.env "%8" = some (.int 32 (BitVec.ofNat 32 lane)))
    (hiv : lookupName s0.env "%indvars.iv" = some (.int 64 iv))
    (hinc0 : lookupName s0.env "%inc" = some (.int 64 (BitVec.ofNat 64 (k + 1))))
    (hk0 : lookupName s0.env "%k.0" = some (.int 64 (BitVec.ofNat 64 k)))
    (htr0 : lookupName s0.env "%terms.0" = some (.int 64 (BitVec.ofNat 64 K.terms)))
    (htok0 : lookupName s0.env "%tokens.0" = some (.int 64 (BitVec.ofNat 64 K.tok)))
    {o : Nat} (houtn0 : lookupName s0.env "%outn205" = some (.ptr o))
    {nepv : BitVec 64}
    (hnep0 : lookupName s0.env "%nep" = some (.int 64 nepv))
    {r0 : CallOutcome}
    (hlife : stage2NoEventCalls gap "llvm.lifetime.start.p0"
      [.int 64 (BitVec.ofNat 64 8), .ptr o] s0.mem s0.next = some r0)
    (hmemLife : r0.mem = s0.mem) (hnextLife : r0.next = s0.next)
    (hguard0 : evalICmp .ult (BitVec.ofNat 64 (k + 1)) nepv = 1)
    (halen0 : lookupName s0.env "%alen.0.ph1405" =
      some (.int 64 (BitVec.ofNat 64 K.arena.length)))
    (harena0 : lookupName s0.env "%arena.0.ph1406" =
      some (.int 64 (BitVec.ofNat 64 K.arenaWord)))
    {next comma : Nat} {byte : UInt8}
    (hk : K.ent[k]? = some lane) (hbs : K.bs[lane]? = some byte) (hb : byte.toNat = 34)
    (hk1 : K.ent[k + 1]? = some next)
    (hcommaEnt : K.ent[k + 2]? = some comma)
    (hcomma : ∀ q, K.ent[k + 2]? = some q → K.bs.getD q 0 = 44)
    (hklt : k + 3 < K.nep)
    (hspNe : iv.toNat % 2 ^ 32 ≠ 0)
    {r : CallOutcome}
    (hret : r.ret = .int 32 (BitVec.ofNat 32 1))
    (hscratch : next - lane - 1 + 64 ≤ K.scratchcap)
    {foot : List (Nat × Nat)}
    (hcall : stage2NoEventCalls gap "s2_string_body"
      (stage2NoEventWalkStringArgs K lane (BitVec.ofNat 64 (next - lane - 1)))
      (writeBytes (writeBytes s0.mem (K.c + 32) (natToBytes (k + 2) 8))
        (K.next0 + 16) (natToBytes 0 8)) s0.next = some r)
    (hframe : UnchangedOutside
      (writeBytes (writeBytes s0.mem (K.c + 32) (natToBytes (k + 2) 8))
        (K.next0 + 16) (natToBytes 0 8)) r.mem foot)
    (hfoot : ∀ q ∈ foot,
      ∃ r' ∈ stage2NoEventRunRegions K.scratch K.scratchcap K.stk K.e K.c K.d ++
        [(K.next0, K.nextEnd - K.next0)], r'.1 ≤ q.1 ∧ q.1 + q.2 ≤ r'.1 + r'.2)
    (hpresent : ∀ a, inRegions
      (stage2NoEventRunRegions K.scratch K.scratchcap K.stk K.e K.c K.d) a →
        present r.mem a)
    (hcodeEmpty : bodyCodePoints K.bs ⟨lane, lane + 2⟩ = some [])
    (hsubZero : next - lane - 1 = 0)
    (hbPos : 1 ≤ K.b)
    (htrace : Stage2NoEventWalkTrace K)
    (count : Stage2NoEventWalkCount K k) :
    Stage2NoEventWalkRow (stage2NoEventCalls gap) mem F K k s0 := by
  classical
  refine Classical.choice (show Nonempty
    (Stage2NoEventWalkRow (stage2NoEventCalls gap) mem F K k s0) from ?_)
  have hwLt : lane < 2 ^ 32 := by
    have h0 := hinv0.inside lane (List.mem_of_getElem? hk)
    have h1 := hinv0.maxDoc
    simp only [stage2MaxDocument] at h1
    omega
  obtain ⟨sE, hsegE, hpcE, hmemE, hnextE, hincE, hlcE, hidxE, hfrE, hspE, hkE,
    htrE, htokE, halenE, harenaE, hbaseE⟩ :=
    stage2NoEventWalkStringEntryBase (calls := stage2NoEventCalls gap)
      (K := K) (mem := mem) (s := s0) hinv0 hpc0 (w := BitVec.ofNat 32 lane) h8 hiv
      (inc := BitVec.ofNat 64 (k + 1)) (k := BitVec.ofNat 64 k)
      (terms := BitVec.ofNat 64 K.terms) (tok := BitVec.ofNat 64 K.tok) hinc0 hk0 htr0 htok0
      houtn0 hnep0 hlife hmemLife hnextLife hguard0
      (alen := K.arena.length) (arenaWord := K.arenaWord) halen0 harena0 hbase0
  have hidxE' : lookupName sE.env "%idxprom.lcssa1109" =
      some (.int 64 (BitVec.ofNat 64 lane)) := by
    simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hwLt] using hidxE
  have hcallE : stage2NoEventCalls gap "s2_string_body"
      (stage2NoEventWalkStringArgs K lane (BitVec.ofNat 64 (next - lane - 1)))
      (writeBytes (writeBytes sE.mem (K.c + 32) (natToBytes (k + 2) 8))
        (K.next0 + 16) (natToBytes 0 8)) sE.next = some r := by
    rw [hmemE, hmemLife, hnextE]
    exact hcall
  have hframeE : UnchangedOutside
      (writeBytes (writeBytes sE.mem (K.c + 32) (natToBytes (k + 2) 8))
        (K.next0 + 16) (natToBytes 0 8)) r.mem foot := by
    rw [hmemE, hmemLife]
    exact hframe
  obtain ⟨s27, hseg4, hinv27, hbase27, hpc27, hmem27, hcall243, halen27, harena27, htok27,
    hterms27, hinc27, hfr27, hsp27, hsub27, hlc27⟩ :=
    stage2NoEventWalkStringCallLeg (gap := gap) (K := K) (mem := mem) (k := k) (s := sE)
      (fr := 1) (sp := iv.toNat % 2 ^ 32) (lane := lane) (next := next)
      hsegE.inv' hpcE hbaseE hk hkE hincE hlcE hidxE' hfrE hspE htokE htrE
      halenE harenaE
      hk1 hklt (form := 1) hret (Or.inl rfl) hscratch hcallE hframeE hfoot hpresent
  obtain ⟨sMid, hseg1, hpcMid, hmemMid27, hbaseMid, hlift⟩ :=
    stage2NoEventWalkStringLeaf27StepPlain (gap := gap) (K := K) (mem := mem) (s := s27)
      hinv27 hpc27 hbase27 hcall243
  have hmemMid : sMid.mem = r.mem := by rw [hmemMid27, hmem27]
  have hseg7 : Stage2NoEventWalkSegment (stage2NoEventCalls gap) mem K s0 K sMid 7 :=
    hsegE.trans (hseg4.trans hseg1)
  have hlaneNext : lane < next := by
    obtain ⟨hkltL, hkval⟩ := List.getElem?_eq_some_iff.mp hk
    obtain ⟨hqltL, hqval⟩ := List.getElem?_eq_some_iff.mp hk1
    have hord := (List.pairwise_iff_getElem.mp hinv0.order) k (k + 1) hkltL hqltL (by omega)
    rw [hkval, hqval] at hord
    exact hord
  have hnextComma : next < comma := by
    obtain ⟨h1, h1v⟩ := List.getElem?_eq_some_iff.mp hk1
    obtain ⟨h2, h2v⟩ := List.getElem?_eq_some_iff.mp hcommaEnt
    have hh := (List.pairwise_iff_getElem.mp hinv0.order) (k + 1) (k + 2) h1 h2 (by omega)
    rw [h1v, h2v] at hh
    exact hh
  have hlq : lane ≤ comma := by omega
  have hqN : comma ≤ K.n := le_of_lt (hinv0.inside comma (List.mem_of_getElem? hcommaEnt))
  have hdelta : 0 + 2 ≤ comma - lane := by omega
  have hspan : lane + 2 ≤ next + 1 := by omega
  have hkAddr : k + 3 < 2 ^ 63 := by
    have h1 := hinv0.maxDoc
    have h2 := hinv0.nepLe
    simp only [stage2MaxDocument] at h1
    omega
  have hquote : K.bs[lane]? = some (34 : UInt8) := by
    have hbyte34 : byte = (34 : UInt8) := by
      apply UInt8.toNat_inj.mp
      simpa using hb
    rw [hbs, hbyte34]
  have htokN : K.tok + 1 ≤ K.n := by
    unfold Stage2NoEventWalkCount at count
    have h1 : K.nep ≤ K.n := hinv0.nepLe
    omega
  have hlane1 : lane + 1 < 2 ^ 32 := by
    have h0 := hinv0.inside next (List.mem_of_getElem? hk1)
    have h1 := hinv0.maxDoc
    simp only [stage2MaxDocument] at h1
    omega
  have hbL (n : String) (v : Value) (hv : (n, v) ∈ stage2NoEventWalkBaseValues K) :
      lookupName sMid.env n = some v := hbaseMid n v hv
  have hsubMid : lookupName sMid.env "%sub234" = some (.int 64 (BitVec.ofNat 64 0)) := by
    rw [← hsubZero]
    exact hlift "%sub234" _ (by decide) hsub27
  obtain ⟨sA, jA, hjA, hsegTail, hpcA, hafter, hInvA, hbaseA⟩ :=
    stage2NoEventWalkStringPlainTail (gap := gap) (K := K) (mem := mem) (k := k)
      (s := sMid) (lane := lane) (fr := 1) (sp := iv.toNat % 2 ^ 32) (outn := K.next0 + 16)
      hseg1.inv' hpcMid (hlift "%.lcssa1125" _ (by decide) hlc27) hsubMid
      (hlift "%tokens.0.lcssa1075" _ (by decide) htok27)
      (hlift "%terms.0.lcssa1081" _ (by decide) hterms27)
      (hlift "%alen.0.ph1405" _ (by decide) halen27)
      (hlift "%arena.0.ph1406" _ (by decide) harena27)
      (hbL "%outn205" (.ptr (K.next0 + 16)) (by
        simp [stage2NoEventWalkBaseValues, stage2NoEventWalkBaseCellValues, entryCells1,
          entryCells2, entryCells3, entryCells4, preHeaderCells]))
      (hlift "%frame.0.lcssa1099" _ (by decide) hfr27)
      (hlift "%sp.0.lcssa1093.wide" _ (by decide) hsp27)
      (hlift "%inc217" _ (by decide) hinc27) hbaseMid hwLt hlane1 htokN
  let route : Stage2NoEventWalkStringRoute (stage2NoEventCalls gap) mem K k s0 :=
    stage2NoEventWalkStringRoute_plain (calls := stage2NoEventCalls gap) (mem := mem)
      (K := K) (k := k) (s := s0) htrace
      (sMid := sMid) (sA := sA) (jHead := 7) (jTail := jA) (lane := lane) (q := comma)
      (frame := 1) (sp := iv.toNat % 2 ^ 32)
      hseg7 hsegTail hpcA hafter (by decide) (by decide) (Nat.mod_lt _ (by decide)) hspNe hkAddr
      (by rw [stage2NoEventWalkStringCarryPlain]; exact hklt)
      hk hcommaEnt hlq hqN (by omega) hdelta (by
        show Stage2NoEventWalkBaseLookups (stage2NoEventWalkStringCarryPlain K lane) sA
        exact hbaseA) hbPos hcomma hquote hcodeEmpty
  refine ⟨stage2NoEventWalkStringRow_cont_of_route_count count route ?_⟩
  have hjTail : route.jTail ≤ 2 := hjA
  have hpot := stage2NoEventWalkStringPotential (K := K) (Kc := route.Kc)
    (k := k) (lane := route.lane) (q := route.q)
    (by have := route.klt; rw [route.nepEq] at this; omega)
    route.laneEq route.qEq route.laneLeQ route.qLeN
    route.nepEq route.nEq route.entEq
  have hheadBound := route.headBound
  have hdelta' := route.deltaLe
  omega

/-! ### Axiom footprints -/

#print axioms stage2NoEventWalkInv_laneAt
#print axioms Stage2NoEventWalkBaseLookups.stringValueCells
#print axioms stage2NoEventWalkStringEntryBase
#print axioms stage2NoEventWalkStringCallLeg
#print axioms stage2NoEventWalkStringLeaf27StepArena
#print axioms stage2NoEventWalkStringLeaf27StepPlain
#print axioms stage2NoEventWalkStringRow_of_entry_arena
#print axioms stage2NoEventWalkStringRow_of_entry_plain

end LeanLLVM.Refinement
