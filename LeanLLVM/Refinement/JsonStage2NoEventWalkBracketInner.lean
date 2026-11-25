/-
The no-event walk's bracket descend, inner half: the dispatch's `[` leaf, the
marker push, and the element's two arms.

`JsonStage2NoEventWalkRowsDescend` proves the bracket head's own segment to the
continuation dispatch `NodeBlock15` and names the rest `Stage2NoEventWalkBracketInner`.
That premise's window is `Stage2NoEventWalkBracketDispatch`: `%7` (the element's
class byte), `%8` (its lane), `%k.0 = k + 1`, `%inc = k + 2`, the two counts, and
the base lookups.  This module supplies the missing link: from `NodeBlock15`'s
`[` leaf (`LeafBlock9`) through `if.then35`'s array-stack bound test and
`if.end51`'s marker push, at `if.end327`'s entry, where the entry at `k + 2` is
read and tested for `]`.

**The block the tree did not model.**  `if.end51` had no pin and no link: the
parsed body carries the block (`JsonStage2NoEventIR`), but no `_find` lemma and
no row.  `ifEnd51Block`/`ifEnd51Block_find` pin it and `link_ifEnd51` walks it —
the `gep` at `%stk + %indvars.iv.in`, the one-byte store of the marker `1`, and
the `%inc < %nep` guard — carrying the invariant across the stack write by
`Stage2NoEventWalkInv.stack_write`, exactly as the peeled push's
`link_ifThen47peel` does.

**The closer's edge the tree did not model.**  `link_ifThen334` states
`if.then334`'s `phi` run at the `if.end327.peel` edge only; the continuation
route reaches it from `if.then334.loopexit`, whose `phi` sources are `%48`,
`%k.0`, `%terms.0`, `%tokens.0`.  `link_ifThen334LoopexitEdge` is that edge.

**What is proved here.**

* the five-block prologue: `NodeBlock15` → `NodeBlock13` → `LeafBlock9` →
  `if.then35` → `if.end51`, as a chain to `if.end327`'s entry;
* the closer arm: `if.end327`'s `]` read, `if.then334.loopexit`, `if.then334`,
  `close_arr` and `if.then350`'s pop read, ten blocks to `after_value` at index
  `k + 3`, with the class's `Stage2NoEventWalkCycleSrc`, and the trace by the
  existing `[` and `[]` relations;
* the element arm: `if.end327`'s false byte test and `if.end`'s six `phi`s and
  four adds, seven blocks to the next `NodeBlock15` at index `k + 1`;
* both arms as `Stage2NoEventWalkBracketInnerOut` producers, with the tree's
  cycle `stage2NoEventWalkCycle_of_afterValue`.

**The window's missing cells.**  `Stage2NoEventWalkBracketDispatch` records the
class byte, its lane, the index, the guard's index, the two counts and the base
lookups.  Beyond those, the window carries twenty-three fields, none a
consequence of the dispatch: the invariant; the array stack's cursor cell, its
bound cell and their relation and stack room (`%indvars.iv.in`,
`%indvars.iv`, `%wide.trip.count1409`, `iv`'s value, the cursor's `< 520`); the
stack base; the head's two arena `phi`s; the consumed-count bound; the
four-entry liveness; the report's base; the outer opener's lane and byte; and the
trace.  `if.then35` compares `%indvars.iv` with `%wide.trip.count1409`; the
marker push addresses `%stk + %indvars.iv.in`; the closer reads the entry at
`k + 2`; the trace needs the outer `[`'s *byte* at its lane to account the token
the descend's `if.end` already counted in the registers.  **The dispatch struct
is this window's projection** (its `disp` field): the richer window is the
dispatch window this route needs, and the assembly's arm premise can be restated
over it without changing anything proved here.

**The recursion's trace is a hypothesis, not a fact about the carry.**  A
`Stage2NoEventWalkTrace` is a predicate over `K.bs`, `K.arena` and the counts; no
carry alone determines one, so a trace-free premise (`Stage2NoEventWalkBracketInner`)
cannot produce the endpoint's `CycleSrc`.  `Stage2NoEventWalkBracketInnerAll` is
therefore stated **over the window**, so the recursion receives the trace it
needs at every level, exactly as `stage2NoEventWalkRow_cont_bracketPair` threads
`htrace`.  The element arm builds the *successor* window's trace at `K1` from
`bs1`/`byte91` (`stage2NoEventWalkOpenBracketRel` and `Stage2NoEventWalkTrace.step`,
the closer's own construction), and the successor window's staging — including
its `live : k + 5 < nep` — is the caller's, supplied at each dispatch of the
element's class.

**The price.**  The closer's inner segment is ten blocks; the shared cycle's
price is its own credit (eight).  The row's form is
`j0 + 10 + p + Φ(k+4) ≤ Φ(k)`, i.e. `j0 + 18 ≤ 128 + 8·(ent[k+4] − ent[k])`.
The arm states the prefix's share as `j0 + 10 ≤ 96`: the descend step's own chain
is nine links (`…BracketDescendStep`), so `9 + 10 = 19 ≤ 96` holds with room.
The element arm's prefix is seven links and its stated share is `j0 + 7 ≤ 32`.

**What the demanded premise cannot carry.**  `Stage2NoEventWalkBracketInner`'s
`price` field quantifies over the caller's `j0` but has no bound on it: the
caller obtains `j0` from `Stage2NoEventWalkSegment.of_chain`, an existential, so
no row can discharge that field from the chain alone.  The producers here take
the prefix's share as an explicit hypothesis of the same shape; a caller that
knows its own chain's count — the descend step's is nine — supplies it.
-/
import LeanLLVM.Refinement.JsonStage2NoEventWalkRowsDescend
import LeanLLVM.Refinement.JsonStage2NoEventWalkRowsContainerB

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000
set_option pp.maxSteps 200000

namespace LeanLLVM.Refinement

open LeanLLVM
open LeanLLVM.JSON
open LeanLLVM.Refinement.JsonStage2NoEventIR
open LeanLLVM.Refinement.JsonEntryIR (readLanes32)
open LeanLLVM.Refinement.BlockEval
open LeanLLVM.Refinement.JsonEntrySteps
  (readBytes_writeBytes_frame readBytes_length readBytes_one)

/-! ### `if.end51`: the array's marker push, pinned

The parsed body carries the block; no module pinned it or walked it.  The three
instructions are the fixture's: the `gep` at `%stk + %indvars.iv.in`, the one-byte
store of `1`, and the next entry's guard. -/

/-- `if.end51`: the non-peeled array's marker push and next-entry guard. -/
def ifEnd51Block : Block :=
  { name := "if.end51",
    instrs :=
      [ Instr.gep "%arrayidx50" (Ty.int 8) (Operand.reg "%stk")
          (Operand.reg "%indvars.iv.in"),
        Instr.store (Ty.int 8) (Operand.imm (.int 8 (BitVec.ofNat 8 1)))
          (Operand.reg "%arrayidx50"),
        Instr.icmp "%cmp319.not" IPred.ult 64 (Operand.reg "%inc")
          (Operand.reg "%nep") ],
    term := Term.condbr (Operand.reg "%cmp319.not") "if.end327" "if.then321" }

theorem ifEnd51Block_find :
    stage2NoEventBody.findBlock "if.end51" = some ifEnd51Block := by
  decide

/-- The byte the marker push stores: `1` at one byte. -/
def stage2NoEventWalkBracketMarker : List UInt8 :=
  natToBytes ((BitVec.ofNat 8 1).toNat) ((8 + 7) / 8)

theorem stage2NoEventWalkBracketMarker_length :
    stage2NoEventWalkBracketMarker.length = 1 := by
  decide

theorem stage2NoEventWalkBracketMarker_val :
    bytesToNat stage2NoEventWalkBracketMarker = 1 := by
  decide

/-! ### A one-byte store of an immediate

`stage2NoEventWalk_denote_store_int` stores a register's word; the marker push
stores the literal `1`. -/

theorem stage2NoEventWalk_denote_store8_imm (calls : Calls) (env : Env) (s : State)
    (x : BitVec 8) (p : String) {a : Nat}
    (hp : lookupName env p = some (.ptr a)) (is : List Instr) :
    denoteCode calls (.store (.int 8) (.imm (.int 8 x)) (.reg p) :: is)
        (stateAt env s) =
      denoteCode calls is
        (stateAt env (stage2NoEventStepState s
          (writeBytes s.mem a (natToBytes x.toNat ((8 + 7) / 8))) s.next)) := by
  have hstep : evalInstr calls (stateAt env s)
      (.store (.int 8) (.imm (.int 8 x)) (.reg p)) =
      some (stateAt env (stage2NoEventStepState s
        (writeBytes s.mem a (natToBytes x.toNat ((8 + 7) / 8))) s.next)) := by
    simp only [evalInstr, evalOperand, Const.toValue, hp, storeValue, State.bind,
      reduceIte, stateAt, stage2NoEventStepState]
  rw [denoteCode_cons_of _ _ _ _ _ hstep]

/-- **`if.end51`'s marker push**: the `gep`, the one-byte store and the
next-entry guard, at the address the `gep` computes.  The stack write is the
invariant's (`stack_write`), the address inside the stack's 520 bytes. -/
theorem link_ifEnd51 {calls : Calls} {K : Stage2NoEventWalkCarry} {mem : Mem}
    {s : State} {ivIn inc nep : BitVec 64} {stk a : Nat}
    (h : Stage2NoEventWalkInv K mem s) (hpc : s.pc = "if.end51")
    (hivIn : lookupName s.env "%indvars.iv.in" = some (.int 64 ivIn))
    (hstk : lookupName s.env "%stk" = some (.ptr stk))
    (hinc : lookupName s.env "%inc" = some (.int 64 inc))
    (hnep : lookupName s.env "%nep" = some (.int 64 nep))
    (hpos : (ivIn.signExtend 64).toNat < 2 ^ 63)
    (ha : a = stk + (ivIn.signExtend 64).toNat)
    (hstkK : stk = K.stk) (hoff : (ivIn.signExtend 64).toNat < 520)
    (hult : BitVec.ult inc nep = true) :
    Stage2NoEventWalkLink calls K mem s K
      (stage2NoEventWalkStored
        (("%cmp319.not", .int 1 1) ::
          ("%arrayidx50", .ptr a) :: s.env)
        s (writeBytes s.mem a stage2NoEventWalkBracketMarker) "if.end327") := by
  have hbit : evalICmp .ult inc nep = (1 : BitVec 1) := by
    simp only [evalICmp, hult]
    rfl
  have hcode : denoteCode calls ifEnd51Block.instrs (stateAt s.env s) =
      some (stateAt
        (("%cmp319.not", .int 1 1) ::
          ("%arrayidx50", .ptr a) :: s.env)
        (stage2NoEventStepState s
          (writeBytes s.mem a
            (natToBytes (BitVec.ofNat 8 1).toNat ((8 + 7) / 8))) s.next)) := by
    rw [ifEnd51Block]
    rw [denoteCode_gep8_reg (calls := calls) (env := s.env) (s := s)
      (d := "%arrayidx50") (base := "%stk") (off := "%indvars.iv.in")
      (a := stk) (idx := ivIn) hstk hivIn hpos]
    rw [← ha]
    rw [stage2NoEventWalk_denote_store8_imm (calls := calls) (env := _) (s := s)
      (x := BitVec.ofNat 8 1) (p := "%arrayidx50") (a := a)
      (by simp only [lookupName_cons_self])]
    rw [denoteCode_icmp_ult_reg (calls := calls) (env := _) (s := _)
      (d := "%cmp319.not") (a := "%inc") (b := "%nep") (x := inc) (y := nep)
      (by
        rw [lookupName_cons_ne _ _ (by decide)]
        exact hinc)
      (by
        rw [lookupName_cons_ne _ _ (by decide)]
        exact hnep)
      (is := [])]
    simp only [hbit, denoteCode_nil]
  refine ⟨h, ?_, ?_⟩
  · have hstep := stage2NoEventWalk_step_condbr_true (f := stage2NoEventBody)
      (by rw [hpc]; exact ifEnd51Block_find)
      (by simpa only [stateAt] using hcode) rfl (by rw [lookupName_cons_self])
    simpa only [stage2NoEventWalkStored, stage2NoEventWalkNext, stage2NoEventStepState,
      stateAt, stage2NoEventWalkBracketMarker] using hstep
  · refine Stage2NoEventWalkInv.mem_congr
      (Stage2NoEventWalkInv.stack_write h
        (a := a) (bs := stage2NoEventWalkBracketMarker) ?_) rfl
    intro k hk
    have hk0 : k = 0 := by
      have hl := stage2NoEventWalkBracketMarker_length
      omega
    subst hk0
    have haK : a = K.stk + (ivIn.signExtend 64).toNat := by rw [ha, hstkK]
    rw [haK]
    refine ⟨(K.stk, 520), ?_, by omega, by omega⟩
    exact List.mem_append_left _ (List.mem_cons_of_mem _ List.mem_cons_self)

/-! ### The closer's `phi` run at the continuation edge

`if.then334`'s four `phi`s at the `if.then334.loopexit` edge: the depth is `%48`,
the index `%k.0`, and the two counts the entry's own. -/

/-- `if.then334`'s `phi` run at the `if.then334.loopexit` edge. -/
theorem ifThen334_phi_denote_loopexit (calls : Calls) (env : Env) (s : State)
    {sp : BitVec 32} {k terms tok : BitVec 64}
    (hpre : s.pre = some "if.then334.loopexit")
    (hsp : lookupName env "%48" = some (.int 32 sp))
    (hk : lookupName env "%k.0" = some (.int 64 k))
    (htr : lookupName env "%terms.0" = some (.int 64 terms))
    (htokr : lookupName env "%tokens.0" = some (.int 64 tok)) :
    denoteCode calls ifThen334PhiInstrs (stateAt env s) =
      some (stateAt (cells (ifThen334PhiCells sp k tok terms) env) s) := by
  have hsel : PhiSelects (stateAt env s) "if.then334.loopexit" ifThen334PhiSpecs
      [("%sp.0.lcssa1096.wide", .int 32 sp), ("%k.0.lcssa1090", .int 64 k),
       ("%terms.0.lcssa1084", .int 64 terms),
       ("%tokens.0.lcssa1078", .int 64 tok)] := by
    refine PhiSelects.cons (op := .reg "%48") (by decide) ?_
      (PhiSelects.cons (op := .reg "%k.0") (by decide) ?_
        (PhiSelects.cons (op := .reg "%terms.0") (by decide) ?_
          (PhiSelects.cons (op := .reg "%tokens.0") (by decide) ?_
            PhiSelects.nil)))
    all_goals simp only [stateAt, evalOperand, hsp, hk, htr, htokr]
  rw [ifThen334_phi_eq, ← List.append_nil (List.map PhiSpec.instr ifThen334PhiSpecs),
    denoteCode_phiRun (s := stateAt env s) (p := "if.then334.loopexit")
      (specs := ifThen334PhiSpecs) (rest := [])
      (hpre := hpre) (hsel := hsel) (hrest := rfl)]
  simp only [State.bindAll, State.bind, ifThen334PhiCells, cells]
  rfl

/-- **`if.then334` at the continuation edge**: the four `phi`s and the three
counts, `K` to `{K with tok := K.tok + 2, terms := K.terms + 7}`. -/
theorem link_ifThen334LoopexitEdge {calls : Calls} {K : Stage2NoEventWalkCarry}
    {mem : Mem} {s : State} {sp : BitVec 32} {k terms tok : BitVec 64}
    (h : Stage2NoEventWalkInv K mem s) (hpc : s.pc = "if.then334")
    (hpre : s.pre = some "if.then334.loopexit")
    (hsp : lookupName s.env "%48" = some (.int 32 sp))
    (hk : lookupName s.env "%k.0" = some (.int 64 k))
    (htr : lookupName s.env "%terms.0" = some (.int 64 terms))
    (htokr : lookupName s.env "%tokens.0" = some (.int 64 tok))
    (htok : K.tok + 2 ≤ K.n) :
    Stage2NoEventWalkLink calls K mem s
      { K with tok := K.tok + 2, terms := K.terms + 7 }
      (bracketCounts s sp k tok terms) := by
  have h1 := ifThen334_phi_denote_loopexit (calls := calls) (env := s.env) (s := s)
    (sp := sp) (k := k) (terms := terms) (tok := tok) hpre hsp hk htr htokr
  have h2 := ifThen334_counts_denote (calls := calls) (env := s.env) (s := s)
    (sp := sp) (k := k) (terms := terms) (tok := tok)
  have hcode : denoteCode calls ifThen334Block.instrs (stateAt s.env s) =
      some (stateAt (cells (ifThen334AllCells sp k tok terms) s.env) s) := by
    rw [ifThen334_split]
    rw [denoteCode_append_apply (a := ifThen334PhiInstrs) (b := ifThen334Rest)
      h1 (by decide)]
    exact h2
  refine ⟨h, ?_, ?_⟩
  · have hstep := stage2NoEventWalk_step_br (s := s) (f := stage2NoEventBody)
      (by rw [hpc]; exact ifThen334Block_find)
      (by simpa only [stateAt] using hcode) rfl
    simpa only [bracketCounts, stage2NoEventWalkNext, stateAt] using hstep
  · exact Stage2NoEventWalkInv.mem_congr (Stage2NoEventWalkInv.count h htok) rfl

/-! ### The marker write keeps a carry

The descend's `if.end` advances the counts in the registers, not in the carry.
`Stage2NoEventWalkLink`'s two carry indices let a link's source and target carry
differ; this restates a link whose target carry the count bound supplies. -/

/-- **A link at a reindexed carry**: the run and the invariant at the source are
the link's, the target's invariant is the caller's. -/
theorem Stage2NoEventWalkLink.reindex {calls : Calls} {K K' : Stage2NoEventWalkCarry}
    {mem : Mem} {s s' : State} (hl : Stage2NoEventWalkLink calls K mem s K s')
    (h' : Stage2NoEventWalkInv K' mem s') :
    Stage2NoEventWalkLink calls K mem s K' s' :=
  ⟨hl.inv, hl.step, h'⟩

/-! ### The reads at the marker's memory

The marker push writes one stack byte; the entry stream and the document are ABI
regions, so the entry at `k + 2` and its document byte read as they did
(`Inv.sep`'s two order facts).  This is
`stage2NoEventWalkBracketDescendReads` at the unpeeled address. -/

/-- **The dispatch's post-push reads**: the entry at `k + 2`, its lane, its
document byte. -/
theorem stage2NoEventWalkBracketMarkerReads {K : Stage2NoEventWalkCarry} {mem : Mem}
    {k : Nat} {s : State} {off : Nat}
    (h : Stage2NoEventWalkInv K mem s)
    {lane : Nat} {byte : UInt8}
    (hk2 : K.ent[k + 2]? = some lane) (hbs2 : K.bs[lane]? = some byte)
    (hoff : off < 520) :
    ∃ bs4 : List UInt8,
      readBytes (writeBytes s.mem (K.stk + off) stage2NoEventWalkBracketMarker)
        (K.ep + (BitVec.ofNat 64 (k + 2)).toNat * 4) 4 = some bs4 ∧
      bytesToNat bs4 = lane ∧ bytesToNat bs4 < 2 ^ 32 ∧
      readBytes (writeBytes s.mem (K.stk + off) stage2NoEventWalkBracketMarker)
        (K.b + (BitVec.signExtend 64 (BitVec.ofNat 64 (bytesToNat bs4))).toNat) 1
        = some [byte] := by
  have hlen : K.ent.length = K.nep :=
    readLanes32_length mem K.ep K.nep K.ent h.entries
  have hk2lt : k + 2 < K.nep := (List.getElem?_eq_some_iff.mp hk2).1.trans_eq hlen
  obtain ⟨-, hget⟩ := readLanes32_lane (m := s.mem) (addr := K.ep) (n := K.nep)
    (l := K.ent) h.entriesAt
  obtain ⟨q, bs4, hq, hread4, hval4q⟩ := hget (k + 2) hk2lt
  have hqlane : q = lane := by
    rw [hq] at hk2
    exact Option.some.inj hk2
  have hval4 : bytesToNat bs4 = lane := by rw [hval4q, hqlane]
  have hk2toNat : (BitVec.ofNat 64 (k + 2)).toNat = k + 2 := by
    rw [BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by have := h.nepLt; omega)
  have hmkLen : stage2NoEventWalkBracketMarker.length = 1 :=
    stage2NoEventWalkBracketMarker_length
  have hlaneW : readBytes (writeBytes s.mem (K.stk + off)
      stage2NoEventWalkBracketMarker)
      (K.ep + (BitVec.ofNat 64 (k + 2)).toNat * 4) 4 = some bs4 := by
    rw [hk2toNat,
      show K.ep + (k + 2) * 4 = K.ep + 4 * (k + 2) from by omega]
    refine (readBytes_writeBytes_frame s.mem stage2NoEventWalkBracketMarker
      (K.stk + off) (K.ep + 4 * (k + 2)) 4 ?_).trans hread4
    rcases h.stackEpOrder with hord | hord
    · right
      rw [hmkLen]
      omega
    · left; omega
  have hmaxDoc : K.n ≤ 2 ^ 32 := by
    have := h.maxDoc
    simpa [stage2MaxDocument] using this
  have hnextLt : lane < K.n := h.inside lane (List.mem_of_getElem? hk2)
  have hval4lt : bytesToNat bs4 < 2 ^ 32 := by
    rw [hval4]
    omega
  have hlane64 : (BitVec.signExtend 64 (BitVec.ofNat 64 (bytesToNat bs4))).toNat
      = lane := by
    rw [hval4, stage2NoEventSignExtend_ofNat (by omega : lane < 2 ^ 63)]
  have hbyte1W : readBytes (writeBytes s.mem (K.stk + off)
      stage2NoEventWalkBracketMarker)
      (K.b + (BitVec.signExtend 64 (BitVec.ofNat 64 (bytesToNat bs4))).toNat) 1
      = some [byte] := by
    rw [hlane64]
    have hgd : K.bs.getD lane 0 = byte := by
      rw [List.getD_eq_getElem?_getD, hbs2]; rfl
    have hreadDoc : readBytes s.mem (K.b + lane) 1 = some [byte] := by
      have hb := h.docByte hnextLt
      rw [hgd] at hb
      simp [readBytes, hb]
    refine (readBytes_writeBytes_frame s.mem stage2NoEventWalkBracketMarker
      (K.stk + off) (K.b + lane) 1 ?_).trans hreadDoc
    rcases h.stackDocOrder with hord | hord
    · right
      rw [hmkLen]
      omega
    · left; omega
  exact ⟨bs4, hlaneW, hval4, hval4lt, hbyte1W⟩

/-- **The popped marker**: the closer's pop read at the address the push wrote. -/
theorem stage2NoEventWalkBracketMarker_pop (mem : Mem) (a : Nat) :
    readBytes (writeBytes mem a stage2NoEventWalkBracketMarker) a 1
      = some stage2NoEventWalkBracketMarker := by
  have hmkLen : stage2NoEventWalkBracketMarker.length = 1 :=
    stage2NoEventWalkBracketMarker_length
  have hsing : ∃ b, stage2NoEventWalkBracketMarker = [b] := by
    match hm : stage2NoEventWalkBracketMarker with
    | [] => rw [hm] at hmkLen; simp at hmkLen
    | [b] => exact ⟨b, rfl⟩
    | b :: c :: rest => rw [hm] at hmkLen; simp at hmkLen
  obtain ⟨b, hb⟩ := hsing
  rw [hb, readBytes_one]
  have h := readByte_writeBytes_at mem [b] a 0 (by simp)
  simp only [Nat.add_zero] at h
  rw [h]
  rfl

/-! ### The window the dispatch does not carry

`Stage2NoEventWalkBracketDispatch` fixes the entry's class byte, its lane, the
index, the guard's index and the two counts.  The route from there needs six
more facts and none is a consequence of that struct: the invariant, the array
stack's two bound cells (the `if.then35` test and the marker's address), the
stack base, the consumed-count bound, the four-entry liveness, and the outer
opener's lane (the token the descend's `if.end` counted in the registers but left
out of the carry's trace). -/

/-- **The bracket inner route's window.** -/
structure Stage2NoEventWalkBracketInnerWindow (K : Stage2NoEventWalkCarry) (mem : Mem)
    (k : Nat) (s : State) (next : Nat) (nextByte : UInt8) : Type where
  /-- The continuation dispatch's own readings. -/
  disp : Stage2NoEventWalkBracketDispatch K k s next nextByte
  /-- The dispatch selected the `[` class. -/
  byte91 : nextByte.toNat = 91
  /-- The entry at `k + 1` is the opener. -/
  bs1 : K.bs[next]? = some nextByte
  /-- The invariant at the dispatch. -/
  inv : Stage2NoEventWalkInv K mem s
  /-- The outer opener at `k`, whose token and terms the descend's `if.end`
  already moved in the registers. -/
  outerLane : Nat
  outerByte : UInt8
  outerBs : K.bs[outerLane]? = some outerByte
  outerOpen : outerByte.toNat = 91
  /-- The array stack's cursor cell and its bound. -/
  ivIn : BitVec 64
  iv : BitVec 64
  cnt : BitVec 64
  hIVIn : lookupName s.env "%indvars.iv.in" = some (.int 64 ivIn)
  hIV : lookupName s.env "%indvars.iv" = some (.int 64 iv)
  hCnt : lookupName s.env "%wide.trip.count1409" = some (.int 64 cnt)
  ivInLt : (ivIn.signExtend 64).toNat < 520
  ivVal : iv.toNat = (ivIn.signExtend 64).toNat + 1
  ivNe : iv ≠ cnt
  /-- The stack's base. -/
  hStk : lookupName s.env "%stk" = some (.ptr K.stk)
  /-- The head's arena-length and arena-word `phi`s, carried through the descend. -/
  alenPhi : lookupName s.env "%alen.0.ph1405" =
    some (.int 64 (BitVec.ofNat 64 K.arena.length))
  arenaPhi : lookupName s.env "%arena.0.ph1406" =
    some (.int 64 (BitVec.ofNat 64 K.arenaWord))
  /-- The consumed-count bound at the head's index. -/
  count : Stage2NoEventWalkCount K k
  /-- The four-entry advance's room: the closer reads `k + 2`, and the cycle
  returns at `k + 4`. -/
  live : k + 4 < K.nep
  /-- The report's base. -/
  bPos : 1 ≤ K.b
  /-- The trace at the dispatch's carry. -/
  trace : Stage2NoEventWalkTrace K

/-! ### The first half: the dispatch's `[` leaf to the `]` read

Five blocks — the three-block dispatch's `[` leaf, `if.then35`'s bound test, the
marker push — to `if.end327`'s entry, with the reads' memory and the two arms'
lookups. -/

/-- **The bracket inner route's first half**, at `if.end327`'s entry. -/
structure Stage2NoEventWalkBracketInnerAt327 (calls : Calls) (K : Stage2NoEventWalkCarry)
    (mem : Mem) (k : Nat) (s : State) : Type where
  s5 : State
  /-- The five-link run to the entry. -/
  seg : Stage2NoEventWalkSegment calls mem K s K s5 5
  inv : Stage2NoEventWalkInv K mem s5
  pc : s5.pc = "if.end327"
  pre : s5.pre = some "if.end51"
  /-- The marker's address inside the stack. -/
  off : Nat
  hOff : off < 520
  mem_eq : s5.mem = writeBytes s.mem (K.stk + off) stage2NoEventWalkBracketMarker
  iv : BitVec 64
  /-- The stack cursor the push addressed, and its relation to the bound test's
  cell. -/
  ivIn : BitVec 64
  ivVal : iv.toNat = (ivIn.signExtend 64).toNat + 1
  off_eq : off = (ivIn.signExtend 64).toNat
  hIV : lookupName s5.env "%indvars.iv" = some (.int 64 iv)
  hInc : lookupName s5.env "%inc" = some (.int 64 (BitVec.ofNat 64 (k + 2)))
  hEp : lookupName s5.env "%ep" = some (.ptr K.ep)
  hB : lookupName s5.env "%b" = some (.ptr K.b)
  hK0 : lookupName s5.env "%k.0" = some (.int 64 (BitVec.ofNat 64 (k + 1)))
  hTok : lookupName s5.env "%tokens.0" =
    some (.int 64 (BitVec.ofNat 64 (K.tok + 1)))
  hTerms : lookupName s5.env "%terms.0" =
    some (.int 64 (BitVec.ofNat 64 (K.terms + 3)))
  /-- The entry chain's stable live-ins at the push's memory. -/
  base : Stage2NoEventWalkBaseLookups K s5
  alenPhi : lookupName s5.env "%alen.0.ph1405" =
    some (.int 64 (BitVec.ofNat 64 K.arena.length))
  arenaPhi : lookupName s5.env "%arena.0.ph1406" =
    some (.int 64 (BitVec.ofNat 64 K.arenaWord))

/-- **The dispatch's `[` leaf through the marker push**, at `if.end327`'s entry. -/
noncomputable def stage2NoEventWalkBracketInnerTo327 {calls : Calls}
    {K : Stage2NoEventWalkCarry} {mem : Mem} {k : Nat} {s : State}
    {next : Nat} {nextByte : UInt8}
    (W : Stage2NoEventWalkBracketInnerWindow K mem k s next nextByte) :
    Stage2NoEventWalkBracketInnerAt327 calls K mem k s := by
  classical
  obtain ⟨disp, byte91, bs1, inv, oLane, oByte, oBs, oOpen, ivIn, iv,
    cnt, hIVIn, hIV, hCnt, ivInLt, ivVal, ivNe, hStk, alenPhi, arenaPhi, count, live,
    bPos, trace⟩ := W
  let off : Nat := (ivIn.signExtend 64).toNat
  let S1 := stage2NoEventWalkNext (("%Pivot16", .int 1 0) :: s.env) s "NodeBlock13"
  let S2 := stage2NoEventWalkNext (("%Pivot14", .int 1 1) :: S1.env) S1 "LeafBlock9"
  let S3 := stage2NoEventWalkNext (("%SwitchLeaf10", .int 1 1) :: S2.env) S2 "if.then35"
  let S4 := stage2NoEventWalkNext (("%exitcond", .int 1 0) :: S3.env) S3 "if.end51"
  let S5 := stage2NoEventWalkStored
    (("%cmp319.not", .int 1 1) :: ("%arrayidx50", .ptr (K.stk + off)) :: S4.env)
    S4 (writeBytes s.mem (K.stk + off) stage2NoEventWalkBracketMarker) "if.end327"
  have h7 : lookupName s.env "%7" = some (.int 8 (BitVec.ofNat 8 nextByte.toNat)) :=
    disp.byte
  have hy91 : (BitVec.ofNat 8 nextByte.toNat) = BitVec.ofNat 8 91 := by rw [byte91]
  have L1 : Stage2NoEventWalkLink calls K mem s K S1 :=
    link_nodeBlock15_false inv disp.pc h7 (by rw [hy91]; decide)
  have h7₁ : lookupName S1.env "%7" =
      some (.int 8 (BitVec.ofNat 8 nextByte.toNat)) :=
    lookupName_cons_other _ _ _ (by decide) h7
  have L2 : Stage2NoEventWalkLink calls K mem S1 K S2 :=
    link_nodeBlock13_true L1.inv' rfl h7₁ (by rw [hy91]; decide)
  have h7₂ : lookupName S2.env "%7" =
      some (.int 8 (BitVec.ofNat 8 nextByte.toNat)) :=
    lookupName_cons_other _ _ _ (by decide) h7₁
  have L3 : Stage2NoEventWalkLink calls K mem S2 K S3 :=
    link_leafBlock9_true L2.inv' rfl h7₂ (by rw [hy91]; decide)
  have hiv3 : lookupName S3.env "%indvars.iv" = some (.int 64 iv) := by
    simp only [S3, S2, S1, stage2NoEventWalkNext]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact hIV
  have hcnt3 : lookupName S3.env "%wide.trip.count1409" = some (.int 64 cnt) := by
    simp only [S3, S2, S1, stage2NoEventWalkNext]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact hCnt
  have hne : evalICmp .eq iv cnt = (0 : BitVec 1) := by
    simp [evalICmp, ivNe]
  have L4 : Stage2NoEventWalkLink calls K mem S3 K S4 :=
    link_ifThen35_false L3.inv' rfl hiv3 hcnt3 hne
  have hIVIn4 : lookupName S4.env "%indvars.iv.in" = some (.int 64 ivIn) := by
    simp only [S4, S3, S2, S1, stage2NoEventWalkNext]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact hIVIn
  have hStk4 : lookupName S4.env "%stk" = some (.ptr K.stk) := by
    simp only [S4, S3, S2, S1, stage2NoEventWalkNext]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact hStk
  have hInc4 : lookupName S4.env "%inc" =
      some (.int 64 (BitVec.ofNat 64 (k + 2))) := by
    simp only [S4, S3, S2, S1, stage2NoEventWalkNext]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact disp.inc
  have hNep4 : lookupName S4.env "%nep" = some (.int 64 (BitVec.ofNat 64 K.nep)) := by
    simp only [S4, S3, S2, S1, stage2NoEventWalkNext]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact disp.baseLookups "%nep" _ (by
      simp only [stage2NoEventWalkBaseValues, stage2NoEventWalkParamEntries]
      exact List.mem_append_left _ (by simp))
  have hk2nep : k + 2 < K.nep := by omega
  have hult : BitVec.ult (BitVec.ofNat 64 (k + 2)) (BitVec.ofNat 64 K.nep) = true := by
    refine BitVec.ult_iff_toNat_lt.2 ?_
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by have := inv.nepLt; omega),
      Nat.mod_eq_of_lt inv.nepLt]
    omega
  have L5 : Stage2NoEventWalkLink calls K mem S4 K S5 :=
    link_ifEnd51 L4.inv' rfl hIVIn4 hStk4 hInc4 hNep4
      (by omega) rfl rfl (by omega) hult
  have hrun : ∀ n, runFuel calls (5 + n) stage2NoEventBody s =
      runFuel calls n stage2NoEventBody S5 := by
    intro n
    rw [show 5 + n = 1 + (1 + (1 + (1 + (1 + n)))) from by omega]
    rw [stage2NoEventWalkLink_runFuel L1, stage2NoEventWalkLink_runFuel L2,
      stage2NoEventWalkLink_runFuel L3, stage2NoEventWalkLink_runFuel L4,
      stage2NoEventWalkLink_runFuel L5]
  have hInc5 : lookupName S5.env "%inc" =
      some (.int 64 (BitVec.ofNat 64 (k + 2))) := by
    simp only [S5, S4, S3, S2, S1, stage2NoEventWalkNext, stage2NoEventWalkStored]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact disp.inc
  have hEp5 : lookupName S5.env "%ep" = some (.ptr K.ep) := by
    simp only [S5, S4, S3, S2, S1, stage2NoEventWalkNext, stage2NoEventWalkStored]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact disp.baseLookups "%ep" _ (by
      simp only [stage2NoEventWalkBaseValues, stage2NoEventWalkParamEntries]
      exact List.mem_append_left _ (by simp))
  have hB5 : lookupName S5.env "%b" = some (.ptr K.b) := by
    simp only [S5, S4, S3, S2, S1, stage2NoEventWalkNext, stage2NoEventWalkStored]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact disp.baseLookups "%b" _ (by
      simp only [stage2NoEventWalkBaseValues, stage2NoEventWalkParamEntries]
      exact List.mem_append_left _ (by simp))
  have hIV5 : lookupName S5.env "%indvars.iv" = some (.int 64 iv) := by
    simp only [S5, S4, S3, S2, S1, stage2NoEventWalkNext, stage2NoEventWalkStored]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact hIV
  have hK05 : lookupName S5.env "%k.0" = some (.int 64 (BitVec.ofNat 64 (k + 1))) := by
    simp only [S5, S4, S3, S2, S1, stage2NoEventWalkNext, stage2NoEventWalkStored]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact disp.index
  have hTok5 : lookupName S5.env "%tokens.0" =
      some (.int 64 (BitVec.ofNat 64 (K.tok + 1))) := by
    simp only [S5, S4, S3, S2, S1, stage2NoEventWalkNext, stage2NoEventWalkStored]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact disp.tokens
  have hTerms5 : lookupName S5.env "%terms.0" =
      some (.int 64 (BitVec.ofNat 64 (K.terms + 3))) := by
    simp only [S5, S4, S3, S2, S1, stage2NoEventWalkNext, stage2NoEventWalkStored]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact disp.terms
  have hAlen5 : lookupName S5.env "%alen.0.ph1405" =
      some (.int 64 (BitVec.ofNat 64 K.arena.length)) := by
    simp only [S5, S4, S3, S2, S1, stage2NoEventWalkNext, stage2NoEventWalkStored]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact alenPhi
  have hArena5 : lookupName S5.env "%arena.0.ph1406" =
      some (.int 64 (BitVec.ofNat 64 K.arenaWord)) := by
    simp only [S5, S4, S3, S2, S1, stage2NoEventWalkNext, stage2NoEventWalkStored]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact arenaPhi
  have hbase : Stage2NoEventWalkBaseLookups K S5 := by
    have b0 : ∀ n v, (n, v) ∈ stage2NoEventWalkBaseValues K →
        lookupName s.env n = some v := disp.baseLookups
    have b1 := stage2NoEventCycleBase (K := K) (env := s.env) b0
      (cs := [("%Pivot16", .int 1 0)]) (names := ["%Pivot16"]) rfl (by decide)
    have b2 := stage2NoEventCycleBase (K := K) b1
      (cs := [("%Pivot14", .int 1 1)]) (names := ["%Pivot14"]) rfl (by decide)
    have b3 := stage2NoEventCycleBase (K := K) b2
      (cs := [("%SwitchLeaf10", .int 1 1)]) (names := ["%SwitchLeaf10"]) rfl
      (by decide)
    have b4 := stage2NoEventCycleBase (K := K) b3
      (cs := [("%exitcond", .int 1 0)]) (names := ["%exitcond"]) rfl (by decide)
    have b5 := stage2NoEventCycleBase (K := K) b4
      (cs := [("%cmp319.not", .int 1 1),
        ("%arrayidx50", .ptr (K.stk + off))])
      (names := ["%cmp319.not", "%arrayidx50"]) rfl (by decide)
    exact b5
  exact
    { s5 := S5
      seg := ⟨hrun, L5.inv'⟩
      inv := L5.inv'
      pc := rfl
      pre := rfl
      off := off
      hOff := ivInLt
      mem_eq := rfl
      iv := iv
      ivIn := ivIn
      ivVal := ivVal
      off_eq := rfl
      hIV := hIV5
      hInc := hInc5
      hEp := hEp5
      hB := hB5
      hK0 := hK05
      hTok := hTok5
      hTerms := hTerms5
      base := hbase
      alenPhi := hAlen5
      arenaPhi := hArena5 }

/-! ### The closer arm: the `]` read to `after_value`

Five more blocks from `if.end327`'s entry: the `]` read, `if.then334.loopexit`'s
truncation, `if.then334`'s four `phi`s and three counts, `close_arr`'s seven
`phi`s and depth test, and `if.then350`'s pop read.  Ten blocks in all, to
`after_value` at index `k + 3`, with the class's `Stage2NoEventWalkCycleSrc`. -/

/-- **The bracket inner closer arm**: the entry at `k + 2` is `]`, so the walk
closes the nested array and reaches `after_value`'s entry at `k + 3` in ten
blocks, at the carry `{K with tok := K.tok + 3, terms := K.terms + 10}`. -/
theorem stage2NoEventWalkBracketInnerCloser {calls : Calls}
    {K : Stage2NoEventWalkCarry} {mem : Mem} {k : Nat} {s : State}
    {next : Nat} {nextByte : UInt8}
    (W : Stage2NoEventWalkBracketInnerWindow K mem k s next nextByte)
    {lane2 : Nat} {byte2 : UInt8}
    (hk2 : K.ent[k + 2]? = some lane2) (hbs2 : K.bs[lane2]? = some byte2)
    (hb2 : byte2.toNat = 93)
    (hcomma : ∀ q, K.ent[k + 3]? = some q → K.bs.getD q 0 = 44) :
    ∃ (sE : State) (Kc : Stage2NoEventWalkCarry),
      Kc = { K with tok := K.tok + 3, terms := K.terms + 10 } ∧
      Stage2NoEventWalkSegment calls mem K s Kc sE 10 ∧
      Nonempty (Stage2NoEventWalkCycleSrc calls mem Kc (k + 3) sE) := by
  classical
  let A := stage2NoEventWalkBracketInnerTo327 (calls := calls) W
  obtain ⟨disp, byte91, bs1, inv, oLane, oByte, oBs, oOpen, ivIn, iv,
    cnt, hIVIn, hIV, hCnt, ivInLt, ivVal, ivNe, hStk, alenPhi, arenaPhi, count, live,
    bPos, trace⟩ := W
  -- the reads at the marker's memory
  obtain ⟨bs4, hlane, hval4, hval4lt, hbyte⟩ :=
    stage2NoEventWalkBracketMarkerReads (K := K) (off := A.off) inv hk2 hbs2 A.hOff
  -- the closer's values
  let sp48 : BitVec 32 := BitVec.ofNat 32 (iv.toNat % 2 ^ 32)
  let K1 : Stage2NoEventWalkCarry := { K with tok := K.tok + 1, terms := K.terms + 3 }
  let Kc : Stage2NoEventWalkCarry := { K1 with tok := K1.tok + 2, terms := K1.terms + 7 }
  let a : Nat := closeReadAddr K.stk (sp48 + BitVec.ofNat 32 4294967295).toNat
  let S6 := stage2NoEventWalkNext
    (("%cmp332", .int 1 1) ::
      ("%47", .int 8 (BitVec.ofNat 8 (bytesToNat [byte2]))) ::
      ("%arrayidx330",
        .ptr (K.b + (BitVec.signExtend 64
          (BitVec.ofNat 64 (bytesToNat bs4))).toNat)) ::
      ("%idxprom329", .int 64 (BitVec.ofNat 64 (bytesToNat bs4))) ::
      ("%46", .int 32 (BitVec.ofNat 32 (bytesToNat bs4))) ::
      ("%arrayidx328", .ptr (K.ep + (BitVec.ofNat 64 (k + 2)).toNat * 4)) ::
      A.s5.env) A.s5 "if.then334.loopexit"
  let S7 := stage2NoEventWalkNext
    (("%48", .int 32 (BitVec.ofNat 32 (iv.toNat % 2 ^ 32))) :: S6.env)
    S6 "if.then334"
  let S8 := bracketCounts S7 sp48 (BitVec.ofNat 64 (k + 1))
    (BitVec.ofNat 64 (K.tok + 1)) (BitVec.ofNat 64 (K.terms + 3))
  let S9 := bracketArr S8 sp48 (BitVec.ofNat 64 (k + 3))
    (BitVec.ofNat 64 K.arena.length) (BitVec.ofNat 64 K.arenaWord)
    (BitVec.ofNat 64 (K.terms + 10)) (BitVec.ofNat 64 (K.tok + 3))
  let S10 := bracketRead S9 sp48 a stage2NoEventWalkBracketMarker
  have hk2nep : k + 2 < K.nep := by omega
  have hb93 : byte2 = (0x5D : UInt8) :=
    stage2NoEventWalk_uint8_eq_of_toNat (by rw [hb2]; decide)
  have hbSlide : bytesToNat [byte2] = byte2.toNat :=
    stage2NoEventWalkBytesToNat_single byte2
  have hbit : evalICmp .eq (BitVec.ofNat 8 (bytesToNat [byte2])) (BitVec.ofNat 8 93) = 1 := by
    rw [hbSlide, hb2]
    decide
  have hmaxDoc : K.n ≤ 2 ^ 32 := by
    have := inv.maxDoc
    simpa [stage2MaxDocument] using this
  have hneLe := inv.nepLe
  have hincLt : (BitVec.ofNat 64 (k + 2)).toNat < 2 ^ 63 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := inv.nepLt; omega)]
    omega
  have hmem6 : A.s5.mem = writeBytes s.mem (K.stk + A.off)
      stage2NoEventWalkBracketMarker := A.mem_eq
  have L6 : Stage2NoEventWalkLink calls K mem A.s5 K S6 :=
    link_ifEnd327_true A.inv A.pc A.hInc A.hEp A.hB hincLt
      (by rw [hmem6]; exact hlane)
      hval4lt
      (by rw [hmem6]; exact hbyte) hbit
  -- the carry reindex: the descend's `if.end` counted the outer opener
  have htok1 : K.tok + 1 ≤ K.n := by
    have hcnt : K.tok ≤ k := count
    have hne := inv.nepLe
    omega
  have hK1inv : Stage2NoEventWalkInv K1 mem S6 :=
    Stage2NoEventWalkInv.count (K := K) L6.inv' (t := 1) (c := 3) htok1
  have L6r : Stage2NoEventWalkLink calls K mem A.s5 K1 S6 :=
    Stage2NoEventWalkLink.reindex L6 hK1inv
  -- `if.then334.loopexit`: the truncation
  have hIV6 : lookupName S6.env "%indvars.iv" = some (.int 64 iv) := by
    simp only [S6, stage2NoEventWalkNext]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact A.hIV
  have L7 : Stage2NoEventWalkLink calls K1 mem S6 K1 S7 :=
    link_ifThen334Loopexit L6r.inv' rfl hIV6
  have h48 : lookupName S7.env "%48" =
      some (.int 32 (BitVec.ofNat 32 (iv.toNat % 2 ^ 32))) := by
    simp only [S7, stage2NoEventWalkNext]
    exact lookupName_cons_self _ _ _
  have hK07 : lookupName S7.env "%k.0" =
      some (.int 64 (BitVec.ofNat 64 (k + 1))) := by
    simp only [S7, stage2NoEventWalkNext]
    rw [lookupName_cons_ne _ _ (by decide)]
    exact A.hK0
  have hTok7 : lookupName S7.env "%tokens.0" =
      some (.int 64 (BitVec.ofNat 64 (K.tok + 1))) := by
    simp only [S7, stage2NoEventWalkNext]
    rw [lookupName_cons_ne _ _ (by decide)]
    exact A.hTok
  have hTerms7 : lookupName S7.env "%terms.0" =
      some (.int 64 (BitVec.ofNat 64 (K.terms + 3))) := by
    simp only [S7, stage2NoEventWalkNext]
    rw [lookupName_cons_ne _ _ (by decide)]
    exact A.hTerms
  have htokKc : K1.tok + 2 ≤ K1.n := by
    have hcnt : K.tok ≤ k := count
    have hne := inv.nepLe
    show K.tok + 1 + 2 ≤ K.n
    omega
  have L8 : Stage2NoEventWalkLink calls K1 mem S7 Kc S8 :=
    link_ifThen334LoopexitEdge L7.inv' rfl rfl h48 hK07 hTerms7 hTok7 htokKc
  -- the four `phi` counts, normalised
  have hsp8 : lookupName S8.env "%sp.0.lcssa1096.wide" = some (.int 32 sp48) := by
    simp only [S8, bracketCounts, stage2NoEventWalkNext]
    exact stage2NoEventWalkCells_some (cs := ifThen334AllCells sp48
      (BitVec.ofNat 64 (k + 1)) (BitVec.ofNat 64 (K.tok + 1))
      (BitVec.ofNat 64 (K.terms + 3)))
      (n := "%sp.0.lcssa1096.wide") (v := .int 32 sp48)
      (by simp only [ifThen334AllCells, ifThen334Cells, ifThen334PhiCells,
        List.mem_append, List.mem_cons, List.not_mem_nil, or_false]; tauto)
      (by simp only [ifThen334AllCells, ifThen334Cells, ifThen334PhiCells,
        List.map_append, List.map_cons, List.map_nil]; decide)
  have hinc335 : lookupName S8.env "%inc335" =
      some (.int 64 (BitVec.ofNat 64 (k + 3))) := by
    have hc : lookupName S8.env "%inc335" = some (.int 64
        (BitVec.ofNat 64 (k + 1) + BitVec.ofNat 64 2)) := by
      simp only [S8, bracketCounts, stage2NoEventWalkNext]
      exact stage2NoEventWalkCells_some (cs := ifThen334AllCells sp48
        (BitVec.ofNat 64 (k + 1)) (BitVec.ofNat 64 (K.tok + 1))
        (BitVec.ofNat 64 (K.terms + 3)))
        (n := "%inc335") (v := .int 64 (BitVec.ofNat 64 (k + 1) + BitVec.ofNat 64 2))
        (by simp only [ifThen334AllCells, ifThen334Cells, ifThen334PhiCells,
          List.mem_append, List.mem_cons, List.not_mem_nil, or_false]; tauto)
        (by simp only [ifThen334AllCells, ifThen334Cells, ifThen334PhiCells,
          List.map_append, List.map_cons, List.map_nil]; decide)
    simpa only [stage2NoEventWalkOfNat_add] using hc
  have hterms8 : lookupName S8.env "%add338" =
      some (.int 64 (BitVec.ofNat 64 (K.terms + 10))) := by
    have hc : lookupName S8.env "%add338" = some (.int 64
        (BitVec.ofNat 64 (K.terms + 3) + BitVec.ofNat 64 7)) := by
      simp only [S8, bracketCounts, stage2NoEventWalkNext]
      exact stage2NoEventWalkCells_some (cs := ifThen334AllCells sp48
        (BitVec.ofNat 64 (k + 1)) (BitVec.ofNat 64 (K.tok + 1))
        (BitVec.ofNat 64 (K.terms + 3)))
        (n := "%add338") (v := .int 64
          (BitVec.ofNat 64 (K.terms + 3) + BitVec.ofNat 64 7))
        (by simp only [ifThen334AllCells, ifThen334Cells, ifThen334PhiCells,
          List.mem_append, List.mem_cons, List.not_mem_nil, or_false]; tauto)
        (by simp only [ifThen334AllCells, ifThen334Cells, ifThen334PhiCells,
          List.map_append, List.map_cons, List.map_nil]; decide)
    simpa only [stage2NoEventWalkOfNat_add] using hc
  have htoks8 : lookupName S8.env "%inc337" =
      some (.int 64 (BitVec.ofNat 64 (K.tok + 3))) := by
    have hc : lookupName S8.env "%inc337" = some (.int 64
        (BitVec.ofNat 64 (K.tok + 1) + BitVec.ofNat 64 2)) := by
      simp only [S8, bracketCounts, stage2NoEventWalkNext]
      exact stage2NoEventWalkCells_some (cs := ifThen334AllCells sp48
        (BitVec.ofNat 64 (k + 1)) (BitVec.ofNat 64 (K.tok + 1))
        (BitVec.ofNat 64 (K.terms + 3)))
        (n := "%inc337") (v := .int 64
          (BitVec.ofNat 64 (K.tok + 1) + BitVec.ofNat 64 2))
        (by simp only [ifThen334AllCells, ifThen334Cells, ifThen334PhiCells,
          List.mem_append, List.mem_cons, List.not_mem_nil, or_false]; tauto)
        (by simp only [ifThen334AllCells, ifThen334Cells, ifThen334PhiCells,
          List.map_append, List.map_cons, List.map_nil]; decide)
    simpa only [stage2NoEventWalkOfNat_add] using hc
  have halen8 : lookupName S8.env "%alen.0.ph1405" =
      some (.int 64 (BitVec.ofNat 64 K.arena.length)) := by
    simp only [S8, bracketCounts, stage2NoEventWalkNext]
    rw [stage2NoEventWalkCells_notin (cs := ifThen334AllCells sp48
      (BitVec.ofNat 64 (k + 1)) (BitVec.ofNat 64 (K.tok + 1))
      (BitVec.ofNat 64 (K.terms + 3))) (n := "%alen.0.ph1405") (env := S7.env)
      (by rw [ifThen334AllCells, ifThen334Cells, ifThen334PhiCells]; simp)]
    simp only [S7, S6, stage2NoEventWalkNext]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact A.alenPhi
  have harena8 : lookupName S8.env "%arena.0.ph1406" =
      some (.int 64 (BitVec.ofNat 64 K.arenaWord)) := by
    simp only [S8, bracketCounts, stage2NoEventWalkNext]
    rw [stage2NoEventWalkCells_notin (cs := ifThen334AllCells sp48
      (BitVec.ofNat 64 (k + 1)) (BitVec.ofNat 64 (K.tok + 1))
      (BitVec.ofNat 64 (K.terms + 3))) (n := "%arena.0.ph1406") (env := S7.env)
      (by rw [ifThen334AllCells, ifThen334Cells, ifThen334PhiCells]; simp)]
    simp only [S7, S6, stage2NoEventWalkNext]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact A.arenaPhi
  have hivMax : iv.toNat < 2 ^ 32 := by rw [ivVal]; omega
  have hsp48val : sp48.toNat = iv.toNat := by
    simp only [sp48, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (Nat.mod_lt _ (by decide : 0 < 2 ^ 32)),
      Nat.mod_eq_of_lt hivMax]
  have hsp1 : 1 ≤ sp48.toNat := by rw [hsp48val, ivVal]; omega
  have hspNe : sp48.toNat ≠ 0 := by omega
  have hspLt : sp48.toNat < 2 ^ 32 := sp48.isLt
  have hpop : readBytes A.s5.mem
      (closeReadAddr K.stk (sp48 + BitVec.ofNat 32 4294967295).toNat) 1
      = some stage2NoEventWalkBracketMarker := by
    have haddr : closeReadAddr K.stk (sp48 + BitVec.ofNat 32 4294967295).toNat
        = K.stk + A.off := by
      simp only [closeReadAddr]
      rw [stage2NoEventSub32_one hsp1]
      have hIVv : iv.toNat = (A.ivIn.signExtend 64).toNat + 1 := A.ivVal
      have hOff : A.off = (A.ivIn.signExtend 64).toNat := A.off_eq
      have : sp48.toNat - 1 = A.off := by omega
      rw [this]
    rw [haddr]
    simpa only [A.mem_eq] using
      stage2NoEventWalkBracketMarker_pop s.mem (K.stk + A.off)
  have L9 : Stage2NoEventWalkLink calls Kc mem S8 Kc S9 :=
    link_closeArr (K := Kc) L8.inv' rfl rfl hsp8 hinc335 halen8 harena8 hterms8 htoks8 hspNe
  have hstk9 : lookupName S9.env "%stk" = some (.ptr K.stk) := by
    simp only [S9, bracketArr, stage2NoEventWalkNext]
    rw [stage2NoEventWalkCells_notin (cs := closeArrAllCells sp48
      (BitVec.ofNat 64 (k + 3)) (BitVec.ofNat 64 K.arena.length)
      (BitVec.ofNat 64 K.arenaWord) (BitVec.ofNat 64 (K.terms + 10))
      (BitVec.ofNat 64 (K.tok + 3))) (n := "%stk") (env := S8.env)
      (by rw [closeArrAllCells, closeArrTail, closeArrPhiCells]; simp)]
    simp only [S8, bracketCounts, stage2NoEventWalkNext]
    rw [stage2NoEventWalkCells_notin (cs := ifThen334AllCells sp48
      (BitVec.ofNat 64 (k + 1)) (BitVec.ofNat 64 (K.tok + 1))
      (BitVec.ofNat 64 (K.terms + 3))) (n := "%stk") (env := S7.env)
      (by rw [ifThen334AllCells, ifThen334Cells, ifThen334PhiCells]; simp)]
    simp only [S7, S6, stage2NoEventWalkNext]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact A.base "%stk" _ (by
      simp only [stage2NoEventWalkBaseValues, stage2NoEventWalkParamEntries]
      exact List.mem_append_left _ (by simp))
  have hsp9 : lookupName S9.env "%sp.3" = some (.int 32 sp48) := by
    simp only [S9, bracketArr, stage2NoEventWalkNext]
    exact stage2NoEventWalkCells_some (cs := closeArrAllCells sp48
      (BitVec.ofNat 64 (k + 3)) (BitVec.ofNat 64 K.arena.length)
      (BitVec.ofNat 64 K.arenaWord) (BitVec.ofNat 64 (K.terms + 10))
      (BitVec.ofNat 64 (K.tok + 3)))
      (n := "%sp.3") (v := .int 32 sp48)
      (by simp only [closeArrAllCells, closeArrTail, closeArrPhiCells,
        List.mem_append, List.mem_cons, List.not_mem_nil, or_false]; tauto)
      (by simp only [closeArrAllCells, closeArrTail, closeArrPhiCells,
        List.map_append, List.map_cons, List.map_nil]; decide)
  have L10 : Stage2NoEventWalkLink calls Kc mem S9 Kc S10 :=
    link_ifThen350 (K := Kc) (s := S9) (stk := K.stk) (sp3 := sp48)
      (a := closeReadAddr K.stk (sp48 + BitVec.ofNat 32 4294967295).toNat)
      (bs := stage2NoEventWalkBracketMarker) L9.inv' rfl hsp9 hstk9 hpop rfl
  -- the ten-block run
  have hrun : ∀ n, runFuel calls (10 + n) stage2NoEventBody s =
      runFuel calls n stage2NoEventBody S10 := by
    intro n
    rw [show 10 + n = 5 + (1 + (1 + (1 + (1 + (1 + n))))) from by omega,
      A.seg.run (1 + (1 + (1 + (1 + (1 + n))))),
      stage2NoEventWalkLink_runFuel L6r, stage2NoEventWalkLink_runFuel L7,
      stage2NoEventWalkLink_runFuel L8, stage2NoEventWalkLink_runFuel L9,
      stage2NoEventWalkLink_runFuel L10]
  have hseg : Stage2NoEventWalkSegment calls mem K s Kc S10 10 := ⟨hrun, L10.inv'⟩
  refine ⟨S10, Kc, rfl, hseg, ⟨?_⟩⟩
  -- the endpoint bundle
  have hKctok : Kc.tok = K.tok + 3 := rfl
  have hnd50 : ((("%50", .int 8 (BitVec.ofNat 8 (bytesToNat stage2NoEventWalkBracketMarker))) ::
      closeGepCells50 a ++ closeIdxCells50 (sp48 + BitVec.ofNat 32 4294967295)).map (·.1)).Nodup := by
    simp only [closeGepCells50, closeIdxCells50, List.map_append, List.map_cons,
      List.map_nil]
    decide
  have h50 : lookupName S10.env "%50" = some (.int 8 (BitVec.ofNat 8 1)) := by
    simp only [S10, bracketRead, stage2NoEventWalkNext,
      stage2NoEventWalkBracketMarker_val]
    exact stage2NoEventWalkCells_some (cs :=
      ("%50", .int 8 (BitVec.ofNat 8 (bytesToNat stage2NoEventWalkBracketMarker))) ::
        closeGepCells50 a ++ closeIdxCells50 (sp48 + BitVec.ofNat 32 4294967295))
      (n := "%50") (v := .int 8 (BitVec.ofNat 8 1))
      (List.mem_cons.mpr (Or.inl rfl)) hnd50
  have hsp10 : lookupName S10.env "%sp.3" = some (.int 32 sp48) := by
    simp only [S10, bracketRead, stage2NoEventWalkNext]
    rw [stage2NoEventWalkCells_notin (cs :=
      ("%50", .int 8 (BitVec.ofNat 8 (bytesToNat stage2NoEventWalkBracketMarker))) ::
        closeGepCells50 a ++ closeIdxCells50 (sp48 + BitVec.ofNat 32 4294967295))
      (n := "%sp.3") (env := S9.env)
      (by simp only [closeGepCells50, closeIdxCells50, List.map_append,
        List.map_cons, List.map_nil]; decide)]
    exact hsp9
  have hk10 : lookupName S10.env "%k.5" = some (.int 64 (BitVec.ofNat 64 (k + 3))) := by
    simp only [S10, bracketRead, stage2NoEventWalkNext]
    rw [stage2NoEventWalkCells_notin (cs :=
      ("%50", .int 8 (BitVec.ofNat 8 (bytesToNat stage2NoEventWalkBracketMarker))) ::
        closeGepCells50 a ++ closeIdxCells50 (sp48 + BitVec.ofNat 32 4294967295))
      (n := "%k.5") (env := S9.env)
      (by simp only [closeGepCells50, closeIdxCells50, List.map_append,
        List.map_cons, List.map_nil]; decide)]
    simp only [S9, bracketArr, stage2NoEventWalkNext]
    exact stage2NoEventWalkCells_some (cs := closeArrAllCells sp48
      (BitVec.ofNat 64 (k + 3)) (BitVec.ofNat 64 K.arena.length)
      (BitVec.ofNat 64 K.arenaWord) (BitVec.ofNat 64 (K.terms + 10))
      (BitVec.ofNat 64 (K.tok + 3)))
      (n := "%k.5") (v := .int 64 (BitVec.ofNat 64 (k + 3)))
      (by simp only [closeArrAllCells, closeArrTail, closeArrPhiCells,
        List.mem_append, List.mem_cons, List.not_mem_nil, or_false]; tauto)
      (by simp only [closeArrAllCells, closeArrTail, closeArrPhiCells,
        List.map_append, List.map_cons, List.map_nil]; decide)
  have halen10 : lookupName S10.env "%alen.7" =
      some (.int 64 (BitVec.ofNat 64 K.arena.length)) := by
    simp only [S10, bracketRead, stage2NoEventWalkNext]
    rw [stage2NoEventWalkCells_notin (cs :=
      ("%50", .int 8 (BitVec.ofNat 8 (bytesToNat stage2NoEventWalkBracketMarker))) ::
        closeGepCells50 a ++ closeIdxCells50 (sp48 + BitVec.ofNat 32 4294967295))
      (n := "%alen.7") (env := S9.env)
      (by simp only [closeGepCells50, closeIdxCells50, List.map_append,
        List.map_cons, List.map_nil]; decide)]
    simp only [S9, bracketArr, stage2NoEventWalkNext]
    exact stage2NoEventWalkCells_some (cs := closeArrAllCells sp48
      (BitVec.ofNat 64 (k + 3)) (BitVec.ofNat 64 K.arena.length)
      (BitVec.ofNat 64 K.arenaWord) (BitVec.ofNat 64 (K.terms + 10))
      (BitVec.ofNat 64 (K.tok + 3)))
      (n := "%alen.7") (v := .int 64 (BitVec.ofNat 64 K.arena.length))
      (by simp only [closeArrAllCells, closeArrTail, closeArrPhiCells,
        List.mem_append, List.mem_cons, List.not_mem_nil, or_false]; tauto)
      (by simp only [closeArrAllCells, closeArrTail, closeArrPhiCells,
        List.map_append, List.map_cons, List.map_nil]; decide)
  have harena10 : lookupName S10.env "%arena.9" =
      some (.int 64 (BitVec.ofNat 64 K.arenaWord)) := by
    simp only [S10, bracketRead, stage2NoEventWalkNext]
    rw [stage2NoEventWalkCells_notin (cs :=
      ("%50", .int 8 (BitVec.ofNat 8 (bytesToNat stage2NoEventWalkBracketMarker))) ::
        closeGepCells50 a ++ closeIdxCells50 (sp48 + BitVec.ofNat 32 4294967295))
      (n := "%arena.9") (env := S9.env)
      (by simp only [closeGepCells50, closeIdxCells50, List.map_append,
        List.map_cons, List.map_nil]; decide)]
    simp only [S9, bracketArr, stage2NoEventWalkNext]
    exact stage2NoEventWalkCells_some (cs := closeArrAllCells sp48
      (BitVec.ofNat 64 (k + 3)) (BitVec.ofNat 64 K.arena.length)
      (BitVec.ofNat 64 K.arenaWord) (BitVec.ofNat 64 (K.terms + 10))
      (BitVec.ofNat 64 (K.tok + 3)))
      (n := "%arena.9") (v := .int 64 (BitVec.ofNat 64 K.arenaWord))
      (by simp only [closeArrAllCells, closeArrTail, closeArrPhiCells,
        List.mem_append, List.mem_cons, List.not_mem_nil, or_false]; tauto)
      (by simp only [closeArrAllCells, closeArrTail, closeArrPhiCells,
        List.map_append, List.map_cons, List.map_nil]; decide)
  have hterms10 : lookupName S10.env "%terms.7" =
      some (.int 64 (BitVec.ofNat 64 (K.terms + 10))) := by
    simp only [S10, bracketRead, stage2NoEventWalkNext]
    rw [stage2NoEventWalkCells_notin (cs :=
      ("%50", .int 8 (BitVec.ofNat 8 (bytesToNat stage2NoEventWalkBracketMarker))) ::
        closeGepCells50 a ++ closeIdxCells50 (sp48 + BitVec.ofNat 32 4294967295))
      (n := "%terms.7") (env := S9.env)
      (by simp only [closeGepCells50, closeIdxCells50, List.map_append,
        List.map_cons, List.map_nil]; decide)]
    simp only [S9, bracketArr, stage2NoEventWalkNext]
    exact stage2NoEventWalkCells_some (cs := closeArrAllCells sp48
      (BitVec.ofNat 64 (k + 3)) (BitVec.ofNat 64 K.arena.length)
      (BitVec.ofNat 64 K.arenaWord) (BitVec.ofNat 64 (K.terms + 10))
      (BitVec.ofNat 64 (K.tok + 3)))
      (n := "%terms.7") (v := .int 64 (BitVec.ofNat 64 (K.terms + 10)))
      (by simp only [closeArrAllCells, closeArrTail, closeArrPhiCells,
        List.mem_append, List.mem_cons, List.not_mem_nil, or_false]; tauto)
      (by simp only [closeArrAllCells, closeArrTail, closeArrPhiCells,
        List.map_append, List.map_cons, List.map_nil]; decide)
  have htoks10 : lookupName S10.env "%tokens.7" =
      some (.int 64 (BitVec.ofNat 64 (K.tok + 3))) := by
    simp only [S10, bracketRead, stage2NoEventWalkNext]
    rw [stage2NoEventWalkCells_notin (cs :=
      ("%50", .int 8 (BitVec.ofNat 8 (bytesToNat stage2NoEventWalkBracketMarker))) ::
        closeGepCells50 a ++ closeIdxCells50 (sp48 + BitVec.ofNat 32 4294967295))
      (n := "%tokens.7") (env := S9.env)
      (by simp only [closeGepCells50, closeIdxCells50, List.map_append,
        List.map_cons, List.map_nil]; decide)]
    simp only [S9, bracketArr, stage2NoEventWalkNext]
    exact stage2NoEventWalkCells_some (cs := closeArrAllCells sp48
      (BitVec.ofNat 64 (k + 3)) (BitVec.ofNat 64 K.arena.length)
      (BitVec.ofNat 64 K.arenaWord) (BitVec.ofNat 64 (K.terms + 10))
      (BitVec.ofNat 64 (K.tok + 3)))
      (n := "%tokens.7") (v := .int 64 (BitVec.ofNat 64 (K.tok + 3)))
      (by simp only [closeArrAllCells, closeArrTail, closeArrPhiCells,
        List.mem_append, List.mem_cons, List.not_mem_nil, or_false]; tauto)
      (by simp only [closeArrAllCells, closeArrTail, closeArrPhiCells,
        List.map_append, List.map_cons, List.map_nil]; decide)
  -- the base lookups through the route's layers
  have hbase : Stage2NoEventWalkBaseLookups Kc S10 := by
    have b0 : ∀ n v, (n, v) ∈ stage2NoEventWalkBaseValues K →
        lookupName s.env n = some v := disp.baseLookups
    have b1 := stage2NoEventCycleBase (K := K) (env := s.env) b0
      (cs := [("%Pivot16", .int 1 0)]) (names := ["%Pivot16"]) rfl (by decide)
    have b2 := stage2NoEventCycleBase (K := K) b1
      (cs := [("%Pivot14", .int 1 1)]) (names := ["%Pivot14"]) rfl (by decide)
    have b3 := stage2NoEventCycleBase (K := K) b2
      (cs := [("%SwitchLeaf10", .int 1 1)]) (names := ["%SwitchLeaf10"]) rfl
      (by decide)
    have b4 := stage2NoEventCycleBase (K := K) b3
      (cs := [("%exitcond", .int 1 0)]) (names := ["%exitcond"]) rfl (by decide)
    have b5 := stage2NoEventCycleBase (K := K) b4
      (cs := [("%cmp319.not", .int 1 1),
        ("%arrayidx50", .ptr (K.stk + A.off))])
      (names := ["%cmp319.not", "%arrayidx50"]) rfl (by decide)
    have b6 := stage2NoEventCycleBase (K := K) b5
      (cs := [("%cmp332", .int 1 1),
        ("%47", .int 8 (BitVec.ofNat 8 (bytesToNat [byte2]))),
        ("%arrayidx330", .ptr (K.b + (BitVec.signExtend 64
          (BitVec.ofNat 64 (bytesToNat bs4))).toNat)),
        ("%idxprom329", .int 64 (BitVec.ofNat 64 (bytesToNat bs4))),
        ("%46", .int 32 (BitVec.ofNat 32 (bytesToNat bs4))),
        ("%arrayidx328", .ptr (K.ep + (BitVec.ofNat 64 (k + 2)).toNat * 4))])
      (names := ["%cmp332", "%47", "%arrayidx330", "%idxprom329", "%46",
        "%arrayidx328"]) rfl (by decide)
    have b7 := stage2NoEventCycleBase (K := K) b6
      (cs := [("%48", .int 32 (BitVec.ofNat 32 (iv.toNat % 2 ^ 32)))])
      (names := ["%48"]) rfl (by decide)
    have b8 := stage2NoEventCycleBase (K := K) b7
      (cs := ifThen334AllCells sp48 (BitVec.ofNat 64 (k + 1))
        (BitVec.ofNat 64 (K.tok + 1)) (BitVec.ofNat 64 (K.terms + 3)))
      (names := (ifThen334AllCells sp48 (BitVec.ofNat 64 (k + 1))
        (BitVec.ofNat 64 (K.tok + 1)) (BitVec.ofNat 64 (K.terms + 3))).map (·.1))
      rfl (by simp only [ifThen334AllCells, ifThen334Cells, ifThen334PhiCells,
        List.map_append, List.map_cons, List.map_nil]; decide)
    have b9 := stage2NoEventCycleBase (K := K) b8
      (cs := closeArrAllCells sp48 (BitVec.ofNat 64 (k + 3))
        (BitVec.ofNat 64 K.arena.length) (BitVec.ofNat 64 K.arenaWord)
        (BitVec.ofNat 64 (K.terms + 10)) (BitVec.ofNat 64 (K.tok + 3)))
      (names := (closeArrAllCells sp48 (BitVec.ofNat 64 (k + 3))
        (BitVec.ofNat 64 K.arena.length) (BitVec.ofNat 64 K.arenaWord)
        (BitVec.ofNat 64 (K.terms + 10)) (BitVec.ofNat 64 (K.tok + 3))).map (·.1))
      rfl (by simp only [closeArrAllCells, closeArrTail, closeArrPhiCells,
        List.map_append, List.map_cons, List.map_nil]; decide)
    have b10 := stage2NoEventCycleBase (K := K) b9
      (cs := ("%50", .int 8 (BitVec.ofNat 8 (bytesToNat stage2NoEventWalkBracketMarker))) ::
        closeGepCells50 a ++ closeIdxCells50 (sp48 + BitVec.ofNat 32 4294967295))
      (names := (("%50", .int 8 (BitVec.ofNat 8 (bytesToNat stage2NoEventWalkBracketMarker))) ::
        closeGepCells50 a ++ closeIdxCells50 (sp48 + BitVec.ofNat 32 4294967295)).map (·.1))
      rfl (by simp only [closeGepCells50, closeIdxCells50, List.map_append,
        List.map_cons, List.map_nil]; decide)
    intro n v hv
    have hbv : stage2NoEventWalkBaseValues Kc = stage2NoEventWalkBaseValues K := rfl
    rw [hbv] at hv
    exact b10 n v hv
  -- the trace: the outer opener, then the nested pair
  have hbsOuter : K.bs[oLane]? = some (0x5B : UInt8) := by
    have hy : oByte = (0x5B : UInt8) :=
      stage2NoEventWalk_uint8_eq_of_toNat (by rw [oOpen]; decide)
    simpa [hy] using oBs
  have hbsNext : K.bs[next]? = some (0x5B : UInt8) := by
    have hy : nextByte = (0x5B : UInt8) :=
      stage2NoEventWalk_uint8_eq_of_toNat (by rw [byte91]; decide)
    simpa [hy] using bs1
  have hbsClose : K.bs[lane2]? = some (0x5D : UInt8) := by
    simpa [hb93] using hbs2
  have htrace1 : Stage2NoEventWalkTrace K1 := by
    refine Stage2NoEventWalkTrace.step (K := K) trace
      (stage2NoEventWalkOpenBracketRel hbsOuter) ?_ K1 rfl rfl ?_ ?_
    · exact stage2NoEventArenaBound_markers (by
        intro e he
        simp only [List.mem_cons, List.not_mem_nil, or_false] at he
        rcases he with rfl
        exact ⟨by decide, by decide⟩)
    · rfl
    · have h3 : ([ConsumerEvent.kind 3].map ConsumerEvent.terms).sum = 3 := by decide
      rw [h3]
  have htrace : Stage2NoEventWalkTrace Kc := by
    refine Stage2NoEventWalkTrace.step (K := K1) htrace1
      (stage2NoEventWalkEmptyArrayRel hbsNext hbsClose)
      (stage2NoEventArenaBound_emptyArray K.arena) Kc rfl rfl ?_ ?_
    · rfl
    · have h7 : ([ConsumerEvent.kind 3, ConsumerEvent.kind 4].map
          ConsumerEvent.terms).sum = 7 := by decide
      rw [h7]
  refine
    { inv := L10.inv'
      pc := rfl
      frame := 1
      frameLt := by decide
      frameNe := by decide
      sp := sp48.toNat
      spLt := hspLt
      spNe := hspNe
      kAddr := by
        have hne := inv.nepLe
        omega
      klt := by
        have : Kc.nep = K.nep := rfl
        omega
      count := by
        show Kc.tok ≤ k + 3
        rw [hKctok]
        have hcnt : K.tok ≤ k := count
        omega
      phiRun := by
        refine ⟨"if.then350", rfl, ?_⟩
        refine PhiSelects.cons (op := .reg "%50") (by decide) ?_
          (PhiSelects.cons (op := .reg "%sp.3") (by decide) ?_
            (PhiSelects.cons (op := .reg "%k.5") (by decide) ?_
              (PhiSelects.cons (op := .reg "%alen.7") (by decide) ?_
                (PhiSelects.cons (op := .reg "%arena.9") (by decide) ?_
                  (PhiSelects.cons (op := .reg "%terms.7") (by decide) ?_
                    (PhiSelects.cons (op := .reg "%tokens.7") (by decide) ?_
                      PhiSelects.nil))))))
        all_goals
          simp only [Kc, K1, stateAt, evalOperand, h50, hsp10, hk10, halen10,
            harena10, hterms10, htoks10, BitVec.ofNat_toNat, BitVec.setWidth_eq]
      baseLookups := hbase
      bPos := bPos
      trace := htrace
      comma := hcomma }

/-! ### The element arm: the false byte test to the next dispatch

`if.end327`'s byte is not `]`, so `if.end`'s six `phi`s and four adds hand the
element's byte and lane to `NodeBlock15` at index `k + 1`, with the carry moved by
the opener the descend's `if.end` already counted. -/

/-- **The bracket inner element arm**: seven blocks from the dispatch to the next
`NodeBlock15`, whose window is the element's. -/
theorem stage2NoEventWalkBracketInnerElement {calls : Calls}
    {K : Stage2NoEventWalkCarry} {mem : Mem} {k : Nat} {s : State}
    {next : Nat} {nextByte : UInt8}
    (W : Stage2NoEventWalkBracketInnerWindow K mem k s next nextByte)
    {lane2 : Nat} {byte2 : UInt8}
    (hk2 : K.ent[k + 2]? = some lane2) (hbs2 : K.bs[lane2]? = some byte2)
    (hne : byte2.toNat ≠ 93) :
    ∃ (s2 : State) (K1 : Stage2NoEventWalkCarry),
      K1 = { K with tok := K.tok + 1, terms := K.terms + 3 } ∧
      Stage2NoEventWalkSegment calls mem K s K1 s2 7 ∧
      Stage2NoEventWalkBracketDispatch K1 (k + 1) s2 lane2 byte2 ∧
      Stage2NoEventWalkTrace K1 := by
  classical
  let A := stage2NoEventWalkBracketInnerTo327 (calls := calls) W
  obtain ⟨disp, byte91, bs1, inv, oLane, oByte, oBs, oOpen, ivIn, iv,
    cnt, hIVIn, hIV, hCnt, ivInLt, ivVal, ivNe, hStk, alenPhi, arenaPhi, count, live,
    bPos, trace⟩ := W
  obtain ⟨bs4, hlane, hval4, hval4lt, hbyte⟩ :=
    stage2NoEventWalkBracketMarkerReads (K := K) (off := A.off) inv hk2 hbs2 A.hOff
  let K1 : Stage2NoEventWalkCarry := { K with tok := K.tok + 1, terms := K.terms + 3 }
  let S6 := stage2NoEventWalkNext
    (("%cmp332", .int 1 0) ::
      ("%47", .int 8 (BitVec.ofNat 8 (bytesToNat [byte2]))) ::
      ("%arrayidx330",
        .ptr (K.b + (BitVec.signExtend 64
          (BitVec.ofNat 64 (bytesToNat bs4))).toNat)) ::
      ("%idxprom329", .int 64 (BitVec.ofNat 64 (bytesToNat bs4))) ::
      ("%46", .int 32 (BitVec.ofNat 32 (bytesToNat bs4))) ::
      ("%arrayidx328", .ptr (K.ep + (BitVec.ofNat 64 (k + 2)).toNat * 4)) ::
      A.s5.env) A.s5 "if.end"
  let S7 := stage2NoEventWalkNext
    (cells (ifEndAllCells (BitVec.ofNat 8 (bytesToNat [byte2]))
      (BitVec.ofNat 32 (bytesToNat bs4)) iv (BitVec.ofNat 64 (k + 2))
      (BitVec.ofNat 64 (K.terms + 3)) (BitVec.ofNat 64 (K.tok + 1))) S6.env)
    S6 "NodeBlock15"
  have hbSlide : bytesToNat [byte2] = byte2.toNat :=
    stage2NoEventWalkBytesToNat_single byte2
  have hbit : evalICmp .eq (BitVec.ofNat 8 (bytesToNat [byte2])) (BitVec.ofNat 8 93) = 0 := by
    rw [hbSlide]
    have hy : (BitVec.ofNat 8 byte2.toNat) ≠ (BitVec.ofNat 8 93) := by
      intro hh
      exact hne (by
        have := congrArg BitVec.toNat hh
        simpa only [BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt (by have := byte2.toNat_lt; omega),
          Nat.mod_eq_of_lt (by decide : 93 < 2 ^ 8)] using this)
    have hd : decide ((BitVec.ofNat 8 byte2.toNat) = (BitVec.ofNat 8 93)) = false := by
      simp only [decide_eq_false_iff_not]
      exact hy
    simp only [evalICmp, hd]
    decide
  have hmaxDoc : K.n ≤ 2 ^ 32 := by
    have := inv.maxDoc
    simpa [stage2MaxDocument] using this
  have hneLe := inv.nepLe
  have hincLt : (BitVec.ofNat 64 (k + 2)).toNat < 2 ^ 63 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := inv.nepLt; omega)]
    omega
  have hmem6 : A.s5.mem = writeBytes s.mem (K.stk + A.off)
      stage2NoEventWalkBracketMarker := A.mem_eq
  have L6 : Stage2NoEventWalkLink calls K mem A.s5 K S6 :=
    link_ifEnd327_false A.inv A.pc A.hInc A.hEp A.hB hincLt
      (by rw [hmem6]; exact hlane) hval4lt (by rw [hmem6]; exact hbyte) hbit
  have h477 : lookupName S6.env "%47" =
      some (.int 8 (BitVec.ofNat 8 (bytesToNat [byte2]))) := by
    simp only [S6, stage2NoEventWalkNext]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact lookupName_cons_self _ _ _
  have h466 : lookupName S6.env "%46" =
      some (.int 32 (BitVec.ofNat 32 (bytesToNat bs4))) := by
    simp only [S6, stage2NoEventWalkNext]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact lookupName_cons_self _ _ _
  have hIV6 : lookupName S6.env "%indvars.iv" = some (.int 64 iv) := by
    simp only [S6, stage2NoEventWalkNext]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact A.hIV
  have hInc6 : lookupName S6.env "%inc" =
      some (.int 64 (BitVec.ofNat 64 (k + 2))) := by
    simp only [S6, stage2NoEventWalkNext]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact A.hInc
  have hTok6 : lookupName S6.env "%tokens.0" =
      some (.int 64 (BitVec.ofNat 64 (K.tok + 1))) := by
    simp only [S6, stage2NoEventWalkNext]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact A.hTok
  have hTerms6 : lookupName S6.env "%terms.0" =
      some (.int 64 (BitVec.ofNat 64 (K.terms + 3))) := by
    simp only [S6, stage2NoEventWalkNext]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact A.hTerms
  have L7 : Stage2NoEventWalkLink calls K mem S6 K1 S7 := by
    have hh := link_ifEnd_fromEnd327 (calls := calls) (K := K) (s := S6) L6.inv'
      rfl rfl h477 h466 hIV6 hInc6 hTerms6 hTok6
    refine Stage2NoEventWalkLink.reindex hh ?_
    have htok1 : K.tok + 1 ≤ K.n := by
      have hcnt : K.tok ≤ k := count
      have hne' := inv.nepLe
      omega
    exact Stage2NoEventWalkInv.count (K := K) hh.inv' (t := 1) (c := 3) htok1
  have hrun : ∀ n, runFuel calls (7 + n) stage2NoEventBody s =
      runFuel calls n stage2NoEventBody S7 := by
    intro n
    rw [show 7 + n = 5 + (1 + (1 + n)) from by omega,
      A.seg.run (1 + (1 + n)),
      stage2NoEventWalkLink_runFuel L6, stage2NoEventWalkLink_runFuel L7]
  have hseg : Stage2NoEventWalkSegment calls mem K s K1 S7 7 := ⟨hrun, L7.inv'⟩
  -- the next dispatch's window
  have h7 : lookupName S7.env "%7" = some (.int 8 (BitVec.ofNat 8 byte2.toNat)) := by
    simp only [S7, stage2NoEventWalkNext]
    have hw := ifEndAllCells_dispatch (v7 := BitVec.ofNat 8 (bytesToNat [byte2]))
      (v8 := BitVec.ofNat 32 (bytesToNat bs4)) (ivIn := iv)
      (k0 := BitVec.ofNat 64 (k + 2)) (termsIn := BitVec.ofNat 64 (K.terms + 3))
      (toksIn := BitVec.ofNat 64 (K.tok + 1)) S6.env
    have := hw.1
    simpa only [hbSlide] using this
  have h8 : lookupName S7.env "%8" = some (.int 32 (BitVec.ofNat 32 lane2)) := by
    simp only [S7, stage2NoEventWalkNext]
    have hw := ifEndAllCells_dispatch (v7 := BitVec.ofNat 8 (bytesToNat [byte2]))
      (v8 := BitVec.ofNat 32 (bytesToNat bs4)) (ivIn := iv)
      (k0 := BitVec.ofNat 64 (k + 2)) (termsIn := BitVec.ofNat 64 (K.terms + 3))
      (toksIn := BitVec.ofNat 64 (K.tok + 1)) S6.env
    have := hw.2.1
    simpa only [hval4] using this
  have hk07 : lookupName S7.env "%k.0" =
      some (.int 64 (BitVec.ofNat 64 ((k + 1) + 1))) := by
    simp only [S7, stage2NoEventWalkNext]
    have hw := ifEndAllCells_dispatch (v7 := BitVec.ofNat 8 (bytesToNat [byte2]))
      (v8 := BitVec.ofNat 32 (bytesToNat bs4)) (ivIn := iv)
      (k0 := BitVec.ofNat 64 (k + 2)) (termsIn := BitVec.ofNat 64 (K.terms + 3))
      (toksIn := BitVec.ofNat 64 (K.tok + 1)) S6.env
    exact hw.2.2.1
  have hinc7 : lookupName S7.env "%inc" =
      some (.int 64 (BitVec.ofNat 64 ((k + 1) + 2))) := by
    simp only [S7, stage2NoEventWalkNext]
    have hw := ifEndAllCells_dispatch (v7 := BitVec.ofNat 8 (bytesToNat [byte2]))
      (v8 := BitVec.ofNat 32 (bytesToNat bs4)) (ivIn := iv)
      (k0 := BitVec.ofNat 64 (k + 2)) (termsIn := BitVec.ofNat 64 (K.terms + 3))
      (toksIn := BitVec.ofNat 64 (K.tok + 1)) S6.env
    have h := hw.2.2.2.2.2
    have hs : BitVec.ofNat 64 (k + 2) + BitVec.ofNat 64 1
        = BitVec.ofNat 64 ((k + 1) + 2) := by
      rw [stage2NoEventWalkOfNat_add]
    rw [hs] at h
    exact h
  have htok7 : lookupName S7.env "%tokens.0" =
      some (.int 64 (BitVec.ofNat 64 (K1.tok + 1))) := by
    simp only [S7, stage2NoEventWalkNext]
    have hw := ifEndAllCells_dispatch (v7 := BitVec.ofNat 8 (bytesToNat [byte2]))
      (v8 := BitVec.ofNat 32 (bytesToNat bs4)) (ivIn := iv)
      (k0 := BitVec.ofNat 64 (k + 2)) (termsIn := BitVec.ofNat 64 (K.terms + 3))
      (toksIn := BitVec.ofNat 64 (K.tok + 1)) S6.env
    have h := hw.2.2.2.1
    have hs : BitVec.ofNat 64 (K.tok + 1) + BitVec.ofNat 64 1
        = BitVec.ofNat 64 (K1.tok + 1) := by
      rw [stage2NoEventWalkOfNat_add]
    rw [hs] at h
    exact h
  have hterms7 : lookupName S7.env "%terms.0" =
      some (.int 64 (BitVec.ofNat 64 (K1.terms + 3))) := by
    simp only [S7, stage2NoEventWalkNext]
    have hw := ifEndAllCells_dispatch (v7 := BitVec.ofNat 8 (bytesToNat [byte2]))
      (v8 := BitVec.ofNat 32 (bytesToNat bs4)) (ivIn := iv)
      (k0 := BitVec.ofNat 64 (k + 2)) (termsIn := BitVec.ofNat 64 (K.terms + 3))
      (toksIn := BitVec.ofNat 64 (K.tok + 1)) S6.env
    have h := hw.2.2.2.2.1
    have hs : BitVec.ofNat 64 (K.terms + 3) + BitVec.ofNat 64 3
        = BitVec.ofNat 64 (K1.terms + 3) := by
      rw [stage2NoEventWalkOfNat_add]
    rw [hs] at h
    exact h
  have hbase7 : Stage2NoEventWalkBaseLookups K1 S7 := by
    have b0 : ∀ n v, (n, v) ∈ stage2NoEventWalkBaseValues K →
        lookupName s.env n = some v := disp.baseLookups
    have b1 := stage2NoEventCycleBase (K := K) (env := s.env) b0
      (cs := [("%Pivot16", .int 1 0)]) (names := ["%Pivot16"]) rfl (by decide)
    have b2 := stage2NoEventCycleBase (K := K) b1
      (cs := [("%Pivot14", .int 1 1)]) (names := ["%Pivot14"]) rfl (by decide)
    have b3 := stage2NoEventCycleBase (K := K) b2
      (cs := [("%SwitchLeaf10", .int 1 1)]) (names := ["%SwitchLeaf10"]) rfl
      (by decide)
    have b4 := stage2NoEventCycleBase (K := K) b3
      (cs := [("%exitcond", .int 1 0)]) (names := ["%exitcond"]) rfl (by decide)
    have b5 := stage2NoEventCycleBase (K := K) b4
      (cs := [("%cmp319.not", .int 1 1),
        ("%arrayidx50", .ptr (K.stk + A.off))])
      (names := ["%cmp319.not", "%arrayidx50"]) rfl (by decide)
    have b6 := stage2NoEventCycleBase (K := K) b5
      (cs := [("%cmp332", .int 1 0),
        ("%47", .int 8 (BitVec.ofNat 8 (bytesToNat [byte2]))),
        ("%arrayidx330", .ptr (K.b + (BitVec.signExtend 64
          (BitVec.ofNat 64 (bytesToNat bs4))).toNat)),
        ("%idxprom329", .int 64 (BitVec.ofNat 64 (bytesToNat bs4))),
        ("%46", .int 32 (BitVec.ofNat 32 (bytesToNat bs4))),
        ("%arrayidx328", .ptr (K.ep + (BitVec.ofNat 64 (k + 2)).toNat * 4))])
      (names := ["%cmp332", "%47", "%arrayidx330", "%idxprom329", "%46",
        "%arrayidx328"]) rfl (by decide)
    have b7 := stage2NoEventCycleBase (K := K) b6
      (cs := ifEndAllCells (BitVec.ofNat 8 (bytesToNat [byte2]))
        (BitVec.ofNat 32 (bytesToNat bs4)) iv (BitVec.ofNat 64 (k + 2))
        (BitVec.ofNat 64 (K.terms + 3)) (BitVec.ofNat 64 (K.tok + 1)))
      (names := (ifEndAllCells (BitVec.ofNat 8 (bytesToNat [byte2]))
        (BitVec.ofNat 32 (bytesToNat bs4)) iv (BitVec.ofNat 64 (k + 2))
        (BitVec.ofNat 64 (K.terms + 3)) (BitVec.ofNat 64 (K.tok + 1))).map (·.1))
      rfl (by simp only [ifEndAllCells, ifEndTailCells, ifEndPhiCells,
        List.map_append, List.map_cons, List.map_nil]; decide)
    intro n v hv
    have hbv : stage2NoEventWalkBaseValues K1 = stage2NoEventWalkBaseValues K := rfl
    rw [hbv] at hv
    exact b7 n v hv
  -- the successor window's trace: the opener at `k + 1` is the entry's byte
  have hbsNext : K.bs[next]? = some (0x5B : UInt8) := by
    have hy : nextByte = (0x5B : UInt8) :=
      stage2NoEventWalk_uint8_eq_of_toNat (by rw [byte91]; decide)
    simpa [hy] using bs1
  have htrace1 : Stage2NoEventWalkTrace K1 := by
    refine Stage2NoEventWalkTrace.step (K := K) trace
      (stage2NoEventWalkOpenBracketRel hbsNext) ?_ K1 rfl rfl ?_ ?_
    · exact stage2NoEventArenaBound_markers (by
        intro e he
        simp only [List.mem_cons, List.not_mem_nil, or_false] at he
        rcases he with rfl
        exact ⟨by decide, by decide⟩)
    · rfl
    · have h3 : ([ConsumerEvent.kind 3].map ConsumerEvent.terms).sum = 3 := by decide
      rw [h3]
  exact ⟨S7, K1, rfl, hseg,
    { pc := rfl
      pre := rfl
      byte := h7
      lane := h8
      index := hk07
      inc := hinc7
      tokens := htok7
      terms := hterms7
      baseLookups := hbase7 }, htrace1⟩

/-! ### The producers

`Stage2NoEventWalkBracketInner` quantifies over the caller's prefix count `j0`
without bounding it, and the caller gets `j0` from
`Stage2NoEventWalkSegment.of_chain`, an existential.  So the price field cannot be
discharged from the dispatch window alone: the producers below take the prefix's
share as a hypothesis instead, at the counts this module proves.  The
recursion's second arm is the same shape one index in, and its premise is the
recursion's own window (trace included) plus the successor window's staging. -/

/-- **The recursion's premise**, at the window: the trace and the staging are
hypotheses of the recursion, not facts about the carry, so the endpoint's
`Stage2NoEventWalkCycleSrc` is producible.  (The committed
`Stage2NoEventWalkBracketInner` is the trace-free projection of this: a caller
that can build the window from the dispatch gets that one from this.) -/
def Stage2NoEventWalkBracketInnerAll (calls : Calls) (mem : Mem)
    (K : Stage2NoEventWalkCarry) (k : Nat) (next : Nat) (nextByte : UInt8) : Prop :=
  ∀ (s₀ : State), Stage2NoEventWalkBracketInnerWindow K mem k s₀ next nextByte →
    ∀ (j : Nat), Nonempty (Stage2NoEventWalkBracketInnerOut calls mem K k s₀ j)

/-- **The closer's inner producer**: the window, the `]` entry, the separator,
the prefix's share (`j0 + 10 ≤ 96`) and the arm's ten-block segment, the endpoint's
bundle and the shared cycle, as a `Stage2NoEventWalkBracketInnerOut`. -/
noncomputable def stage2NoEventWalkBracketInnerOutCloser {calls : Calls} {mem : Mem}
    {K : Stage2NoEventWalkCarry} {k : Nat} {s : State} {next : Nat} {nextByte : UInt8}
    (W : Stage2NoEventWalkBracketInnerWindow K mem k s next nextByte)
    {lane2 : Nat} {byte2 : UInt8}
    (hk2 : K.ent[k + 2]? = some lane2) (hbs2 : K.bs[lane2]? = some byte2)
    (hb2 : byte2.toNat = 93)
    (hcomma : ∀ q, K.ent[k + 3]? = some q → K.bs.getD q 0 = 44)
    (j0 : Nat) (hj0 : j0 + 10 ≤ 96) :
    Stage2NoEventWalkBracketInnerOut calls mem K k s j0 := by
  classical
  let w := stage2NoEventWalkBracketInnerCloser (calls := calls) W hk2 hbs2 hb2 hcomma
  let sE := Classical.choose w
  have hspec := Classical.choose_spec w
  let Kc := Classical.choose hspec
  have hspecK := Classical.choose_spec hspec
  have hKc : Kc = { K with tok := K.tok + 3, terms := K.terms + 10 } := hspecK.1
  have hseg : Stage2NoEventWalkSegment calls mem K s Kc sE 10 := hspecK.2.1
  let src := Classical.choice hspecK.2.2
  let cw := stage2NoEventWalkCycle_of_afterValue src
  let s' := Classical.choose cw
  have hcws := Classical.choose_spec cw
  let p := Classical.choose hcws
  have hcyc : Stage2NoEventWalkCycle calls mem Kc (k + 3) sE 1 s' p :=
    Classical.choose_spec hcws
  refine ⟨Kc, k + 3, sE, s', 10, p, hseg, src, hcyc, ?_, ?_, ?_, by omega, ?_⟩
  · rw [hKc]
  · rw [hKc]
  · rw [hKc]
  -- the composed price: ten blocks, the cycle's eight, four entries' allowance
  have hne := W.inv.nepLe
  have hk3 : k + 3 ≤ K.nep := by have := W.live; omega
  have hlen : K.ent.length = K.nep :=
    readLanes32_length mem K.ep K.nep K.ent W.inv.entries
  have hent : K.ent.getD k 0 ≤ K.ent.getD (k + 3) 0 :=
    stage2NoEventEnt_getD_le (l := K.ent) W.inv.order (d := 0) (i := k) (j := k + 3)
      (by omega) (by rw [hlen]; have := W.live; omega)
  have hpot : stage2NoEventWalkPotential K (k + 3) + 96
      ≤ stage2NoEventWalkPotential K k := by
    have := stage2NoEventWalkPotential_add (K := K) (k := k) (d := 3) hk3 hent
    simpa using this
  have e3 : stage2NoEventWalkPotential Kc (k + 3) = stage2NoEventWalkPotential K (k + 3) := by
    rw [hKc]
    simp only [stage2NoEventWalkPotential]
  have e4 : stage2NoEventWalkPotential Kc (k + 4) = stage2NoEventWalkPotential K (k + 4) := by
    rw [hKc]
    simp only [stage2NoEventWalkPotential]
  have hcred : p + stage2NoEventWalkPotential K (k + 4)
      ≤ stage2NoEventWalkPotential K (k + 3) := by
    have h := hcyc.headPriced.credit
    rw [show (k + 3) + 1 = k + 4 from by omega, e4, e3] at h
    exact h
  have hgoal : j0 + 10 + p + stage2NoEventWalkPotential K (k + 4)
      ≤ stage2NoEventWalkPotential K k := by
    have h1 : j0 + 10 + p + stage2NoEventWalkPotential K (k + 4)
        ≤ 96 + p + stage2NoEventWalkPotential K (k + 4) := by omega
    have h2 : 96 + p + stage2NoEventWalkPotential K (k + 4)
        ≤ 96 + stage2NoEventWalkPotential K (k + 3) := by omega
    have h3 : 96 + stage2NoEventWalkPotential K (k + 3)
        ≤ stage2NoEventWalkPotential K (k + 3) + 96 := by omega
    have h4 : stage2NoEventWalkPotential K (k + 3) + 96
        ≤ stage2NoEventWalkPotential K k := hpot
    omega
  show j0 + 10 + p + stage2NoEventWalkPotential Kc ((k + 3) + 1)
      ≤ stage2NoEventWalkPotential K k
  rw [show (k + 3) + 1 = k + 4 from by omega, e4]
  exact hgoal

/-- **The element's inner producer**: the window, the non-`]` entry, the next
window's recursive producer and the prefix's share (`j0 + 7 ≤ 32`), as a
`Stage2NoEventWalkBracketInnerOut` through the seven-block handoff. -/
noncomputable def stage2NoEventWalkBracketInnerOutElement {calls : Calls} {mem : Mem}
    {K : Stage2NoEventWalkCarry} {k : Nat} {s : State} {next : Nat} {nextByte : UInt8}
    (W : Stage2NoEventWalkBracketInnerWindow K mem k s next nextByte)
    {lane2 : Nat} {byte2 : UInt8}
    (hk2 : K.ent[k + 2]? = some lane2) (hbs2 : K.bs[lane2]? = some byte2)
    (hne : byte2.toNat ≠ 93)
    (hel : Stage2NoEventWalkBracketInnerAll calls mem
      { K with tok := K.tok + 1, terms := K.terms + 3 } (k + 1) lane2 byte2)
    -- The successor window's staging, as the caller supplies it at every
    -- dispatch of the element's class; its `live` is `k + 5 < nep`, one entry
    -- past this arm's `k + 4 < nep`.
    (hstage : ∀ (s₀ : State), Stage2NoEventWalkBracketDispatch
      { K with tok := K.tok + 1, terms := K.terms + 3 } (k + 1) s₀ lane2 byte2 →
      Stage2NoEventWalkBracketInnerWindow
        { K with tok := K.tok + 1, terms := K.terms + 3 } mem (k + 1) s₀ lane2 byte2)
    (j0 : Nat) (hj0 : j0 + 7 ≤ 32) :
    Stage2NoEventWalkBracketInnerOut calls mem K k s j0 := by
  classical
  let w := stage2NoEventWalkBracketInnerElement (calls := calls) W hk2 hbs2 hne
  let s2 := Classical.choose w
  have hspec := Classical.choose_spec w
  let K1 := Classical.choose hspec
  have hspecK := Classical.choose_spec hspec
  have hK1 : K1 = { K with tok := K.tok + 1, terms := K.terms + 3 } := hspecK.1
  have hseg7 : Stage2NoEventWalkSegment calls mem K s K1 s2 7 := hspecK.2.1
  have hdisp2 : Stage2NoEventWalkBracketDispatch K1 (k + 1) s2 lane2 byte2 :=
    hspecK.2.2.1
  rw [hK1] at hseg7 hdisp2
  let I := Classical.choice (hel s2 (hstage s2 hdisp2) 0)
  have hlt : k < I.kc + 1 := by have h := I.hlt; omega
  refine ⟨I.Kc, I.kc, I.sE, I.s', 7 + I.j1, I.p, hseg7.trans I.seg, I.src, I.cyc,
    I.hnep, I.ha12, I.hn0, hlt, ?_⟩
  have hne := W.inv.nepLe
  have hk1 : k + 1 ≤ K.nep := by have := W.live; omega
  have hlen : K.ent.length = K.nep :=
    readLanes32_length mem K.ep K.nep K.ent W.inv.entries
  have hent : K.ent.getD k 0 ≤ K.ent.getD (k + 1) 0 :=
    stage2NoEventEnt_getD_le (l := K.ent) W.inv.order (d := 0) (i := k) (j := k + 1)
      (by omega) (by rw [hlen]; have := W.live; omega)
  have hpot : stage2NoEventWalkPotential K (k + 1) + 32
      ≤ stage2NoEventWalkPotential K k := by
    have := stage2NoEventWalkPotential_add (K := K) (k := k) (d := 1) hk1 hent
    simpa using this
  have eP : stage2NoEventWalkPotential ({ K with tok := K.tok + 1, terms := K.terms + 3 } : Stage2NoEventWalkCarry) (k + 1) = stage2NoEventWalkPotential K (k + 1) := by
    simp only [stage2NoEventWalkPotential]
  have hcred : I.j1 + I.p + stage2NoEventWalkPotential I.Kc (I.kc + 1) ≤
      stage2NoEventWalkPotential K (k + 1) := by
    have h := I.price
    simpa only [Nat.zero_add, eP] using h
  have hgoal : j0 + (7 + I.j1) + I.p + stage2NoEventWalkPotential I.Kc (I.kc + 1)
      ≤ stage2NoEventWalkPotential K k := by
    have h1 : j0 + (7 + I.j1) + I.p + stage2NoEventWalkPotential I.Kc (I.kc + 1)
        ≤ 32 + (I.j1 + I.p + stage2NoEventWalkPotential I.Kc (I.kc + 1)) := by omega
    have h2 : 32 + (I.j1 + I.p + stage2NoEventWalkPotential I.Kc (I.kc + 1))
        ≤ 32 + stage2NoEventWalkPotential K (k + 1) := by omega
    have h3 : stage2NoEventWalkPotential K (k + 1) + 32
        ≤ stage2NoEventWalkPotential K k := hpot
    omega
  exact hgoal

#print axioms stage2NoEventWalkBracketInnerTo327
#print axioms stage2NoEventWalkBracketInnerCloser
#print axioms stage2NoEventWalkBracketInnerElement
#print axioms stage2NoEventWalkBracketInnerOutCloser
#print axioms stage2NoEventWalkBracketInnerOutElement
#print axioms Stage2NoEventWalkBracketInnerAll
#print axioms Stage2NoEventWalkBracketInnerWindow

#print axioms ifEnd51Block_find
#print axioms link_ifEnd51
#print axioms ifThen334_phi_denote_loopexit
#print axioms link_ifThen334LoopexitEdge
#print axioms stage2NoEventWalkBracketMarkerReads
#print axioms stage2NoEventWalkBracketMarker_pop

end LeanLLVM.Refinement
