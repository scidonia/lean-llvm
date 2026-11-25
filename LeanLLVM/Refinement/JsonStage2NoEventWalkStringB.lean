/-
The no-event walk's string class at the head: the quote's staging, the head
edge's `string_value` entry, and the class's one-step trace.

The head block's read is the class pivot: `%3` is the document's byte at the
entry's lane, and a `"` (34) sends the dispatch `NodeBlock5 → LeafBlock →
string_value`.  The dispatch row and the `string_value` block are
`JsonStage2NoEventWalkClose`'s; that module proves the block's run at its
`string_value.loopexit` edge, where the eight `phi`s come from the loop's own
registers.  At the head the edge is `LeafBlock`, and the `phi` operands are the
head's read and `phi` cells instead — `%inc.lcssa1130` is the head's `%inc.peel`,
`%.lcssa1125` its `%2`, `%idxprom.lcssa1109` its `%idxprom.peel`, and the reading
and stack words its own `phi` cells.  This module proves that run
(`stringValueHead_denote`) and its link, so the class's entry from a head is one
chain: the dispatch, the merge, and the closing entry's test to `if.end216`.

`string_value`'s route then reads the closing entry's lane (`if.end216`), forms
the body's cursor and length (`if.end230`) and calls `s2_string_body`
(`if.end239`); those blocks are the `WalkString` module's.  This module stops at
`if.end216`'s entry: the body's byte-sum loop (`for.body270`) and the after-value
arm's return to `if.end.peel` have no rows in the tree yet, so the priced head
segment to the next head is not claimed here.

**The class's output step.**  A string entry is one consumer event and one parser
token.  The event is `.str false len payload cs` with `payload` the arena cursor
`%alen.0.ph1405` (the head's own `phi` cell), `len` the decoded body's byte count
the callee wrote at `%outn205`, and `cs` the decoded code points; the token is the
span the entry's two quote positions name.  The relation's arena row
(`Stage2NoEvent.strArena`) reads the body from the extended arena, so
`Stage2NoEvent K.bs K'.arena [ev] [tok]` holds at the class's event and token.
The class's carry moves `tok` by one, `terms` by the record's `tag + len + payload`,
the arena by the decoded body, and the arena word by the body's byte sum modulo a
word — the walk's own register arithmetic (`%tokens.4`, `%terms.4`, `%arena.6`,
and the byte-sum loop's `%arena.5`).  The trace at the target is the source's
prefix, transported along the arena's extension and appended with this step; the
trace carries no memory read of its own, so the class claims the logical arena, not
a scratch prefix holding the concatenation (the decoder writes each body into the
scratch base, which the byte-sum loop reads for the latest body only).

**The empty string.**  `s2_string_body`'s form 1 — no escape position inside the
body — writes nothing to the arena and leaves `%outn205`'s word at the body's
length, so for a non-empty body the walk's arena and its word would advance without
the body ever being materialised.  The class therefore claims form 1 only at
`len = 0`: the empty string is one plain record (`field = plainSpan (lane + 1)`,
`len = 0`, no code points), whose contribution is the walk's `%add260`
(`plainSpan (lane + 1) + 6`), with the arena and its word unchanged.  Non-empty
bodies are the arena form above.
-/
import LeanLLVM.Refinement.JsonStage2NoEventWalkHead
import LeanLLVM.Refinement.JsonStage2NoEventWalkString

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000

namespace LeanLLVM.Refinement

open LeanLLVM
open LeanLLVM.JSON
open LeanLLVM.Refinement.JsonStage2NoEventIR
open LeanLLVM.Refinement.BlockEval

/-! ### The head's string class

The head's read fixes the class: the document's byte at the entry's lane, its
`i8` cell at `%3`, and the address the load read.  A `"` is the table's `string`
constructor. -/

/-- **The head's class staging**: the read's lane, byte, address and `%3` cell,
and the class table's value at that byte.  The lane and byte are the head's own
facts, so the class cannot disagree with the byte the dispatch tests. -/
theorem stage2NoEventWalkStringB_headStaging
    {K : Stage2NoEventWalkCarry} {mem : Mem} {k : Nat} {s : State}
    (h : Stage2NoEventWalkHead K mem k s) {lane : Nat} {byte : UInt8}
    (hent : K.ent[k]? = some lane) (hbs : K.bs[lane]? = some byte) :
    Nonempty (Stage2NoEventHeadClass byte.toNat) ∧
      lookupName s.env "%3" = some (.int 8 (BitVec.ofNat 8 byte.toNat)) ∧
      lookupName s.env "%2" = some (.int 32 (BitVec.ofNat 32 lane)) ∧
      lookupName s.env "%idxprom.peel" = some (.int 64 (BitVec.ofNat 64 lane)) ∧
      lookupName s.env "%inc.peel" = some (.int 64 (BitVec.ofNat 64 (k + 1))) ∧
      lookupName s.env "%arrayidx.peel" = some (.ptr (K.ep + 4 * k)) ∧
      lookupName s.env "%arrayidx6.peel" = some (.ptr (K.b + lane)) ∧
      readBytes s.mem (K.b + lane) 1 = some [byte] := by
  obtain ⟨lane', byte', hent', -, hbs', hread', h2, hidx, hinc, hidxarr, haddr,
    h3⟩ := h.laneRead
  have hlane : lane = lane' :=
    Option.some.inj (by rw [← hent, hent'])
  subst hlane
  have hbyte : byte = byte' :=
    Option.some.inj (by rw [← hbs, hbs'])
  subst hbyte
  exact ⟨⟨stage2NoEventHeadClass_complete byte.toNat⟩, h3, h2, hidx, hinc, hidxarr,
    haddr, hread'⟩

/-! ### `string_value` at the head's edge

`JsonStage2NoEventWalkClose` pins the block and proves its run at the
`string_value.loopexit` edge.  At the head the edge is `LeafBlock`, whose operands
are the head's read and `phi` cells, and whose `%frame.0.lcssa1099` is the head's
own frame cell rather than the loop exit's `1`.  The run below is the same block
at that edge: the eight `phi`s, the `%outn205` lifetime marker, and the closing
entry's test. -/

/-- The `phi` cells the `LeafBlock` edge installs, newest first. -/
def stringValueHeadCells (env : Env) (inc lane fr sp k terms tok : Nat) : Env :=
  ("%tokens.0.lcssa1075", .int 64 (BitVec.ofNat 64 tok)) ::
    ("%terms.0.lcssa1081", .int 64 (BitVec.ofNat 64 terms)) ::
    ("%k.0.lcssa1087", .int 64 (BitVec.ofNat 64 k)) ::
    ("%sp.0.lcssa1093.wide", .int 32 (BitVec.ofNat 32 sp)) ::
    ("%frame.0.lcssa1099", .int 8 (BitVec.ofNat 8 fr)) ::
    ("%idxprom.lcssa1109", .int 64 (BitVec.ofNat 64 lane)) ::
    ("%.lcssa1125", .int 32 (BitVec.ofNat 32 lane)) ::
    ("%inc.lcssa1130", .int 64 (BitVec.ofNat 64 inc)) :: env

/-- The block's environment at the head's edge: the test's bit over the `phi`
cells. -/
def stringValueHeadEnv (env : Env) (inc lane fr sp k terms tok nep : Nat) : Env :=
  ("%cmp207.not",
      .int 1 (evalICmp .ult (BitVec.ofNat 64 inc) (BitVec.ofNat 64 nep))) ::
    stringValueHeadCells env inc lane fr sp k terms tok

/-- The `phi` cells keep the `%outn205` staging word's binding. -/
theorem stringValueHeadCells_outn (env : Env) (inc lane fr sp k terms tok : Nat)
    {outn : Nat} (h : lookupName env "%outn205" = some (.ptr outn)) :
    lookupName (stringValueHeadCells env inc lane fr sp k terms tok) "%outn205" =
      some (.ptr outn) := by
  simp only [stringValueHeadCells]
  repeat rw [lookupName_cons_ne _ _ (by decide)]
  exact h

/-- The `phi` cells keep the entry count's binding. -/
theorem stringValueHeadCells_nep (env : Env) (inc lane fr sp k terms tok : Nat)
    {nep : Nat} (h : lookupName env "%nep" = some (.int 64 (BitVec.ofNat 64 nep))) :
    lookupName (stringValueHeadCells env inc lane fr sp k terms tok) "%nep" =
      some (.int 64 (BitVec.ofNat 64 nep)) := by
  simp only [stringValueHeadCells]
  repeat rw [lookupName_cons_ne _ _ (by decide)]
  exact h

/-- The advanced index resolves through the `phi` cells. -/
theorem stringValueHeadCells_inc (env : Env) (inc lane fr sp k terms tok : Nat) :
    lookupName (stringValueHeadCells env inc lane fr sp k terms tok) "%inc.lcssa1130" =
      some (.int 64 (BitVec.ofNat 64 inc)) := by
  simp only [stringValueHeadCells]
  repeat rw [lookupName_cons_ne _ _ (by decide)]
  rw [lookupName_cons_self]

/-- The test's bit at the block's exit. -/
theorem stringValueHeadEnv_cmp (env : Env) (inc lane fr sp k terms tok nep : Nat) :
    lookupName (stringValueHeadEnv env inc lane fr sp k terms tok nep) "%cmp207.not" =
      some (.int 1 (evalICmp .ult (BitVec.ofNat 64 inc) (BitVec.ofNat 64 nep))) := by
  simp only [stringValueHeadEnv, lookupName_cons_self]

/-- The `i64` comparison's guard at the `Nat` representatives. -/
theorem stage2NoEventWalkStringB_ult {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64)
    (h : a < b) :
    evalICmp .ult (BitVec.ofNat 64 a) (BitVec.ofNat 64 b) = 1 := by
  unfold evalICmp
  rw [BitVec.ult]
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb, h, decide_true,
    BitVec.ofBool_true]

/-- **`string_value` at the head's edge**: the eight `phi`s select the head's own
cells, the lifetime marker leaves the state alone, and the test compares the
advanced index against the entry count. -/
theorem stringValueHead_denote {gap : Calls} (env : Env) (s : State)
    {inc lane fr sp k terms tok nep outn : Nat}
    (hpre : s.pre = some "LeafBlock")
    (hinc : lookupName env "%inc.peel" = some (.int 64 (BitVec.ofNat 64 inc)))
    (h2 : lookupName env "%2" = some (.int 32 (BitVec.ofNat 32 lane)))
    (hidx : lookupName env "%idxprom.peel" = some (.int 64 (BitVec.ofNat 64 lane)))
    (hfr : lookupName env "%frame.0.ph1402" = some (.int 8 (BitVec.ofNat 8 fr)))
    (hsp : lookupName env "%sp.0.ph1403" = some (.int 32 (BitVec.ofNat 32 sp)))
    (hk : lookupName env "%k.0.ph1404" = some (.int 64 (BitVec.ofNat 64 k)))
    (hterms : lookupName env "%terms.0.ph1407" = some (.int 64 (BitVec.ofNat 64 terms)))
    (htok : lookupName env "%tokens.0.ph1408" = some (.int 64 (BitVec.ofNat 64 tok)))
    (houtn : lookupName env "%outn205" = some (.ptr outn))
    (hnep : lookupName env "%nep" = some (.int 64 (BitVec.ofNat 64 nep))) :
    denoteCode (stage2NoEventCalls gap) stringValueInstrs (stateAt env s) =
      some (stateAt (stringValueHeadEnv env inc lane fr sp k terms tok nep) s) := by
  have hsel : PhiSelects (stateAt env s) "LeafBlock" stringValuePhiSpecs
      [("%inc.lcssa1130", .int 64 (BitVec.ofNat 64 inc)),
       ("%.lcssa1125", .int 32 (BitVec.ofNat 32 lane)),
       ("%idxprom.lcssa1109", .int 64 (BitVec.ofNat 64 lane)),
       ("%frame.0.lcssa1099", .int 8 (BitVec.ofNat 8 fr)),
       ("%sp.0.lcssa1093.wide", .int 32 (BitVec.ofNat 32 sp)),
       ("%k.0.lcssa1087", .int 64 (BitVec.ofNat 64 k)),
       ("%terms.0.lcssa1081", .int 64 (BitVec.ofNat 64 terms)),
       ("%tokens.0.lcssa1075", .int 64 (BitVec.ofNat 64 tok))] := by
    refine PhiSelects.cons (op := .reg "%inc.peel") (by decide) ?_
      (PhiSelects.cons (op := .reg "%2") (by decide) ?_
        (PhiSelects.cons (op := .reg "%idxprom.peel") (by decide) ?_
          (PhiSelects.cons (op := .reg "%frame.0.ph1402") (by decide) ?_
            (PhiSelects.cons (op := .reg "%sp.0.ph1403") (by decide) ?_
              (PhiSelects.cons (op := .reg "%k.0.ph1404") (by decide) ?_
                (PhiSelects.cons (op := .reg "%terms.0.ph1407") (by decide) ?_
                  (PhiSelects.cons (op := .reg "%tokens.0.ph1408") (by decide) ?_
                    PhiSelects.nil)))))))
    all_goals
      simp only [stateAt, evalOperand, hinc, h2, hidx, hfr, hsp, hk, hterms, htok]
  rw [stringValuePhi_eq,
    denoteCode_phiRun (s := stateAt env s) (p := "LeafBlock")
      (specs := stringValuePhiSpecs)
      (rest := [Instr.callVoid "llvm.lifetime.start.p0"
          [((Ty.int 64), (Operand.imm (.int 64 (BitVec.ofNat 64 8)))),
            (Ty.ptr, (Operand.reg "%outn205"))],
        Instr.icmp "%cmp207.not" IPred.ult 64 (Operand.reg "%inc.lcssa1130")
          (Operand.reg "%nep")]) hpre hsel (by decide)]
  simp only [State.bindAll, State.bind]
  show denoteCode (stage2NoEventCalls gap)
      [Instr.callVoid "llvm.lifetime.start.p0"
        [((Ty.int 64), (Operand.imm (.int 64 (BitVec.ofNat 64 8)))),
          (Ty.ptr, (Operand.reg "%outn205"))],
       Instr.icmp "%cmp207.not" IPred.ult 64 (Operand.reg "%inc.lcssa1130")
        (Operand.reg "%nep")]
      (stateAt (stringValueHeadCells env inc lane fr sp k terms tok) s) =
    some (stateAt (stringValueHeadEnv env inc lane fr sp k terms tok nep) s)
  rw [stage2NoEventWalk_denote_lifetimeStart (gap := gap)
    (env := stringValueHeadCells env inc lane fr sp k terms tok) (s := s)
    "%outn205" (sz := 8) (a := outn) (stringValueHeadCells_outn env inc lane fr sp k terms tok houtn)]
  rw [stage2NoEventWalk_denote_icmp_reg (calls := stage2NoEventCalls gap)
    (env := stringValueHeadCells env inc lane fr sp k terms tok) (s := s)
    "%cmp207.not" "%inc.lcssa1130" "%nep" .ult 64
    (x := BitVec.ofNat 64 inc) (y := BitVec.ofNat 64 nep)
    (stringValueHeadCells_inc env inc lane fr sp k terms tok)
    (stringValueHeadCells_nep env inc lane fr sp k terms tok hnep)
    (is := [])]
  simp only [denoteCode_nil, stringValueHeadEnv]

/-- **The `string_value` link at the head's edge**: the `phi` run, the lifetime
marker, and the closing entry's test taken to `if.end216`.  The block writes no
memory, so the invariant is transported as-is. -/
theorem link_string_valueHead {gap : Calls} {K : Stage2NoEventWalkCarry} {mem : Mem}
    {s : State} {inc lane fr sp k terms tok nep outn : Nat}
    (h : Stage2NoEventWalkInv K mem s) (hpc : s.pc = "string_value")
    (hpre : s.pre = some "LeafBlock")
    (hinc : lookupName s.env "%inc.peel" = some (.int 64 (BitVec.ofNat 64 inc)))
    (h2 : lookupName s.env "%2" = some (.int 32 (BitVec.ofNat 32 lane)))
    (hidx : lookupName s.env "%idxprom.peel" = some (.int 64 (BitVec.ofNat 64 lane)))
    (hfr : lookupName s.env "%frame.0.ph1402" = some (.int 8 (BitVec.ofNat 8 fr)))
    (hsp : lookupName s.env "%sp.0.ph1403" = some (.int 32 (BitVec.ofNat 32 sp)))
    (hk : lookupName s.env "%k.0.ph1404" = some (.int 64 (BitVec.ofNat 64 k)))
    (hterms : lookupName s.env "%terms.0.ph1407" = some (.int 64 (BitVec.ofNat 64 terms)))
    (htok : lookupName s.env "%tokens.0.ph1408" = some (.int 64 (BitVec.ofNat 64 tok)))
    (houtn : lookupName s.env "%outn205" = some (.ptr outn))
    (hnep : lookupName s.env "%nep" = some (.int 64 (BitVec.ofNat 64 nep)))
    (hy : evalICmp .ult (BitVec.ofNat 64 inc) (BitVec.ofNat 64 nep) = 1) :
    Stage2NoEventWalkLink (stage2NoEventCalls gap) K mem s K
      (stage2NoEventWalkNext
        (stringValueHeadEnv s.env inc lane fr sp k terms tok nep) s "if.end216") := by
  have hcode : denoteCode (stage2NoEventCalls gap) stringValueInstrs (stateAt s.env s) =
      some (stateAt (stringValueHeadEnv s.env inc lane fr sp k terms tok nep) s) :=
    stringValueHead_denote (gap := gap) s.env s hpre hinc h2 hidx hfr hsp hk hterms htok
      houtn hnep
  refine stage2NoEventWalkLink_condbr_true
    (env' := stringValueHeadEnv s.env inc lane fr sp k terms tok nep) h
    (by rw [hpc]; exact stringValueBlock_find) hcode rfl ?_
  rw [stringValueHeadEnv_cmp, hy]

/-! ### The class's entry into its route

The head's own read and `phi` cells supply every value `string_value`'s merge
selects, the base lookups supply `%nep` and `%outn205`, and `k + 1 < nep` is the
string's closing entry being a real entry.  The chain is the dispatch row
(`stage2NoEventRow_string`) and the merge's link, and it ends at `if.end216`'s
entry, where the body's route begins. -/

/-- A base cell's value at a head. -/
theorem Stage2NoEventWalkHead.baseLookup {K : Stage2NoEventWalkCarry} {mem : Mem}
    {k : Nat} {s : State} (h : Stage2NoEventWalkHead K mem k s) {n : String} {v : Value}
    (hv : (n, v) ∈ stage2NoEventWalkBaseValues K) : lookupName s.env n = some v :=
  h.baseLookups n v hv

/-- The `LeafBlock` handoff's two cells over a state's environment. -/
theorem stage2NoEventWalkStringB_leafEnv_lookup {s : State} {n : String} {v : Value}
    (h1 : "%SwitchLeaf" ≠ n) (h2 : "%Pivot6" ≠ n)
    (h : lookupName s.env n = some v) :
    lookupName (("%SwitchLeaf", .int 1 (1 : BitVec 1)) ::
      ("%Pivot6", .int 1 (1 : BitVec 1)) :: s.env) n = some v :=
  lookupName_cons_other _ _ _ h1 (lookupName_cons_other _ _ _ h2 h)

/-- **The head's string entry**: the dispatch and the `string_value` merge at the
head's own values, to `if.end216`'s entry.  `hk1` is the closing quote's entry
being below the entry count — the class's continuation condition. -/
theorem stage2NoEventWalkStringB_entry {gap : Calls} {K : Stage2NoEventWalkCarry}
    {mem : Mem} {k : Nat} {s : State}
    (h : Stage2NoEventWalkHead K mem k s) {lane : Nat} {byte : UInt8}
    (hent : K.ent[k]? = some lane) (hbs : K.bs[lane]? = some byte)
    (h34 : byte.toNat = 34) (hk1 : k + 1 < K.nep) :
    ∃ (fr sp : Nat),
      Stage2NoEventWalkChain (stage2NoEventCalls gap) mem K s K
        (stage2NoEventWalkAt
          (stringValueHeadEnv
            (("%SwitchLeaf", .int 1 1) :: ("%Pivot6", .int 1 1) :: s.env)
            (k + 1) lane fr sp k K.terms K.tok K.nep) s
          "if.end216" "string_value") := by
  -- the head's read and `phi` cells
  have hstage := stage2NoEventWalkStringB_headStaging h hent hbs
  obtain ⟨-, h3, h2, hidx, hinc, -, -, -⟩ := hstage
  obtain ⟨sp, fr, one, wide, hsp, hfr, -, -, -, -⟩ := h.spPhi
  have hk := h.kEq
  have hterms := h.termsPhi
  have htok := h.tokensPhi
  -- the base parameters at the head
  have hnep : lookupName s.env "%nep" = some (.int 64 (BitVec.ofNat 64 K.nep)) :=
    h.baseLookup (by
      simp [stage2NoEventWalkBaseValues, stage2NoEventWalkParamEntries])
  have houtn : lookupName s.env "%outn205" = some (.ptr (K.next0 + 16)) :=
    h.baseLookup (by
      simp [stage2NoEventWalkBaseValues, stage2NoEventWalkBaseCellValues, entryCells1,
        entryCells2, entryCells3, entryCells4, preHeaderCells])
  -- the dispatch, at the head's own byte
  have h3' : lookupName s.env "%3" = some (.int 8 (BitVec.ofNat 8 34)) := by
    rw [h3, h34]
  have hrow := stage2NoEventRow_string (calls := stage2NoEventCalls gap) h.inv h.pc h3'
  -- the closing entry's test, taken
  have hguard : evalICmp .ult (BitVec.ofNat 64 (k + 1)) (BitVec.ofNat 64 K.nep) = 1 :=
    stage2NoEventWalkStringB_ult (Nat.lt_trans hk1 h.inv.nepLt) h.inv.nepLt hk1
  let S1 := stage2NoEventWalkAt
    (("%SwitchLeaf", .int 1 1) :: ("%Pivot6", .int 1 1) :: s.env) s
    "string_value" "LeafBlock"
  have hlink : Stage2NoEventWalkLink (stage2NoEventCalls gap) K mem S1 K
      (stage2NoEventWalkNext
        (stringValueHeadEnv
          (("%SwitchLeaf", .int 1 1) :: ("%Pivot6", .int 1 1) :: s.env)
          (k + 1) lane fr sp k K.terms K.tok K.nep) S1 "if.end216") :=
    link_string_valueHead (gap := gap) hrow.inv (by simp only [S1, stage2NoEventWalkAt])
      (by simp only [S1, stage2NoEventWalkAt])
      (stage2NoEventWalkStringB_leafEnv_lookup (by decide) (by decide) hinc)
      (stage2NoEventWalkStringB_leafEnv_lookup (by decide) (by decide) h2)
      (stage2NoEventWalkStringB_leafEnv_lookup (by decide) (by decide) hidx)
      (stage2NoEventWalkStringB_leafEnv_lookup (by decide) (by decide) hfr)
      (stage2NoEventWalkStringB_leafEnv_lookup (by decide) (by decide) hsp)
      (stage2NoEventWalkStringB_leafEnv_lookup (by decide) (by decide) hk)
      (stage2NoEventWalkStringB_leafEnv_lookup (by decide) (by decide) hterms)
      (stage2NoEventWalkStringB_leafEnv_lookup (by decide) (by decide) htok)
      (stage2NoEventWalkStringB_leafEnv_lookup (by decide) (by decide) houtn)
      (stage2NoEventWalkStringB_leafEnv_lookup (by decide) (by decide) hnep) hguard
  refine ⟨fr, sp, ?_⟩
  simpa only [S1, stage2NoEventWalkAt, stage2NoEventWalkNext] using
    (Stage2NoEventWalkChain.trans hrow
      (Stage2NoEventWalkChain.tail hlink (Stage2NoEventWalkChain.nil hlink.inv')))

/-! ### The class's event and token

A string entry is one record and one token.  The record's field is the arena
cursor — the head's own `%alen.0.ph1405` cell — its length is the decoded body's
byte count the callee wrote at `%outn205`, and its code points are the body's
decode.  The token is the span between the entry's quote and the closing one. -/

/-- The record's `tag + len + payload` at a string event. -/
theorem ConsumerEvent.terms_str_false (len field : Nat) (cs : List Nat) :
    ConsumerEvent.terms (ConsumerEvent.str false len field cs) = 6 + len + field := by
  simp [ConsumerEvent.terms, ConsumerEvent.str, EventRecord.tagStr]

/-- **The class's relation at the walk's arena form**: the body the route decoded
into the arena at the cursor is the record's field, and the document's quote and
the token's span are the entry's. -/
theorem stage2NoEventWalkStringB_relationArena
    {K : Stage2NoEventWalkCarry} {lane nextLane len : Nat} {body : List UInt8}
    {cs : List Nat}
    (hquote : K.bs[lane]? = some (34 : UInt8))
    (hspan : lane + 2 ≤ nextLane + 1)
    (hcode : bodyCodePoints K.bs ⟨lane, nextLane + 1⟩ = some cs)
    (hbelow : K.arena.length < 2 ^ 63)
    (hdecode : escapeCodePoints (((K.arena ++ body).drop K.arena.length).take len) =
      some cs) :
    Stage2NoEvent K.bs (K.arena ++ body)
      [ConsumerEvent.str false len K.arena.length cs] [Token.string ⟨lane, nextLane + 1⟩] :=
  Stage2NoEvent.strArena hquote hspan hcode hbelow (by simpa using hdecode)
    Stage2NoEvent.nil

/-- **The class's relation at the document form**: the body read straight out of
the document's quote gives the same code points, so the plain record is the same
token's. -/
theorem stage2NoEventWalkStringB_relationPlain
    {K : Stage2NoEventWalkCarry} {lane nextLane len : Nat} {cs : List Nat}
    (hquote : K.bs[lane]? = some (34 : UInt8))
    (hstop : nextLane + 1 = lane + 2 + len)
    (hbody : escapeCodePoints ((K.bs.drop (lane + 1)).take len) = some cs)
    (hcode : bodyCodePoints K.bs ⟨lane, nextLane + 1⟩ = some cs) :
    Stage2NoEvent K.bs K.arena
      [ConsumerEvent.str false len (plainSpan (lane + 1)) cs]
      [Token.string ⟨lane, nextLane + 1⟩] :=
  Stage2NoEvent.strPlain hquote hstop hbody hcode Stage2NoEvent.nil

/-- The empty body decodes to no code points. -/
theorem stage2NoEventWalkStringB_escapeCodePoints_nil : escapeCodePoints [] = some [] := rfl

/-- **The empty string's relation**: the plain record at `len = 0` — its field is
the document body's first byte with the top bit set, its code points are none, and
the token's span is the entry's two quotes, two bytes apart. -/
theorem stage2NoEventWalkStringB_relationPlainEmpty
    {K : Stage2NoEventWalkCarry} {lane : Nat}
    (hquote : K.bs[lane]? = some (34 : UInt8))
    (hcode : bodyCodePoints K.bs ⟨lane, lane + 2⟩ = some []) :
    Stage2NoEvent K.bs K.arena
      [ConsumerEvent.str false 0 (plainSpan (lane + 1)) []] [Token.string ⟨lane, lane + 2⟩] :=
  Stage2NoEvent.strPlain hquote (by simp)
    (by simpa using stage2NoEventWalkStringB_escapeCodePoints_nil) hcode Stage2NoEvent.nil

/-- **The carry the string class's step delivers**: one event counted, the
record's contribution added, the decoded body appended to the arena, and the
arena word advanced by that body's byte sum modulo a word. -/
def stage2NoEventWalkStringCarry (K : Stage2NoEventWalkCarry) (len : Nat)
    (body : List UInt8) : Stage2NoEventWalkCarry :=
  { K with tok := K.tok + 1,
           terms := K.terms + (EventRecord.tagStr + len + K.arena.length),
           arena := K.arena ++ body,
           arenaWord := (K.arenaWord + byteSum body) % 2 ^ 64 }

/-- The class's step counts one token. -/
theorem stage2NoEventWalkStringCarry_tok (K : Stage2NoEventWalkCarry) (len : Nat)
    (body : List UInt8) :
    (stage2NoEventWalkStringCarry K len body).tok = K.tok + 1 := rfl

/-- The class's step's terms contribution is the record's `tag + len + payload`. -/
theorem stage2NoEventWalkStringCarry_terms (K : Stage2NoEventWalkCarry) (len : Nat)
    (body : List UInt8) (cs : List Nat) :
    (stage2NoEventWalkStringCarry K len body).terms =
      K.terms + ConsumerEvent.terms (ConsumerEvent.str false len K.arena.length cs) := by
  simp only [stage2NoEventWalkStringCarry, ConsumerEvent.terms_str_false, EventRecord.tagStr]

/-- The class's step extends the arena. -/
theorem stage2NoEventWalkStringCarry_arena (K : Stage2NoEventWalkCarry) (len : Nat)
    (body : List UInt8) :
    (stage2NoEventWalkStringCarry K len body).arena = K.arena ++ body := rfl

/-- The class's step advances the arena word by the body's byte sum. -/
theorem stage2NoEventWalkStringCarry_arenaWord (K : Stage2NoEventWalkCarry) (len : Nat)
    (body : List UInt8) :
    (stage2NoEventWalkStringCarry K len body).arenaWord =
      (K.arenaWord + byteSum body) % 2 ^ 64 := rfl

/-- **The empty string's carry**: one token counted, the plain record's
contribution (`tag + 0 + plainSpan`, which is the walk's `%add260`), and the arena
and its word where they were — form 1 writes nothing to the arena and the
byte-sum loop adds nothing. -/
def stage2NoEventWalkStringCarryPlain (K : Stage2NoEventWalkCarry) (lane : Nat) :
    Stage2NoEventWalkCarry :=
  { K with tok := K.tok + 1,
           terms := K.terms + (EventRecord.tagStr + 0 + plainSpan (lane + 1)),
           arena := K.arena,
           arenaWord := K.arenaWord }

/-- The empty string's step counts one token. -/
theorem stage2NoEventWalkStringCarryPlain_tok (K : Stage2NoEventWalkCarry) (lane : Nat) :
    (stage2NoEventWalkStringCarryPlain K lane).tok = K.tok + 1 := rfl

/-- The empty string's step's contribution is its record's `tag + len + payload`. -/
theorem stage2NoEventWalkStringCarryPlain_terms (K : Stage2NoEventWalkCarry) (lane : Nat) :
    (stage2NoEventWalkStringCarryPlain K lane).terms =
      K.terms + ConsumerEvent.terms
        (ConsumerEvent.str false 0 (plainSpan (lane + 1)) []) := by
  simp only [stage2NoEventWalkStringCarryPlain, ConsumerEvent.terms_str_false,
    EventRecord.tagStr]

/-- The empty string's step leaves the arena where it was. -/
theorem stage2NoEventWalkStringCarryPlain_arena (K : Stage2NoEventWalkCarry) (lane : Nat) :
    (stage2NoEventWalkStringCarryPlain K lane).arena = K.arena := rfl

/-- The empty string's step leaves the arena word where it was. -/
theorem stage2NoEventWalkStringCarryPlain_arenaWord (K : Stage2NoEventWalkCarry) (lane : Nat) :
    (stage2NoEventWalkStringCarryPlain K lane).arenaWord = K.arenaWord := rfl

/-- The class's step leaves the document and the scratch buffer where they were. -/
theorem stage2NoEventWalkStringCarry_static (K : Stage2NoEventWalkCarry) (len : Nat)
    (body : List UInt8) :
    (stage2NoEventWalkStringCarry K len body).bs = K.bs ∧
      (stage2NoEventWalkStringCarry K len body).scratch = K.scratch ∧
      (stage2NoEventWalkStringCarry K len body).a12 = K.a12 :=
  ⟨rfl, rfl, rfl⟩

/-! ### The target trace

The class's step turns the source's prefix trace into the target's: the prefix's
relation is transported along the arena's extension, the class's event and token
are appended, and the two counts are the target carry's. -/

/-- **The string class's trace step**: from the head's prefix trace and the
class's own record and token, the target trace at the class's carry. -/
theorem Stage2NoEventWalkTrace.stringStep {K : Stage2NoEventWalkCarry}
    (htr : Stage2NoEventWalkTrace K) {lane nextLane len : Nat} {body : List UInt8}
    {cs : List Nat}
    (hquote : K.bs[lane]? = some (34 : UInt8))
    (hspan : lane + 2 ≤ nextLane + 1)
    (hcode : bodyCodePoints K.bs ⟨lane, nextLane + 1⟩ = some cs)
    (hbelow : K.arena.length < 2 ^ 63)
    (hbodyLen : body.length = len)
    (hdecode : escapeCodePoints (((K.arena ++ body).drop K.arena.length).take len) =
      some cs) :
    Stage2NoEventWalkTrace (stage2NoEventWalkStringCarry K len body) := by
  cases htr with
  | intro obs toks rel obsLen termsEq arenaBound =>
    -- the prefix reads the extended arena
    have hprefix : Stage2NoEvent K.bs (K.arena ++ body) obs toks :=
      Stage2NoEvent.arena_append rel arenaBound
    -- the class's own record and token
    have hone : Stage2NoEvent K.bs (K.arena ++ body)
        [ConsumerEvent.str false len K.arena.length cs]
        [Token.string ⟨lane, nextLane + 1⟩] :=
      Stage2NoEvent.strArena hquote hspan hcode hbelow
        (by simpa using hdecode) Stage2NoEvent.nil
    have hrel : Stage2NoEvent K.bs (K.arena ++ body)
        (obs ++ [ConsumerEvent.str false len K.arena.length cs])
        (toks ++ [Token.string ⟨lane, nextLane + 1⟩]) :=
      Stage2NoEvent.append hprefix hone
    refine Stage2NoEventWalkTrace.intro
      (obs ++ [ConsumerEvent.str false len K.arena.length cs])
      (toks ++ [Token.string ⟨lane, nextLane + 1⟩]) ?_ ?_ ?_ ?_
    · simpa only [stage2NoEventWalkStringCarry] using hrel
    · simp only [stage2NoEventWalkStringCarry, List.length_append, List.length_cons,
        List.length_nil, obsLen]
    · rw [stage2NoEventWalkStringCarry_terms, List.map_append, List.sum_append,
        List.map_singleton, List.sum_singleton, termsEq]
    · -- the span bound: the prefix's records at the old arena, this one at its own
      intro e he htag hpay
      rw [List.mem_append, List.mem_singleton] at he
      rcases he with he | rfl
      · have hle := arenaBound e he htag hpay
        simp only [stage2NoEventWalkStringCarry, List.length_append, hbodyLen]
        omega
      · simp only [stage2NoEventWalkStringCarry, List.length_append, hbodyLen,
          ConsumerEvent.str]
        omega

/-- **The empty string's trace step**: the plain record at `len = 0` appended to
the prefix.  The arena does not move, so the prefix's relation is the source's own
and the span bound is the source's; the new record's field is above the top bit, so
the bound's implication is vacuous at it. -/
theorem Stage2NoEventWalkTrace.stringPlainStep {K : Stage2NoEventWalkCarry}
    (htr : Stage2NoEventWalkTrace K) {lane : Nat}
    (hquote : K.bs[lane]? = some (34 : UInt8))
    (hcode : bodyCodePoints K.bs ⟨lane, lane + 2⟩ = some []) :
    Stage2NoEventWalkTrace (stage2NoEventWalkStringCarryPlain K lane) := by
  cases htr with
  | intro obs toks rel obsLen termsEq arenaBound =>
    have hone : Stage2NoEvent K.bs K.arena
        [ConsumerEvent.str false 0 (plainSpan (lane + 1)) []] [Token.string ⟨lane, lane + 2⟩] :=
      stage2NoEventWalkStringB_relationPlainEmpty hquote hcode
    have hrel : Stage2NoEvent K.bs K.arena
        (obs ++ [ConsumerEvent.str false 0 (plainSpan (lane + 1)) []])
        (toks ++ [Token.string ⟨lane, lane + 2⟩]) :=
      Stage2NoEvent.append rel hone
    refine Stage2NoEventWalkTrace.intro
      (obs ++ [ConsumerEvent.str false 0 (plainSpan (lane + 1)) []])
      (toks ++ [Token.string ⟨lane, lane + 2⟩]) ?_ ?_ ?_ ?_
    · simpa only [stage2NoEventWalkStringCarryPlain] using hrel
    · simp only [stage2NoEventWalkStringCarryPlain, List.length_append, List.length_cons,
        List.length_nil, obsLen]
    · rw [stage2NoEventWalkStringCarryPlain_terms, List.map_append, List.sum_append,
        List.map_singleton, List.sum_singleton, termsEq]
    · -- the span bound: the prefix's records unchanged, the plain record vacuous
      intro e he htag hpay
      rw [List.mem_append, List.mem_singleton] at he
      rcases he with he | rfl
      · exact arenaBound e he htag hpay
      · simp only [ConsumerEvent.str] at hpay
        exact absurd hpay (plainSpan_not_lt (lane + 1))

/-! ### The class's one-step export

The class's relation, the target's trace, and the carry's delta as one statement.
The source trace is the head's prefix; the target's is the same prefix with this
record and token appended, read at the carry the class's registers move to. -/

/-- **The string class's one step.**  `htr` is the head's prefix trace; the
route's own reads are the body's length, its decode and its arena placement, the
entry's two quote positions, and the arena's room for the body.  The class
consumes one token and one event, the relation holds at the extended arena, the
target trace is the source's with this step appended, and the carry moves by the
walk's four registers' deltas. -/
theorem stage2NoEventWalkStringB_oneStep
    {K : Stage2NoEventWalkCarry}
    (htr : Stage2NoEventWalkTrace K)
    {lane nextLane len : Nat} {body : List UInt8} {cs : List Nat}
    (hquote : K.bs[lane]? = some (34 : UInt8))
    (hspan : lane + 2 ≤ nextLane + 1)
    (hcode : bodyCodePoints K.bs ⟨lane, nextLane + 1⟩ = some cs)
    (hbelow : K.arena.length < 2 ^ 63)
    (hbodyLen : body.length = len)
    (hdecode : escapeCodePoints (((K.arena ++ body).drop K.arena.length).take len) =
      some cs) :
    ∃ (K' : Stage2NoEventWalkCarry),
      K' = stage2NoEventWalkStringCarry K len body ∧
      Stage2NoEvent K.bs K'.arena
        [ConsumerEvent.str false len K.arena.length cs]
        [Token.string ⟨lane, nextLane + 1⟩] ∧
      Stage2NoEventWalkTrace K' ∧
      K'.tok = K.tok + 1 ∧
      K'.terms = K.terms +
        ConsumerEvent.terms (ConsumerEvent.str false len K.arena.length cs) ∧
      K'.arena = K.arena ++ body ∧
      K'.arenaWord = (K.arenaWord + byteSum body) % 2 ^ 64 := by
  refine ⟨stage2NoEventWalkStringCarry K len body, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact stage2NoEventWalkStringB_relationArena hquote hspan hcode hbelow hdecode
  · exact Stage2NoEventWalkTrace.stringStep htr hquote hspan hcode hbelow hbodyLen hdecode
  · exact stage2NoEventWalkStringCarry_tok K len body
  · exact stage2NoEventWalkStringCarry_terms K len body cs
  · exact stage2NoEventWalkStringCarry_arena K len body
  · exact stage2NoEventWalkStringCarry_arenaWord K len body

/-- **The string class's step at a head**: the head's class staging, its arena
cursor cell, and the one-step export.  The head's byte is the token's opening
quote (`h34`); the route reads the closing entry's position, and the carry's
arena cursor is the head's own `%alen.0.ph1405`. -/
theorem stage2NoEventWalkStringB_step
    {K : Stage2NoEventWalkCarry} {mem : Mem} {k : Nat} {s : State}
    (h : Stage2NoEventWalkHead K mem k s)
    (htr : Stage2NoEventWalkTrace K)
    {lane : Nat} {byte : UInt8} {nextLane len : Nat} {body : List UInt8} {cs : List Nat}
    (hent : K.ent[k]? = some lane) (hbs : K.bs[lane]? = some byte)
    (h34 : byte.toNat = 34)
    (hspan : lane + 2 ≤ nextLane + 1)
    (hcode : bodyCodePoints K.bs ⟨lane, nextLane + 1⟩ = some cs)
    (hbelow : K.arena.length < 2 ^ 63)
    (hbodyLen : body.length = len)
    (hdecode : escapeCodePoints (((K.arena ++ body).drop K.arena.length).take len) =
      some cs) :
    Nonempty (Stage2NoEventHeadClass byte.toNat) ∧
      lookupName s.env "%3" = some (.int 8 (BitVec.ofNat 8 34)) ∧
      lookupName s.env "%alen.0.ph1405" = some (.int 64 (BitVec.ofNat 64 K.arena.length)) ∧
      ∃ (K' : Stage2NoEventWalkCarry),
        K' = stage2NoEventWalkStringCarry K len body ∧
        Stage2NoEvent K.bs K'.arena
          [ConsumerEvent.str false len K.arena.length cs]
          [Token.string ⟨lane, nextLane + 1⟩] ∧
        Stage2NoEventWalkTrace K' ∧
        K'.tok = K.tok + 1 ∧
        K'.terms = K.terms +
          ConsumerEvent.terms (ConsumerEvent.str false len K.arena.length cs) ∧
        K'.arena = K.arena ++ body ∧
        K'.arenaWord = (K.arenaWord + byteSum body) % 2 ^ 64 := by
  have hstage := stage2NoEventWalkStringB_headStaging h hent hbs
  obtain ⟨hclass, h3, -⟩ := hstage
  have h3' : lookupName s.env "%3" = some (.int 8 (BitVec.ofNat 8 34)) := by
    rw [h3, h34]
  have hbyte : byte = (34 : UInt8) := UInt8.toNat_inj.mp h34
  have hquote : K.bs[lane]? = some (34 : UInt8) := by rw [hbs, hbyte]
  exact ⟨hclass, h3', h.alenPhi,
    stage2NoEventWalkStringB_oneStep htr hquote hspan hcode hbelow hbodyLen hdecode⟩

/-! ### Axiom footprints -/

#print axioms stage2NoEventWalkStringB_headStaging
#print axioms stringValueHead_denote
#print axioms link_string_valueHead
#print axioms Stage2NoEventWalkHead.baseLookup
#print axioms stage2NoEventWalkStringB_leafEnv_lookup
#print axioms stage2NoEventWalkStringB_entry
#print axioms ConsumerEvent.terms_str_false
#print axioms stage2NoEventWalkStringB_relationArena
#print axioms stage2NoEventWalkStringB_relationPlain
#print axioms stage2NoEventWalkStringB_relationPlainEmpty
#print axioms stage2NoEventWalkStringCarryPlain_terms
#print axioms Stage2NoEventWalkTrace.stringStep
#print axioms Stage2NoEventWalkTrace.stringPlainStep
#print axioms stage2NoEventWalkStringB_oneStep
#print axioms stage2NoEventWalkStringB_step

end LeanLLVM.Refinement
