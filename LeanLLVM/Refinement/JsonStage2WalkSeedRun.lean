/-
The stage-2 walk's seed run: `entry`, the preheader, and the header's first pass
as control steps.

`walkEntry_denote` (`JsonStage2WalkRun`) states the entry block's fifty-seven
instructions as one `denoteCode` equality.  This module turns that equality and
the two blocks after it into the steps that reach `NodeBlock21`, which is where
`WalkSeedState` (`JsonStage2WalkScope`) is asserted:

* `walkEntry_step` — the entry block's step, in both arms of its own test: the
  terminator is `condbr %cmp.i247.not, if.then492.i, while.body.i.lr.ph`, and the
  test bit is `%nep == 0`, so the zero arm jumps to `if.then492.i` and the
  non-zero arm to the preheader.  The statement is a single `if` on `nep`, so one
  theorem carries both.
* `walkPreheader_denote` — `while.body.i.lr.ph`'s five literal-offset
  `getelementptr`s, at a state's own environment, and `walkPreheader_step` — the
  unconditional edge into `while.body.i`.
* `whileBodyFirst_denote` — `while.body.i`'s leading `phi` run selecting the
  preheader's arm (`%k.0.i249 = 0`, `%sp.i.0248 = 0`), then the lane and document
  loads and the cursor store, and `walkHeader_step` — the edge into
  `NodeBlock21`.

Each step is stated at a `denoteCode` equality the caller supplies, so the run
composes with the block equalities the rest of the tree proves.  `runFuel` forms
(`walkEntry_runFuel`, `walkPreheader_runFuel`, `walkHeader_runFuel`) shift one
fuel unit per step, which is the shape a prefix is composed in.

The state's *memory* at `NodeBlock21` is `walkEntryMem`: the entry run's named
folds plus the header's cursor word.  Its five log clauses are proved at it
(`walkEntryMem_hash`, `_len`, `_cap`, `_alen`, `_acap`), read through the folds
by their extents.  What remains for `WalkSeedState`'s production is the register
half — the lookups the header's and the preheader's cells bind, which `WalkPtrs`
and `WalkRegs` name — and the two claims over the run's write set: the staged
objects' presence and the frame.  Those are the open row; the steps, their
`runFuel` forms and the memory clauses are here.
-/
import LeanLLVM.Refinement.JsonStage2WalkRun

set_option autoImplicit false

namespace LeanLLVM.Refinement
open LeanLLVM
open LeanLLVM.Refinement.JsonStage2IR
open LeanLLVM.Refinement.BlockEval
open LeanLLVM.Refinement.JsonEntrySteps (denoteCode_lookupName)
open LeanLLVM.Refinement.JsonScanLane

namespace WalkScope

/-! ### The entry block's step -/

/-- The entry block's branch target, at the state its run leaves: `if.then492.i`
when the entry count is zero and the preheader otherwise. -/
def walkEntryJump (s : State) (nep : Nat) : State :=
  { s with
    pc := if nep = 0 then "if.then492.i" else "while.body.i.lr.ph"
    pre := some "entry" }

/-- `BitVec.ofNat 64` is zero exactly when the `Nat` is. -/
theorem walkOfNat64_eq_zero {n : Nat} (hn : n < 2 ^ 64) :
    BitVec.ofNat 64 n = 0 ↔ n = 0 := by
  constructor
  · intro h
    have htoNat : (BitVec.ofNat 64 n).toNat = n := walkToNat_ofNat64 hn
    rw [h] at htoNat
    simpa using htoNat.symm
  · intro h
    subst h
    rfl

/-- **The entry block's step**, in both arms of its own test.  `%cmp.i247.not`
is `%nep == 0` (`walkEntryEnv4`), and the terminator branches on it: the zero arm
jumps to the flush arm, the non-zero arm to the preheader. -/
theorem walkEntry_step (s : State) (hpc : s.pc = "entry") {s₁ : State} {nep : Nat}
    (hden : denoteCode (stage2Calls stage2SubCalls) walkEntryInstrs s = some s₁)
    (hne : lookupName s₁.env "%cmp.i247.not" =
      some (.int 1 (evalICmp .eq (BitVec.ofNat 64 nep) (BitVec.ofNat 64 0))))
    (hne64 : nep < 2 ^ 64) (hpc₁ : s₁.pc = s.pc) :
    step (stage2Calls stage2SubCalls) stage2Body s = .jump (walkEntryJump s₁ nep) := by
  have hfind : stage2Body.findBlock s.pc = some walkEntryBlock := by
    rw [hpc]; exact walkEntryBlock_find
  simp only [LeanLLVM.step, hfind, walkEntryBlock, hden]
  dsimp only [execTerm]
  rw [show evalOperand s₁ (Operand.reg "%cmp.i247.not") =
      some (.int 1 (evalICmp .eq (BitVec.ofNat 64 nep) (BitVec.ofNat 64 0))) by
    simp [evalOperand, hne]]
  by_cases h0 : nep = 0
  · have hbit : evalICmp .eq (BitVec.ofNat 64 nep) (BitVec.ofNat 64 0) = 1 :=
      (evalICmp_eq_one_iff _ _).2 (by simpa using (walkOfNat64_eq_zero hne64).2 h0)
    rw [hbit]
    simp [walkEntryJump, h0, hpc, hpc₁]
  · have hnz : (BitVec.ofNat 64 nep) ≠ (0 : BitVec 64) :=
      fun h => h0 ((walkOfNat64_eq_zero hne64).1 h)
    have hbit : evalICmp .eq (BitVec.ofNat 64 nep) (BitVec.ofNat 64 0) = 0 :=
      (evalICmp_eq_zero_iff _ _).2 (by simpa using hnz)
    rw [hbit]
    simp [walkEntryJump, h0, hpc, hpc₁]

/-- **The entry block's one-step prefix.** -/
theorem walkEntry_runFuel (s : State) (hpc : s.pc = "entry") {s₁ : State} {nep : Nat}
    (hden : denoteCode (stage2Calls stage2SubCalls) walkEntryInstrs s = some s₁)
    (hne : lookupName s₁.env "%cmp.i247.not" =
      some (.int 1 (evalICmp .eq (BitVec.ofNat 64 nep) (BitVec.ofNat 64 0))))
    (hne64 : nep < 2 ^ 64) (hpc₁ : s₁.pc = s.pc) (n : Nat) :
    runFuel (stage2Calls stage2SubCalls) (1 + n) stage2Body s =
      runFuel (stage2Calls stage2SubCalls) n stage2Body (walkEntryJump s₁ nep) := by
  have hs := walkEntry_step s hpc hden hne hne64 hpc₁
  rw [show 1 + n = n + 1 from by omega]
  simp only [runFuel, hs]

/-! ### The preheader -/

/-- **`while.body.i.lr.ph`'s run** at a state's own environment: five
literal-offset `getelementptr`s, `%k11.i` first (`%c.i + 32`). -/
theorem walkPreheader_denote {calls : Calls} (s : State)
    {c z tok : Nat}
    (hc : lookupName s.env "%c.i" = some (.ptr c))
    (hz : lookupName s.env "%z" = some (.ptr z))
    (ht : lookupName s.env "%t352.i" = some (.ptr tok)) :
    denoteCode calls walkPreheaderInstrs s =
      some (s.bind "%k11.i" (.ptr (c + 32)) |>.bind "%h1.i.i.i51" (.ptr (z + 24))
        |>.bind "%gap.i" (.ptr (tok + 20)) |>.bind "%end.i" (.ptr (tok + 8))
        |>.bind "%kind404.i" (.ptr (tok + 16))) := by
  simp only [walkPreheaderInstrs]
  rw [walkDenoteCode_gep8_imm (calls := calls) (s := s) (d := "%k11.i") (base := "%c.i")
    (a := c) (c := 32) hc (by decide)]
  rw [walkDenoteCode_gep8_imm (calls := calls)
    (s := s.bind "%k11.i" (.ptr (c + 32))) (d := "%h1.i.i.i51") (base := "%z")
    (a := z) (c := 24)
    (by simp only [State.bind]; repeat rw [lookupName_cons_ne _ _ (by decide)]; exact hz)
    (by decide)]
  rw [walkDenoteCode_gep8_imm (calls := calls)
    (s := s.bind "%k11.i" (.ptr (c + 32)) |>.bind "%h1.i.i.i51" (.ptr (z + 24)))
    (d := "%gap.i") (base := "%t352.i") (a := tok) (c := 20)
    (by simp only [State.bind]; repeat rw [lookupName_cons_ne _ _ (by decide)]; exact ht)
    (by decide)]
  rw [walkDenoteCode_gep8_imm (calls := calls)
    (s := s.bind "%k11.i" (.ptr (c + 32)) |>.bind "%h1.i.i.i51" (.ptr (z + 24))
      |>.bind "%gap.i" (.ptr (tok + 20)))
    (d := "%end.i") (base := "%t352.i") (a := tok) (c := 8)
    (by simp only [State.bind]; repeat rw [lookupName_cons_ne _ _ (by decide)]; exact ht)
    (by decide)]
  rw [walkDenoteCode_gep8_imm (calls := calls)
    (s := s.bind "%k11.i" (.ptr (c + 32)) |>.bind "%h1.i.i.i51" (.ptr (z + 24))
      |>.bind "%gap.i" (.ptr (tok + 20)) |>.bind "%end.i" (.ptr (tok + 8)))
    (d := "%kind404.i") (base := "%t352.i") (a := tok) (c := 16)
    (by simp only [State.bind]; repeat rw [lookupName_cons_ne _ _ (by decide)]; exact ht)
    (by decide)]
  rfl

/-- **The preheader's step**: the unconditional edge into `while.body.i`. -/
theorem walkPreheader_step {s s₁ : State}
    (hpc : s.pc = "while.body.i.lr.ph")
    (hden : denoteCode (stage2Calls stage2SubCalls) walkPreheaderInstrs s = some s₁)
    (hpc₁ : s₁.pc = s.pc) :
    step (stage2Calls stage2SubCalls) stage2Body s =
      .jump { s₁ with pc := "while.body.i", pre := some "while.body.i.lr.ph" } := by
  have hfind : stage2Body.findBlock s.pc = some walkPreheaderBlock := by
    rw [hpc]; exact walkPreheaderBlock_find
  simp only [LeanLLVM.step, hfind, walkPreheaderBlock, hden]
  simp only [execTerm, hpc, hpc₁]

/-- **The preheader's one-step prefix.** -/
theorem walkPreheader_runFuel {s s₁ : State}
    (hpc : s.pc = "while.body.i.lr.ph")
    (hden : denoteCode (stage2Calls stage2SubCalls) walkPreheaderInstrs s = some s₁)
    (hpc₁ : s₁.pc = s.pc) (n : Nat) :
    runFuel (stage2Calls stage2SubCalls) (1 + n) stage2Body s =
      runFuel (stage2Calls stage2SubCalls) n stage2Body
        { s₁ with pc := "while.body.i", pre := some "while.body.i.lr.ph" } := by
  have hs := walkPreheader_step hpc hden hpc₁
  rw [show 1 + n = n + 1 from by omega]
  simp only [runFuel, hs]

/-! ### The header's first pass -/

/-- **`while.body.i`'s first pass**: both `phi`s take the preheader's arm, so the
index and the depth are zero; then the block count into `%inc.i`, the lane at the
first entry position, the document byte that lane selects, and the cursor store.
The header's latch-entered run is `whileBody_denote` (`JsonStage2WalkScope`); the
difference is exactly the `phi` selection, which is why this is the first pass and
not a special case of that theorem's hypotheses. -/
theorem whileBodyFirst_denote {calls : Calls} (env : Env) (s : State)
    {ep b c q : Nat} {bs : List UInt8} {bt : UInt8}
    (h5 : lookupName env "%5" = some (.ptr ep))
    (h3 : lookupName env "%3" = some (.ptr b))
    (hK : lookupName env "%k11.i" = some (.ptr (c + 32)))
    (hpre : s.pre = some "while.body.i.lr.ph")
    (hread : readBytes s.mem ep 4 = some bs) (hbs : bytesToNat bs = q)
    (hdoc : readBytes s.mem (b + q) 1 = some [bt])
    (hq : q < 2 ^ 32) :
    denoteCode calls whileBodyInstrs (stateAt env s) =
      some (stateAt (whileBodyOut env 0 0 b ep c q bt)
        { s with mem := writeBytes s.mem (c + 32) (wordBytes 8 1) }) := by
  simp only [whileBodyInstrs, whileBodyOut]
  walk_eval

/-- **The header's first-pass step**: the edge into `NodeBlock21`. -/
theorem walkHeader_step {s s₁ : State}
    (hpc : s.pc = "while.body.i")
    (hden : denoteCode (stage2Calls stage2SubCalls) whileBodyInstrs s = some s₁)
    (hpc₁ : s₁.pc = s.pc) :
    step (stage2Calls stage2SubCalls) stage2Body s =
      .jump { s₁ with pc := "NodeBlock21", pre := some "while.body.i" } := by
  have hfind : stage2Body.findBlock s.pc = some whileBodyBlock := by
    rw [hpc]; exact whileBody_find
  simp only [LeanLLVM.step, hfind, whileBodyBlock, hden]
  simp only [execTerm, hpc, hpc₁]

/-- **The header's first-pass one-step prefix.** -/
theorem walkHeader_runFuel {s s₁ : State}
    (hpc : s.pc = "while.body.i")
    (hden : denoteCode (stage2Calls stage2SubCalls) whileBodyInstrs s = some s₁)
    (hpc₁ : s₁.pc = s.pc) (n : Nat) :
    runFuel (stage2Calls stage2SubCalls) (1 + n) stage2Body s =
      runFuel (stage2Calls stage2SubCalls) n stage2Body
        { s₁ with pc := "NodeBlock21", pre := some "while.body.i" } := by
  have hs := walkHeader_step hpc hden hpc₁
  rw [show 1 + n = n + 1 from by omega]
  simp only [runFuel, hs]

/-! ### The seed's memory clauses

`walkEntry_denote` leaves the entry run's memory as a nest of named folds; the
header's first pass then writes the cursor word at `%c.i + 32`.  `walkEntryMem`
is that whole memory at the seed's own geometry, and the five clauses
`WalkSeedState` states about the log are read at it: the zeroed hash word at
`%z + 32` and the event cursor, event capacity, arena cursor and arena capacity
at `%z + 8`, `%z + 16`, `%z + 48` and `%z + 56`.

The reads are the entry run's own arithmetic.  The record's staging is a
`stage2WriteStores` fold, so the segment's store list is split at the store the
read names (`readBytes_stage2WriteStores_at`), and the segment's later writes —
the record's memset and its five stores, the two zeroed slots at the call's
cursor, and the header's cursor word — are peeled by their extents: the log's
64 bytes are separate from the cursor record's 1192 (`walkStage_log_sep`, read
off the adapter's `DisjointRegions`) and end at or below the call's cursor
(`WalkStage.sevenEnd`).  The hash word is inside the sixteen-byte `memset` at
`%z + 24`, so its four bytes are a slice of that write
(`walkReadBytes_writeBytes_slice`).

What remains for `WalkSeedState`'s production is then the register half — the
lookups the header's and the preheader's cells bind, which `WalkPtrs` and
`WalkRegs` name — and the two memory claims over the run's write set: the staged
objects' presence and the frame (`UnchangedOutside`).  Those are the next row;
the five reads are here. -/

/-- The entry run's outgoing memory at the seed's own geometry: `s2_init`'s
record, the log's fields and both cursor loads, the cursor record's memset and
five stores, the two zeroed slots, and the header's cursor store. -/
def walkEntryMem {m0 : Mem} (G : WalkGeom m0) (S : WalkStage G) : Mem :=
  writeBytes
    (walkSeg4PostMem (G.next0 + 8) (G.next0 + 12)
      (walkSeg3PostMem G.b G.n G.ep G.nep S.e S.c
        (walkSeg2PostMem S.s S.z G.nep G.xp G.nxp G.dst G.ndst0 G.dstcap G.ev G.nev0
          G.evcap
          (walkSeg2InitMem S.s G.b G.ep (BitVec.ofNat 64 G.n)
            ((BitVec.ofNat 64 G.n + BitVec.ofNat 64 63) >>> 6) m0))))
    (S.c + 32) (wordBytes 8 1)

/-- Every store the cursor record's staging writes lies in the record's own
extent, `[c, c + 1192)`. -/
theorem walkSeg3Stores_bounds (b n ep nep eAddr cAddr : Nat) :
    ∀ st ∈ walkSeg3Stores b n ep nep eAddr cAddr,
      cAddr ≤ st.1 ∧ st.1 + st.2.length ≤ cAddr + 1192 := by
  intro st hst
  simp only [walkSeg3Stores, List.mem_cons, List.not_mem_nil, or_false] at hst
  rcases hst with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    (simp only [natToBytes_length, List.length_replicate, woff_8, woff_16, woff_24,
      woff_40, woff_1112]
     omega)

/-- A read outside every store the cursor record's staging writes is unchanged by
it. -/
theorem readBytes_walkSeg3PostMem_out {m : Mem} {a len b n ep nep eAddr cAddr : Nat}
    (h : ∀ st ∈ walkSeg3Stores b n ep nep eAddr cAddr,
      a + len ≤ st.1 ∨ st.1 + st.2.length ≤ a) :
    readBytes (walkSeg3PostMem b n ep nep eAddr cAddr m) a len = readBytes m a len := by
  show readBytes (stage2WriteStores m (walkSeg3Stores b n ep nep eAddr cAddr)) a len = _
  exact readBytes_stage2WriteStores_of_all_outside _ h

/-- A read outside the two zeroed slots is unchanged by them. -/
theorem readBytes_walkSeg4PostMem_out {m : Mem} {a len root xj : Nat}
    (h1 : a + len ≤ root ∨ root + 4 ≤ a)
    (h2 : a + len ≤ xj ∨ xj + 8 ≤ a) :
    readBytes (walkSeg4PostMem root xj m) a len = readBytes m a len := by
  simp only [walkSeg4PostMem]
  rw [walkReadBytes_writeBytes_outside (start := xj) (v := natToBytes 0 8) h2,
    walkReadBytes_writeBytes_outside (start := root) (v := natToBytes 0 4) h1]

/-- A read outside the header's cursor store is unchanged by it. -/
theorem readBytes_walkHeaderWrite_out {m : Mem} {a len c : Nat}
    (h : a + len ≤ c + 32 ∨ c + 32 + 8 ≤ a) :
    readBytes (writeBytes m (c + 32) (wordBytes 8 1)) a len = readBytes m a len :=
  walkReadBytes_writeBytes_outside (start := c + 32) (v := wordBytes 8 1) h

/-- **The cursor record and the log are separate**, and the log ends at or below
the call's cursor. -/
theorem walkStage_log_sep {m0 : Mem} (G : WalkGeom m0) (S : WalkStage G) :
    (S.z + 64 ≤ S.c ∨ S.c + 1192 ≤ S.z) ∧ S.z + 64 ≤ G.next0 := by
  have hcz : (S.z, stage2LogExtent) ≠ (S.c, stage2CursorExtent) := by
    intro hh
    have h2 := congrArg Prod.snd hh
    simp [stage2LogExtent, stage2CursorExtent] at h2
  have hp := staged_pair (b := G.b) (n := G.n) (ep := G.ep) (nep := G.nep)
    (xp := G.xp) (nxp := G.nxp) (dst := G.dst) (ndst0 := G.ndst0) (ev := G.ev)
    (evcap := G.evcap) (ndst := G.ndst) (nev := G.nev) (err := G.err)
    (c := S.c) (ctype := S.ctype) (cst := S.cst) (tok := S.tok) (sv := S.s)
    (z := S.z) (e := S.e) S.separate
    (by simp [stage2WalkRegions, stage2StagedWrites])
    (by simp [stage2WalkRegions, stage2StagedWrites]) hcz
  refine ⟨by simpa [stage2LogExtent, stage2CursorExtent] using hp, ?_⟩
  simpa [stage2LogExtent] using S.sevenEnd (S.z, stage2LogExtent) (by simp [stage2StagedWrites])

/-- **A read inside the log's extent passes the entry run's later writes.** -/
theorem walkEntryMem_read_out {m0 : Mem} (G : WalkGeom m0) (S : WalkStage G)
    {a len : Nat} (hz0 : S.z ≤ a) (hz1 : a + len ≤ S.z + 64) :
    readBytes (walkEntryMem G S) a len =
      readBytes
        (walkSeg2PostMem S.s S.z G.nep G.xp G.nxp G.dst G.ndst0 G.dstcap G.ev G.nev0
          G.evcap
          (walkSeg2InitMem S.s G.b G.ep (BitVec.ofNat 64 G.n)
            ((BitVec.ofNat 64 G.n + BitVec.ofNat 64 63) >>> 6) m0)) a len := by
  obtain ⟨hcz, hzn⟩ := walkStage_log_sep G S
  show readBytes
      (writeBytes
        (walkSeg4PostMem (G.next0 + 8) (G.next0 + 12)
          (walkSeg3PostMem G.b G.n G.ep G.nep S.e S.c
            (walkSeg2PostMem S.s S.z G.nep G.xp G.nxp G.dst G.ndst0 G.dstcap G.ev G.nev0
              G.evcap
              (walkSeg2InitMem S.s G.b G.ep (BitVec.ofNat 64 G.n)
                ((BitVec.ofNat 64 G.n + BitVec.ofNat 64 63) >>> 6) m0))))
        (S.c + 32) (wordBytes 8 1)) a len = _
  rw [readBytes_walkHeaderWrite_out (by
    rcases hcz with h | h
    · left; omega
    · right; omega)]
  rw [readBytes_walkSeg4PostMem_out (root := G.next0 + 8) (xj := G.next0 + 12)
    (by left; omega) (by left; omega)]
  rw [readBytes_walkSeg3PostMem_out (b := G.b) (n := G.n) (ep := G.ep) (nep := G.nep)
    (eAddr := S.e) (cAddr := S.c) ?_]
  intro st hst
  obtain ⟨hlo, hhi⟩ := walkSeg3Stores_bounds G.b G.n G.ep G.nep S.e S.c st hst
  rcases hcz with h | h <;> omega



/-- A read at a store of the second segment's store list, through the list's
tail. -/
theorem walkSeg2PostMem_read_at {m : Mem}
    {sAddr b ep zAddr nep xp nxp dst v1 dstcap ev v2 evcap : Nat} {n nb : BitVec 64}
    {pre post : List (Nat × List UInt8)} {a len : Nat} {bs : List UInt8}
    (hstores : walkSeg2Stores sAddr zAddr nep xp nxp dst v1 dstcap ev v2 evcap =
      pre ++ (a, bs) :: post)
    (hlen : bs.length = len)
    (hpost : ∀ st ∈ post, a + bs.length ≤ st.1 ∨ st.1 + st.2.length ≤ a) :
    readBytes (walkSeg2PostMem sAddr zAddr nep xp nxp dst v1 dstcap ev v2 evcap
        (walkSeg2InitMem sAddr b ep n nb m)) a len = some bs := by
  rw [walkSeg2PostMem_eq, hstores]
  subst hlen
  exact readBytes_stage2WriteStores_at (walkSeg2InitMem sAddr b ep n nb m) pre post a bs hpost

/-- **The log's event cursor survives the second segment.** -/
theorem walkSeg2PostMem_len {m : Mem}
    {sAddr b ep zAddr nep xp nxp dst v1 dstcap ev v2 evcap : Nat} {n nb : BitVec 64} :
    readBytes (walkSeg2PostMem sAddr zAddr nep xp nxp dst v1 dstcap ev v2 evcap
        (walkSeg2InitMem sAddr b ep n nb m)) (zAddr + woff 8) 8 = some (wordBytes 8 v2) := by
  refine walkSeg2PostMem_read_at (pre := walkSeg2Ws1 sAddr zAddr nep xp nxp dst ++
      walkSeg2Ws2 zAddr v1 dstcap ev) (post := [(zAddr + woff 16, wordBytes 8 evcap)])
    (a := zAddr + woff 8) (bs := wordBytes 8 v2) ?_ (by rw [wordBytes, natToBytes_length]) ?_
  · simp [walkSeg2Stores, walkSeg2Ws3, List.append_assoc]
  · intro st hst
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hst
    subst hst
    simp only [wordBytes, natToBytes_length, woff_8, woff_16]
    omega

/-- **The log's event capacity survives the second segment.** -/
theorem walkSeg2PostMem_cap {m : Mem}
    {sAddr b ep zAddr nep xp nxp dst v1 dstcap ev v2 evcap : Nat} {n nb : BitVec 64} :
    readBytes (walkSeg2PostMem sAddr zAddr nep xp nxp dst v1 dstcap ev v2 evcap
        (walkSeg2InitMem sAddr b ep n nb m)) (zAddr + woff 16) 8 = some (wordBytes 8 evcap) := by
  refine walkSeg2PostMem_read_at (pre := walkSeg2Ws1 sAddr zAddr nep xp nxp dst ++
      walkSeg2Ws2 zAddr v1 dstcap ev ++ [(zAddr + woff 8, wordBytes 8 v2)])
    (post := []) (a := zAddr + woff 16) (bs := wordBytes 8 evcap)
    ?_ (by rw [wordBytes, natToBytes_length]) ?_
  · simp [walkSeg2Stores, walkSeg2Ws3, List.append_assoc]
  · intro st hst; simp at hst

/-- **The log's arena cursor survives the second segment.** -/
theorem walkSeg2PostMem_alen {m : Mem}
    {sAddr b ep zAddr nep xp nxp dst v1 dstcap ev v2 evcap : Nat} {n nb : BitVec 64} :
    readBytes (walkSeg2PostMem sAddr zAddr nep xp nxp dst v1 dstcap ev v2 evcap
        (walkSeg2InitMem sAddr b ep n nb m)) (zAddr + woff 48) 8 = some (wordBytes 8 v1) := by
  refine walkSeg2PostMem_read_at (pre := walkSeg2Ws1 sAddr zAddr nep xp nxp dst)
    (post := [(zAddr + woff 56, wordBytes 8 dstcap), (zAddr, natToBytes ev 8)] ++
      walkSeg2Ws3 zAddr v2 evcap)
    (a := zAddr + woff 48) (bs := wordBytes 8 v1)
    ?_ (by rw [wordBytes, natToBytes_length]) ?_
  · simp [walkSeg2Stores, walkSeg2Ws2, List.append_assoc]
  · intro st hst
    simp only [List.mem_append, walkSeg2Ws3, List.mem_cons, List.not_mem_nil,
      or_false] at hst
    rcases hst with (rfl | rfl) | (rfl | rfl)
    all_goals
      (simp only [wordBytes, natToBytes_length, woff_8, woff_16, woff_48, woff_56]
       omega)

/-- **The log's arena capacity survives the second segment.** -/
theorem walkSeg2PostMem_acap {m : Mem}
    {sAddr b ep zAddr nep xp nxp dst v1 dstcap ev v2 evcap : Nat} {n nb : BitVec 64} :
    readBytes (walkSeg2PostMem sAddr zAddr nep xp nxp dst v1 dstcap ev v2 evcap
        (walkSeg2InitMem sAddr b ep n nb m)) (zAddr + woff 56) 8 =
      some (wordBytes 8 dstcap) := by
  refine walkSeg2PostMem_read_at (pre := walkSeg2Ws1 sAddr zAddr nep xp nxp dst ++
      [(zAddr + woff 48, wordBytes 8 v1)])
    (post := [(zAddr, natToBytes ev 8)] ++ walkSeg2Ws3 zAddr v2 evcap)
    (a := zAddr + woff 56) (bs := wordBytes 8 dstcap)
    ?_ (by rw [wordBytes, natToBytes_length]) ?_
  · simp [walkSeg2Stores, walkSeg2Ws2, List.append_assoc]
  · intro st hst
    simp only [List.mem_append, walkSeg2Ws3, List.mem_cons, List.not_mem_nil,
      or_false] at hst
    rcases hst with rfl | (rfl | rfl)
    all_goals
      (simp only [wordBytes, natToBytes_length, woff_8, woff_16, woff_56]
       omega)

/-- `natToBytes` of zero is a run of zero bytes. -/
theorem walkNatToBytes_zero_four : natToBytes 0 4 = List.replicate 4 0 := by decide

/-- The stage-2 record's stores split at a write: the stores before it are
written first, then it, then the rest. -/
theorem stage2WriteStores_split {m : Mem} (pre post : List (Nat × List UInt8))
    (a : Nat) (bs : List UInt8) :
    stage2WriteStores m (pre ++ (a, bs) :: post) =
      stage2WriteStores (writeBytes (stage2WriteStores m pre) a bs) post := by
  rw [stage2WriteStores_append]
  rfl

/-- A read of a written run, from any interior offset: the bytes are the run's
own, sliced. -/
theorem walkReadBytes_writeBytes_slice {m : Mem} (start : Nat) (bs : List UInt8) :
    ∀ {j n : Nat}, j + n ≤ bs.length →
      readBytes (writeBytes m start bs) (start + j) n = some ((bs.drop j).take n) := by
  intro j n h
  have hsame : readBytes (writeBytes m start bs) start bs.length = some bs :=
    readBytes_writeBytes_same m bs
  obtain ⟨-, h1⟩ := readBytes_split (writeBytes m start bs) start j (bs.length - j)
    (by rwa [show j + (bs.length - j) = bs.length from by omega])
  have h2 : readBytes (writeBytes m start bs) (start + j) (bs.length - j) =
      some (bs.drop j) := h1
  obtain ⟨h3, -⟩ := readBytes_split (writeBytes m start bs) (start + j) n
    (bs.length - j - n) (by rwa [show n + (bs.length - j - n) = bs.length - j from by omega])
  exact h3

/-- **The log's zeroed hash word survives the second segment.**  The `memset` at
`z + 24` covers sixteen bytes, so the four at `z + 32` are inside its write. -/
theorem walkSeg2PostMem_hash {m : Mem}
    {sAddr b ep zAddr nep xp nxp dst v1 dstcap ev v2 evcap : Nat} {n nb : BitVec 64} :
    readBytes (walkSeg2PostMem sAddr zAddr nep xp nxp dst v1 dstcap ev v2 evcap
        (walkSeg2InitMem sAddr b ep n nb m)) (zAddr + woff 32) 4 =
      some (natToBytes 0 4) := by
  rw [walkSeg2PostMem_eq]
  rw [show walkSeg2Stores sAddr zAddr nep xp nxp dst v1 dstcap ev v2 evcap =
      [(sAddr + woff 56, wordBytes 8 nep), (sAddr + woff 72, natToBytes xp 8),
       (sAddr + woff 80, wordBytes 8 nxp)] ++
        (zAddr + woff 24, List.replicate 16 0) ::
          ((zAddr + woff 40, natToBytes dst 8) ::
            ([(zAddr + woff 48, wordBytes 8 v1), (zAddr + woff 56, wordBytes 8 dstcap),
              (zAddr, natToBytes ev 8)] ++
             [(zAddr + woff 8, wordBytes 8 v2), (zAddr + woff 16, wordBytes 8 evcap)]))
      from by
        simp only [walkSeg2Stores, walkSeg2Ws1, walkSeg2Ws2, walkSeg2Ws3,
          seg2MemsetCount, List.append_assoc]
        rfl]
  rw [stage2WriteStores_split]
  rw [readBytes_stage2WriteStores_of_all_outside _ ?_]
  · have hslice := walkReadBytes_writeBytes_slice
      (m := stage2WriteStores (walkSeg2InitMem sAddr b ep n nb m)
        [(sAddr + woff 56, wordBytes 8 nep), (sAddr + woff 72, natToBytes xp 8),
         (sAddr + woff 80, wordBytes 8 nxp)])
      (start := zAddr + woff 24) (bs := List.replicate 16 0) (j := 8) (n := 4)
      (by simp)
    rw [show zAddr + woff 24 + 8 = zAddr + woff 32 from by rw [woff_24, woff_32]]
      at hslice
    rw [hslice, walkNatToBytes_zero_four]
    simp [List.drop_replicate, List.take_replicate]
  · intro st hst
    simp only [List.mem_cons, List.not_mem_nil, or_false, List.mem_append] at hst
    rcases hst with rfl | ((rfl | rfl | rfl) | rfl | rfl)
    all_goals
      (simp only [natToBytes_length, wordBytes, woff_8, woff_16, woff_24, woff_32,
        woff_40, woff_48, woff_56, List.length_replicate]
       omega)


/-- **The seed's memory clauses, read at the entry run's own fold.** -/
theorem walkEntryMem_len {m0 : Mem} (G : WalkGeom m0) (S : WalkStage G) :
    readBytes (walkEntryMem G S) (S.z + 8) 8 = some (wordBytes 8 G.nev0) := by
  have hw : woff 8 = 8 := woff_8
  rw [show S.z + 8 = S.z + woff 8 from by rw [woff_8]]
  rw [walkEntryMem_read_out G S (a := S.z + woff 8) (len := 8) (by omega) (by omega)]
  exact walkSeg2PostMem_len

theorem walkEntryMem_cap {m0 : Mem} (G : WalkGeom m0) (S : WalkStage G) :
    readBytes (walkEntryMem G S) (S.z + 16) 8 = some (wordBytes 8 G.evcap) := by
  have hw : woff 16 = 16 := woff_16
  rw [show S.z + 16 = S.z + woff 16 from by rw [woff_16]]
  rw [walkEntryMem_read_out G S (a := S.z + woff 16) (len := 8) (by omega) (by omega)]
  exact walkSeg2PostMem_cap

theorem walkEntryMem_alen {m0 : Mem} (G : WalkGeom m0) (S : WalkStage G) :
    readBytes (walkEntryMem G S) (S.z + 48) 8 = some (wordBytes 8 G.ndst0) := by
  have hw : woff 48 = 48 := woff_48
  rw [show S.z + 48 = S.z + woff 48 from by rw [woff_48]]
  rw [walkEntryMem_read_out G S (a := S.z + woff 48) (len := 8) (by omega) (by omega)]
  exact walkSeg2PostMem_alen

theorem walkEntryMem_acap {m0 : Mem} (G : WalkGeom m0) (S : WalkStage G) :
    readBytes (walkEntryMem G S) (S.z + 56) 8 = some (wordBytes 8 G.dstcap) := by
  have hw : woff 56 = 56 := woff_56
  rw [show S.z + 56 = S.z + woff 56 from by rw [woff_56]]
  rw [walkEntryMem_read_out G S (a := S.z + woff 56) (len := 8) (by omega) (by omega)]
  exact walkSeg2PostMem_acap

theorem walkEntryMem_hash {m0 : Mem} (G : WalkGeom m0) (S : WalkStage G) :
    readBytes (walkEntryMem G S) (S.z + 32) 4 = some (natToBytes 0 4) := by
  have hw : woff 32 = 32 := woff_32
  rw [show S.z + 32 = S.z + woff 32 from by rw [woff_32]]
  rw [walkEntryMem_read_out G S (a := S.z + woff 32) (len := 4) (by omega) (by omega)]
  exact walkSeg2PostMem_hash

/-- info: 'LeanLLVM.Refinement.WalkScope.stage2WriteStores_split' does not depend on any axioms -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.WalkScope.stage2WriteStores_split

/-- info: 'LeanLLVM.Refinement.WalkScope.walkNatToBytes_zero_four' does not depend on any axioms -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.WalkScope.walkNatToBytes_zero_four

/-- info: 'LeanLLVM.Refinement.WalkScope.walkReadBytes_writeBytes_slice' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.WalkScope.walkReadBytes_writeBytes_slice

/-- info: 'LeanLLVM.Refinement.WalkScope.walkSeg2PostMem_read_at' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.WalkScope.walkSeg2PostMem_read_at

/-- info: 'LeanLLVM.Refinement.WalkScope.walkSeg2PostMem_len' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.WalkScope.walkSeg2PostMem_len

/-- info: 'LeanLLVM.Refinement.WalkScope.walkSeg2PostMem_hash' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.WalkScope.walkSeg2PostMem_hash

/-- info: 'LeanLLVM.Refinement.WalkScope.walkStage_log_sep' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.WalkScope.walkStage_log_sep

/-- info: 'LeanLLVM.Refinement.WalkScope.walkSeg3Stores_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.WalkScope.walkSeg3Stores_bounds

/-- info: 'LeanLLVM.Refinement.WalkScope.walkEntryMem_read_out' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.WalkScope.walkEntryMem_read_out

/-- info: 'LeanLLVM.Refinement.WalkScope.walkEntryMem_len' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.WalkScope.walkEntryMem_len

/-- info: 'LeanLLVM.Refinement.WalkScope.walkEntryMem_hash' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.WalkScope.walkEntryMem_hash

/-! ### The seed's register clauses

`walkSeedFinalEnv` is the environment at `NodeBlock21` after the three runs: the
entry run's cells (`walkEntryEnv1` through `walkEntryEnv4`), the preheader's five
literal-offset binds, and the header's eight (`whileBodyOut` at the first pass).
The two `phi` values are the preheader's arm — the index and the depth are zero —
and the remaining clauses `WalkSeedState` states about the environment are
lookups in it: `WalkPtrs`' six addresses, `WalkRegs`' twenty-four, which are the
entry run's own cells, and the two `phi` registers.

The proof is a peel to the binding and an exact match: the environment is a cons
chain once the builders are unfolded, so `walk_final_lk` walks it and closes at
the cell.  `WalkRegs`' list is a literal (`walkStaticRegs`), so its twenty-four
members are its twenty-four cells; the three stack objects are at the call's
cursor, which the caller states as `s.next = G.next0`.

`WalkIter` — `%7` and `%8`, the entry stream's lane and the document byte — is
the remaining environment clause, and it reads the entry stream at `G.ep` through
the entry run's folds; that peel is the next row. -/

/-- The environment at `NodeBlock21` after the three runs: the entry run's cells,
then the preheader's five, then the header's eight. -/
def walkSeedFinalEnv {m0 : Mem} (G : WalkGeom m0) (S : WalkStage G) (env : Env)
    (s : State) (q : Nat) (bt : UInt8) : Env :=
  let e1 := walkEntryEnv1 env s.next G.n
  let e2 := walkEntryEnv2 e1 S.s S.z G.nep G.xp G.nxp G.dst G.ndst0 G.nev0 G.ev
  let e3 := walkEntryEnv3 e2 G.b G.n G.ep S.s S.c
  let e4 := walkEntryEnv4 e3 G.b G.nep
  let p1 : Env := ("%k11.i", .ptr (S.c + 32)) :: e4
  let p2 : Env := ("%h1.i.i.i51", .ptr (S.z + 24)) :: p1
  let p3 : Env := ("%gap.i", .ptr (S.tok + 20)) :: p2
  let p4 : Env := ("%end.i", .ptr (S.tok + 8)) :: p3
  let p5 : Env := ("%kind404.i", .ptr (S.tok + 16)) :: p4
  whileBodyOut p5 0 0 G.b G.ep S.c q bt

/-- Peel the seed's environment to a binding and match it exactly. -/
macro "walk_final_lk" : tactic => `(tactic|
  (simp only [walkSeedFinalEnv, whileBodyOut, walkEntryEnv4, walkEntryEnv3,
     walkEntryEnv2, walkEntryEnv1, cells, State.bind]
   simp only [woff_4, woff_8, woff_16, woff_24, woff_32, woff_40, woff_48, woff_56,
     woff_64, woff_72, woff_80, woff_1112, woff_1192]
   repeat rw [lookupName_cons_ne _ _ (by decide)]
   first
   | (rw [lookupName_cons_self]; rfl)
   | rfl))

theorem walkSeedFinalEnv_k {m0 : Mem} (G : WalkGeom m0) (S : WalkStage G) (env : Env)
    (s : State) (q : Nat) (bt : UInt8) :
    lookupName (walkSeedFinalEnv G S env s q bt) "%k.0.i249" = some (.int 64 0) := by
  walk_final_lk

theorem walkSeedFinalEnv_sp {m0 : Mem} (G : WalkGeom m0) (S : WalkStage G) (env : Env)
    (s : State) (q : Nat) (bt : UInt8) :
    lookupName (walkSeedFinalEnv G S env s q bt) "%sp.i.0248" = some (.int 32 0) := by
  walk_final_lk

theorem walkSeedFinalEnv_ptrs {m0 : Mem} (G : WalkGeom m0) (S : WalkStage G) (env : Env)
    (s : State) (q : Nat) (bt : UInt8)
    (hct : lookupName env "%ctype.i" = some (.ptr S.ctype))
    (hcs : lookupName env "%cst.i" = some (.ptr S.cst)) :
    WalkPtrs G (walkSeed G S) (walkSeedFinalEnv G S env s q bt) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · walk_final_lk
  · walk_final_lk
  · walk_final_lk
  · simp only [walkSeedFinalEnv, whileBodyOut, walkEntryEnv4, walkEntryEnv3,
      walkEntryEnv2, walkEntryEnv1, cells, State.bind]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact hct
  · simp only [walkSeedFinalEnv, whileBodyOut, walkEntryEnv4, walkEntryEnv3,
      walkEntryEnv2, walkEntryEnv1, cells, State.bind]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact hcs
  · walk_final_lk

theorem walkSeedFinalEnv_regs {m0 : Mem} (G : WalkGeom m0) (S : WalkStage G) (env : Env)
    (s : State) (q : Nat) (bt : UInt8) (hnext : s.next = G.next0) :
    WalkRegs G (walkSeed G S) (walkSeedFinalEnv G S env s q bt) := by
  intro p hp
  simp only [walkStaticRegs, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  all_goals first
    | walk_final_lk
    | (simp only [walkSeedFinalEnv, whileBodyOut, walkEntryEnv4, walkEntryEnv3,
        walkEntryEnv2, walkEntryEnv1, cells, State.bind]
       repeat rw [lookupName_cons_ne _ _ (by decide)]
       rw [lookupName_cons_self, hnext])

/-- info: 'LeanLLVM.Refinement.WalkScope.walkSeedFinalEnv_k' depends on axioms: [propext] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.WalkScope.walkSeedFinalEnv_k

/-- info: 'LeanLLVM.Refinement.WalkScope.walkSeedFinalEnv_sp' depends on axioms: [propext] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.WalkScope.walkSeedFinalEnv_sp

/-- info: 'LeanLLVM.Refinement.WalkScope.walkSeedFinalEnv_ptrs' depends on axioms: [propext] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.WalkScope.walkSeedFinalEnv_ptrs

/-- info: 'LeanLLVM.Refinement.WalkScope.walkSeedFinalEnv_regs' depends on axioms: [propext] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.WalkScope.walkSeedFinalEnv_regs

/-! ### Axiom footprints -/

/-- info: 'LeanLLVM.Refinement.WalkScope.walkEntry_step' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.WalkScope.walkEntry_step

/-- info: 'LeanLLVM.Refinement.WalkScope.walkEntry_runFuel' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.WalkScope.walkEntry_runFuel

/-- info: 'LeanLLVM.Refinement.WalkScope.walkPreheader_denote' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.WalkScope.walkPreheader_denote

/-- info: 'LeanLLVM.Refinement.WalkScope.walkPreheader_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.WalkScope.walkPreheader_step

/-- info: 'LeanLLVM.Refinement.WalkScope.whileBodyFirst_denote' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.WalkScope.whileBodyFirst_denote

/-- info: 'LeanLLVM.Refinement.WalkScope.walkHeader_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.WalkScope.walkHeader_step

end WalkScope
end LeanLLVM.Refinement
