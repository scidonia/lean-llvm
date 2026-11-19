/-
The fallback's seam: the second reader, the ladder and the body's return.

The numeric conversion's fallback (`num_fast_el1`'s `if.end285`) runs the
inlined `num_scan` second reader, the inlined `to_double` and the exponent
ladder, and returns `1` with the converted double at `%out`.  The pieces at the
seam's ends are proved:

* the second reader's blocks are `JsonStage2NumFastScanSlow`'s per-edge steps,
  from `if.end285`'s counter and sign step through the digit loops, the exponent
  and the ten-`phi` handoff at `for.body.outer.i.outer.i`;
* the ladder's two shapes — positive residual first and negative residual
  first — are `JsonStage2NumFastTier3Join`'s, from the head `while.cond203.i.i`
  with the two cells `if.end198.i.i` forms, to `while.end253.i.i`;
* `if.end291`'s store and `cleanup300`'s return are stated here at their own
  pins: the store writes the phi's incoming — the epilogue's `%cond366.i.i` —
  at `%out`, and the return block's `phi` selects `1` from `if.end291`'s edge.

**The two boundaries.**  The seam does not restate the copy or the epilogue.
Two hypotheses name what it does not prove, and `JsonStage2NumFastFallback`'s
seam takes them as its only interior boundaries:

* `fbCopyEntry` (positive) and `fbCopyEntryNeg` (negative): from the copy's
  entry — the ten cells `slEntry` binds, the scan's carried lexeme, digit array
  and counter — the run reaches the ladder's head `while.cond203.i.i` with
  `%sub200.i.i` and `%conv202.i.i` at the model's residual and widened head.
  This is the `to_double` interior from the second reader's handoff through the
  `T`/`F` parse, the copy, the lead clamps and the big multiply; the copy's own
  statements (`t3MainInv`, `t3MainLoop_run_at'`, the handoff and the residual
  loop) are what discharges it.
* `FbEpilogue`: from the ladder's exit `while.end253.i.i` the run reaches
  `if.end291`'s inlet `for.end359.i.i` with `%cond366.i.i` the model's rounded
  bits, within a caller-given bound `J`.  This is the rounding loop
  `for.cond255.i.i` and the sign select.

The second reader's traversal is `JsonStage2NumFastScanSlow`'s per-edge chain
composed at the arm's "scan's shape": a single `runFuel` prefix from
`if.end6.i` to the handoff, supplied as a hypothesis because the digit loops'
induction over those edges is the arm's, not this module's.  The per-edge steps
and the handoff step are `NumFastScanSlow`'s and are used unchanged.

**The conclusion.**  The seam returns `1`, writes the model's `strtodSpec`
bytes at `%out`, leaves `%err` and the bytes outside the two slots, and carries
the fallback class: `numFastEmitted`'s fallback clause is
`StrtodTier3.tier3Emitted` (`numFastEmitted_eq_fallback`), and that model's bits
are `strtodSpec`'s (`StrtodTier3.tier3Binary_eq_strtodSpec`).  The model's sign
tie is `NumFastScanSlow`'s: the reader's `%cmp1.i` and `%i.0.i` are the
decomposition's sign and sign index on a well-formed lexeme.

There is no `sorry`, `admit` or `native_decide` below.
-/
import LeanLLVM.Refinement.JsonStage2NumFastScanSlow
import LeanLLVM.Refinement.JsonStage2NumFastTier3Join

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

namespace LeanLLVM.Refinement

open LeanLLVM
open LeanLLVM.JSON
open LeanLLVM.Refinement.BlockEval
open LeanLLVM.Refinement.JsonScanLane
open LeanLLVM.Refinement.NumFastScanSlow
open LeanLLVM.Refinement.NumFastTier3Ladder
open LeanLLVM.Refinement.NumFastTier3Join

namespace NumFastFallback

/-! ### The scan's carried cells

`fbScanCarry` is the reader's environment as the seam hands it on: the lexeme's
base and length, the sign's index and test, the digit array's base and the
counter.  The scan's blocks bind more names in front of it; a lookup through
them is the lookup below.
-/

/-- The cells the second reader carries: `%p`, `%n`, `%i.0.i`, `%cmp1.i`,
`%dig.i.i` and `@g_nume1_slow`. -/
def fbScanCarry (env : Env) (p n g : Nat) (i0 : BitVec 64) (sgn : BitVec 1)
    (digA : Nat) : Prop :=
  lookupName env "%p" = some (.ptr p) ∧
  lookupName env "%n" = some (.int 64 n) ∧
  lookupName env "%i.0.i" = some (.int 64 i0) ∧
  lookupName env "%cmp1.i" = some (.int 1 sgn) ∧
  lookupName env "%dig.i.i" = some (.ptr digA) ∧
  lookupName env "@g_nume1_slow" = some (.ptr g)

theorem fbScanCarry.p {env p n g i0 sgn digA} (h : fbScanCarry env p n g i0 sgn digA) :
    lookupName env "%p" = some (.ptr p) := h.1

theorem fbScanCarry.n {env p n g i0 sgn digA} (h : fbScanCarry env p n g i0 sgn digA) :
    lookupName env "%n" = some (.int 64 n) := h.2.1

theorem fbScanCarry.i0 {env p n g i0 sgn digA} (h : fbScanCarry env p n g i0 sgn digA) :
    lookupName env "%i.0.i" = some (.int 64 i0) := h.2.2.1

theorem fbScanCarry.cmp {env p n g i0 sgn digA} (h : fbScanCarry env p n g i0 sgn digA) :
    lookupName env "%cmp1.i" = some (.int 1 sgn) := h.2.2.2.1

theorem fbScanCarry.dig {env p n g i0 sgn digA} (h : fbScanCarry env p n g i0 sgn digA) :
    lookupName env "%dig.i.i" = some (.ptr digA) := h.2.2.2.2.1

theorem fbScanCarry.g {env p n g i0 sgn digA} (h : fbScanCarry env p n g i0 sgn digA) :
    lookupName env "@g_nume1_slow" = some (.ptr g) := h.2.2.2.2.2

/-- The carried cells' own lookups: peel the names a block bound and stop at the
one the hypothesis holds. -/
macro "fb_lk" : tactic => `(tactic|
  (first
   | assumption
   | (repeat rw [lookupName_cons_ne _ _ (by decide)]
      first | rw [lookupName_cons_self] | assumption | rfl)))

/-- The scan's cells through `if.end285`'s environment. -/
theorem fbScanCarry_slEnv285 {env : Env} {p n g : Nat} {i0 : BitVec 64}
    {sgn : BitVec 1} {digA : Nat} {gv : BitVec 64} {b0 : UInt8}
    (h : fbScanCarry env p n g i0 sgn digA) :
    fbScanCarry (slEnv285 env p n i0 sgn digA gv b0) p n g i0 sgn digA := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals
    (simp only [slEnv285, slCarry]
     fb_lk)

/-- The scan's cells through the ten-`phi` handoff. -/
theorem fbScanCarry_slEntry {env : Env} {p n g : Nat} {i0 : BitVec 64}
    {sgn : BitVec 1} {digA : Nat} (h : fbScanCarry env p n g i0 sgn digA) :
    fbScanCarry (slEntry env i0) p n g i0 sgn digA := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals
    (simp only [slEntry]
     fb_lk)

/-! ### `if.end291`: the epilogue's store -/

/-- `if.end291`, from its pin: the phi, the digit array's lifetime end, and the
store at `%out`. -/
def fbInstrs291 : List Instr :=
  [Instr.phi "%retval.1.i.i" Ty.double
     [("if.then59.i.i", (Operand.reg "%cond.i.i")),
      ("if.then123.i.i", (Operand.reg "%cond125.i.i")),
      ("for.end359.i.i", (Operand.reg "%cond366.i.i")),
      ("if.then113.i.i", (Operand.reg "%spec.select694.i.i"))],
   Instr.callVoid "llvm.lifetime.end.p0"
     [((Ty.int 64), (Operand.imm (Const.int 64 0x0000000000000300#64))),
      (Ty.ptr, (Operand.reg "%dig.i.i"))],
   Instr.store Ty.double (Operand.reg "%retval.1.i.i") (Operand.reg "%out")]

theorem fb_find_291 :
    numFastBody.findBlock "if.end291" =
      some ⟨"if.end291", fbInstrs291, Term.br "cleanup300"⟩ := by
  simpa only [fbInstrs291] using numFast_findBlock_if_end291

/-- `if.end291`'s chain at the epilogue's edge: the phi selects `%cond366.i.i`,
the lifetime marker ends the digit array's lifetime, and the store writes the
value at `%out`. -/
theorem fb_291_denote {calls : Calls} {env : Env} {s : State} {bits : BitVec 64}
    {digA out : Nat} {r : CallOutcome}
    (hpre : s.pre = some "for.end359.i.i")
    (hbits : lookupName env "%cond366.i.i" = some (.float bits))
    (hdig : lookupName env "%dig.i.i" = some (.ptr digA))
    (hout : lookupName env "%out" = some (.ptr out))
    (hlife : calls "llvm.lifetime.end.p0"
      [.int 64 0x0000000000000300#64, .ptr digA] s.mem s.next = some r) :
    denoteCode calls fbInstrs291 (stateAt env s) =
      some (stateAt (("%retval.1.i.i", .float bits) :: env)
        { s with mem := writeBytes r.mem out (natToBytes bits.toNat 8),
                 next := r.next }) := by
  unfold fbInstrs291
  block_phi_run
  have hdig' : lookupName (("%retval.1.i.i", .float bits) :: env) "%dig.i.i"
      = some (.ptr digA) := by
    rw [lookupName_cons_ne _ _ (by decide)]
    exact hdig
  have hout' : lookupName (("%retval.1.i.i", .float bits) :: env) "%out"
      = some (.ptr out) := by
    rw [lookupName_cons_ne _ _ (by decide)]
    exact hout
  have hv' : lookupName (("%retval.1.i.i", .float bits) :: env) "%retval.1.i.i"
      = some (.float bits) := by
    rw [lookupName_cons_self]
  rw [denoteCode_callVoid_some calls (("%retval.1.i.i", .float bits) :: env) s
    "llvm.lifetime.end.p0"
    [((Ty.int 64), (Operand.imm (Const.int 64 0x0000000000000300#64))),
     (Ty.ptr, (Operand.reg "%dig.i.i"))]
    [.int 64 0x0000000000000300#64, .ptr digA] r
    (evalOperands_lifetimeMark (env := ("%retval.1.i.i", .float bits) :: env)
      (s := s) (w := 0x300) hdig') hlife]
  rw [NumFastTier1.denoteCode_store_double calls
    (("%retval.1.i.i", .float bits) :: env) { s with mem := r.mem, next := r.next }
    "%retval.1.i.i" "%out" hv' hout']
  simp only [denoteCode_nil, stateAt]
  all_goals block_close

/-- **`if.end291`'s step.**  At the epilogue's edge the block ends the digit
array's lifetime and stores the converted double at `%out`, leaving for
`cleanup300`. -/
theorem fb_291_step {calls : Calls} {env : Env} {s : State} {bits : BitVec 64}
    {digA out : Nat} {r : CallOutcome}
    (hpc : s.pc = "if.end291") (hpre : s.pre = some "for.end359.i.i")
    (hbits : lookupName env "%cond366.i.i" = some (.float bits))
    (hdig : lookupName env "%dig.i.i" = some (.ptr digA))
    (hout : lookupName env "%out" = some (.ptr out))
    (hlife : calls "llvm.lifetime.end.p0"
      [.int 64 0x0000000000000300#64, .ptr digA] s.mem s.next = some r) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (("%retval.1.i.i", .float bits) :: env)
        { s with mem := writeBytes r.mem out (natToBytes bits.toNat 8),
                 next := r.next, pc := "cleanup300", pre := some "if.end291" }) := by
  refine numFast_step_at
    (s' := stateAt (("%retval.1.i.i", .float bits) :: env)
      { s with mem := writeBytes r.mem out (natToBytes bits.toNat 8), next := r.next })
    (b := ⟨"if.end291", fbInstrs291, Term.br "cleanup300"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using fb_find_291
  · simpa only [stateAt] using fb_291_denote hpre hbits hdig hout hlife
  · simp only [execTerm, stateAt, hpc]

/-! ### `cleanup300`: the fallback's return -/

/-- `cleanup300`'s chain at `if.end291`'s edge: the thirteen-member `phi`
selects the literal `1`. -/
theorem fb_cleanup300_denote {calls : Calls} {env : Env} {s : State}
    (hpre : s.pre = some "if.end291") :
    denoteCode calls numFastCleanup300Instrs (stateAt env s) =
      some (stateAt (("%retval.8", .int 32 1) :: env) s) := by
  unfold numFastCleanup300Instrs
  block_eval

/-- **`cleanup300`'s step at the fallback's edge.**  Entered from `if.end291`,
the block returns `1`. -/
theorem fb_cleanup300_step {calls : Calls} {env : Env} {s : State}
    (hpc : s.pc = "cleanup300") (hpre : s.pre = some "if.end291") :
    step calls numFastBody (stateAt env s) =
      .ret (some (.int 32 1)) (stateAt (("%retval.8", .int 32 1) :: env) s) := by
  refine numFast_step_at (s' := stateAt (("%retval.8", .int 32 1) :: env) s)
    (b := ⟨"cleanup300", numFastCleanup300Instrs,
      Term.ret (Ty.int 32) (some (Operand.reg "%retval.8"))⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using numFast_findBlock_cleanup300
  · simpa only [denoteCode_nil] using
      fb_cleanup300_denote (calls := calls) (env := env) (s := s) hpre
  · simp only [execTerm, evalOperand, stateAt, lookupName_cons_self]

/-! ### The model's bits -/

/-- **The tier-3 model's bits are `strtodSpec`'s.**  The emitted fallback's
model is `tier3Emitted` at the reader, whose value is `tier3Binary`'s, and
`tier3Binary_eq_strtodSpec` is the conversion's contract. -/
theorem fb_model_bits {d : Decimal} (hd : d.wellFormed) :
    (StrtodTier3.tier3Emitted StrtodReader.reader d.lexeme).toBits =
      (strtodSpec d).toBits := by
  have h1 : StrtodTier3.tier3Emitted StrtodReader.reader d.lexeme
      = StrtodTier3.tier3Binary d := by
    simp only [StrtodTier3.tier3Emitted, StrtodReader.reader_lexeme hd]
  rw [h1, StrtodTier3.tier3Binary_eq_strtodSpec]

/-! ### The epilogue boundary and the `cleanup300` tail -/

/-- The epilogue's boundary: from the ladder's exit, the run reaches
`if.end291`'s inlet with the model's rounded bits, within `J` control steps.
This is the rounding loop `for.cond255.i.i` and the sign select at
`for.end359.i.i`. -/
def FbEpilogue (calls : Calls) (d : Decimal) (digA out J : Nat) : Prop :=
  ∀ (e : State), e.pc = "while.end253.i.i" → t3DivExitWord e →
    ∃ (f : State) (j : Nat), j ≤ J ∧
      f.pc = "if.end291" ∧ f.pre = some "for.end359.i.i" ∧
      lookupName f.env "%cond366.i.i"
        = some (.float (StrtodTier3.tier3Emitted StrtodReader.reader d.lexeme).toBits) ∧
      lookupName f.env "%dig.i.i" = some (.ptr digA) ∧
      lookupName f.env "%out" = some (.ptr out) ∧
      ∀ k, runFuel calls (j + k) numFastBody e = runFuel calls k numFastBody f

/-- `if.end291`'s lifetime marker is answered by the calls selection. -/
def FbStart291 (calls : Calls) (digA : Nat) : Prop :=
  ∀ (f : State), f.pc = "if.end291" → f.pre = some "for.end359.i.i" →
    ∃ (r : CallOutcome),
      calls "llvm.lifetime.end.p0"
        [.int 64 0x0000000000000300#64, .ptr digA] f.mem f.next = some r

/-- **The fallback's tail.**  From the ladder's exit, the epilogue boundary
reaches `if.end291`, the store writes the converted double at `%out`, and
`cleanup300` returns `1`.  The stored bytes are the model's `tier3Emitted` bits,
which `fb_model_bits` reads as `strtodSpec`'s. -/
theorem fb_tail {calls : Calls} {d : Decimal} {out err digA J : Nat}
    (hd : d.wellFormed)
    (hEpi : FbEpilogue calls d digA out J)
    (hStart : FbStart291 calls digA)
    (e : State) (hpc : e.pc = "while.end253.i.i") (hword : t3DivExitWord e) :
    ∃ (o : CallOutcome) (r : CallOutcome),
      runFuel calls (J + 2) numFastBody (stateAt e.env e) =
        some (.ret (some o.ret) o.mem) ∧
      o.ret = .int 32 1 ∧
      o.next = r.next ∧
      o.mem = writeBytes r.mem out (wordBytes 8 (strtodSpec d).toBits) ∧
      UnchangedOutside r.mem o.mem [(out, 8), (err, 8)] := by
  obtain ⟨f, j, hjJ, hfpc, hfpre, hfbits, hfdig, hfout, hrun⟩ := hEpi e hpc hword
  obtain ⟨r, hr⟩ := hStart f hfpc hfpre
  have hbitsEq : (StrtodTier3.tier3Emitted StrtodReader.reader d.lexeme).toBits
      = (strtodSpec d).toBits := fb_model_bits hd
  have hstep1 := fb_291_step (calls := calls) (env := f.env) (s := f)
    (bits := (StrtodTier3.tier3Emitted StrtodReader.reader d.lexeme).toBits)
    (digA := digA) (out := out) (r := r) hfpc hfpre hfbits hfdig hfout hr
  have hstep2 := fb_cleanup300_step (calls := calls)
    (env := ("%retval.1.i.i",
      .float (StrtodTier3.tier3Emitted StrtodReader.reader d.lexeme).toBits) :: f.env)
    (s := { f with
      mem := writeBytes r.mem out
        (natToBytes ((StrtodTier3.tier3Emitted StrtodReader.reader d.lexeme).toBits).toNat 8),
      next := r.next, pc := "cleanup300", pre := some "if.end291" }) rfl rfl
  have hrun2 : runFuel calls 2 numFastBody (stateAt f.env f) =
      some (.ret (some (.int 32 1))
        (writeBytes r.mem out
          (natToBytes ((StrtodTier3.tier3Emitted StrtodReader.reader d.lexeme).toBits).toNat 8))) := by
    rw [show (2 : Nat) = 1 + 1 from rfl, runFuel_jump_prefix hstep1 1]
    simp only [runFuel, hstep2]
  have hmemEq :
      writeBytes r.mem out
          (natToBytes ((StrtodTier3.tier3Emitted StrtodReader.reader d.lexeme).toBits).toNat 8)
        = writeBytes r.mem out (wordBytes 8 (strtodSpec d).toBits) := by
    rw [hbitsEq]
    rfl
  have hrun3 : runFuel calls 2 numFastBody (stateAt f.env f) =
      some (.ret (some (.int 32 1))
        (writeBytes r.mem out (wordBytes 8 (strtodSpec d).toBits))) := by
    rw [hrun2, hmemEq]
  have hprefix : runFuel calls (j + 2) numFastBody (stateAt e.env e) =
      some (.ret (some (.int 32 1))
        (writeBytes r.mem out (wordBytes 8 (strtodSpec d).toBits))) := by
    rw [hrun 2]
    exact hrun3
  have hfull : runFuel calls (J + 2) numFastBody (stateAt e.env e) =
      some (.ret (some (.int 32 1))
        (writeBytes r.mem out (wordBytes 8 (strtodSpec d).toBits))) :=
    runFuel_mono_le (by omega) hprefix
  refine ⟨⟨.int 32 1, writeBytes r.mem out (wordBytes 8 (strtodSpec d).toBits),
    r.next⟩, r, hfull, rfl, rfl, rfl, ?_⟩
  exact (UnchangedOutside.refl' r.mem [(out, 8), (err, 8)]).write_le
    (a := out) (w := 8) (bs := wordBytes 8 (strtodSpec d).toBits)
    ⟨(out, 8), by simp, le_rfl, by omega⟩
    (by simp only [wordBytes, natToBytes_length, le_rfl])

/-! ### The copy's entry, and the interior to the ladder's head -/

/-- The second reader's traversal: from `if.end6.i`, the run reaches the
handoff `for.body.outer.i.outer.i` with the carried cells.  This is the arm's
"scan's shape" — the digit loops' induction over `NumFastScanSlow`'s per-edge
steps. -/
def FbReader (calls : Calls) (p n g : Nat) (i0 : BitVec 64) (sgn : BitVec 1)
    (digA : Nat) : Prop :=
  ∀ (e : State), e.pc = "if.end6.i" → e.pre = some "if.end285" →
    fbScanCarry e.env p n g i0 sgn digA →
    ∃ (e' : State) (j : Nat),
      e'.pc = "for.body.outer.i.outer.i" ∧ e'.pre = some "if.then143.i" ∧
      fbScanCarry e'.env p n g i0 sgn digA ∧
      ∀ k, runFuel calls (j + k) numFastBody e = runFuel calls k numFastBody e'

/-- The interior from the copy's entry to the positive ladder's head: the copy,
the lead clamps and the big multiply, reaching `while.cond203.i.i` from
`if.end198.i.i` with the model's residual exponent and widened head. -/
def FbCopyEntryPos (calls : Calls) (p n g digA : Nat) (i0 : BitVec 64)
    (sgn : BitVec 1) (E : Nat) (d0 : BitVec 64) : Prop :=
  ∀ (e : State), e.pc = "for.body.outer.i.i" →
    e.pre = some "for.body.outer.i.outer.i" → slEntryFields e.env i0 →
    fbScanCarry e.env p n g i0 sgn digA →
    ∃ (f : State) (j : Nat),
      f.pc = t3MulHead ∧ f.pre = some "if.end198.i.i" ∧
      lookupName f.env "%sub200.i.i" = some (.int 64 (BitVec.ofNat 64 E)) ∧
      lookupName f.env "%conv202.i.i" = some (.float d0) ∧
      fbScanCarry f.env p n g i0 sgn digA ∧
      ∀ k, runFuel calls (j + k) numFastBody e = runFuel calls k numFastBody f

/-- The interior to the negative ladder's head: the same state, with
`%sub200.i.i` the exponent's own negative value. -/
def FbCopyEntryNeg (calls : Calls) (p n g digA : Nat) (i0 : BitVec 64)
    (sgn : BitVec 1) (E : Nat) (d0 : BitVec 64) : Prop :=
  ∀ (e : State), e.pc = "for.body.outer.i.i" →
    e.pre = some "for.body.outer.i.outer.i" → slEntryFields e.env i0 →
    fbScanCarry e.env p n g i0 sgn digA →
    ∃ (f : State) (j : Nat),
      f.pc = t3MulHead ∧ f.pre = some "if.end198.i.i" ∧
      lookupName f.env "%sub200.i.i" = some (.int 64 (BitVec.ofInt 64 (-(E : Int)))) ∧
      lookupName f.env "%conv202.i.i" = some (.float d0) ∧
      fbScanCarry f.env p n g i0 sgn digA ∧
      ∀ k, runFuel calls (j + k) numFastBody e = runFuel calls k numFastBody f

/-! ### The seam, positive residual first -/

/-- **The fallback's seam, a positive residual first.**  From `if.end285`'s
entry, the second reader reaches the copy's entry, the interior reaches the
ladder's head, the ladder spends the positive residual, and the epilogue and
the store return `1` with `strtodSpec`'s bytes at `%out`.  The interior and the
epilogue are the two named boundaries; the scan's traversal is the arm's
scan's shape. -/
theorem fb_seam_pos {calls : Calls} {env : Env} {s : State} {d : Decimal}
    {p n g gv digA out err : Nat} {i0 : BitVec 64} {sgn : BitVec 1} {b0 : UInt8}
    {E : Nat} {d0 : BitVec 64} {address J : Nat}
    (hpc : s.pc = "if.end285") (hpre : s.pre = some "cleanup282.thread462")
    (hg : lookupName env "@g_nume1_slow" = some (.ptr g))
    (hgv : readBytes s.mem g 8 = some (natToBytes gv.toNat 8))
    (hp : lookupName env "%p" = some (.ptr p))
    (hb : readBytes s.mem p 1 = some [b0])
    (hbw : readBytes (writeBytes s.mem g (natToBytes (gv + 1).toNat 8)) p 1 = some [b0])
    (hn : lookupName env "%n" = some (.int 64 n))
    (hbit : evalICmp .ugt n (slSignIdx b0) = (1 : BitVec 1))
    (hcarry : fbScanCarry env p n g i0 sgn digA)
    (hout : lookupName env "%out" = some (.ptr out))
    (herr : lookupName env "%err" = some (.ptr err))
    (hd : d.wellFormed) (hb0 : d.lexeme.toList.head? = some b0)
    (hsgn : sgn = slSignBit b0) (hi0 : i0 = slSignIdx b0)
    (hclass : LeanLLVM.StrtodRefine.Fallback d kernelDecides)
    (hreader : FbReader calls p n g i0 sgn digA)
    (hcopyEntry : FbCopyEntryPos calls p n g digA i0 sgn E d0)
    (hE : E ≤ 342)
    (hpack : ∀ c, c ≤ (t3Rows E).length →
      ∃ k : Code, t3MulCarried d0 (t3Rows E) c = packMag (.fin k) false ∧ k.IsMag)
    (hstage : ∀ (env : Env) (s : State) (resid : Nat) (d : BitVec 64),
      lookupName env "%e10.0.i.i" = some (.int 64 (BitVec.ofNat 64 resid)) →
      lookupName env "%d201.0.i.i" = some (.float d) →
        lookupName env "@NUMF_EL1_POW10" = some (.ptr address) ∧
        readBytes s.mem (address + min resid 22 * 8) 8
          = some (natToBytes (uitofpBits (10 ^ min resid 22)).toNat 8))
    (hno : ∀ c, c < (t3Rows E).length →
      ¬ overflowTicks * 2 ^ 1074
        ≤ F64.magTicks (F64.ofBits (t3MulCarried d0 (t3Rows E) c))
            * (10 ^ min (t3Resid E c) 22 * 2 ^ 1074))
    (hEpi : FbEpilogue calls d digA out J)
    (hStart : FbStart291 calls digA) :
    ∃ (k : Nat) (o : CallOutcome) (r : CallOutcome),
      runFuel calls k numFastBody (stateAt env s) = some (.ret (some o.ret) o.mem) ∧
      o.ret = .int 32 1 ∧
      o.next = r.next ∧
      o.mem = writeBytes r.mem out (wordBytes 8 (strtodSpec d).toBits) ∧
      UnchangedOutside r.mem o.mem [(out, 8), (err, 8)] ∧
      numFastEmitted d.lexeme
        = StrtodTier3.tier3Emitted StrtodReader.reader d.lexeme ∧
      numFastEmitted d.lexeme = strtodSpec d ∧
      numClassOf (digitCount d) (numEff d) (kernelDecides d) = .fallback := by
  -- `if.end285`: the counter's bump and the sign's index
  let s6 : State :=
    stateAt (slEnv285 env p n i0 sgn digA gv b0)
      { s with mem := writeBytes s.mem g (natToBytes (gv + 1).toNat 8),
               pc := "if.end6.i", pre := some "if.end285" }
  have h285 := sl_285_step (calls := calls) (env := env) (s := s)
    hpc hpre hg hgv hp hb hbw hn hbit
  have hcarry6 : fbScanCarry s6.env p n g i0 sgn digA :=
    fbScanCarry_slEnv285 hcarry
  -- the second reader's traversal
  obtain ⟨e', jr, he'pc, he'pre, he'carry, hrunr⟩ := hreader s6 rfl rfl hcarry6
  -- the terminal edge's counter
  have hbit' : evalICmp .ugt n (slSignIdx b0)
      = (1 : BitVec 1) := hbit
  -- the ten-`phi` handoff
  have hientry := sl_entry_step (calls := calls) (env := e'.env) (s := e')
    he'pc he'pre he'carry.i0
  let e1 : State :=
    stateAt (slEntry e'.env i0)
      { e' with pc := "for.body.outer.i.i", pre := some "for.body.outer.i.outer.i" }
  have hfields : slEntryFields e1.env i0 := by
    simpa only [e1, stateAt] using sl_entry_fields e'.env i0
  have hcarry1 : fbScanCarry e1.env p n g i0 sgn digA := by
    simpa only [e1, stateAt] using fbScanCarry_slEntry he'carry
  -- the interior to the ladder's head
  obtain ⟨f, jc, hfpc, hfpre, hsub, hconv, hcarryf, hrunc⟩ :=
    hcopyEntry e1 rfl rfl hfields hcarry1
  -- the ladder
  obtain ⟨el, jl, hjl, helpc, hword, hrunl⟩ :=
    t3_ladder_run_pos_exit calls d0 E address hE hpack hstage hno f hfpc hfpre hsub hconv (J + 2)
  -- the epilogue and the return
  obtain ⟨o, r, hrun_tail, hret, hnext, hmem, hframe⟩ :=
    fb_tail (calls := calls) (d := d) (out := out) (err := err) (digA := digA)
      (J := J) hd hEpi hStart el helpc hword
  have htail : runFuel calls (jl + (J + 2)) numFastBody f =
      some (.ret (some o.ret) o.mem) := by
    rw [hrunl]
    exact hrun_tail
  refine ⟨1 + (jr + (1 + (jc + (jl + (J + 2))))), o, r, ?_, hret, hnext,
    hmem, hframe, numFastEmitted_eq_fallback hd hclass,
    numFastEmitted_strtodSpec d hd, numClassOf_fallback hclass⟩
  have h1 : runFuel calls
      (1 + (jr + (1 + (jc + (jl + (J + 2)))))) numFastBody (stateAt env s) =
      runFuel calls (jr + (1 + (jc + (jl + (J + 2))))) numFastBody s6 :=
    runFuel_jump_prefix h285 _
  rw [h1, hrunr (1 + (jc + (jl + (J + 2))))]
  have h2 : runFuel calls (1 + (jc + (jl + (J + 2)))) numFastBody e'
      = runFuel calls (jc + (jl + (J + 2))) numFastBody e1 :=
    runFuel_jump_prefix hientry _
  rw [h2, hrunc (jl + (J + 2))]
  exact htail

/-! ### The seam, negative residual first -/

/-- **The fallback's seam, a negative residual first.**  The same chain with the
ladder's negative shape: the positive loop is entered at no rows and the
negative loop spends the exponent. -/
theorem fb_seam_neg {calls : Calls} {env : Env} {s : State} {d : Decimal}
    {p n g gv digA out err : Nat} {i0 : BitVec 64} {sgn : BitVec 1} {b0 : UInt8}
    {E : Nat} {d0 : BitVec 64} {address J : Nat}
    (hpc : s.pc = "if.end285") (hpre : s.pre = some "cleanup282.thread462")
    (hg : lookupName env "@g_nume1_slow" = some (.ptr g))
    (hgv : readBytes s.mem g 8 = some (natToBytes gv.toNat 8))
    (hp : lookupName env "%p" = some (.ptr p))
    (hb : readBytes s.mem p 1 = some [b0])
    (hbw : readBytes (writeBytes s.mem g (natToBytes (gv + 1).toNat 8)) p 1 = some [b0])
    (hn : lookupName env "%n" = some (.int 64 n))
    (hbit : evalICmp .ugt n (slSignIdx b0) = (1 : BitVec 1))
    (hcarry : fbScanCarry env p n g i0 sgn digA)
    (hout : lookupName env "%out" = some (.ptr out))
    (herr : lookupName env "%err" = some (.ptr err))
    (hd : d.wellFormed) (hb0 : d.lexeme.toList.head? = some b0)
    (hsgn : sgn = slSignBit b0) (hi0 : i0 = slSignIdx b0)
    (hclass : LeanLLVM.StrtodRefine.Fallback d kernelDecides)
    (hreader : FbReader calls p n g i0 sgn digA)
    (hcopyEntry : FbCopyEntryNeg calls p n g digA i0 sgn E d0)
    (hE : E ≤ 342) (hpos : 0 < E)
    (hpack : ∀ c, c ≤ (t3Rows E).length →
      ∃ k : Code, t3DivCarried d0 (t3Rows E) c = packMag (.fin k) false ∧
        k.IsMag ∧ 0 < k.ticks)
    (hstage : ∀ (env : Env) (s : State) (resid : Nat) (d : BitVec 64),
      lookupName env "%e10.2.i.i" = some (.int 64 (BitVec.ofInt 64 (-(resid : Int)))) →
      lookupName env "%d201.2.i.i" = some (.float d) →
        lookupName env "@NUMF_EL1_POW10" = some (.ptr address) ∧
        readBytes s.mem (address + min resid 22 * 8) 8
          = some (natToBytes (uitofpBits (10 ^ min resid 22)).toNat 8))
    (hEpi : FbEpilogue calls d digA out J)
    (hStart : FbStart291 calls digA) :
    ∃ (k : Nat) (o : CallOutcome) (r : CallOutcome),
      runFuel calls k numFastBody (stateAt env s) = some (.ret (some o.ret) o.mem) ∧
      o.ret = .int 32 1 ∧
      o.next = r.next ∧
      o.mem = writeBytes r.mem out (wordBytes 8 (strtodSpec d).toBits) ∧
      UnchangedOutside r.mem o.mem [(out, 8), (err, 8)] ∧
      numFastEmitted d.lexeme
        = StrtodTier3.tier3Emitted StrtodReader.reader d.lexeme ∧
      numFastEmitted d.lexeme = strtodSpec d ∧
      numClassOf (digitCount d) (numEff d) (kernelDecides d) = .fallback := by
  let s6 : State :=
    stateAt (slEnv285 env p n i0 sgn digA gv b0)
      { s with mem := writeBytes s.mem g (natToBytes (gv + 1).toNat 8),
               pc := "if.end6.i", pre := some "if.end285" }
  have h285 := sl_285_step (calls := calls) (env := env) (s := s)
    hpc hpre hg hgv hp hb hbw hn hbit
  have hcarry6 : fbScanCarry s6.env p n g i0 sgn digA :=
    fbScanCarry_slEnv285 hcarry
  obtain ⟨e', jr, he'pc, he'pre, he'carry, hrunr⟩ := hreader s6 rfl rfl hcarry6
  have hientry := sl_entry_step (calls := calls) (env := e'.env) (s := e')
    he'pc he'pre he'carry.i0
  let e1 : State :=
    stateAt (slEntry e'.env i0)
      { e' with pc := "for.body.outer.i.i", pre := some "for.body.outer.i.outer.i" }
  have hfields : slEntryFields e1.env i0 := by
    simpa only [e1, stateAt] using sl_entry_fields e'.env i0
  have hcarry1 : fbScanCarry e1.env p n g i0 sgn digA := by
    simpa only [e1, stateAt] using fbScanCarry_slEntry he'carry
  obtain ⟨f, jc, hfpc, hfpre, hsub, hconv, hcarryf, hrunc⟩ :=
    hcopyEntry e1 rfl rfl hfields hcarry1
  obtain ⟨el, jl, hjl, helpc, hword, hrunl⟩ :=
    t3_ladder_run_neg_exit calls d0 E address hE hpos hpack hstage f hfpc hfpre hsub hconv (J + 2)
  obtain ⟨o, r, hrun_tail, hret, hnext, hmem, hframe⟩ :=
    fb_tail (calls := calls) (d := d) (out := out) (err := err) (digA := digA)
      (J := J) hd hEpi hStart el helpc hword
  have htail : runFuel calls (jl + (J + 2)) numFastBody f =
      some (.ret (some o.ret) o.mem) := by
    rw [hrunl]
    exact hrun_tail
  refine ⟨1 + (jr + (1 + (jc + (jl + (J + 2))))), o, r, ?_, hret, hnext,
    hmem, hframe, numFastEmitted_eq_fallback hd hclass,
    numFastEmitted_strtodSpec d hd, numClassOf_fallback hclass⟩
  have h1 : runFuel calls
      (1 + (jr + (1 + (jc + (jl + (J + 2)))))) numFastBody (stateAt env s) =
      runFuel calls (jr + (1 + (jc + (jl + (J + 2))))) numFastBody s6 :=
    runFuel_jump_prefix h285 _
  rw [h1, hrunr (1 + (jc + (jl + (J + 2))))]
  have h2 : runFuel calls (1 + (jc + (jl + (J + 2)))) numFastBody e'
      = runFuel calls (jc + (jl + (J + 2))) numFastBody e1 :=
    runFuel_jump_prefix hientry _
  rw [h2, hrunc (jl + (J + 2))]
  exact htail

/-! ### Axiom footprints -/

#print axioms fb_291_step
#print axioms fb_291_denote
#print axioms fb_cleanup300_step
#print axioms fb_cleanup300_denote
#print axioms fb_model_bits
#print axioms fb_tail
#print axioms fb_seam_pos
#print axioms fb_seam_neg

end NumFastFallback

end LeanLLVM.Refinement
