/-
The no-event body's stores, its walk obligation, and the encoding theorem.

`JsonStage2NoEventContract` states the record; this module is what a body can be
shown to leave at it, at the depth the certified walk reaches:

* **the terminal stores, proved.**  `stage2NoEventReport` models the four stores
  of `stage2_noevent.c`'s `accept` and `if.then562` arms — the three reading words
  and, on refusal, the offset — and `stage2NoEventRun_boundary` turns a walk
  report into the record's post at them.  The stores are word stores, and the
  count's width is what makes the two count words exact; the sum word is the
  modular fact the post states.
* **the walk's loop, stated and not inhabited.**  `Stage2NoEventWalkObligation`
  is a `Satisfies` at the pinned body and the record the flattening adapts
  (`Γ_stage2_noevent_at`), at the certified walk's depth: post, stores theorem,
  `Satisfies` instance, and the loop named rather than implied.  Nothing below
  proves it, and nothing below may be read as proving it.  It is also
  **conditional**: its one parameter is the selection of `od_gap_recover`, the one
  symbol the pinned body calls which this tree does not model, and the three
  modelled sub-units are fixed to the certified models inside
  `stage2NoEventCalls`.  So the hole is the loop *plus* one unmodelled callee, and
  the obligation is narrower than `Stage2WalkObligation`, which fixes its whole
  selection.
* **the encoding, bound to the fold.**  `stage2NoEvent_encoding` states the three
  record widths (13, 9, 1), the seven tag bytes, the plain-string payload bit, and
  the per-record contribution, all against `EventRecord.encodedBytes` and
  `EventRecord.terms`, so an encoding change fails elaboration rather than
  diverging silently.  A text pin on `kernel/json/stage2.c`'s tag constants sits
  beside it.
* **the consumer-boundary corollary.**  `stage2NoEventBoundary_consumer`
  instantiates Item 1's `stage2Boundary_noEventConsumer` once at the certified
  post and reads the new post's words against the certified consumer's fold.  It
  is a corollary, not a second composition: the trace projection, the reader's
  equality and the two folds' equality are that theorem's conclusions.
* **the literal compare's obligation.**  `ne_lit` compares packed immediate bytes;
  the certified `lit_check` takes a `const char *`.  `neLitCheck_eq_litCheck`
  proves the two rules agree at both the verdict and the offset, and the three
  packed constants the pinned body carries are checked against the literals'
  bytes.  What is *not* proved is that the pinned body's unrolled comparison chain
  implements the loop — that is the walk's instruction-level trace, the same
  residue `Stage2NoEventWalkObligation` names.
-/
import LeanLLVM.Refinement.JsonStage2NoEventContract
import LeanLLVM.Refinement.JsonStage2NoEventIR
import LeanLLVM.Refinement.JsonStage2Body
import LeanLLVM.Refinement.JsonStage2IR

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 8000000

namespace LeanLLVM.Refinement

open LeanLLVM
open LeanLLVM.JSON
open LeanLLVM.Refinement.JsonStage2NoEventIR
open LeanLLVM.Refinement.JsonEntryIR (readLanes32)

/-! ### The terminal stores

The body's two exit arms write the same three words and, on refusal only, the
offset: `accept` stores `tokens`, `tokens` again (the declared build mode's
`values = tokens`) and `arena + terms`; `if.then562` stores zero in all three and
the refusal offset.  `stage2NoEventReport` is the transformer, with the refusal
store first — the four objects are separate by the record's pre, so the order
among them is immaterial to the memory a caller observes. -/

/-- The reading a word carries: zero on refusal, the run's number on acceptance. -/
def stage2NoEventWord (refusal : Bool) (v : Nat) : Nat :=
  match refusal with
  | true => 0
  | false => v

/-- The four terminal stores, as a memory transformer: `*err` on refusal, then the
three reading words, which are zero on refusal and the reading on acceptance. -/
def stage2NoEventReport (mem : Mem) (tokensOut valuesOut sumOut err : Nat)
    (refusal : Bool) (tok sumWord eoff : Nat) : Mem :=
  match refusal with
  | true =>
      writeBytes
        (writeBytes
          (writeBytes (writeBytes mem err (wordBytes 8 eoff)) tokensOut
            (wordBytes 8 0))
          valuesOut (wordBytes 8 0))
        sumOut (wordBytes 8 0)
  | false =>
      writeBytes
        (writeBytes
          (writeBytes mem tokensOut (wordBytes 8 tok))
          valuesOut (wordBytes 8 tok))
        sumOut (wordBytes 8 sumWord)

/-- The token word, read back at a slot separate from the stores above it. -/
theorem stage2NoEventReport_tokens (mem : Mem) (tokensOut valuesOut sumOut err : Nat)
    (refusal : Bool) (tok sumWord eoff : Nat)
    (h1 : tokensOut + 8 ≤ valuesOut ∨ valuesOut + 8 ≤ tokensOut)
    (h2 : tokensOut + 8 ≤ sumOut ∨ sumOut + 8 ≤ tokensOut)
    (h3 : tokensOut + 8 ≤ err ∨ err + 8 ≤ tokensOut) :
    readBytes (stage2NoEventReport mem tokensOut valuesOut sumOut err refusal tok
      sumWord eoff) tokensOut 8 =
      some (wordBytes 8 (stage2NoEventWord refusal tok)) := by
  cases refusal with
  | false =>
      simp only [stage2NoEventReport, stage2NoEventWord]
      rw [readBytes_wordBytes_frame (addr := sumOut) (v := sumWord) (p := tokensOut)
        (n := 8) (by omega)]
      rw [readBytes_wordBytes_frame (addr := valuesOut) (v := tok) (p := tokensOut)
        (n := 8) (by omega)]
      rw [readBytes_wordBytes_same]
  | true =>
      simp only [stage2NoEventReport, stage2NoEventWord]
      rw [readBytes_wordBytes_frame (addr := sumOut) (v := 0) (p := tokensOut)
        (n := 8) (by omega)]
      rw [readBytes_wordBytes_frame (addr := valuesOut) (v := 0) (p := tokensOut)
        (n := 8) (by omega)]
      rw [readBytes_wordBytes_same]

/-- The value word, read back at a slot separate from the sum's. -/
theorem stage2NoEventReport_values (mem : Mem) (tokensOut valuesOut sumOut err : Nat)
    (refusal : Bool) (tok sumWord eoff : Nat)
    (h : valuesOut + 8 ≤ sumOut ∨ sumOut + 8 ≤ valuesOut) :
    readBytes (stage2NoEventReport mem tokensOut valuesOut sumOut err refusal tok
      sumWord eoff) valuesOut 8 =
      some (wordBytes 8 (stage2NoEventWord refusal tok)) := by
  cases refusal with
  | false =>
      simp only [stage2NoEventReport, stage2NoEventWord]
      rw [readBytes_wordBytes_frame (addr := sumOut) (v := sumWord) (p := valuesOut)
        (n := 8) (by omega)]
      rw [readBytes_wordBytes_same]
  | true =>
      simp only [stage2NoEventReport, stage2NoEventWord]
      rw [readBytes_wordBytes_frame (addr := sumOut) (v := 0) (p := valuesOut)
        (n := 8) (by omega)]
      rw [readBytes_wordBytes_same]

/-- The sum word: the run's last store, so nothing gates the read-back. -/
theorem stage2NoEventReport_sum (mem : Mem) (tokensOut valuesOut sumOut err : Nat)
    (refusal : Bool) (tok sumWord eoff : Nat) :
    readBytes (stage2NoEventReport mem tokensOut valuesOut sumOut err refusal tok
      sumWord eoff) sumOut 8 =
      some (wordBytes 8 (stage2NoEventWord refusal sumWord)) := by
  cases refusal with
  | false => simp only [stage2NoEventReport, stage2NoEventWord]; rw [readBytes_wordBytes_same]
  | true => simp only [stage2NoEventReport, stage2NoEventWord]; rw [readBytes_wordBytes_same]

/-- On refusal the refusal slot carries the offset. -/
theorem stage2NoEventReport_err_refusal (mem : Mem) (tokensOut valuesOut sumOut err : Nat)
    (tok sumWord eoff : Nat)
    (h1 : tokensOut + 8 ≤ err ∨ err + 8 ≤ tokensOut)
    (h2 : valuesOut + 8 ≤ err ∨ err + 8 ≤ valuesOut)
    (h3 : sumOut + 8 ≤ err ∨ err + 8 ≤ sumOut) :
    readBytes (stage2NoEventReport mem tokensOut valuesOut sumOut err true tok
      sumWord eoff) err 8 = some (wordBytes 8 eoff) := by
  simp only [stage2NoEventReport]
  rw [readBytes_wordBytes_frame (addr := sumOut) (v := 0) (p := err) (n := 8) (by omega)]
  rw [readBytes_wordBytes_frame (addr := valuesOut) (v := 0) (p := err) (n := 8) (by omega)]
  rw [readBytes_wordBytes_frame (addr := tokensOut) (v := 0) (p := err) (n := 8) (by omega)]
  rw [readBytes_wordBytes_same]

/-- On acceptance the refusal slot is not written, so a caller reads what it
staged. -/
theorem stage2NoEventReport_err_accept (mem : Mem) (tokensOut valuesOut sumOut err : Nat)
    (tok sumWord eoff : Nat)
    (h1 : tokensOut + 8 ≤ err ∨ err + 8 ≤ tokensOut)
    (h2 : valuesOut + 8 ≤ err ∨ err + 8 ≤ valuesOut)
    (h3 : sumOut + 8 ≤ err ∨ err + 8 ≤ sumOut) :
    readBytes (stage2NoEventReport mem tokensOut valuesOut sumOut err false tok
      sumWord eoff) err 8 = readBytes mem err 8 := by
  simp only [stage2NoEventReport]
  rw [readBytes_wordBytes_frame (addr := sumOut) (v := sumWord) (p := err) (n := 8) (by omega)]
  rw [readBytes_wordBytes_frame (addr := valuesOut) (v := tok) (p := err) (n := 8) (by omega)]
  rw [readBytes_wordBytes_frame (addr := tokensOut) (v := tok) (p := err) (n := 8) (by omega)]

/-- Every byte of a listed write is inside the list. -/
theorem inRegions_writes_byte {tokensOut valuesOut sumOut err a k : Nat}
    (ha : (a, 8) ∈ stage2NoEventWrites tokensOut valuesOut sumOut err) (hk : k < 8) :
    inRegions (stage2NoEventWrites tokensOut valuesOut sumOut err) (a + k) :=
  ⟨(a, 8), ha, by omega, by omega⟩

/-- The stores' whole effect is inside the four write regions. -/
theorem stage2NoEventReport_frame (mem : Mem) (tokensOut valuesOut sumOut err : Nat)
    (refusal : Bool) (tok sumWord eoff : Nat) :
    UnchangedOn (inRegions (stage2NoEventWrites tokensOut valuesOut sumOut err)) mem
      (stage2NoEventReport mem tokensOut valuesOut sumOut err refusal tok sumWord eoff) := by
  rw [← unchangedOutside_iff_inRegions]
  have hinside (a : Nat) (ha : (a, 8) ∈ stage2NoEventWrites tokensOut valuesOut
      sumOut err) (v : Nat) :
      ∀ k, k < (wordBytes 8 v).length →
        inRegions (stage2NoEventWrites tokensOut valuesOut sumOut err) (a + k) := by
    intro k hk
    rw [show (wordBytes 8 v).length = 8 from natToBytes_length v 8] at hk
    exact inRegions_writes_byte ha hk
  have hbase : UnchangedOutside mem mem
      (stage2NoEventWrites tokensOut valuesOut sumOut err) := fun _ _ => rfl
  cases refusal with
  | false =>
      simp only [stage2NoEventReport]
      exact UnchangedOutside.write_inside
        (UnchangedOutside.write_inside
          (UnchangedOutside.write_inside hbase
            (hinside tokensOut (by simp [stage2NoEventWrites]) tok))
          (hinside valuesOut (by simp [stage2NoEventWrites]) tok))
        (hinside sumOut (by simp [stage2NoEventWrites]) sumWord)
  | true =>
      simp only [stage2NoEventReport]
      exact UnchangedOutside.write_inside
        (UnchangedOutside.write_inside
          (UnchangedOutside.write_inside
            (UnchangedOutside.write_inside hbase
              (hinside err (by simp [stage2NoEventWrites]) eoff))
            (hinside tokensOut (by simp [stage2NoEventWrites]) 0))
          (hinside valuesOut (by simp [stage2NoEventWrites]) 0))
        (hinside sumOut (by simp [stage2NoEventWrites]) 0)

/-- Presence survives the stores. -/
theorem stage2NoEventReport_present (mem : Mem) (tokensOut valuesOut sumOut err : Nat)
    (refusal : Bool) (tok sumWord eoff : Nat) {a : Nat} (h : present mem a) :
    present (stage2NoEventReport mem tokensOut valuesOut sumOut err refusal tok
      sumWord eoff) a := by
  cases refusal with
  | false =>
      simp only [stage2NoEventReport]
      exact present_writeBytes _ _ _ (present_writeBytes _ _ _
        (present_writeBytes _ _ _ h))
  | true =>
      simp only [stage2NoEventReport]
      exact present_writeBytes _ _ _ (present_writeBytes _ _ _ (present_writeBytes _ _ _
        (present_writeBytes _ _ _ h)))

/-! ### The walk's report

The loop's residue, spelled in the record's own vocabulary: the staging the call
was made at, and what the walk did — its refusal bit, its count, its events, the
arena list the fold sums, the contribution, and the region it wrote.  A proof of
the loop is a proof that produces this object; nothing in this module produces
one. -/

/-- **The report a model of the no-event walk produces.**  The first half is
`stage2NoEventPre`'s clauses at the run's own numbers; `refusal` onwards is what
the loop owes. -/
structure Stage2NoEventRun (args : List Value) (mem m0 : Mem) where
  b : Nat
  n : Nat
  ep : Nat
  nep : Nat
  xp : Nat
  nxp : Nat
  scratch : Nat
  scratchcap : Nat
  tokensOut : Nat
  valuesOut : Nat
  sumOut : Nat
  err : Nat
  bs : List UInt8
  ent : List Nat
  /-- **The cursor the run was called at.** -/
  next0 : Nat
  /-- **The cursor the run's stack writes reached.** -/
  nextEnd : Nat
  args_eq : args = [.ptr b, .int 64 (BitVec.ofNat 64 n), .ptr ep,
    .int 64 (BitVec.ofNat 64 nep), .ptr xp, .int 64 (BitVec.ofNat 64 nxp),
    .ptr scratch, .int 64 (BitVec.ofNat 64 scratchcap), .ptr tokensOut,
    .ptr valuesOut, .ptr sumOut, .ptr err]
  doc : readBytes mem b n = some bs
  tail : HasBytes mem (b + n) stage2ReadTail
  entries : readLanes32 mem ep nep = some ent
  order : ent.Pairwise (· < ·)
  inside : ∀ q ∈ ent, q < n
  esc : HasBytes mem xp (4 * nxp)
  scratchBytes : HasBytes mem scratch scratchcap
  scratchRoom : n + stage2ArenaReserve ≤ scratchcap
  tokensBytes : HasBytes mem tokensOut 8
  valuesBytes : HasBytes mem valuesOut 8
  sumBytes : HasBytes mem sumOut 8
  errBytes : HasBytes mem err 8
  maxDoc : n ≤ stage2MaxDocument
  nLt : n < 2 ^ 64
  scratchcapLt : scratchcap < 2 ^ 64
  nepLt : nep < 2 ^ 64
  nxpLt : nxp < 2 ^ 64
  separate : DisjointRegions
    (stage2NoEventRegions b n ep nep xp nxp scratch scratchcap tokensOut
      valuesOut sumOut err)
  watermark : ∀ r ∈ stage2NoEventRegions b n ep nep xp nxp scratch scratchcap
      tokensOut valuesOut sumOut err, r.1 + r.2 ≤ next0
  /-- The container stack `%stk`. -/
  stk : Nat
  /-- The refusal record `%e`. -/
  e : Nat
  /-- The cursor record `%c`. -/
  c : Nat
  /-- The number path's output slot `%d`. -/
  d : Nat
  /-- The four staged objects are present at their extents. -/
  stagedBytes : ∀ r ∈ stage2NoEventStagedRegions stk e c d, HasBytes mem r.1 r.2
  /-- They are separate from every staged input and output, and from each other. -/
  stagedSep : DisjointRegions
    (stage2NoEventRegions b n ep nep xp nxp scratch scratchcap tokensOut
      valuesOut sumOut err ++ stage2NoEventStagedRegions stk e c d)
  /-- And they end at or below the cursor the call was made at. -/
  stagedEnd : ∀ r ∈ stage2NoEventStagedRegions stk e c d, r.1 + r.2 ≤ next0
  /-- The walk's refusal bit, as the verdict word's input. -/
  refusal : Bool
  /-- The count the reading words carry. -/
  tok : Nat
  /-- The decoded string bodies, in document order. -/
  arena : List UInt8
  /-- The consumer's events. -/
  obs : List ConsumerEvent
  /-- The reference parser's tokens. -/
  toks : List Token
  /-- The events' contribution to the sum. -/
  terms : Nat
  /-- The refusal offset. -/
  eoff : Nat
  tokLe : tok ≤ n
  rel : Stage2NoEvent bs arena obs toks
  obsLen : obs.length = tok
  termsEq : terms = (obs.map ConsumerEvent.terms).sum
  offLe : refusal = true → eoff ≤ n
  nextEnd_static : next0 + (stage2BootstrapExtent + 8) ≤ nextEnd
  walkPresent : ∀ a, inRegions (stage2NoEventRunRegions scratch scratchcap stk e c d) a →
    present m0 a
  walkFrame : UnchangedOutside mem m0
    (stage2NoEventRunRegions scratch scratchcap stk e c d ++
      [(next0, nextEnd - next0)])

namespace Stage2NoEventRun

variable {args : List Value} {mem m0 : Mem}

/-- **The staging is the record's precondition.** -/
theorem pre (h : Stage2NoEventRun args mem m0) :
    Γ_stage2_noevent.pre args mem h.next0 :=
  ⟨h.b, h.n, h.ep, h.nep, h.xp, h.nxp, h.scratch, h.scratchcap, h.tokensOut,
    h.valuesOut, h.sumOut, h.err, h.bs, h.ent, h.args_eq, h.doc, h.tail,
    h.entries, h.order, h.inside, h.esc, h.scratchBytes, h.scratchRoom,
    h.tokensBytes, h.valuesBytes, h.sumBytes, h.errBytes, h.maxDoc, h.nLt,
    h.scratchcapLt, h.nepLt, h.nxpLt, h.separate, h.watermark⟩

/-- **The four staged objects' staging**, from the run's report. -/
theorem stagedPre (h : Stage2NoEventRun args mem m0) :
    stage2NoEventStagedPre args mem h.next0 h.stk h.e h.c h.d :=
  ⟨h.stagedBytes, h.b, h.n, h.ep, h.nep, h.xp, h.nxp, h.scratch, h.scratchcap,
    h.tokensOut, h.valuesOut, h.sumOut, h.err, h.args_eq, h.stagedSep,
    h.watermark, h.stagedEnd⟩

end Stage2NoEventRun

/-- The four output words are pairwise separate, read off the record's own
`DisjointRegions` at the write list's tail. -/
theorem stage2NoEventRegions_writes {b n ep nep xp nxp scratch scratchcap
    tokensOut valuesOut sumOut err : Nat}
    (h : DisjointRegions (stage2NoEventRegions b n ep nep xp nxp scratch scratchcap
      tokensOut valuesOut sumOut err)) :
    DisjointRegions (stage2NoEventWrites tokensOut valuesOut sumOut err) := by
  unfold DisjointRegions at h ⊢
  rw [stage2NoEventRegions] at h
  exact (List.pairwise_append.mp h).2.1

/-- The six slot separations the read-backs need. -/
theorem stage2NoEventWrites_slots {tokensOut valuesOut sumOut err : Nat}
    (h : DisjointRegions (stage2NoEventWrites tokensOut valuesOut sumOut err)) :
    (tokensOut + 8 ≤ valuesOut ∨ valuesOut + 8 ≤ tokensOut) ∧
    (tokensOut + 8 ≤ sumOut ∨ sumOut + 8 ≤ tokensOut) ∧
    (tokensOut + 8 ≤ err ∨ err + 8 ≤ tokensOut) ∧
    (valuesOut + 8 ≤ sumOut ∨ sumOut + 8 ≤ valuesOut) ∧
    (valuesOut + 8 ≤ err ∨ err + 8 ≤ valuesOut) ∧
    (sumOut + 8 ≤ err ∨ err + 8 ≤ sumOut) := by
  unfold DisjointRegions at h
  simp only [stage2NoEventWrites, List.pairwise_cons, List.Pairwise.nil,
    List.mem_cons, List.not_mem_nil, forall_eq_or_imp, true_and,
    and_true] at h
  obtain ⟨⟨h1, h2, h3, -⟩, ⟨h4, h5, -⟩, ⟨h6, -⟩, -⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6⟩

/-- The verdict word is `1` exactly on acceptance. -/
theorem stage2Verdict_eq_one {refusal : Bool}
    (h : stage2Verdict refusal = (1 : BitVec 64)) : refusal = false := by
  cases refusal with
  | false => rfl
  | true => simp [stage2Verdict] at h

/-- The verdict word is `0` exactly on refusal. -/
theorem stage2Verdict_eq_zero {refusal : Bool}
    (h : stage2Verdict refusal = (0 : BitVec 64)) : refusal = true := by
  cases refusal with
  | false => simp [stage2Verdict] at h
  | true => rfl

/-- **The refusal slot is outside everything the run writes.**  The run's write
list is the scratch buffer and the four staged objects; the refusal slot is one of
the record's staged inputs, so its separation from them is the staging's pair of
cross clauses. -/
theorem stage2NoEventRunRegions_err_outside {b n ep nep xp nxp scratch scratchcap
    tokensOut valuesOut sumOut err stk e c d : Nat}
    (hsep : DisjointRegions (stage2NoEventRegions b n ep nep xp nxp scratch
      scratchcap tokensOut valuesOut sumOut err))
    (hstaged : DisjointRegions (stage2NoEventRegions b n ep nep xp nxp scratch
      scratchcap tokensOut valuesOut sumOut err ++
        stage2NoEventStagedRegions stk e c d)) :
    ∀ r ∈ stage2NoEventRunRegions scratch scratchcap stk e c d,
      r.1 + r.2 ≤ err ∨ err + 8 ≤ r.1 := by
  unfold DisjointRegions at hsep hstaged
  rw [stage2NoEventRegions, List.pairwise_append] at hsep
  obtain ⟨-, -, hcross⟩ := hsep
  rw [List.pairwise_append] at hstaged
  obtain ⟨-, -, hcrossS⟩ := hstaged
  intro r hr
  rcases List.mem_cons.mp hr with rfl | hr
  · exact hcross (scratch, scratchcap) (by simp) (err, 8) (by simp [stage2NoEventWrites])
  · exact (hcrossS (err, 8) (by simp [stage2NoEventRegions, stage2NoEventWrites]) r hr).symm

/-- **The walk left the refusal slot as the caller staged it.**  The slot is one
of the record's staged inputs, separate from every region the run writes, so the
walk's frame gives its bytes back unchanged. -/
theorem Stage2NoEventRun.errFrame {args : List Value} {mem m0 : Mem}
    (h : Stage2NoEventRun args mem m0) :
    readBytes m0 h.err 8 = readBytes mem h.err 8 := by
  refine readBytes_eq_of_UnchangedOn
    (unchangedOutside_iff_inRegions.mp h.walkFrame) (a := h.err) (n := 8) ?_
  intro k hk
  rintro ⟨r, hr, hlo, hhi⟩
  rcases List.mem_append.mp hr with hr | hr
  · have hout := stage2NoEventRunRegions_err_outside h.separate h.stagedSep r hr
    omega
  · rcases List.mem_cons.mp hr with rfl | hnil
    · -- the stack interval starts at or above every staged object's end
      have hend := h.watermark (h.err, 8) (by simp [stage2NoEventRegions, stage2NoEventWrites])
      omega
    · exact absurd hnil (by simp)

/-- **The stores make the record's post true, from the walk's report and the six
facts about the stores' memory.**  The facts are the store lemmas' own:
the three words' read-backs, the refusal slot's two sides, presence, and silence
outside the four written regions. -/
theorem stage2NoEventBoundary_of_parts {args : List Value} {mem m0 m : Mem}
    (h : Stage2NoEventRun args mem m0)
    (hTokens : readBytes m h.tokensOut 8 =
      some (wordBytes 8 (stage2NoEventWord h.refusal h.tok)))
    (hValues : readBytes m h.valuesOut 8 =
      some (wordBytes 8 (stage2NoEventWord h.refusal h.tok)))
    (hSum : readBytes m h.sumOut 8 =
      some (wordBytes 8 (stage2NoEventWord h.refusal
        ((byteSum h.arena + h.terms) % 2 ^ 64))))
    (hErrRefuse : h.refusal = true → readBytes m h.err 8 = some (wordBytes 8 h.eoff))
    (hErrAccept : h.refusal = false →
      readBytes m h.err 8 = readBytes m0 h.err 8)
    (hErrWalk : readBytes m0 h.err 8 = readBytes mem h.err 8)
    (_hpres : ∀ a, present m0 a → present m a)
    (hframeSlots : UnchangedOn (inRegions (stage2NoEventWrites h.tokensOut
      h.valuesOut h.sumOut h.err)) m0 m) :
    stage2NoEventBoundary args mem h.next0 m (.int 64 (stage2Verdict h.refusal)) := by
  -- the walk left the refusal slot as the caller staged it
  have herrWalk : readBytes m0 h.err 8 = readBytes mem h.err 8 := hErrWalk
  -- the frame: the run's list inside the post's
  have hwalkWide : UnchangedOutside mem m0
      (stage2NoEventWrites h.tokensOut h.valuesOut h.sumOut h.err ++
        (stage2NoEventRunRegions h.scratch h.scratchcap h.stk h.e h.c h.d ++
          [(h.next0, h.nextEnd - h.next0)])) :=
    UnchangedOutside.of_covered h.walkFrame fun r hr =>
      ⟨r, List.mem_append_right _ hr, le_refl _, le_refl _⟩
  have hframe : UnchangedOutside mem m
      (stage2NoEventWrites h.tokensOut h.valuesOut h.sumOut h.err ++
        (stage2NoEventRunRegions h.scratch h.scratchcap h.stk h.e h.c h.d ++
          [(h.next0, h.nextEnd - h.next0)])) := by
    intro a ha
    have hout : ¬ inRegions (stage2NoEventWrites h.tokensOut h.valuesOut h.sumOut
        h.err) a := by
      rintro ⟨r, hr, hi⟩
      exact ha r (List.mem_append_left _ hr) hi
    exact (hframeSlots a hout).trans (hwalkWide a ha)
  -- presence at the four words
  have hpresent : ∀ a, inRegions (stage2NoEventWrites h.tokensOut h.valuesOut
      h.sumOut h.err) a → present m a := by
    intro a ha
    obtain ⟨r, hr, hlo, hhi⟩ := ha
    simp only [stage2NoEventWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · have hk : a - h.tokensOut < 8 := by omega
      have hp := readBytes_some_present m h.tokensOut 8 _ hTokens (a - h.tokensOut) hk
      simpa [show h.tokensOut + (a - h.tokensOut) = a by omega] using hp
    · have hk : a - h.valuesOut < 8 := by omega
      have hp := readBytes_some_present m h.valuesOut 8 _ hValues (a - h.valuesOut) hk
      simpa [show h.valuesOut + (a - h.valuesOut) = a by omega] using hp
    · have hk : a - h.sumOut < 8 := by omega
      have hp := readBytes_some_present m h.sumOut 8 _ hSum (a - h.sumOut) hk
      simpa [show h.sumOut + (a - h.sumOut) = a by omega] using hp
    · -- the refusal slot: written on refusal, the caller's bytes on acceptance
      have hk : a - h.err < 8 := by omega
      have hread : readBytes m h.err 8 = some (wordBytes 8 h.eoff) ∨
          readBytes m h.err 8 = readBytes mem h.err 8 := by
        cases hb : h.refusal with
        | true => exact Or.inl (hErrRefuse hb)
        | false => exact Or.inr ((hErrAccept hb).trans herrWalk)
      rcases hread with hr' | hr'
      · have hp := readBytes_some_present m h.err 8 _ hr' (a - h.err) hk
        simpa [show h.err + (a - h.err) = a by omega] using hp
      · obtain ⟨vs, hvs⟩ := h.errBytes
        rw [← hr'] at hvs
        have hp := readBytes_some_present m h.err 8 vs hvs (a - h.err) hk
        simpa [show h.err + (a - h.err) = a by omega] using hp
  -- the three arms, at the verdict word
  refine stage2NoEventBoundary_of_witness
    (w :=
      { b := h.b, n := h.n, ep := h.ep, nep := h.nep, xp := h.xp, nxp := h.nxp,
        scratch := h.scratch, scratchcap := h.scratchcap, tokensOut := h.tokensOut,
        valuesOut := h.valuesOut, sumOut := h.sumOut, err := h.err,
        verdict := stage2Verdict h.refusal, tok := h.tok, terms := h.terms,
        bs := h.bs, arena := h.arena, obs := h.obs, toks := h.toks, stk := h.stk,
        e := h.e, c := h.c, d := h.d, nextEnd := h.nextEnd })
    (h := ?_)
  refine
    { args_eq := h.args_eq, value_eq := rfl,
      verdict_range := stage2Verdict_range h.refusal, doc := h.doc,
      accept_tokens := ?_, accept_values := ?_, accept_sum := ?_,
      accept_tok_le := ?_, accept_tok_lt := ?_, accept_rel := ?_,
      accept_len := ?_, accept_terms := ?_,
      refuse_tokens := ?_, refuse_values := ?_, refuse_sum := ?_,
      refuse_word := ?_, accept_word := ?_, present := hpresent,
      next_le := by show h.next0 ≤ h.nextEnd; have := h.nextEnd_static; omega,
      frame := hframe }
  · intro hone
    have hb := stage2Verdict_eq_one hone
    simpa [stage2NoEventWord, hb] using hTokens
  · intro hone
    have hb := stage2Verdict_eq_one hone
    simpa [stage2NoEventWord, hb] using hValues
  · intro hone
    have hb := stage2Verdict_eq_one hone
    simpa [stage2NoEventWord, hb] using hSum
  · intro hone
    have hb := stage2Verdict_eq_one hone
    exact h.tokLe
  · intro hone
    have hb := stage2Verdict_eq_one hone
    exact Nat.lt_of_le_of_lt h.tokLe h.nLt
  · intro hone
    have hb := stage2Verdict_eq_one hone
    exact h.rel
  · intro hone
    have hb := stage2Verdict_eq_one hone
    exact h.obsLen
  · intro hone
    have hb := stage2Verdict_eq_one hone
    exact h.termsEq
  · intro hzero
    have hb := stage2Verdict_eq_zero hzero
    simpa [stage2NoEventWord, hb] using hTokens
  · intro hzero
    have hb := stage2Verdict_eq_zero hzero
    simpa [stage2NoEventWord, hb] using hValues
  · intro hzero
    have hb := stage2Verdict_eq_zero hzero
    simpa [stage2NoEventWord, hb] using hSum
  · intro hzero
    have hb := stage2Verdict_eq_zero hzero
    exact ⟨h.eoff, h.offLe hb, hErrRefuse hb⟩
  · intro hone
    have hb := stage2Verdict_eq_one hone
    exact (hErrAccept hb).trans herrWalk

/-- **The stores make the boundary true.**  The facts about the stores' memory
are the emitted stores' own; `stage2NoEventBoundary_of_parts` consumes them. -/
theorem stage2NoEventRun_boundary_parts {args : List Value} {mem m0 : Mem}
    (h : Stage2NoEventRun args mem m0) :
    stage2NoEventBoundary args mem h.next0
      (stage2NoEventReport m0 h.tokensOut h.valuesOut h.sumOut h.err h.refusal
        h.tok ((byteSum h.arena + h.terms) % 2 ^ 64) h.eoff)
      (.int 64 (stage2Verdict h.refusal)) := by
  have hslots := stage2NoEventWrites_slots
    (stage2NoEventRegions_writes h.separate)
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hslots
  exact stage2NoEventBoundary_of_parts h
    (stage2NoEventReport_tokens m0 h.tokensOut h.valuesOut h.sumOut h.err
      h.refusal h.tok ((byteSum h.arena + h.terms) % 2 ^ 64) h.eoff h1 h2 h3)
    (stage2NoEventReport_values m0 h.tokensOut h.valuesOut h.sumOut h.err
      h.refusal h.tok ((byteSum h.arena + h.terms) % 2 ^ 64) h.eoff h4)
    (stage2NoEventReport_sum m0 h.tokensOut h.valuesOut h.sumOut h.err
      h.refusal h.tok ((byteSum h.arena + h.terms) % 2 ^ 64) h.eoff)
    (fun hr => by
      rw [hr]
      exact stage2NoEventReport_err_refusal m0 h.tokensOut h.valuesOut h.sumOut
        h.err h.tok ((byteSum h.arena + h.terms) % 2 ^ 64) h.eoff h3 h5 h6)
    (fun hr => by
      rw [hr]
      exact stage2NoEventReport_err_accept m0 h.tokensOut h.valuesOut h.sumOut
        h.err h.tok ((byteSum h.arena + h.terms) % 2 ^ 64) h.eoff h3 h5 h6)
    h.errFrame
    (fun a ha => stage2NoEventReport_present m0 h.tokensOut h.valuesOut h.sumOut
      h.err h.refusal h.tok ((byteSum h.arena + h.terms) % 2 ^ 64) h.eoff ha)
    (stage2NoEventReport_frame m0 h.tokensOut h.valuesOut h.sumOut h.err h.refusal
      h.tok ((byteSum h.arena + h.terms) % 2 ^ 64) h.eoff)

/-- **The stores make the record's post true.**  `Γ_stage2_noevent`'s post is
`stage2NoEventBoundary` at a non-`ub` outcome, and `stage2NoEventRun_boundary` is
`stage2NoEventRun_boundary_parts` read through it. -/
theorem stage2NoEventRun_boundary {args : List Value} {mem m0 : Mem}
    (h : Stage2NoEventRun args mem m0) :
    Γ_stage2_noevent.post args mem h.next0
      (.ret (some (.int 64 (stage2Verdict h.refusal)))
        (stage2NoEventReport m0 h.tokensOut h.valuesOut h.sumOut h.err h.refusal
          h.tok ((byteSum h.arena + h.terms) % 2 ^ 64) h.eoff)) :=
  stage2NoEventRun_boundary_parts h

/-! ### The call environment and the walk's obligation

The pinned body calls seven symbols.  Four resolve in `stage2Calls` (the lifetime
markers, `memset`, and the trap, which answers `none` because its arms are the
reserve checks' faults and the pre puts them out of reach).  Three are
sub-units, and the census's disposition is exact: `s2_string_body` and
`num_fast_el1` are the certified models, and `od_gap_recover` is the one symbol
this tree does not model — its C text is `kernel/json/stage2.c:898`, it is a plain
`static void` the certified fixture (`probes/install/ir/stage2.candidate.ll`)
happened to inline and the new body did not, and
**nothing in the tree supplies a model or a contract for it**.  So its selection
is the obligation's parameter, and it is the *only* free symbol: the three
modelled ones are fixed inside `stage2NoEventCalls`, because at an arbitrary
selection the statement is not a stronger theorem but a false one.  A future item
that wants to discharge the obligation begins by authoring that one model; the
parameter is the discharger's choice, not a universal quantification, so no proof
is expected at every `Calls`. -/

/-- The four objects the flattening appends, as the body's parameters. -/
def stage2NoEventStagingArgs (stk e c d : Nat) : List Value :=
  [.ptr stk, .ptr e, .ptr c, .ptr d]

/-- `stage2_noevent.h`'s twelve arguments followed by the four the flattening
appends. -/
def stage2NoEventArgs (a12 : List Value) (stk e c d : Nat) : List Value :=
  a12 ++ stage2NoEventStagingArgs stk e c d

/-- **The record at the flattened body**: the budget and the post read at the
twelve-slot prefix, and the precondition holds when the arguments are the ABI's
followed by the four staging objects and those objects are staged. -/
def Γ_stage2_noevent_at (stk e c d : Nat) : MemContract where
  budget := fun args mem => Γ_stage2_noevent.budget (args.take 12) mem
  pre := fun args mem next =>
    ∃ a12, args = stage2NoEventArgs a12 stk e c d ∧
      Γ_stage2_noevent.pre a12 mem next ∧
      stage2NoEventStagedPre a12 mem next stk e c d
  post := fun args mem next o => Γ_stage2_noevent.post (args.take 12) mem next o

/-- The adapter's prefix is the ABI's argument list. -/
theorem stage2NoEventArgs_take12 (a12 : List Value) (h : a12.length = 12)
    (stk e c d : Nat) :
    (stage2NoEventArgs a12 stk e c d).take 12 = a12 := by
  rw [stage2NoEventArgs, stage2NoEventStagingArgs]
  rw [List.take_append_of_le_length (by omega)]
  exact List.take_of_length_le (by omega)

/-- The record's precondition fixes the argument list. -/
theorem stage2NoEventPre_length {args : List Value} {mem : Mem} {next : Nat}
    (h : Γ_stage2_noevent.pre args mem next) : args.length = 12 := by
  obtain ⟨b, n, ep, nep, xp, nxp, scratch, scratchcap, tokensOut, valuesOut,
    sumOut, err, bs, ent, hargs, -⟩ := h
  subst hargs
  rfl

/-- **The record's precondition is the adapter's.** -/
theorem Γ_stage2_noevent_at_pre {a12 : List Value} {mem : Mem} {next : Nat}
    {stk e c d : Nat} (h : Γ_stage2_noevent.pre a12 mem next)
    (hstaged : stage2NoEventStagedPre a12 mem next stk e c d) :
    (Γ_stage2_noevent_at stk e c d).pre (stage2NoEventArgs a12 stk e c d) mem next :=
  ⟨a12, rfl, h, hstaged⟩

/-- **The no-event entry's call environment**: the three modelled sub-units fixed
to the certified models, and `od_gap_recover` from the parameter. -/
def stage2NoEventCalls (gap : Calls) : Calls :=
  fun callee args mem next =>
    if callee = "od_gap_recover" then gap callee args mem next
    else JsonStage2IR.stage2Calls stage2SubCalls callee args mem next

/-- **The walk's obligation at a staging: the pinned body, run with the selection
the record gives it.**

This is the loop, stated and **not inhabited**: a proof would be the completion
budget for a 167-block body plus the `Stage2NoEventRun` report it produces, and
nothing here supplies either.

It is also **conditional**, and the condition is not the loop.  The selection
fixes `s2_string_body`, `num_fast_el1` and the three intrinsic symbols to the
certified models, and takes `od_gap_recover`'s from `gap`; that helper's C text
is `kernel/json/stage2.c:898`, and nothing in this tree supplies a model or a
contract for it.  So the obligation is the loop relative to a contract at
`od_gap_recover`, and no current item discharges it: a future one begins by
authoring that model.  `gap` is the *discharger's choice*, not a universal
quantification — the statement is not to be proved at every `Calls`, and at an
arbitrary one it is false.

The **literal chain is inside this obligation**, not beside it.  The body's
scalar-literal compare is emitted as an unrolled `icmp eq i8` chain with packed
immediates, so it is body text this `Satisfies` quantifies over.
`neLitCheck_eq_litCheck` states the *rule* the model uses — the same verdict and
the same offset as the certified `lit_check` at every token/literal pair — and
its constants are pinned against the fixture's phis; that the emitted chain
computes this rule is a fact about the body's trace, which is exactly what this
obligation names and nothing here assumes.  A reader of the lemma must not read
it as covering the emitted code. -/
def Stage2NoEventWalkObligation (gap : Calls) (stk e c d : Nat) : Prop :=
  Satisfies (stage2NoEventCalls gap) stage2NoEventBody
    (Γ_stage2_noevent_at stk e c d)

/-- The obligation's own vocabulary: a body's `Satisfies` is a completion at the
record's budget and the post of the outcome it reaches.  This is a restatement,
not a proof of either conjunct. -/
theorem Stage2NoEventWalkObligation.summary (gap : Calls) (stk e c d : Nat)
    (h : Stage2NoEventWalkObligation gap stk e c d) :
    ∀ args mem next,
      (Γ_stage2_noevent_at stk e c d).pre args mem next →
      (∃ v m, runFuel (stage2NoEventCalls gap)
          ((Γ_stage2_noevent_at stk e c d).budget args mem) stage2NoEventBody
          (EntryState stage2NoEventBody args mem next) = some (.ret v m)) ∧
      ∀ o, BehFromState (stage2NoEventCalls gap) stage2NoEventBody
          (EntryState stage2NoEventBody args mem next) o →
        (Γ_stage2_noevent_at stk e c d).post args mem next o := h

/-- The stage-2 selection at a staging: `envForUnit` at the pinned body, with the
adapter's arguments appended. -/
def envForStage2NoEvent (gap : Calls) (stk e c d : Nat) : Calls :=
  fun callee args mem next =>
    envForUnit "leanllvm_json_stage2_noevent" (Γ_stage2_noevent_at stk e c d)
      (stage2NoEventCalls gap) stage2NoEventBody callee
      (stage2NoEventArgs args stk e c d) mem next

/-- **The walk resolves at the record, given its obligation, its pin, and the four
objects' staging.**  The `Satisfies` hypothesis is the walk's own obligation — the
thing this module names and does not discharge — and `retsValued` is read off the
pinned AST by `stage2NoEventBody_retsValued`. -/
theorem satisfies_calls_stage2_noevent {gap : Calls} (stk e c d : Nat)
    (hwalk : Satisfies (stage2NoEventCalls gap) stage2NoEventBody
      (Γ_stage2_noevent_at stk e c d))
    (hstaged : ∀ {args : List Value} {mem : Mem} {next : Nat},
      Γ_stage2_noevent.pre args mem next →
        stage2NoEventStagedPre args mem next stk e c d) :
    CallSatisfies (envForStage2NoEvent gap stk e c d) Γ_stage2_noevent
      "leanllvm_json_stage2_noevent" := by
  intro args mem next hpre
  obtain ⟨r, hsome, hpost, hnext⟩ :=
    satisfies_calls (calls := stage2NoEventCalls gap) (body := stage2NoEventBody)
      (Γ := Γ_stage2_noevent_at stk e c d) (sym := "leanllvm_json_stage2_noevent")
      hwalk stage2NoEventBody_retsValued (stage2NoEventArgs args stk e c d) mem next
      (Γ_stage2_noevent_at_pre hpre (hstaged hpre))
  have htake : (stage2NoEventArgs args stk e c d).take 12 = args :=
    stage2NoEventArgs_take12 args (stage2NoEventPre_length hpre) stk e c d
  exact ⟨r, by simpa [envForStage2NoEvent] using hsome,
    by simpa [Γ_stage2_noevent_at, htake] using hpost, hnext⟩

/-! ### The encoding, bound to the fold

The entry's accumulations are the consumer's fold's, so the constants they use
must be the encoding's.  The theorem below binds the three record widths, the
seven tag bytes, the number's tag constant, and the plain-string payload bit to
`EventRecord.encodedBytes` and `EventRecord.terms`; the text pin beside it binds
the tag constants to `kernel/json/stage2.c`. -/

/-- The plain-string payload bit, as the record's field. -/
theorem stage2NoEvent_encoding :
    -- the seven one-byte tags: `T_OBJ`, `T_OBJ_END`, `T_ARR`, `T_ARR_END`,
    -- `T_TRUE`, `T_FALSE`, `T_NULL`
    (∀ t ∈ [(1 : Nat), 2, 3, 4, 8, 9, 10],
      tagRecord t = [UInt8.ofNat t] ∧ (tagRecord t).length = 1 ∧
        EventRecord.terms (.tag t) = t) ∧
    -- the number: `T_NUM` and the eight payload bytes, nine in all
    (∀ bits : Nat,
      numberRecordBytes bits = [UInt8.ofNat stage2TagNum] ++ wordBytes 8 bits ∧
        (numberRecordBytes bits).length = 9 ∧
        EventRecord.terms (.number bits) = stage2TagNum + bits) ∧
    -- a key or string: the tag, four length bytes, eight field bytes, thirteen
    (∀ (key : Bool) (len span : Nat),
      strRecordBytes key len span =
          [UInt8.ofNat (if key then EventRecord.tagKey else EventRecord.tagStr)] ++
            wordBytes 4 len ++ wordBytes 8 span ∧
        (strRecordBytes key len span).length = 13 ∧
        EventRecord.terms (.str key len span) =
          (if key then EventRecord.tagKey else EventRecord.tagStr) + len + span) ∧
    -- the plain-string payload bit: the field is the body's first byte with the
    -- top bit set, and its low sixty-three bits are the byte's offset
    (∀ (key : Bool) (len bodyStart : Nat),
      strRecordBytes key len (plainSpan bodyStart) =
          [UInt8.ofNat (if key then EventRecord.tagKey else EventRecord.tagStr)] ++
            wordBytes 4 len ++ wordBytes 8 (bodyStart + 2 ^ 63) ∧
        2 ^ 63 ≤ plainSpan bodyStart ∧ plainSpan bodyStart - 2 ^ 63 = bodyStart) ∧
    -- the tag constants the sum's arithmetic reads
    EventRecord.tagKey = 5 ∧ EventRecord.tagStr = 6 ∧ stage2TagNum = 7 := by
  refine ⟨?_, ?_, ?_, ?_, rfl, rfl, rfl⟩
  · intro t ht
    exact ⟨rfl, rfl, rfl⟩
  · intro bits
    exact ⟨rfl, by simp [numberRecordBytes, EventRecord.encodedBytes, numberRecord,
      wordBytes, natToBytes_length], rfl⟩
  · intro key len span
    refine ⟨rfl, ?_, rfl⟩
    simp [strRecordBytes, EventRecord.encodedBytes, wordBytes, natToBytes_length]
  · intro key len bodyStart
    exact ⟨rfl, Nat.le_of_not_lt (plainSpan_not_lt bodyStart), plainSpan_sub bodyStart⟩

-- The text pin: the tag constants are `stage2.c`'s, and the search discriminates.
#guard occurs stage2Src "T_OBJ = 1, T_OBJ_END = 2, T_ARR = 3, T_ARR_END = 4,"
#guard occurs stage2Src "T_KEY = 5, T_STR = 6, T_NUM = 7, T_TRUE = 8, T_FALSE = 9, T_NULL = 10"
#guard !occurs stage2Src "T_OBJ = 0, T_OBJ_END = 2, T_ARR = 3, T_ARR_END = 4,"
#guard occurs stage2Src "static int lit_check(const uint8_t *p, uint64_t n, const char *lit, uint32_t ln,"

/-! ### The consumer-boundary corollary

Item 1's `stage2Boundary_noEventConsumer` projects the certified post's trace to
the consumer's vocabulary.  Read once at the certified post, it identifies the
new post's arena and events with the certified trace's; the new post's words are
then the certified consumer's readings, modulo the sum's word.  This is one
instantiation of that theorem — the trace projection, the reader's equality and
the two folds' equality are its conclusions, not steps repeated here. -/

/-- **The new post's words are the certified consumer's readings.**  The certified
post supplies the trace, the parse and the emitted stream; the new post supplies
the arena prefix and the events.  On acceptance the two count words hold the
certified consumer's token count and the sum word holds its sum modulo `2 ^ 64`.
The bridge between the two runs is the hypothesis that the no-event entry's
existential arena and events are the certified trace's decoded prefix and its
consumer rows — which is what the differential compares, and what a refinement of
this entry would establish. -/
theorem stage2NoEventBoundary_consumer {args : List Value} {mem : Mem} {next : Nat}
    {m : Mem} {v : Value} {w : Stage2NoEventWitness}
    (h : Stage2NoEventFacts w args mem next m v) (hacc : w.verdict = 1)
    {bw : Stage2BoundaryWitness} {argsC : List Value} {memC mC : Mem} {nextC : Nat}
    {vC : Value} {bs : List UInt8} {t : Tape} {rs : List EventRecord}
    (hcert : Stage2BoundaryFacts bw argsC memC nextC mC vC)
    (hbs : readBytes memC bw.b bw.n = some bs)
    (hcertAcc : bw.verdict = 1)
    (hparse : parseBytes Limits.default (ByteString.literal bs) = .ok t)
    (hrecs : bw.evs = (rs.map EventRecord.encodedBytes).flatten)
    (hb : ∀ r ∈ rs, r.Bounded)
    (hrel : Stage2Records bs (bw.arena.take bw.ndstU) rs t.tokens)
    (harena : w.arena = bw.arena.take bw.ndstU)
    (hobs : w.obs = consumeRecords bs (bw.arena.take bw.ndstU) rs) :
    readBytes m w.tokensOut 8 = some (wordBytes 8
        (consumeBytesResult bs (bw.arena.take bw.ndstU) bw.evs).tokens) ∧
      readBytes m w.valuesOut 8 = some (wordBytes 8
        (consumeBytesResult bs (bw.arena.take bw.ndstU) bw.evs).values) ∧
      readBytes m w.sumOut 8 = some (wordBytes 8
        ((consumeBytesResult bs (bw.arena.take bw.ndstU) bw.evs).sum % 2 ^ 64)) := by
  obtain ⟨obs, pv, hno, hobsEq, hconsume, hdecode, hbytes, hfold, hdec, hsep,
    hused, hevs⟩ :=
    stage2Boundary_noEventConsumer hcert hbs hcertAcc hparse hrecs hb hrel
  -- the trace's events and the new post's are the same list
  have hobs' : w.obs = obs := by rw [hobs, ← hobsEq]
  -- the reader's result is the certified consumer's
  have hconsumed : consumeBytesResult bs (bw.arena.take bw.ndstU) bw.evs =
      consumer (bw.arena.take bw.ndstU) rs := hbytes
  -- token count
  have hlenObs : rs.length = w.obs.length := by
    rw [hobs', hobsEq]
    simp [consumeRecords]
  have htok : (consumeBytesResult bs (bw.arena.take bw.ndstU) bw.evs).tokens = w.tok := by
    rw [hconsumed]
    simp only [consumer]
    rw [hlenObs, h.accept_len hacc]
  have hval : (consumeBytesResult bs (bw.arena.take bw.ndstU) bw.evs).values = w.tok := by
    rw [hconsumed]
    simp only [consumer]
    rw [hlenObs, h.accept_len hacc]
  -- sum
  have hsumRes : (consumeBytesResult bs (bw.arena.take bw.ndstU) bw.evs).sum =
      byteSum w.arena + w.terms := by
    rw [hconsumed, hfold, harena]
    simp only [noEventFold, hobs', h.accept_terms hacc]
  refine ⟨?_, ?_, ?_⟩
  · rw [h.accept_tokens hacc, htok]
  · rw [h.accept_values hacc, hval]
  · rw [h.accept_sum hacc, hsumRes]

/-! ### The literal compare

`ne_lit` compares a token's bytes against a packed immediate, because the fragment
has no module-global `const char *` to hand the certified `lit_check`.  The rule
is the same, and this section proves it: the loop walks the packed word's low
`ln` bytes (each `(uint8_t)(lit >> (8 * i))`), stops at the first that differs,
stops at the token's end if it is shorter, and refuses at `ln` if the token is
longer.  `litCheck` is the certified rule (`JsonStage2Body`). -/

/-- The literal's bytes as `ne_lit` reads them out of the packed word:
`(uint8_t)(lit >> (8 * i))` for each `i < ln`. -/
def packBytes (lit ln : Nat) : List UInt8 :=
  (List.range ln).map fun i => UInt8.ofNat ((lit >>> (8 * i)) % 256)

/-- `ne_lit`'s loop, over the literal's bytes and an offset. -/
def neLitGo : Nat → List UInt8 → List UInt8 → Option Nat
  | _, [], [] => none
  | i, [], _ :: _ => some i
  | i, _ :: _, [] => some i
  | i, c :: cs, b :: bs => if c = b then neLitGo (i + 1) cs bs else some i

/-- `ne_lit`'s rule: the loop from offset zero. -/
def neLitCheck (q litBytes : List UInt8) : Option Nat := neLitGo 0 q litBytes

/-- **The loop, at an offset.**  A first difference at `i` and a length difference
are both the certified rule's, shifted by the offset. -/
theorem neLitGo_eq_litCheck : ∀ (i : Nat) (q litBytes : List UInt8),
    neLitGo i q litBytes = (litCheck q litBytes).map (· + i)
  | i, [], [] => by simp [neLitGo, litCheck]
  | i, [], _ :: _ => by simp [neLitGo, litCheck]
  | i, _ :: _, [] => by simp [neLitGo, litCheck]
  | i, c :: cs, b :: bs => by
      have hstep : neLitGo i (c :: cs) (b :: bs) =
          if c = b then neLitGo (i + 1) cs bs else some i := rfl
      rw [hstep]
      by_cases hcb : c = b
      · rw [ite_eq_left hcb]
        rw [neLitGo_eq_litCheck (i + 1) cs bs]
        rw [litCheck]
        rw [ite_eq_left hcb]
        rw [Option.map_map]
        congr 1
        funext x
        simp only [Function.comp_apply]
        omega
      · rw [ite_eq_right hcb]
        rw [litCheck]
        rw [ite_eq_right hcb]
        simp

/-- **`ne_lit`'s rule is `lit_check`'s.**  Same verdict, same offset: the first
position that differs, the token's end when it is shorter than the literal, and
the literal's width when it is longer. -/
theorem neLitCheck_eq_litCheck (q litBytes : List UInt8) :
    neLitCheck q litBytes = litCheck q litBytes := by
  unfold neLitCheck
  rw [neLitGo_eq_litCheck]
  cases litCheck q litBytes <;> rfl

/-- The three packed immediates the pinned body carries, and their widths. -/
def neLitTrue : Nat := 1702195828
def neLitFalse : Nat := 435728179558
def neLitNull : Nat := 1819047278

/-- `true`'s packed immediate is the little-endian word of its bytes. -/
theorem packBytes_true : packBytes neLitTrue 4 = [0x74, 0x72, 0x75, 0x65] := by
  decide

/-- `false`'s. -/
theorem packBytes_false : packBytes neLitFalse 5 =
    [0x66, 0x61, 0x6C, 0x73, 0x65] := by
  decide

/-- `null`'s. -/
theorem packBytes_null : packBytes neLitNull 4 = [0x6E, 0x75, 0x6C, 0x6C] := by
  decide

/-- **`ne_lit` at `true`.** -/
theorem neLitCheck_true (q : List UInt8) :
    neLitCheck q (packBytes neLitTrue 4) =
      litCheck q [0x74, 0x72, 0x75, 0x65] := by
  rw [neLitCheck_eq_litCheck, packBytes_true]

/-- **`ne_lit` at `false`.** -/
theorem neLitCheck_false (q : List UInt8) :
    neLitCheck q (packBytes neLitFalse 5) =
      litCheck q [0x66, 0x61, 0x6C, 0x73, 0x65] := by
  rw [neLitCheck_eq_litCheck, packBytes_false]

/-- **`ne_lit` at `null`.** -/
theorem neLitCheck_null (q : List UInt8) :
    neLitCheck q (packBytes neLitNull 4) =
      litCheck q [0x6E, 0x75, 0x6C, 0x6C] := by
  rw [neLitCheck_eq_litCheck, packBytes_null]

/-- The certified literal rule's three literal byte strings, as the walk's own
`stage2Literal` names them. -/
theorem stage2Literal_eq_litCheck (q : List UInt8) :
    litCheck q [0x74, 0x72, 0x75, 0x65] =
        litCheck q ((stage2Literal 8).getD []) ∧
      litCheck q [0x66, 0x61, 0x6C, 0x73, 0x65] =
        litCheck q ((stage2Literal 9).getD []) ∧
      litCheck q [0x6E, 0x75, 0x6C, 0x6C] =
        litCheck q ((stage2Literal 10).getD []) := by
  refine ⟨?_, ?_, ?_⟩ <;> rfl

/-! ### The literal constants in the pinned body

The pinned body's compare is the unrolled loop with the three packed constants,
their widths and their tags.  These guards read the fixture and assert that the
constants the rule above is stated at are the constants the body carries, so a
re-capture with a different literal fails here rather than silently diverging. -/

/-- The immediate `i64` values of a `phi` named `dst`, in text order. -/
def phiImms (f : Function) (dst : String) : List Nat :=
  (f.blocks.flatMap (·.instrs)).flatMap fun i =>
    match i with
    | .phi d _ inc =>
        if d = dst then
          inc.filterMap fun p =>
            match p.2 with
            | .imm (.int 64 v) => some v.toNat
            | _ => none
        else []
    | _ => []

#guard phiImms stage2NoEventBody "%lit.0" = [neLitFalse, neLitNull, neLitTrue]
#guard phiImms stage2NoEventBody "%ln.0" = [5, 4, 4]
#guard phiImms stage2NoEventBody "%tag.0" = [9, 10, 8]

/-! ### Axiom footprints -/

#print axioms stage2NoEventReport
#print axioms stage2NoEventBoundary_of_parts
#print axioms stage2NoEventRun_boundary_parts
#print axioms stage2NoEventRun_boundary
#print axioms satisfies_calls_stage2_noevent
#print axioms stage2NoEvent_encoding
#print axioms stage2NoEventBoundary_consumer
#print axioms neLitCheck_eq_litCheck
#print axioms neLitCheck_true

end LeanLLVM.Refinement
