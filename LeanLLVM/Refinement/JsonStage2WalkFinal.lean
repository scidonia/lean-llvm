/-
The stage-2 walk's last class-F link: `if.then425.i`, the scalar value's record.

`if.then425.i` calls `od_scalar_value` at the cursor record, the token's staging
and the log, and branches on the answer: the emitting arm appends the token's
record to the trace, and the refusing arm leaves the carry where it was.  The
contract's post (`s2ScalarValuePost`) names the appended record as an
`EventRecord`, so the carrying arm is the same shape `if.then328.i` proved for a
block's own stores — the trace's `events`, `evlen_eq` and `evBytes` advance, the
frame widens with the cursor, and the log's other four fields are read across the
two writes.  The refusing arm's writes are the error record's two words, which are
inside the staged error extent and outside the log, the event stream and every
carried byte; its carry is the source's.

The log's buffer word at `%z` is the caller's fact (`hzread`), as it is for
`if.then328.i`: the invariant binds the four fields from `%z + 8` on, and the
emitted body stored `%ev` at `%z` in `entry`.  The refusal's address is the staged
one (`%c.i + 1112`'s pointer), so the link takes the model's `stage2ErrSetMsg`
shape at `C.stage.e` — all three of `err_set`'s fields, the message word
included.
-/
import LeanLLVM.Refinement.JsonStage2WalkCall

set_option autoImplicit false

namespace LeanLLVM.Refinement

open LeanLLVM
open LeanLLVM.Refinement.JsonStage2IR
open LeanLLVM.Refinement.JsonStage2IR (stage2Calls)
open LeanLLVM.Refinement.BlockEval
open LeanLLVM.Refinement.JsonEntrySteps (denoteCode_lookupName)
open LeanLLVM.Refinement.JsonS1MasksIR

namespace WalkScope


/-- A little-endian eight-byte word round-trips through `bytesToNat` below
`2 ^ 64`. -/
theorem walkBytesToNat_word8 {n : Nat} (h : n < 2 ^ 64) :
    bytesToNat (wordBytes 8 n) = n := by
  rw [wordBytes, natToBytes_toNat, show (256 : Nat) ^ 8 = 2 ^ 64 from by decide,
    Nat.mod_eq_of_lt h]

/-- `if.then425.i`: `od_scalar_value`, then the test on its answer. -/
def walkIfThen425 : Block :=
  { name := "if.then425.i",
    instrs := [
      Instr.call "%call427.i" (Ty.int 32) "od_scalar_value"
        [(Ty.ptr, Operand.reg "%c.i"), (Ty.ptr, Operand.reg "%t352.i"),
         (Ty.ptr, Operand.reg "%z")],
      Instr.icmp "%tobool428.not.i" IPred.eq 32 (Operand.reg "%call427.i")
        (Operand.imm (.int 32 (BitVec.ofNat 32 0)))],
    term := Term.condbr (Operand.reg "%tobool428.not.i") "if.then432.i" "if.then447.i" }

theorem walkIfThen425_find : stage2Body.findBlock "if.then425.i" = some walkIfThen425 := by
  simp [stage2Body, Function.findBlock, findBlockList, walkIfThen425]

theorem walkIfThen425_denote {sub : Calls} (env : Env) (s : State)
    {c t o : Nat} {x : BitVec 32} {r : CallOutcome}
    (hc : lookupName env "%c.i" = some (.ptr c))
    (ht : lookupName env "%t352.i" = some (.ptr t))
    (ho : lookupName env "%z" = some (.ptr o))
    (hcall : stage2Calls sub "od_scalar_value" [.ptr c, .ptr t, .ptr o]
      s.mem s.next = some r)
    (hretv : r.ret = .int 32 x) :
    denoteCode (stage2Calls sub) walkIfThen425.instrs (stateAt env s) =
      some (stateAt (cells [
        ("%tobool428.not.i", .int 1 (evalICmp .eq x (BitVec.ofNat 32 0))),
        ("%call427.i", .int 32 x)] env) { s with mem := r.mem, next := r.next }) := by
  simp only [walkIfThen425]
  rw [walkDenoteCode_call (calls := stage2Calls sub) (env := env) (s := s)
    (d := "%call427.i") (callee := "od_scalar_value") (ty := .int 32)
    (walkArgs_scalarValue env s hc ht ho) hcall]
  rw [denoteCode_icmp_eq_imm_w (calls := stage2Calls sub)
    (env := ("%call427.i", r.ret) :: env)
    (s := { s with mem := r.mem, next := r.next })
    (d := "%tobool428.not.i") (a := "%call427.i") (w := 32)
    (x := x) (c := BitVec.ofNat 32 0)
    (by rw [lookupName_cons_self]; exact congrArg some hretv) []]
  simp only [cells, stateAt, hretv]
  rfl

/-- **`if.then425.i` on the emitting arm**: `od_scalar_value` appended the token's
record, the answer is `1`, and the branch takes the escape scan's entry with the
carry's trace advanced by the record. -/
theorem WalkLink.if_then425_i_emit {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G)
    (s : State) (hInv : WalkInv G C s) (hblock : C.block = "if.then425.i")
    {ev : EventRecord} {r : CallOutcome}
    (hc : lookupName s.env "%c.i" = some (.ptr C.stage.c))
    (ht : lookupName s.env "%t352.i" = some (.ptr C.stage.tok))
    (ho : lookupName s.env "%z" = some (.ptr C.stage.z))
    (hzread : readBytes s.mem C.stage.z 8 = some (wordBytes 8 G.ev))
    (hcall : stage2Calls stage2SubCalls "od_scalar_value"
      [.ptr C.stage.c, .ptr C.stage.tok, .ptr C.stage.z] s.mem s.next = some r)
    (happ : s2ScalarValueAppend s.mem r.mem C.stage.z ev.encodedBytes)
    (hret : r.ret = .int 32 (BitVec.ofNat 32 1))
    (hev64 : G.ev < 2 ^ 64) (hevlen64 : C.evlen < 2 ^ 64)
    (hlt : C.events.length < C.k) :
    ∃ s', WalkLink (stage2Calls stage2SubCalls) G C s
      { C with block := "if.then447.i",
               evlen := C.evlen + ev.encodedSize,
               events := C.events ++ [ev] } s' := by
  obtain ⟨buf, len, hbuf, hlen, hmeq⟩ := happ
  have hbuf' : buf = G.ev := by
    simp only [stage2ReadWord, hzread, Option.map_some, Option.some.injEq] at hbuf
    rw [walkBytesToNat_word8 hev64] at hbuf
    exact hbuf.symm
  have hlen' : len = C.evlen := by
    simp only [stage2ReadWord, hInv.log_len, Option.map_some, Option.some.injEq] at hlen
    rw [walkBytesToNat_word8 hevlen64] at hlen
    exact hlen.symm
  subst hbuf'; subst hlen'
  let nl := C.evlen + ev.encodedBytes.length
  let s₁ : State := stateAt (cells [
    ("%tobool428.not.i", .int 1 (evalICmp .eq (BitVec.ofNat 32 1) (BitVec.ofNat 32 0))),
    ("%call427.i", .int 32 (BitVec.ofNat 32 1))] s.env) { s with mem := r.mem, next := r.next }
  have hden : denoteCode (stage2Calls stage2SubCalls) walkIfThen425.instrs s =
      some s₁ := by
    dsimp only [s₁]
    exact walkIfThen425_denote (sub := stage2SubCalls) (env := s.env) (s := s)
      (c := C.stage.c) (t := C.stage.tok) (o := C.stage.z)
      (x := BitVec.ofNat 32 1) (r := r) hc ht ho hcall hret
  have hpc : s.pc = C.block := hInv.pc_eq
  have hbit : evalICmp .eq (BitVec.ofNat 32 1) (BitVec.ofNat 32 0)
      = (0 : BitVec 1) := by decide
  let s' : State := { s₁ with pc := "if.then447.i", pre := some s.pc }
  have hstep : LeanLLVM.step (stage2Calls stage2SubCalls) stage2Body s = Ctrl.jump s' := by
    have hfind : stage2Body.findBlock s.pc = some walkIfThen425 := by
      rw [hpc, hblock]; exact walkIfThen425_find
    have hterm : walkIfThen425.term =
        Term.condbr (Operand.reg "%tobool428.not.i") "if.then432.i" "if.then447.i" := rfl
    simp only [LeanLLVM.step, hfind, hden, hterm]
    rw [walkExecTerm_condbr (d := "%tobool428.not.i") (tl := "if.then432.i")
      (fl := "if.then447.i") (bit := (0 : BitVec 1))
      (by dsimp only [s₁]; simp [stateAt, cells, lookupName, hbit])]
    dsimp only [s', s₁, cells, stateAt]
    simp only [hbit]
    rfl
  have hEvLen : (C.events.map EventRecord.encodedBytes).flatten.length =
      (C.events.map EventRecord.encodedSize).sum := by
    simp only [List.length_flatten, List.map_map]; rfl
  have hrecLen : ev.encodedBytes.length = ev.encodedSize := rfl
  have hflat : ((C.events ++ [ev]).map EventRecord.encodedBytes).flatten =
      (C.events.map EventRecord.encodedBytes).flatten ++ ev.encodedBytes := by
    rw [List.map_append, List.flatten_append]
    simp
  have hEvNew : C.evlen = G.nev0 + (C.events.map EventRecord.encodedBytes).flatten.length := by
    rw [hInv.evlen_eq, hEvLen]
  have hNev : G.nev0 +
      ((C.events.map EventRecord.encodedBytes).flatten.length + ev.encodedBytes.length) ≤ G.evcap := by
    have hsum := EventRecord.sum_encodedSize_le C.events
    simp only [stage2RecordBytes] at hsum
    have hroom := G.evRoom
    simp only [stage2RecordBytes] at hroom
    have h1 := hlt; have h2 := hInv.k_le; have h3 := G.nep_le
    have h4 := EventRecord.encodedSize_le ev
    simp only [stage2RecordBytes] at h4
    rw [hEvLen, hrecLen]
    omega
  have hmem : r.mem = writeBytes (writeBytes s.mem (G.ev + C.evlen) ev.encodedBytes)
      (C.stage.z + 8) (wordBytes 8 (C.evlen + ev.encodedBytes.length)) := hmeq
  have hzev := walkLog_ev_sep hInv
  simp only [stage2LogExtent] at hzev
  -- the event trace's read after the two writes
  have hevBytes' : readBytes r.mem (G.ev + G.nev0)
      ((C.events ++ [ev]).map EventRecord.encodedBytes).flatten.length =
      some ((C.events ++ [ev]).map EventRecord.encodedBytes).flatten := by
    rw [hflat]
    rw [List.length_append]
    rw [hmem]
    have hsep : (G.ev + G.nev0) +
        ((C.events.map EventRecord.encodedBytes).flatten.length + ev.encodedBytes.length) ≤
        C.stage.z + 8 ∨ (C.stage.z + 8) + (wordBytes 8 (C.evlen + ev.encodedBytes.length)).length ≤
        (G.ev + G.nev0) := by
      rw [wordBytes, natToBytes_length]
      rcases hzev with h | h
      · right; omega
      · left; omega
    rw [walkReadBytes_writeBytes_outside (start := C.stage.z + 8)
      (addr := G.ev + G.nev0)
      (n := (C.events.map EventRecord.encodedBytes).flatten.length + ev.encodedBytes.length)
      (v := wordBytes 8 (C.evlen + ev.encodedBytes.length)) hsep]
    rw [show (G.ev + C.evlen) = (G.ev + G.nev0) +
        (C.events.map EventRecord.encodedBytes).flatten.length from by rw [hEvNew]; omega]
    exact walkReadBytes_writeBytes_append (m := s.mem) (a := G.ev + G.nev0)
      (N := (C.events.map EventRecord.encodedBytes).flatten.length) hInv.evBytes
  -- the log's four other fields across the two writes
  have hlogRead : ∀ off w, 16 ≤ off → off + w ≤ stage2LogExtent →
      readBytes r.mem (C.stage.z + off) w = readBytes s.mem (C.stage.z + off) w := by
    intro off w hoff hw
    rw [hmem]
    rw [walkReadBytes_log_of_log_write (m := writeBytes s.mem (G.ev + C.evlen) ev.encodedBytes)
      (off := 8) (off' := off) (N := w) (v := wordBytes 8 (C.evlen + ev.encodedBytes.length))
      (by
        rw [wordBytes, natToBytes_length]
        right; omega)]
    have hlenv : C.evlen + ev.encodedBytes.length ≤ G.evcap := by
      rw [hEvNew]; omega
    refine walkReadBytes_log_of_write (m := s.mem) (z := C.stage.z)
      (a := G.ev + C.evlen) (w := ev.encodedBytes.length) (off := off) (w' := w)
      (bs := ev.encodedBytes) (by simp [hrecLen]) ?_ hw
    rcases hzev with h | h
    · right
      simp only [stage2LogExtent]
      omega
    · left
      calc G.ev + C.evlen + ev.encodedBytes.length
          ≤ G.ev + G.evcap := by have := hlenv; omega
        _ ≤ C.stage.z := h
  have hlogLen' : readBytes r.mem (C.stage.z + 8) 8 = some (wordBytes 8 (C.evlen + ev.encodedBytes.length)) := by
    rw [hmem]
    exact readBytes_writeBytes_same (writeBytes s.mem (G.ev + C.evlen) ev.encodedBytes)
      (wordBytes 8 (C.evlen + ev.encodedBytes.length)) (addr := C.stage.z + 8)
  refine ⟨s', ⟨hInv, hstep, ?_, le_of_eq rfl⟩⟩
  refine
    { pc_eq := rfl
      blockIndex := ?_
      k_le := hInv.k_le
      events_le := by
        show (C.events ++ [ev]).length ≤ C.k
        simp only [List.length_append, List.length_singleton]; omega
      evlen_eq := ?_
      evBytes := hevBytes'
      alen_le_sum := hInv.alen_le_sum
      alen_ge := hInv.alen_ge
      spans_order := hInv.spans_order
      spans_end := hInv.spans_end
      spans_inside := hInv.spans_inside
      pending_at := hInv.pending_at
      pending_cursor := hInv.pending_cursor
      pending_len := hInv.pending_len
      eoff_le := hInv.eoff_le
      inner_cap := hInv.inner_cap
      depth_cap := hInv.depth_cap
      depth_reg := ?_
      sp_le_wlen := hInv.sp_le_wlen
      wlen_cap := hInv.wlen_cap
      tyBytes := by
        dsimp only [s', s₁, stateAt]
        rw [hmem]
        have hwz : (wordBytes 8 (C.evlen + ev.encodedBytes.length)).length = 8 := by
          simp [wordBytes, natToBytes_length]
        have hL : stage2LogExtent = 64 := rfl
        have hcap := hInv.wlen_cap
        have hS : stage2StackExtent = 520 := rfl
        simp only [stage2StackExtent] at hcap
        refine (hInv.tyBytes.write_outside ?_).write_outside ?_
        · rcases ctype_ev_sep hInv with h | h
          · exact Or.inr (by omega)
          · refine Or.inl ?_
            have hv := hNev
            have he := hEvNew
            omega
        · rcases ctype_log_sep hInv with h | h
          · exact Or.inr (by omega)
          · exact Or.inl (by omega)
      stBytes := by
        dsimp only [s', s₁, stateAt]
        rw [hmem]
        have hwz : (wordBytes 8 (C.evlen + ev.encodedBytes.length)).length = 8 := by
          simp [wordBytes, natToBytes_length]
        have hL : stage2LogExtent = 64 := rfl
        have hcap := hInv.wlen_cap
        have hS : stage2StackExtent = 520 := rfl
        simp only [stage2StackExtent] at hcap
        refine (hInv.stBytes.write_outside ?_).write_outside ?_
        · rcases cst_ev_sep hInv with h | h
          · exact Or.inr (by omega)
          · refine Or.inl ?_
            have hv := hNev
            have he := hEvNew
            omega
        · rcases cst_log_sep hInv with h | h
          · exact Or.inr (by omega)
          · exact Or.inl (by omega)
      ptrs := ?_
      regs := ?_
      iter := ?_
      log_hash := ?_
      log_len := by
        show readBytes r.mem (C.stage.z + 8) 8 = some (wordBytes 8 (C.evlen + ev.encodedSize))
        rw [← hrecLen]; exact hlogLen'
      log_cap := ?_
      log_alen := ?_
      log_acap := ?_
      owned := ?_
      frame := ?_
      blockLocal := by simp [WalkLocal] }
  · rw [show s'.env = s₁.env from rfl]
    rw [denoteCode_lookupName (stage2Calls stage2SubCalls) walkIfThen425.instrs
      "%k.0.i249" (by refine fun i hi => ?_; simp only [walkIfThen425, List.mem_cons, List.not_mem_nil,
        or_false] at hi; rcases hi with rfl | rfl <;> decide) s s₁ hden]
    exact hInv.blockIndex
  · show C.evlen + ev.encodedSize = G.nev0 +
      (((C.events ++ [ev]).map EventRecord.encodedSize).sum)
    rw [List.map_append, List.sum_append]
    simp only [List.map_singleton, List.sum_singleton]
    have h := hInv.evlen_eq
    omega
  · rw [show s'.env = s₁.env from rfl]
    rw [denoteCode_lookupName (stage2Calls stage2SubCalls) walkIfThen425.instrs
      "%sp.i.0248" (by refine fun i hi => ?_; simp only [walkIfThen425, List.mem_cons, List.not_mem_nil,
        or_false] at hi; rcases hi with rfl | rfl <;> decide) s s₁ hden]
    exact hInv.depth_reg
  · rw [show s'.env = s₁.env from rfl]
    exact WalkPtrs.of_run hInv.ptrs (by unfold walkCarried; decide) hden
  · rw [show s'.env = s₁.env from rfl]
    exact WalkRegs.of_run hInv.regs (by unfold walkCarried; decide) hden
  · rw [show s'.env = s₁.env from rfl]
    exact WalkIter.of_run hInv.iter (by unfold walkCarried; decide) hden
  · show readBytes r.mem (C.stage.z + 32) 4 = some (natToBytes 0 4)
    rw [hlogRead 32 4 (by decide) (by decide)]; exact hInv.log_hash
  · show readBytes r.mem (C.stage.z + 16) 8 = some (wordBytes 8 G.evcap)
    rw [hlogRead 16 8 (by decide) (by decide)]; exact hInv.log_cap
  · obtain ⟨a, h0, ha, hr⟩ := hInv.log_alen
    exact ⟨a, h0, ha, Eq.trans (hlogRead 48 8 (by decide) (by decide)) hr⟩
  · show readBytes r.mem (C.stage.z + 56) 8 = some (wordBytes 8 G.dstcap)
    rw [hlogRead 56 8 (by decide) (by decide)]; exact hInv.log_acap
  · show ∀ q ∈ walkStaged G C, HasBytes r.mem q.1 q.2
    rw [hmem]
    exact walkStaged_write rfl (walkStaged_write rfl hInv.owned)
  · -- the frame at the wider cursor
    have h0 : UnchangedOutside m0 s.mem (walkWide G
        { C with block := "if.then447.i", evlen := C.evlen + ev.encodedSize,
                 events := C.events ++ [ev] }) :=
      hInv.frame.of_covered
        (walkWide_grow (Nat.le_refl _) (by simp only [hrecLen]; omega) rfl)
    have hmRec : (G.ev, C.evlen + ev.encodedBytes.length) ∈ walkWide G
        { C with block := "if.then447.i", evlen := C.evlen + ev.encodedSize,
                 events := C.events ++ [ev] } := by
      simp [walkWide, walkPresent, hrecLen]
    have hmLog : (C.stage.z, stage2LogExtent) ∈ walkWide G
        { C with block := "if.then447.i", evlen := C.evlen + ev.encodedSize,
                 events := C.events ++ [ev] } := by
      simp [walkWide, walkPresent, stage2ReportScratch, stage2StagedWrites]
    have h1 : UnchangedOutside s.mem r.mem (walkWide G
        { C with block := "if.then447.i", evlen := C.evlen + ev.encodedSize,
                 events := C.events ++ [ev] }) := by
      rw [hmem]
      refine UnchangedOutside.write_le
        (a := C.stage.z + 8) (w := 8)
        (UnchangedOutside.write_le (a := G.ev + C.evlen) (w := ev.encodedBytes.length)
          (UnchangedOutside.refl' s.mem _)
          ⟨(G.ev, C.evlen + ev.encodedBytes.length), hmRec, by omega, by omega⟩
          (bs := ev.encodedBytes) (by simp [hrecLen]))
        ⟨(C.stage.z, stage2LogExtent), hmLog, by omega,
          by simp only [stage2LogExtent]; omega⟩
        (bs := wordBytes 8 (C.evlen + ev.encodedBytes.length)) (by simp [wordBytes, natToBytes_length])
    exact h0.trans' h1


/-- **`if.then425.i`'s emit arm, with the answer named.**  `od_scalar_value` returned one
(its record appended), so `%tobool428.not.i` is zero and the run takes `if.then447.i` with
the event appended to the trace: the carry's `evlen` and `events` move, which the link's
conclusion already states. -/
theorem walkIfThen425_emit_at {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State)
    (hInv : WalkInv G C s) (hblock : C.block = "if.then425.i")
    {ev : EventRecord} {r : CallOutcome}
    (hc : lookupName s.env "%c.i" = some (.ptr C.stage.c))
    (ht : lookupName s.env "%t352.i" = some (.ptr C.stage.tok))
    (ho : lookupName s.env "%z" = some (.ptr C.stage.z))
    (hzread : readBytes s.mem C.stage.z 8 = some (wordBytes 8 G.ev))
    (hcall : stage2Calls stage2SubCalls "od_scalar_value"
      [.ptr C.stage.c, .ptr C.stage.tok, .ptr C.stage.z] s.mem s.next = some r)
    (happ : s2ScalarValueAppend s.mem r.mem C.stage.z ev.encodedBytes)
    (hret : r.ret = .int 32 (BitVec.ofNat 32 1))
    (hev64 : G.ev < 2 ^ 64) (hevlen64 : C.evlen < 2 ^ 64)
    (hlt : C.events.length < C.k) :
    ∃ (s' : State), WalkLink (stage2Calls stage2SubCalls) G C s
        { C with
          block := "if.then447.i"
          evlen := C.evlen + ev.encodedSize
          events := C.events ++ [ev] } s' ∧
      s' = { stateAt (cells [
          ("%tobool428.not.i", .int 1 (evalICmp .eq (BitVec.ofNat 32 1)
            (BitVec.ofNat 32 0))),
          ("%call427.i", .int 32 (BitVec.ofNat 32 1))] s.env)
          { s with mem := r.mem, next := r.next } with
        pc := "if.then447.i"
        pre := some s.pc } := by
  obtain ⟨s', hl⟩ := WalkLink.if_then425_i_emit (G := G) (C := C) (s := s) hInv hblock hc ht
    ho hzread hcall happ hret hev64 hevlen64 hlt
  refine ⟨s', hl, ?_⟩
  have hden : denoteCode (stage2Calls stage2SubCalls) walkIfThen425.instrs s =
      some (stateAt (cells [
          ("%tobool428.not.i", .int 1 (evalICmp .eq (BitVec.ofNat 32 1)
            (BitVec.ofNat 32 0))),
          ("%call427.i", .int 32 (BitVec.ofNat 32 1))] s.env)
        { s with mem := r.mem, next := r.next }) := by
    simpa only [stateAt] using (walkIfThen425_denote (sub := stage2SubCalls) (env := s.env)
      (s := s) (c := C.stage.c) (t := C.stage.tok) (o := C.stage.z)
      (x := BitVec.ofNat 32 1) (r := r) hc ht ho hcall hret)
  have hbit0 : evalICmp .eq (BitVec.ofNat 32 1) (BitVec.ofNat 32 0) = (0 : BitVec 1) := by
    decide
  have hbit : lookupName (stateAt (cells [
      ("%tobool428.not.i", .int 1 (evalICmp .eq (BitVec.ofNat 32 1)
        (BitVec.ofNat 32 0))),
      ("%call427.i", .int 32 (BitVec.ofNat 32 1))] s.env)
      { s with mem := r.mem, next := r.next }).env "%tobool428.not.i" =
      some (.int 1 (0 : BitVec 1)) := by
    simp only [stateAt, cells, lookupName_cons_self, hbit0]
  have hfind : stage2Body.findBlock s.pc = some walkIfThen425 := by
    rw [hInv.pc_eq, hblock]; exact walkIfThen425_find
  have hterm : walkIfThen425.term =
      Term.condbr (.reg "%tobool428.not.i") "if.then432.i" "if.then447.i" := rfl
  have hstep : step (stage2Calls stage2SubCalls) stage2Body s = Ctrl.jump
      { stateAt (cells [
          ("%tobool428.not.i", .int 1 (evalICmp .eq (BitVec.ofNat 32 1)
            (BitVec.ofNat 32 0))),
          ("%call427.i", .int 32 (BitVec.ofNat 32 1))] s.env)
          { s with mem := r.mem, next := r.next } with
        pc := "if.then447.i"
        pre := some s.pc } := by
    simp only [LeanLLVM.step, hfind, hden, hterm]
    rw [walkExecTerm_condbr (d := "%tobool428.not.i") (tl := "if.then432.i")
      (fl := "if.then447.i") (bit := (0 : BitVec 1)) hbit]
    dsimp only [stateAt]
    rfl
  exact Ctrl.jump.inj ((WalkLink.step hl).symm.trans hstep)

/-- **`if.then425.i` on the refusing arm**: `od_scalar_value` or `out_tag` refused,
the answer is `0`, the branch takes the refusal's continuation, and the carry is
the source's (the callee's writes are the error record, outside every clause). -/
theorem WalkLink.if_then425_i_refuse {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G)
    (s : State) (hInv : WalkInv G C s) (hblock : C.block = "if.then425.i")
    {r : CallOutcome} {pos : Nat}
    (hc : lookupName s.env "%c.i" = some (.ptr C.stage.c))
    (ht : lookupName s.env "%t352.i" = some (.ptr C.stage.tok))
    (ho : lookupName s.env "%z" = some (.ptr C.stage.z))
    (hcall : stage2Calls stage2SubCalls "od_scalar_value"
      [.ptr C.stage.c, .ptr C.stage.tok, .ptr C.stage.z] s.mem s.next = some r)
    (hrefuse : r.mem = stage2ErrSetMsg s.mem (C.stage.e) pos 0)
    (hret : r.ret = .int 32 (BitVec.ofNat 32 0)) :
    ∃ s', WalkLink (stage2Calls stage2SubCalls) G C s
      { C with block := "if.then432.i" } s' := by
  let s₁ : State := stateAt (cells [
    ("%tobool428.not.i", .int 1 (evalICmp .eq (BitVec.ofNat 32 0) (BitVec.ofNat 32 0))),
    ("%call427.i", .int 32 (BitVec.ofNat 32 0))] s.env) { s with mem := r.mem, next := r.next }
  have hden : denoteCode (stage2Calls stage2SubCalls) walkIfThen425.instrs s =
      some s₁ := by
    dsimp only [s₁]
    exact walkIfThen425_denote (sub := stage2SubCalls) (env := s.env) (s := s)
      (c := C.stage.c) (t := C.stage.tok) (o := C.stage.z)
      (x := BitVec.ofNat 32 0) (r := r) hc ht ho hcall hret
  have hpc : s.pc = C.block := hInv.pc_eq
  have hbit : evalICmp .eq (BitVec.ofNat 32 0) (BitVec.ofNat 32 0)
      = (1 : BitVec 1) := by decide
  let s' : State := { s₁ with pc := "if.then432.i", pre := some s.pc }
  have hstep : LeanLLVM.step (stage2Calls stage2SubCalls) stage2Body s = Ctrl.jump s' := by
    have hfind : stage2Body.findBlock s.pc = some walkIfThen425 := by
      rw [hpc, hblock]; exact walkIfThen425_find
    have hterm : walkIfThen425.term =
        Term.condbr (Operand.reg "%tobool428.not.i") "if.then432.i" "if.then447.i" := rfl
    simp only [LeanLLVM.step, hfind, hden, hterm]
    rw [walkExecTerm_condbr (d := "%tobool428.not.i") (tl := "if.then432.i")
      (fl := "if.then447.i") (bit := (1 : BitVec 1))
      (by dsimp only [s₁]; simp [stateAt, cells, hbit])]
    dsimp only [s', s₁, cells, stateAt]
    simp only [hbit]
    rfl
  have hez := e_z_sep hInv
  have heev := e_ev_sep hInv
  simp only [stage2ErrorExtent, stage2LogExtent] at hez heev
  have hNev : G.nev0 + (C.events.map EventRecord.encodedBytes).flatten.length ≤ G.evcap := by
    have hsum := EventRecord.sum_encodedSize_le C.events
    simp only [stage2RecordBytes] at hsum
    have hroom := G.evRoom
    simp only [stage2RecordBytes] at hroom
    have hlen : (C.events.map EventRecord.encodedBytes).flatten.length =
        (C.events.map EventRecord.encodedSize).sum := by
      simp only [List.length_flatten, List.map_map]; rfl
    rw [hlen]
    have h1 := hInv.events_le; have h2 := hInv.k_le; have h3 := G.nep_le
    omega
  -- a read of the log across the four-byte error store
  have herr4Log : ∀ off N, off + N ≤ stage2LogExtent →
      readBytes (writeBytes s.mem C.stage.e (wordBytes 4 0)) (C.stage.z + off) N =
      readBytes s.mem (C.stage.z + off) N := by
    intro off N hoff
    simp only [stage2LogExtent] at hoff
    refine walkReadBytes_writeBytes_outside (start := C.stage.e) (addr := C.stage.z + off)
      (n := N) (v := wordBytes 4 0) ?_
    rw [wordBytes, natToBytes_length]
    rcases hez with h | h
    · right
      exact Nat.le_trans (Nat.add_le_add_left (by decide : 4 ≤ 24) C.stage.e)
        (Nat.le_trans h (Nat.le_add_right C.stage.z off))
    · left
      rw [Nat.add_assoc]
      exact Nat.le_trans (Nat.add_le_add_left hoff C.stage.z) h
  have herr8Log2 : ∀ off N, off + N ≤ stage2LogExtent →
      readBytes (writeBytes (writeBytes s.mem C.stage.e (wordBytes 4 0)) (C.stage.e + 8)
        (wordBytes 8 pos)) (C.stage.z + off) N =
      readBytes s.mem (C.stage.z + off) N := by
    intro off N hoff
    have hoff' := hoff
    simp only [stage2LogExtent] at hoff'
    rw [walkReadBytes_log_of_eoff_write (m := writeBytes s.mem C.stage.e (wordBytes 4 0))
      (e := C.stage.e) (z := C.stage.z) (off := off) (j := pos) (N := N)
      (by
        rcases hez with h | h
        · left; simp only [stage2ErrorExtent]; exact h
        · right; simp only [stage2LogExtent]; exact h) hoff]
    exact herr4Log off N hoff
  -- the same read across the record's third store, which is outside the log
  have herr8Log : ∀ off N, off + N ≤ stage2LogExtent →
      readBytes (writeBytes (writeBytes (writeBytes s.mem C.stage.e (wordBytes 4 0))
        (C.stage.e + 8) (wordBytes 8 pos)) (C.stage.e + 16) (wordBytes 8 0))
        (C.stage.z + off) N =
      readBytes s.mem (C.stage.z + off) N := by
    intro off N hoff
    rw [walkReadBytes_writeBytes_outside (m := writeBytes (writeBytes s.mem C.stage.e
        (wordBytes 4 0)) (C.stage.e + 8) (wordBytes 8 pos))
      (start := C.stage.e + 16) (v := wordBytes 8 0) (addr := C.stage.z + off) (n := N) ?_]
    · exact herr8Log2 off N hoff
    · have hw : (wordBytes 8 0).length = 8 := by simp [wordBytes, natToBytes_length]
      rw [hw]
      rcases hez with h | h
      · right; omega
      · left
        have hoff' := hoff
        simp only [stage2LogExtent] at hoff'
        omega
  have herr8Ev2 : readBytes (writeBytes (writeBytes s.mem C.stage.e (wordBytes 4 0)) (C.stage.e + 8)
        (wordBytes 8 pos)) (G.ev + G.nev0)
        (C.events.map EventRecord.encodedBytes).flatten.length =
      readBytes s.mem (G.ev + G.nev0)
        (C.events.map EventRecord.encodedBytes).flatten.length := by
    rw [walkReadBytes_ev_of_eoff_write (m := writeBytes s.mem C.stage.e (wordBytes 4 0))
      (e := C.stage.e) (ev := G.ev) (evcap := G.evcap) (nev0 := G.nev0) (j := pos)
      (N := (C.events.map EventRecord.encodedBytes).flatten.length)
      (by
        rcases heev with h | h
        · left; simp only [stage2ErrorExtent]; exact h
        · right; exact h) hNev]
    refine walkReadBytes_writeBytes_outside (start := C.stage.e) (addr := G.ev + G.nev0)
      (n := (C.events.map EventRecord.encodedBytes).flatten.length) (v := wordBytes 4 0) ?_
    rw [wordBytes, natToBytes_length]
    rcases heev with h | h
    · right
      exact Nat.le_trans (Nat.add_le_add_left (by decide : 4 ≤ 24) C.stage.e)
        (Nat.le_trans h (Nat.le_add_right G.ev G.nev0))
    · left
      rw [Nat.add_assoc]
      exact Nat.le_trans (Nat.add_le_add_left hNev G.ev) h
  -- and across the record's third store
  have herr8Ev : readBytes (writeBytes (writeBytes (writeBytes s.mem C.stage.e (wordBytes 4 0))
        (C.stage.e + 8) (wordBytes 8 pos)) (C.stage.e + 16) (wordBytes 8 0))
        (G.ev + G.nev0)
        (C.events.map EventRecord.encodedBytes).flatten.length =
      readBytes s.mem (G.ev + G.nev0)
        (C.events.map EventRecord.encodedBytes).flatten.length := by
    rw [walkReadBytes_writeBytes_outside (m := writeBytes (writeBytes s.mem C.stage.e
        (wordBytes 4 0)) (C.stage.e + 8) (wordBytes 8 pos))
      (start := C.stage.e + 16) (v := wordBytes 8 0) (addr := G.ev + G.nev0)
      (n := (C.events.map EventRecord.encodedBytes).flatten.length) ?_]
    · exact herr8Ev2
    · have hw : (wordBytes 8 0).length = 8 := by simp [wordBytes, natToBytes_length]
      rw [hw]
      rcases heev with h | h
      · right; omega
      · left; omega
  refine ⟨s', ⟨hInv, hstep, ?_, le_of_eq rfl⟩⟩
  refine
    { pc_eq := rfl
      blockIndex := ?_
      k_le := hInv.k_le
      events_le := hInv.events_le
      evlen_eq := hInv.evlen_eq
      evBytes := ?_
      alen_le_sum := hInv.alen_le_sum
      alen_ge := hInv.alen_ge
      spans_order := hInv.spans_order
      spans_end := hInv.spans_end
      spans_inside := hInv.spans_inside
      pending_at := hInv.pending_at
      pending_cursor := hInv.pending_cursor
      pending_len := hInv.pending_len
      eoff_le := hInv.eoff_le
      inner_cap := hInv.inner_cap
      depth_cap := hInv.depth_cap
      depth_reg := ?_
      sp_le_wlen := hInv.sp_le_wlen
      wlen_cap := hInv.wlen_cap
      tyBytes := by
        dsimp only [s', s₁, stateAt]
        rw [hrefuse]
        unfold stage2ErrSetMsg stage2ErrSet
        have h1 : (wordBytes 4 0).length = 4 := by simp [wordBytes, natToBytes_length]
        have h2 : (wordBytes 8 pos).length = 8 := by simp [wordBytes, natToBytes_length]
        have hx : stage2ErrorExtent = 24 := rfl
        refine ((hInv.tyBytes.write_outside ?_).write_outside ?_).write_outside ?_
        · rcases (stack_e_sep hInv).1 with h | h
          · exact Or.inr (by omega)
          · exact Or.inl (by omega)
        · rcases (stack_e_sep hInv).1 with h | h
          · exact Or.inr (by omega)
          · exact Or.inl (by omega)
        · rcases (stack_e_sep hInv).1 with h | h
          · exact Or.inr (by omega)
          · exact Or.inl (by simp only [wordBytes, natToBytes_length]; omega)
      stBytes := by
        dsimp only [s', s₁, stateAt]
        rw [hrefuse]
        unfold stage2ErrSetMsg stage2ErrSet
        have h1 : (wordBytes 4 0).length = 4 := by simp [wordBytes, natToBytes_length]
        have h2 : (wordBytes 8 pos).length = 8 := by simp [wordBytes, natToBytes_length]
        have hx : stage2ErrorExtent = 24 := rfl
        refine ((hInv.stBytes.write_outside ?_).write_outside ?_).write_outside ?_
        · rcases (stack_e_sep hInv).2 with h | h
          · exact Or.inr (by omega)
          · exact Or.inl (by omega)
        · rcases (stack_e_sep hInv).2 with h | h
          · exact Or.inr (by omega)
          · exact Or.inl (by omega)
        · rcases (stack_e_sep hInv).2 with h | h
          · exact Or.inr (by omega)
          · exact Or.inl (by simp only [wordBytes, natToBytes_length]; omega)
      ptrs := ?_
      regs := ?_
      iter := ?_
      log_hash := ?_
      log_len := ?_
      log_cap := ?_
      log_alen := ?_
      log_acap := ?_
      owned := ?_
      frame := ?_
      blockLocal := by simp [WalkLocal] }
  · rw [show s'.env = s₁.env from rfl]
    rw [denoteCode_lookupName (stage2Calls stage2SubCalls) walkIfThen425.instrs
      "%k.0.i249" (by refine fun i hi => ?_; simp only [walkIfThen425, List.mem_cons,
        List.not_mem_nil, or_false] at hi; rcases hi with rfl | rfl <;> decide) s s₁ hden]
    exact hInv.blockIndex
  · show readBytes r.mem (G.ev + G.nev0)
      (C.events.map EventRecord.encodedBytes).flatten.length =
      some (C.events.map EventRecord.encodedBytes).flatten
    rw [hrefuse, stage2ErrSetMsg, stage2ErrSet]
    rw [herr8Ev]
    exact hInv.evBytes
  · rw [show s'.env = s₁.env from rfl]
    rw [denoteCode_lookupName (stage2Calls stage2SubCalls) walkIfThen425.instrs
      "%sp.i.0248" (by refine fun i hi => ?_; simp only [walkIfThen425, List.mem_cons,
        List.not_mem_nil, or_false] at hi; rcases hi with rfl | rfl <;> decide) s s₁ hden]
    exact hInv.depth_reg
  · rw [show s'.env = s₁.env from rfl]
    exact WalkPtrs.of_run hInv.ptrs (by unfold walkCarried; decide) hden
  · rw [show s'.env = s₁.env from rfl]
    exact WalkRegs.of_run hInv.regs (by unfold walkCarried; decide) hden
  · rw [show s'.env = s₁.env from rfl]
    exact WalkIter.of_run hInv.iter (by unfold walkCarried; decide) hden
  · show readBytes r.mem (C.stage.z + 32) 4 = some (natToBytes 0 4)
    rw [hrefuse, stage2ErrSetMsg, stage2ErrSet]
    rw [herr8Log 32 4 (by decide)]
    exact hInv.log_hash
  · show readBytes r.mem (C.stage.z + 8) 8 = some (wordBytes 8 C.evlen)
    rw [hrefuse, stage2ErrSetMsg, stage2ErrSet]
    rw [herr8Log 8 8 (by decide)]
    exact hInv.log_len
  · show readBytes r.mem (C.stage.z + 16) 8 = some (wordBytes 8 G.evcap)
    rw [hrefuse, stage2ErrSetMsg, stage2ErrSet]
    rw [herr8Log 16 8 (by decide)]
    exact hInv.log_cap
  · obtain ⟨a, h0, ha, hr⟩ := hInv.log_alen
    refine ⟨a, h0, ha, ?_⟩
    show readBytes r.mem (C.stage.z + 48) 8 = some (wordBytes 8 a)
    rw [hrefuse, stage2ErrSetMsg, stage2ErrSet]
    rw [herr8Log 48 8 (by decide)]
    exact hr
  · show readBytes r.mem (C.stage.z + 56) 8 = some (wordBytes 8 G.dstcap)
    rw [hrefuse, stage2ErrSetMsg, stage2ErrSet]
    rw [herr8Log 56 8 (by decide)]
    exact hInv.log_acap
  · show ∀ q ∈ walkStaged G C, HasBytes r.mem q.1 q.2
    rw [hrefuse]
    unfold stage2ErrSetMsg stage2ErrSet
    exact walkStaged_write rfl (walkStaged_write rfl (walkStaged_write rfl hInv.owned))
  · show UnchangedOutside m0 r.mem (walkWide G C)
    rw [hrefuse]
    unfold stage2ErrSetMsg stage2ErrSet
    have hregion : (C.stage.e, stage2ErrorExtent) ∈ walkWide G C := by
      simp [walkWide, walkPresent, stage2ReportScratch, stage2StagedWrites]
    refine UnchangedOutside.write_le (a := C.stage.e + 16) (w := 8)
      (UnchangedOutside.write_le (a := C.stage.e + 8) (w := 8)
        (UnchangedOutside.write_le (a := C.stage.e) (w := 4) hInv.frame
          ⟨(C.stage.e, stage2ErrorExtent), hregion, by omega,
            by simp only [stage2ErrorExtent]; omega⟩
          (bs := wordBytes 4 0) (by simp [wordBytes, natToBytes_length]))
        ⟨(C.stage.e, stage2ErrorExtent), hregion, by simp only [stage2ErrorExtent]; omega,
          by simp only [stage2ErrorExtent]; omega⟩
        (bs := wordBytes 8 pos) (by simp [wordBytes, natToBytes_length]))
      ⟨(C.stage.e, stage2ErrorExtent), hregion, by simp only [stage2ErrorExtent]; omega,
        by simp only [stage2ErrorExtent]; omega⟩
      (bs := wordBytes 8 0) (by simp [wordBytes, natToBytes_length])


/-- A byte at an inside index of the state stack is separated from the log. -/
theorem walkCstByte_log_sep {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {s : State}
    (hInv : WalkInv G C s) {q : Nat} (hq : q + 1 ≤ stage2StackExtent) :
    C.stage.cst + q + 1 ≤ C.stage.z ∨
      C.stage.z + stage2LogExtent ≤ C.stage.cst + q := by
  have hsep := cst_log_sep hInv
  have h520 : stage2StackExtent = 520 := rfl
  rw [h520] at hq
  simp only [stage2LogExtent] at hsep ⊢
  rcases hsep with hsep | hsep
  · left; omega
  · right; omega

/-- A byte at an inside index of the state stack is separated from the event
stream. -/
theorem walkCstByte_ev_sep {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {s : State}
    (hInv : WalkInv G C s) {q : Nat} (hq : q + 1 ≤ stage2StackExtent) :
    C.stage.cst + q + 1 ≤ G.ev ∨ G.ev + G.evcap ≤ C.stage.cst + q := by
  have hsep := cst_ev_sep hInv
  have h520 : stage2StackExtent = 520 := rfl
  rw [h520] at hq
  rcases hsep with hsep | hsep
  · left; omega
  · right; omega

/-- **`s2_after_value`'s four memory facts at an arbitrary depth binding.**  The
callee's model writes one of two places — the root slot at depth zero and the top
container's state byte above it — and both are inside the walk's frame: the root
slot is the first allocated slot and the byte is inside `%cst.i`'s staged extent.
The depth is the register the call passes (`%sub.i`, which the dispatch binds as
`%sp.i.0248 - 1`), so the lemma takes its value and its bound rather than reading
the carry: the instance at `BitVec.ofNat 32 C.sp` is `walkAfterValue_facts`. -/
theorem walkAfterValue_facts_at {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {s : State}
    (hInv : WalkInv G C s) {spz : BitVec 32} (hspz : spz.toNat ≤ stage2StackExtent)
    {m : Mem}
    (hm : stage2AfterValue s.mem spz.toNat (G.next0 + 8)
      C.stage.ctype C.stage.cst = some m)
    (hfr : UnchangedOutside s.mem m
      (s2AfterValueFoot [.int 32 spz, .ptr (G.next0 + 8),
        .ptr C.stage.ctype, .ptr C.stage.cst] s.mem s.next)) :
    UnchangedOutside m0 m (walkWide G C) ∧
      (∀ q ∈ walkStaged G C, HasBytes m q.1 q.2) ∧
      (∀ off w, off + w ≤ stage2LogExtent →
        readBytes m (C.stage.z + off) w = readBytes s.mem (C.stage.z + off) w) ∧
      readBytes m (G.ev + G.nev0)
          (C.events.map EventRecord.encodedBytes).flatten.length =
        readBytes s.mem (G.ev + G.nev0)
          (C.events.map EventRecord.encodedBytes).flatten.length := by
  have hroot : G.next0 + 8 + 4 ≤ C.stage.z ∨ C.stage.z + stage2LogExtent ≤ G.next0 + 8 :=
    C.stage.rootSlot_log
  have hrootev : G.next0 + 8 + 4 ≤ G.ev + G.nev0 ∨ G.ev + G.evcap ≤ G.next0 + 8 :=
    C.stage.rootSlot_ev
  have hbyte : spz.toNat - 1 + 1 ≤ stage2StackExtent := by
    have h520 : stage2StackExtent = 520 := rfl
    rw [h520] at hspz ⊢
    omega
  have hfoot : s2AfterValueFoot [.int 32 spz, .ptr (G.next0 + 8),
      .ptr C.stage.ctype, .ptr C.stage.cst] s.mem s.next =
      (if spz.toNat = 0 then [(G.next0 + 8, 4)]
       else [(C.stage.cst + (spz.toNat - 1), 1)]) := by
    simp [s2AfterValueFoot]
  have hsub : ∀ q ∈ s2AfterValueFoot [.int 32 spz, .ptr (G.next0 + 8),
      .ptr C.stage.ctype, .ptr C.stage.cst] s.mem s.next,
      ∃ w ∈ walkWide G C, w.1 ≤ q.1 ∧ q.1 + q.2 ≤ w.1 + w.2 := by
    intro q hq
    rw [hfoot] at hq
    by_cases h0 : spz.toNat = 0
    · rw [ite_eq_left h0] at hq
      simp only [List.mem_singleton] at hq
      subst hq
      exact walkWide_rootSlot
    · rw [ite_eq_right h0] at hq
      simp only [List.mem_singleton] at hq
      subst hq
      exact walkWide_cst_byte (q := spz.toNat - 1) hbyte
  have hevcap : G.nev0 + (C.events.map EventRecord.encodedBytes).flatten.length ≤ G.evcap := by
    have hsum := EventRecord.sum_encodedSize_le C.events
    simp only [stage2RecordBytes] at hsum
    have h4' := G.evRoom
    simp only [stage2RecordBytes] at h4'
    have hlen : (C.events.map EventRecord.encodedBytes).flatten.length =
        (C.events.map EventRecord.encodedSize).sum := by
      simp only [List.length_flatten, List.map_map]
      rfl
    have h1 := hInv.events_le
    have h2 := hInv.k_le
    have h3 := G.nep_le
    omega
  have hframe : UnchangedOutside m0 m (walkWide G C) :=
    hInv.frame.trans' (UnchangedOutside.of_subset hfr hsub)
  have howned : ∀ q ∈ walkStaged G C, HasBytes m q.1 q.2 := by
    obtain h1 | ⟨b, h1⟩ := stage2AfterValue_form hm
    · rw [h1]; exact walkStaged_write rfl hInv.owned
    · rw [h1]; exact walkStaged_write rfl hInv.owned
  have hlog : ∀ off w, off + w ≤ stage2LogExtent →
      readBytes m (C.stage.z + off) w = readBytes s.mem (C.stage.z + off) w := by
    intro off w hsubw
    obtain h1 | ⟨b, h1⟩ := stage2AfterValue_form hm
    · rw [h1]
      refine walkReadBytes_log_of_write (w := 4) (by simp [wordBytes, natToBytes_length])
        ?_ hsubw
      simpa [wordBytes, natToBytes_length] using hroot
    · rw [h1]
      exact walkReadBytes_log_of_write (w := 1) (by simp) (walkCstByte_log_sep hInv hbyte) hsubw
  have hev : readBytes m (G.ev + G.nev0)
        (C.events.map EventRecord.encodedBytes).flatten.length =
      readBytes s.mem (G.ev + G.nev0)
        (C.events.map EventRecord.encodedBytes).flatten.length := by
    obtain h1 | ⟨b, h1⟩ := stage2AfterValue_form hm
    · rw [h1]
      refine walkReadBytes_ev_of_write (w := 4) (by simp [wordBytes, natToBytes_length]) ?_
      rcases hrootev with h | h
      · exact Or.inl h
      · exact Or.inr (by omega)
    · rw [h1]
      refine walkReadBytes_ev_of_write (w := 1) (by simp) ?_
      rcases walkCstByte_ev_sep hInv hbyte with h | h
      · exact Or.inl (by omega)
      · exact Or.inr (by omega)
  exact ⟨hframe, howned, hlog, hev⟩

/-- The `%conv115.i` `phi`: the kind byte the token's arm selected. -/
def walkIfThen109Incoming : List (String × Operand) :=
  [("LeafBlock23", .imm (.int 8 (BitVec.ofNat 8 2))),
   ("LeafBlock25", .imm (.int 8 (BitVec.ofNat 8 2))),
   ("cond.end.i", .imm (.int 8 (BitVec.ofNat 8 4)))]

/-- `if.then109.i`: the value's flag, the hash word's load and its test. -/
def walkIfThen109 : Block :=
  { name := "if.then109.i",
    instrs := [
      Instr.phi "%conv115.i" (Ty.int 8) walkIfThen109Incoming,
      Instr.callVoid "s2_after_value"
        [(Ty.int 32, Operand.reg "%sub.i"), (Ty.ptr, Operand.reg "%root_done.i"),
         (Ty.ptr, Operand.reg "%ctype.i"), (Ty.ptr, Operand.reg "%cst.i")],
      Instr.load "%17" (Ty.int 32) (Operand.reg "%hash1.i.i"),
      Instr.icmp "%tobool.not.i.i49" IPred.eq 32 (Operand.reg "%17")
        (Operand.imm (.int 32 (BitVec.ofNat 32 0)))],
    term := Term.condbr (Operand.reg "%tobool.not.i.i49") "if.end.i.i55" "if.then.i.i50" }

theorem walkIfThen109_find : stage2Body.findBlock "if.then109.i" = some walkIfThen109 := by
  simp [stage2Body, Function.findBlock, findBlockList, walkIfThen109,
    walkIfThen109Incoming]

theorem walkIfThen109_denote {sub : Calls} (env : Env) (s : State)
    {p : String} {op : Operand} {c8 : BitVec 8} {spz : BitVec 32}
    {rd ct cs : Nat} {r : CallOutcome} {hzA : Nat}
    (hpre : s.pre = some p)
    (hinc : phiIncoming p walkIfThen109Incoming = some op)
    (hop : evalOperand (stateAt env s) op = some (.int 8 c8))
    (hsub : lookupName env "%sub.i" = some (.int 32 spz))
    (hrd : lookupName env "%root_done.i" = some (.ptr rd))
    (hct : lookupName env "%ctype.i" = some (.ptr ct))
    (hcs : lookupName env "%cst.i" = some (.ptr cs))
    (hcall : stage2Calls sub "s2_after_value"
      [.int 32 spz, .ptr rd, .ptr ct, .ptr cs] s.mem s.next = some r)
    (hz : lookupName env "%hash1.i.i" = some (.ptr hzA))
    (hread : readBytes r.mem hzA 4 = some (natToBytes 0 4)) :
    denoteCode (stage2Calls sub) walkIfThen109.instrs (stateAt env s) =
      some (stateAt (cells [
        ("%tobool.not.i.i49", .int 1 (evalICmp .eq
          (BitVec.ofNat 32 (bytesToNat (natToBytes 0 4))) (BitVec.ofNat 32 0))),
        ("%17", .int 32 (BitVec.ofNat 32 (bytesToNat (natToBytes 0 4)))),
        ("%conv115.i", .int 8 c8)] env) { s with mem := r.mem, next := r.next }) := by
  simp only [walkIfThen109]
  rw [denoteCode_phi (calls := stage2Calls sub) (env := env) (s := s)
    (d := "%conv115.i") (ty := .int 8) (inc := walkIfThen109Incoming)
    (p := p) (op := op) (v := .int 8 c8) hpre hinc hop _ (by decide)]
  rw [walkDenoteCode_callVoid (calls := stage2Calls sub)
    (env := ("%conv115.i", .int 8 c8) :: env) (s := s)
    (callee := "s2_after_value")
    (args := [(Ty.int 32, Operand.reg "%sub.i"),
      (Ty.ptr, Operand.reg "%root_done.i"), (Ty.ptr, Operand.reg "%ctype.i"),
      (Ty.ptr, Operand.reg "%cst.i")])
    (vs := [.int 32 spz, .ptr rd, .ptr ct, .ptr cs]) (r := r)
    (by
      simp only [evalOperands, evalOperand, stateAt]
      rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
        lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide)]
      simp [hsub, hrd, hct, hcs])
    hcall [Instr.load "%17" (Ty.int 32) (Operand.reg "%hash1.i.i"),
      Instr.icmp "%tobool.not.i.i49" IPred.eq 32 (Operand.reg "%17")
        (Operand.imm (.int 32 (BitVec.ofNat 32 0)))]]
  rw [denoteCode_load32 (calls := stage2Calls sub)
    (env := ("%conv115.i", .int 8 c8) :: env)
    (s := { s with mem := r.mem, next := r.next })
    (d := "%17") (p := "%hash1.i.i") (a := hzA)
    (q := bytesToNat (natToBytes 0 4))
    (by rw [lookupName_cons_ne _ _ (by decide)]; exact hz)
    hread rfl [Instr.icmp "%tobool.not.i.i49" IPred.eq 32 (Operand.reg "%17")
        (Operand.imm (.int 32 (BitVec.ofNat 32 0)))]]
  rw [denoteCode_icmp_eq_imm_w (calls := stage2Calls sub)
    (env := ("%17", .int 32 (BitVec.ofNat 32 (bytesToNat (natToBytes 0 4)))) ::
      ("%conv115.i", .int 8 c8) :: env)
    (s := { s with mem := r.mem, next := r.next })
    (d := "%tobool.not.i.i49") (a := "%17") (w := 32)
    (x := BitVec.ofNat 32 (bytesToNat (natToBytes 0 4)))
    (c := BitVec.ofNat 32 0)
    (by simp [stateAt, evalOperand, lookupName]) []]
  simp only [denoteCode_nil]
  rfl

/-- **The hash word's value is zero**: the initialisation's `memset` over the
sixteen bytes at `%z + 24` is the invariant's `log_hash`, so the word four bytes
later is the word the load binds. -/
theorem walkBytesToNat_zero4 : bytesToNat (natToBytes 0 4) = 0 := by decide

/-- **`if.then109.i` is a link**: the value's flag is set, the hash word is zero,
and the block takes the log-word comparison's edge with the carry unmoved. -/
theorem WalkLink.if_then109_i {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State)
    (hInv : WalkInv G C s) (hblock : C.block = "if.then109.i")
    {p : String} {op : Operand} {c8 : BitVec 8} {spz : BitVec 32}
    (hpre : s.pre = some p)
    (hinc : phiIncoming p walkIfThen109Incoming = some op)
    (hop : evalOperand (stateAt s.env s) op = some (.int 8 c8))
    (hsub : lookupName s.env "%sub.i" = some (.int 32 spz))
    (hspz : spz.toNat ≤ stage2StackExtent)
    (hrd : lookupName s.env "%root_done.i" = some (.ptr (G.next0 + 8)))
    (hpreA : s2AfterValuePre [.int 32 spz, .ptr (G.next0 + 8),
      .ptr C.stage.ctype, .ptr C.stage.cst] s.mem s.next)
    (hspw : spz.toNat = 0 ∨ spz.toNat - 1 < C.wlen) :
    ∃ s', WalkLink (stage2Calls stage2SubCalls) G C s { C with
      block := "if.end.i.i55", stMap := walkAfterValueMapAt C spz.toNat } s' := by
  obtain ⟨r, hcall, hpost, hfr⟩ := s2AfterValueContract.resolves (next := s.next) hpreA
  obtain ⟨m, hm, -, hmem, -⟩ := hpost
  have hfr' : UnchangedOutside s.mem m
      (s2AfterValueFoot [.int 32 spz, .ptr (G.next0 + 8),
        .ptr C.stage.ctype, .ptr C.stage.cst] s.mem s.next) := by
    rw [hmem] at hfr; exact hfr
  obtain ⟨hframe, howned, hlog, hev⟩ :=
    walkAfterValue_facts_at (G := G) (C := C) (s := s) hInv hspz hm hfr'
  have hread : readBytes r.mem (C.stage.z + 32) 4 = some (natToBytes 0 4) := by
    rw [hmem, hlog 32 4 (by decide)]
    exact hInv.log_hash
  have hevm : readBytes m (G.ev + G.nev0)
      (C.events.map EventRecord.encodedBytes).flatten.length =
      readBytes s.mem (G.ev + G.nev0)
        (C.events.map EventRecord.encodedBytes).flatten.length := hev
  let s₁ : State := stateAt (cells [
    ("%tobool.not.i.i49", .int 1 (evalICmp .eq
      (BitVec.ofNat 32 (bytesToNat (natToBytes 0 4))) (BitVec.ofNat 32 0))),
    ("%17", .int 32 (BitVec.ofNat 32 (bytesToNat (natToBytes 0 4)))),
    ("%conv115.i", .int 8 c8)] s.env) { s with mem := r.mem, next := r.next }
  have hden : denoteCode (stage2Calls stage2SubCalls) walkIfThen109.instrs s =
      some s₁ := by
    dsimp only [s₁]
    exact walkIfThen109_denote (sub := stage2SubCalls) (env := s.env) (s := s)
      (p := p) (op := op) (c8 := c8) (spz := spz) (rd := G.next0 + 8)
      (ct := C.stage.ctype) (cs := C.stage.cst) (r := r) (hzA := C.stage.z + 32)
      hpre hinc hop hsub hrd (hInv.ptrs.2.2.2.1)
      (hInv.ptrs.2.2.2.2.1) hcall (hInv.ptrs.2.2.2.2.2) hread
  have hpc : s.pc = C.block := hInv.pc_eq
  have hbit : evalICmp .eq (BitVec.ofNat 32 (bytesToNat (natToBytes 0 4)))
      (BitVec.ofNat 32 0) = (1 : BitVec 1) := by
    rw [walkBytesToNat_zero4]
    decide
  let s' : State := { s₁ with pc := "if.end.i.i55", pre := some s.pc }
  have hstep : LeanLLVM.step (stage2Calls stage2SubCalls) stage2Body s = Ctrl.jump s' := by
    have hfind : stage2Body.findBlock s.pc = some walkIfThen109 := by
      rw [hpc, hblock]; exact walkIfThen109_find
    have hterm : walkIfThen109.term =
        Term.condbr (Operand.reg "%tobool.not.i.i49") "if.end.i.i55" "if.then.i.i50" := rfl
    simp only [LeanLLVM.step, hfind, hden, hterm]
    rw [walkExecTerm_condbr (d := "%tobool.not.i.i49") (tl := "if.end.i.i55")
      (fl := "if.then.i.i50") (bit := (1 : BitVec 1))
      (by dsimp only [s₁]; simp [stateAt, cells, lookupName, hbit])]
    dsimp only [s', s₁, cells, stateAt]
    simp only [hbit]
    rfl
  refine ⟨s', ⟨hInv, hstep, ?_, le_of_eq rfl⟩⟩
  refine
    { pc_eq := rfl
      blockIndex := ?_
      k_le := hInv.k_le
      events_le := hInv.events_le
      evlen_eq := hInv.evlen_eq
      evBytes := ?_
      alen_le_sum := hInv.alen_le_sum
      alen_ge := hInv.alen_ge
      spans_order := hInv.spans_order
      spans_end := hInv.spans_end
      spans_inside := hInv.spans_inside
      pending_at := hInv.pending_at
      pending_cursor := hInv.pending_cursor
      pending_len := hInv.pending_len
      eoff_le := hInv.eoff_le
      inner_cap := hInv.inner_cap
      depth_cap := hInv.depth_cap
      depth_reg := ?_
      sp_le_wlen := hInv.sp_le_wlen
      wlen_cap := hInv.wlen_cap
      tyBytes := by
        dsimp only [s', s₁, stateAt]
        rw [hmem]
        exact walkAfterValue_tyBytesAt (G := G) (C := C) (s := s) hInv
          (sp := spz.toNat) hspz hm
      stBytes := by
        dsimp only [s', s₁, stateAt]
        rw [hmem]
        exact walkAfterValue_stBytesAt (G := G) (C := C) (s := s) hInv
          (sp := spz.toNat) hspz hspw hm
      ptrs := ?_
      regs := ?_
      iter := ?_
      log_hash := ?_
      log_len := ?_
      log_cap := ?_
      log_alen := ?_
      log_acap := ?_
      owned := ?_
      frame := ?_
      blockLocal := by simp [WalkLocal] }
  · rw [show s'.env = s₁.env from rfl]
    rw [denoteCode_lookupName (stage2Calls stage2SubCalls) walkIfThen109.instrs
      "%k.0.i249" (by refine fun i hi => ?_; simp only [walkIfThen109, walkIfThen109Incoming,
      List.mem_cons, List.not_mem_nil, or_false] at hi; rcases hi with rfl | rfl | rfl | rfl <;> decide) s s₁ hden]
    exact hInv.blockIndex
  · rw [show s'.mem = m from hmem]
    rw [hevm]
    exact hInv.evBytes
  · rw [show s'.env = s₁.env from rfl]
    rw [denoteCode_lookupName (stage2Calls stage2SubCalls) walkIfThen109.instrs
      "%sp.i.0248" (by refine fun i hi => ?_; simp only [walkIfThen109, walkIfThen109Incoming,
      List.mem_cons, List.not_mem_nil, or_false] at hi; rcases hi with rfl | rfl | rfl | rfl <;> decide) s s₁ hden]
    exact hInv.depth_reg
  · rw [show s'.env = s₁.env from rfl]
    exact WalkPtrs.of_run hInv.ptrs (by unfold walkCarried; decide) hden
  · rw [show s'.env = s₁.env from rfl]
    exact WalkRegs.of_run hInv.regs (by unfold walkCarried; decide) hden
  · rw [show s'.env = s₁.env from rfl]
    exact WalkIter.of_run hInv.iter (by unfold walkCarried; decide) hden
  · rw [show s'.mem = m from hmem]
    rw [hlog 32 4 (by decide)]
    exact hInv.log_hash
  · rw [show s'.mem = m from hmem]
    rw [hlog 8 8 (by decide)]
    exact hInv.log_len
  · rw [show s'.mem = m from hmem]
    rw [hlog 16 8 (by decide)]
    exact hInv.log_cap
  · rw [show s'.mem = m from hmem]
    rw [hlog 48 8 (by decide)]
    exact hInv.log_alen
  · rw [show s'.mem = m from hmem]
    rw [hlog 56 8 (by decide)]
    exact hInv.log_acap
  · rw [show s'.mem = m from hmem]
    simpa [walkStaged] using howned
  · rw [show s'.mem = m from hmem]
    simpa [walkWide, walkPresent] using hframe


/-- **`num_fast_el1`'s four memory facts**: the callee writes one of its two
caller's slots — the value's at `%d.i` and the offset's at `%ei.i` — both inside
the walk's frame, and neither is in the log or the event stream.  The two slots'
separation from those regions is the caller's: `%d.i` is staged beside the
seventeen (the adapter's pre), and `%ei.i` is the first of the four stack
allocations, below every staged object by the watermark. -/
theorem walkNumFast_facts {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {s : State}
    (hInv : WalkInv G C s) {m : Mem} {w w' : Nat}
    (hm : m = writeBytes s.mem C.stage.d (wordBytes 8 w) ∨
          m = writeBytes s.mem G.next0 (wordBytes 8 w'))
    (hdlog : C.stage.d + 8 ≤ C.stage.z ∨ C.stage.z + stage2LogExtent ≤ C.stage.d)
    (hdev : C.stage.d + 8 ≤ G.ev ∨ G.ev + G.evcap ≤ C.stage.d) :
    UnchangedOutside m0 m (walkWide G C) ∧
      (∀ q ∈ walkStaged G C, HasBytes m q.1 q.2) ∧
      (∀ off w'', off + w'' ≤ stage2LogExtent →
        readBytes m (C.stage.z + off) w'' = readBytes s.mem (C.stage.z + off) w'') ∧
      readBytes m (G.ev + G.nev0)
          (C.events.map EventRecord.encodedBytes).flatten.length =
        readBytes s.mem (G.ev + G.nev0)
          (C.events.map EventRecord.encodedBytes).flatten.length := by
  have hz0 : C.stage.z + stage2LogExtent ≤ G.next0 :=
    C.stage.sevenEnd (C.stage.z, stage2LogExtent) (by simp [stage2StagedWrites])
  have hev0 : G.ev + G.evcap ≤ G.next0 :=
    G.watermark (G.ev, G.evcap) (by simp [stage2Regions])
  have hdmem : (C.stage.d, 8) ∈ walkWide G C := by
    simp [walkWide, walkPresent, stage2ReportScratch]
  have hnext : (G.next0, 8) ∈ walkWide G C := by
    simp [walkWide, walkPresent, stage2AllocaWrites]
  have hlen : (wordBytes 8 w).length = 8 := by simp [wordBytes, natToBytes_length]
  have hlen' : (wordBytes 8 w').length = 8 := by simp [wordBytes, natToBytes_length]
  have hframe : UnchangedOutside m0 m (walkWide G C) := by
    rcases hm with hm | hm
    · rw [hm]
      exact (hInv.frame).write_le (w := 8) ⟨(C.stage.d, 8), hdmem, Nat.le_refl _, by omega⟩
        (Nat.le_of_eq hlen)
    · rw [hm]
      exact (hInv.frame).write_le (w := 8) ⟨(G.next0, 8), hnext, Nat.le_refl _, by omega⟩
        (Nat.le_of_eq hlen')
  have howned : ∀ q ∈ walkStaged G C, HasBytes m q.1 q.2 := by
    rcases hm with hm | hm
    · rw [hm]; exact walkStaged_write rfl hInv.owned
    · rw [hm]; exact walkStaged_write rfl hInv.owned
  have hlog : ∀ off w'', off + w'' ≤ stage2LogExtent →
      readBytes m (C.stage.z + off) w'' = readBytes s.mem (C.stage.z + off) w'' := by
    intro off w'' hsubw
    rcases hm with hm | hm
    · rw [hm]
      exact walkReadBytes_log_of_write (w := 8) (Nat.le_of_eq hlen) hdlog hsubw
    · rw [hm]
      refine walkReadBytes_log_of_write (w := 8) (Nat.le_of_eq hlen') ?_ hsubw
      right; exact hz0
  have hevcap : G.nev0 + (C.events.map EventRecord.encodedBytes).flatten.length ≤ G.evcap := by
    have hsum := EventRecord.sum_encodedSize_le C.events
    simp only [stage2RecordBytes] at hsum
    have hroom := G.evRoom
    simp only [stage2RecordBytes] at hroom
    have hlen2 : (C.events.map EventRecord.encodedBytes).flatten.length =
        (C.events.map EventRecord.encodedSize).sum := by
      simp only [List.length_flatten, List.map_map]; rfl
    have h1 := hInv.events_le; have h2 := hInv.k_le; have h3 := G.nep_le
    rw [hlen2]; omega
  have hev : readBytes m (G.ev + G.nev0)
        (C.events.map EventRecord.encodedBytes).flatten.length =
      readBytes s.mem (G.ev + G.nev0)
        (C.events.map EventRecord.encodedBytes).flatten.length := by
    rcases hm with hm | hm
    · rw [hm]
      refine walkReadBytes_ev_of_write (w := 8) (Nat.le_of_eq hlen) ?_
      rcases hdev with h | h
      · exact Or.inl (by omega)
      · exact Or.inr (by omega)
    · rw [hm]
      refine walkReadBytes_ev_of_write (w := 8) (Nat.le_of_eq hlen') ?_
      exact Or.inr (by omega)
  exact ⟨hframe, howned, hlog, hev⟩

/-- `if.then19.i`: the number path's two markers, the lexeme's extent and the
call. -/
def walkIfThen19 : Block :=
  { name := "if.then19.i",
    instrs := [
      Instr.callVoid "llvm.lifetime.start.p0"
        [((Ty.int 64), (Operand.imm (.int 64 (BitVec.ofNat 64 8)))),
         (Ty.ptr, (Operand.reg "%d.i"))],
      Instr.callVoid "llvm.lifetime.start.p0"
        [((Ty.int 64), (Operand.imm (.int 64 (BitVec.ofNat 64 8)))),
         (Ty.ptr, (Operand.reg "%ei.i"))],
      Instr.binop "%sub.i99" BinOp.sub 64 (Operand.reg "%ee.0.lcssa.i")
        (Operand.reg "%idxprom.i"),
      Instr.call "%call23.i" (Ty.int 32) "num_fast_el1"
        [(Ty.ptr, (Operand.reg "%arrayidx10.i")),
         ((Ty.int 64), (Operand.reg "%sub.i99")),
         (Ty.ptr, (Operand.reg "%d.i")), (Ty.ptr, (Operand.reg "%ei.i"))],
      Instr.icmp "%tobool24.not.not.i" IPred.eq 32 (Operand.reg "%call23.i")
        (Operand.imm (.int 32 (BitVec.ofNat 32 0)))],
    term := Term.condbr (Operand.reg "%tobool24.not.not.i") "if.then25.i"
      "if.end67.critedge.i" }

theorem walkIfThen19_find : stage2Body.findBlock "if.then19.i" = some walkIfThen19 := by
  simp [stage2Body, Function.findBlock, findBlockList, walkIfThen19]

theorem walkIfThen19_denote {sub : Calls} (env : Env) (s : State)
    {x y : BitVec 64} {p dof eof : Nat} {xout : BitVec 32} {r : CallOutcome}
    (hd : lookupName env "%d.i" = some (.ptr dof))
    (he : lookupName env "%ei.i" = some (.ptr eof))
    (hee : lookupName env "%ee.0.lcssa.i" = some (.int 64 x))
    (hix : lookupName env "%idxprom.i" = some (.int 64 y))
    (harr : lookupName env "%arrayidx10.i" = some (.ptr p))
    (hcall : stage2Calls sub "num_fast_el1"
      [.ptr p, .int 64 (x - y), .ptr dof, .ptr eof] s.mem s.next = some r)
    (hretv : r.ret = .int 32 xout) :
    denoteCode (stage2Calls sub) walkIfThen19.instrs (stateAt env s) =
      some (stateAt (cells [
        ("%tobool24.not.not.i", .int 1 (evalICmp .eq xout (BitVec.ofNat 32 0))),
        ("%call23.i", r.ret),
        ("%sub.i99", .int 64 (x - y))] env) { s with mem := r.mem, next := r.next }) := by
  simp only [walkIfThen19]
  rw [walkDenoteCode_lifetimeStart (sub := sub) (env := env) (s := s) (size := 8)
    (obj := "%d.i") (p := dof) hd]
  rw [walkDenoteCode_lifetimeStart (sub := sub) (env := env) (s := s) (size := 8)
    (obj := "%ei.i") (p := eof) he]
  rw [denoteCode_sub_reg (calls := stage2Calls sub) (env := env) (s := s)
    (d := "%sub.i99") (a := "%ee.0.lcssa.i") (b := "%idxprom.i") hee hix
    [Instr.call "%call23.i" (Ty.int 32) "num_fast_el1"
        [(Ty.ptr, (Operand.reg "%arrayidx10.i")),
         ((Ty.int 64), (Operand.reg "%sub.i99")),
         (Ty.ptr, (Operand.reg "%d.i")), (Ty.ptr, (Operand.reg "%ei.i"))],
      Instr.icmp "%tobool24.not.not.i" IPred.eq 32 (Operand.reg "%call23.i")
        (Operand.imm (.int 32 (BitVec.ofNat 32 0)))]]
  rw [walkDenoteCode_call (calls := stage2Calls sub)
    (env := ("%sub.i99", .int 64 (x - y)) :: env) (s := s)
    (d := "%call23.i") (callee := "num_fast_el1") (ty := .int 32)
    (args := [(Ty.ptr, Operand.reg "%arrayidx10.i"),
      (Ty.int 64, Operand.reg "%sub.i99"), (Ty.ptr, Operand.reg "%d.i"),
      (Ty.ptr, Operand.reg "%ei.i")])
    (vs := [.ptr p, .int 64 (x - y), .ptr dof, .ptr eof]) (r := r)
    (walkArgs_numFast (("%sub.i99", .int 64 (x - y)) :: env) s
      (by rw [lookupName_cons_ne _ _ (by decide)]; exact harr)
      (by rw [lookupName_cons_self])
      (by rw [lookupName_cons_ne _ _ (by decide)]; exact hd)
      (by rw [lookupName_cons_ne _ _ (by decide)]; exact he)) hcall
    [Instr.icmp "%tobool24.not.not.i" IPred.eq 32 (Operand.reg "%call23.i")
        (Operand.imm (.int 32 (BitVec.ofNat 32 0)))]]
  rw [denoteCode_icmp_eq_imm_w (calls := stage2Calls sub)
    (env := ("%call23.i", r.ret) :: ("%sub.i99", .int 64 (x - y)) :: env)
    (s := { s with mem := r.mem, next := r.next })
    (d := "%tobool24.not.not.i") (a := "%call23.i") (w := 32)
    (x := xout) (c := BitVec.ofNat 32 0)
    (by rw [lookupName_cons_self]; exact congrArg some hretv) []]
  simp only [denoteCode_nil]
  rfl


/-- **`if.then19.i` is a link**: the number path's two markers, its lexeme's
extent and `num_fast_el1`.  The callee writes one of its two slots, both inside the
frame, so the carry is the source's and the branch is the answer's own bit. -/
theorem WalkLink.if_then19_i {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State)
    (hInv : WalkInv G C s) (hblock : C.block = "if.then19.i")
    {x y : BitVec 64} {p w w' : Nat} {r : CallOutcome} {xout : BitVec 32}
    (hd : lookupName s.env "%d.i" = some (.ptr C.stage.d))
    (he : lookupName s.env "%ei.i" = some (.ptr G.next0))
    (hee : lookupName s.env "%ee.0.lcssa.i" = some (.int 64 x))
    (hix : lookupName s.env "%idxprom.i" = some (.int 64 y))
    (harr : lookupName s.env "%arrayidx10.i" = some (.ptr p))
    (hcall : stage2Calls stage2SubCalls "num_fast_el1"
      [.ptr p, .int 64 (x - y), .ptr C.stage.d, .ptr G.next0] s.mem s.next = some r)
    (hretv : r.ret = .int 32 xout)
    (hm : r.mem = writeBytes s.mem C.stage.d (wordBytes 8 w) ∨
          r.mem = writeBytes s.mem G.next0 (wordBytes 8 w'))
    (hdlog : C.stage.d + 8 ≤ C.stage.z ∨ C.stage.z + stage2LogExtent ≤ C.stage.d)
    (hdev : C.stage.d + 8 ≤ G.ev ∨ G.ev + G.evcap ≤ C.stage.d) :
    ∃ s', WalkLink (stage2Calls stage2SubCalls) G C s
      { C with block := (if evalICmp .eq xout (BitVec.ofNat 32 0) = 1
          then "if.then25.i" else "if.end67.critedge.i") } s' := by
  obtain ⟨hframe, howned, hlog, hev⟩ :=
    walkNumFast_facts (G := G) (C := C) (s := s) hInv (m := r.mem) hm hdlog hdev
  let s₁ : State := stateAt (cells [
    ("%tobool24.not.not.i", .int 1 (evalICmp .eq xout (BitVec.ofNat 32 0))),
    ("%call23.i", r.ret),
    ("%sub.i99", .int 64 (x - y))] s.env) { s with mem := r.mem, next := r.next }
  have hden : denoteCode (stage2Calls stage2SubCalls) walkIfThen19.instrs s = some s₁ := by
    dsimp only [s₁]
    exact walkIfThen19_denote (sub := stage2SubCalls) (env := s.env) (s := s)
      (x := x) (y := y) (p := p) (dof := C.stage.d) (eof := G.next0)
      (xout := xout) (r := r) hd he hee hix harr hcall hretv
  have hpc : s.pc = C.block := hInv.pc_eq
  let bit := evalICmp .eq xout (BitVec.ofNat 32 0)
  let s' : State := { s₁ with
    pc := (if bit = 1 then "if.then25.i" else "if.end67.critedge.i"), pre := some s.pc }
  have hstep : LeanLLVM.step (stage2Calls stage2SubCalls) stage2Body s = Ctrl.jump s' := by
    have hfind : stage2Body.findBlock s.pc = some walkIfThen19 := by
      rw [hpc, hblock]; exact walkIfThen19_find
    have hterm : walkIfThen19.term =
        Term.condbr (Operand.reg "%tobool24.not.not.i") "if.then25.i"
          "if.end67.critedge.i" := rfl
    simp only [LeanLLVM.step, hfind, hden, hterm]
    rw [walkExecTerm_condbr (d := "%tobool24.not.not.i") (tl := "if.then25.i")
      (fl := "if.end67.critedge.i") (bit := bit)
      (by dsimp only [s₁, bit]; simp [stateAt, cells, lookupName])]
    dsimp only [s', s₁, bit, cells, stateAt]
  refine ⟨s', ⟨hInv, hstep, ?_, le_of_eq rfl⟩⟩
  refine
    { pc_eq := rfl
      blockIndex := ?_
      k_le := hInv.k_le
      events_le := hInv.events_le
      evlen_eq := hInv.evlen_eq
      evBytes := ?_
      alen_le_sum := hInv.alen_le_sum
      alen_ge := hInv.alen_ge
      spans_order := hInv.spans_order
      spans_end := hInv.spans_end
      spans_inside := hInv.spans_inside
      pending_at := hInv.pending_at
      pending_cursor := hInv.pending_cursor
      pending_len := hInv.pending_len
      eoff_le := hInv.eoff_le
      inner_cap := hInv.inner_cap
      depth_cap := hInv.depth_cap
      depth_reg := ?_
      sp_le_wlen := hInv.sp_le_wlen
      wlen_cap := hInv.wlen_cap
      tyBytes := by
        dsimp only [s', s₁, stateAt]
        have h1 : (wordBytes 8 w).length = 8 := by simp [wordBytes, natToBytes_length]
        have h2 : (wordBytes 8 w').length = 8 := by simp [wordBytes, natToBytes_length]
        have hm2 := hm
        rcases hm2 with h | h
        · rw [h]
          refine hInv.tyBytes.write_outside ?_
          rcases (stack_d_sep hInv).1 with h' | h'
          · exact Or.inr (by omega)
          · exact Or.inl (by omega)
        · rw [h]
          refine hInv.tyBytes.write_outside (Or.inr ?_)
          have hse := (stack_alloca_sep (G := G) (C := C) (s := s) hInv
            (a := G.next0) (by omega)).1
          omega
      stBytes := by
        dsimp only [s', s₁, stateAt]
        have h1 : (wordBytes 8 w).length = 8 := by simp [wordBytes, natToBytes_length]
        have h2 : (wordBytes 8 w').length = 8 := by simp [wordBytes, natToBytes_length]
        have hm2 := hm
        rcases hm2 with h | h
        · rw [h]
          refine hInv.stBytes.write_outside ?_
          rcases (stack_d_sep hInv).2 with h' | h'
          · exact Or.inr (by omega)
          · exact Or.inl (by omega)
        · rw [h]
          refine hInv.stBytes.write_outside (Or.inr ?_)
          have hse := (stack_alloca_sep (G := G) (C := C) (s := s) hInv
            (a := G.next0) (by omega)).2
          omega
      ptrs := ?_
      regs := ?_
      iter := ?_
      log_hash := ?_
      log_len := ?_
      log_cap := ?_
      log_alen := ?_
      log_acap := ?_
      owned := ?_
      frame := ?_
      blockLocal := by
        by_cases hb : bit = 1
        · rw [ite_eq_left hb]; simp [WalkLocal]
        · rw [ite_eq_right hb]; simp [WalkLocal] }
  · rw [show s'.env = s₁.env from rfl]
    rw [denoteCode_lookupName (stage2Calls stage2SubCalls) walkIfThen19.instrs
      "%k.0.i249" (by refine fun i hi => ?_; simp only [walkIfThen19, List.mem_cons, List.not_mem_nil,
        or_false] at hi; rcases hi with rfl | rfl | rfl | rfl | rfl <;> decide) s s₁ hden]
    exact hInv.blockIndex
  · rw [show s'.mem = r.mem from rfl, hev]
    exact hInv.evBytes
  · rw [show s'.env = s₁.env from rfl]
    rw [denoteCode_lookupName (stage2Calls stage2SubCalls) walkIfThen19.instrs
      "%sp.i.0248" (by refine fun i hi => ?_; simp only [walkIfThen19, List.mem_cons, List.not_mem_nil,
        or_false] at hi; rcases hi with rfl | rfl | rfl | rfl | rfl <;> decide) s s₁ hden]
    exact hInv.depth_reg
  · rw [show s'.env = s₁.env from rfl]
    exact WalkPtrs.of_run hInv.ptrs (by unfold walkCarried; decide) hden
  · rw [show s'.env = s₁.env from rfl]
    exact WalkRegs.of_run hInv.regs (by unfold walkCarried; decide) hden
  · rw [show s'.env = s₁.env from rfl]
    exact WalkIter.of_run hInv.iter (by unfold walkCarried; decide) hden
  · rw [show s'.mem = r.mem from rfl, hlog 32 4 (by decide)]
    exact hInv.log_hash
  · rw [show s'.mem = r.mem from rfl, hlog 8 8 (by decide)]
    exact hInv.log_len
  · rw [show s'.mem = r.mem from rfl, hlog 16 8 (by decide)]
    exact hInv.log_cap
  · rw [show s'.mem = r.mem from rfl, hlog 48 8 (by decide)]
    exact hInv.log_alen
  · rw [show s'.mem = r.mem from rfl, hlog 56 8 (by decide)]
    exact hInv.log_acap
  · show ∀ q ∈ walkStaged G C, HasBytes r.mem q.1 q.2
    exact howned
  · rw [show s'.mem = r.mem from rfl]
    exact hframe

/-! ### The instrument -/

/-- info: 'LeanLLVM.Refinement.WalkScope.walkIfThen425_denote' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.WalkScope.walkIfThen425_denote

/-- info: 'LeanLLVM.Refinement.WalkScope.WalkLink.if_then425_i_emit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.WalkScope.WalkLink.if_then425_i_emit

/-- info: 'LeanLLVM.Refinement.WalkScope.WalkLink.if_then425_i_refuse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.WalkScope.WalkLink.if_then425_i_refuse

/-- info: 'LeanLLVM.Refinement.WalkScope.walkIfThen109_denote' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.WalkScope.walkIfThen109_denote

/-- info: 'LeanLLVM.Refinement.WalkScope.WalkLink.if_then109_i' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.WalkScope.WalkLink.if_then109_i

/-- info: 'LeanLLVM.Refinement.WalkScope.walkAfterValue_facts_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.WalkScope.walkAfterValue_facts_at

/-- info: 'LeanLLVM.Refinement.WalkScope.walkIfThen19_denote' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.WalkScope.walkIfThen19_denote

/-- info: 'LeanLLVM.Refinement.WalkScope.WalkLink.if_then19_i' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.WalkScope.WalkLink.if_then19_i

/-- info: 'LeanLLVM.Refinement.WalkScope.walkNumFast_facts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.WalkScope.walkNumFast_facts

end WalkScope

end LeanLLVM.Refinement
