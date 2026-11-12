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
one (`%c.i + 1112`'s pointer), so the link takes the model's `stage2ErrSet` shape
at `C.stage.e`.
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
      spans_inside := hInv.spans_inside
      pending_at := hInv.pending_at
      pending_cursor := hInv.pending_cursor
      pending_len := hInv.pending_len
      eoff_le := hInv.eoff_le
      inner_cap := hInv.inner_cap
      depth_cap := hInv.depth_cap
      depth_reg := ?_
      ptrs := ?_
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
  · show readBytes r.mem (C.stage.z + 32) 4 = some (natToBytes 0 4)
    rw [hlogRead 32 4 (by decide) (by decide)]; exact hInv.log_hash
  · show readBytes r.mem (C.stage.z + 16) 8 = some (wordBytes 8 G.evcap)
    rw [hlogRead 16 8 (by decide) (by decide)]; exact hInv.log_cap
  · show readBytes r.mem (C.stage.z + 48) 8 = some (wordBytes 8 C.alen)
    rw [hlogRead 48 8 (by decide) (by decide)]; exact hInv.log_alen
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
    (hrefuse : r.mem = stage2ErrSet s.mem (C.stage.e) pos)
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
  have herr8Log : ∀ off N, off + N ≤ stage2LogExtent →
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
  have herr8Ev : readBytes (writeBytes (writeBytes s.mem C.stage.e (wordBytes 4 0)) (C.stage.e + 8)
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
      spans_inside := hInv.spans_inside
      pending_at := hInv.pending_at
      pending_cursor := hInv.pending_cursor
      pending_len := hInv.pending_len
      eoff_le := hInv.eoff_le
      inner_cap := hInv.inner_cap
      depth_cap := hInv.depth_cap
      depth_reg := ?_
      ptrs := ?_
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
    rw [hrefuse, stage2ErrSet]
    rw [herr8Ev]
    exact hInv.evBytes
  · rw [show s'.env = s₁.env from rfl]
    rw [denoteCode_lookupName (stage2Calls stage2SubCalls) walkIfThen425.instrs
      "%sp.i.0248" (by refine fun i hi => ?_; simp only [walkIfThen425, List.mem_cons,
        List.not_mem_nil, or_false] at hi; rcases hi with rfl | rfl <;> decide) s s₁ hden]
    exact hInv.depth_reg
  · rw [show s'.env = s₁.env from rfl]
    exact WalkPtrs.of_run hInv.ptrs (by unfold walkCarried; decide) hden
  · show readBytes r.mem (C.stage.z + 32) 4 = some (natToBytes 0 4)
    rw [hrefuse, stage2ErrSet]
    rw [herr8Log 32 4 (by decide)]
    exact hInv.log_hash
  · show readBytes r.mem (C.stage.z + 8) 8 = some (wordBytes 8 C.evlen)
    rw [hrefuse, stage2ErrSet]
    rw [herr8Log 8 8 (by decide)]
    exact hInv.log_len
  · show readBytes r.mem (C.stage.z + 16) 8 = some (wordBytes 8 G.evcap)
    rw [hrefuse, stage2ErrSet]
    rw [herr8Log 16 8 (by decide)]
    exact hInv.log_cap
  · show readBytes r.mem (C.stage.z + 48) 8 = some (wordBytes 8 C.alen)
    rw [hrefuse, stage2ErrSet]
    rw [herr8Log 48 8 (by decide)]
    exact hInv.log_alen
  · show readBytes r.mem (C.stage.z + 56) 8 = some (wordBytes 8 G.dstcap)
    rw [hrefuse, stage2ErrSet]
    rw [herr8Log 56 8 (by decide)]
    exact hInv.log_acap
  · show ∀ q ∈ walkStaged G C, HasBytes r.mem q.1 q.2
    rw [hrefuse]
    unfold stage2ErrSet
    exact walkStaged_write rfl (walkStaged_write rfl hInv.owned)
  · show UnchangedOutside m0 r.mem (walkWide G C)
    rw [hrefuse]
    unfold stage2ErrSet
    have hregion : (C.stage.e, stage2ErrorExtent) ∈ walkWide G C := by
      simp [walkWide, walkPresent, stage2ReportScratch, stage2StagedWrites]
    refine UnchangedOutside.write_le (a := C.stage.e + 8) (w := 8)
      (UnchangedOutside.write_le (a := C.stage.e) (w := 4) hInv.frame
        ⟨(C.stage.e, stage2ErrorExtent), hregion, by omega,
          by simp only [stage2ErrorExtent]; omega⟩
        (bs := wordBytes 4 0) (by simp [wordBytes, natToBytes_length]))
      ⟨(C.stage.e, stage2ErrorExtent), hregion, by simp only [stage2ErrorExtent]; omega,
        by simp only [stage2ErrorExtent]; omega⟩
      (bs := wordBytes 8 pos) (by simp [wordBytes, natToBytes_length])

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

end WalkScope

end LeanLLVM.Refinement
