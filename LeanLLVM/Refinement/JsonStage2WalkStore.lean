/-
Class D of the walk's census: the ten store blocks.

The census (`JsonStage2WalkScope`) classifies the dispatch's `store` shapes as
class D and names ten of them.  Each is a block of the pinned body whose
`denoteCode` chain ends in a store, so each link is a `denoteCode` trace, a
`step`, and the invariant rebuilt clause by clause — the pattern
`WalkLink.refusalStore` sets at class C.  Eight of the ten leave the carry's
block only; the two event-stream stores advance `evlen`/`events`, and the arena
cursor store advances `alen`/`spans`.

The addresses the invariant does not bind are the callers', exactly as class C
and class A take theirs: the two hash stores' `%z + 24`, the two container-stack
bytes' `%cst.i + q`, the arena cursor's log field and the state-stack byte's
index are the previous blocks' products.  The memory clauses are transported
across each write by `walkReadBytes_writeBytes_outside`, and the region claim by
`owns_writeBytes_inside`; the two event stores need one new append lemma and the
arena-cursor store needs the region's growth, both proved here.
-/
import LeanLLVM.Refinement.JsonStage2WalkScope

set_option autoImplicit false

namespace LeanLLVM.Refinement
namespace WalkScope

open LeanLLVM
open LeanLLVM.Refinement.JsonStage2IR
open LeanLLVM.Refinement.BlockEval

/-! ## Helper lemmas

The chain shapes the ten blocks use beyond the existing vocabulary: a pointer
load, `mul` (absent from the tree's `denoteCode` steps), the append of one byte
to a readable event trace, and the log's own internal writes.  Then the two
separations the staging owes (the cursor record against the event stream, the
log against the event stream), the region claim's growth, and the
`sub %sp, 1` arithmetic `if.then330.i` writes. -/

/-- A `ptr` load of `wordBytes 8 q` at an address is `q`. -/
theorem walkLoadValuePtr {m : Mem} {a q : Nat}
    (h : readBytes m a 8 = some (wordBytes 8 q)) (hq : q < 2 ^ 64) :
    loadValue m .ptr a = some (.ptr q) := by
  simp only [loadValue, h, wordBytes]
  rw [natToBytes_toNat, show (256 : Nat) ^ 8 = 2 ^ 64 from by decide,
    Nat.mod_eq_of_lt hq]

/-- `%d = load ptr, ptr %p`, at a pointer word. -/
theorem walkDenoteCode_loadPtr (calls : Calls) (env : Env) (s : State) (d p : String)
    {a q : Nat}
    (hp : lookupName env p = some (.ptr a))
    (hv : readBytes s.mem a 8 = some (wordBytes 8 q)) (hq : q < 2 ^ 64)
    (is : List Instr) :
    denoteCode calls (.load d .ptr (.reg p) :: is) (stateAt env s) =
      denoteCode calls is (stateAt ((d, .ptr q) :: env) s) := by
  have h : evalInstr calls (stateAt env s) (.load d .ptr (.reg p)) =
      some (stateAt ((d, .ptr q) :: env) s) := by
    simpa only [stateAt, State.bind, withEnv] using
      LeanLLVM.Refinement.JsonS1MasksIR.evalInstr_load
        (hp := evalOperand_reg_of env s p (.ptr a) hp)
        (hv := walkLoadValuePtr hv hq)
  exact denoteCode_cons_of _ _ _ _ _ h

/-- `%d = mul i64 %a, <c>`, the shape the two hash updates write and the tree
does not yet have a step for. -/
theorem walkEvalInstr_mul_imm (calls : Calls) (env : Env) (s : State) (d a : String)
    {x c : BitVec 64}
    (ha : lookupName env a = some (.int 64 x)) :
    evalInstr calls (stateAt env s) (.binop d .mul 64 (.reg a) (.imm (.int 64 c))) =
      some (stateAt ((d, .int 64 (x * c)) :: env) s) := by
  simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq, stateAt, State.bind, withEnv]
    using LeanLLVM.Refinement.JsonS1MasksIR.evalInstr_binop (r := (x * c).toNat)
      (ha := evalOperand_reg_of env s a (.int 64 x) ha)
      (hb := evalOperand_lit_of _ 64 c)
      (hr := by simp [evalBinopNat, evalBinop, BitVec.ofNat_toNat])

/-- The chain step for `mul`. -/
theorem walkDenoteCode_mul_imm (calls : Calls) (env : Env) (s : State) (d a : String)
    {x c : BitVec 64}
    (ha : lookupName env a = some (.int 64 x)) (is : List Instr) :
    denoteCode calls (.binop d .mul 64 (.reg a) (.imm (.int 64 c)) :: is) (stateAt env s) =
      denoteCode calls is (stateAt ((d, .int 64 (x * c)) :: env) s) := by
  rw [denoteCode_cons_of _ _ _ _ _ (walkEvalInstr_mul_imm calls env s d a ha)]

/-- **One byte appended to a readable trace.**  From a readable `N`-byte flat
trace, the byte written at its end makes the trace readable at `N + 1` and its
content the old trace followed by the byte.  This is the event stream's write
shape; the tree has no append lemma for `readBytes`. -/
theorem walkReadBytes_writeByte_append {m : Mem} :
    ∀ {a N : Nat} {flat : List UInt8}, readBytes m a N = some flat →
      ∀ b : UInt8, readBytes (writeByte m (a + N) b) a (N + 1) = some (flat ++ [b])
  | a, 0, flat, h, b => by
      simp only [readBytes, Option.some.injEq] at h
      subst h
      rw [show a + 0 = a from rfl, show (0 : Nat) + 1 = 1 from rfl]
      rw [show writeByte m a b = writeBytes m a [b] from rfl]
      rw [show (1 : Nat) = ([b] : List UInt8).length from rfl]
      rw [readBytes_writeBytes_same]
      rfl
  | a, N + 1, flat, h, b => by
      rw [readBytes] at h
      split at h
      · exact absurd h (by simp)
      · rename_i c hc
        split at h
        · exact absurd h (by simp)
        · rename_i rest hr
          simp only [Option.some.injEq] at h
          subst h
          rw [show a + (N + 1) = (a + 1) + N from by omega]
          rw [readBytes]
          rw [readByte_writeByte_other m b (by omega)]
          rw [hc]
          rw [walkReadBytes_writeByte_append (a := a + 1) (N := N) hr b]
          rfl

/-- **A write to a log field leaves the event stream alone.** -/
theorem walkReadBytes_ev_of_log_write {m : Mem} {z ev evcap nev0 N off : Nat}
    {v : List UInt8}
    (hzev : z + stage2LogExtent ≤ ev ∨ ev + evcap ≤ z)
    (hoff : off + v.length ≤ stage2LogExtent) (hN : nev0 + N ≤ evcap) :
    readBytes (writeBytes m (z + off) v) (ev + nev0) N = readBytes m (ev + nev0) N := by
  refine walkReadBytes_writeBytes_outside (start := z + off) (addr := ev + nev0) (n := N) ?_
  rcases hzev with h | h
  · right
    simp only [stage2LogExtent] at *
    omega
  · left
    simp only [stage2LogExtent] at *
    omega

/-- **A write to a log field leaves another of the log's fields alone.** -/
theorem walkReadBytes_log_of_log_write {m : Mem} {z off off' N : Nat} {v : List UInt8}
    (hlo : off' + N ≤ off ∨ off + v.length ≤ off') :
    readBytes (writeBytes m (z + off) v) (z + off') N = readBytes m (z + off') N := by
  refine walkReadBytes_writeBytes_outside (start := z + off) (addr := z + off') (n := N) ?_
  rcases hlo with h | h
  · left; omega
  · right; omega

/-- `%d = %a - 1` at `i32`, as the emitted body's `add i32 %sp, 4294967295`. -/
theorem walkOfNat32_add_pred {q : Nat} (hq : 1 ≤ q) (hq32 : q < 2 ^ 32) :
    BitVec.ofNat 32 q + BitVec.ofNat 32 4294967295 = BitVec.ofNat 32 (q - 1) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt hq32]
  have h4294967295 : 4294967295 = 2 ^ 32 - 1 := by decide
  rw [h4294967295, Nat.mod_eq_of_lt (by decide : (2 : Nat) ^ 32 - 1 < 2 ^ 32)]
  rw [show q + (2 ^ 32 - 1) = (q - 1) + 1 * 2 ^ 32 from by omega]
  rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]

/-! ### The two separations the staging still owes

`ctype_ev_sep`/`cst_ev_sep` read the cursor record's neighbours out of
`stage2WalkRegions`; the cursor record and the log are entries 8 and 13, and the
event stream entry 4, so the same read gives them. -/

/-- **The cursor record and the event stream are separate.** -/
theorem walkCursor_ev_sep {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {s : State}
    (_h : WalkInv G C s) :
    C.stage.c + stage2CursorExtent ≤ G.ev ∨ G.ev + G.evcap ≤ C.stage.c := by
  have hpair : (stage2WalkRegions G.b G.n G.ep G.nep G.xp G.nxp G.dst G.ndst0 G.ev
      G.evcap G.ndst G.nev G.err C.stage.c C.stage.ctype C.stage.cst C.stage.tok
      C.stage.s C.stage.z C.stage.e).Pairwise
      (fun r q => r.1 + r.2 ≤ q.1 ∨ q.1 + q.2 ≤ r.1) := by
    have hsep := C.stage.separate
    unfold DisjointRegions at hsep
    rw [stage2StagedRegions] at hsep
    exact (List.pairwise_append.mp hsep).1
  have hlen : (stage2WalkRegions G.b G.n G.ep G.nep G.xp G.nxp G.dst G.ndst0 G.ev
      G.evcap G.ndst G.nev G.err C.stage.c C.stage.ctype C.stage.cst C.stage.tok
      C.stage.s C.stage.z C.stage.e).length = 15 := by
    simp [stage2WalkRegions, stage2Regions, stage2StagedWrites]
  have h' := List.pairwise_iff_getElem.mp hpair 4 8 (by omega) (by omega) (by omega)
  simpa [stage2WalkRegions, stage2Regions, stage2StagedWrites] using h'.symm

/-- **The log and the event stream are separate.** -/
theorem walkLog_ev_sep {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {s : State}
    (_h : WalkInv G C s) :
    C.stage.z + stage2LogExtent ≤ G.ev ∨ G.ev + G.evcap ≤ C.stage.z := by
  have hpair : (stage2WalkRegions G.b G.n G.ep G.nep G.xp G.nxp G.dst G.ndst0 G.ev
      G.evcap G.ndst G.nev G.err C.stage.c C.stage.ctype C.stage.cst C.stage.tok
      C.stage.s C.stage.z C.stage.e).Pairwise
      (fun r q => r.1 + r.2 ≤ q.1 ∨ q.1 + q.2 ≤ r.1) := by
    have hsep := C.stage.separate
    unfold DisjointRegions at hsep
    rw [stage2StagedRegions] at hsep
    exact (List.pairwise_append.mp hsep).1
  have hlen : (stage2WalkRegions G.b G.n G.ep G.nep G.xp G.nxp G.dst G.ndst0 G.ev
      G.evcap G.ndst G.nev G.err C.stage.c C.stage.ctype C.stage.cst C.stage.tok
      C.stage.s C.stage.z C.stage.e).length = 15 := by
    simp [stage2WalkRegions, stage2Regions, stage2StagedWrites]
  have h' := List.pairwise_iff_getElem.mp hpair 4 13 (by omega) (by omega) (by omega)
  simpa [stage2WalkRegions, stage2Regions, stage2StagedWrites] using h'.symm

/-! ## The three container-stack bytes

`if.end150.i`, `if.end162.i` and `if.end195.i` are one `store i8 <imm>,
%arrayidx143.i`/`%arrayidx188.i` and a jump to the merge.  The address is the
state stack's byte at the depth the previous block indexed; the store binds
nothing, so every register clause is the one it had, and the write is inside the
state stack's extent. -/

/-- **The state-stack byte store.**  One `i8` literal at `%cst.i + q`, with `q`
inside the stack's extent. -/
theorem WalkLink.store8Stack {calls : Calls} {m0 : Mem} (G : WalkGeom m0)
    (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    {B : Block} (hfind : stage2Body.findBlock C.block = some B)
    {p : String} {x : BitVec 8} {q : Nat}
    (hinstrs : B.instrs = [Instr.store (.int 8) (.imm (.int 8 x)) (.reg p)])
    (hterm : B.term = Term.br "cleanup478.i")
    (hp : lookupName s.env p = some (.ptr (C.stage.cst + q)))
    (hq : q < stage2StackExtent) :
    ∃ s', WalkLink calls G C s { C with block := "cleanup478.i" } s' := by
  have hpc : s.pc = C.block := hInv.pc_eq
  have hlen : (natToBytes x.toNat 1).length = 1 := by simp [natToBytes_length]
  have hv : (natToBytes x.toNat 1).length ≤ 1 := by omega
  let m' : Mem := writeBytes s.mem (C.stage.cst + q) (natToBytes x.toNat 1)
  let s' : State := { stateAt s.env { s with mem := m' } with pc := "cleanup478.i", pre := some s.pc }
  have hden : denoteCode calls B.instrs s = some (stateAt s.env { s with mem := m' }) := by
    rw [hinstrs, ← stateAt_self s]
    exact denoteCode_store8_imm calls s.env s x p hp []
  have hstep : LeanLLVM.step calls stage2Body s = Ctrl.jump s' := by
    simp only [LeanLLVM.step, hpc, hfind, hden, hterm, execTerm]
    dsimp only [s', m', stateAt]
    rw [hpc]
  have hN : G.nev0 + (C.events.map EventRecord.encodedBytes).flatten.length ≤ G.evcap := by
    have hsum := EventRecord.sum_encodedSize_le C.events
    simp only [stage2RecordBytes] at hsum
    have hroom := G.evRoom
    simp only [stage2RecordBytes] at hroom
    have hlen : (C.events.map EventRecord.encodedBytes).flatten.length =
        (C.events.map EventRecord.encodedSize).sum := by
      simp only [List.length_flatten, List.map_map]
      rfl
    have h1 := hInv.events_le
    have h2 := hInv.k_le
    have h3 := G.nep_le
    rw [hlen]; omega
  have hsz := cst_log_sep hInv
  have hsev := cst_ev_sep hInv
  refine ⟨s', ⟨hInv, hstep, ?_, ?_⟩⟩
  · refine
      { pc_eq := rfl
        blockIndex := hInv.blockIndex
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
        depth_reg := hInv.depth_reg
        ptrs := hInv.ptrs
        log_hash := ?_
        log_len := ?_
        log_cap := ?_
        log_alen := ?_
        log_acap := ?_
        owned := walkStaged_write rfl hInv.owned
        frame := ?_
        blockLocal := ?_ }
    · dsimp only [s', stateAt, m']
      rw [readBytes_ev_of_stack_write (base := C.stage.cst)
        (v := natToBytes x.toNat 1) hsev (sp := q) hq hv
        (ev := G.ev) (evcap := G.evcap) (nev0 := G.nev0)
        (N := (C.events.map EventRecord.encodedBytes).flatten.length) hN]
      exact hInv.evBytes
    · dsimp only [s', stateAt, m']
      rw [readBytes_log_of_stack_write (base := C.stage.cst)
        (v := natToBytes x.toNat 1) hsz (sp := q) hq hv (off := 32) (len := 4) (by decide)]
      exact hInv.log_hash
    · dsimp only [s', stateAt, m']
      rw [readBytes_log_of_stack_write (base := C.stage.cst)
        (v := natToBytes x.toNat 1) hsz (sp := q) hq hv (off := 8) (len := 8) (by decide)]
      exact hInv.log_len
    · dsimp only [s', stateAt, m']
      rw [readBytes_log_of_stack_write (base := C.stage.cst)
        (v := natToBytes x.toNat 1) hsz (sp := q) hq hv (off := 16) (len := 8) (by decide)]
      exact hInv.log_cap
    · dsimp only [s', stateAt, m']
      rw [readBytes_log_of_stack_write (base := C.stage.cst)
        (v := natToBytes x.toNat 1) hsz (sp := q) hq hv (off := 48) (len := 8) (by decide)]
      exact hInv.log_alen
    · dsimp only [s', stateAt, m']
      rw [readBytes_log_of_stack_write (base := C.stage.cst)
        (v := natToBytes x.toNat 1) hsz (sp := q) hq hv (off := 56) (len := 8) (by decide)]
      exact hInv.log_acap
    · dsimp only [s', stateAt, m']
      refine walkFrame_write_inside hInv.frame ?_
      intro k hk
      have hk0 : k = 0 := by omega
      subst hk0
      refine walkWide_of_seven ?_
      refine ⟨(C.stage.cst, stage2StackExtent), by simp [stage2StagedWrites], by omega, ?_⟩
      simp only [stage2StackExtent] at hq ⊢
      omega
    · dsimp only [s']
      simp [WalkLocal]
  · rfl

/-- `if.end150.i`: the state stack's byte is set to `4`. -/
def walkIf_end150_i : Block :=
  { name := "if.end150.i",
    instrs := [Instr.store (.int 8) (.imm (.int 8 (BitVec.ofNat 8 4)))
      (.reg "%arrayidx143.i")],
    term := Term.br "cleanup478.i" }

theorem walkIf_end150_i_find :
    stage2Body.findBlock "if.end150.i" = some walkIf_end150_i := by
  simp [stage2Body, Function.findBlock, findBlockList, walkIf_end150_i]

theorem WalkLink.if_end150_i {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "if.end150.i")
    {q : Nat} (hp : lookupName s.env "%arrayidx143.i" = some (.ptr (C.stage.cst + q)))
    (hq : q < stage2StackExtent) :
    ∃ s', WalkLink calls G C s { C with block := "cleanup478.i" } s' := by
  exact WalkLink.store8Stack G C s hInv
    (by rw [hblock]; exact walkIf_end150_i_find) rfl rfl hp hq

/-- `if.end162.i`: the state stack's byte is set to `2`. -/
def walkIf_end162_i : Block :=
  { name := "if.end162.i",
    instrs := [Instr.store (.int 8) (.imm (.int 8 (BitVec.ofNat 8 2)))
      (.reg "%arrayidx143.i")],
    term := Term.br "cleanup478.i" }

theorem walkIf_end162_i_find :
    stage2Body.findBlock "if.end162.i" = some walkIf_end162_i := by
  simp [stage2Body, Function.findBlock, findBlockList, walkIf_end162_i]

theorem WalkLink.if_end162_i {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "if.end162.i")
    {q : Nat} (hp : lookupName s.env "%arrayidx143.i" = some (.ptr (C.stage.cst + q)))
    (hq : q < stage2StackExtent) :
    ∃ s', WalkLink calls G C s { C with block := "cleanup478.i" } s' := by
  exact WalkLink.store8Stack G C s hInv
    (by rw [hblock]; exact walkIf_end162_i_find) rfl rfl hp hq

/-- `if.end195.i`: the state stack's byte is set to `2`. -/
def walkIf_end195_i : Block :=
  { name := "if.end195.i",
    instrs := [Instr.store (.int 8) (.imm (.int 8 (BitVec.ofNat 8 2)))
      (.reg "%arrayidx188.i")],
    term := Term.br "cleanup478.i" }

theorem walkIf_end195_i_find :
    stage2Body.findBlock "if.end195.i" = some walkIf_end195_i := by
  simp [stage2Body, Function.findBlock, findBlockList, walkIf_end195_i]

theorem WalkLink.if_end195_i {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "if.end195.i")
    {q : Nat} (hp : lookupName s.env "%arrayidx188.i" = some (.ptr (C.stage.cst + q)))
    (hq : q < stage2StackExtent) :
    ∃ s', WalkLink calls G C s { C with block := "cleanup478.i" } s' := by
  exact WalkLink.store8Stack G C s hInv
    (by rw [hblock]; exact walkIf_end195_i_find) rfl rfl hp hq


/-! ### The chain vocabulary for these blocks

`block_step` has no `mul`, and four of the ten blocks use it; the two macros
below are `walk_step`/`walk_close`'s phase order with the `mul` step added, so a
block's chain is a computation and the side goals are discharged against the
statement's builder. -/

macro "walk_store_step" : tactic => `(tactic|
  (first
   | rw [walkDenoteCode_mul_imm _ _ _ _ _ ?_ _]
   | block_step))

macro "walk_store_eval" : tactic => `(tactic|
  (repeat walk_store_step
   block_close
   all_goals (try omega)))


/-! ## The two hash updates

`if.then.i.i` and `if.then.i.i50` are the same six instructions: load the log's
hash word at `%z + 24`, extend the state byte, mix it in with `xor`, `mul` and
`add`, and store the word back.  The invariant has no clause for that word, so
what survives is everything else: the store is inside the log's extent, and the
log is separate from the event stream. -/

/-- **The hash update.**  Six instructions over the log's hash word; the value
they compute is the block's own, and only the store's address is used. -/
theorem WalkLink.hashStore {calls : Calls} {m0 : Mem} (G : WalkGeom m0)
    (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    {B : Block} (hfind : stage2Body.findBlock C.block = some B)
    {src ld xr xy xv xa : String} {b : BitVec 8} {v0 : Nat}
    (hinstrs : B.instrs = [
      Instr.load ld (.int 64) (.reg "%h1.i.i.i51"),
      Instr.zext xr 8 64 (.reg src),
      Instr.binop xy .xor 64 (.reg ld) (.reg xr),
      Instr.binop xv .mul 64 (.reg xy) (.imm (.int 64 (BitVec.ofNat 64 16088033396387240377))),
      Instr.binop xa .add 64 (.reg xv) (.imm (.int 64 (BitVec.ofNat 64 11400714819323198485))),
      Instr.store (.int 64) (.reg xa) (.reg "%h1.i.i.i51")])
    (hterm : B.term = Term.br "cleanup478.i")
    (hh : lookupName s.env "%h1.i.i.i51" = some (.ptr (C.stage.z + 24)))
    (hread : readBytes s.mem (C.stage.z + 24) 8 = some (wordBytes 8 v0))
    (hv0 : v0 < 2 ^ 64)
    (hs : lookupName s.env src = some (.int 8 b))
    (hsrc : ld ≠ src) (hxr_ld : xr ≠ ld)
    (hxa : xa ≠ "%h1.i.i.i51") (hxv : xv ≠ "%h1.i.i.i51")
    (hxy : xy ≠ "%h1.i.i.i51") (hxr : xr ≠ "%h1.i.i.i51")
    (hld : ld ≠ "%h1.i.i.i51")
    (hne : ∀ n, n ∈ [xa, xv, xy, xr, ld] →
      n ≠ "%k.0.i249" ∧ n ≠ "%sp.i.0248" ∧ n ≠ "%3" ∧ n ≠ "%5" ∧ n ≠ "%k11.i"
        ∧ n ≠ "%ctype.i" ∧ n ≠ "%cst.i" ∧ n ≠ "%hash1.i.i") :
    ∃ s', WalkLink calls G C s { C with block := "cleanup478.i" } s' := by
  have hpc : s.pc = C.block := hInv.pc_eq
  have hread' : readBytes s.mem (C.stage.z + 24) 8 =
      some (natToBytes (BitVec.ofNat 64 v0).toNat 8) := by
    rw [walkToNat_ofNat64 hv0]; exact hread
  let cs : List (String × Value) := [
    (xa, .int 64 (((BitVec.ofNat 64 v0 ^^^ BitVec.ofNat 64 b.toNat) *
      BitVec.ofNat 64 16088033396387240377) + BitVec.ofNat 64 11400714819323198485)),
    (xv, .int 64 ((BitVec.ofNat 64 v0 ^^^ BitVec.ofNat 64 b.toNat) *
      BitVec.ofNat 64 16088033396387240377)),
    (xy, .int 64 (BitVec.ofNat 64 v0 ^^^ BitVec.ofNat 64 b.toNat)),
    (xr, .int 64 (BitVec.ofNat 64 b.toNat)),
    (ld, .int 64 (BitVec.ofNat 64 v0))]
  let out : Env := cells cs s.env
  let m' : Mem := writeBytes s.mem (C.stage.z + 24)
    (natToBytes (((BitVec.ofNat 64 v0 ^^^ BitVec.ofNat 64 b.toNat) *
      BitVec.ofNat 64 16088033396387240377) + BitVec.ofNat 64 11400714819323198485).toNat 8)
  let s' : State := { stateAt out { s with mem := m' } with pc := "cleanup478.i", pre := some s.pc }
  have henv' : s'.env = out := rfl
  have hmem' : s'.mem = m' := rfl
  have hmem : ∀ c ∈ cs, c.1 ∈ [xa, xv, xy, xr, ld] := by
    intro c hc
    obtain ⟨n, w⟩ := c
    simp only [cs, List.mem_cons, List.not_mem_nil, or_false] at hc ⊢
    rcases hc with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> simp
  have hden : denoteCode calls B.instrs s = some (stateAt out { s with mem := m' }) := by
    rw [hinstrs, ← stateAt_self s]
    dsimp only [out, m', cs]
    rw [denoteCode_load64 calls s.env s ld "%h1.i.i.i51" (v := BitVec.ofNat 64 v0) hh hread'
      [Instr.zext xr 8 64 (.reg src),
       Instr.binop xy .xor 64 (.reg ld) (.reg xr),
       Instr.binop xv .mul 64 (.reg xy) (.imm (.int 64 (BitVec.ofNat 64 16088033396387240377))),
       Instr.binop xa .add 64 (.reg xv) (.imm (.int 64 (BitVec.ofNat 64 11400714819323198485))),
       Instr.store (.int 64) (.reg xa) (.reg "%h1.i.i.i51")]]
    rw [denoteCode_zext calls ((ld, .int 64 (BitVec.ofNat 64 v0)) :: s.env) s xr src 8 64
      (by rw [lookupName_cons_ne _ _ hsrc]; exact hs)
      [Instr.binop xy .xor 64 (.reg ld) (.reg xr),
       Instr.binop xv .mul 64 (.reg xy) (.imm (.int 64 (BitVec.ofNat 64 16088033396387240377))),
       Instr.binop xa .add 64 (.reg xv) (.imm (.int 64 (BitVec.ofNat 64 11400714819323198485))),
       Instr.store (.int 64) (.reg xa) (.reg "%h1.i.i.i51")]]
    rw [denoteCode_xor_reg calls _ s xy ld xr
      (by rw [lookupName_cons_ne _ _ hxr_ld, lookupName_cons_self])
      (by rw [lookupName_cons_self])
      [Instr.binop xv .mul 64 (.reg xy) (.imm (.int 64 (BitVec.ofNat 64 16088033396387240377))),
       Instr.binop xa .add 64 (.reg xv) (.imm (.int 64 (BitVec.ofNat 64 11400714819323198485))),
       Instr.store (.int 64) (.reg xa) (.reg "%h1.i.i.i51")]]
    rw [walkDenoteCode_mul_imm calls _ s xv xy (by rw [lookupName_cons_self])
      [Instr.binop xa .add 64 (.reg xv) (.imm (.int 64 (BitVec.ofNat 64 11400714819323198485))),
       Instr.store (.int 64) (.reg xa) (.reg "%h1.i.i.i51")]]
    rw [denoteCode_add_imm calls _ s xa xv (by rw [lookupName_cons_self])
      [Instr.store (.int 64) (.reg xa) (.reg "%h1.i.i.i51")]]
    rw [denoteCode_store64 calls _ s xa "%h1.i.i.i51" (by rw [lookupName_cons_self]) ?_ []]
    · dsimp only [cs, cells]
      rfl
    · rw [lookupName_cons_ne _ _ hxa, lookupName_cons_ne _ _ hxv,
        lookupName_cons_ne _ _ hxy, lookupName_cons_ne _ _ hxr,
        lookupName_cons_ne _ _ hld]
      exact hh
  have hstep : LeanLLVM.step calls stage2Body s = Ctrl.jump s' := by
    simp only [LeanLLVM.step, hpc, hfind, hden, hterm, execTerm]
    dsimp only [s', stateAt, out]
    rw [hpc]
  have hmlen : (natToBytes (((BitVec.ofNat 64 v0 ^^^ BitVec.ofNat 64 b.toNat) *
      BitVec.ofNat 64 16088033396387240377) + BitVec.ofNat 64 11400714819323198485).toNat 8).length = 8 :=
    natToBytes_length _ _
  have hN : G.nev0 + (C.events.map EventRecord.encodedBytes).flatten.length ≤ G.evcap := by
    have hsum := EventRecord.sum_encodedSize_le C.events
    simp only [stage2RecordBytes] at hsum
    have hroom := G.evRoom
    simp only [stage2RecordBytes] at hroom
    have hlen : (C.events.map EventRecord.encodedBytes).flatten.length =
        (C.events.map EventRecord.encodedSize).sum := by
      simp only [List.length_flatten, List.map_map]; rfl
    have h1 := hInv.events_le; have h2 := hInv.k_le; have h3 := G.nep_le
    rw [hlen]; omega
  have hzev := walkLog_ev_sep hInv
  refine ⟨s', ⟨hInv, hstep, ?_, ?_⟩⟩
  · refine
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
        ptrs := ?_
        log_hash := ?_
        log_len := ?_
        log_cap := ?_
        log_alen := ?_
        log_acap := ?_
        owned := walkStaged_write rfl hInv.owned
        frame := ?_
        blockLocal := ?_ }
    · rw [henv']
      dsimp only [out]
      exact walkLookup_cells_ne s.env "%k.0.i249" hInv.blockIndex cs
        (fun c hc => (hne c.1 (hmem c hc)).1)
    · rw [hmem']
      dsimp only [m']
      rw [walkReadBytes_ev_of_log_write (z := C.stage.z) (ev := G.ev) (evcap := G.evcap)
        (nev0 := G.nev0) (N := _) (off := 24) (v := natToBytes _ 8) hzev
        (by rw [hmlen]; decide) hN]
      exact hInv.evBytes
    · rw [henv']
      dsimp only [out]
      exact walkLookup_cells_ne s.env "%sp.i.0248" hInv.depth_reg cs
        (fun c hc => (hne c.1 (hmem c hc)).2.1)
    · rw [henv']
      dsimp only [out]
      exact hInv.ptrs.cells_of cs
        (fun c hc => ⟨(hne c.1 (hmem c hc)).2.2.1, (hne c.1 (hmem c hc)).2.2.2.1,
          (hne c.1 (hmem c hc)).2.2.2.2.1, (hne c.1 (hmem c hc)).2.2.2.2.2.1,
          (hne c.1 (hmem c hc)).2.2.2.2.2.2.1, (hne c.1 (hmem c hc)).2.2.2.2.2.2.2⟩)
    · rw [hmem']
      dsimp only [m']
      rw [walkReadBytes_log_of_log_write (z := C.stage.z) (off := 24)
        (off' := 32) (N := 4) (v := natToBytes _ 8) (by rw [hmlen]; omega)]
      exact hInv.log_hash
    · rw [hmem']
      dsimp only [m']
      rw [walkReadBytes_log_of_log_write (z := C.stage.z) (off := 24)
        (off' := 8) (N := 8) (v := natToBytes _ 8) (by rw [hmlen]; omega)]
      exact hInv.log_len
    · rw [hmem']
      dsimp only [m']
      rw [walkReadBytes_log_of_log_write (z := C.stage.z) (off := 24)
        (off' := 16) (N := 8) (v := natToBytes _ 8) (by rw [hmlen]; omega)]
      exact hInv.log_cap
    · rw [hmem']
      dsimp only [m']
      rw [walkReadBytes_log_of_log_write (z := C.stage.z) (off := 24)
        (off' := 48) (N := 8) (v := natToBytes _ 8) (by rw [hmlen]; omega)]
      exact hInv.log_alen
    · rw [hmem']
      dsimp only [m']
      rw [walkReadBytes_log_of_log_write (z := C.stage.z) (off := 24)
        (off' := 56) (N := 8) (v := natToBytes _ 8) (by rw [hmlen]; omega)]
      exact hInv.log_acap
    · rw [hmem']
      dsimp only [m']
      refine walkFrame_write_inside hInv.frame ?_
      intro k hk
      refine walkWide_of_seven ?_
      refine ⟨(C.stage.z, stage2LogExtent), by simp [stage2StagedWrites], by omega, ?_⟩
      simp only [stage2LogExtent] at ⊢
      omega
    · simp [WalkLocal]
  · rfl

/-! ### `if.then.i.i` and `if.then.i.i50`

The two blocks of the log's hash update, at their own registers: `%11`/`%18` for
the loaded word and `%conv42.i`/`%conv115.i` for the byte the state stack's push
left. -/

/-- `if.then.i.i`: the first hash update. -/
def walkIf_then_i_i : Block :=
  { name := "if.then.i.i",
    instrs := [
      Instr.load "%11" (.int 64) (.reg "%h1.i.i.i51"),
      Instr.zext "%conv.i.i.i" 8 64 (.reg "%conv42.i"),
      Instr.binop "%xor.us.i.i.i" .xor 64 (.reg "%11") (.reg "%conv.i.i.i"),
      Instr.binop "%12" .mul 64 (.reg "%xor.us.i.i.i")
        (.imm (.int 64 (BitVec.ofNat 64 16088033396387240377))),
      Instr.binop "%mul11.i.i.i" .add 64 (.reg "%12")
        (.imm (.int 64 (BitVec.ofNat 64 11400714819323198485))),
      Instr.store (.int 64) (.reg "%mul11.i.i.i") (.reg "%h1.i.i.i51")],
    term := Term.br "cleanup478.i" }

theorem walkIf_then_i_i_find :
    stage2Body.findBlock "if.then.i.i" = some walkIf_then_i_i := by
  simp [stage2Body, Function.findBlock, findBlockList, walkIf_then_i_i]

theorem WalkLink.if_then_i_i {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "if.then.i.i")
    {v0 : Nat} {b : BitVec 8}
    (hh : lookupName s.env "%h1.i.i.i51" = some (.ptr (C.stage.z + 24)))
    (hread : readBytes s.mem (C.stage.z + 24) 8 = some (wordBytes 8 v0))
    (hv0 : v0 < 2 ^ 64)
    (hs : lookupName s.env "%conv42.i" = some (.int 8 b)) :
    ∃ s', WalkLink calls G C s { C with block := "cleanup478.i" } s' := by
  exact WalkLink.hashStore G C s hInv
    (by rw [hblock]; exact walkIf_then_i_i_find) rfl rfl hh hread hv0 hs
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by intro n hn
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
        rcases hn with rfl | rfl | rfl | rfl | rfl <;>
          exact ⟨by decide, by decide, by decide, by decide, by decide, by decide,
            by decide, by decide⟩)

/-- `if.then.i.i50`: the second hash update. -/
def walkIf_then_i_i50 : Block :=
  { name := "if.then.i.i50",
    instrs := [
      Instr.load "%18" (.int 64) (.reg "%h1.i.i.i51"),
      Instr.zext "%conv.i.i.i52" 8 64 (.reg "%conv115.i"),
      Instr.binop "%xor.us.i.i.i53" .xor 64 (.reg "%18") (.reg "%conv.i.i.i52"),
      Instr.binop "%19" .mul 64 (.reg "%xor.us.i.i.i53")
        (.imm (.int 64 (BitVec.ofNat 64 16088033396387240377))),
      Instr.binop "%mul11.i.i.i54" .add 64 (.reg "%19")
        (.imm (.int 64 (BitVec.ofNat 64 11400714819323198485))),
      Instr.store (.int 64) (.reg "%mul11.i.i.i54") (.reg "%h1.i.i.i51")],
    term := Term.br "cleanup478.i" }

theorem walkIf_then_i_i50_find :
    stage2Body.findBlock "if.then.i.i50" = some walkIf_then_i_i50 := by
  simp [stage2Body, Function.findBlock, findBlockList, walkIf_then_i_i50]

theorem WalkLink.if_then_i_i50 {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "if.then.i.i50")
    {v0 : Nat} {b : BitVec 8}
    (hh : lookupName s.env "%h1.i.i.i51" = some (.ptr (C.stage.z + 24)))
    (hread : readBytes s.mem (C.stage.z + 24) 8 = some (wordBytes 8 v0))
    (hv0 : v0 < 2 ^ 64)
    (hs : lookupName s.env "%conv115.i" = some (.int 8 b)) :
    ∃ s', WalkLink calls G C s { C with block := "cleanup478.i" } s' := by
  exact WalkLink.hashStore G C s hInv
    (by rw [hblock]; exact walkIf_then_i_i50_find) rfl rfl hh hread hv0 hs
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by intro n hn
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
        rcases hn with rfl | rfl | rfl | rfl | rfl <;>
          exact ⟨by decide, by decide, by decide, by decide, by decide, by decide,
            by decide, by decide⟩)


/-! ## The two event-stream stores

`out_reserve.exit.i.i` and `.i60` are the same four instructions: load the event
stream's pointer from the log's first field, compute its end from the carried
event cursor, write the record's tag byte there, and write the new length into
the log's length field.  This is the one class-D shape that moves the carry:
`evlen` advances by one and the trace gains the record.  The tag byte is inside
the *grown* event prefix, the length word is inside the log, and the log is
separate from the event stream, so `evBytes` is the old trace followed by the
byte (`walkReadBytes_writeByte_append`) and `frame` is the region grown by one
byte (`walkWide_grow`). -/

/-- **The event-stream record store.** -/
theorem WalkLink.outReserveStore {calls : Calls} {m0 : Mem} (G : WalkGeom m0)
    (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    {B : Block} (hfind : stage2Body.findBlock C.block = some B)
    {ld gp st ldv src : String} {b : BitVec 8}
    (hinstrs : B.instrs = [
      Instr.load ld Ty.ptr (.reg "%z"),
      Instr.gep gp (.int 8) (.reg ld) (.reg ldv),
      Instr.store (.int 8) (.reg src) (.reg gp),
      Instr.store (.int 64) (.reg st) (.reg "%len")])
    (hterm : B.term = Term.br "cleanup478.i")
    (hz : lookupName s.env "%z" = some (.ptr C.stage.z))
    (hload : readBytes s.mem C.stage.z 8 = some (wordBytes 8 G.ev))
    (hev64 : G.ev < 2 ^ 64)
    (hs : lookupName s.env src = some (.int 8 b))
    (ho : lookupName s.env ldv = some (.int 64 (BitVec.ofNat 64 C.evlen)))
    (hst : lookupName s.env st = some (.int 64 (BitVec.ofNat 64 (C.evlen + 1))))
    (hlen : lookupName s.env "%len" = some (.ptr (C.stage.z + 8)))
    (hev63 : C.evlen < 2 ^ 63) (hev64len : C.evlen + 1 < 2 ^ 64)
    (hlt : C.events.length < C.k)
    (hldv : ld ≠ ldv) (hg_src : gp ≠ src) (hl_src : ld ≠ src)
    (hg_st : gp ≠ st) (hl_st : ld ≠ st)
    (hg_len : gp ≠ "%len") (hl_len : ld ≠ "%len")
    (hne : ∀ n, n ∈ [gp, ld] →
      n ≠ "%k.0.i249" ∧ n ≠ "%sp.i.0248" ∧ n ≠ "%3" ∧ n ≠ "%5" ∧ n ≠ "%k11.i"
        ∧ n ≠ "%ctype.i" ∧ n ≠ "%cst.i" ∧ n ≠ "%hash1.i.i") :
    ∃ s', WalkLink calls G C s
      { C with block := "cleanup478.i", evlen := C.evlen + 1, events := C.events ++ [EventRecord.tag b.toNat] } s' := by
  have hpc : s.pc = C.block := hInv.pc_eq
  let cs : List (String × Value) := [
    (gp, .ptr (G.ev + C.evlen)), (ld, .ptr G.ev)]
  let out : Env := cells cs s.env
  let m' : Mem := writeBytes (writeBytes s.mem (G.ev + C.evlen)
    (natToBytes b.toNat 1)) (C.stage.z + 8) (wordBytes 8 (C.evlen + 1))
  let s' : State := { stateAt out { s with mem := m' } with pc := "cleanup478.i", pre := some s.pc }
  have henv' : s'.env = out := rfl
  have hmem' : s'.mem = m' := rfl
  have hmem : ∀ c ∈ cs, c.1 ∈ [gp, ld] := by
    intro c hc
    obtain ⟨n, w⟩ := c
    simp only [cs, List.mem_cons, List.not_mem_nil, or_false] at hc ⊢
    rcases hc with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> simp
  have htag : natToBytes b.toNat 1 = [UInt8.ofNat b.toNat] := by
    simp only [natToBytes, Nat.mod_eq_of_lt b.isLt]
  have htaglen : (natToBytes b.toNat 1).length = 1 := natToBytes_length _ _
  have hden : denoteCode calls B.instrs s = some (stateAt out { s with mem := m' }) := by
    rw [hinstrs, ← stateAt_self s]
    dsimp only [out, m', cs]
    rw [walkDenoteCode_loadPtr calls s.env s ld "%z" (q := G.ev) hz hload hev64
      [Instr.gep gp (.int 8) (.reg ld) (.reg ldv),
       Instr.store (.int 8) (.reg src) (.reg gp),
       Instr.store (.int 64) (.reg st) (.reg "%len")]]
    rw [denoteCode_gep8_ofNat calls _ s gp ld ldv
      (by rw [lookupName_cons_self])
      (by rw [lookupName_cons_ne _ _ hldv]; exact ho) hev63
      [Instr.store (.int 8) (.reg src) (.reg gp),
       Instr.store (.int 64) (.reg st) (.reg "%len")]]
    rw [denoteCode_store8 calls _ s src gp
      (by rw [lookupName_cons_ne _ _ hg_src, lookupName_cons_ne _ _ hl_src]; exact hs)
      (by rw [lookupName_cons_self])
      [Instr.store (.int 64) (.reg st) (.reg "%len")]]
    rw [denoteCode_store64_ofNat calls _ { s with mem := writeBytes s.mem (G.ev + C.evlen) (natToBytes b.toNat 1) } st "%len"
      (by rw [lookupName_cons_ne _ _ hg_st, lookupName_cons_ne _ _ hl_st]; exact hst)
      hev64len
      (by rw [lookupName_cons_ne _ _ hg_len, lookupName_cons_ne _ _ hl_len]; exact hlen) []]
    dsimp only [cs, cells]
    rfl
  have hstep : LeanLLVM.step calls stage2Body s = Ctrl.jump s' := by
    simp only [LeanLLVM.step, hpc, hfind, hden, hterm, execTerm]
    dsimp only [s', stateAt, out]
    rw [hpc]
  have hEvLen : (C.events.map EventRecord.encodedBytes).flatten.length =
      (C.events.map EventRecord.encodedSize).sum := by
    simp only [List.length_flatten, List.map_map]; rfl
  have hN : G.nev0 + ((C.events.map EventRecord.encodedBytes).flatten.length + 1) ≤ G.evcap := by
    have hsum := EventRecord.sum_encodedSize_le C.events
    simp only [stage2RecordBytes] at hsum
    have hroom := G.evRoom
    simp only [stage2RecordBytes] at hroom
    have h1 := hlt
    have h2 := hInv.k_le
    have h3 := G.nep_le
    rw [hEvLen]
    omega
  have hevlen_lt : C.evlen < G.evcap := by
    have hsum := EventRecord.sum_encodedSize_le C.events
    simp only [stage2RecordBytes] at hsum
    have hroom := G.evRoom
    simp only [stage2RecordBytes] at hroom
    have h1 := hlt; have h2 := hInv.k_le; have h3 := G.nep_le
    rw [hInv.evlen_eq]
    omega
  have hzev := walkLog_ev_sep hInv
  -- the frame grown by the new event byte
  have hframeEv : UnchangedOutside m0
      (writeBytes s.mem (G.ev + C.evlen) (natToBytes b.toNat 1))
      (walkWide G ({ C with
        block := "cleanup478.i", evlen := C.evlen + 1,
        events := C.events ++ [EventRecord.tag b.toNat] })) := by
    refine UnchangedOutside.write_grow hInv.frame
      (walkWide_grow (show C.alen ≤ C.alen from Nat.le_refl _)
        (show C.evlen ≤ C.evlen + 1 from by omega) rfl) ?_
    exact ⟨(G.ev, C.evlen + 1), by simp [walkWide, walkPresent], by omega,
      by rw [htaglen]; omega⟩
  refine ⟨s', ⟨hInv, hstep, ?_, ?_⟩⟩
  · refine
      { pc_eq := rfl
        blockIndex := ?_
        k_le := hInv.k_le
        events_le := ?_
        evlen_eq := ?_
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
        ptrs := ?_
        log_hash := ?_
        log_len := ?_
        log_cap := ?_
        log_alen := ?_
        log_acap := ?_
        owned := walkStaged_write rfl (walkStaged_write rfl hInv.owned)
        frame := ?_
        blockLocal := ?_ }
    · rw [henv']
      dsimp only [out]
      exact walkLookup_cells_ne s.env "%k.0.i249" hInv.blockIndex cs
        (fun c hc => (hne c.1 (hmem c hc)).1)
    · simp only [List.length_append, List.length_cons, List.length_nil]
      omega
    · rw [hInv.evlen_eq]
      simp only [List.map_append, List.sum_append, EventRecord.encodedSize_tag,
        List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
      omega
    · -- evBytes
      have hflat : ((C.events ++ [EventRecord.tag b.toNat]).map
          EventRecord.encodedBytes).flatten =
          (C.events.map EventRecord.encodedBytes).flatten ++ [UInt8.ofNat b.toNat] := by
        rw [List.map_append, List.flatten_append]
        simp [EventRecord.encodedBytes]
      rw [hmem']
      dsimp only [m']
      rw [hflat, htag]
      simp only [List.length_append, List.length_cons, List.length_nil]
      have haddr : G.ev + C.evlen = G.ev + G.nev0 +
          (C.events.map EventRecord.encodedBytes).flatten.length := by
        rw [hInv.evlen_eq, hEvLen]; omega
      rw [walkReadBytes_ev_of_log_write (z := C.stage.z) (ev := G.ev) (evcap := G.evcap)
        (nev0 := G.nev0) (N := (C.events.map EventRecord.encodedBytes).flatten.length + 1)
        (off := 8) (v := wordBytes 8 (C.evlen + 1)) hzev
        (by simp only [wordBytes, natToBytes_length]; decide) hN]
      rw [haddr]
      exact walkReadBytes_writeByte_append (a := G.ev + G.nev0)
        (N := (C.events.map EventRecord.encodedBytes).flatten.length)
        (flat := (C.events.map EventRecord.encodedBytes).flatten) hInv.evBytes
        (UInt8.ofNat b.toNat)
    · rw [henv']
      dsimp only [out]
      exact walkLookup_cells_ne s.env "%sp.i.0248" hInv.depth_reg cs
        (fun c hc => (hne c.1 (hmem c hc)).2.1)
    · rw [henv']
      dsimp only [out]
      exact hInv.ptrs.cells_of cs
        (fun c hc => ⟨(hne c.1 (hmem c hc)).2.2.1, (hne c.1 (hmem c hc)).2.2.2.1,
          (hne c.1 (hmem c hc)).2.2.2.2.1, (hne c.1 (hmem c hc)).2.2.2.2.2.1,
          (hne c.1 (hmem c hc)).2.2.2.2.2.2.1, (hne c.1 (hmem c hc)).2.2.2.2.2.2.2⟩)
    · rw [hmem']
      dsimp only [m']
      rw [walkReadBytes_writeBytes_outside (start := C.stage.z + 8) (addr := C.stage.z + 32)
        (n := 4) (v := wordBytes 8 (C.evlen + 1)) (by simp only [wordBytes, natToBytes_length]; omega)]
      rw [walkReadBytes_writeBytes_outside (start := G.ev + C.evlen) (addr := C.stage.z + 32)
        (n := 4) ?_]
      · exact hInv.log_hash
      · rcases hzev with h | h
        · left; simp only [stage2LogExtent] at *; omega
        · right; rw [htaglen]; omega
    · rw [hmem']
      dsimp only [m']
      have hself : readBytes (writeBytes (writeBytes s.mem (G.ev + C.evlen) (natToBytes b.toNat 1))
          (C.stage.z + 8) (wordBytes 8 (C.evlen + 1))) (C.stage.z + 8) 8 =
          some (wordBytes 8 (C.evlen + 1)) := readBytes_writeBytes_same _ _
      rw [hself]
    · rw [hmem']
      dsimp only [m']
      rw [walkReadBytes_writeBytes_outside (start := C.stage.z + 8) (addr := C.stage.z + 16)
        (n := 8) (v := wordBytes 8 (C.evlen + 1)) (by simp only [wordBytes, natToBytes_length]; omega)]
      rw [walkReadBytes_writeBytes_outside (start := G.ev + C.evlen) (addr := C.stage.z + 16)
        (n := 8) ?_]
      · exact hInv.log_cap
      · rcases hzev with h | h
        · left; simp only [stage2LogExtent] at *; omega
        · right; rw [htaglen]; omega
    · rw [hmem']
      dsimp only [m']
      rw [walkReadBytes_writeBytes_outside (start := C.stage.z + 8) (addr := C.stage.z + 48)
        (n := 8) (v := wordBytes 8 (C.evlen + 1)) (by simp only [wordBytes, natToBytes_length]; omega)]
      rw [walkReadBytes_writeBytes_outside (start := G.ev + C.evlen) (addr := C.stage.z + 48)
        (n := 8) ?_]
      · exact hInv.log_alen
      · rcases hzev with h | h
        · left; simp only [stage2LogExtent] at *; omega
        · right; rw [htaglen]; omega
    · rw [hmem']
      dsimp only [m']
      rw [walkReadBytes_writeBytes_outside (start := C.stage.z + 8) (addr := C.stage.z + 56)
        (n := 8) (v := wordBytes 8 (C.evlen + 1)) (by simp only [wordBytes, natToBytes_length]; omega)]
      rw [walkReadBytes_writeBytes_outside (start := G.ev + C.evlen) (addr := C.stage.z + 56)
        (n := 8) ?_]
      · exact hInv.log_acap
      · rcases hzev with h | h
        · left; simp only [stage2LogExtent] at *; omega
        · right; rw [htaglen]; omega
    · rw [hmem']
      dsimp only [m']
      refine walkFrame_write_inside hframeEv ?_
      intro k hk
      rw [show (wordBytes 8 (C.evlen + 1)).length = 8 from natToBytes_length _ _] at hk
      exact walkWide_of_seven
        ⟨(C.stage.z, stage2LogExtent), by simp [stage2StagedWrites], by omega,
          by simp only [stage2LogExtent]; omega⟩
    · simp [WalkLocal]
  · rfl

/-- `out_reserve.exit.i.i`: the first key/string record's tag and length. -/
def walkOut_reserve_exit_i_i : Block :=
  { name := "out_reserve.exit.i.i",
    instrs := [
      Instr.load "%13" Ty.ptr (.reg "%z"),
      Instr.gep "%add.ptr.i.i" (.int 8) (.reg "%13") (.reg "%o.val.i.i"),
      Instr.store (.int 8) (.reg "%conv42.i") (.reg "%add.ptr.i.i"),
      Instr.store (.int 64) (.reg "%add.i.i.i") (.reg "%len")],
    term := Term.br "cleanup478.i" }

theorem walkOut_reserve_exit_i_i_find :
    stage2Body.findBlock "out_reserve.exit.i.i" = some walkOut_reserve_exit_i_i := by
  simp [stage2Body, Function.findBlock, findBlockList, walkOut_reserve_exit_i_i]

theorem WalkLink.out_reserve_exit_i_i {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "out_reserve.exit.i.i")
    {b : BitVec 8}
    (hz : lookupName s.env "%z" = some (.ptr C.stage.z))
    (hload : readBytes s.mem C.stage.z 8 = some (wordBytes 8 G.ev))
    (hev64 : G.ev < 2 ^ 64)
    (hs : lookupName s.env "%conv42.i" = some (.int 8 b))
    (ho : lookupName s.env "%o.val.i.i" = some (.int 64 (BitVec.ofNat 64 C.evlen)))
    (hst : lookupName s.env "%add.i.i.i" = some (.int 64 (BitVec.ofNat 64 (C.evlen + 1))))
    (hlen : lookupName s.env "%len" = some (.ptr (C.stage.z + 8)))
    (hev63 : C.evlen < 2 ^ 63) (hev64len : C.evlen + 1 < 2 ^ 64)
    (hlt : C.events.length < C.k) :
    ∃ s', WalkLink calls G C s
      { C with block := "cleanup478.i", evlen := C.evlen + 1, events := C.events ++ [EventRecord.tag b.toNat] } s' := by
  exact WalkLink.outReserveStore G C s hInv
    (by rw [hblock]; exact walkOut_reserve_exit_i_i_find) rfl rfl hz hload hev64 hs ho hst hlen
    hev63 hev64len hlt (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)
    (by intro n hn
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
        rcases hn with rfl | rfl <;>
          exact ⟨by decide, by decide, by decide, by decide, by decide, by decide,
            by decide, by decide⟩)

/-- `out_reserve.exit.i.i60`: the second key/string record's tag and length. -/
def walkOut_reserve_exit_i_i60 : Block :=
  { name := "out_reserve.exit.i.i60",
    instrs := [
      Instr.load "%20" Ty.ptr (.reg "%z"),
      Instr.gep "%add.ptr.i.i61" (.int 8) (.reg "%20") (.reg "%o.val.i.i56"),
      Instr.store (.int 8) (.reg "%conv115.i") (.reg "%add.ptr.i.i61"),
      Instr.store (.int 64) (.reg "%add.i.i.i58") (.reg "%len")],
    term := Term.br "cleanup478.i" }

theorem walkOut_reserve_exit_i_i60_find :
    stage2Body.findBlock "out_reserve.exit.i.i60" = some walkOut_reserve_exit_i_i60 := by
  simp [stage2Body, Function.findBlock, findBlockList, walkOut_reserve_exit_i_i60]

theorem WalkLink.out_reserve_exit_i_i60 {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "out_reserve.exit.i.i60")
    {b : BitVec 8}
    (hz : lookupName s.env "%z" = some (.ptr C.stage.z))
    (hload : readBytes s.mem C.stage.z 8 = some (wordBytes 8 G.ev))
    (hev64 : G.ev < 2 ^ 64)
    (hs : lookupName s.env "%conv115.i" = some (.int 8 b))
    (ho : lookupName s.env "%o.val.i.i56" = some (.int 64 (BitVec.ofNat 64 C.evlen)))
    (hst : lookupName s.env "%add.i.i.i58" = some (.int 64 (BitVec.ofNat 64 (C.evlen + 1))))
    (hlen : lookupName s.env "%len" = some (.ptr (C.stage.z + 8)))
    (hev63 : C.evlen < 2 ^ 63) (hev64len : C.evlen + 1 < 2 ^ 64)
    (hlt : C.events.length < C.k) :
    ∃ s', WalkLink calls G C s
      { C with block := "cleanup478.i", evlen := C.evlen + 1, events := C.events ++ [EventRecord.tag b.toNat] } s' := by
  exact WalkLink.outReserveStore G C s hInv
    (by rw [hblock]; exact walkOut_reserve_exit_i_i60_find) rfl rfl hz hload hev64 hs ho hst hlen
    hev63 hev64len hlt (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)
    (by intro n hn
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
        rcases hn with rfl | rfl <;>
          exact ⟨by decide, by decide, by decide, by decide, by decide, by decide,
            by decide, by decide⟩)


/-! ## The arena-cursor store

`if.else285.i` loads the decoded length the callee left in `%outn.i`, adds it to
the log's arena cursor (`%z.val36`, the word at `%z + 48`), and writes the sum
back.  This is the one class-D shape that advances the arena carry: `alen` becomes
`a + l` and the decoded extent is appended to `spans`.  The frame grows
with the cursor (`walkWide_grow`), its new bytes present because the arena was
staged whole; the four span facts the new extent owes are the caller's, as the
brief records.  The record in flight is *closed* here: `if.end256.i` set it to the
entry's position and extent when it made the reservation, and this block is where
the window it reserved has been decoded, so the carry leaves with `pending` empty
and the next entry's record enters at the next check.

The log's recorded cursor is re-read from the write itself, so `log_alen` needs no
side condition beyond the store; the record's own `alen` is related to the loaded
word by `hca` (`C.alen ≤ a`), which the body gets from `if.end256.i`'s load of
`%alen` — a data-flow fact the invariant does not carry.

**This is the pre-reservation statement.**  The link below moves `alen` to `a + l`,
which lets the cursor lag the write's own word; `WalkLink.z_arena_reserve_exit`
instead reserves the token's whole extent at the cursor when the callee is called
(`alen + ext`, the window appended to `spans` at the cursor, `pending` cleared
there), so the two statements do not compose: after the reservation the block
writes the word back *below* the carried cursor, and the restated link — the store
alone, with `alen` and `spans` left where the reservation put them — is what a
traversal after the exit composes.  That restatement is owed, not implied by the
statement below, and `hca` is where the difference shows: the reservation makes
`C.alen ≤ a` false in general. -/

/-- `if.else285.i`: the arena cursor advances by the decoded length. -/
def walkIf_else285_i : Block :=
  { name := "if.else285.i",
    instrs := [
      Instr.load "%32" (.int 64) (.reg "%outn.i"),
      Instr.binop "%add289.i" .add 64 (.reg "%z.val36") (.reg "%32"),
      Instr.store (.int 64) (.reg "%add289.i") (.reg "%alen")],
    term := Term.br "if.end290.i" }

theorem walkIf_else285_i_find :
    stage2Body.findBlock "if.else285.i" = some walkIf_else285_i := by
  simp [stage2Body, Function.findBlock, findBlockList, walkIf_else285_i]

theorem WalkLink.if_else285_i {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "if.else285.i")
    {l a ao : Nat}
    (houtn : lookupName s.env "%outn.i" = some (.ptr ao))
    (hread : readBytes s.mem ao 8 = some (wordBytes 8 l)) (hl64 : l < 2 ^ 64)
    (hz36 : lookupName s.env "%z.val36" = some (.int 64 (BitVec.ofNat 64 a)))
    (halen : lookupName s.env "%alen" = some (.ptr (C.stage.z + 48)))
    (hal64 : a + l < 2 ^ 64)
    (hca : C.alen ≤ a)
    (hge : G.ndst0 ≤ a)
    (hsum : a ≤ G.ndst0 + (C.spans.map (fun r => r.2)).sum)
    (hspan : ∀ r ∈ C.spans, r.1 + r.2 ≤ a)
    (hinside : a + l ≤ G.n) :
    ∃ s', WalkLink calls G C s
      { C with block := "if.end290.i", alen := a + l, spans := C.spans ++ [(a, l)], pending := none } s' := by
  have hpc : s.pc = C.block := hInv.pc_eq
  let cs : List (String × Value) := [
    ("%add289.i", .int 64 (BitVec.ofNat 64 (a + l))),
    ("%32", .int 64 (BitVec.ofNat 64 l))]
  let out : Env := cells cs s.env
  let m' : Mem := writeBytes s.mem (C.stage.z + 48) (wordBytes 8 (a + l))
  let s' : State := { stateAt out { s with mem := m' } with pc := "if.end290.i", pre := some s.pc }
  have henv' : s'.env = out := rfl
  have hmem' : s'.mem = m' := rfl
  have hread' : readBytes s.mem ao 8 = some (natToBytes (BitVec.ofNat 64 l).toNat 8) := by
    rw [walkToNat_ofNat64 hl64]; exact hread
  have hmlen : (wordBytes 8 (a + l)).length = 8 := natToBytes_length _ _
  have hden : denoteCode calls walkIf_else285_i.instrs s = some (stateAt out { s with mem := m' }) := by
    dsimp only [walkIf_else285_i]
    rw [← stateAt_self s]
    dsimp only [out, m', cs]
    rw [denoteCode_load64 calls s.env s "%32" "%outn.i" (v := BitVec.ofNat 64 l) houtn hread'
      [Instr.binop "%add289.i" .add 64 (.reg "%z.val36") (.reg "%32"),
       Instr.store (.int 64) (.reg "%add289.i") (.reg "%alen")]]
    rw [denoteCode_add_reg calls _ s "%add289.i" "%z.val36" "%32"
      (by rw [lookupName_cons_ne _ _ (by decide)]; exact hz36)
      (by rw [lookupName_cons_self])
      [Instr.store (.int 64) (.reg "%add289.i") (.reg "%alen")]]
    rw [← BitVec.ofNat_add]
    rw [denoteCode_store64_ofNat calls _ s "%add289.i" "%alen"
      (by rw [lookupName_cons_self]) hal64
      (by rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide)]; exact halen) []]
    dsimp only [cs, cells]
    rfl
  have hfind : stage2Body.findBlock C.block = some walkIf_else285_i := by
    rw [hblock]; exact walkIf_else285_i_find
  have htermN : walkIf_else285_i.term = Term.br "if.end290.i" := rfl
  have hstep : LeanLLVM.step calls stage2Body s = Ctrl.jump s' := by
    simp only [LeanLLVM.step, hpc, hfind, hden, htermN, execTerm]
    dsimp only [s', stateAt, out]
    rw [hpc]
  have hN : G.nev0 + (C.events.map EventRecord.encodedBytes).flatten.length ≤ G.evcap := by
    have hsum' := EventRecord.sum_encodedSize_le C.events
    simp only [stage2RecordBytes] at hsum'
    have hroom := G.evRoom
    simp only [stage2RecordBytes] at hroom
    have hlen : (C.events.map EventRecord.encodedBytes).flatten.length =
        (C.events.map EventRecord.encodedSize).sum := by
      simp only [List.length_flatten, List.map_map]; rfl
    have h1 := hInv.events_le; have h2 := hInv.k_le; have h3 := G.nep_le
    rw [hlen]; omega
  have hzev := walkLog_ev_sep hInv
  -- the frame widened with the arena cursor the store advances
  have hframeA : UnchangedOutside m0 s.mem (walkWide G
      ({ C with
        block := "if.end290.i", alen := a + l, spans := C.spans ++ [(a, l)] })) :=
    UnchangedOutside.of_covered hInv.frame
      (walkWide_grow (show C.alen ≤ a + l from by omega)
        (show C.evlen ≤ C.evlen from Nat.le_refl _) rfl)
  refine ⟨s', ⟨hInv, hstep, ?_, ?_⟩⟩
  · refine
      { pc_eq := rfl
        blockIndex := ?_
        k_le := hInv.k_le
        events_le := hInv.events_le
        evlen_eq := hInv.evlen_eq
        evBytes := ?_
        alen_le_sum := ?_
        alen_ge := ?_
        spans_order := ?_
        spans_end := ?_
        spans_inside := ?_
        pending_at := ?_
        pending_cursor := ?_
        pending_len := ?_
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
        owned := walkStaged_write rfl hInv.owned
        frame := ?_
        blockLocal := ?_ }
    · rw [henv']
      dsimp only [out]
      exact walkLookup_cells_ne s.env "%k.0.i249" hInv.blockIndex cs
        (by intro c hc
            simp only [cs, List.mem_cons, List.not_mem_nil, or_false] at hc
            rcases hc with rfl | rfl <;> simp)
    · rw [hmem']
      dsimp only [m']
      rw [walkReadBytes_ev_of_log_write (z := C.stage.z) (ev := G.ev) (evcap := G.evcap)
        (nev0 := G.nev0) (N := _) (off := 48) (v := wordBytes 8 (a + l)) hzev
        (by rw [hmlen]; decide) hN]
      exact hInv.evBytes
    · dsimp only
      rw [List.map_append, List.sum_append]
      simp only [List.map_singleton, List.sum_singleton]
      omega
    · dsimp only
      omega
    · dsimp only
      rw [List.pairwise_append]
      refine ⟨hInv.spans_order, ?_, ?_⟩
      · exact List.Pairwise.cons (by intro b hb; exact absurd hb (by simp)) List.Pairwise.nil
      · intro r hr s' hs'
        simp only [List.mem_singleton] at hs'
        subst hs'
        exact hspan r hr
    · dsimp only
      intro r hr
      rcases List.mem_append.mp hr with hr | hr
      · exact hInv.spans_inside r hr
      · simp only [List.mem_singleton] at hr
        subst hr
        exact hinside
    · dsimp only
      intro r hr
      rcases List.mem_append.mp hr with hr | hr
      · exact Nat.le_trans (hInv.spans_end r hr) (by omega)
      · simp only [List.mem_singleton] at hr
        subst hr
        omega
    · dsimp only
      intro p off len hp
      simp at hp
    · dsimp only
      intro p off len hp
      simp at hp
    · dsimp only
      intro p off len hp
      simp at hp
    · rw [henv']
      dsimp only [out]
      exact walkLookup_cells_ne s.env "%sp.i.0248" hInv.depth_reg cs
        (by intro c hc
            simp only [cs, List.mem_cons, List.not_mem_nil, or_false] at hc
            rcases hc with rfl | rfl <;> simp)
    · rw [henv']
      dsimp only [out]
      exact hInv.ptrs.cells_of cs
        (by intro c hc
            simp only [cs, List.mem_cons, List.not_mem_nil, or_false] at hc
            rcases hc with rfl | rfl <;>
              exact ⟨by simp, by simp, by simp, by simp, by simp, by simp⟩)
    · rw [hmem']
      dsimp only [m']
      rw [walkReadBytes_log_of_log_write (z := C.stage.z) (off := 48)
        (off' := 32) (N := 4) (v := wordBytes 8 (a + l)) (by rw [hmlen]; omega)]
      exact hInv.log_hash
    · rw [hmem']
      dsimp only [m']
      rw [walkReadBytes_log_of_log_write (z := C.stage.z) (off := 48)
        (off' := 8) (N := 8) (v := wordBytes 8 (a + l)) (by rw [hmlen]; omega)]
      exact hInv.log_len
    · rw [hmem']
      dsimp only [m']
      rw [walkReadBytes_log_of_log_write (z := C.stage.z) (off := 48)
        (off' := 16) (N := 8) (v := wordBytes 8 (a + l)) (by rw [hmlen]; omega)]
      exact hInv.log_cap
    · refine ⟨a + l, Nat.le_refl _, ?_⟩
      rw [hmem']
      dsimp only [m']
      exact readBytes_writeBytes_same _ _
    · rw [hmem']
      dsimp only [m']
      rw [walkReadBytes_log_of_log_write (z := C.stage.z) (off := 48)
        (off' := 56) (N := 8) (v := wordBytes 8 (a + l)) (by rw [hmlen]; omega)]
      exact hInv.log_acap
    · rw [hmem']
      dsimp only [m']
      refine walkFrame_write_inside hframeA ?_
      intro k hk
      rw [hmlen] at hk
      exact walkWide_of_seven
        ⟨(C.stage.z, stage2LogExtent), by simp [stage2StagedWrites], by omega,
          by simp only [stage2LogExtent]; omega⟩
    · simp [WalkLocal]
  · rfl

/-! ## The state-stack decrement

`if.then330.i` computes `%sp.i.0248 - 1`, zero-extends it, indexes the state
stack and writes `1`.  The emitted `sub` is `add i32 %sp, 4294967295`, so the
index is `C.sp - 1` at the `i32` wrap; `1 ≤ C.sp` is what makes it the
predecessor. -/

/-- `if.then330.i`: the state stack's byte at depth minus one is set to `1`. -/
def walkIf_then330_i : Block :=
  { name := "if.then330.i",
    instrs := [
      Instr.binop "%sub331.i" .add 32 (.reg "%sp.i.0248")
        (.imm (.int 32 (BitVec.ofNat 32 4294967295))),
      Instr.zext "%idxprom332.i" 32 64 (.reg "%sub331.i"),
      Instr.gep "%arrayidx333.i" (.int 8) (.reg "%cst.i") (.reg "%idxprom332.i"),
      Instr.store (.int 8) (.imm (.int 8 (BitVec.ofNat 8 1))) (.reg "%arrayidx333.i")],
    term := Term.br "cleanup478.i" }

theorem walkIf_then330_i_find :
    stage2Body.findBlock "if.then330.i" = some walkIf_then330_i := by
  simp [stage2Body, Function.findBlock, findBlockList, walkIf_then330_i]

theorem WalkLink.if_then330_i {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "if.then330.i") (hsp1 : 1 ≤ C.sp) :
    ∃ s', WalkLink calls G C s { C with block := "cleanup478.i" } s' := by
  have hpc : s.pc = C.block := hInv.pc_eq
  have hsp32 : C.sp < 2 ^ 32 := by
    have h := hInv.depth_cap
    simp only [stage2StackExtent] at h
    omega
  have hpred32 : C.sp - 1 < 2 ^ 32 := by omega
  have hpred63 : C.sp - 1 < 2 ^ 63 := by omega
  have hpred_ext : C.sp - 1 < stage2StackExtent := by
    have h := hInv.depth_cap
    simp only [stage2StackExtent] at h ⊢
    omega
  let cs : List (String × Value) := [
    ("%arrayidx333.i", .ptr (C.stage.cst + (C.sp - 1))),
    ("%idxprom332.i", .int 64 (BitVec.ofNat 64 (C.sp - 1))),
    ("%sub331.i", .int 32 (BitVec.ofNat 32 (C.sp - 1)))]
  let out : Env := cells cs s.env
  let m' : Mem := writeBytes s.mem (C.stage.cst + (C.sp - 1))
    (natToBytes (BitVec.ofNat 8 1).toNat 1)
  let s' : State := { stateAt out { s with mem := m' } with pc := "cleanup478.i", pre := some s.pc }
  have henv' : s'.env = out := rfl
  have hmem' : s'.mem = m' := rfl
  have hlen : (natToBytes 1 1).length = 1 := natToBytes_length _ _
  have hv1 : (natToBytes (BitVec.ofNat 8 1).toNat 1).length ≤ 1 := by
    simp [natToBytes_length]
  have hden : denoteCode calls walkIf_then330_i.instrs s = some (stateAt out { s with mem := m' }) := by
    dsimp only [walkIf_then330_i]
    rw [← stateAt_self s]
    dsimp only [out, m', cs]
    rw [walkDenoteCode_add_imm_w calls s.env s "%sub331.i" "%sp.i.0248" 32
      (c := BitVec.ofNat 32 4294967295) hInv.depth_reg
      [Instr.zext "%idxprom332.i" 32 64 (.reg "%sub331.i"),
       Instr.gep "%arrayidx333.i" (.int 8) (.reg "%cst.i") (.reg "%idxprom332.i"),
       Instr.store (.int 8) (.imm (.int 8 (BitVec.ofNat 8 1))) (.reg "%arrayidx333.i")]]
    rw [walkOfNat32_add_pred hsp1 hsp32]
    rw [denoteCode_zext32_64_ofNat calls _ s "%idxprom332.i" "%sub331.i"
      (by rw [lookupName_cons_self]) hpred32
      [Instr.gep "%arrayidx333.i" (.int 8) (.reg "%cst.i") (.reg "%idxprom332.i"),
       Instr.store (.int 8) (.imm (.int 8 (BitVec.ofNat 8 1))) (.reg "%arrayidx333.i")]]
    rw [denoteCode_gep8_ofNat calls _ s "%arrayidx333.i" "%cst.i" "%idxprom332.i"
      (by rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide)]; exact hInv.ptrs.2.2.2.2.1)
      (by rw [lookupName_cons_self]) hpred63
      [Instr.store (.int 8) (.imm (.int 8 (BitVec.ofNat 8 1))) (.reg "%arrayidx333.i")]]
    rw [denoteCode_store8_imm calls _ s (BitVec.ofNat 8 1) "%arrayidx333.i"
      (by rw [lookupName_cons_self]) []]
    dsimp only [cs, cells]
    rfl
  have hfind : stage2Body.findBlock C.block = some walkIf_then330_i := by
    rw [hblock]; exact walkIf_then330_i_find
  have htermN : walkIf_then330_i.term = Term.br "cleanup478.i" := rfl
  have hstep : LeanLLVM.step calls stage2Body s = Ctrl.jump s' := by
    simp only [LeanLLVM.step, hpc, hfind, hden, htermN, execTerm]
    dsimp only [s', stateAt, out]
    rw [hpc]
  have hN : G.nev0 + (C.events.map EventRecord.encodedBytes).flatten.length ≤ G.evcap := by
    have hsum := EventRecord.sum_encodedSize_le C.events
    simp only [stage2RecordBytes] at hsum
    have hroom := G.evRoom
    simp only [stage2RecordBytes] at hroom
    have hlen' : (C.events.map EventRecord.encodedBytes).flatten.length =
        (C.events.map EventRecord.encodedSize).sum := by
      simp only [List.length_flatten, List.map_map]; rfl
    have h1 := hInv.events_le; have h2 := hInv.k_le; have h3 := G.nep_le
    rw [hlen']; omega
  have hsz := cst_log_sep hInv
  have hsev := cst_ev_sep hInv
  refine ⟨s', ⟨hInv, hstep, ?_, ?_⟩⟩
  · refine
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
        ptrs := ?_
        log_hash := ?_
        log_len := ?_
        log_cap := ?_
        log_alen := ?_
        log_acap := ?_
        owned := walkStaged_write rfl hInv.owned
        frame := ?_
        blockLocal := ?_ }
    · rw [henv']
      dsimp only [out]
      exact walkLookup_cells_ne s.env "%k.0.i249" hInv.blockIndex cs
        (by intro c hc
            simp only [cs, List.mem_cons, List.not_mem_nil, or_false] at hc
            rcases hc with rfl | rfl | rfl <;> simp)
    · rw [hmem']
      dsimp only [m']
      rw [readBytes_ev_of_stack_write (base := C.stage.cst)
        (v := natToBytes (BitVec.ofNat 8 1).toNat 1) hsev
        (sp := C.sp - 1) hpred_ext (by simp [natToBytes]) (ev := G.ev) (evcap := G.evcap)
        (nev0 := G.nev0) (N := _) hN]
      exact hInv.evBytes
    · rw [henv']
      dsimp only [out]
      exact walkLookup_cells_ne s.env "%sp.i.0248" hInv.depth_reg cs
        (by intro c hc
            simp only [cs, List.mem_cons, List.not_mem_nil, or_false] at hc
            rcases hc with rfl | rfl | rfl <;> simp)
    · rw [henv']
      dsimp only [out]
      exact hInv.ptrs.cells_of cs
        (by intro c hc
            simp only [cs, List.mem_cons, List.not_mem_nil, or_false] at hc
            rcases hc with rfl | rfl | rfl <;>
              exact ⟨by simp, by simp, by simp, by simp, by simp, by simp⟩)
    · rw [hmem']
      dsimp only [m']
      rw [readBytes_log_of_stack_write (base := C.stage.cst)
        (v := natToBytes (BitVec.ofNat 8 1).toNat 1) hsz
        (sp := C.sp - 1) hpred_ext (by simp [natToBytes]) (off := 32) (len := 4) (by decide)]
      exact hInv.log_hash
    · rw [hmem']
      dsimp only [m']
      rw [readBytes_log_of_stack_write (base := C.stage.cst)
        (v := natToBytes (BitVec.ofNat 8 1).toNat 1) hsz
        (sp := C.sp - 1) hpred_ext (by simp [natToBytes]) (off := 8) (len := 8) (by decide)]
      exact hInv.log_len
    · rw [hmem']
      dsimp only [m']
      rw [readBytes_log_of_stack_write (base := C.stage.cst)
        (v := natToBytes (BitVec.ofNat 8 1).toNat 1) hsz
        (sp := C.sp - 1) hpred_ext (by simp [natToBytes]) (off := 16) (len := 8) (by decide)]
      exact hInv.log_cap
    · rw [hmem']
      dsimp only [m']
      rw [readBytes_log_of_stack_write (base := C.stage.cst)
        (v := natToBytes (BitVec.ofNat 8 1).toNat 1) hsz
        (sp := C.sp - 1) hpred_ext (by simp [natToBytes]) (off := 48) (len := 8) (by decide)]
      exact hInv.log_alen
    · rw [hmem']
      dsimp only [m']
      rw [readBytes_log_of_stack_write (base := C.stage.cst)
        (v := natToBytes (BitVec.ofNat 8 1).toNat 1) hsz
        (sp := C.sp - 1) hpred_ext (by simp [natToBytes]) (off := 56) (len := 8) (by decide)]
      exact hInv.log_acap
    · rw [hmem']
      dsimp only [m']
      refine walkFrame_write_inside hInv.frame ?_
      intro k hk
      have hk0 : k = 0 := by omega
      subst hk0
      refine walkWide_of_seven ?_
      refine ⟨(C.stage.cst, stage2StackExtent), by simp [stage2StagedWrites], by omega, ?_⟩
      simp only [stage2StackExtent] at hpred_ext ⊢
      omega
    · simp [WalkLocal]
  · rfl


/-! ## The two-entry advance

`if.end207.i` advances the entry cursor by two, writes it through `%k11.i`, loads
the next lane's entry position, and branches on the bound test.  The carry's `k`
does not move here — the header's leading `phi` is what advances it — so the link
is block-only, and the store is the cursor record's own field, which is exactly
the address `WalkPtrs` carries (`%c.i + 32`).  The tested registers `%inc.i` and
`%4` are the header's increment and the entry count, both produced before the
block and not in the invariant; the entry lane's read is the staging's. -/

/-- `if.end207.i`: the two-entry advance and the bound test. -/
def walkIf_end207_i : Block :=
  { name := "if.end207.i",
    instrs := [
      Instr.binop "%inc208.i" .add 64 (.reg "%k.0.i249")
        (.imm (.int 64 (BitVec.ofNat 64 2))),
      Instr.gep "%arrayidx209.i" (.int 32) (.reg "%5") (.reg "%inc.i"),
      Instr.load "%25" (.int 32) (.reg "%arrayidx209.i"),
      Instr.store (.int 64) (.reg "%inc208.i") (.reg "%k11.i"),
      Instr.zext "%conv211.i" 32 64 (.reg "%25"),
      Instr.icmp "%cmp212.not.i" .ugt 64 (.reg "%4") (.reg "%conv211.i")],
    term := Term.condbr (.reg "%cmp212.not.i") "if.then219.i" "if.then214.i" }

theorem walkIf_end207_i_find :
    stage2Body.findBlock "if.end207.i" = some walkIf_end207_i := by
  simp [stage2Body, Function.findBlock, findBlockList, walkIf_end207_i]

theorem WalkLink.if_end207_i {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "if.end207.i")
    {x : BitVec 64} {q : Nat} {bs : List UInt8}
    (hkinc : C.k + 1 < 2 ^ 63)
    (hinc : lookupName s.env "%inc.i" = some (.int 64 (BitVec.ofNat 64 (C.k + 1))))
    (h4 : lookupName s.env "%4" = some (.int 64 x))
    (hread : readBytes s.mem (G.ep + (C.k + 1) * 4) 4 = some bs)
    (hbs : bytesToNat bs = q)
    (hk64 : C.k + 2 < 2 ^ 64) :
    ∃ s', WalkLink calls G C s
      { C with block := (if evalICmp .ugt x (BitVec.ofNat 64 q) = 1 then "if.then219.i" else "if.then214.i") } s' := by
  have hpc : s.pc = C.block := hInv.pc_eq
  have hq32 : q < 2 ^ 32 := by
    rw [← hbs]
    exact bytesToNat_lt_32 (walkReadBytes_length hread)
  obtain ⟨h3, h5, hk11, hct, hcs, hhash⟩ := hInv.ptrs
  let cs : List (String × Value) := [
    ("%cmp212.not.i", .int 1 (evalICmp .ugt x (BitVec.ofNat 64 q))),
    ("%conv211.i", .int 64 (BitVec.ofNat 64 q)),
    ("%25", .int 32 (BitVec.ofNat 32 q)),
    ("%arrayidx209.i", .ptr (G.ep + (C.k + 1) * 4)),
    ("%inc208.i", .int 64 (BitVec.ofNat 64 (C.k + 2)))]
  let out : Env := cells cs s.env
  let m' : Mem := writeBytes s.mem (C.stage.c + 32) (wordBytes 8 (C.k + 2))
  let bit : BitVec 1 := evalICmp .ugt x (BitVec.ofNat 64 q)
  let s' : State := { stateAt out { s with mem := m' } with pc := (if bit = 1 then "if.then219.i" else "if.then214.i"), pre := some s.pc }
  have henv' : s'.env = out := rfl
  have hmem' : s'.mem = m' := rfl
  have hden : denoteCode calls walkIf_end207_i.instrs s = some (stateAt out { s with mem := m' }) := by
    dsimp only [walkIf_end207_i]
    rw [← stateAt_self s]
    dsimp only [out, m', cs, bit]
    rw [walkDenoteCode_add_imm_w calls s.env s "%inc208.i" "%k.0.i249" 64
      (c := BitVec.ofNat 64 2) hInv.blockIndex
      [Instr.gep "%arrayidx209.i" (.int 32) (.reg "%5") (.reg "%inc.i"),
       Instr.load "%25" (.int 32) (.reg "%arrayidx209.i"),
       Instr.store (.int 64) (.reg "%inc208.i") (.reg "%k11.i"),
       Instr.zext "%conv211.i" 32 64 (.reg "%25"),
       Instr.icmp "%cmp212.not.i" .ugt 64 (.reg "%4") (.reg "%conv211.i")]]
    rw [← BitVec.ofNat_add]
    rw [denoteCode_gep32_ofNat calls _ s "%arrayidx209.i" "%5" "%inc.i"
      (by rw [lookupName_cons_ne _ _ (by decide)]; exact h5)
      (by rw [lookupName_cons_ne _ _ (by decide)]; exact hinc) hkinc
      [Instr.load "%25" (.int 32) (.reg "%arrayidx209.i"),
       Instr.store (.int 64) (.reg "%inc208.i") (.reg "%k11.i"),
       Instr.zext "%conv211.i" 32 64 (.reg "%25"),
       Instr.icmp "%cmp212.not.i" .ugt 64 (.reg "%4") (.reg "%conv211.i")]]
    rw [denoteCode_load32 calls _ s "%25" "%arrayidx209.i"
      (by rw [lookupName_cons_self]) hread hbs
      [Instr.store (.int 64) (.reg "%inc208.i") (.reg "%k11.i"),
       Instr.zext "%conv211.i" 32 64 (.reg "%25"),
       Instr.icmp "%cmp212.not.i" .ugt 64 (.reg "%4") (.reg "%conv211.i")]]
    rw [denoteCode_store64_ofNat calls _ s "%inc208.i" "%k11.i"
      (by rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
        lookupName_cons_self]) hk64
      (by rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
        lookupName_cons_ne _ _ (by decide)]; exact hk11)
      [Instr.zext "%conv211.i" 32 64 (.reg "%25"),
       Instr.icmp "%cmp212.not.i" .ugt 64 (.reg "%4") (.reg "%conv211.i")]]
    rw [denoteCode_zext32_64_ofNat calls
      (("%25", .int 32 (BitVec.ofNat 32 q)) ::
        ("%arrayidx209.i", .ptr (G.ep + (C.k + 1) * 4)) ::
          ("%inc208.i", .int 64 (BitVec.ofNat 64 (C.k + 2))) :: s.env)
      { s with mem := writeBytes s.mem (C.stage.c + 32) (wordBytes 8 (C.k + 2)) }
      "%conv211.i" "%25" (by rw [lookupName_cons_self]) hq32
      [Instr.icmp "%cmp212.not.i" .ugt 64 (.reg "%4") (.reg "%conv211.i")]]
    rw [walkDenoteCode_icmp
      (("%conv211.i", .int 64 (BitVec.ofNat 64 q)) ::
        ("%25", .int 32 (BitVec.ofNat 32 q)) ::
          ("%arrayidx209.i", .ptr (G.ep + (C.k + 1) * 4)) ::
            ("%inc208.i", .int 64 (BitVec.ofNat 64 (C.k + 2))) :: s.env)
      { s with mem := writeBytes s.mem (C.stage.c + 32) (wordBytes 8 (C.k + 2)) }
      "%cmp212.not.i" 64 .ugt
      (evalOperand_reg_of _ _ "%4" (.int 64 x)
        (by rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
          lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide)]; exact h4))
      (evalOperand_reg_of _ _ "%conv211.i" (.int 64 (BitVec.ofNat 64 q))
        (by rw [lookupName_cons_self])) []]
    dsimp only [cs, cells]
    rfl
  have hfind : stage2Body.findBlock C.block = some walkIf_end207_i := by
    rw [hblock]; exact walkIf_end207_i_find
  have htermN : walkIf_end207_i.term =
      Term.condbr (.reg "%cmp212.not.i") "if.then219.i" "if.then214.i" := rfl
  have hbit : lookupName out "%cmp212.not.i" = some (.int 1 bit) := by
    dsimp only [out, cs, cells, bit]
    rw [lookupName_cons_self]
  have hstep : LeanLLVM.step calls stage2Body s = Ctrl.jump s' := by
    simp only [LeanLLVM.step, hpc, hfind, hden, htermN]
    rw [walkExecTerm_condbr (d := "%cmp212.not.i") (tl := "if.then219.i")
      (fl := "if.then214.i") (bit := bit) hbit]
    dsimp only [s', stateAt, out, cs, cells, bit]
    rw [hpc]
  have hN : G.nev0 + (C.events.map EventRecord.encodedBytes).flatten.length ≤ G.evcap := by
    have hsum := EventRecord.sum_encodedSize_le C.events
    simp only [stage2RecordBytes] at hsum
    have hroom := G.evRoom
    simp only [stage2RecordBytes] at hroom
    have hlen : (C.events.map EventRecord.encodedBytes).flatten.length =
        (C.events.map EventRecord.encodedSize).sum := by
      simp only [List.length_flatten, List.map_map]; rfl
    have h1 := hInv.events_le; have h2 := hInv.k_le; have h3 := G.nep_le
    rw [hlen]; omega
  have hcz := cursor_log_sep hInv
  have hcev := walkCursor_ev_sep hInv
  have hwlen : (wordBytes 8 (C.k + 2)).length = 8 := natToBytes_length _ _
  refine ⟨s', ⟨hInv, hstep, ?_, ?_⟩⟩
  · refine
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
        ptrs := ?_
        log_hash := ?_
        log_len := ?_
        log_cap := ?_
        log_alen := ?_
        log_acap := ?_
        owned := walkStaged_write rfl hInv.owned
        frame := ?_
        blockLocal := ?_ }
    · rw [henv']
      dsimp only [out]
      exact walkLookup_cells_ne s.env "%k.0.i249" hInv.blockIndex cs
        (by intro c hc
            simp only [cs, List.mem_cons, List.not_mem_nil, or_false] at hc
            rcases hc with rfl | rfl | rfl | rfl | rfl <;> simp)
    · rw [hmem']
      dsimp only [m']
      rw [readBytes_ev_of_cursor_write (c := C.stage.c) (ev := G.ev) (nev0 := G.nev0)
        (evcap := G.evcap) (N := _) (v := wordBytes 8 (C.k + 2)) hcev
        (by rw [hwlen]) hN]
      exact hInv.evBytes
    · rw [henv']
      dsimp only [out]
      exact walkLookup_cells_ne s.env "%sp.i.0248" hInv.depth_reg cs
        (by intro c hc
            simp only [cs, List.mem_cons, List.not_mem_nil, or_false] at hc
            rcases hc with rfl | rfl | rfl | rfl | rfl <;> simp)
    · rw [henv']
      dsimp only [out]
      exact hInv.ptrs.cells_of cs
        (by intro c hc
            simp only [cs, List.mem_cons, List.not_mem_nil, or_false] at hc
            rcases hc with rfl | rfl | rfl | rfl | rfl <;>
              exact ⟨by simp, by simp, by simp, by simp, by simp, by simp⟩)
    · rw [hmem']
      dsimp only [m']
      rw [readBytes_log_of_cursor_write (c := C.stage.c) (z := C.stage.z) hcz
        (by rw [hwlen]) (off := 32) (len := 4) (by decide)]
      exact hInv.log_hash
    · rw [hmem']
      dsimp only [m']
      rw [readBytes_log_of_cursor_write (c := C.stage.c) (z := C.stage.z) hcz
        (by rw [hwlen]) (off := 8) (len := 8) (by decide)]
      exact hInv.log_len
    · rw [hmem']
      dsimp only [m']
      rw [readBytes_log_of_cursor_write (c := C.stage.c) (z := C.stage.z) hcz
        (by rw [hwlen]) (off := 16) (len := 8) (by decide)]
      exact hInv.log_cap
    · rw [hmem']
      dsimp only [m']
      rw [readBytes_log_of_cursor_write (c := C.stage.c) (z := C.stage.z) hcz
        (by rw [hwlen]) (off := 48) (len := 8) (by decide)]
      exact hInv.log_alen
    · rw [hmem']
      dsimp only [m']
      rw [readBytes_log_of_cursor_write (c := C.stage.c) (z := C.stage.z) hcz
        (by rw [hwlen]) (off := 56) (len := 8) (by decide)]
      exact hInv.log_acap
    · rw [hmem']
      dsimp only [m']
      exact hInv.frame_cursorK (v := wordBytes 8 (C.k + 2)) (by rw [hwlen])
    · simp only [WalkLocal]
      split <;> simp
  · rfl

end WalkScope
end LeanLLVM.Refinement
