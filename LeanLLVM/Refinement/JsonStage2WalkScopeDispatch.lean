import LeanLLVM.Refinement.JsonStage2WalkScopeStaged

set_option autoImplicit false

namespace LeanLLVM.Refinement
namespace WalkScope

open LeanLLVM
open LeanLLVM.Refinement.JsonStage2IR
open LeanLLVM.Refinement.BlockEval

/-! ## A: the append lemma for phi-free runs -/

theorem walkDenoteRun_append_of {calls : Calls} :
    ∀ (is : List Instr) (pend : List (String × Value)) (js : List Instr) (s : State),
      is.any Instr.isPhi = false → startsWithPhi js = false →
      denoteRun calls pend (is ++ js) s
        = (denoteRun calls pend is s).bind (denoteRun calls [] js)
  | [], pend, js, s, _, hjs => by
      simp only [List.nil_append, denoteRun, Option.bind_some]
      exact denoteRun_nil_pend hjs
  | i :: is, pend, js, s, h, hjs => by
      have hi : i.isPhi = false := by
        simpa using List.any_eq_false.mp h i (by simp)
      have htail : is.any Instr.isPhi = false := by
        rw [List.any_eq_false] at h ⊢
        exact fun j hj => h j (by simp [hj])
      rw [show (i :: is) ++ js = i :: (is ++ js) from rfl,
          denoteRun_cons_of (calls := calls) (pend := pend) hi,
          denoteRun_cons_of (calls := calls) (pend := pend) hi]
      cases evalInstr calls (s.bindAll pend) i with
      | none => rfl
      | some s' => exact walkDenoteRun_append_of is [] js s' htail hjs

theorem walkDenoteCode_append_some {calls : Calls} {is js : List Instr} {s s' : State}
    (his : is.any Instr.isPhi = false) (hjs : startsWithPhi js = false)
    (h : denoteCode calls is s = some s') :
    denoteCode calls (is ++ js) s = denoteCode calls js s' := by
  rw [denoteCode] at h ⊢
  rw [walkDenoteRun_append_of (calls := calls) is [] js s his hjs, h]
  rfl




/-! ## C: the nesting arm's block -/

theorem walkEvalICmp_eq_self {w : Nat} (a : BitVec w) : evalICmp .eq a a = 1 := by
  simp [evalICmp]

/-- A bind at a name the list does not carry leaves a lookup alone. -/
theorem walkLookup_cells_ne (env : Env) (n : String) {v : Value}
    (h : lookupName env n = some v) (cs : List (String × Value))
    (hne : ∀ c ∈ cs, c.1 ≠ n) : lookupName (cells cs env) n = some v := by
  induction cs with
  | nil => exact h
  | cons c rest ih =>
      simp only [cells, lookupName_cons_ne c.2 (cells rest env) (hne c (by simp))]
      exact ih (fun c' hc' => hne c' (by simp [hc']))

/-- The chain's first nine instructions. -/
def ifEnd24Head : List Instr := [
  Instr.icmp "%cmp26.i" IPred.eq 8 (.reg "%8") (.imm (.int 8 (BitVec.ofNat 8 123))),
  Instr.select "%conv28.i" (Ty.int 8) (.reg "%cmp26.i")
    (.imm (.int 8 (BitVec.ofNat 8 1))) (.imm (.int 8 (BitVec.ofNat 8 2))),
  Instr.zext "%idxprom29.i" 32 64 (.reg "%sp.i.0248"),
  Instr.gep "%arrayidx30.i" (Ty.int 8) (.reg "%ctype.i") (.reg "%idxprom29.i"),
  Instr.store (Ty.int 8) (.reg "%conv28.i") (.reg "%arrayidx30.i"),
  Instr.gep "%arrayidx32.i" (Ty.int 8) (.reg "%cst.i") (.reg "%idxprom29.i"),
  Instr.store (Ty.int 8) (.imm (.int 8 (BitVec.ofNat 8 0))) (.reg "%arrayidx32.i"),
  Instr.binop "%inc33.i" BinOp.add 32 (.reg "%sp.i.0248")
    (.imm (.int 32 (BitVec.ofNat 32 1))),
  Instr.select "%conv42.i" (Ty.int 8) (.reg "%cmp26.i")
    (.imm (.int 8 (BitVec.ofNat 8 1))) (.imm (.int 8 (BitVec.ofNat 8 3)))]

/-- The chain's last two instructions, written by hand. -/
def ifEnd24Tail : List Instr := [
  Instr.load "%10" (Ty.int 32) (.reg "%hash1.i.i"),
  Instr.icmp "%tobool.not.i.i" IPred.eq 32 (.reg "%10")
    (.imm (.int 32 (BitVec.ofNat 32 0)))]

def ifEnd24Instrs : List Instr := ifEnd24Head ++ ifEnd24Tail

theorem ifEnd24Instrs_split : ifEnd24Instrs = ifEnd24Head ++ ifEnd24Tail := rfl

def ifEnd24Block : Block :=
  { name := "if.end24.i", instrs := ifEnd24Instrs,
    term := Term.condbr (.reg "%tobool.not.i.i") "if.end.i.i" "if.then.i.i" }

theorem ifEnd24_find : stage2Body.findBlock "if.end24.i" = some ifEnd24Block := by
  simp [stage2Body, Function.findBlock, findBlockList, ifEnd24Block, ifEnd24Instrs,
    ifEnd24Head, ifEnd24Tail]

/-- `%cmp26.i`: the test the arm's two selects read. -/
def ifEnd24Test (b : BitVec 8) : BitVec 1 :=
  evalICmp .eq b (BitVec.ofNat 8 123)

/-- `%conv28.i`, the byte the type stack receives. -/
def ifEnd24Ty (b : BitVec 8) : BitVec 8 :=
  if ifEnd24Test b = 1 then 1 else 2

/-- `%conv42.i`, the byte the state stack receives. -/
def ifEnd24St (b : BitVec 8) : BitVec 8 :=
  if ifEnd24Test b = 1 then 1 else 3

/-! #### The two stack writes as one map update -/

/-- A one-byte `natToBytes` is the list of its own byte. -/
theorem walkNatToBytes_singleton (v : Nat) :
    natToBytes v 1 = [(natToBytes v 1).getD 0 0] := by
  have hlen := natToBytes_length v 1
  cases h : natToBytes v 1 with
  | nil => rw [h] at hlen; simp at hlen
  | cons y ys =>
      have hys : ys = [] := by
        rw [h] at hlen
        simpa using hlen
      subst hys
      rfl

/-- The byte `if.end24.i` pushes onto the type stack, as the store's own list
holds it. -/
def ifEnd24TyByte (b : BitVec 8) : UInt8 :=
  (natToBytes (ifEnd24Ty b).toNat 1).getD 0 0

/-- The byte `if.end24.i` pushes onto the state stack: zero. -/
def ifEnd24StByte : UInt8 := (natToBytes 0 1).getD 0 0

/-- The state stack's pushed byte is zero. -/
theorem ifEnd24StByte_zero : ifEnd24StByte = 0 := rfl

/-- **`if.end24.i`'s two stores, as one map update at an arbitrary depth.**  The
type stack receives `ifEnd24TyByte b` at `sp` and the state stack zero; each store
is outside the other stack's extent, so both maps advance to the written mark
`max wlen (sp + 1)`.  The mark rather than `sp + 1` is the sound depth: a push
after a pop stores at an index below the mark, which leaves the mark where it
was. -/
theorem walkStack_ifEnd24_at {mem : Mem} {ctype cst sp wlen : Nat} {TM SM : Nat → UInt8}
    {b : BitVec 8}
    (hT : WalkStackBytes mem ctype TM wlen) (hS : WalkStackBytes mem cst SM wlen)
    (hsep : cst + stage2StackExtent ≤ ctype ∨ ctype + stage2StackExtent ≤ cst)
    (hsp : sp ≤ wlen) (hcap : max wlen (sp + 1) ≤ stage2StackExtent) :
    WalkStackBytes
        (writeBytes (writeBytes mem (ctype + sp) (natToBytes (ifEnd24Ty b).toNat 1))
          (cst + sp) (natToBytes 0 1))
        ctype (fun i => if i = sp then ifEnd24TyByte b else TM i) (max wlen (sp + 1)) ∧
      WalkStackBytes
        (writeBytes (writeBytes mem (ctype + sp) (natToBytes (ifEnd24Ty b).toNat 1))
          (cst + sp) (natToBytes 0 1))
        cst (fun i => if i = sp then ifEnd24StByte else SM i) (max wlen (sp + 1)) := by
  have hTstep : WalkStackBytes (writeBytes mem (ctype + sp)
      (natToBytes (ifEnd24Ty b).toNat 1)) ctype
      (fun i => if i = sp then ifEnd24TyByte b else TM i) (max wlen (sp + 1)) :=
    hT.pushNatAt (v := (ifEnd24Ty b).toNat) hsp
  have hSstep : WalkStackBytes (writeBytes mem (cst + sp)
      (natToBytes 0 1)) cst
      (fun i => if i = sp then ifEnd24StByte else SM i) (max wlen (sp + 1)) :=
    hS.pushNatAt (v := 0) hsp
  refine ⟨hTstep.write_outside ?_, ?_⟩
  · rcases hsep with h | h
    · left
      simp only [natToBytes_length]
      omega
    · right
      omega
  · refine (hS.write_outside ?_).pushNatAt (i := sp) hsp
    rcases hsep with h | h
    · right
      omega
    · left
      simp only [natToBytes_length]
      omega

/-- **`s2_value_pos` reads the map at `sp - 1`.**  At a positive depth the helper
loads the two stacks' top bytes, and the agreement turns both into the carried
values: the map is what the helper's answer is a function of. -/
theorem walkStack_valuePos {m : Mem} {ct cs sp rd : Nat} {TM SM : Nat → UInt8}
    (hsp : sp ≠ 0) (hT : WalkStackBytes m ct TM sp) (hS : WalkStackBytes m cs SM sp) :
    stage2ValuePos m sp rd ct cs =
      some (if (TM (sp - 1)).toNat = 1 then
        (if (SM (sp - 1)).toNat = 2 then 1 else 0)
      else (if (SM (sp - 1)).toNat = 0 ∨ (SM (sp - 1)).toNat = 2 then 1 else 0)) := by
  have hlt : sp - 1 < sp := by omega
  simp only [stage2ValuePos, hsp, hT.at hlt, hS.at hlt]
  simp


/-- **`s2_value_pos`'s answer is the carried maps' function.**  At a positive
depth the helper reads the two stacks' tops, so the word it answers with is
determined by `tyMap` and `stMap` rather than by the caller's memory.  This is the
premise a stack-reading link needs; it is derived, not assumed. -/
theorem walkValuePos_answer {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {s : State}
    (h : WalkInv G C s) {sp rd : Nat} (hsp : sp ≠ 0) (hspw : sp ≤ C.wlen) :
    stage2ValuePos s.mem sp rd C.stage.ctype C.stage.cst =
      some (if (C.tyMap (sp - 1)).toNat = 1 then
        (if (C.stMap (sp - 1)).toNat = 2 then 1 else 0)
      else (if (C.stMap (sp - 1)).toNat = 0 ∨ (C.stMap (sp - 1)).toNat = 2 then 1 else 0)) :=
  walkStack_valuePos hsp (h.tyBytes.restrict hspw) (h.stBytes.restrict hspw)

/-- The head's cells, newest first. -/
def ifEnd24HeadCells (sp ctype cst : Nat) (b : BitVec 8) : List (String × Value) :=
  [("%conv42.i", .int 8 (ifEnd24St b)),
   ("%inc33.i", .int 32 (BitVec.ofNat 32 (sp + 1))),
   ("%arrayidx32.i", .ptr (cst + sp)),
   ("%arrayidx30.i", .ptr (ctype + sp)),
   ("%idxprom29.i", .int 64 (BitVec.ofNat 64 sp)),
   ("%conv28.i", .int 8 (ifEnd24Ty b)),
   ("%cmp26.i", .int 1 (ifEnd24Test b))]

/-- The tail's cells, newest first. -/
def ifEnd24TailCells : List (String × Value) :=
  [("%tobool.not.i.i", .int 1 (evalICmp .eq (BitVec.ofNat 32 0) (BitVec.ofNat 32 0))),
   ("%10", .int 32 (BitVec.ofNat 32 0))]

def ifEnd24Mid (env : Env) (sp ctype cst : Nat) (b : BitVec 8) : Env :=
  cells (ifEnd24HeadCells sp ctype cst b) env

def ifEnd24Out (env : Env) (sp ctype cst : Nat) (b : BitVec 8) : Env :=
  cells ifEnd24TailCells (ifEnd24Mid env sp ctype cst b)

theorem ifEnd24Head_denote {calls : Calls} (env : Env) (s : State)
    {sp ctype cst : Nat} {b : BitVec 8}
    (h8 : lookupName env "%8" = some (.int 8 b))
    (hspv : lookupName env "%sp.i.0248" = some (.int 32 (BitVec.ofNat 32 sp)))
    (hct : lookupName env "%ctype.i" = some (.ptr ctype))
    (hcs : lookupName env "%cst.i" = some (.ptr cst))
    (hsp32 : sp < 2 ^ 32) :
    denoteCode calls ifEnd24Head (stateAt env s) =
      some (stateAt (ifEnd24Mid env sp ctype cst b)
        { s with mem := writeBytes (writeBytes s.mem (ctype + sp)
            (natToBytes (ifEnd24Ty b).toNat 1)) (cst + sp) (natToBytes 0 1) }) := by
  simp only [ifEnd24Head, ifEnd24Mid, ifEnd24HeadCells]
  walk_eval

/-- The last two instructions, written by hand: the hash word's load and the
branch test it feeds. -/
theorem ifEnd24Tail_denote {calls : Calls} (env : Env) (s : State) {z : Nat}
    (hhash : lookupName env "%hash1.i.i" = some (.ptr (z + 32)))
    (hread : readBytes s.mem (z + 32) 4 = some (natToBytes 0 4)) :
    denoteCode calls ifEnd24Tail (stateAt env s) =
      some (stateAt (cells ifEnd24TailCells env) s) := by
  simp only [ifEnd24Tail, ifEnd24TailCells]
  rw [denoteCode_load32 calls env s "%10" "%hash1.i.i" hhash hread (q := 0) (by rfl) _]
  rw [denoteCode_icmp_eq_imm_w calls (("%10", .int 32 (BitVec.ofNat 32 0)) :: env) s
    "%tobool.not.i.i" "%10" 32 (x := BitVec.ofNat 32 0) (c := BitVec.ofNat 32 0)
    (by rfl) []]
  rfl

theorem ifEnd24_denote {calls : Calls} (env : Env) (s : State)
    {sp ctype cst z : Nat} {b : BitVec 8}
    (h8 : lookupName env "%8" = some (.int 8 b))
    (hspv : lookupName env "%sp.i.0248" = some (.int 32 (BitVec.ofNat 32 sp)))
    (hct : lookupName env "%ctype.i" = some (.ptr ctype))
    (hcs : lookupName env "%cst.i" = some (.ptr cst))
    (hhash : lookupName env "%hash1.i.i" = some (.ptr (z + 32)))
    (hsp : sp < stage2StackExtent)
    (hcz : ctype + stage2StackExtent ≤ z ∨ z + stage2LogExtent ≤ ctype)
    (hsz : cst + stage2StackExtent ≤ z ∨ z + stage2LogExtent ≤ cst)
    (hread : readBytes s.mem (z + 32) 4 = some (natToBytes 0 4)) :
    denoteCode calls ifEnd24Instrs (stateAt env s) =
      some (stateAt (ifEnd24Out env sp ctype cst b)
        { s with mem := writeBytes (writeBytes s.mem (ctype + sp)
            (natToBytes (ifEnd24Ty b).toNat 1)) (cst + sp) (natToBytes 0 1) }) := by
  have hsp32 : sp < 2 ^ 32 := by
    have h520 : stage2StackExtent = 520 := rfl
    omega
  have hread' : readBytes (writeBytes (writeBytes s.mem (ctype + sp)
      (natToBytes (ifEnd24Ty b).toNat 1)) (cst + sp) (natToBytes 0 1))
      (z + 32) 4 = some (natToBytes 0 4) := by
    rw [readBytes_log_of_stack_write (base := cst) (v := natToBytes 0 1) hsz
      (sp := sp) hsp (by simp [natToBytes]) (off := 32) (len := 4) (by decide)]
    rw [readBytes_log_of_stack_write (base := ctype)
      (v := natToBytes (ifEnd24Ty b).toNat 1) hcz
      (sp := sp) hsp (by simp [natToBytes]) (off := 32) (len := 4) (by decide)]
    exact hread
  rw [ifEnd24Instrs_split]
  rw [walkDenoteCode_append_some (calls := calls) (is := ifEnd24Head) (js := ifEnd24Tail)
    (s := stateAt env s)
    (s' := stateAt (ifEnd24Mid env sp ctype cst b)
      { s with mem := writeBytes (writeBytes s.mem (ctype + sp)
          (natToBytes (ifEnd24Ty b).toNat 1)) (cst + sp) (natToBytes 0 1) })
    (by decide) (by decide)
    (ifEnd24Head_denote (calls := calls) env s h8 hspv hct hcs hsp32)]
  exact ifEnd24Tail_denote (calls := calls) (ifEnd24Mid env sp ctype cst b) _ hhash hread'




/-! ### The event stream and the two stacks' separation -/

theorem ctype_ev_sep {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {s : State}
    (_h : WalkInv G C s) :
    C.stage.ctype + stage2StackExtent ≤ G.ev ∨ G.ev + G.evcap ≤ C.stage.ctype := by
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
  have h' := List.pairwise_iff_getElem.mp hpair 4 9 (by omega) (by omega) (by omega)
  simpa [stage2WalkRegions, stage2Regions, stage2StagedWrites] using h'.symm

theorem cst_ev_sep {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {s : State}
    (_h : WalkInv G C s) :
    C.stage.cst + stage2StackExtent ≤ G.ev ∨ G.ev + G.evcap ≤ C.stage.cst := by
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
  have h' := List.pairwise_iff_getElem.mp hpair 4 10 (by omega) (by omega) (by omega)
  simpa [stage2WalkRegions, stage2Regions, stage2StagedWrites] using h'.symm

theorem readBytes_ev_of_stack_write {m : Mem} {base ev evcap nev0 N : Nat}
    {v : List UInt8} {sp : Nat}
    (hbev : base + stage2StackExtent ≤ ev ∨ ev + evcap ≤ base)
    (hsp : sp < stage2StackExtent) (hv : v.length ≤ 1) (hN : nev0 + N ≤ evcap) :
    readBytes (writeBytes m (base + sp) v) (ev + nev0) N = readBytes m (ev + nev0) N := by
  refine walkReadBytes_writeBytes_outside (start := base + sp) ?_
  rcases hbev with hbev | hbev
  · right
    simp only [stage2StackExtent] at *
    omega
  · left
    omega

/-! ### The nesting arm's terminator -/

theorem ifEnd24Out_branch (s : State) {env : Env} {sp ctype cst : Nat} {b : BitVec 8} :
    evalOperand (stateAt (ifEnd24Out env sp ctype cst b) s) (.reg "%tobool.not.i.i")
      = some (.int 1 1) := by
  dsimp only [stateAt, evalOperand, ifEnd24Out, ifEnd24TailCells, cells]
  rw [lookupName_cons_self]
  simp [walkEvalICmp_eq_self]

theorem ifEnd24_term {calls : Calls} (s : State)
    {sp ctype cst z : Nat} {b : BitVec 8}
    (hpc : s.pc = "if.end24.i")
    (h8 : lookupName s.env "%8" = some (.int 8 b))
    (hspv : lookupName s.env "%sp.i.0248" = some (.int 32 (BitVec.ofNat 32 sp)))
    (hct : lookupName s.env "%ctype.i" = some (.ptr ctype))
    (hcs : lookupName s.env "%cst.i" = some (.ptr cst))
    (hhash : lookupName s.env "%hash1.i.i" = some (.ptr (z + 32)))
    (hsp : sp < stage2StackExtent)
    (hcz : ctype + stage2StackExtent ≤ z ∨ z + stage2LogExtent ≤ ctype)
    (hsz : cst + stage2StackExtent ≤ z ∨ z + stage2LogExtent ≤ cst)
    (hread : readBytes s.mem (z + 32) 4 = some (natToBytes 0 4)) :
    step calls stage2Body s =
      .jump { (stateAt (ifEnd24Out s.env sp ctype cst b)
          { s with mem := writeBytes (writeBytes s.mem (ctype + sp)
              (natToBytes (ifEnd24Ty b).toNat 1)) (cst + sp) (natToBytes 0 1) }) with
        pc := "if.end.i.i", pre := some "if.end24.i" } := by
  have hden := ifEnd24_denote (calls := calls) (env := s.env) (s := s)
    h8 hspv hct hcs hhash hsp hcz hsz hread
  simp only [step, hpc, ifEnd24_find, ifEnd24Block]
  rw [show denoteCode calls ifEnd24Instrs s =
      some (stateAt (ifEnd24Out s.env sp ctype cst b)
        { s with mem := writeBytes (writeBytes s.mem (ctype + sp)
            (natToBytes (ifEnd24Ty b).toNat 1)) (cst + sp) (natToBytes 0 1) }) from by
    rw [← stateAt_self s]; exact hden]
  dsimp only
  unfold execTerm
  dsimp only
  rw [ifEnd24Out_branch]
  simp [hpc, stateAt]




/-- **The nesting arm's step**: one control step from the invariant at
`if.end24.i` into `if.end.i.i`, the branch the log's zeroed hash word fixes, with
the two container stacks written at the carried depth, every clause preserved and
the measure unchanged (this block advances neither the entry index nor the inner
work). -/
theorem ifEnd24_step {calls : Calls} {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G)
    (s : State) (hInv : WalkInv G C s) (hblock : C.block = "if.end24.i")
    {b : BitVec 8} (h8 : lookupName s.env "%8" = some (.int 8 b))
    (hguard : NestGuard C.sp) :
    ∃ e : State,
      step calls stage2Body s = .jump e ∧
      WalkInv G { C with
        block := "if.end.i.i", wlen := max C.wlen (C.sp + 1),
        tyMap := fun i => if i = C.sp then ifEnd24TyByte b else C.tyMap i,
        stMap := fun i => if i = C.sp then ifEnd24StByte else C.stMap i } e ∧
      walkMeasure G { C with block := "if.end.i.i" } = walkMeasure G C ∧
      ∀ n, runFuel calls (1 + n) stage2Body s = runFuel calls n stage2Body e := by
  have hpc : s.pc = "if.end24.i" := by rw [hInv.pc_eq, hblock]
  obtain ⟨h3, h5, hK, hct, hcst, hhash⟩ := hInv.ptrs
  have hspv := hInv.depth_reg
  have hspExt : C.sp < stage2StackExtent := by
    have h520 : stage2StackExtent = 520 := rfl
    have := hguard
    simp only [NestGuard] at this
    omega
  have hcz := ctype_log_sep hInv
  have hsz := cst_log_sep hInv
  have hcev := ctype_ev_sep hInv
  have hsev := cst_ev_sep hInv
  have hN : G.nev0 + (C.events.map EventRecord.encodedBytes).flatten.length ≤ G.evcap := by
    have hsum := EventRecord.sum_encodedSize_le C.events
    simp only [stage2RecordBytes] at hsum
    have h4' := G.evRoom
    simp only [stage2RecordBytes] at h4'
    have hlen : (C.events.map EventRecord.encodedBytes).flatten.length =
        (C.events.map EventRecord.encodedSize).sum := by
      simp only [List.length_flatten, List.map_map]
      rfl
    have h1 : C.events.length ≤ C.k := hInv.events_le_of_tight (by
      rw [hblock]; exact walkEmitC_of_not_contains (by decide))
    have h2 := hInv.k_le
    have h3 := G.nep_le
    omega
  let e : State :=
    { (stateAt (ifEnd24Out s.env C.sp C.stage.ctype C.stage.cst b)
        { s with mem := writeBytes (writeBytes s.mem (C.stage.ctype + C.sp)
            (natToBytes (ifEnd24Ty b).toNat 1)) (C.stage.cst + C.sp) (natToBytes 0 1) }) with
      pc := "if.end.i.i"
      pre := some "if.end24.i" }
  have hstep : step calls stage2Body s = .jump e :=
    ifEnd24_term (calls := calls) (s := s) hpc h8 hspv hct hcst hhash hspExt hcz hsz
      hInv.log_hash
  obtain ⟨hTy, hSt⟩ :=
    walkStack_ifEnd24_at (mem := s.mem) (ctype := C.stage.ctype) (cst := C.stage.cst)
      (sp := C.sp) (wlen := C.wlen) (TM := C.tyMap) (SM := C.stMap) (b := b)
      hInv.tyBytes hInv.stBytes (ctype_cst_sep hInv) hInv.sp_le_wlen
      (by refine max_le hInv.wlen_cap ?_; have := hspExt; omega)
  refine ⟨e, hstep, ?_, ?_, ?_⟩
  · refine
      { pc_eq := rfl
        blockIndex := ?_
        k_le := hInv.k_le
        events_le := by
          show C.events.length ≤ C.k + walkEmitC "if.end.i.i"
          have h := hInv.events_le
          rw [hblock] at h
          have h1 : walkEmitC "if.end24.i" = 0 := walkEmitC_of_not_contains (by decide)
          have h2 : walkEmitC "if.end.i.i" = 0 := walkEmitC_of_not_contains (by decide)
          omega
        events_nep := hInv.events_nep
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
        sp_le_wlen := le_trans (Nat.le_succ _) (le_max_right _ _)
        wlen_cap := max_le hInv.wlen_cap (by have := hspExt; omega)
        tyBytes := hTy
        stBytes := hSt
        ptrs := ?_
        regs := by
          dsimp only [e, ifEnd24Out, ifEnd24Mid]
          exact (hInv.regs.names_of_eq ["%conv42.i", "%inc33.i", "%arrayidx32.i",
            "%arrayidx30.i", "%idxprom29.i", "%conv28.i", "%cmp26.i"] rfl (by decide)).names_of_eq
            ["%tobool.not.i.i", "%10"] rfl (by decide)
        iter := by
          dsimp only [e, ifEnd24Out, ifEnd24Mid]
          exact (hInv.iter.names_of_eq ["%conv42.i", "%inc33.i", "%arrayidx32.i",
            "%arrayidx30.i", "%idxprom29.i", "%conv28.i", "%cmp26.i"] rfl (by decide)).names_of_eq
            ["%tobool.not.i.i", "%10"] rfl (by decide)
        log_hash := ?_
        log_len := ?_
        log_cap := ?_
        log_alen := ?_
        log_acap := ?_
        log_base := ?_
        log_dst := ?_
        owned := walkStaged_write rfl (walkStaged_write rfl hInv.owned)
        root_slot := by
          dsimp only [e]
          exact hasBytes_writeBytes (hasBytes_writeBytes hInv.root_slot)
        next_ge := hInv.next_ge
        frame := ?_
        inc_reg := by
          dsimp only [e, stateAt]
          exact walkLookup_cells_ne _ "%inc.i"
            (walkLookup_cells_ne s.env "%inc.i" hInv.inc_reg _
              (by
                intro c hc
                simp only [ifEnd24HeadCells, List.mem_cons, List.not_mem_nil, or_false] at hc
                rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp))
            _
            (by
              intro c hc
              simp only [ifEnd24TailCells, List.mem_cons, List.not_mem_nil, or_false] at hc
              rcases hc with rfl | rfl <;> simp)
        idx_reg := by
          dsimp only [e, stateAt]
          exact walkLookup_cells_ne _ "%idxprom.i"
            (walkLookup_cells_ne s.env "%idxprom.i" hInv.idx_reg _
              (by
                intro c hc
                simp only [ifEnd24HeadCells, List.mem_cons, List.not_mem_nil, or_false] at hc
                rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp))
            _
            (by
              intro c hc
              simp only [ifEnd24TailCells, List.mem_cons, List.not_mem_nil, or_false] at hc
              rcases hc with rfl | rfl <;> simp)
        blockLocal := ?_ }
    · dsimp only [e, stateAt]
      exact walkLookup_cells_ne _ "%k.0.i249"
        (walkLookup_cells_ne s.env "%k.0.i249" hInv.blockIndex _
          (by
            intro c hc
            simp only [ifEnd24HeadCells, List.mem_cons, List.not_mem_nil, or_false] at hc
            rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp))
        _
        (by
          intro c hc
          simp only [ifEnd24TailCells, List.mem_cons, List.not_mem_nil, or_false] at hc
          rcases hc with rfl | rfl <;> simp)
    · dsimp only [e, stateAt]
      rw [readBytes_ev_of_stack_write (base := C.stage.cst) (v := natToBytes 0 1) hsev
        (sp := C.sp) hspExt (by simp [natToBytes]) (ev := G.ev) (evcap := G.evcap)
        (nev0 := G.nev0) (N := (C.events.map EventRecord.encodedBytes).flatten.length) hN]
      rw [readBytes_ev_of_stack_write (base := C.stage.ctype)
        (v := natToBytes (ifEnd24Ty b).toNat 1) hcev (sp := C.sp) hspExt
        (by simp [natToBytes]) (ev := G.ev) (evcap := G.evcap) (nev0 := G.nev0)
        (N := (C.events.map EventRecord.encodedBytes).flatten.length) hN]
      exact hInv.evBytes
    · dsimp only [e, stateAt]
      exact walkLookup_cells_ne _ "%sp.i.0248"
        (walkLookup_cells_ne s.env "%sp.i.0248" hInv.depth_reg _
          (by
            intro c hc
            simp only [ifEnd24HeadCells, List.mem_cons, List.not_mem_nil, or_false] at hc
            rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp))
        _
        (by
          intro c hc
          simp only [ifEnd24TailCells, List.mem_cons, List.not_mem_nil, or_false] at hc
          rcases hc with rfl | rfl <;> simp)
    · dsimp only [e, stateAt]
      exact (hInv.ptrs.cells_of (ifEnd24HeadCells C.sp C.stage.ctype C.stage.cst b)
        (by
          intro c hc
          simp only [ifEnd24HeadCells, List.mem_cons, List.not_mem_nil, or_false] at hc
          rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
            exact ⟨by simp, by simp, by simp, by simp, by simp, by simp⟩)).cells_of
        ifEnd24TailCells
        (by
          intro c hc
          simp only [ifEnd24TailCells, List.mem_cons, List.not_mem_nil, or_false] at hc
          rcases hc with rfl | rfl <;>
            exact ⟨by simp, by simp, by simp, by simp, by simp, by simp⟩)
    · dsimp only [e, stateAt]
      rw [readBytes_log_of_stack_write (base := C.stage.cst) (v := natToBytes 0 1) hsz
        (sp := C.sp) hspExt (by simp [natToBytes]) (off := 32) (len := 4) (by decide)]
      rw [readBytes_log_of_stack_write (base := C.stage.ctype)
        (v := natToBytes (ifEnd24Ty b).toNat 1) hcz (sp := C.sp) hspExt
        (by simp [natToBytes]) (off := 32) (len := 4) (by decide)]
      exact hInv.log_hash
    · dsimp only [e, stateAt]
      rw [readBytes_log_of_stack_write (base := C.stage.cst) (v := natToBytes 0 1) hsz
        (sp := C.sp) hspExt (by simp [natToBytes]) (off := 8) (len := 8) (by decide)]
      rw [readBytes_log_of_stack_write (base := C.stage.ctype)
        (v := natToBytes (ifEnd24Ty b).toNat 1) hcz (sp := C.sp) hspExt
        (by simp [natToBytes]) (off := 8) (len := 8) (by decide)]
      exact hInv.log_len
    · dsimp only [e, stateAt]
      rw [readBytes_log_of_stack_write (base := C.stage.cst) (v := natToBytes 0 1) hsz
        (sp := C.sp) hspExt (by simp [natToBytes]) (off := 16) (len := 8) (by decide)]
      rw [readBytes_log_of_stack_write (base := C.stage.ctype)
        (v := natToBytes (ifEnd24Ty b).toNat 1) hcz (sp := C.sp) hspExt
        (by simp [natToBytes]) (off := 16) (len := 8) (by decide)]
      exact hInv.log_cap
    · dsimp only [e, stateAt]
      rw [readBytes_log_of_stack_write (base := C.stage.cst) (v := natToBytes 0 1) hsz
        (sp := C.sp) hspExt (by simp [natToBytes]) (off := 48) (len := 8) (by decide)]
      rw [readBytes_log_of_stack_write (base := C.stage.ctype)
        (v := natToBytes (ifEnd24Ty b).toNat 1) hcz (sp := C.sp) hspExt
        (by simp [natToBytes]) (off := 48) (len := 8) (by decide)]
      exact hInv.log_alen
    · dsimp only [e, stateAt]
      rw [readBytes_log_of_stack_write (base := C.stage.cst) (v := natToBytes 0 1) hsz
        (sp := C.sp) hspExt (by simp [natToBytes]) (off := 56) (len := 8) (by decide)]
      rw [readBytes_log_of_stack_write (base := C.stage.ctype)
        (v := natToBytes (ifEnd24Ty b).toNat 1) hcz (sp := C.sp) hspExt
        (by simp [natToBytes]) (off := 56) (len := 8) (by decide)]
      exact hInv.log_acap
    · dsimp only [e, stateAt]
      rw [readBytes_log_base_of_stack_write (base := C.stage.cst) (v := natToBytes 0 1) hsz
        (sp := C.sp) hspExt (by simp [natToBytes])]
      rw [readBytes_log_base_of_stack_write (base := C.stage.ctype)
        (v := natToBytes (ifEnd24Ty b).toNat 1) hcz (sp := C.sp) hspExt
        (by simp [natToBytes])]
      exact hInv.log_base
    · dsimp only [e, stateAt]
      rw [readBytes_log_of_stack_write (base := C.stage.cst) (v := natToBytes 0 1) hsz
        (sp := C.sp) hspExt (by simp [natToBytes]) (off := 40) (len := 8) (by decide)]
      rw [readBytes_log_of_stack_write (base := C.stage.ctype)
        (v := natToBytes (ifEnd24Ty b).toNat 1) hcz (sp := C.sp) hspExt
        (by simp [natToBytes]) (off := 40) (len := 8) (by decide)]
      exact hInv.log_dst
    · dsimp only [e, stateAt]
      exact walkFrame_cst (G := G) (C := C) (v := natToBytes 0 1)
        (by simp [natToBytes]) hguard
        (walkFrame_ctype (G := G) (C := C) (v := natToBytes (ifEnd24Ty b).toNat 1)
          (by simp [natToBytes]) hguard hInv.frame)
    · dsimp only [e, stateAt]
      simp [WalkLocal]
  · rfl
  · intro n
    rw [show 1 + n = n + 1 from by omega]
    simp only [runFuel, hstep]




/-! ### The dispatch's trace

The trace the obligation's completion conjunct is: a chain of the walk's own
control steps, each of which preserves `WalkInv` and does not raise
`walkMeasure`.  The chain is what an induction over the dispatch produces, block
by block; this section states it, proves that it carries the invariant and the
measure, and gives it the links the module has proved: the header's block, the
nesting arm, the latch, and the censused classes A, B and
B′, the eighteen refusal stores of C, class D's ten stores, the two entry links,
class E's twelve merges and twelve of class G's fourteen reads, and the class F
blocks the call and finalisation modules prove, the arena reservation's completion
among them — a hundred and fifty-three blocks in all.  The four scan headers are
covered as counted rounds (`walkScanRounds457_of_cell` applying `scanRound_at`)
rather than as one-block links, three more blocks are discharged as steps, and the
five outside both are named with their obstruction under *The census* below. -/

/-! ### The census's arithmetic

The table's columns and the reconciliation as `#guard`s: the class rows sum to the
body's 165 blocks, the proved column sums to the 153 links the modules close, and
the links, the four scan rounds, the three finalisation steps and the five rows
outside both sum to 165 again.  `JsonStage2IR` pins the body's own count
(`stage2Body.blocks.length = 165`), so these lines hold the prose to the pinned body
rather than to a transcription; H1's four scan headers are counted in the rounds
term, not in the links, because their visit is the round
(`walkScanRounds457_of_cell` applying `scanRound_at`) rather than a one-block link. -/

#guard decide (60 + 9 + 1 + 18 + 11 + 15 + 19 + 14 + 10 + 2 + 6 = 165)
#guard decide (60 + 9 + 1 + 18 + 11 + 15 + 14 + 6 + 2 + 17 = 153)
#guard decide (153 + 4 + 3 + 5 = 165)

/-- **One link of the dispatch's trace**: a control step that preserves
`WalkInv` and does not raise the measure. -/
structure WalkLink (calls : Calls) {m0 : Mem} (G : WalkGeom m0)
    (C : WalkCarry G) (s : State) (C' : WalkCarry G) (s' : State) : Prop where
  /-- The invariant holds at the link's source. -/
  inv : WalkInv G C s
  /-- The step is a control step into the link's target. -/
  step : step calls stage2Body s = .jump s'
  /-- The invariant holds at the link's target. -/
  inv' : WalkInv G C' s'
  /-- The measure does not rise across the link. -/
  mono : walkMeasure G C' ≤ walkMeasure G C
  /-- **The link keeps the adapter's staging.**  A control step moves the carried
  numbers and the state, never the staging objects: every successor is a
  `{ C with … }` update, so this is `rfl` at each link site.  It is a field rather
  than a derived fact because the targets are existential in the dispatch results
  and the terminal post has to name the scratch objects the caller staged. -/
  stage_eq : C'.stage = C.stage

/-- **A trace**: a chain of links, from the invariant at its head to the invariant
at its tail. -/
inductive WalkChain (calls : Calls) {m0 : Mem} (G : WalkGeom m0) :
    WalkCarry G → State → WalkCarry G → State → Prop
  | nil {C : WalkCarry G} {s : State} (h : WalkInv G C s) :
      WalkChain calls G C s C s
  | tail {C C' C'' : WalkCarry G} {s s' s'' : State}
      (hl : WalkLink calls G C s C' s')
      (ht : WalkChain calls G C' s' C'' s'') :
      WalkChain calls G C s C'' s''

/-- A link's step, at `runFuel`: one control step is one fuel unit. -/
theorem walkLink_runFuel {calls : Calls} {m0 : Mem} {G : WalkGeom m0}
    {C C' : WalkCarry G} {s s' : State} (hl : WalkLink calls G C s C' s') (n : Nat) :
    runFuel calls (1 + n) stage2Body s = runFuel calls n stage2Body s' := by
  have hs : step calls stage2Body s = .jump s' := WalkLink.step hl
  rw [show 1 + n = n + 1 from by omega]
  simp only [runFuel, hs]

/-- **The trace carries the measure bound.**  Every link is non-increasing, so the
tail's measure is at most the head's. -/
theorem WalkChain.measure_le {calls : Calls} {m0 : Mem} {G : WalkGeom m0}
    {C C' : WalkCarry G} {s s' : State} (h : WalkChain calls G C s C' s') :
    walkMeasure G C' ≤ walkMeasure G C := by
  induction h with
  | nil => exact Nat.le_refl _
  | tail hl _ ih => exact le_trans ih hl.mono

/-- **The trace is a run.**  A chain of `k` links runs for `k` steps of fuel and
leaves exactly the fuel the tail needs, so a trace's end state is the run's state
at the head's fuel plus `k`. -/
theorem WalkChain.steps {calls : Calls} {m0 : Mem} {G : WalkGeom m0}
    {C C' : WalkCarry G} {s s' : State} (h : WalkChain calls G C s C' s') :
    ∃ k, ∀ n, runFuel calls (k + n) stage2Body s = runFuel calls n stage2Body s' := by
  induction h with
  | nil => exact ⟨0, fun n => by simp⟩
  | tail hl _ ih =>
      obtain ⟨k, hk⟩ := ih
      exact ⟨k + 1, fun n => by
        rw [show k + 1 + n = 1 + (k + n) from by omega, walkLink_runFuel hl, hk]⟩

/-- **The trace to a return completes.**  At a state whose step returns, the chain
from the head gives the run's outcome: the completion conjunct, at the trace's own
step count. -/
theorem WalkChain.completes {calls : Calls} {m0 : Mem} {G : WalkGeom m0}
    {C C' : WalkCarry G} {s s' sret : State} {v : Value}
    (h : WalkChain calls G C s C' s') (hret : step calls stage2Body s' = .ret v sret) :
    ∃ k, runFuel calls k stage2Body s = some (.ret v sret.mem) := by
  obtain ⟨k, hk⟩ := h.steps
  refine ⟨k + 1, ?_⟩
  rw [hk 1]
  simp only [runFuel, hret]

/-- **The trace's first proved link: the header's block.**  `while.body.i` advances
the entry index and strictly lowers the measure. -/
theorem WalkLink.whileBody {calls : Calls} {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G)
    (s : State) (hInv : WalkInv G C s) (hblock : C.block = "while.body.i")
    {k sp : Nat}
    (hpre : s.pre = some "cleanup478.i")
    (hk2 : lookupName s.env "%k.2.i" = some (.int 64 (BitVec.ofNat 64 k)))
    (hsp1 : lookupName s.env "%sp.i.1" = some (.int 32 (BitVec.ofNat 32 sp)))
    (hkge : C.k < k) (hklt : k < G.nep) (hspc : sp ≤ stage2StackExtent)
    (hspw : sp ≤ C.wlen) :
    ∃ s', WalkLink calls G C s { C with block := "NodeBlock21", k := k, sp := sp } s' := by
  obtain ⟨e, hstep, hinv, hmono, -⟩ :=
    whileBody_step (calls := calls) G C s hInv hblock hpre hk2 hsp1 hkge hklt hspc hspw
  exact ⟨e, ⟨hInv, hstep, hinv, le_of_lt hmono, rfl⟩⟩

/-- **The trace's second proved link: the nesting arm.**  `if.end24.i` writes the
two container stacks and branches on the log's zeroed hash word, with the measure
unchanged.  Its `%8` is read from the invariant's per-iteration carrier: the
header bound it at the carried index, and no block between the header and
`if.end24.i` rebinds it (`WalkIter.reg8`). -/
theorem WalkLink.ifEnd24 {calls : Calls} {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G)
    (s : State) (hInv : WalkInv G C s) (hblock : C.block = "if.end24.i")
    {b : BitVec 8} (h8 : lookupName s.env "%8" = some (.int 8 b))
    (hguard : NestGuard C.sp) :
    ∃ s', WalkLink calls G C s { C with
      block := "if.end.i.i", wlen := max C.wlen (C.sp + 1),
      tyMap := fun i => if i = C.sp then ifEnd24TyByte b else C.tyMap i,
      stMap := fun i => if i = C.sp then ifEnd24StByte else C.stMap i } s' := by
  obtain ⟨e, hstep, hinv, hmono, -⟩ :=
    ifEnd24_step (b := b) G C s hInv hblock h8 hguard
  exact ⟨e, ⟨hInv, hstep, hinv, le_of_eq hmono, rfl⟩⟩

end WalkScope
end LeanLLVM.Refinement
