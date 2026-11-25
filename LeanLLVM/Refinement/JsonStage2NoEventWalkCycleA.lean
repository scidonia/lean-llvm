/-
The no-event walk's shared cycle: the after-value dispatch's return to the head.

The class rows end where a value has been consumed: `after_value`, with the
dispatch's seven `phi`s bound to the class's readings.  The return from there to
`NodeBlock5` is one path, shared by every class, and this module owns it:

    after_value → if.end369 → if.end378 → if.end410 → NodeBlock41 → LeafBlock37
      → value.outer.backedge → if.end.peel → NodeBlock5

The byte the cycle reads is the `,` that follows the value at a non-zero depth:
`if.end378` loads the entry at the class's index, `NodeBlock41`'s `slt 93` takes
its true arm for it, `LeafBlock37`'s `eq 44` takes `value.outer.backedge`, and the
backedge's `cmp.not.peel` guard admits the next head.  The cycle writes no memory,
so the invariant travels by `Stage2NoEventWalkInv.mem_congr` at every hop.

`value.outer.backedge`'s `phi` run is the edge's: the seven carried readings come
from `LeafBlock37`'s registers, so the run's selection is a hypothesis of the
`phi`-level lemma and `value.outer.backedge`'s entry lemma builds it from that
edge's own registers.  `if.end.peel` then binds the head's nine `phi`s from the
backedge's cells and reads the next entry's lane and the document's byte at it,
which is exactly `Stage2NoEventWalkHead`'s layer equation.

`Stage2NoEventWalkCycleSrc` is the class lane's endpoint: the state at
`after_value`'s entry, the class's carry and trace, the dispatch `phi` run's
selection, the depth and frame words the continuation needs, and the head's base
lookups carried through the class route.  `stage2NoEventWalkCycle_of_afterValue`
turns one into `Stage2NoEventWalkCycle` — a priced head segment from the endpoint
to the next head — so a class lane composes its own route with this cycle to
obtain `Row.cont`.  The cycle is parameterised by its index delta `d`: one entry
on this (after-value) path, four on the object-member pair path that `if.end303`
opens.  The credit is `32·d + 8·(ent[k+d] − ent[k])`, so the entry allowance
alone pays for the steps: the lemma is `Φ K (k+d) + 32·d ≤ Φ K k`, and the
table's `32·d + 8·(ent[k+d] − ent[k])` leaves the byte term as headroom over it.
`d = 1` is therefore the instance `stage2NoEventWalkCycle_of_afterValue` proves,
with its target at `k + 1`.

**What this module does not prove.**  It owns the *after-value* entry only.  The
object-member continuation reaches the same backedge from `if.end303` (the pair
route's endpoint, `%inc304 = %k.1.in + 4`): that block's denotation, its
`PhiSelects` at its edge and a `d = 4` instance of this cycle are the pair
route's, and nothing here states them.  The closing classes' pop back to
`after_value` (`if.then334`/`do.body391`/`do.body417` reaching
`close_arr`/`close_obj`) is the class lanes'.  Both ends this module takes are
given: the endpoint (`Stage2NoEventWalkCycleSrc`, from the class route) and the
backedge's own edge (`LeafBlock37`).
-/
import LeanLLVM.Refinement.JsonStage2NoEventWalkSeed

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 1600000

namespace LeanLLVM.Refinement

open LeanLLVM
open LeanLLVM.JSON
open LeanLLVM.Refinement.JsonStage2NoEventIR
open LeanLLVM.Refinement.JsonEntryIR (readLanes32)
open LeanLLVM.Refinement.BlockEval
open LeanLLVM.Refinement.JsonEntrySteps (readBytes_one readBytes_length)
open LeanLLVM.Refinement.JsonS1MasksIR
  (evalInstr_select_true evalInstr_select_false)

/-- Peel a `lookupName` through a block's own cons cells: the branch that can
close, the peel, or the cell the name is.  Applied where a step's environment is
the block's cons chain rather than a `cells` builder. -/
macro "cycle_lk" : tactic => `(tactic|
  (repeat first
    | rfl
    | assumption
    | rw [lookupName_cons_self]
    | rw [lookupName_cons_ne _ _ (by decide)]))

/-! ### Arithmetic on the model's words

The cycle's cells are `BitVec.ofNat` words; the identities below are the ones a
`zext`, an `add` and the two `icmp` guards need. -/

/-- **A successor at 64 bits.** -/
theorem stage2NoEventOfNatSucc {k : Nat} (h : k + 1 < 2 ^ 64) :
    BitVec.ofNat 64 k + (1 : BitVec 64) = BitVec.ofNat 64 (k + 1) := by
  apply BitVec.eq_of_toNat_eq
  have hk : k < 2 ^ 64 := by omega
  have h1 : (1 : BitVec 64).toNat = 1 := by decide
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat, h1, Nat.mod_eq_of_lt hk,
    Nat.mod_eq_of_lt h]

/-- **A `zext` from 32 to 64 bits is the number.** -/
theorem stage2NoEventOfNat64_ofNat32 {x : Nat} (h : x < 2 ^ 32) :
    BitVec.ofNat 64 (BitVec.ofNat 32 x).toNat = BitVec.ofNat 64 x := by
  rw [stage2NoEventOfNat32_toNat h]

/-- **A sign-extended word's `Nat` is the number**, below the modulus. -/
theorem stage2NoEventSignExtend_toNat {x : Nat} (h : x < 2 ^ 64) :
    ((BitVec.ofNat 64 x).signExtend 64).toNat = x := by
  rw [BitVec.signExtend_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

/-- **A non-zero depth word is not zero.** -/
theorem stage2NoEventOfNat32_ne {x : Nat} (hx : x < 2 ^ 32) (h : x ≠ 0) :
    BitVec.ofNat 32 x ≠ BitVec.ofNat 32 0 := by
  intro hc
  apply h
  have h' := congrArg BitVec.toNat hc
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx] at h'
  exact h'

/-- **A non-zero frame byte is not zero.** -/
theorem stage2NoEventOfNat8_ne {x : Nat} (hx : x < 2 ^ 8) (h : x ≠ 0) :
    BitVec.ofNat 8 x ≠ BitVec.ofNat 8 0 := by
  intro hc
  apply h
  have h' := congrArg BitVec.toNat hc
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx] at h'
  exact h'

/-- **`icmp eq` at zero from distinct words.** -/
theorem stage2NoEventICmp_eq_zero {w : Nat} {x c : BitVec w} (h : x ≠ c) :
    evalICmp .eq x c = 0 := by
  simp [evalICmp, h]

/-- **`icmp ult` is one at the `Nat` order.** -/
theorem stage2NoEventICmp_ult_one {w : Nat} {x y : Nat}
    (hx : x < 2 ^ w) (hy : y < 2 ^ w) (h : x < y) :
    evalICmp .ult (BitVec.ofNat w x) (BitVec.ofNat w y) = 1 := by
  simp only [evalICmp, BitVec.ult, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx,
    Nat.mod_eq_of_lt hy, h, BitVec.ofBool]
  rfl

/-- **`icmp ugt` is one at the `Nat` order.** -/
theorem stage2NoEventICmp_ugt_one {w : Nat} {x y : Nat}
    (hx : x < 2 ^ w) (hy : y < 2 ^ w) (h : y < x) :
    evalICmp .ugt (BitVec.ofNat w x) (BitVec.ofNat w y) = 1 := by
  simp only [evalICmp, BitVec.ult, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx,
    Nat.mod_eq_of_lt hy, h, BitVec.ofBool]
  rfl

/-- **`icmp ugt` is zero at or below the `Nat` order.** -/
theorem stage2NoEventICmp_ugt_zero {w : Nat} {x y : Nat}
    (hx : x < 2 ^ w) (hy : y < 2 ^ w) (h : x ≤ y) :
    evalICmp .ugt (BitVec.ofNat w x) (BitVec.ofNat w y) = 0 := by
  have hlt : ¬ y < x := by omega
  simp only [evalICmp, BitVec.ult, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx,
    Nat.mod_eq_of_lt hy, hlt, BitVec.ofBool]
  rfl

/-- **Four bytes are below `2 ^ 32`.** -/
theorem stage2NoEventBytesToNat_lt_32 {bs : List UInt8} (h : bs.length = 4) :
    bytesToNat bs < 2 ^ 32 := by
  have := bytesToNat_lt bs
  rw [h] at this
  calc bytesToNat bs < 256 ^ 4 := this
    _ = 2 ^ 32 := by decide

/-- **The one-byte encoding read back.** -/
theorem stage2NoEventBytesToNat_singleton (b : UInt8) :
    bytesToNat [b] = b.toNat := by
  simp [bytesToNat]

/-! ### A 32-bit select

`%umax` is a 32-bit select; the tree's select steps are 64-bit, so the cycle
states its own. -/

/-- `%d = select i1 %c, %a, <b>` at 32 bits, condition set. -/
theorem step_select32_imm_true (calls : Calls) (env : Env) (s : State)
    (d c a : String) {x y : BitVec 32}
    (hc : lookupName env c = some (.int 1 (1 : BitVec 1)))
    (ha : lookupName env a = some (.int 32 x)) :
    evalInstr calls (stateAt env s)
        (.select d (.int 32) (.reg c) (.reg a) (.imm (.int 32 y))) =
      some (stateAt ((d, .int 32 x) :: env) s) := by
  show evalInstr calls (stateAt env s)
      (.select d (.int 32) (.reg c) (.reg a) (.imm (.int 32 y))) =
    some ((stateAt env s).bind d (.int 32 x))
  exact evalInstr_select_true (calls := calls) (s := stateAt env s) (d := d)
    (ty := Ty.int 32) (c := .reg c) (a := .reg a) (b := .imm (.int 32 y))
    (va := .int 32 x) (vb := .int 32 y)
    (hc := evalOperand_reg_of env s c (.int 1 (1 : BitVec 1)) hc)
    (ha := evalOperand_reg_of env s a (.int 32 x) ha)
    (hb := evalOperand_lit_of (s := stateAt env s) 32 y)

/-- `%d = select i1 %c, %a, <b>` at 32 bits, condition clear. -/
theorem step_select32_imm_false (calls : Calls) (env : Env) (s : State)
    (d c a : String) {x y : BitVec 32}
    (hc : lookupName env c = some (.int 1 (0 : BitVec 1)))
    (ha : lookupName env a = some (.int 32 x)) :
    evalInstr calls (stateAt env s)
        (.select d (.int 32) (.reg c) (.reg a) (.imm (.int 32 y))) =
      some (stateAt ((d, .int 32 y) :: env) s) := by
  show evalInstr calls (stateAt env s)
      (.select d (.int 32) (.reg c) (.reg a) (.imm (.int 32 y))) =
    some ((stateAt env s).bind d (.int 32 y))
  exact evalInstr_select_false (calls := calls) (s := stateAt env s) (d := d)
    (ty := Ty.int 32) (c := .reg c) (a := .reg a) (b := .imm (.int 32 y))
    (va := .int 32 x) (vb := .int 32 y)
    (hc := evalOperand_reg_of env s c (.int 1 (0 : BitVec 1)) hc)
    (ha := evalOperand_reg_of env s a (.int 32 x) ha)
    (hb := evalOperand_lit_of (s := stateAt env s) 32 y)

/-- `%d = select i1 %c, %a, <b>` at 32 bits, by the condition's bit. -/
theorem stage2NoEventDenoteSelect32 (calls : Calls) (env : Env) (s : State)
    (d c a : String) {bb : BitVec 1} {x y : BitVec 32}
    (hc : lookupName env c = some (.int 1 bb))
    (ha : lookupName env a = some (.int 32 x)) (is : List Instr) :
    denoteCode calls (.select d (.int 32) (.reg c) (.reg a) (.imm (.int 32 y)) :: is)
        (stateAt env s) =
      denoteCode calls is (stateAt ((d, .int 32 (if bb = 1 then x else y)) :: env) s) := by
  rcases bitVec1_eq_zero_or_one bb with h | h
  · rw [h, ite_eq_right (by decide)]
    exact denoteCode_cons_of calls
      (.select d (.int 32) (.reg c) (.reg a) (.imm (.int 32 y))) is
      (stateAt env s) (stateAt ((d, .int 32 y) :: env) s)
      (step_select32_imm_false calls env s d c a (x := x) (y := y)
        (by rw [hc, h]) ha) (by rfl)
  · rw [h, ite_eq_left rfl]
    exact denoteCode_cons_of calls
      (.select d (.int 32) (.reg c) (.reg a) (.imm (.int 32 y))) is
      (stateAt env s) (stateAt ((d, .int 32 x) :: env) s)
      (step_select32_imm_true calls env s d c a (x := x) (y := y)
        (by rw [hc, h]) ha) (by rfl)

/-! ### A block's unconditional branch as a link -/

/-- One control step at a block's unconditional branch. -/
theorem stage2NoEventWalkLink_br {calls : Calls} {K : Stage2NoEventWalkCarry}
    {mem : Mem} {s : State} {env' : Env} {blk : Block} {dest : String}
    (h : Stage2NoEventWalkInv K mem s)
    (hfind : stage2NoEventBody.findBlock s.pc = some blk)
    (hcode : denoteCode calls blk.instrs (stateAt s.env s) = some (stateAt env' s))
    (hterm : blk.term = Term.br dest) :
    Stage2NoEventWalkLink calls K mem s K (stage2NoEventWalkNext env' s dest) := by
  refine ⟨h, ?_, Stage2NoEventWalkInv.mem_congr h rfl⟩
  have hstep := stage2NoEventWalk_step_br (f := stage2NoEventBody) hfind hcode hterm
  simpa only [stage2NoEventWalkNext, stateAt] using hstep


/-! ### The entry stream's and the document's readings at the run's memory

The head the cycle produces reads the next entry's lane and the document's byte
at it.  Both are the caller's staging, kept by the run's frame because the ABI
regions and the stack interval are separate. -/

/-- The four ABI entries followed by the writes and the staged objects. -/
theorem stage2NoEventCycleRegions {K : Stage2NoEventWalkCarry} {mem : Mem}
    {s : State} (h : Stage2NoEventWalkInv K mem s) :
    DisjointRegions
      ([(K.b, K.n + stage2ReadTail), (K.ep, 4 * K.nep), (K.xp, 4 * K.nxp),
        (K.scratch, K.scratchcap)] ++
        (stage2NoEventWrites K.tokensOut K.valuesOut K.sumOut K.err ++
          stage2NoEventStagedRegions K.stk K.e K.c K.d)) := by
  simpa only [Stage2NoEventWalkSep, stage2NoEventRegions, List.append_assoc] using h.sep

/-- **The second and fourth entries of a region list are separated.** -/
theorem stage2NoEventCycleSep24 {a b c d : Nat × Nat} {rest : List (Nat × Nat)}
    (h : DisjointRegions ((a :: b :: c :: d :: []) ++ rest)) :
    b.1 + b.2 ≤ d.1 ∨ d.1 + d.2 ≤ b.1 := by
  unfold DisjointRegions at h
  rw [List.pairwise_append] at h
  obtain ⟨h1, -⟩ := h
  rw [List.pairwise_cons] at h1
  obtain ⟨-, h1⟩ := h1
  rw [List.pairwise_cons] at h1
  exact h1.1 d (by simp)

/-- **The first and fourth entries of a region list are separated.** -/
theorem stage2NoEventCycleSep14 {a b c d : Nat × Nat} {rest : List (Nat × Nat)}
    (h : DisjointRegions ((a :: b :: c :: d :: []) ++ rest)) :
    a.1 + a.2 ≤ d.1 ∨ d.1 + d.2 ≤ a.1 := by
  unfold DisjointRegions at h
  rw [List.pairwise_append] at h
  obtain ⟨h1, -⟩ := h
  rw [List.pairwise_cons] at h1
  exact h1.1 d (by simp)

/-- **The entry stream is outside the run's writes**, so its read is the staging's. -/
theorem stage2NoEventCycleOutLane {K : Stage2NoEventWalkCarry} {mem : Mem}
    {s : State} (h : Stage2NoEventWalkInv K mem s) :
    ∀ j, j < 4 * K.nep → ¬ inRegions
      (stage2NoEventRunRegions K.scratch K.scratchcap K.stk K.e K.c K.d ++
        [(K.next0, K.nextEnd - K.next0)]) (K.ep + j) := by
  intro j hj hin
  have hfour := stage2NoEventCycleRegions h
  obtain ⟨r, hr, hlo, hhi⟩ := hin
  rcases List.mem_append.mp hr with hr | hr
  · rcases List.mem_cons.mp hr with hsc | hst
    · subst hsc
      rcases stage2NoEventCycleSep24 hfour with h' | h' <;> omega
    · have hep : (K.ep, 4 * K.nep) ∈ stage2NoEventRegions K.b K.n K.ep K.nep K.xp
          K.nxp K.scratch K.scratchcap K.tokensOut K.valuesOut K.sumOut K.err := by
        simp [stage2NoEventRegions]
      rcases disjointRegions_against
        (rs := stage2NoEventRegions K.b K.n K.ep K.nep K.xp K.nxp K.scratch
          K.scratchcap K.tokensOut K.valuesOut K.sumOut K.err)
        (ss := stage2NoEventStagedRegions K.stk K.e K.c K.d) h.sep hep r hst with h' | h'
      · omega
      · omega
  · have hle : K.ep + 4 * K.nep ≤ K.next0 :=
      h.watermark (K.ep, 4 * K.nep) (by simp [stage2NoEventRegions])
    have hr' : r = (K.next0, K.nextEnd - K.next0) := by
      simpa only [List.mem_singleton] using hr
    subst hr'
    simp only at hlo hhi
    omega

/-- **The document is outside the run's writes.** -/
theorem stage2NoEventCycleOutDoc {K : Stage2NoEventWalkCarry} {mem : Mem}
    {s : State} (h : Stage2NoEventWalkInv K mem s) {lane : Nat} (hlane : lane < K.n) :
    ∀ j, j < 1 → ¬ inRegions
      (stage2NoEventRunRegions K.scratch K.scratchcap K.stk K.e K.c K.d ++
        [(K.next0, K.nextEnd - K.next0)]) (K.b + lane + j) := by
  intro j hj hin
  have hfour := stage2NoEventCycleRegions h
  obtain ⟨r, hr, hlo, hhi⟩ := hin
  rcases List.mem_append.mp hr with hr | hr
  · rcases List.mem_cons.mp hr with hsc | hst
    · subst hsc
      rcases stage2NoEventCycleSep14 hfour with h' | h' <;> omega
    · have hdoc : (K.b, K.n + stage2ReadTail) ∈ stage2NoEventRegions K.b K.n K.ep
          K.nep K.xp K.nxp K.scratch K.scratchcap K.tokensOut K.valuesOut K.sumOut
          K.err := by
        simp [stage2NoEventRegions]
      rcases disjointRegions_against
        (rs := stage2NoEventRegions K.b K.n K.ep K.nep K.xp K.nxp K.scratch
          K.scratchcap K.tokensOut K.valuesOut K.sumOut K.err)
        (ss := stage2NoEventStagedRegions K.stk K.e K.c K.d) h.sep hdoc r hst with h' | h'
      · omega
      · omega
  · have hle : K.b + (K.n + stage2ReadTail) ≤ K.next0 :=
      h.watermark (K.b, K.n + stage2ReadTail) (by simp [stage2NoEventRegions])
    have hr' : r = (K.next0, K.nextEnd - K.next0) := by
      simpa only [List.mem_singleton] using hr
    subst hr'
    simp only at hlo hhi
    omega

/-- **A `readLanes32` read is its lanes**, with each lane's four bytes and value. -/
theorem stage2NoEventCycleLanes {m : Mem} {addr : Nat} :
    ∀ {n : Nat} {l : List Nat}, readLanes32 m addr n = some l →
      l.length = n ∧ ∀ j, j < n →
        ∃ q bs, l[j]? = some q ∧ readBytes m (addr + 4 * j) 4 = some bs ∧
          bytesToNat bs = q
  | 0, l, h => by
      simp only [readLanes32, Option.some.injEq] at h
      subst h
      exact ⟨rfl, fun j hj => absurd hj (Nat.not_lt_zero j)⟩
  | n + 1, l, h => by
      simp only [readLanes32] at h
      cases hb : readBytes m addr 4 with
      | none => rw [hb] at h; cases h
      | some bs =>
          rw [hb] at h
          cases hr : readLanes32 m (addr + 4) n with
          | none => rw [hr] at h; cases h
          | some tl =>
              rw [hr] at h
              simp only [Option.map_some, Option.bind_some, Option.some.injEq] at h
              subst h
              obtain ⟨hlen, hget⟩ := stage2NoEventCycleLanes (m := m) (addr := addr + 4) hr
              refine ⟨by simp [hlen], ?_⟩
              intro j hj
              cases j with
              | zero => exact ⟨bytesToNat bs, bs, by simp, by simpa using hb, rfl⟩
              | succ i =>
                  obtain ⟨q, bs', hq, hread, hval⟩ := hget i (by omega)
                  exact ⟨q, bs', by simp [hq], by
                    rw [show addr + 4 * (i + 1) = addr + 4 + 4 * i from by omega]
                    exact hread, hval⟩

/-- **The entry at an index inside the stream**, its lane's four bytes and value,
and the lane's bound. -/
theorem stage2NoEventCycleEnt_lane {K : Stage2NoEventWalkCarry} {m : Mem} {j : Nat}
    (hent : readLanes32 m K.ep K.nep = some K.ent) (hj : j < K.nep) :
    ∃ (lane : Nat) (bs : List UInt8), K.ent[j]? = some lane ∧
      readBytes m (K.ep + 4 * j) 4 = some bs ∧ bytesToNat bs = lane ∧
      lane < 2 ^ 32 := by
  obtain ⟨-, hget⟩ := stage2NoEventCycleLanes hent
  obtain ⟨lane, bs, hq, hread, hval⟩ := hget j hj
  refine ⟨lane, bs, hq, hread, hval, ?_⟩
  rw [← hval]
  exact stage2NoEventBytesToNat_lt_32 (readBytes_length _ _ _ hread)


/-! ### The after-value dispatch

The class lane leaves the state at `after_value`'s entry with the dispatch's `phi`
run selected.  The block's own remainder is the two tests. -/

/-- The after-value dispatch's seven `phi`s, in the order the block writes them. -/
def afterValuePhiSpecs : List PhiSpec :=
  [ ⟨"%frame.6", Ty.int 8,
      [("cleanup287", .reg "%frame.0.lcssa1099"), ("if.then343", .reg "%49"),
       ("close_obj", .imm (.int 8 (BitVec.ofNat 8 0))), ("if.then350", .reg "%50"),
       ("close_arr", .reg "%frame.4"), ("if.end545", .reg "%frame.0.lcssa1097"),
       ("while.body557", .reg "%frame.0.lcssa1097")]⟩,
    ⟨"%sp.4", Ty.int 32,
      [("cleanup287", .reg "%sp.0.lcssa1093.wide"), ("if.then343", .reg "%dec"),
       ("close_obj", .reg "%dec"), ("if.then350", .reg "%sp.3"),
       ("close_arr", .reg "%sp.3"), ("if.end545", .reg "%sp.0.lcssa1091.wide"),
       ("while.body557", .reg "%sp.0.lcssa1091.wide")]⟩,
    ⟨"%k.6", Ty.int 64,
      [("cleanup287", .reg "%inc217"), ("if.then343", .reg "%k.4"),
       ("close_obj", .reg "%k.4"), ("if.then350", .reg "%k.5"),
       ("close_arr", .reg "%k.5"), ("if.end545", .reg "%inc.lcssa"),
       ("while.body557", .reg "%inc.lcssa")]⟩,
    ⟨"%alen.8", Ty.int 64,
      [("cleanup287", .reg "%alen.4"), ("if.then343", .reg "%alen.6"),
       ("close_obj", .reg "%alen.6"), ("if.then350", .reg "%alen.7"),
       ("close_arr", .reg "%alen.7"), ("if.end545", .reg "%alen.0.ph1405"),
       ("while.body557", .reg "%alen.0.ph1405")]⟩,
    ⟨"%arena.10", Ty.int 64,
      [("cleanup287", .reg "%arena.6"), ("if.then343", .reg "%arena.8"),
       ("close_obj", .reg "%arena.8"), ("if.then350", .reg "%arena.9"),
       ("close_arr", .reg "%arena.9"), ("if.end545", .reg "%arena.0.ph1406"),
       ("while.body557", .reg "%arena.0.ph1406")]⟩,
    ⟨"%terms.8", Ty.int 64,
      [("cleanup287", .reg "%terms.4"), ("if.then343", .reg "%terms.6"),
       ("close_obj", .reg "%terms.6"), ("if.then350", .reg "%terms.7"),
       ("close_arr", .reg "%terms.7"), ("if.end545", .reg "%terms.12"),
       ("while.body557", .reg "%terms.12")]⟩,
    ⟨"%tokens.8", Ty.int 64,
      [("cleanup287", .reg "%tokens.4"), ("if.then343", .reg "%tokens.6"),
       ("close_obj", .reg "%tokens.6"), ("if.then350", .reg "%tokens.7"),
       ("close_arr", .reg "%tokens.7"), ("if.end545", .reg "%tokens.12"),
       ("while.body557", .reg "%tokens.12")]⟩ ]

/-- The after-value `phi` run, as instructions. -/
def afterValuePhiInstrs : List Instr := afterValuePhiSpecs.map PhiSpec.instr

/-- The after-value dispatch's two tests. -/
def afterValueDispatchInstrs : List Instr :=
  [ Instr.icmp "%cmp355" IPred.eq 32 (Operand.reg "%sp.4")
      (Operand.imm (.int 32 (BitVec.ofNat 32 0))),
    Instr.icmp "%cmp358" IPred.ult 64 (Operand.reg "%k.6") (Operand.reg "%nep") ]

/-- `after_value`, pinned. -/
def afterValueBlock : Block :=
  { name := "after_value", instrs := afterValuePhiInstrs ++ afterValueDispatchInstrs,
    term := Term.condbr (Operand.reg "%cmp355") "if.then357" "if.end369" }

theorem afterValueBlock_find :
    stage2NoEventBody.findBlock "after_value" = some afterValueBlock := by
  decide

/-- The `phi` run's cells, newest first. -/
def afterValuePhiCells (fr sp k alen arena terms tok : Nat) : List (String × Value) :=
  [("%tokens.8", .int 64 (BitVec.ofNat 64 tok)),
   ("%terms.8", .int 64 (BitVec.ofNat 64 terms)),
   ("%arena.10", .int 64 (BitVec.ofNat 64 arena)),
   ("%alen.8", .int 64 (BitVec.ofNat 64 alen)),
   ("%k.6", .int 64 (BitVec.ofNat 64 k)),
   ("%sp.4", .int 32 (BitVec.ofNat 32 sp)),
   ("%frame.6", .int 8 (BitVec.ofNat 8 fr))]

/-- The dispatch's two cells, newest first. -/
def afterValueDispatchCells : List (String × Value) :=
  [("%cmp358", .int 1 1), ("%cmp355", .int 1 0)]

/-- The after-value `phi` run's binding, at the seven values the class lane's
edge supplies. -/
theorem afterValue_phi_denote {calls : Calls} {env : Env} {s : State} {p : String}
    {fr sp k alen arena terms tok : Nat}
    (hpre : s.pre = some p)
    (hsel : PhiSelects (stateAt env s) p afterValuePhiSpecs
      [("%frame.6", .int 8 (BitVec.ofNat 8 fr)),
       ("%sp.4", .int 32 (BitVec.ofNat 32 sp)),
       ("%k.6", .int 64 (BitVec.ofNat 64 k)),
       ("%alen.8", .int 64 (BitVec.ofNat 64 alen)),
       ("%arena.10", .int 64 (BitVec.ofNat 64 arena)),
       ("%terms.8", .int 64 (BitVec.ofNat 64 terms)),
       ("%tokens.8", .int 64 (BitVec.ofNat 64 tok))]) :
    denoteCode calls afterValuePhiInstrs (stateAt env s) =
      some (stateAt (cells (afterValuePhiCells fr sp k alen arena terms tok) env) s) := by
  rw [afterValuePhiInstrs,
    ← List.append_nil (List.map PhiSpec.instr afterValuePhiSpecs),
    denoteCode_phiRun (s := stateAt env s) (p := p) (specs := afterValuePhiSpecs)
      (vs := _) (rest := []) hpre hsel (by decide)]
  simp only [stateAt_bindAll_runCells, afterValuePhiCells, runCells, cells]
  rfl

/-- The dispatch's two tests, from the `phi` cells. -/
theorem afterValue_dispatch_denote (calls : Calls) (env : Env) (s : State)
    {sp k nep : Nat}
    (hsp : lookupName env "%sp.4" = some (.int 32 (BitVec.ofNat 32 sp)))
    (hk : lookupName env "%k.6" = some (.int 64 (BitVec.ofNat 64 k)))
    (hnep : lookupName env "%nep" = some (.int 64 (BitVec.ofNat 64 nep)))
    (hspLt : sp < 2 ^ 32) (hspNe : sp ≠ 0)
    (hkLt : k < 2 ^ 64) (hkl : k < nep) (hnepLt : nep < 2 ^ 64) :
    denoteCode calls afterValueDispatchInstrs (stateAt env s) =
      some (stateAt (cells afterValueDispatchCells env) s) := by
  rw [afterValueDispatchInstrs]
  rw [stage2NoEventWalk_denote_icmp_imm (calls := calls) (env := env) (s := s)
    (d := "%cmp355") (a := "%sp.4") (p := .eq) (w := 32)
    (x := BitVec.ofNat 32 sp) (c := BitVec.ofNat 32 0) ?_
    (is := [Instr.icmp "%cmp358" IPred.ult 64 (Operand.reg "%k.6")
      (Operand.reg "%nep")])]
  all_goals cycle_lk
  rw [stage2NoEventICmp_eq_zero (x := BitVec.ofNat 32 sp)
    (c := BitVec.ofNat 32 0) (stage2NoEventOfNat32_ne hspLt hspNe)]
  rw [denoteCode_icmp_ult_reg (calls := calls)
    (env := ("%cmp355", Value.int 1 (0 : BitVec 1)) :: env) (s := s)
    (d := "%cmp358") (a := "%k.6") (b := "%nep")
    (x := BitVec.ofNat 64 k) (y := BitVec.ofNat 64 nep) ?_ ?_ (is := [])]
  all_goals cycle_lk
  rw [stage2NoEventICmp_ult_one (w := 64) (x := k) (y := nep) hkLt hnepLt hkl]
  simp only [afterValueDispatchCells, cells, denoteCode_nil]

/-- **The after-value block's run**: the `phi` run and the two tests. -/
theorem afterValue_denote {calls : Calls} {env : Env} {s : State} {p : String}
    {fr sp k alen arena terms tok nep : Nat}
    (hpre : s.pre = some p)
    (hsel : PhiSelects (stateAt env s) p afterValuePhiSpecs
      [("%frame.6", .int 8 (BitVec.ofNat 8 fr)),
       ("%sp.4", .int 32 (BitVec.ofNat 32 sp)),
       ("%k.6", .int 64 (BitVec.ofNat 64 k)),
       ("%alen.8", .int 64 (BitVec.ofNat 64 alen)),
       ("%arena.10", .int 64 (BitVec.ofNat 64 arena)),
       ("%terms.8", .int 64 (BitVec.ofNat 64 terms)),
       ("%tokens.8", .int 64 (BitVec.ofNat 64 tok))])
    (hnep : lookupName env "%nep" = some (.int 64 (BitVec.ofNat 64 nep)))
    (hspLt : sp < 2 ^ 32) (hspNe : sp ≠ 0)
    (hkLt : k < 2 ^ 64) (hkl : k < nep) (hnepLt : nep < 2 ^ 64) :
    denoteCode calls afterValueBlock.instrs (stateAt env s) =
      some (stateAt
        (cells afterValueDispatchCells (cells (afterValuePhiCells fr sp k alen arena
          terms tok) env)) s) := by
  have hphi := afterValue_phi_denote (calls := calls) (s := s) (env := env)
    (fr := fr) (sp := sp) (k := k) (alen := alen) (arena := arena) (terms := terms)
    (tok := tok) hpre hsel
  rw [afterValueBlock]
  rw [denoteCode_append_apply (a := afterValuePhiInstrs) (b := afterValueDispatchInstrs)
    (s := stateAt env s)
    (s' := stateAt (cells (afterValuePhiCells fr sp k alen arena terms tok) env) s)
    hphi (by decide)]
  rw [afterValue_dispatch_denote (calls := calls)
    (env := cells (afterValuePhiCells fr sp k alen arena terms tok) env) (s := s)
    (sp := sp) (k := k) (nep := nep)
    (by
      exact cells_lookup_of_mem _ _ (by simp [afterValuePhiCells]) (by
        rw [show (afterValuePhiCells fr sp k alen arena terms tok).map (·.1) =
          ["%tokens.8", "%terms.8", "%arena.10", "%alen.8", "%k.6", "%sp.4",
            "%frame.6"] from rfl]
        decide))
    (by
      exact cells_lookup_of_mem _ _ (by simp [afterValuePhiCells]) (by
        rw [show (afterValuePhiCells fr sp k alen arena terms tok).map (·.1) =
          ["%tokens.8", "%terms.8", "%arena.10", "%alen.8", "%k.6", "%sp.4",
            "%frame.6"] from rfl]
        decide))
    (by
      rw [cells_lookup_of_notin _ _ (by
        rw [show (afterValuePhiCells fr sp k alen arena terms tok).map (·.1) =
          ["%tokens.8", "%terms.8", "%arena.10", "%alen.8", "%k.6", "%sp.4",
            "%frame.6"] from rfl]
        decide)]
      exact hnep)
    hspLt hspNe hkLt hkl hnepLt]

/-! ### The dispatch's middle blocks -/

/-- `if.end369`: the live-entry test, to the zero-depth closer path. -/
def ifEnd369Block : Block :=
  { name := "if.end369", instrs := [],
    term := Term.condbr (Operand.reg "%cmp358") "if.end378" "if.then372" }

theorem ifEnd369Block_find :
    stage2NoEventBody.findBlock "if.end369" = some ifEnd369Block := by
  decide

/-- `if.end378`'s seven instructions. -/
def ifEnd378Instrs : List Instr :=
  [ Instr.binop "%inc379" BinOp.add 64 (Operand.reg "%k.6")
      (Operand.imm (.int 64 (BitVec.ofNat 64 1))),
    Instr.gep "%arrayidx380" (Ty.int 32) (Operand.reg "%ep") (Operand.reg "%k.6"),
    Instr.load "%52" (Ty.int 32) (Operand.reg "%arrayidx380"),
    Instr.icmp "%cmp382" IPred.eq 8 (Operand.reg "%frame.6")
      (Operand.imm (.int 8 (BitVec.ofNat 8 0))),
    Instr.zext "%idxprom385" 32 64 (Operand.reg "%52"),
    Instr.gep "%arrayidx386" (Ty.int 8) (Operand.reg "%b")
      (Operand.reg "%idxprom385"),
    Instr.load "%53" (Ty.int 8) (Operand.reg "%arrayidx386") ]

/-- `if.end378`, pinned. -/
def ifEnd378Block : Block :=
  { name := "if.end378", instrs := ifEnd378Instrs,
    term := Term.condbr (Operand.reg "%cmp382") "if.then384" "if.end410" }

theorem ifEnd378Block_find :
    stage2NoEventBody.findBlock "if.end378" = some ifEnd378Block := by
  decide

/-- `if.end410`: the hand-off to the deep-dispatch root. -/
def ifEnd410Block : Block :=
  { name := "if.end410", instrs := [], term := Term.br "NodeBlock41" }

theorem ifEnd410Block_find :
    stage2NoEventBody.findBlock "if.end410" = some ifEnd410Block := by
  decide

/-- `NodeBlock41`: the byte against 93. -/
def nodeBlock41Instrs : List Instr :=
  [ Instr.icmp "%Pivot42" IPred.slt 8 (Operand.reg "%53")
      (Operand.imm (.int 8 (BitVec.ofNat 8 93))) ]

/-- `NodeBlock41`, pinned. -/
def nodeBlock41Block : Block :=
  { name := "NodeBlock41", instrs := nodeBlock41Instrs,
    term := Term.condbr (Operand.reg "%Pivot42") "LeafBlock37" "LeafBlock39" }

theorem nodeBlock41Block_find :
    stage2NoEventBody.findBlock "NodeBlock41" = some nodeBlock41Block := by
  decide

/-- `LeafBlock37`: the byte against 44. -/
def leafBlock37Instrs : List Instr :=
  [ Instr.icmp "%SwitchLeaf38" IPred.eq 8 (Operand.reg "%53")
      (Operand.imm (.int 8 (BitVec.ofNat 8 44))) ]

/-- `NodeBlock41`'s cell: the byte `,` is below 93. -/
def nodeBlock41Cells : List (String × Value) := [("%Pivot42", .int 1 1)]

/-- `LeafBlock37`'s cell: the byte is `,`. -/
def leafBlock37Cells : List (String × Value) := [("%SwitchLeaf38", .int 1 1)]

/-- **`NodeBlock41`'s test**, at the byte `,`. -/
theorem nodeBlock41_denote (calls : Calls) (env : Env) (s : State)
    (h53 : lookupName env "%53" = some (.int 8 (BitVec.ofNat 8 44))) :
    denoteCode calls nodeBlock41Instrs (stateAt env s) =
      some (stateAt (cells nodeBlock41Cells env) s) := by
  rw [nodeBlock41Instrs]
  rw [stage2NoEventWalk_denote_icmp_imm (calls := calls) (env := env) (s := s)
    (d := "%Pivot42") (a := "%53") (p := .slt) (w := 8)
    (x := BitVec.ofNat 8 44) (c := BitVec.ofNat 8 93) ?_ (is := [])]
  · rw [show evalICmp .slt (BitVec.ofNat 8 44) (BitVec.ofNat 8 93) = 1 from by decide]
    simp only [nodeBlock41Cells, cells, denoteCode_nil]
  · cycle_lk

/-- **`LeafBlock37`'s test**, at the byte `,`. -/
theorem leafBlock37_denote (calls : Calls) (env : Env) (s : State)
    (h53 : lookupName env "%53" = some (.int 8 (BitVec.ofNat 8 44))) :
    denoteCode calls leafBlock37Instrs (stateAt env s) =
      some (stateAt (cells leafBlock37Cells env) s) := by
  rw [leafBlock37Instrs]
  rw [stage2NoEventWalk_denote_icmp_imm (calls := calls) (env := env) (s := s)
    (d := "%SwitchLeaf38") (a := "%53") (p := .eq) (w := 8)
    (x := BitVec.ofNat 8 44) (c := BitVec.ofNat 8 44) ?_ (is := [])]
  · rw [show evalICmp .eq (BitVec.ofNat 8 44) (BitVec.ofNat 8 44) = 1 from by decide]
    simp only [leafBlock37Cells, cells, denoteCode_nil]
  · cycle_lk

/-- `LeafBlock37`, pinned. -/
def leafBlock37Block : Block :=
  { name := "LeafBlock37", instrs := leafBlock37Instrs,
    term := Term.condbr (Operand.reg "%SwitchLeaf38") "value.outer.backedge"
      "if.then428" }

theorem leafBlock37Block_find :
    stage2NoEventBody.findBlock "LeafBlock37" = some leafBlock37Block := by
  decide

/-- The `if.end378` cells, newest first. -/
def ifEnd378Cells (ep b lane k _fr : Nat) (byte : UInt8) :
    List (String × Value) :=
  [("%53", .int 8 (BitVec.ofNat 8 byte.toNat)),
   ("%arrayidx386", .ptr (b + lane)),
   ("%idxprom385", .int 64 (BitVec.ofNat 64 lane)),
   ("%cmp382", .int 1 0),
   ("%52", .int 32 (BitVec.ofNat 32 lane)),
   ("%arrayidx380", .ptr (ep + 4 * k)),
   ("%inc379", .int 64 (BitVec.ofNat 64 (k + 1)))]

/-- **`if.end378`'s run**, at the entry's lane and the document's byte. -/
theorem ifEnd378_denote (calls : Calls) (env : Env) (s : State)
    {ep b lane k fr : Nat} {byte : UInt8} {bs4 : List UInt8}
    (hk : lookupName env "%k.6" = some (.int 64 (BitVec.ofNat 64 k)))
    (hep : lookupName env "%ep" = some (.ptr ep))
    (hb : lookupName env "%b" = some (.ptr b))
    (hframe : lookupName env "%frame.6" = some (.int 8 (BitVec.ofNat 8 fr)))
    (hkLt : k < 2 ^ 63) (hfrLt : fr < 2 ^ 8) (hfrNe : fr ≠ 0)
    (hbs : bytesToNat bs4 = lane) (hLaneLt : lane < 2 ^ 32)
    (hlane : readBytes s.mem (ep + 4 * k) 4 = some bs4)
    (hbyte : readBytes s.mem (b + lane) 1 = some [byte]) :
    denoteCode calls ifEnd378Instrs (stateAt env s) =
      some (stateAt (cells (ifEnd378Cells ep b lane k fr byte) env) s) := by
  rw [ifEnd378Instrs]
  rw [stage2NoEventWalk_denote_add_imm_w (calls := calls) (env := env) (s := s)
    (d := "%inc379") (a := "%k.6") (w := 64) (x := BitVec.ofNat 64 k)
    (c := BitVec.ofNat 64 1) ?_
    (is := [Instr.gep "%arrayidx380" (Ty.int 32) (Operand.reg "%ep")
        (Operand.reg "%k.6"),
      Instr.load "%52" (Ty.int 32) (Operand.reg "%arrayidx380"),
      Instr.icmp "%cmp382" IPred.eq 8 (Operand.reg "%frame.6")
        (Operand.imm (.int 8 (BitVec.ofNat 8 0))),
      Instr.zext "%idxprom385" 32 64 (Operand.reg "%52"),
      Instr.gep "%arrayidx386" (Ty.int 8) (Operand.reg "%b")
        (Operand.reg "%idxprom385"),
      Instr.load "%53" (Ty.int 8) (Operand.reg "%arrayidx386")])]
  all_goals cycle_lk
  rw [show BitVec.ofNat 64 k + BitVec.ofNat 64 1 = BitVec.ofNat 64 (k + 1) from
    stage2NoEventOfNatSucc (by omega)]
  rw [stage2NoEventWalk_denote_gep32 (calls := calls)
    (env := ("%inc379", Value.int 64 (BitVec.ofNat 64 (k + 1))) :: env) (s := s)
    (d := "%arrayidx380") (base := "%ep") (off := "%k.6") (a := ep)
    (o := BitVec.ofNat 64 k) ?_ ?_
    (by rw [stage2NoEventSignExtend_toNat (by omega)]; omega)
    (is := [Instr.load "%52" (Ty.int 32) (Operand.reg "%arrayidx380"),
      Instr.icmp "%cmp382" IPred.eq 8 (Operand.reg "%frame.6")
        (Operand.imm (.int 8 (BitVec.ofNat 8 0))),
      Instr.zext "%idxprom385" 32 64 (Operand.reg "%52"),
      Instr.gep "%arrayidx386" (Ty.int 8) (Operand.reg "%b")
        (Operand.reg "%idxprom385"),
      Instr.load "%53" (Ty.int 8) (Operand.reg "%arrayidx386")])]
  all_goals cycle_lk
  rw [show ep + ((BitVec.ofNat 64 k).signExtend 64).toNat * 4 = ep + 4 * k from by
    rw [stage2NoEventSignExtend_toNat (by omega), Nat.mul_comm]]
  rw [stage2NoEventWalk_denote_load_int (calls := calls)
    (env := ("%arrayidx380", Value.ptr (ep + 4 * k)) ::
      ("%inc379", Value.int 64 (BitVec.ofNat 64 (k + 1))) :: env) (s := s)
    (d := "%52") (p := "%arrayidx380") (w := 32) (a := ep + 4 * k) (bs := bs4)
    (by decide) ?_ hlane
    (is := [Instr.icmp "%cmp382" IPred.eq 8 (Operand.reg "%frame.6")
        (Operand.imm (.int 8 (BitVec.ofNat 8 0))),
      Instr.zext "%idxprom385" 32 64 (Operand.reg "%52"),
      Instr.gep "%arrayidx386" (Ty.int 8) (Operand.reg "%b")
        (Operand.reg "%idxprom385"),
      Instr.load "%53" (Ty.int 8) (Operand.reg "%arrayidx386")])]
  all_goals cycle_lk
  rw [hbs]
  rw [stage2NoEventWalk_denote_icmp_imm (calls := calls)
    (env := ("%52", Value.int 32 (BitVec.ofNat 32 lane)) ::
      ("%arrayidx380", Value.ptr (ep + 4 * k)) ::
      ("%inc379", Value.int 64 (BitVec.ofNat 64 (k + 1))) :: env) (s := s)
    (d := "%cmp382") (a := "%frame.6") (p := .eq) (w := 8)
    (x := BitVec.ofNat 8 fr) (c := BitVec.ofNat 8 0) ?_
    (is := [Instr.zext "%idxprom385" 32 64 (Operand.reg "%52"),
      Instr.gep "%arrayidx386" (Ty.int 8) (Operand.reg "%b")
        (Operand.reg "%idxprom385"),
      Instr.load "%53" (Ty.int 8) (Operand.reg "%arrayidx386")])]
  all_goals cycle_lk
  rw [stage2NoEventICmp_eq_zero (x := BitVec.ofNat 8 fr)
    (c := BitVec.ofNat 8 0) (stage2NoEventOfNat8_ne hfrLt hfrNe)]
  rw [denoteCode_zext (calls := calls)
    (env := ("%cmp382", Value.int 1 (0 : BitVec 1)) ::
      ("%52", Value.int 32 (BitVec.ofNat 32 lane)) ::
      ("%arrayidx380", Value.ptr (ep + 4 * k)) ::
      ("%inc379", Value.int 64 (BitVec.ofNat 64 (k + 1))) :: env)
    (s := s) (d := "%idxprom385")
    (v := "%52") (wIn := 32) (wOut := 64) (x := BitVec.ofNat 32 lane) ?_
    (is := [Instr.gep "%arrayidx386" (Ty.int 8) (Operand.reg "%b")
        (Operand.reg "%idxprom385"),
      Instr.load "%53" (Ty.int 8) (Operand.reg "%arrayidx386")])]
  all_goals cycle_lk
  rw [stage2NoEventOfNat64_ofNat32 hLaneLt]
  rw [denoteCode_gep8_reg (calls := calls)
    (env := ("%idxprom385", Value.int 64 (BitVec.ofNat 64 lane)) ::
      ("%cmp382", Value.int 1 (0 : BitVec 1)) ::
      ("%52", Value.int 32 (BitVec.ofNat 32 lane)) ::
      ("%arrayidx380", Value.ptr (ep + 4 * k)) ::
      ("%inc379", Value.int 64 (BitVec.ofNat 64 (k + 1))) :: env)
    (s := s) (d := "%arrayidx386") (base := "%b") (off := "%idxprom385") (a := b)
    (idx := BitVec.ofNat 64 lane) ?_ ?_
    (stage2NoEventLane_signExtend_lt hLaneLt)
    (is := [Instr.load "%53" (Ty.int 8) (Operand.reg "%arrayidx386")])]
  all_goals cycle_lk
  rw [stage2NoEventSignExtend_toNat (by omega)]
  rw [stage2NoEventWalk_denote_load_int (calls := calls)
    (env := ("%arrayidx386", Value.ptr (b + lane)) ::
      ("%idxprom385", Value.int 64 (BitVec.ofNat 64 lane)) ::
      ("%cmp382", Value.int 1 (0 : BitVec 1)) ::
      ("%52", Value.int 32 (BitVec.ofNat 32 lane)) ::
      ("%arrayidx380", Value.ptr (ep + 4 * k)) ::
      ("%inc379", Value.int 64 (BitVec.ofNat 64 (k + 1))) :: env) (s := s)
    (d := "%53") (p := "%arrayidx386") (w := 8) (a := b + lane) (bs := [byte])
    (by decide) (by cycle_lk) hbyte (is := [])]
  rw [stage2NoEventBytesToNat_singleton]
  simp only [ifEnd378Cells, cells, denoteCode_nil]

/-! ### `value.outer.backedge`

The backedge's `phi` run is the edge's, so it is a hypothesis; the five computed
cells after it are the edge's `phi` cells' own readings. -/

/-- The backedge's seven `phi`s, in the order the block writes them. -/
def outerBackedgePhiSpecs : List PhiSpec :=
  [ ⟨"%frame.0.ph.be", Ty.int 8,
      [("LeafBlock37", .reg "%frame.6"), ("if.end303", .imm (.int 8 (BitVec.ofNat 8 0)))]⟩,
    ⟨"%sp.0.ph.be", Ty.int 32,
      [("LeafBlock37", .reg "%sp.4"), ("if.end303", .reg "%sp.1")]⟩,
    ⟨"%k.0.ph.be", Ty.int 64,
      [("LeafBlock37", .reg "%inc379"), ("if.end303", .reg "%inc304")]⟩,
    ⟨"%alen.0.ph.be", Ty.int 64,
      [("LeafBlock37", .reg "%alen.8"), ("if.end303", .reg "%alen.2")]⟩,
    ⟨"%arena.0.ph.be", Ty.int 64,
      [("LeafBlock37", .reg "%arena.10"), ("if.end303", .reg "%arena.3")]⟩,
    ⟨"%terms.0.ph.be", Ty.int 64,
      [("LeafBlock37", .reg "%terms.8"), ("if.end303", .reg "%terms.2")]⟩,
    ⟨"%tokens.0.ph.be", Ty.int 64,
      [("LeafBlock37", .reg "%tokens.8"), ("if.end303", .reg "%tokens.2")]⟩ ]

/-- The backedge's `phi` run, as instructions. -/
def outerBackedgePhiInstrs : List Instr := outerBackedgePhiSpecs.map PhiSpec.instr

/-- The backedge's five computed cells. -/
def outerBackedgeTailInstrs : List Instr :=
  [ Instr.zext "%45" 32 64 (Operand.reg "%sp.0.ph.be"),
    Instr.icmp "%umax.max" IPred.ugt 32 (Operand.reg "%sp.0.ph.be")
      (Operand.imm (.int 32 (BitVec.ofNat 32 520))),
    Instr.select "%umax" (Ty.int 32) (Operand.reg "%umax.max")
      (Operand.reg "%sp.0.ph.be") (Operand.imm (.int 32 (BitVec.ofNat 32 520))),
    Instr.zext "%wide.trip.count" 32 64 (Operand.reg "%umax"),
    Instr.icmp "%cmp.not.peel" IPred.ult 64 (Operand.reg "%k.0.ph.be")
      (Operand.reg "%nep") ]

/-- `value.outer.backedge`, pinned. -/
def outerBackedgeBlock : Block :=
  { name := "value.outer.backedge",
    instrs := outerBackedgePhiInstrs ++ outerBackedgeTailInstrs,
    term := Term.condbr (Operand.reg "%cmp.not.peel") "if.end.peel" "if.then" }

theorem outerBackedgeBlock_find :
    stage2NoEventBody.findBlock "value.outer.backedge" = some outerBackedgeBlock := by
  decide

/-- The backedge `phi` run's cells, newest first. -/
def outerBackedgePhiCells (fr sp k alen arena terms tok : Nat) :
    List (String × Value) :=
  [("%tokens.0.ph.be", .int 64 (BitVec.ofNat 64 tok)),
   ("%terms.0.ph.be", .int 64 (BitVec.ofNat 64 terms)),
   ("%arena.0.ph.be", .int 64 (BitVec.ofNat 64 arena)),
   ("%alen.0.ph.be", .int 64 (BitVec.ofNat 64 alen)),
   ("%k.0.ph.be", .int 64 (BitVec.ofNat 64 k)),
   ("%sp.0.ph.be", .int 32 (BitVec.ofNat 32 sp)),
   ("%frame.0.ph.be", .int 8 (BitVec.ofNat 8 fr))]

/-- The backedge's tail cells, newest first.  The two stack words are written as
the head's `phi` layer wants them: the depth and the `520`-budgeted trip count. -/
def outerBackedgeTailCells (sp _k : Nat) : List (String × Value) :=
  [("%cmp.not.peel", .int 1 1),
   ("%wide.trip.count", .int 64 (BitVec.ofNat 64 (max sp 520))),
   ("%umax", .int 32 (BitVec.ofNat 32 (max sp 520))),
   ("%umax.max", .int 1 (if 520 < sp then 1 else 0)),
   ("%45", .int 64 (BitVec.ofNat 64 sp))]

/-- The backedge `phi` run's binding, at the seven values the edge supplies. -/
theorem outerBackedge_phi_denote {calls : Calls} {env : Env} {s : State} {p : String}
    {fr sp k alen arena terms tok : Nat}
    (hpre : s.pre = some p)
    (hsel : PhiSelects (stateAt env s) p outerBackedgePhiSpecs
      [("%frame.0.ph.be", .int 8 (BitVec.ofNat 8 fr)),
       ("%sp.0.ph.be", .int 32 (BitVec.ofNat 32 sp)),
       ("%k.0.ph.be", .int 64 (BitVec.ofNat 64 k)),
       ("%alen.0.ph.be", .int 64 (BitVec.ofNat 64 alen)),
       ("%arena.0.ph.be", .int 64 (BitVec.ofNat 64 arena)),
       ("%terms.0.ph.be", .int 64 (BitVec.ofNat 64 terms)),
       ("%tokens.0.ph.be", .int 64 (BitVec.ofNat 64 tok))]) :
    denoteCode calls outerBackedgePhiInstrs (stateAt env s) =
      some (stateAt (cells (outerBackedgePhiCells fr sp k alen arena terms tok) env)
        s) := by
  rw [outerBackedgePhiInstrs,
    ← List.append_nil (List.map PhiSpec.instr outerBackedgePhiSpecs),
    denoteCode_phiRun (s := stateAt env s) (p := p) (specs := outerBackedgePhiSpecs)
      (vs := _) (rest := []) hpre hsel (by decide)]
  simp only [stateAt_bindAll_runCells, outerBackedgePhiCells, runCells, cells]
  rfl

/-- The backedge's five computed cells, from its `phi` cells. -/
theorem outerBackedge_tail_denote (calls : Calls) (env : Env) (s : State)
    {sp k nep : Nat}
    (hsp : lookupName env "%sp.0.ph.be" = some (.int 32 (BitVec.ofNat 32 sp)))
    (hk : lookupName env "%k.0.ph.be" = some (.int 64 (BitVec.ofNat 64 k)))
    (hnep : lookupName env "%nep" = some (.int 64 (BitVec.ofNat 64 nep)))
    (hspLt : sp < 2 ^ 32) (hk'Lt : k < nep) (hnepLt : nep < 2 ^ 64) :
    denoteCode calls outerBackedgeTailInstrs (stateAt env s) =
      some (stateAt (cells (outerBackedgeTailCells sp k) env) s) := by
  have hkLt : k < 2 ^ 64 := by omega
  rw [outerBackedgeTailInstrs]
  rw [denoteCode_zext (calls := calls) (env := env) (s := s) (d := "%45")
    (v := "%sp.0.ph.be") (wIn := 32) (wOut := 64) (x := BitVec.ofNat 32 sp) ?_
    (is := [Instr.icmp "%umax.max" IPred.ugt 32 (Operand.reg "%sp.0.ph.be")
        (Operand.imm (.int 32 (BitVec.ofNat 32 520))),
      Instr.select "%umax" (Ty.int 32) (Operand.reg "%umax.max")
        (Operand.reg "%sp.0.ph.be") (Operand.imm (.int 32 (BitVec.ofNat 32 520))),
      Instr.zext "%wide.trip.count" 32 64 (Operand.reg "%umax"),
      Instr.icmp "%cmp.not.peel" IPred.ult 64 (Operand.reg "%k.0.ph.be")
        (Operand.reg "%nep")])]
  all_goals cycle_lk
  rw [stage2NoEventOfNat64_ofNat32 hspLt]
  rw [stage2NoEventWalk_denote_icmp_imm (calls := calls)
    (env := ("%45", Value.int 64 (BitVec.ofNat 64 sp)) :: env) (s := s)
    (d := "%umax.max") (a := "%sp.0.ph.be") (p := .ugt) (w := 32)
    (x := BitVec.ofNat 32 sp) (c := BitVec.ofNat 32 520) ?_
    (is := [Instr.select "%umax" (Ty.int 32) (Operand.reg "%umax.max")
        (Operand.reg "%sp.0.ph.be") (Operand.imm (.int 32 (BitVec.ofNat 32 520))),
      Instr.zext "%wide.trip.count" 32 64 (Operand.reg "%umax"),
      Instr.icmp "%cmp.not.peel" IPred.ult 64 (Operand.reg "%k.0.ph.be")
        (Operand.reg "%nep")])]
  all_goals cycle_lk
  have hugt : evalICmp .ugt (BitVec.ofNat 32 sp) (BitVec.ofNat 32 520) =
      (if 520 < sp then (1 : BitVec 1) else 0) := by
    by_cases h : 520 < sp
    · rw [ite_eq_left h]
      exact stage2NoEventICmp_ugt_one hspLt (by decide) h
    · rw [ite_eq_right h]
      exact stage2NoEventICmp_ugt_zero hspLt (by decide) (by omega)
  rw [hugt]
  rw [stage2NoEventDenoteSelect32 (calls := calls)
    (env := ("%umax.max", Value.int 1 (if 520 < sp then (1 : BitVec 1) else 0)) ::
      ("%45", Value.int 64 (BitVec.ofNat 64 sp)) :: env) (s := s)
    (d := "%umax") (c := "%umax.max") (a := "%sp.0.ph.be")
    (bb := (if 520 < sp then (1 : BitVec 1) else 0)) (x := BitVec.ofNat 32 sp)
    (y := BitVec.ofNat 32 520) ?_ ?_
    (is := [Instr.zext "%wide.trip.count" 32 64 (Operand.reg "%umax"),
      Instr.icmp "%cmp.not.peel" IPred.ult 64 (Operand.reg "%k.0.ph.be")
        (Operand.reg "%nep")])]
  all_goals cycle_lk
  have hmax : (if (if 520 < sp then (1 : BitVec 1) else 0) = 1 then
      BitVec.ofNat 32 sp else BitVec.ofNat 32 520) =
      BitVec.ofNat 32 (max sp 520) := by
    by_cases h : 520 < sp
    · rw [ite_eq_left h, ite_eq_left rfl, Nat.max_eq_left (by omega)]
    · rw [ite_eq_right h, ite_eq_right (by decide), Nat.max_eq_right (by omega)]
  rw [hmax]
  rw [denoteCode_zext (calls := calls)
    (env := ("%umax", Value.int 32 (BitVec.ofNat 32 (max sp 520))) ::
      ("%umax.max", Value.int 1 (if 520 < sp then (1 : BitVec 1) else 0)) ::
      ("%45", Value.int 64 (BitVec.ofNat 64 sp)) :: env)
    (s := s) (d := "%wide.trip.count")
    (v := "%umax") (wIn := 32) (wOut := 64) (x := BitVec.ofNat 32 (max sp 520)) ?_
    (is := [Instr.icmp "%cmp.not.peel" IPred.ult 64 (Operand.reg "%k.0.ph.be")
        (Operand.reg "%nep")])]
  all_goals cycle_lk
  rw [stage2NoEventOfNat64_ofNat32 (by omega)]
  rw [denoteCode_icmp_ult_reg (calls := calls)
    (env := ("%wide.trip.count", Value.int 64 (BitVec.ofNat 64 (max sp 520))) ::
      ("%umax", Value.int 32 (BitVec.ofNat 32 (max sp 520))) ::
      ("%umax.max", Value.int 1 (if 520 < sp then (1 : BitVec 1) else 0)) ::
      ("%45", Value.int 64 (BitVec.ofNat 64 sp)) :: env) (s := s)
    (d := "%cmp.not.peel") (a := "%k.0.ph.be") (b := "%nep")
    (x := BitVec.ofNat 64 k) (y := BitVec.ofNat 64 nep) ?_ ?_ (is := [])]
  all_goals cycle_lk
  rw [stage2NoEventICmp_ult_one (w := 64) (x := k) (y := nep) hkLt hnepLt hk'Lt]
  simp only [outerBackedgeTailCells, cells, denoteCode_nil]

/-- The backedge `phi` run at `LeafBlock37`'s edge, from that edge's registers. -/
theorem outerBackedge_phi_leaf_denote {calls : Calls} {env : Env} {s : State}
    {fr sp k alen arena terms tok : Nat}
    (hpre : s.pre = some "LeafBlock37")
    (hframe : lookupName env "%frame.6" = some (.int 8 (BitVec.ofNat 8 fr)))
    (hspc : lookupName env "%sp.4" = some (.int 32 (BitVec.ofNat 32 sp)))
    (hkc : lookupName env "%inc379" = some (.int 64 (BitVec.ofNat 64 k)))
    (halen : lookupName env "%alen.8" = some (.int 64 (BitVec.ofNat 64 alen)))
    (harena : lookupName env "%arena.10" = some (.int 64 (BitVec.ofNat 64 arena)))
    (hterms : lookupName env "%terms.8" = some (.int 64 (BitVec.ofNat 64 terms)))
    (htok : lookupName env "%tokens.8" = some (.int 64 (BitVec.ofNat 64 tok))) :
    denoteCode calls outerBackedgePhiInstrs (stateAt env s) =
      some (stateAt (cells (outerBackedgePhiCells fr sp k alen arena terms tok) env)
        s) := by
  have hsel : PhiSelects (stateAt env s) "LeafBlock37" outerBackedgePhiSpecs
      [("%frame.0.ph.be", .int 8 (BitVec.ofNat 8 fr)),
       ("%sp.0.ph.be", .int 32 (BitVec.ofNat 32 sp)),
       ("%k.0.ph.be", .int 64 (BitVec.ofNat 64 k)),
       ("%alen.0.ph.be", .int 64 (BitVec.ofNat 64 alen)),
       ("%arena.0.ph.be", .int 64 (BitVec.ofNat 64 arena)),
       ("%terms.0.ph.be", .int 64 (BitVec.ofNat 64 terms)),
       ("%tokens.0.ph.be", .int 64 (BitVec.ofNat 64 tok))] := by
    refine PhiSelects.cons (op := .reg "%frame.6") (by decide) ?_
      (PhiSelects.cons (op := .reg "%sp.4") (by decide) ?_
        (PhiSelects.cons (op := .reg "%inc379") (by decide) ?_
          (PhiSelects.cons (op := .reg "%alen.8") (by decide) ?_
            (PhiSelects.cons (op := .reg "%arena.10") (by decide) ?_
              (PhiSelects.cons (op := .reg "%terms.8") (by decide) ?_
                (PhiSelects.cons (op := .reg "%tokens.8") (by decide) ?_
                  PhiSelects.nil))))))
    all_goals
      simp only [stateAt, evalOperand, hframe, hspc, hkc, halen, harena, hterms, htok]
  rw [outerBackedgePhiInstrs,
    ← List.append_nil (List.map PhiSpec.instr outerBackedgePhiSpecs),
    denoteCode_phiRun (s := stateAt env s) (p := "LeafBlock37")
      (specs := outerBackedgePhiSpecs) (vs := _) (rest := []) hpre hsel (by decide)]
  simp only [stateAt_bindAll_runCells, outerBackedgePhiCells, runCells, cells]
  rfl

/-- **`value.outer.backedge`'s run at `LeafBlock37`'s edge**: its `phi` run and
its five computed cells. -/
theorem outerBackedge_leaf_denote {calls : Calls} {env : Env} {s : State}
    {fr sp k alen arena terms tok nep : Nat}
    (hpre : s.pre = some "LeafBlock37")
    (hframe : lookupName env "%frame.6" = some (.int 8 (BitVec.ofNat 8 fr)))
    (hspc : lookupName env "%sp.4" = some (.int 32 (BitVec.ofNat 32 sp)))
    (hkc : lookupName env "%inc379" = some (.int 64 (BitVec.ofNat 64 k)))
    (halen : lookupName env "%alen.8" = some (.int 64 (BitVec.ofNat 64 alen)))
    (harena : lookupName env "%arena.10" = some (.int 64 (BitVec.ofNat 64 arena)))
    (hterms : lookupName env "%terms.8" = some (.int 64 (BitVec.ofNat 64 terms)))
    (htok : lookupName env "%tokens.8" = some (.int 64 (BitVec.ofNat 64 tok)))
    (hnep : lookupName env "%nep" = some (.int 64 (BitVec.ofNat 64 nep)))
    (hspLt : sp < 2 ^ 32) (hk'Lt : k < nep) (hnepLt : nep < 2 ^ 64) :
    denoteCode calls outerBackedgeBlock.instrs (stateAt env s) =
      some (stateAt
        (cells (outerBackedgeTailCells sp k)
          (cells (outerBackedgePhiCells fr sp k alen arena terms tok) env)) s) := by
  have hphi := outerBackedge_phi_leaf_denote (calls := calls) (env := env) (s := s)
    (fr := fr) (sp := sp) (k := k) (alen := alen) (arena := arena) (terms := terms)
    (tok := tok) hpre hframe hspc hkc halen harena hterms htok
  rw [outerBackedgeBlock]
  rw [denoteCode_append_apply (a := outerBackedgePhiInstrs)
    (b := outerBackedgeTailInstrs) (s := stateAt env s)
    (s' := stateAt (cells (outerBackedgePhiCells fr sp k alen arena terms tok) env) s)
    hphi (by decide)]
  rw [outerBackedge_tail_denote (calls := calls)
    (env := cells (outerBackedgePhiCells fr sp k alen arena terms tok) env) (s := s)
    (sp := sp) (k := k) (nep := nep)
    (by
      exact cells_lookup_of_mem _ _ (by simp [outerBackedgePhiCells]) (by
        rw [show (outerBackedgePhiCells fr sp k alen arena terms tok).map (·.1) =
          ["%tokens.0.ph.be", "%terms.0.ph.be", "%arena.0.ph.be", "%alen.0.ph.be",
            "%k.0.ph.be", "%sp.0.ph.be", "%frame.0.ph.be"] from rfl]
        decide))
    (by
      exact cells_lookup_of_mem _ _ (by simp [outerBackedgePhiCells]) (by
        rw [show (outerBackedgePhiCells fr sp k alen arena terms tok).map (·.1) =
          ["%tokens.0.ph.be", "%terms.0.ph.be", "%arena.0.ph.be", "%alen.0.ph.be",
            "%k.0.ph.be", "%sp.0.ph.be", "%frame.0.ph.be"] from rfl]
        decide))
    (by
      rw [cells_lookup_of_notin _ _ (by
        rw [show (outerBackedgePhiCells fr sp k alen arena terms tok).map (·.1) =
          ["%tokens.0.ph.be", "%terms.0.ph.be", "%arena.0.ph.be", "%alen.0.ph.be",
            "%k.0.ph.be", "%sp.0.ph.be", "%frame.0.ph.be"] from rfl]
        decide)]
      exact hnep)
    hspLt hk'Lt hnepLt]


/-! ### The head's `phi` run at the backedge edge, and its read row -/

/-- The head's nine `phi`s at the `value.outer.backedge` edge. -/
theorem loopHeadBackedge_phi_denote {calls : Calls} {env : Env} {s : State}
    {K : Stage2NoEventWalkCarry} {k sp fr wide : Nat}
    (hpre : s.pre = some "value.outer.backedge")
    (hwide : lookupName env "%wide.trip.count" =
      some (.int 64 (BitVec.ofNat 64 wide)))
    (hone : lookupName env "%45" = some (.int 64 (BitVec.ofNat 64 sp)))
    (htok : lookupName env "%tokens.0.ph.be" =
      some (.int 64 (BitVec.ofNat 64 K.tok)))
    (hterms : lookupName env "%terms.0.ph.be" =
      some (.int 64 (BitVec.ofNat 64 K.terms)))
    (harena : lookupName env "%arena.0.ph.be" =
      some (.int 64 (BitVec.ofNat 64 K.arenaWord)))
    (halen : lookupName env "%alen.0.ph.be" =
      some (.int 64 (BitVec.ofNat 64 K.arena.length)))
    (hk : lookupName env "%k.0.ph.be" =
      some (.int 64 (BitVec.ofNat 64 k)))
    (hsp : lookupName env "%sp.0.ph.be" =
      some (.int 32 (BitVec.ofNat 32 sp)))
    (hfr : lookupName env "%frame.0.ph.be" =
      some (.int 8 (BitVec.ofNat 8 fr))) :
    denoteCode calls loopHeadPhiInstrs (stateAt env s) =
      some (stateAt (cells (loopHeadPhiCellsAt K k sp fr sp wide) env) s) := by
  have hsel : PhiSelects (stateAt env s) "value.outer.backedge" loopHeadPhiSpecs
      [("%wide.trip.count1409", .int 64 (BitVec.ofNat 64 wide)),
       ("%1", .int 64 (BitVec.ofNat 64 sp)),
       ("%tokens.0.ph1408", .int 64 (BitVec.ofNat 64 K.tok)),
       ("%terms.0.ph1407", .int 64 (BitVec.ofNat 64 K.terms)),
       ("%arena.0.ph1406", .int 64 (BitVec.ofNat 64 K.arenaWord)),
       ("%alen.0.ph1405", .int 64 (BitVec.ofNat 64 K.arena.length)),
       ("%k.0.ph1404", .int 64 (BitVec.ofNat 64 k)),
       ("%sp.0.ph1403", .int 32 (BitVec.ofNat 32 sp)),
       ("%frame.0.ph1402", .int 8 (BitVec.ofNat 8 fr))] := by
    refine PhiSelects.cons (op := .reg "%wide.trip.count") (by decide) ?_
      (PhiSelects.cons (op := .reg "%45") (by decide) ?_
        (PhiSelects.cons (op := .reg "%tokens.0.ph.be") (by decide) ?_
          (PhiSelects.cons (op := .reg "%terms.0.ph.be") (by decide) ?_
            (PhiSelects.cons (op := .reg "%arena.0.ph.be") (by decide) ?_
              (PhiSelects.cons (op := .reg "%alen.0.ph.be") (by decide) ?_
                (PhiSelects.cons (op := .reg "%k.0.ph.be") (by decide) ?_
                  (PhiSelects.cons (op := .reg "%sp.0.ph.be") (by decide) ?_
                    (PhiSelects.cons (op := .reg "%frame.0.ph.be") (by decide) ?_
                      PhiSelects.nil))))))))
    all_goals simp only [stateAt, evalOperand, hwide, hone, htok, hterms, harena,
      halen, hk, hsp, hfr]
  rw [loopHeadPhi_eq,
    ← List.append_nil (List.map PhiSpec.instr loopHeadPhiSpecs),
    denoteCode_phiRun (s := stateAt env s) (p := "value.outer.backedge")
      (specs := loopHeadPhiSpecs) (vs := _) (rest := []) hpre hsel (by decide)]
  simp only [stateAt_bindAll_runCells, loopHeadPhiCellsAt, runCells, cells]
  rfl

/-- **The head's read row at the backedge edge.** -/
theorem loopHeadBackedge_read_denote (calls : Calls) (env : Env) (s : State)
    {K : Stage2NoEventWalkCarry} {k sp fr wide lane : Nat} {bs4 : List UInt8}
    {byte : UInt8}
    (hk : lookupName env "%k.0.ph1404" = some (.int 64 (BitVec.ofNat 64 k)))
    (hep : lookupName env "%ep" = some (.ptr K.ep))
    (hb : lookupName env "%b" = some (.ptr K.b))
    (hkLt : k < 2 ^ 63) (hbs : bytesToNat bs4 = lane)
    (hLaneLt : lane < 2 ^ 32)
    (hlane : readBytes s.mem (K.ep + 4 * k) 4 = some bs4)
    (hbyte : readBytes s.mem (K.b + lane) 1 = some [byte]) :
    denoteCode calls loopHeadReadInstrs (stateAt env s) =
      some (stateAt (cells (loopHeadReadCellsAt K k sp fr sp wide lane byte) env)
        s) := by
  rw [loopHeadReadInstrs]
  rw [stage2NoEventWalk_denote_add_imm_w (calls := calls) (env := env) (s := s)
    (d := "%inc.peel") (a := "%k.0.ph1404") (w := 64) (x := BitVec.ofNat 64 k)
    (c := BitVec.ofNat 64 1) ?_
    (is := [Instr.gep "%arrayidx.peel" (Ty.int 32) (Operand.reg "%ep")
        (Operand.reg "%k.0.ph1404"),
      Instr.load "%2" (Ty.int 32) (Operand.reg "%arrayidx.peel"),
      Instr.zext "%idxprom.peel" 32 64 (Operand.reg "%2"),
      Instr.gep "%arrayidx6.peel" (Ty.int 8) (Operand.reg "%b")
        (Operand.reg "%idxprom.peel"),
      Instr.load "%3" (Ty.int 8) (Operand.reg "%arrayidx6.peel")])]
  all_goals cycle_lk
  rw [show BitVec.ofNat 64 k + BitVec.ofNat 64 1 = BitVec.ofNat 64 (k + 1) from
    stage2NoEventOfNatSucc (by omega)]
  rw [stage2NoEventWalk_denote_gep32 (calls := calls)
    (env := ("%inc.peel", Value.int 64 (BitVec.ofNat 64 (k + 1))) :: env) (s := s)
    (d := "%arrayidx.peel") (base := "%ep") (off := "%k.0.ph1404") (a := K.ep)
    (o := BitVec.ofNat 64 k) ?_ ?_
    (by rw [stage2NoEventSignExtend_toNat (by omega)]; omega)
    (is := [Instr.load "%2" (Ty.int 32) (Operand.reg "%arrayidx.peel"),
      Instr.zext "%idxprom.peel" 32 64 (Operand.reg "%2"),
      Instr.gep "%arrayidx6.peel" (Ty.int 8) (Operand.reg "%b")
        (Operand.reg "%idxprom.peel"),
      Instr.load "%3" (Ty.int 8) (Operand.reg "%arrayidx6.peel")])]
  all_goals cycle_lk
  rw [show K.ep + ((BitVec.ofNat 64 k).signExtend 64).toNat * 4 = K.ep + 4 * k from by
    rw [stage2NoEventSignExtend_toNat (by omega), Nat.mul_comm]]
  rw [stage2NoEventWalk_denote_load_int (calls := calls)
    (env := ("%arrayidx.peel", Value.ptr (K.ep + 4 * k)) ::
      ("%inc.peel", Value.int 64 (BitVec.ofNat 64 (k + 1))) :: env) (s := s)
    (d := "%2") (p := "%arrayidx.peel") (w := 32) (a := K.ep + 4 * k) (bs := bs4)
    (by decide) ?_ hlane
    (is := [Instr.zext "%idxprom.peel" 32 64 (Operand.reg "%2"),
      Instr.gep "%arrayidx6.peel" (Ty.int 8) (Operand.reg "%b")
        (Operand.reg "%idxprom.peel"),
      Instr.load "%3" (Ty.int 8) (Operand.reg "%arrayidx6.peel")])]
  all_goals cycle_lk
  rw [hbs]
  rw [denoteCode_zext (calls := calls)
    (env := ("%2", Value.int 32 (BitVec.ofNat 32 lane)) ::
      ("%arrayidx.peel", Value.ptr (K.ep + 4 * k)) ::
      ("%inc.peel", Value.int 64 (BitVec.ofNat 64 (k + 1))) :: env)
    (s := s) (d := "%idxprom.peel")
    (v := "%2") (wIn := 32) (wOut := 64) (x := BitVec.ofNat 32 lane) ?_
    (is := [Instr.gep "%arrayidx6.peel" (Ty.int 8) (Operand.reg "%b")
        (Operand.reg "%idxprom.peel"),
      Instr.load "%3" (Ty.int 8) (Operand.reg "%arrayidx6.peel")])]
  all_goals cycle_lk
  rw [stage2NoEventOfNat64_ofNat32 hLaneLt]
  rw [denoteCode_gep8_reg (calls := calls)
    (env := ("%idxprom.peel", Value.int 64 (BitVec.ofNat 64 lane)) ::
      ("%2", Value.int 32 (BitVec.ofNat 32 lane)) ::
      ("%arrayidx.peel", Value.ptr (K.ep + 4 * k)) ::
      ("%inc.peel", Value.int 64 (BitVec.ofNat 64 (k + 1))) :: env)
    (s := s) (d := "%arrayidx6.peel") (base := "%b") (off := "%idxprom.peel") (a := K.b)
    (idx := BitVec.ofNat 64 lane) ?_ ?_
    (stage2NoEventLane_signExtend_lt hLaneLt)
    (is := [Instr.load "%3" (Ty.int 8) (Operand.reg "%arrayidx6.peel")])]
  all_goals cycle_lk
  rw [stage2NoEventSignExtend_toNat (by omega)]
  rw [stage2NoEventWalk_denote_load_int (calls := calls)
    (env := ("%arrayidx6.peel", Value.ptr (K.b + lane)) ::
      ("%idxprom.peel", Value.int 64 (BitVec.ofNat 64 lane)) ::
      ("%2", Value.int 32 (BitVec.ofNat 32 lane)) ::
      ("%arrayidx.peel", Value.ptr (K.ep + 4 * k)) ::
      ("%inc.peel", Value.int 64 (BitVec.ofNat 64 (k + 1))) :: env) (s := s)
    (d := "%3") (p := "%arrayidx6.peel") (w := 8) (a := K.b + lane) (bs := [byte])
    (by decide) (by cycle_lk) hbyte (is := [])]
  rw [stage2NoEventBytesToNat_singleton]
  simp only [loopHeadReadCellsAt, loopHeadReadCells, cells, denoteCode_nil]

/-- **`if.end.peel`'s run at the backedge edge**: its nine `phi`s and its six
reads, ending in the head's layer equation. -/
theorem loopHeadBackedge_denote {calls : Calls} {env : Env} {s : State}
    {K : Stage2NoEventWalkCarry} {k sp fr wide lane : Nat} {bs4 : List UInt8}
    {byte : UInt8}
    (hpre : s.pre = some "value.outer.backedge")
    (hwide : lookupName env "%wide.trip.count" =
      some (.int 64 (BitVec.ofNat 64 wide)))
    (hone : lookupName env "%45" = some (.int 64 (BitVec.ofNat 64 sp)))
    (htok : lookupName env "%tokens.0.ph.be" =
      some (.int 64 (BitVec.ofNat 64 K.tok)))
    (hterms : lookupName env "%terms.0.ph.be" =
      some (.int 64 (BitVec.ofNat 64 K.terms)))
    (harena : lookupName env "%arena.0.ph.be" =
      some (.int 64 (BitVec.ofNat 64 K.arenaWord)))
    (halen : lookupName env "%alen.0.ph.be" =
      some (.int 64 (BitVec.ofNat 64 K.arena.length)))
    (hkbe : lookupName env "%k.0.ph.be" = some (.int 64 (BitVec.ofNat 64 k)))
    (hspbe : lookupName env "%sp.0.ph.be" = some (.int 32 (BitVec.ofNat 32 sp)))
    (hfrbe : lookupName env "%frame.0.ph.be" = some (.int 8 (BitVec.ofNat 8 fr)))
    (hep : lookupName env "%ep" = some (.ptr K.ep))
    (hb : lookupName env "%b" = some (.ptr K.b))
    (hkLt : k < 2 ^ 63) (hbs : bytesToNat bs4 = lane)
    (hLaneLt : lane < 2 ^ 32)
    (hlane : readBytes s.mem (K.ep + 4 * k) 4 = some bs4)
    (hbyte : readBytes s.mem (K.b + lane) 1 = some [byte]) :
    denoteCode calls loopHeadBlock.instrs (stateAt env s) =
      some (stateAt
        (cells (loopHeadReadCellsAt K k sp fr sp wide lane byte)
          (cells (loopHeadPhiCellsAt K k sp fr sp wide) env)) s) := by
  have hphi := loopHeadBackedge_phi_denote (calls := calls) (s := s) (env := env)
    (K := K) (k := k) (sp := sp) (fr := fr) (wide := wide) hpre hwide hone htok
    hterms harena halen hkbe hspbe hfrbe
  rw [loopHeadBlock]
  rw [denoteCode_append_apply (a := loopHeadPhiInstrs) (b := loopHeadReadInstrs)
    (s := stateAt env s)
    (s' := stateAt (cells (loopHeadPhiCellsAt K k sp fr sp wide) env) s)
    hphi (by decide)]
  rw [loopHeadBackedge_read_denote (calls := calls)
    (env := cells (loopHeadPhiCellsAt K k sp fr sp wide) env) (s := s)
    (K := K) (k := k) (sp := sp) (fr := fr) (wide := wide) (lane := lane)
    (bs4 := bs4) (byte := byte)
    (by
      exact cells_lookup_of_mem _ _ (by simp [loopHeadPhiCellsAt]) (by
        rw [loopHeadPhiCellsAt_names]; decide))
    (by
      rw [cells_lookup_of_notin _ _ (by rw [loopHeadPhiCellsAt_names]; decide)]
      exact hep)
    (by
      rw [cells_lookup_of_notin _ _ (by rw [loopHeadPhiCellsAt_names]; decide)]
      exact hb)
    hkLt hbs hLaneLt hlane hbyte]

/-! ### The cycle's statement and its endpoint -/

/-- **The cycle**: a priced head segment from the endpoint at index `k` to the
next head at `k + d`, at the same carry.  `d` is the path's index delta — one
entry on the after-value path (`%inc379 = %k.6 + 1`), four on the object-member
pair path (`if.end303`'s `%inc304 = %k.1.in + 4`). -/
structure Stage2NoEventWalkCycle (calls : Calls) (mem : Mem)
    (K : Stage2NoEventWalkCarry) (k : Nat) (s : State) (d : Nat) (s' : State)
    (p : Nat) : Prop where
  /-- The run, its price, and the target's head and trace. -/
  headPriced : Stage2NoEventWalkHeadPricedSegment calls mem K k s K (k + d) s' p

/-- **The class lane's endpoint**: the state at `after_value`'s entry, the class's
carry and trace, the dispatch `phi` run's selection, the depth and frame words the
continuation needs, and the head's base lookups carried through the class route. -/
structure Stage2NoEventWalkCycleSrc (calls : Calls) (mem : Mem)
    (K : Stage2NoEventWalkCarry) (k : Nat) (s : State) : Type where
  /-- The invariant at the endpoint. -/
  inv : Stage2NoEventWalkInv K mem s
  /-- The after-value block is the next one to run. -/
  pc : s.pc = "after_value"
  /-- The frame word (the container's tag), non-zero on the array path. -/
  frame : Nat
  frameLt : frame < 2 ^ 8
  frameNe : frame ≠ 0
  /-- The depth word, non-zero at a nested value. -/
  sp : Nat
  spLt : sp < 2 ^ 32
  spNe : sp ≠ 0
  /-- The next head's index fits the address arithmetic. -/
  kAddr : k + 1 < 2 ^ 63
  /-- The next entry exists, so the backedge's guard admits it. -/
  klt : k + 1 < K.nep
  /-- The consumed-count bound at the endpoint's index. -/
  count : Stage2NoEventWalkCount K k
  /-- The dispatch `phi` run, at the class's own edge and readings. -/
  phiRun : ∃ p, s.pre = some p ∧
    PhiSelects (stateAt s.env s) p afterValuePhiSpecs
      [("%frame.6", .int 8 (BitVec.ofNat 8 frame)),
       ("%sp.4", .int 32 (BitVec.ofNat 32 sp)),
       ("%k.6", .int 64 (BitVec.ofNat 64 k)),
       ("%alen.8", .int 64 (BitVec.ofNat 64 K.arena.length)),
       ("%arena.10", .int 64 (BitVec.ofNat 64 K.arenaWord)),
       ("%terms.8", .int 64 (BitVec.ofNat 64 K.terms)),
       ("%tokens.8", .int 64 (BitVec.ofNat 64 K.tok))]
  /-- The entry chain's live-ins survived the class route. -/
  baseLookups : Stage2NoEventWalkBaseLookups K s
  /-- The report's base is at least one. -/
  bPos : 1 ≤ K.b
  /-- The class route's output evidence. -/
  trace : Stage2NoEventWalkTrace K
  /-- The byte at the class's index is the comma that continues the walk. -/
  comma : ∀ lane, K.ent[k]? = some lane → K.bs.getD lane 0 = 44

/-- **The cycle's credit at a delta of `d` entries**: `d` entries' allowance
covers the steps, and the byte term only falls because the entries are in
document order. -/
theorem stage2NoEventWalkPotential_add {K : Stage2NoEventWalkCarry} {k d : Nat}
    (hd : k + d ≤ K.nep) (hent : K.ent.getD k 0 ≤ K.ent.getD (k + d) 0) :
    stage2NoEventWalkPotential K (k + d) + 32 * d ≤
      stage2NoEventWalkPotential K k := by
  unfold stage2NoEventWalkPotential
  have h1 : K.nep - (k + d) + d = K.nep - k := by omega
  have h2 : K.n - K.ent.getD (k + d) 0 ≤ K.n - K.ent.getD k 0 := by omega
  rw [← h1]
  omega

/-- **The base lookups through one layer of the cycle's cells.** -/
theorem stage2NoEventCycleBase {K : Stage2NoEventWalkCarry} {env : Env}
    (h : ∀ n v, (n, v) ∈ stage2NoEventWalkBaseValues K → lookupName env n = some v)
    {cs : List (String × Value)} {names : List String}
    (hcs : cs.map (·.1) = names)
    (hdisj : stage2NoEventWalkBaseNames.all
      (fun n => !decide (n ∈ names)) = true) :
    ∀ n v, (n, v) ∈ stage2NoEventWalkBaseValues K →
      lookupName (cells cs env) n = some v := by
  intro n v hv
  have hmem : n ∈ stage2NoEventWalkBaseNames := by
    have := List.mem_map_of_mem (f := Prod.fst) hv
    rwa [stage2NoEventWalkBaseValues_names] at this
  rw [cells_lookup_of_notin cs env (by
    rw [hcs]
    have := List.all_eq_true.mp hdisj n hmem
    simpa using this)]
  exact h n v hv

/-! ### The cycle

From the class lane's endpoint the cycle runs the eight blocks and lands at the
next head.  The two reads it needs are the entry at the class's index (the
comma) and the entry at the next index (the head's lane); both are the caller's
staging, kept by the run's frame, and the second one's byte is the head's `%3`.
-/

/-- **The cycle, from the class lane's endpoint.** -/
theorem stage2NoEventWalkCycle_of_afterValue {calls : Calls} {mem : Mem}
    {K : Stage2NoEventWalkCarry} {k : Nat} {s : State}
    (h : Stage2NoEventWalkCycleSrc calls mem K k s) :
    ∃ (s' : State) (p : Nat), Stage2NoEventWalkCycle calls mem K k s 1 s' p := by
  obtain ⟨inv, hpc, fr, hfrLt, hfrNe, sp, hspLt, hspNe, hkAddr, hklt, hcount, hphi,
    hbase, hbpos, htrace, hcomma⟩ := h
  obtain ⟨pEdge, hpre, hsel⟩ := hphi
  have hnepLt : K.nep < 2 ^ 64 := inv.nepLt
  have hklt' : k < K.nep := by omega
  have hk64 : k < 2 ^ 64 := by omega
  -- the carry's own registers
  have hb : lookupName s.env "%b" = some (.ptr K.b) :=
    hbase "%b" _ (by simp [stage2NoEventWalkBaseValues, stage2NoEventWalkParamEntries])
  have hep : lookupName s.env "%ep" = some (.ptr K.ep) :=
    hbase "%ep" _ (by simp [stage2NoEventWalkBaseValues, stage2NoEventWalkParamEntries])
  have hnep : lookupName s.env "%nep" = some (.int 64 (BitVec.ofNat 64 K.nep)) :=
    hbase "%nep" _ (by simp [stage2NoEventWalkBaseValues, stage2NoEventWalkParamEntries])
  -- the entry stream at the run's memory, and the two entries the cycle reads
  have hlanes : readLanes32 s.mem K.ep K.nep = some K.ent :=
    inv.readLanes_off (stage2NoEventCycleOutLane inv) inv.entries
  obtain ⟨hlen, -⟩ := stage2NoEventCycleLanes hlanes
  obtain ⟨laneAV, bsAV, hgetAV, hreadAV, hvalAV, hltAV⟩ :=
    stage2NoEventCycleEnt_lane hlanes hklt'
  obtain ⟨laneNX, bsNX, hgetNX, hreadNX, hvalNX, hltNX⟩ :=
    stage2NoEventCycleEnt_lane hlanes hklt
  have hinsAV : laneAV < K.n := inv.inside laneAV (List.mem_of_getElem? hgetAV)
  have hinsNX : laneNX < K.n := inv.inside laneNX (List.mem_of_getElem? hgetNX)
  -- the document's two bytes, kept by the run's frame
  have hdocAV : readBytes s.mem (K.b + laneAV) 1 = some [K.bs.getD laneAV 0] :=
    inv.readBytes_off (K := K) (a := K.b + laneAV) (N := 1)
      (bs := [K.bs.getD laneAV 0]) (stage2NoEventCycleOutDoc inv hinsAV) (by
        rw [readBytes_one, readByte_of_readBytes inv.doc hinsAV]
        rfl)
  have hdocNX : readBytes s.mem (K.b + laneNX) 1 = some [K.bs.getD laneNX 0] :=
    inv.readBytes_off (K := K) (a := K.b + laneNX) (N := 1)
      (bs := [K.bs.getD laneNX 0]) (stage2NoEventCycleOutDoc inv hinsNX) (by
        rw [readBytes_one, readByte_of_readBytes inv.doc hinsNX]
        rfl)
  have hcommaAV : K.bs.getD laneAV 0 = 44 := hcomma laneAV hgetAV
  have hbyteAV : readBytes s.mem (K.b + laneAV) 1 = some [44] := by
    rw [hcommaAV] at hdocAV
    exact hdocAV
  have hbslen : K.bs.length = K.n := readBytes_length mem K.b K.n (bs := K.bs) inv.doc
  have hbsgetNX : K.bs[laneNX]? = some (K.bs.getD laneNX 0) := by
    have hlt : laneNX < K.bs.length := by omega
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt]
    simp
  have hbytereNX : readBytes s.mem (K.b + laneNX) 1 = some [K.bs.getD laneNX 0] := hdocNX
  -- the state the after-value dispatch leaves, and the chain's states
  let e1 : Env := cells afterValueDispatchCells
    (cells (afterValuePhiCells fr sp k K.arena.length K.arenaWord K.terms K.tok) s.env)
  let r1 : State := stage2NoEventWalkNext e1 s "if.end369"
  let r2 : State := stage2NoEventWalkNext e1 r1 "if.end378"
  let e3 : Env := cells (ifEnd378Cells K.ep K.b laneAV k fr 44) e1
  let r3 : State := stage2NoEventWalkNext e3 r2 "if.end410"
  let r4 : State := stage2NoEventWalkNext e3 r3 "NodeBlock41"
  let e5 : Env := cells nodeBlock41Cells e3
  let r5 : State := stage2NoEventWalkNext e5 r4 "LeafBlock37"
  let e6 : Env := cells leafBlock37Cells e5
  let r6 : State := stage2NoEventWalkNext e6 r5 "value.outer.backedge"
  let e7 : Env := cells (outerBackedgeTailCells sp (k + 1))
    (cells (outerBackedgePhiCells fr sp (k + 1) K.arena.length K.arenaWord K.terms
      K.tok) e6)
  let r7 : State := stage2NoEventWalkNext e7 r6 "if.end.peel"
  let e8 : Env := cells
    (loopHeadReadCellsAt K (k + 1) sp fr sp (max sp 520) laneNX
      (K.bs.getD laneNX 0))
    (cells (loopHeadPhiCellsAt K (k + 1) sp fr sp (max sp 520)) e7)
  let r8 : State := stage2NoEventWalkNext e8 r7 "NodeBlock5"
  -- the first hop: the after-value dispatch
  have l1 : Stage2NoEventWalkLink calls K mem s K r1 :=
    stage2NoEventWalkLink_condbr_false inv (by rw [hpc]; exact afterValueBlock_find)
      (afterValue_denote (calls := calls) (env := s.env) (s := s) (p := pEdge)
        hpre hsel hnep hspLt hspNe hk64 hklt' hnepLt)
      rfl (by cycle_lk)
  have l2 : Stage2NoEventWalkLink calls K mem r1 K r2 :=
    stage2NoEventWalkLink_condbr_true l1.inv'
      (by rw [show r1.pc = "if.end369" from rfl]; exact ifEnd369Block_find)
      (by rw [ifEnd369Block]; exact denoteCode_nil calls (stateAt e1 r1))
      rfl (by cycle_lk)
  have l3 : Stage2NoEventWalkLink calls K mem r2 K r3 :=
    stage2NoEventWalkLink_condbr_false l2.inv'
      (by rw [show r2.pc = "if.end378" from rfl]; exact ifEnd378Block_find)
      (ifEnd378_denote (calls := calls) (env := e1) (s := r2)
        (ep := K.ep) (b := K.b) (lane := laneAV) (k := k) (fr := fr) (byte := 44)
        (bs4 := bsAV) (by cycle_lk) (by cycle_lk) (by cycle_lk) (by cycle_lk)
        (by omega) hfrLt hfrNe hvalAV hltAV hreadAV hbyteAV)
      rfl (by cycle_lk)
  have l4 : Stage2NoEventWalkLink calls K mem r3 K r4 :=
    stage2NoEventWalkLink_br l3.inv'
      (by rw [show r3.pc = "if.end410" from rfl]; exact ifEnd410Block_find)
      (by rw [ifEnd410Block]; exact denoteCode_nil calls (stateAt e3 r3))
      rfl
  have l5 : Stage2NoEventWalkLink calls K mem r4 K r5 :=
    stage2NoEventWalkLink_condbr_true l4.inv'
      (by rw [show r4.pc = "NodeBlock41" from rfl]; exact nodeBlock41Block_find)
      (nodeBlock41_denote (calls := calls) (env := e3) (s := r4) (by cycle_lk))
      rfl (by cycle_lk)
  have l6 : Stage2NoEventWalkLink calls K mem r5 K r6 :=
    stage2NoEventWalkLink_condbr_true l5.inv'
      (by rw [show r5.pc = "LeafBlock37" from rfl]; exact leafBlock37Block_find)
      (leafBlock37_denote (calls := calls) (env := e5) (s := r5) (by cycle_lk))
      rfl (by cycle_lk)
  -- the backedge's `phi` run at `LeafBlock37`'s edge
  have hframe6 : lookupName e6 "%frame.6" = some (.int 8 (BitVec.ofNat 8 fr)) := by
    cycle_lk
  have hsp4 : lookupName e6 "%sp.4" = some (.int 32 (BitVec.ofNat 32 sp)) := by
    cycle_lk
  have hinc379 : lookupName e6 "%inc379" =
      some (.int 64 (BitVec.ofNat 64 (k + 1))) := by
    cycle_lk
  have halen8 : lookupName e6 "%alen.8" =
      some (.int 64 (BitVec.ofNat 64 K.arena.length)) := by
    cycle_lk
  have harena10 : lookupName e6 "%arena.10" =
      some (.int 64 (BitVec.ofNat 64 K.arenaWord)) := by
    cycle_lk
  have hterms8 : lookupName e6 "%terms.8" =
      some (.int 64 (BitVec.ofNat 64 K.terms)) := by
    cycle_lk
  have htokens8 : lookupName e6 "%tokens.8" =
      some (.int 64 (BitVec.ofNat 64 K.tok)) := by
    cycle_lk
  have hnep6 : lookupName e6 "%nep" = some (.int 64 (BitVec.ofNat 64 K.nep)) := by
    cycle_lk
  have l7 : Stage2NoEventWalkLink calls K mem r6 K r7 :=
    stage2NoEventWalkLink_condbr_true l6.inv'
      (by rw [show r6.pc = "value.outer.backedge" from rfl]
          exact outerBackedgeBlock_find)
      (outerBackedge_leaf_denote (calls := calls) (env := e6) (s := r6)
        (fr := fr) (sp := sp) (k := k + 1) (alen := K.arena.length)
        (arena := K.arenaWord) (terms := K.terms) (tok := K.tok) (nep := K.nep)
        rfl hframe6 hsp4 hinc379 halen8 harena10 hterms8 htokens8 hnep6
        hspLt hklt hnepLt)
      rfl (by cycle_lk)
  -- the head's `phi` run at the backedge's edge, and its read row
  have hpre7 : r7.pre = some "value.outer.backedge" := rfl
  have hwide7 : lookupName e7 "%wide.trip.count" =
      some (.int 64 (BitVec.ofNat 64 (max sp 520))) := by
    cycle_lk
  have h45 : lookupName e7 "%45" = some (.int 64 (BitVec.ofNat 64 sp)) := by
    cycle_lk
  have htokBE : lookupName e7 "%tokens.0.ph.be" =
      some (.int 64 (BitVec.ofNat 64 K.tok)) := by
    cycle_lk
  have htermsBE : lookupName e7 "%terms.0.ph.be" =
      some (.int 64 (BitVec.ofNat 64 K.terms)) := by
    cycle_lk
  have harenaBE : lookupName e7 "%arena.0.ph.be" =
      some (.int 64 (BitVec.ofNat 64 K.arenaWord)) := by
    cycle_lk
  have halenBE : lookupName e7 "%alen.0.ph.be" =
      some (.int 64 (BitVec.ofNat 64 K.arena.length)) := by
    cycle_lk
  have hkBE : lookupName e7 "%k.0.ph.be" =
      some (.int 64 (BitVec.ofNat 64 (k + 1))) := by
    cycle_lk
  have hspBE : lookupName e7 "%sp.0.ph.be" = some (.int 32 (BitVec.ofNat 32 sp)) := by
    cycle_lk
  have hfrBE : lookupName e7 "%frame.0.ph.be" =
      some (.int 8 (BitVec.ofNat 8 fr)) := by
    cycle_lk

  have l8 : Stage2NoEventWalkLink calls K mem r7 K r8 :=
    stage2NoEventWalkLink_br l7.inv'
      (by rw [show r7.pc = "if.end.peel" from rfl]; exact loopHeadBlock_find)
      (loopHeadBackedge_denote (calls := calls) (env := e7) (s := r7) (K := K)
        (k := k + 1) (sp := sp) (fr := fr) (wide := max sp 520) (lane := laneNX)
        (bs4 := bsNX) (byte := K.bs.getD laneNX 0) hpre7 hwide7 h45 htokBE htermsBE harenaBE
        halenBE hkBE hspBE hfrBE (by cycle_lk) (by cycle_lk) hkAddr hvalNX hltNX
        hreadNX hbytereNX)
      rfl
  -- the run, at the eight steps' own fuel
  have hrun : ∀ n, runFuel calls (8 + n) stage2NoEventBody s =
      runFuel calls n stage2NoEventBody r8 := by
    intro n
    rw [show 8 + n = 1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + n))))))) from by omega]
    rw [stage2NoEventWalkLink_runFuel l1, stage2NoEventWalkLink_runFuel l2,
      stage2NoEventWalkLink_runFuel l3, stage2NoEventWalkLink_runFuel l4,
      stage2NoEventWalkLink_runFuel l5, stage2NoEventWalkLink_runFuel l6,
      stage2NoEventWalkLink_runFuel l7, stage2NoEventWalkLink_runFuel l8]
  -- the credit
  have hent : K.ent.getD k 0 ≤ K.ent.getD (k + 1) 0 :=
    stage2NoEventEnt_getD_le (l := K.ent) inv.order (d := 0) (i := k) (j := k + 1)
      (by omega) (by rw [hlen]; omega)
  have hcred : 8 + stage2NoEventWalkPotential K (k + 1) ≤
      stage2NoEventWalkPotential K k := by
    have h32 := stage2NoEventWalkPotential_add (K := K) (k := k) (d := 1)
      (by omega) hent
    omega
  -- the target's head
  have hhead : Stage2NoEventWalkHead K mem (k + 1) r8 :=
    { inv := Stage2NoEventWalkInv.mem_congr inv rfl
      pc := rfl
      klt := hklt
      count := Stage2NoEventWalkCount.step (a := 0) (b := 1) hcount rfl rfl (by omega)
      bPos := hbpos
      layers := ⟨e7, sp, fr, sp, max sp 520, laneNX, K.bs.getD laneNX 0, rfl, hgetNX,
        hltNX, hbsgetNX, hbytereNX, hspLt, hfrLt, rfl, rfl⟩
      baseLookups := by
        have h1 := stage2NoEventCycleBase (K := K) (env := s.env) hbase
          (cs := afterValuePhiCells fr sp k K.arena.length K.arenaWord K.terms K.tok)
          (names := ["%tokens.8", "%terms.8", "%arena.10", "%alen.8", "%k.6",
            "%sp.4", "%frame.6"]) rfl (by decide)
        have h0 := stage2NoEventCycleBase (K := K) h1
          (cs := afterValueDispatchCells) (names := ["%cmp358", "%cmp355"])
          rfl (by decide)
        have h2 := stage2NoEventCycleBase (K := K) h0
          (cs := ifEnd378Cells K.ep K.b laneAV k fr 44)
          (names := ["%53", "%arrayidx386", "%idxprom385", "%cmp382", "%52",
            "%arrayidx380", "%inc379"]) rfl (by decide)
        have h3 := stage2NoEventCycleBase (K := K) h2
          (cs := nodeBlock41Cells) (names := ["%Pivot42"]) rfl (by decide)
        have h4 := stage2NoEventCycleBase (K := K) h3
          (cs := leafBlock37Cells) (names := ["%SwitchLeaf38"]) rfl (by decide)
        have h5 := stage2NoEventCycleBase (K := K) h4
          (cs := outerBackedgePhiCells fr sp (k + 1) K.arena.length K.arenaWord
            K.terms K.tok)
          (names := ["%tokens.0.ph.be", "%terms.0.ph.be", "%arena.0.ph.be",
            "%alen.0.ph.be", "%k.0.ph.be", "%sp.0.ph.be", "%frame.0.ph.be"])
          rfl (by decide)
        have h6 := stage2NoEventCycleBase (K := K) h5
          (cs := outerBackedgeTailCells sp (k + 1))
          (names := ["%cmp.not.peel", "%wide.trip.count", "%umax", "%umax.max",
            "%45"]) rfl (by decide)
        have h7 := stage2NoEventCycleBase (K := K) h6
          (cs := loopHeadPhiCellsAt K (k + 1) sp fr sp (max sp 520))
          (names := loopHeadPhiCellNames) rfl (by decide)
        have h8 := stage2NoEventCycleBase (K := K) h7
          (cs := loopHeadReadCellsAt K (k + 1) sp fr sp (max sp 520) laneNX
            (K.bs.getD laneNX 0))
          (names := loopHeadReadCellNames) rfl (by decide)
        exact h8 }
  exact ⟨r8, 8, ⟨⟨⟨hrun, l8.inv'⟩, hhead, htrace⟩, hcred⟩⟩

/-! ### Axiom footprints -/

#print axioms stage2NoEventOfNatSucc
#print axioms step_select32_imm_true
#print axioms stage2NoEventDenoteSelect32
#print axioms stage2NoEventWalkLink_br
#print axioms stage2NoEventCycleEnt_lane
#print axioms stage2NoEventCycleOutLane
#print axioms stage2NoEventCycleOutDoc
#print axioms afterValue_phi_denote
#print axioms afterValue_denote
#print axioms ifEnd378_denote
#print axioms outerBackedge_leaf_denote
#print axioms nodeBlock41_denote
#print axioms leafBlock37_denote
#print axioms loopHeadBackedge_phi_denote
#print axioms loopHeadBackedge_read_denote
#print axioms loopHeadBackedge_denote
#print axioms stage2NoEventWalkPotential_add
#print axioms stage2NoEventCycleBase
#print axioms stage2NoEventWalkCycle_of_afterValue

end LeanLLVM.Refinement
