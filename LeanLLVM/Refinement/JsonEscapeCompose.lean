/-
The blocks the walk's trace does not carry, and the emitter's two readings.

`JsonEscapeDecodeTrace` states a step for every block on the walk's paths except
two: `if.end21` (block 11), the refusal guard's first half, and `while.end35`
(block 23), the final copy's entry.  Both are on the composed paths — the first on
the iteration arm's escape seam, the second on the exit continuation and on the
entry path that reaches the exit before the latch — so the composition names them
here.

**Consolidation.**  Each step fact below says, at the lemma, what a later reader
would otherwise have to find in a plan: if the trace's owner supplies this block's
step fact, consume theirs and delete this one.  The proofs live here so the
composition can name the block, not so the block's trace lives here.

The second half is the emitter's two unit forms.  The `\u` escape's first unit is
`hex4` (`hex4_hxCode`: the block's `%and27.i` is the specification's code unit at
the sixteen bytes it read, once the four lane tests hold).  The pair rule is
`surrogateTail`'s own guard and answer, stated as four step laws
(`surrogateTail_none_of_guard`, `_none_of_hex4_none`, `_none_of_lo_out`,
`_some_of_pair`) plus the one-bit reading of the block's combined gate
(`and_one_iff`, `and_one_zero`, `evalICmp_ule_one_iff`).

**What is not here**, so a later reader does not take the seam for closed: the
block's gate bits are not yet *identified* with `SurrogateGuard` at a state — that
needs the high-surrogate range read out of `%21 = %vecext.i207 &&& 64512` against
`55296`, the pair's value read out of `%add30.i`, and the UTF-8 store's word
(`(udIfEnd32Word cp).toNat = bytesToNat (utf8Encode cp.toNat)`, the equation
`JsonEscapeDecodeTrace.udIfEnd32I_decode` still takes as its `hword`).  Each is
arithmetic over the block's own `BitVec` form; none is a statement about the
specification.
-/
import LeanLLVM.Refinement.JsonEscapeCopyLoops

set_option autoImplicit false
set_option maxRecDepth 16000

namespace LeanLLVM.Refinement

open LeanLLVM
open LeanLLVM.Refinement.JsonEscapeIR
open LeanLLVM.Refinement.JsonEscapeIntrinsics
open LeanLLVM.Refinement.JsonScanSpec
open LeanLLVM.Refinement.BitLanes

/-! ### `if.end21`

The refusal guard's first half: the byte after the escape must be inside the body.
`%sub` is the escape's body-relative offset, so `%add.i100` is the second byte's
offset and the test is `ult` against the body's length.

If the trace's owner supplies this block's step fact, consume theirs and delete
this one. -/

def udIfEnd21 : Block := blockAt usDecFunction 11 (by decide)

theorem findBlock_udIfEnd21 : usDecFunction.findBlock "if.end21" = some udIfEnd21 := by
  decide

theorem udIfEnd21_instrs :
    udIfEnd21.instrs =
      [ .binop "%add.i100" .add 64 (.reg "%sub") (.imm (.int 64 (BitVec.ofInt 64 1))),
        .icmp "%cmp.not.i" .ult 64 (.reg "%add.i100") (.reg "%n") ] := by
  decide

theorem udIfEnd21_term :
    udIfEnd21.term = .condbr (.reg "%cmp.not.i") "if.end.i" "if.then22" := by
  decide

def udIfEnd21Env (env : Env) (subv nv : BitVec 64) : Env :=
  ("%cmp.not.i", .int 1 (evalICmp .ult (subv + BitVec.ofInt 64 1) nv)) ::
    ("%add.i100", .int 64 (subv + BitVec.ofInt 64 1)) :: env

theorem udIfEnd21_denote (env : Env) (s : State) (subv nv : BitVec 64)
    (hsub : lookupName env "%sub" = some (.int 64 subv))
    (hn : lookupName env "%n" = some (.int 64 nv)) :
    denoteCode escapeCalls udIfEnd21.instrs (withEnv env s) =
      some (withEnv (udIfEnd21Env env subv nv) s) := by
  rw [udIfEnd21_instrs]
  rw [denoteCode_cons_of _ _ _ _ _ (b_add64_imm _ s "%add.i100" "%sub" subv
    (BitVec.ofInt 64 1) (by ud_lk_h hsub))]
  rw [denoteCode_cons_of _ _ _ _ _ (b_icmp_ult64 _ s "%cmp.not.i" "%add.i100" "%n"
    (subv + BitVec.ofInt 64 1) nv (by ud_lk) (by ud_lk_h hn))]
  simp only [denoteCode, withEnv, udIfEnd21Env]

theorem udIfEnd21_run (env : Env) (s : State) (subv nv : BitVec 64)
    (hsub : lookupName env "%sub" = some (.int 64 subv))
    (hn : lookupName env "%n" = some (.int 64 nv)) :
    Option.map State.mem (denoteCode escapeCalls udIfEnd21.instrs (withEnv env s)) =
        some s.mem ∧
      (denoteCode escapeCalls udIfEnd21.instrs (withEnv env s)).bind
          (fun st => lookupName st.env "%add.i100") =
        some (.int 64 (subv + BitVec.ofInt 64 1)) ∧
      (denoteCode escapeCalls udIfEnd21.instrs (withEnv env s)).bind
          (fun st => lookupName st.env "%cmp.not.i") =
        some (.int 1 (evalICmp .ult (subv + BitVec.ofInt 64 1) nv)) := by
  rw [udIfEnd21_denote env s subv nv hsub hn]
  refine ⟨?_, ?_, ?_⟩
  · simp only [Option.map_some, withEnv]
  all_goals (simp only [Option.bind_some, withEnv, udIfEnd21Env] <;> ud_lk)

/-- The block's step, taken: the second byte is inside the body. -/
theorem udIfEnd21_step (env : Env) (s : State) (subv nv : BitVec 64)
    (hpc : s.pc = "if.end21")
    (hsub : lookupName env "%sub" = some (.int 64 subv))
    (hn : lookupName env "%n" = some (.int 64 nv))
    (hcond : evalICmp .ult (subv + BitVec.ofInt 64 1) nv = (1 : BitVec 1)) :
    step escapeCalls usDecFunction (withEnv env s) =
      .jump { (withEnv (udIfEnd21Env env subv nv) s) with
              pc := "if.end.i", pre := some "if.end21" } := by
  rw [udStep_of (withEnv env s) "if.end21" udIfEnd21 _
    (by rw [withEnv]; exact hpc) findBlock_udIfEnd21
    (udIfEnd21_denote env s subv nv hsub hn), udIfEnd21_term]
  have hcmp : evalOperand (withEnv (udIfEnd21Env env subv nv) s) (.reg "%cmp.not.i") =
      some (.int 1 (evalICmp .ult (subv + BitVec.ofInt 64 1) nv)) :=
    evalOperand_reg_of _ s "%cmp.not.i" _ (by simp only [udIfEnd21Env]; ud_lk)
  rw [udCondbr_one _ _ _ _ _ hcmp hcond]
  simp only [withEnv, hpc]

/-- The block's step, refused: the second byte is at or past the body's end, and
the refusal's two stores are the next block's. -/
theorem udIfEnd21_step_zero (env : Env) (s : State) (subv nv : BitVec 64)
    (hpc : s.pc = "if.end21")
    (hsub : lookupName env "%sub" = some (.int 64 subv))
    (hn : lookupName env "%n" = some (.int 64 nv))
    (hcond : evalICmp .ult (subv + BitVec.ofInt 64 1) nv = (0 : BitVec 1)) :
    step escapeCalls usDecFunction (withEnv env s) =
      .jump { (withEnv (udIfEnd21Env env subv nv) s) with
              pc := "if.then22", pre := some "if.end21" } := by
  rw [udStep_of (withEnv env s) "if.end21" udIfEnd21 _
    (by rw [withEnv]; exact hpc) findBlock_udIfEnd21
    (udIfEnd21_denote env s subv nv hsub hn), udIfEnd21_term]
  have hcmp : evalOperand (withEnv (udIfEnd21Env env subv nv) s) (.reg "%cmp.not.i") =
      some (.int 1 (evalICmp .ult (subv + BitVec.ofInt 64 1) nv)) :=
    evalOperand_reg_of _ s "%cmp.not.i" _ (by simp only [udIfEnd21Env]; ud_lk)
  rw [udCondbr_zero _ _ _ _ _ hcmp hcond]
  simp only [withEnv, hpc]

/-! ### `while.end35`

The final copy's entry: the three `phi`s the four incoming edges supply, the two
copy bases, the remaining byte count and the test that sends a run to the vector
copy.  The `phi` tables are named so an edge states only the operand it supplies,
which is the shape `cleanup32`'s and `while.end`'s steps already use.

If the trace's owner supplies this block's step fact, consume theirs and delete
this one. -/

def udWhileEnd35IncomingJ : List (String × Operand) :=
  [("while.end", .imm (.int 64 (BitVec.ofInt 64 0))),
   ("while.body6", .reg "%j.0294"),
   ("cleanup32", .reg "%j.3"),
   ("while.body", .imm (.int 64 (BitVec.ofInt 64 0)))]

def udWhileEnd35IncomingI : List (String × Operand) :=
  [("while.end", .imm (.int 64 (BitVec.ofInt 64 0))),
   ("while.body6", .reg "%i.0295"),
   ("cleanup32", .reg "%add24"),
   ("while.body", .imm (.int 64 (BitVec.ofInt 64 0)))]

def udWhileEnd35IncomingK : List (String × Operand) :=
  [("while.end", .reg "%k.0.lcssa"),
   ("while.body6", .reg "%k.1296"),
   ("cleanup32", .reg "%add28"),
   ("while.body", .reg "%nxp")]

theorem udWhileEnd35_instrs :
    (blockAt usDecFunction 23 (by decide)).instrs =
      [ .phi "%j.0.lcssa" (.int 64) udWhileEnd35IncomingJ,
        .phi "%i.0.lcssa" (.int 64) udWhileEnd35IncomingI,
        .phi "%k.1.lcssa" (.int 64) udWhileEnd35IncomingK,
        .gep "%add.ptr36" (.int 8) (.reg "%p") (.reg "%i.0.lcssa"),
        .gep "%add.ptr37" (.int 8) (.reg "%dst") (.reg "%j.0.lcssa"),
        .binop "%sub38" .sub 64 (.reg "%n") (.reg "%i.0.lcssa"),
        .icmp "%cmp.i303" .ugt 64 (.reg "%sub38")
          (.imm (.int 64 (BitVec.ofInt 64 64))) ] := by
  decide

theorem udWhileEnd35_term :
    (blockAt usDecFunction 23 (by decide)).term =
      .condbr (.reg "%cmp.i303") "while.body.i" "us_run_long.exit" := by
  decide


def udWhileEnd35Env (env : Env) (paddr daddr : Nat) (j i kv nv : BitVec 64) : Env :=
  ("%cmp.i303", .int 1 (evalICmp .ugt ((nv - i)) (BitVec.ofInt 64 64))) ::
    ("%sub38", .int 64 ((nv - i))) ::
    ("%add.ptr37", .ptr (daddr + j.toNat)) ::
    ("%add.ptr36", .ptr (paddr + i.toNat)) ::
    ("%k.1.lcssa", .int 64 kv) ::
    ("%i.0.lcssa", .int 64 i) ::
    ("%j.0.lcssa", .int 64 j) :: env

theorem udWhileEnd35_denote (env : Env) (s : State) (prev : String)
    (opj opi opk : Operand) (paddr daddr : Nat) (j i kv nv : BitVec 64)
    (hpre : s.pre = some prev)
    (hj : phiIncoming prev udWhileEnd35IncomingJ = some opj)
    (hi : phiIncoming prev udWhileEnd35IncomingI = some opi)
    (hk : phiIncoming prev udWhileEnd35IncomingK = some opk)
    (hopj : evalOperand (withEnv env s) opj = some (.int 64 j))
    (hopi : evalOperand (withEnv (("%j.0.lcssa", .int 64 j) :: env) s) opi =
      some (.int 64 i))
    (hopk : evalOperand (withEnv (("%i.0.lcssa", .int 64 i) ::
      ("%j.0.lcssa", .int 64 j) :: env) s) opk = some (.int 64 kv))
    (hp : lookupName env "%p" = some (.ptr paddr))
    (hdst : lookupName env "%dst" = some (.ptr daddr))
    (hn : lookupName env "%n" = some (.int 64 nv))
    (hi63 : i.toNat < 2 ^ 63) (hj63 : j.toNat < 2 ^ 63)
    (hiw : (i.signExtend 64).toNat = i.toNat)
    (hjw : (j.signExtend 64).toNat = j.toNat) :
    denoteCode escapeCalls (blockAt usDecFunction 23 (by decide)).instrs
        (withEnv env s) =
      some (withEnv (udWhileEnd35Env env paddr daddr j i kv nv) s) := by
  rw [udWhileEnd35_instrs]
  rw [denoteCode_cons_of _ _ _ _ _ (evalInstr_phi (s := withEnv env s)
    (d := "%j.0.lcssa") (ty := .int 64) (inc := udWhileEnd35IncomingJ) hpre hj hopj)]
  rw [show (withEnv env s).bind "%j.0.lcssa" (.int 64 j) =
      withEnv (("%j.0.lcssa", .int 64 j) :: env) s from rfl]
  rw [denoteCode_cons_of _ _ _ _ _ (evalInstr_phi (s := withEnv (("%j.0.lcssa",
      .int 64 j) :: env) s) (d := "%i.0.lcssa") (ty := .int 64)
    (inc := udWhileEnd35IncomingI) hpre hi hopi)]
  rw [show (withEnv (("%j.0.lcssa", .int 64 j) :: env) s).bind "%i.0.lcssa"
      (.int 64 i) =
      withEnv (("%i.0.lcssa", .int 64 i) :: ("%j.0.lcssa", .int 64 j) :: env) s
      from rfl]
  rw [denoteCode_cons_of _ _ _ _ _ (evalInstr_phi (s := withEnv (("%i.0.lcssa",
      .int 64 i) :: ("%j.0.lcssa", .int 64 j) :: env) s) (d := "%k.1.lcssa")
    (ty := .int 64) (inc := udWhileEnd35IncomingK) hpre hk hopk)]
  rw [show (withEnv (("%i.0.lcssa", .int 64 i) :: ("%j.0.lcssa", .int 64 j) :: env)
      s).bind "%k.1.lcssa" (.int 64 kv) =
      withEnv (("%k.1.lcssa", .int 64 kv) :: ("%i.0.lcssa", .int 64 i) ::
        ("%j.0.lcssa", .int 64 j) :: env) s from rfl]
  rw [denoteCode_cons_of _ _ _ _ _ (b_gep8_reg _ s "%add.ptr36" "%p" "%i.0.lcssa"
    paddr i i.toNat (by ud_lk_h hp) (by ud_lk) hiw hi63)]
  rw [denoteCode_cons_of _ _ _ _ _ (b_gep8_reg _ s "%add.ptr37" "%dst" "%j.0.lcssa"
    daddr j j.toNat (by ud_lk_h hdst) (by ud_lk) hjw hj63)]
  rw [denoteCode_cons_of _ _ _ _ _ (b_sub64 _ s "%sub38" "%n" "%i.0.lcssa"
    nv i (by ud_lk_h hn) (by ud_lk))]
  rw [denoteCode_cons_of _ _ _ _ _ (b_icmp_ugt64_imm _ s "%cmp.i303" "%sub38"
    ((nv - i)) (BitVec.ofInt 64 64) (by ud_lk))]
  simp only [denoteCode, withEnv, udWhileEnd35Env]

theorem udWhileEnd35_run (env : Env) (s : State) (prev : String)
    (opj opi opk : Operand) (paddr daddr : Nat) (j i kv nv : BitVec 64)
    (hpre : s.pre = some prev)
    (hj : phiIncoming prev udWhileEnd35IncomingJ = some opj)
    (hi : phiIncoming prev udWhileEnd35IncomingI = some opi)
    (hk : phiIncoming prev udWhileEnd35IncomingK = some opk)
    (hopj : evalOperand (withEnv env s) opj = some (.int 64 j))
    (hopi : evalOperand (withEnv (("%j.0.lcssa", .int 64 j) :: env) s) opi =
      some (.int 64 i))
    (hopk : evalOperand (withEnv (("%i.0.lcssa", .int 64 i) ::
      ("%j.0.lcssa", .int 64 j) :: env) s) opk = some (.int 64 kv))
    (hp : lookupName env "%p" = some (.ptr paddr))
    (hdst : lookupName env "%dst" = some (.ptr daddr))
    (hn : lookupName env "%n" = some (.int 64 nv))
    (hi63 : i.toNat < 2 ^ 63) (hj63 : j.toNat < 2 ^ 63)
    (hiw : (i.signExtend 64).toNat = i.toNat)
    (hjw : (j.signExtend 64).toNat = j.toNat) :
    Option.map State.mem (denoteCode escapeCalls
        (blockAt usDecFunction 23 (by decide)).instrs (withEnv env s)) = some s.mem ∧
      (denoteCode escapeCalls (blockAt usDecFunction 23 (by decide)).instrs
          (withEnv env s)).bind (fun st => lookupName st.env "%add.ptr36") =
        some (.ptr (paddr + i.toNat)) ∧
      (denoteCode escapeCalls (blockAt usDecFunction 23 (by decide)).instrs
          (withEnv env s)).bind (fun st => lookupName st.env "%add.ptr37") =
        some (.ptr (daddr + j.toNat)) ∧
      (denoteCode escapeCalls (blockAt usDecFunction 23 (by decide)).instrs
          (withEnv env s)).bind (fun st => lookupName st.env "%sub38") =
        some (.int 64 ((nv - i))) ∧
      (denoteCode escapeCalls (blockAt usDecFunction 23 (by decide)).instrs
          (withEnv env s)).bind (fun st => lookupName st.env "%cmp.i303") =
        some (.int 1 (evalICmp .ugt ((nv - i)) (BitVec.ofInt 64 64))) := by
  rw [udWhileEnd35_denote env s prev opj opi opk paddr daddr j i kv nv hpre hj hi hk
    hopj hopi hopk hp hdst hn hi63 hj63 hiw hjw]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp only [Option.map_some, withEnv]
  all_goals (simp only [Option.bind_some, withEnv, udWhileEnd35Env]
              <;> ud_lk)

/-- The block's step, taken: the run goes to the vector copy. -/
theorem udWhileEnd35_step (env : Env) (s : State) (prev : String)
    (opj opi opk : Operand) (paddr daddr : Nat) (j i kv nv : BitVec 64)
    (hpc : s.pc = "while.end35")
    (hpre : s.pre = some prev)
    (hj : phiIncoming prev udWhileEnd35IncomingJ = some opj)
    (hi : phiIncoming prev udWhileEnd35IncomingI = some opi)
    (hk : phiIncoming prev udWhileEnd35IncomingK = some opk)
    (hopj : evalOperand (withEnv env s) opj = some (.int 64 j))
    (hopi : evalOperand (withEnv (("%j.0.lcssa", .int 64 j) :: env) s) opi =
      some (.int 64 i))
    (hopk : evalOperand (withEnv (("%i.0.lcssa", .int 64 i) ::
      ("%j.0.lcssa", .int 64 j) :: env) s) opk = some (.int 64 kv))
    (hp : lookupName env "%p" = some (.ptr paddr))
    (hdst : lookupName env "%dst" = some (.ptr daddr))
    (hn : lookupName env "%n" = some (.int 64 nv))
    (hi63 : i.toNat < 2 ^ 63) (hj63 : j.toNat < 2 ^ 63)
    (hiw : (i.signExtend 64).toNat = i.toNat)
    (hjw : (j.signExtend 64).toNat = j.toNat)
    (hcond : evalICmp .ugt ((nv - i)) (BitVec.ofInt 64 64) = (1 : BitVec 1)) :
    step escapeCalls usDecFunction (withEnv env s) =
      .jump { (withEnv (udWhileEnd35Env env paddr daddr j i kv nv) s) with
              pc := "while.body.i", pre := some "while.end35" } := by
  rw [udStep_of (withEnv env s) "while.end35" _ _
    (by rw [withEnv]; exact hpc) findBlock_udWhileEnd35
    (udWhileEnd35_denote env s prev opj opi opk paddr daddr j i kv nv hpre hj hi hk
      hopj hopi hopk hp hdst hn hi63 hj63 hiw hjw), udWhileEnd35_term]
  have hcmp : evalOperand (withEnv (udWhileEnd35Env env paddr daddr j i kv nv) s)
      (.reg "%cmp.i303") =
      some (.int 1 (evalICmp .ugt ((nv - i)) (BitVec.ofInt 64 64))) :=
    evalOperand_reg_of _ s "%cmp.i303" _
      (by simp only [udWhileEnd35Env]; ud_lk)
  rw [udCondbr_one _ _ _ _ _ hcmp hcond]
  simp only [withEnv, hpc]

/-- The block's step, not taken: the run goes to the tail copy. -/
theorem udWhileEnd35_step_zero (env : Env) (s : State) (prev : String)
    (opj opi opk : Operand) (paddr daddr : Nat) (j i kv nv : BitVec 64)
    (hpc : s.pc = "while.end35")
    (hpre : s.pre = some prev)
    (hj : phiIncoming prev udWhileEnd35IncomingJ = some opj)
    (hi : phiIncoming prev udWhileEnd35IncomingI = some opi)
    (hk : phiIncoming prev udWhileEnd35IncomingK = some opk)
    (hopj : evalOperand (withEnv env s) opj = some (.int 64 j))
    (hopi : evalOperand (withEnv (("%j.0.lcssa", .int 64 j) :: env) s) opi =
      some (.int 64 i))
    (hopk : evalOperand (withEnv (("%i.0.lcssa", .int 64 i) ::
      ("%j.0.lcssa", .int 64 j) :: env) s) opk = some (.int 64 kv))
    (hp : lookupName env "%p" = some (.ptr paddr))
    (hdst : lookupName env "%dst" = some (.ptr daddr))
    (hn : lookupName env "%n" = some (.int 64 nv))
    (hi63 : i.toNat < 2 ^ 63) (hj63 : j.toNat < 2 ^ 63)
    (hiw : (i.signExtend 64).toNat = i.toNat)
    (hjw : (j.signExtend 64).toNat = j.toNat)
    (hcond : evalICmp .ugt ((nv - i)) (BitVec.ofInt 64 64) = (0 : BitVec 1)) :
    step escapeCalls usDecFunction (withEnv env s) =
      .jump { (withEnv (udWhileEnd35Env env paddr daddr j i kv nv) s) with
              pc := "us_run_long.exit", pre := some "while.end35" } := by
  rw [udStep_of (withEnv env s) "while.end35" _ _
    (by rw [withEnv]; exact hpc) findBlock_udWhileEnd35
    (udWhileEnd35_denote env s prev opj opi opk paddr daddr j i kv nv hpre hj hi hk
      hopj hopi hopk hp hdst hn hi63 hj63 hiw hjw), udWhileEnd35_term]
  have hcmp : evalOperand (withEnv (udWhileEnd35Env env paddr daddr j i kv nv) s)
      (.reg "%cmp.i303") =
      some (.int 1 (evalICmp .ugt ((nv - i)) (BitVec.ofInt 64 64))) :=
    evalOperand_reg_of _ s "%cmp.i303" _
      (by simp only [udWhileEnd35Env]; ud_lk)
  rw [udCondbr_zero _ _ _ _ _ hcmp hcond]
  simp only [withEnv, hpc]

/-! ### The emitter's hex unit, read off its lanes

`if.end.i115` tests four byte lanes and computes the code unit with two
multiply-adds; `if.end3.i` recomputes the same chain as the stored code point.  The
trace states both blocks at *lane lists* the composition supplies, so the two facts
below are what connects the lanes to the specification: the multiply-add's operand
is the lanes' nibble bytes (`hxPadd_lane`), and the packed lane-0 word masked to
sixteen bits is `hex4`'s code unit (`hex4_hxCode`, through the trace's
`hex4_of_lane_test` and the intrinsic arithmetic's `pmaddUbSwLane_small` /
`pmaddWdLane_small`).

The accessor lemmas at the top are the `getD` forms the lane facts use; the
`zipWith` shape of the same fact is `JsonUtf8Steps.getD_zipWith`, and a later
consolidation replaces these three with it rather than keeping two spellings of one
identity in two modules. -/

/-- The letter test the emitted `select` branches on. -/
def hexLetterTest (x : BitVec 8) : Bool :=
  BitVec.ult ((x ||| BitVec.ofInt 8 32) + BitVec.ofInt 8 (-97)) (BitVec.ofInt 8 6)

theorem hexNib8_def (x : BitVec 8) :
    hexNib8 x = (x &&& BitVec.ofInt 8 15) +
      (if hexLetterTest x then (9 : BitVec 8) else 0) := rfl

/-- `getD` at an index inside the list is the list's own element. -/
theorem getD_of_lt {α : Type} {i : Nat} (l : List α) (d : α) (h : i < l.length) :
    l.getD i d = l[i] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h, Option.getD_some]

/-- `zip` read at an index inside both operands. -/
theorem getD_zip {α β : Type} (a : List α) (b : List β) (za : α) (zb : β) (z : α × β)
    {i : Nat} (hi : i < a.length) (hi' : i < b.length) :
    (a.zip b).getD i z = (a.getD i za, b.getD i zb) := by
  rw [getD_of_lt (a.zip b) z (by
      rw [List.length_zip]
      exact Nat.lt_min.mpr ⟨hi, hi'⟩),
    List.getElem_zip, ← getD_of_lt a za hi, ← getD_of_lt b zb hi']

/-- `map` read at an index inside the list. -/
theorem getD_map {α β : Type} (f : α → β) (a : List α) (z : α) (zb : β) {i : Nat}
    (hi : i < a.length) :
    (a.map f).getD i zb = f (a.getD i z) := by
  rw [getD_of_lt (a.map f) zb (by simpa using hi), List.getElem_map, ← getD_of_lt a z hi]

/-- `selectLanes` read at an index inside all three operands. -/
theorem selectLanes_getD {w : Nat} (cs : List (BitVec 1)) (a b : List (BitVec w))
    (i : Nat) (h1 : i < cs.length) (h2 : i < a.length) (h3 : i < b.length) :
    (selectLanes cs a b).getD i 0 =
      if cs.getD i 0 = 1 then a.getD i 0 else b.getD i 0 := by
  have hmin : i < (a.zip b).length := by
    rw [List.length_zip]; exact Nat.lt_min.mpr ⟨h2, h3⟩
  rw [selectLanes,
    getD_map _ _ _ _ (by rw [List.length_zip]; exact Nat.lt_min.mpr ⟨h1, hmin⟩),
    getD_zip cs (a.zip b) _ _ (0, (0, 0)) h1 hmin,
    getD_zip a b _ _ (0, 0) h2 h3]

theorem hxLowMask_len : hxLowMask.length = 16 := by decide
theorem hxNine_len : hxNine.length = 16 := by decide
theorem hxZero_len : hxZero.length = 16 := by decide

theorem hxLow_getD (l : List (BitVec 8)) (i : Nat) (hi : i < l.length)
    (hm : i < hxLowMask.length) :
    (hxLow l).getD i 0 = l.getD i 0 &&& hxLowMask.getD i 0 := by
  rw [hxLow, getD_map _ _ _ _ (by rw [List.length_zip]; exact Nat.lt_min.mpr ⟨hi, hm⟩),
    getD_zip l hxLowMask _ _ (0, 0) hi hm]

theorem hxNineSel_getD (c : List (BitVec 1)) (i : Nat) (hc : i < c.length)
    (h9 : i < hxNine.length) (hz : i < hxZero.length) :
    (hxNineSel c).getD i 0 =
      if c.getD i 0 = 1 then hxNine.getD i 0 else hxZero.getD i 0 :=
  selectLanes_getD c hxNine hxZero i hc h9 hz

/-- `hxPadd` at an index inside all its operands: the select's nine plus the low
nibble. -/
theorem hxPadd_getD (l : List (BitVec 8)) (c : List (BitVec 1)) (i : Nat)
    (hl : i < l.length) (hc : i < c.length)
    (hm : i < hxLowMask.length) (h9 : i < hxNine.length) (hz : i < hxZero.length) :
    (hxPadd l c).getD i 0 =
      (if c.getD i 0 = 1 then hxNine.getD i 0 else hxZero.getD i 0) +
        (l.getD i 0 &&& hxLowMask.getD i 0) := by
  have hsel_i : i < (hxNineSel c).length := by
    rw [hxNineSel, selectLanes_length]
    exact Nat.lt_min.mpr ⟨hc, Nat.lt_min.mpr ⟨h9, hz⟩⟩
  have hlow_i : i < (hxLow l).length := by
    rw [hxLow, List.length_map, List.length_zip]
    exact Nat.lt_min.mpr ⟨hl, hm⟩
  rw [hxPadd, getD_map _ _ _ _ (by
        rw [List.length_zip]; exact Nat.lt_min.mpr ⟨hsel_i, hlow_i⟩),
    getD_zip (hxNineSel c) (hxLow l) _ _ (0, 0) hsel_i hlow_i,
    hxNineSel_getD c i hc h9 hz, hxLow_getD l i hl hm]

/-- The nibble a lane's byte contributes, at the select it takes. -/
theorem hexNib_lane {x : BitVec 8} {c : BitVec 1}
    (hc : c = BitVec.ofBool (hexLetterTest x)) :
    hexNib x = ((if c = 1 then (9 : BitVec 8) else 0) + (x &&& BitVec.ofInt 8 15)).toNat := by
  rw [hexNib_eq, hexNib8_def]
  have hlet : (if c = 1 then (9 : BitVec 8) else 0) =
      (if hexLetterTest x then (9 : BitVec 8) else 0) := by
    subst hc
    cases hexLetterTest x <;> rfl
  rw [hlet, BitVec.add_comm]


/-- A list of length four or more is its first four elements and a suffix. -/
theorem cons4 {α : Type} (d : α) (l : List α) (h : 4 ≤ l.length) :
    l = l.getD 0 d :: l.getD 1 d :: l.getD 2 d :: l.getD 3 d :: l.drop 4 := by
  match l, h with
  | a :: b :: cc :: d :: rest, _ => rfl
  | [], h => simp at h
  | [_], h => simp at h
  | [_, _], h => simp at h
  | [_, _, _], h => simp at h

/-- The pmadd operand's first four lanes, at one lane. -/
theorem hxPadd_lane {bs : List (BitVec 8)} {c : List (BitVec 1)} (i : Nat) (hi : i < 4)
    (hbl : bs.length = 16) (hcl : c.length = 16) :
    (hxPadd bs c).getD i 0 =
      (if c.getD i 0 = 1 then (9 : BitVec 8) else 0) + (bs.getD i 0 &&& BitVec.ofInt 8 15) := by
  have hbl' : i < bs.length := by omega
  have hcl' : i < c.length := by omega
  rw [hxPadd_getD bs c i hbl' hcl' (by rw [hxLowMask_len]; omega)
    (by rw [hxNine_len]; omega) (by rw [hxZero_len]; omega)]
  have hi' : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
  have h9 : hxNine.getD i 0 = (9 : BitVec 8) := by
    rcases hi' with rfl | rfl | rfl | rfl <;> decide
  have hz : hxZero.getD i 0 = (0 : BitVec 8) := by
    rcases hi' with rfl | rfl | rfl | rfl <;> decide
  have hm : hxLowMask.getD i 0 = BitVec.ofInt 8 15 := by
    rcases hi' with rfl | rfl | rfl | rfl <;> decide
  rw [h9, hz, hm]

/-- **The hex unit, threaded.**  The block's `%and27.i` is `hex4`'s code unit at
the sixteen bytes it read, once the four lane tests hold and the letter select
carries each lane's letter test. -/
theorem hex4_hxCode {body : List UInt8} {q : Nat} {bs : List (BitVec 8)}
    {c : List (BitVec 1)}
    (hbytes : ∀ i, i < 16 → body[q + i]? = some (UInt8.ofBitVec (bs.getD i 0)))
    (hbl : bs.length = 16) (hcl : c.length = 16)
    (hcue : ∀ i, i < 4 → c.getD i 0 = BitVec.ofBool (hexLetterTest (bs.getD i 0)))
    (h0 : hexLaneTest (bs.getD 0 0) = true)
    (h1 : hexLaneTest (bs.getD 1 0) = true)
    (h2 : hexLaneTest (bs.getD 2 0) = true)
    (h3 : hexLaneTest (bs.getD 3 0) = true) :
    hex4 body q = some (((hxCode bs c) &&& BitVec.ofInt 32 65535).toNat) := by
  rw [hex4_of_lane_test hbytes h0 h1 h2 h3]
  congr 1
  have hlen : 4 ≤ (hxPadd bs c).length := by
    rw [hxPadd, List.length_map, List.length_zip, hxNineSel, selectLanes_length,
      hxLow, List.length_map, List.length_zip, hxLowMask_len, hxNine_len, hxZero_len]
    omega
  -- the four lane values, as the select and the low nibble build them
  have hl0 := hxPadd_lane (bs := bs) (c := c) 0 (by decide) hbl hcl
  have hl1 := hxPadd_lane (bs := bs) (c := c) 1 (by decide) hbl hcl
  have hl2 := hxPadd_lane (bs := bs) (c := c) 2 (by decide) hbl hcl
  have hl3 := hxPadd_lane (bs := bs) (c := c) 3 (by decide) hbl hcl
  have hn0 : hexNib (bs.getD 0 0) = ((if c.getD 0 0 = 1 then (9 : BitVec 8) else 0) +
      (bs.getD 0 0 &&& BitVec.ofInt 8 15)).toNat :=
    hexNib_lane (hcue 0 (by decide))
  have hn1 : hexNib (bs.getD 1 0) = ((if c.getD 1 0 = 1 then (9 : BitVec 8) else 0) +
      (bs.getD 1 0 &&& BitVec.ofInt 8 15)).toNat :=
    hexNib_lane (hcue 1 (by decide))
  have hn2 : hexNib (bs.getD 2 0) = ((if c.getD 2 0 = 1 then (9 : BitVec 8) else 0) +
      (bs.getD 2 0 &&& BitVec.ofInt 8 15)).toNat :=
    hexNib_lane (hcue 2 (by decide))
  have hn3 : hexNib (bs.getD 3 0) = ((if c.getD 3 0 = 1 then (9 : BitVec 8) else 0) +
      (bs.getD 3 0 &&& BitVec.ofInt 8 15)).toNat :=
    hexNib_lane (hcue 3 (by decide))
  have hnib0 : ((if c.getD 0 0 = 1 then (9 : BitVec 8) else 0) +
      (bs.getD 0 0 &&& BitVec.ofInt 8 15)).toNat < 16 := by rw [← hn0]; exact hexNib_lt h0
  have hnib1 : ((if c.getD 1 0 = 1 then (9 : BitVec 8) else 0) +
      (bs.getD 1 0 &&& BitVec.ofInt 8 15)).toNat < 16 := by rw [← hn1]; exact hexNib_lt h1
  have hnib2 : ((if c.getD 2 0 = 1 then (9 : BitVec 8) else 0) +
      (bs.getD 2 0 &&& BitVec.ofInt 8 15)).toNat < 16 := by rw [← hn2]; exact hexNib_lt h2
  have hnib3 : ((if c.getD 3 0 = 1 then (9 : BitVec 8) else 0) +
      (bs.getD 3 0 &&& BitVec.ofInt 8 15)).toNat < 16 := by rw [← hn3]; exact hexNib_lt h3
  have hfour : hexFour (bs.getD 0 0) (bs.getD 1 0) (bs.getD 2 0) (bs.getD 3 0) =
      4096 * hexNib (bs.getD 0 0) + 256 * hexNib (bs.getD 1 0) +
        16 * hexNib (bs.getD 2 0) + hexNib (bs.getD 3 0) := by
    simp only [hexFour]; omega
  rw [hfour]
  rw [hxCode, cons4 0 (hxPadd bs c) hlen, hexW8_eq, hexW16_eq, pmaddUbSw_cons,
    pmaddUbSw_cons, pmaddWd_cons, List.getD_cons_zero]
  rw [hl0, hl1, hl2, hl3]
  rw [pmaddUbSwLane_small hnib0 hnib1, pmaddUbSwLane_small hnib2 hnib3,
    pmaddWdLane_small (by rw [BitVec.toNat_ofNat]; omega)
      (by rw [BitVec.toNat_ofNat]; omega)]
  rw [← hn0, ← hn1, ← hn2, ← hn3]
  have e1 : (BitVec.ofNat 16 (16 * hexNib (bs.getD 0 0) + hexNib (bs.getD 1 0))).toNat =
      16 * hexNib (bs.getD 0 0) + hexNib (bs.getD 1 0) := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt]; omega
  have e2 : (BitVec.ofNat 16 (16 * hexNib (bs.getD 2 0) + hexNib (bs.getD 3 0))).toNat =
      16 * hexNib (bs.getD 2 0) + hexNib (bs.getD 3 0) := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt]; omega
  rw [e1, e2]
  rw [show (BitVec.ofInt 32 65535) = (BitVec.ofNat 32 65535) from BitVec.ofInt_ofNat 32 65535]
  rw [and65535_ofNat (by omega), BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  omega


/-! ### The pair's rule, read off the emitter's gate bits

`if.end3.i` computes four bits — the unit's high six bits at `0xD800`, room for
twelve more bytes, and the two trailing bytes `\` and `u` — and `if.then17.i` /
`land.lhs.true22.i` decide the second half.  Those are exactly `surrogateTail`'s
guard and its second-unit test, so the four laws below are the specification side of
that seam: the guard false is `none`, the guard true with no second unit is `none`,
the guard true with an out-of-range second unit is `none`, and the guard true with a
low surrogate is the pair's code point and twelve bytes.

The guard is written as the proposition `surrogateTail` itself tests, so the block's
four bits need only be identified with it (`and_one_iff`, and the `evalICmp`
readings) for the composition to call these. -/

/-- The guard `surrogateTail` tests, as one proposition. -/
def SurrogateGuard (bs : List UInt8) (k cp : Nat) : Prop :=
  0xD800 ≤ cp ∧ cp ≤ 0xDBFF ∧ k + 12 ≤ bs.length ∧
    bs[k + 6]? = some 0x5C ∧ bs[k + 7]? = some 0x75

theorem surrogateTail_eq_guard (bs : List UInt8) (k cp : Nat) :
    SurrogateGuard bs k cp ↔
      (0xD800 ≤ cp ∧ cp ≤ 0xDBFF ∧ k + 12 ≤ bs.length ∧
        bs[k + 6]? = some 0x5C ∧ bs[k + 7]? = some 0x75) := Iff.rfl

/-- The guard false: the parse falls back to the six-byte form of the first half,
which `escapeAt` writes as `none`. -/
theorem surrogateTail_none_of_guard {bs : List UInt8} {k cp : Nat}
    (h : ¬ SurrogateGuard bs k cp) :
    surrogateTail bs k cp = none := by
  unfold surrogateTail SurrogateGuard at *
  rw [if_neg h]

/-- The guard true and no second unit: `none`. -/
theorem surrogateTail_none_of_hex4_none {bs : List UInt8} {k cp : Nat}
    (hg : SurrogateGuard bs k cp) (h : hex4 bs (k + 8) = none) :
    surrogateTail bs k cp = none := by
  unfold surrogateTail SurrogateGuard at *
  rw [if_pos hg, h]

/-- The guard true and a second unit outside the low-surrogate range: `none`. -/
theorem surrogateTail_none_of_lo_out {bs : List UInt8} {k cp lo : Nat}
    (hg : SurrogateGuard bs k cp) (hlo : hex4 bs (k + 8) = some lo)
    (hr : ¬ (0xDC00 ≤ lo ∧ lo ≤ 0xDFFF)) :
    surrogateTail bs k cp = none := by
  unfold surrogateTail SurrogateGuard at *
  rw [if_pos hg, hlo]
  dsimp only
  rw [if_neg hr]

/-- The guard true and a low surrogate: the pair's code point, twelve bytes. -/
theorem surrogateTail_some_of_pair {bs : List UInt8} {k cp lo cp' : Nat}
    (hg : SurrogateGuard bs k cp) (hlo : hex4 bs (k + 8) = some lo)
    (hr : 0xDC00 ≤ lo ∧ lo ≤ 0xDFFF)
    (hcp : cp' = 0x10000 + (cp - 0xD800) * 0x400 + (lo - 0xDC00)) :
    surrogateTail bs k cp = some (cp', 12) := by
  unfold surrogateTail SurrogateGuard at *
  rw [if_pos hg, hlo]
  dsimp only
  rw [if_pos hr, hcp]

/-! ### Reading the gate bits

The block's four bits are combined with `&&&` at one bit, so the decomposition is
the conjunction; and each bit is one `evalICmp`, so its value is the comparison's
`Nat` proposition. -/

/-- One-bit `&&&` is conjunction. -/
theorem and_one_iff {a b : BitVec 1} : a &&& b = (1 : BitVec 1) ↔ a = 1 ∧ b = 1 := by
  rcases bv1_cases a with ha | ha <;> rcases bv1_cases b with hb | hb <;>
    rw [ha, hb] <;> decide

/-- One-bit `&&&` is zero at a zero operand. -/
theorem and_one_zero {a b : BitVec 1} (h : a &&& b = (0 : BitVec 1)) :
    a = 0 ∨ b = 0 := by
  rcases bv1_cases a with ha | ha <;> rcases bv1_cases b with hb | hb
  · exact Or.inl ha
  · exact Or.inl ha
  · exact Or.inr hb
  · rw [ha, hb] at h
    exact absurd h (by decide)

/-- `ule` at one is the `Nat` order. -/
theorem evalICmp_ule_one_iff {w : Nat} (x y : BitVec w) :
    evalICmp .ule x y = (1 : BitVec 1) ↔ x.toNat ≤ y.toNat := by
  unfold evalICmp
  cases h : BitVec.ule x y
  · have hn : ¬ x.toNat ≤ y.toNat := by
      intro hle
      have ht : BitVec.ule x y = true := (BitVec.ule_iff_toNat_le).2 hle
      rw [ht] at h
      exact Bool.noConfusion h
    simp [hn]
  · have hy : x.toNat ≤ y.toNat := (BitVec.ule_iff_toNat_le).1 h
    simp [hy]

/-! ### Axiom footprints -/

/-- info: 'LeanLLVM.Refinement.hexLetterTest' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms hexLetterTest

/-- info: 'LeanLLVM.Refinement.getD_of_lt' depends on axioms: [propext] -/
#guard_msgs in
#print axioms getD_of_lt

/-- info: 'LeanLLVM.Refinement.getD_zip' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms getD_zip

/-- info: 'LeanLLVM.Refinement.getD_map' depends on axioms: [propext] -/
#guard_msgs in
#print axioms getD_map

/-- info: 'LeanLLVM.Refinement.selectLanes_getD' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms selectLanes_getD

/-- info: 'LeanLLVM.Refinement.hxPadd_getD' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms hxPadd_getD

/-- info: 'LeanLLVM.Refinement.hexNib_lane' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms hexNib_lane

/-- info: 'LeanLLVM.Refinement.hxPadd_lane' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms hxPadd_lane

/-- info: 'LeanLLVM.Refinement.cons4' depends on axioms: [propext] -/
#guard_msgs in
#print axioms cons4

/-- info: 'LeanLLVM.Refinement.hex4_hxCode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms hex4_hxCode


/-- info: 'LeanLLVM.Refinement.SurrogateGuard' depends on axioms: [propext] -/
#guard_msgs in
#print axioms SurrogateGuard

/-- info: 'LeanLLVM.Refinement.surrogateTail_none_of_guard' depends on axioms: [propext] -/
#guard_msgs in
#print axioms surrogateTail_none_of_guard

/-- info: 'LeanLLVM.Refinement.surrogateTail_none_of_hex4_none' depends on axioms: [propext] -/
#guard_msgs in
#print axioms surrogateTail_none_of_hex4_none

/-- info: 'LeanLLVM.Refinement.surrogateTail_none_of_lo_out' depends on axioms: [propext] -/
#guard_msgs in
#print axioms surrogateTail_none_of_lo_out

/-- info: 'LeanLLVM.Refinement.surrogateTail_some_of_pair' depends on axioms: [propext] -/
#guard_msgs in
#print axioms surrogateTail_some_of_pair

/-- info: 'LeanLLVM.Refinement.and_one_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms and_one_iff

/-- info: 'LeanLLVM.Refinement.and_one_zero' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms and_one_zero

/-- info: 'LeanLLVM.Refinement.evalICmp_ule_one_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms evalICmp_ule_one_iff

end LeanLLVM.Refinement
