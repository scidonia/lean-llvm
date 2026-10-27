/-
Certified constant propagation.

The pass works block by block.  Walking the instructions in order, it records
the literal value of every instruction whose operands are already literal, and
replaces later uses of that register by the literal.  The substitution is
proved semantics-preserving by an environment invariant: wherever a name is
substituted, the environment binds it to exactly that literal.

The pass does not delete the folded instructions; that is dead-code
elimination, which needs a refinement argument for undefined behaviour and is
the next milestone.  What it does is make constants visible to the branch
folder.
-/
import LeanLLVM.Transform.Basic

namespace LeanLLVM

/-- A substitution from register names to literal constants. -/
abbrev Subst := String → Option Const

def Subst.empty : Subst := fun _ => none

/-- Extend a substitution at one name.  `none` *removes* the name, which is
what keeps the invariant below true when an instruction rebinds a name that the
substitution already mentioned. -/
def Subst.update (σ : Subst) (n : String) (c : Option Const) : Subst :=
  fun x => if x = n then c else σ x

@[simp] theorem Subst.update_self (σ : Subst) (n : String) (c : Option Const) :
    Subst.update σ n c n = c := by
  simp [Subst.update]

theorem Subst.update_ne {σ : Subst} {n x : String} (c : Option Const) (h : x ≠ n) :
    Subst.update σ n c x = σ x := by
  simp [Subst.update, h]

/-- Read an operand as a usable literal, when it is one.  `undef` and `poison`
are undefined behaviour here, so they are never folded and never substituted. -/
def constOperand (σ : Subst) : Operand → Option Const
  | .reg n =>
      match σ n with
      | some c =>
          match c with
          | .undef => none
          | .poison => none
          | _ => some c
      | none => none
  | .imm c =>
      match c with
      | .undef => none
      | .poison => none
      | _ => some c

/-- Replace a register by its literal, when the substitution knows one. -/
def substOperand (σ : Subst) : Operand → Operand
  | .reg n =>
      match σ n with
      | some c => .imm c
      | none => .reg n
  | .imm c => .imm c

def substInstr (σ : Subst) : Instr → Instr
  | .binop d op w a b => .binop d op w (substOperand σ a) (substOperand σ b)
  | .icmp d pred w a b => .icmp d pred w (substOperand σ a) (substOperand σ b)
  | .select d ty c a b => .select d ty (substOperand σ c) (substOperand σ a) (substOperand σ b)
  | .trunc d wIn wOut v => .trunc d wIn wOut (substOperand σ v)
  | .zext d wIn wOut v => .zext d wIn wOut (substOperand σ v)
  | .sext d wIn wOut v => .sext d wIn wOut (substOperand σ v)
  | .alloca d ty align => .alloca d ty align
  | .load d ty p => .load d ty (substOperand σ p)
  | .store ty v p => .store ty (substOperand σ v) (substOperand σ p)

def substTerm (σ : Subst) : Term → Term
  | .ret ty v => .ret ty (v.map (substOperand σ))
  | .br d => .br d
  | .condbr c t f => .condbr (substOperand σ c) t f
  | .unreachable => .unreachable

/-- Fold a binary operation whose operands are already literals of the
instruction's width. -/
def foldBinop (op : BinOp) (w : Nat) : Const → Const → Option Const
  | .int w1 x, .int w2 y =>
      if w1 = w then
        if w2 = w then
          (evalBinopNat op w x.toNat y.toNat).map fun r => .int w (BitVec.ofNat w r)
        else none
      else none
  | _, _ => none

/-- Fold an integer comparison whose operands are literals of the instruction's
width. -/
def foldICmp (pred : IPred) (w : Nat) : Const → Const → Option Const
  | .int w1 x, .int w2 y =>
      if w1 = w then
        if w2 = w then some (.int 1 (evalICmpNat pred w x.toNat y.toNat)) else none
      else none
  | _, _ => none

/-- The literal result of an instruction, when it can be computed without
reading memory. -/
def foldInstr (σ : Subst) : Instr → Option Const
  | .binop _ op w a b =>
      match constOperand σ a, constOperand σ b with
      | some ca, some cb => foldBinop op w ca cb
      | _, _ => none
  | .icmp _ pred w a b =>
      match constOperand σ a, constOperand σ b with
      | some ca, some cb => foldICmp pred w ca cb
      | _, _ => none
  | .select _ _ c a b =>
      match constOperand σ c with
      | some (.int 1 bit) =>
          -- Both arms must be literals: folding an arm that is not a literal
          -- would drop a use of a register, and an unbound register is
          -- undefined behaviour in the source.
          match constOperand σ a, constOperand σ b with
          | some ca, some cb =>
              if bit = (1 : BitVec 1) then some ca
              else if bit = (0 : BitVec 1) then some cb
              else none
          | _, _ => none
      | _ => none
  | .trunc _ wIn wOut v =>
      match constOperand σ v with
      | some (.int w x) =>
          if w = wIn then some (.int wOut (BitVec.ofNat wOut (x.toNat % 2 ^ wOut))) else none
      | _ => none
  | .zext _ wIn wOut v =>
      match constOperand σ v with
      | some (.int w x) =>
          if w = wIn then some (.int wOut (BitVec.ofNat wOut x.toNat)) else none
      | _ => none
  | .sext _ wIn wOut v =>
      match constOperand σ v with
      | some (.int w x) =>
          if w = wIn then
            some (.int wOut (BitVec.ofNat wOut
              (BitVec.signExtend wOut (BitVec.ofNat wIn x.toNat)).toNat))
          else none
      | _ => none
  | _ => none

/-- The substitution after processing one instruction. -/
def foldStep (σ : Subst) (i : Instr) : Subst :=
  match i.dst? with
  | some d => Subst.update σ d (foldInstr σ i)
  | none => σ

/-- Substitute and fold an instruction list, returning the rewritten list and
the substitution that holds after it. -/
def foldInstrs : Subst → List Instr → List Instr × Subst
  | σ, [] => ([], σ)
  | σ, i :: is =>
      let r := foldInstrs (foldStep σ i) is
      (substInstr σ i :: r.1, r.2)

@[simp] theorem foldInstrs_nil (σ : Subst) : foldInstrs σ [] = ([], σ) := rfl

theorem foldInstrs_cons (σ : Subst) (i : Instr) (is : List Instr) :
    foldInstrs σ (i :: is) =
      (let r := foldInstrs (foldStep σ i) is
       (substInstr σ i :: r.1, r.2)) := rfl

/-- The instructions of a block after folding. -/
def foldBlockInstrs (b : Block) : List Instr :=
  (foldInstrs Subst.empty b.instrs).1

/-- The substitution that holds at the end of the block. -/
def foldBlockSubst (b : Block) : Subst :=
  (foldInstrs Subst.empty b.instrs).2

/-- The block after folding: rewritten instructions and a rewritten
terminator. -/
def foldBlock (b : Block) : Block :=
  { b with instrs := foldBlockInstrs b, term := substTerm (foldBlockSubst b) b.term }

/-- The pass: fold constants in every block of every function. -/
def foldConstants (f : Function) : Function :=
  { f with blocks := f.blocks.map foldBlock }

/-! ### Proofs -/

/-- Environment invariant: every register the substitution mentions is bound
to the literal value the substitution gives it. -/
def EnvEmbeds (env : Env) (σ : Subst) : Prop :=
  ∀ x c, σ x = some c → lookupName env x = Const.toValue c

theorem evalOperand_subst {σ : Subst} {s : State} (h : EnvEmbeds s.env σ) (o : Operand) :
    evalOperand s (substOperand σ o) = evalOperand s o := by
  cases o with
  | reg n =>
      simp only [substOperand, evalOperand]
      cases hσ : σ n with
      | none => rfl
      | some c => exact (h n c hσ).symm
  | imm c => rfl

theorem evalInstr_subst {σ : Subst} {s : State} (h : EnvEmbeds s.env σ) (i : Instr) :
    evalInstr s (substInstr σ i) = evalInstr s i := by
  cases i <;> simp [substInstr, evalInstr, evalOperand_subst h]

/-- A constant operand evaluates to its literal. -/
theorem evalOperand_const {σ : Subst} {s : State} {o : Operand} {c : Const}
    (h : EnvEmbeds s.env σ) (hc : constOperand σ o = some c) :
    evalOperand s o = Const.toValue c := by
  cases o with
  | reg n =>
      simp only [constOperand] at hc
      cases hσ : σ n with
      | none => simp [hσ] at hc
      | some c' =>
          simp only [hσ] at hc
          cases c' with
          | int w v => simp at hc; cases hc; exact h n (.int w v) hσ
          | null => simp at hc; cases hc; exact h n .null hσ
          | undef => simp at hc
          | poison => simp at hc
  | imm k =>
      simp only [constOperand] at hc
      cases k with
      | int w v => simp at hc; cases hc; rfl
      | null => simp at hc; cases hc; rfl
      | undef => simp at hc
      | poison => simp at hc

/-- A store does not touch the register environment. -/
theorem storeValue_env {s s' : State} {ty : Ty} {v : Value} {addr : Nat}
    (h : storeValue s ty v addr = some s') : s'.env = s.env := by
  unfold storeValue at h
  repeat' split at h
  all_goals try cases h
  all_goals rfl

/-- Every literal `constOperand` returns has a value. -/
theorem constOperand_toValue {σ : Subst} {o : Operand} {c : Const}
    (h : constOperand σ o = some c) : ∃ v, Const.toValue c = some v := by
  cases o with
  | reg n =>
      simp only [constOperand] at h
      cases hσ : σ n with
      | none => simp [hσ] at h
      | some c' =>
          simp only [hσ] at h
          cases c' with
          | int w v => simp at h; cases h; exact ⟨_, rfl⟩
          | null => simp at h; cases h; exact ⟨_, rfl⟩
          | undef => simp at h
          | poison => simp at h
  | imm k =>
      simp only [constOperand] at h
      cases k with
      | int w v => simp at h; cases h; exact ⟨_, rfl⟩
      | null => simp at h; cases h; exact ⟨_, rfl⟩
      | undef => simp at h
      | poison => simp at h

/-- Executing an instruction with a destination binds exactly that
destination. -/
theorem evalInstr_env {i : Instr} {s s' : State} (h : evalInstr s i = some s') :
    match i.dst? with
    | some d => ∃ v, s'.env = (d, v) :: s.env
    | none => s'.env = s.env := by
  cases i <;> simp only [Instr.dst?, evalInstr] at h ⊢ <;>
    (repeat' split at h) <;>
    (try simp_all) <;>
    (try (subst h; exact ⟨_, rfl⟩)) <;>
    (try (subst h; rfl)) <;>
    (try exact storeValue_env h)

/-- Executing a foldable instruction binds its destination to the folded
literal. -/
theorem evalInstr_fold {σ : Subst} {s : State} {i : Instr} {c : Const}
    (h : EnvEmbeds s.env σ) (hf : foldInstr σ i = some c) :
    ∃ v, Const.toValue c = some v ∧
      ∃ d, i.dst? = some d ∧ evalInstr s i = some (s.bind d v) := by
  cases i with
  | binop d op w a b =>
      simp only [foldInstr] at hf
      cases hca : constOperand σ a with
      | none => simp [hca] at hf
      | some ca =>
        cases hcb : constOperand σ b with
        | none => simp [hca, hcb] at hf
        | some cb =>
          simp only [hca, hcb] at hf
          cases ca with
          | int w1 x =>
            cases cb with
            | int w2 y =>
              simp only [foldBinop] at hf
              by_cases h1 : w1 = w
              · by_cases h2 : w2 = w
                · simp only [h1, h2, ite_true] at hf
                  cases hr : evalBinopNat op w x.toNat y.toNat with
                  | none => simp [hr] at hf
                  | some r =>
                      simp [hr] at hf
                      subst hf
                      cases h1
                      cases h2
                      refine ⟨.int w (BitVec.ofNat w r), rfl, d, rfl, ?_⟩
                      simp [evalInstr, evalOperand_const h hca, evalOperand_const h hcb,
                            Value.intToNat, Const.toValue, hr]
                · simp only [h1, h2, ite_true, ite_false] at hf
                  cases hf
              · simp only [h1, ite_false] at hf
                cases hf
            | null => simp [foldBinop] at hf
            | undef => simp [foldBinop] at hf
            | poison => simp [foldBinop] at hf
          | null => simp [foldBinop] at hf
          | undef => simp [foldBinop] at hf
          | poison => simp [foldBinop] at hf
  | icmp d pred w a b =>
      simp only [foldInstr] at hf
      cases hca : constOperand σ a with
      | none => simp [hca] at hf
      | some ca =>
        cases hcb : constOperand σ b with
        | none => simp [hca, hcb] at hf
        | some cb =>
          simp only [hca, hcb] at hf
          cases ca with
          | int w1 x =>
            cases cb with
            | int w2 y =>
              simp only [foldICmp] at hf
              by_cases h1 : w1 = w
              · by_cases h2 : w2 = w
                · simp only [h1, h2, ite_true] at hf
                  cases hf
                  cases h1
                  cases h2
                  refine ⟨.int 1 (evalICmpNat pred w x.toNat y.toNat), rfl, d, rfl, ?_⟩
                  simp [evalInstr, evalOperand_const h hca, evalOperand_const h hcb,
                        Value.intToNat, Const.toValue]
                · simp only [h1, h2, ite_true, ite_false] at hf
                  cases hf
              · simp only [h1, ite_false] at hf
                cases hf
            | null => simp [foldICmp] at hf
            | undef => simp [foldICmp] at hf
            | poison => simp [foldICmp] at hf
          | null => simp [foldICmp] at hf
          | undef => simp [foldICmp] at hf
          | poison => simp [foldICmp] at hf
  | select d ty cond a b =>
      simp only [foldInstr] at hf
      cases hcc : constOperand σ cond with
      | none => simp [hcc] at hf
      | some cc =>
        cases cc with
        | int w1 bit =>
          by_cases hw : w1 = 1
          · cases hw
            simp only [hcc] at hf
            cases hca : constOperand σ a with
            | none => simp [hca] at hf
            | some ca =>
              cases hcb : constOperand σ b with
              | none => simp [hca, hcb] at hf
              | some cb =>
                simp only [hca, hcb] at hf
                by_cases hb : bit = (1 : BitVec 1)
                · simp only [hb, ite_true] at hf
                  cases hf
                  obtain ⟨v, hv⟩ := constOperand_toValue hca
                  obtain ⟨vb, hvb⟩ := constOperand_toValue hcb
                  have eb : evalOperand s b = some vb := by
                    rw [evalOperand_const h hcb, hvb]
                  have ea : evalOperand s a = some v := by
                    rw [evalOperand_const h hca, hv]
                  refine ⟨v, hv, d, rfl, ?_⟩
                  simp [evalInstr, evalOperand_const h hcc, ea, eb, hb, Const.toValue]
                · by_cases hb0 : bit = (0 : BitVec 1)
                  · simp only [hb0, ite_true] at hf
                    cases hf
                    obtain ⟨v, hv⟩ := constOperand_toValue hcb
                    obtain ⟨va, hva⟩ := constOperand_toValue hca
                    have ea : evalOperand s a = some va := by
                      rw [evalOperand_const h hca, hva]
                    have eb : evalOperand s b = some v := by
                      rw [evalOperand_const h hcb, hv]
                    refine ⟨v, hv, d, rfl, ?_⟩
                    simp [evalInstr, evalOperand_const h hcc, ea, eb, hb0, Const.toValue]
                  · simp only [hb, hb0, ite_false] at hf
                    cases hf
          · simp [hcc, hw] at hf
        | null => simp [hcc] at hf
        | undef => simp [hcc] at hf
        | poison => simp [hcc] at hf
  | trunc d wIn wOut v =>
      simp only [foldInstr] at hf
      cases hcv : constOperand σ v with
      | none => simp [hcv] at hf
      | some cv =>
        simp only [hcv] at hf
        cases cv with
        | int w x =>
          by_cases hw : w = wIn
          · simp only [hw, ite_true] at hf
            cases hf
            cases hw
            refine ⟨.int wOut (BitVec.ofNat wOut (x.toNat % 2 ^ wOut)), rfl, d, rfl, ?_⟩
            simp [evalInstr, evalOperand_const h hcv, Const.toValue]
          · simp only [hw, ite_false] at hf
            cases hf
        | null => simp at hf
        | undef => simp at hf
        | poison => simp at hf
  | zext d wIn wOut v =>
      simp only [foldInstr] at hf
      cases hcv : constOperand σ v with
      | none => simp [hcv] at hf
      | some cv =>
        simp only [hcv] at hf
        cases cv with
        | int w x =>
          by_cases hw : w = wIn
          · simp only [hw, ite_true] at hf
            cases hf
            cases hw
            refine ⟨.int wOut (BitVec.ofNat wOut x.toNat), rfl, d, rfl, ?_⟩
            simp [evalInstr, evalOperand_const h hcv, Const.toValue]
          · simp only [hw, ite_false] at hf
            cases hf
        | null => simp at hf
        | undef => simp at hf
        | poison => simp at hf
  | sext d wIn wOut v =>
      simp only [foldInstr] at hf
      cases hcv : constOperand σ v with
      | none => simp [hcv] at hf
      | some cv =>
        simp only [hcv] at hf
        cases cv with
        | int w x =>
          by_cases hw : w = wIn
          · simp only [hw, ite_true] at hf
            cases hf
            cases hw
            refine ⟨.int wOut (BitVec.ofNat wOut
              (BitVec.signExtend wOut (BitVec.ofNat wIn x.toNat)).toNat), rfl, d, rfl, ?_⟩
            simp [evalInstr, evalOperand_const h hcv, Const.toValue]
          · simp only [hw, ite_false] at hf
            cases hf
        | null => simp at hf
        | undef => simp at hf
        | poison => simp at hf
  | alloca d ty align => simp [foldInstr] at hf
  | load d ty p => simp [foldInstr] at hf
  | store ty v p => simp [foldInstr] at hf

/-- Terminator substitution preserves execution once the invariant holds. -/
theorem execTerm_subst {σ : Subst} {s : State} (h : EnvEmbeds s.env σ) (t : Term) :
    execTerm s (substTerm σ t) = execTerm s t := by
  cases t with
  | ret ty v =>
      cases v with
      | none => rfl
      | some o =>
          cases ty with
          | void => rfl
          | int w =>
              change execTerm s (.ret (.int w) (some (substOperand σ o))) =
                execTerm s (.ret (.int w) (some o))
              simp only [execTerm]
              rw [evalOperand_subst h]
          | ptr =>
              change execTerm s (.ret .ptr (some (substOperand σ o))) =
                execTerm s (.ret .ptr (some o))
              simp only [execTerm]
              rw [evalOperand_subst h]
  | br d => rfl
  | condbr c a b =>
      change execTerm s (.condbr (substOperand σ c) a b) = execTerm s (.condbr c a b)
      simp only [execTerm]
      rw [evalOperand_subst h]
  | unreachable => rfl

/-- The substitution after a step satisfies the invariant. -/
theorem envEmbeds_foldStep {σ : Subst} {s s' : State} {i : Instr}
    (h : EnvEmbeds s.env σ) (hs : evalInstr s i = some s') :
    EnvEmbeds s'.env (foldStep σ i) := by
  unfold foldStep
  split
  · rename_i d hd
    intro x c hx
    have hx' : Subst.update σ d (foldInstr σ i) x = some c := hx
    by_cases hxd : x = d
    · subst hxd
      rw [Subst.update_self] at hx'
      obtain ⟨v, hv, d', hd', hexec⟩ := evalInstr_fold h hx'
      rw [hd'] at hd
      injection hd with hdd
      subst hdd
      rw [hexec] at hs
      injection hs with hs'
      subst hs'
      simp only [State.bind, lookupName_cons_self]
      exact hv.symm
    · rw [Subst.update_ne _ hxd] at hx'
      have henv := evalInstr_env hs
      rw [hd] at henv
      obtain ⟨v, hv⟩ := henv
      rw [hv]
      rw [lookupName_cons_ne v s.env (Ne.symm hxd)]
      exact h x c hx'
  · rename_i hnone
    have hstore : ∃ ty v p, i = .store ty v p := by
      cases i <;> simp [Instr.dst?] at hnone ⊢
    obtain ⟨ty, v, p, rfl⟩ := hstore
    have henv : s'.env = s.env := by
      have h' := evalInstr_env hs
      rw [show (Instr.store ty v p).dst? = none from rfl] at h'
      exact h'
    intro x c hx
    rw [henv]
    exact h x c hx

/-- Folding an instruction list preserves its denotation, and leaves the
environment invariant holding at the end. -/
theorem foldInstrs_correct (σ : Subst) (is : List Instr) (s : State)
    (h : EnvEmbeds s.env σ) :
    denoteCode (foldInstrs σ is).1 s = denoteCode is s ∧
      (∀ s', denoteCode is s = some s' → EnvEmbeds s'.env (foldInstrs σ is).2) := by
  induction is generalizing σ s with
  | nil =>
      refine ⟨rfl, ?_⟩
      intro s' hs'
      cases hs'
      exact h
  | cons i is ih =>
      generalize htail : foldInstrs (foldStep σ i) is = tail
      cases tail with
      | mk rest σ' =>
        simp only [foldInstrs_cons, htail]
        constructor
        · simp only [denoteCode, evalInstr_subst h]
          cases he : evalInstr s i with
          | none => rfl
          | some s'' =>
              have hstep := ih (foldStep σ i) s'' (envEmbeds_foldStep h he)
              rw [htail] at hstep
              exact hstep.1
        · intro s' hs'
          simp only [denoteCode] at hs'
          cases he : evalInstr s i with
          | none => simp [he] at hs'
          | some s'' =>
              simp only [he] at hs'
              have hstep := ih (foldStep σ i) s'' (envEmbeds_foldStep h he)
              rw [htail] at hstep
              exact hstep.2 s' hs'

/-- The block-level theorem: folding preserves the block's instruction
denotation, and the end-of-block substitution is valid for the terminator. -/
theorem foldBlock_denote (b : Block) (s : State) :
    denoteCode (foldBlockInstrs b) s = denoteCode b.instrs s ∧
      (∀ s', denoteCode b.instrs s = some s' →
        execTerm s' (foldBlock b).term = execTerm s' b.term) := by
  have h := foldInstrs_correct Subst.empty b.instrs s
    (fun x c hx => by simp [Subst.empty] at hx)
  exact ⟨h.1, fun s' hs' => execTerm_subst (h.2 s' hs') b.term⟩

/-- One control step is unchanged by constant folding. -/
theorem step_foldConstants (f : Function) (s : State) :
    step (foldConstants f) s = step f s := by
  simp only [step, foldConstants, Function.findBlock]
  rw [findBlockList_map (g := foldBlock) (fun b => rfl) f.blocks s.pc]
  cases hb : findBlockList f.blocks s.pc with
  | none => simp
  | some b =>
      simp only [Option.map_some]
      have hblock := foldBlock_denote b s
      simp only [foldBlock] at hblock ⊢
      rw [hblock.1]
      split
      · rfl
      · rename_i s' hs'
        exact hblock.2 s' hs'

/-- A whole run is unchanged by constant folding. -/
theorem runFuel_foldConstants (n : Nat) (f : Function) (s : State) :
    runFuel n (foldConstants f) s = runFuel n f s := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
      rw [runFuel_succ, runFuel_succ, step_foldConstants]
      cases hs : step f s with
      | ub => rfl
      | ret v s' => rfl
      | jump s' => exact ih s'

theorem foldBlock_name (b : Block) : (foldBlock b).name = b.name := rfl

theorem foldBlock_name_fun : ((fun x => x.name) ∘ foldBlock) = (fun b => b.name) := by
  funext b
  exact foldBlock_name b

theorem entry?_foldConstants (f : Function) :
    (foldConstants f).entry? = f.entry? := by
  simp [Function.entry?, foldConstants, List.head?_map, foldBlock_name_fun]

theorem initState_foldConstants (f : Function) (args : List Value) :
    initState (foldConstants f) args = initState f args := by
  simp [initState, foldConstants, Function.entry?, List.head?_map, foldBlock_name_fun]

/-- Constant folding preserves the observable behaviour exactly. -/
theorem foldConstants_beh (f : Function) (args : List Value) (o : Outcome) :
    Beh (foldConstants f) args o ↔ Beh f args o := by
  unfold Beh
  simp only [initState_foldConstants, runFuel_foldConstants]

/-- The certified pass. -/
def constantPropagation : Pass where
  name := "constprop"
  run := foldConstants

theorem constantPropagation_sound : constantPropagation.Sound :=
  fun f => Refines.of_iff (foldConstants_beh f)

end LeanLLVM
