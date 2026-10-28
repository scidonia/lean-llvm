/-
A refinement relation for a pure 64-bit seam, with an explicit boundary
contract `Γ`.

The shape is the one the LLVM development uses:

  Γ ⊢ target ⊑ source

meaning every behaviour the target can produce on an input admitted by Γ is a
behaviour the source can produce.  For total, deterministic pure functions the
relation is equality under `Γ.pre`; `SemRefines` records the option-valued form
so the same statement can be reused when partiality or undefined behaviour
enters.
-/
import Init.Data.BitVec

namespace LeanLLVM.Vellum

/-- A boundary contract for a pure `BitVec 64 → BitVec 64` seam.

`pre` admits the inputs the caller promises; `post` is the observable
guarantee the seam must meet.  A future memory-aware contract adds heap,
ownership, aliasing and target-configuration fields here; the pure slice keeps
the two fields it actually uses. -/
structure Contract where
  pre : BitVec 64 → Prop
  post : BitVec 64 → BitVec 64 → Prop

/-- Total semantics of a pure function, in the shape used by the LLVM
refinement relation. -/
def Sem (f : BitVec 64 → BitVec 64) : BitVec 64 → Option (BitVec 64) :=
  fun x => some (f x)

/-- Behaviour inclusion under the contract's precondition. -/
def SemRefines (Γ : Contract) (target source : BitVec 64 → Option (BitVec 64)) : Prop :=
  ∀ x y, Γ.pre x → target x = some y → source x = some y

/-- Pure equality form: under the precondition, the target returns what the
source returns. -/
def Refines (Γ : Contract) (target source : BitVec 64 → BitVec 64) : Prop :=
  ∀ x, Γ.pre x → target x = source x

/-- `Γ ⊢ target ⊑ source`. -/
notation:50 Γ:max " ⊢ " target " ⊑ " source => Refines Γ target source

/-- The option-valued relation and the equality form agree for total pure
functions. -/
theorem semRefines_total {Γ : Contract} {t s : BitVec 64 → BitVec 64} :
    SemRefines Γ (Sem t) (Sem s) ↔ Refines Γ t s := by
  constructor
  · intro h x hx
    exact (Option.some.inj (h x (t x) hx rfl)).symm
  · intro h x y hx hy
    cases hy
    exact congrArg some (h x hx).symm

theorem Refines.refl (Γ : Contract) (f : BitVec 64 → BitVec 64) : Γ ⊢ f ⊑ f :=
  fun _ _ => rfl

theorem Refines.trans {Γ : Contract} {a b c : BitVec 64 → BitVec 64}
    (hab : Γ ⊢ a ⊑ b) (hbc : Γ ⊢ b ⊑ c) : Γ ⊢ a ⊑ c :=
  fun x hx => (hab x hx).trans (hbc x hx)

theorem Refines.symm {Γ : Contract} {a b : BitVec 64 → BitVec 64}
    (h : Γ ⊢ a ⊑ b) : Γ ⊢ b ⊑ a :=
  fun x hx => (h x hx).symm

/-- The source meets the contract's postcondition. -/
def Correct (Γ : Contract) (f : BitVec 64 → BitVec 64) : Prop :=
  ∀ x, Γ.pre x → Γ.post x (f x)

/-- Correctness transfers from source to target along refinement. -/
theorem Correct.of_refines {Γ : Contract} {t s : BitVec 64 → BitVec 64}
    (hr : Γ ⊢ t ⊑ s) (hs : Correct Γ s) : Correct Γ t :=
  fun x hx => by
    rw [hr x hx]
    exact hs x hx

/-! ### Contextual replacement -/

/-- A caller context: it computes with the seam at a list of arguments.  The
context is represented by the arguments it passes to the seam and a fold over
their results. -/
structure Context where
  args : BitVec 64 → List (BitVec 64)
  pre : BitVec 64 → Prop

/-- The context only calls the seam at admissible inputs. -/
def Context.admissible (Γ : Contract) (C : Context) : Prop :=
  ∀ x, C.pre x → ∀ a ∈ C.args x, Γ.pre a

/-- The observable result of a context, given a seam implementation. -/
def Context.run (C : Context) (f : BitVec 64 → BitVec 64) (x : BitVec 64) : BitVec 64 :=
  (C.args x).foldl (fun acc a => acc + f a) 0

theorem foldl_add_congr {f g : BitVec 64 → BitVec 64} (init : BitVec 64) :
    ∀ (l : List (BitVec 64)), (∀ a ∈ l, f a = g a) →
      l.foldl (fun acc a => acc + f a) init = l.foldl (fun acc a => acc + g a) init
  | [], _ => rfl
  | a :: as, h => by
      simp only [List.foldl_cons]
      rw [h a (by simp)]
      exact foldl_add_congr (init + g a) as (fun b hb => h b (by simp [hb]))

/-- Replacing a seam by a refinement preserves every caller that only calls it
at admissible inputs. -/
theorem Context.refines {Γ : Contract} {t s : BitVec 64 → BitVec 64} {C : Context}
    (h : Γ ⊢ t ⊑ s) (ha : C.admissible Γ) :
    ∀ x, C.pre x → C.run t x = C.run s x := by
  intro x hx
  unfold Context.run
  exact foldl_add_congr 0 (C.args x) (fun a ha' => h a (ha x hx a ha'))

end LeanLLVM.Vellum
