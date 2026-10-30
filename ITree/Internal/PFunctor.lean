/-
The single mathlib import boundary of the interaction-tree library.

The tree layer is built on mathlib's univariate QPF support: the polynomial
functor `PFunctor`, its coinductive carrier `PFunctor.M`, and the `Vector3`
helpers the `Fin2` indices use.  Every other module imports this adapter rather
than `Mathlib` directly, so the dependency and the representation it brings are
visible in one file.

Adapted from `mit-plv/lean4-itree` at revision
`7f48fefaa2f12f599e6c4aa2be1ef39d5466122b` (`ITree/Utils.lean`); see
`ITree/README.md` for provenance and the list of deviations.
-/
import Mathlib.Data.QPF.Univariate.Basic
import Mathlib.Data.Vector3

namespace ITree.Internal

/-! ### `Vector3`/`Fin2` utilities

`PFunctor.M` objects carry their children in `ULift (Fin2 n)`, so the arities
zero and one need numerals, and the maps over one child need to be injective.
-/

instance {n : Nat} [Fin2.IsLT 0 n] : OfNat (ULift (Fin2 n)) 0 := ⟨.up <| .ofNat' 0⟩

instance {n : Nat} [Fin2.IsLT 1 n] : OfNat (ULift (Fin2 n)) 1 := ⟨.up <| .ofNat' 1⟩

/-- The eliminator out of the empty arity. -/
def elim0 {α : Sort u} (i : ULift (Fin2 0)) : α :=
  i.down.elim0 (C := fun _ => α)

/-- The constant map over the one-element arity. -/
def fin1Const {α} (v : α) :=
  fun (i : ULift (Fin2 1)) =>
    match i.down with | .ofNat' 0 => v

open Vector3 in
/-- The two-element constant map. -/
def fin2Const {α} (x y : α) :=
  fun (i : ULift (Fin2 2)) => [x, y] i.down

theorem elim0_eq_all {α} : ∀ x : ULift (Fin2 0) → α, x = elim0 :=
  fun x => funext fun z => @z.down.elim0 fun _ => x z = elim0 z

theorem fin1Const_inj {α} {x y : α}
    (h : fin1Const x = fin1Const y) : x = y := by
  have := congr (a₁ := 0) h rfl
  simp only [fin1Const] at this
  exact this

theorem fin1Const_fin0 {α} (c : ULift (Fin2 1) → α) : fin1Const (c 0) = c := by
  funext i
  match i with
  | .up (.ofNat' 0) => rfl

end ITree.Internal

/-! ### `PFunctor.M` utilities

The unfolding equation for `corec'` is what makes the coinductive constructors
of the tree computable.
-/

theorem PFunctor.M.unfold_corec'_left.{uA, uB, u} {P : PFunctor.{uA, uB}} {α : Type u}
    (F : P.M ⊕ α → P (P.M ⊕ α))
    (h_eq : ∀ l, F (.inl l) = ⟨l.dest.1, Sum.inl ∘ l.dest.2⟩) :
    ∀ l, PFunctor.M.corec F (.inl l) = l := by
  intros
  apply PFunctor.M.bisim (λ t1 t2 => t1 = PFunctor.M.corec _ (Sum.inl t2)) _ _ _ rfl
  intros t1 t2 h; subst h
  refine ⟨t2.dest.fst, _, t2.dest.snd, ?_, (PFunctor.Obj.eta _).symm, fun _ => rfl⟩
  rw [PFunctor.M.dest_corec, h_eq]; rfl

theorem PFunctor.M.unfold_corec'.{uA, uB, u} {P : PFunctor.{uA, uB}} {α : Type u}
    (F : ∀ {X : Type (max u uA uB)}, (α → X) → α → P.M ⊕ P X) (x : α) :
    .corec' F x =
    match F (@Sum.inr P.M α) x with
    | .inl l => l
    | .inr ⟨a, g⟩ => .mk ⟨a, fun i ↦
      match g i with
      | .inl l => l
      | .inr r => .corec' F r⟩ := by
  conv =>
    lhs
    simp only [PFunctor.M.corec', PFunctor.M.corec₁, PFunctor.M.corec_def, PFunctor.map, Sum.bind,
      Function.id_comp, PFunctor.Obj.mk, PFunctor.Obj.fst, PFunctor.Obj.snd]
  match F (@Sum.inr P.M α) x with
  | .inl v =>
    simp only
    conv => rhs; rw [← (PFunctor.M.mk_dest v)]
    change _ = PFunctor.M.mk ⟨v.dest.1, v.dest.2⟩
    congr; funext i
    apply unfold_corec'_left _ (fun _ => rfl)
  | .inr ⟨a, g⟩ =>
    simp only; congr; funext i
    simp only [Function.comp]
    match g i with
    | .inl l =>
      simp only
      apply unfold_corec'_left _ (fun _ => rfl)
    | .inr r =>
      simp only [PFunctor.M.corec', PFunctor.M.corec₁, PFunctor.map, Sum.bind, Function.id_comp,
        PFunctor.Obj.mk, PFunctor.Obj.fst, PFunctor.Obj.snd]
