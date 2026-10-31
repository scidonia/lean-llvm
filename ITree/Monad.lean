/-
The monad structure of interaction trees.

`map` and `bind` are the usual tree recursions: a result is mapped or bound
immediately, and a `tau` or a visible event recurses into its continuation.  The
laws are equations at strict tree equality, proved through the coinductive
`IEq` and then converted by `ieq_iff_eq`; no silent step is erased anywhere, so
`map id t = t` and `bind (bind t f) g = bind t (fun a => bind (f a) g)` are
statements about the trees themselves.

The instances are the upstream ones: `Functor`, `Monad`, `LawfulFunctor` and
`LawfulMonad` with the seven fields Lean's `LawfulMonad` asks for.  Adapted from
`mit-plv/lean4-itree` at revision
`7f48fefaa2f12f599e6c4aa2be1ef39d5466122b` (`ITree/Monad.lean`); see
`ITree/README.md` for provenance.

Signatures name the trees through the public `ITree` type of `ITree/Core.lean`,
never the `PFunctor.M` carrier; the public abbreviation `Tree` fixes the
universe levels that these polymorphic statements leave open.
-/
import ITree.IEq

namespace ITree

open ITree.Internal

universe u1 v u2

/-- Prove an unfolding lemma of a `corec'` definition: discharge the destructor
of the shape at the head of a child position. -/
macro "prove_unfold_lemma" : tactic => `(tactic|(
  (try simp only [dest_ret, dest_vis, dest_tau]) <;>
  (try simp only [vis, vis', tau, tau']) <;>
  (congr; try funext i) <;>
  solve
  | match i with
    | .up (.ofNat' 0) => rfl
    | .up (.ofNat' 1) => rfl
  | match i with
    | .up (.ofNat' 0) => rfl
))

section
variable {ε : Type u1 → Type v}
variable {α : Type u2} {β : Type u2} {γ : Type u2}

/-! ### Functor -/

/-- Map a function over the results of a tree. -/
def map (f : α → β) (t : ITree ε α) : ITree ε β :=
  .corec' (fun rec t =>
    match t.dest with
    | ⟨.ret v, _⟩ => .inl <| ret <| f v
    | ⟨.tau, c⟩ => .inr <| tau' <| rec <| c 0
    | ⟨.vis _ e, k⟩ => .inr <| vis' e (rec ∘ k)
  ) t

instance : Functor (ITree ε) where
  map := map

theorem map_ret (f : α → β) (v : α) : map f (ret v : ITree ε α) = ret (f v) := by
  conv => lhs; simp only [map]; rw [PFunctor.M.unfold_corec']
  prove_unfold_lemma

theorem map_tau (f : α → β) (c : ITree ε α) : map f (tau c) = tau (map f c) := by
  conv => lhs; simp only [map]; rw [PFunctor.M.unfold_corec']
  prove_unfold_lemma

theorem map_vis {δ : Type u1} (f : α → β) (e : ε δ) (k : δ → ITree ε α) :
    map f (vis e k) = vis e (fun x => map f (k x)) := by
  conv => lhs; simp only [map]; rw [PFunctor.M.unfold_corec']
  prove_unfold_lemma

/-! ### Monad -/

/-- Substitute a tree for each result of a tree. -/
def bind (t : ITree ε α) (f : α → ITree ε β) : ITree ε β :=
  .corec' (fun rec t =>
    match t.dest with
    | ⟨.ret v, _⟩ => .inl <| f v
    | ⟨.tau, c⟩ => .inr <| tau' <| rec <| c 0
    | ⟨.vis _ e, k⟩ => .inr <| vis' e (rec ∘ k)
  ) t

instance : Monad (ITree ε) where
  pure := ret
  bind := bind

theorem bind_map (f : ITree ε (α → β)) (x : ITree ε α) :
    (f >>= fun f => map f x) = f <*> x := by
  simp only [Bind.bind, Seq.seq, Functor.map]

theorem bind_ret (v : α) (f : α → ITree ε β) :
    bind (ret v : ITree ε α) f = f v := by
  conv => lhs; simp only [bind]; rw [PFunctor.M.unfold_corec']
  prove_unfold_lemma

theorem bind_tau (c : ITree ε α) (f : α → ITree ε β) :
    bind (tau c) f = tau (bind c f) := by
  conv => lhs; simp only [bind]; rw [PFunctor.M.unfold_corec']
  prove_unfold_lemma

theorem bind_vis {δ : Type u1} (e : ε δ) (k : δ → ITree ε α) (f : α → ITree ε β) :
    bind (vis e k) f = vis e (fun x => bind (k x) f) := by
  conv => lhs; simp only [bind]; rw [PFunctor.M.unfold_corec']
  prove_unfold_lemma

/-! ### Functor laws

`itree_eq t` turns a goal into a coinductive one and unfolds both sides at `t`'s
head constructor; every branch then closes by the coinductive hypothesis or by
the already-proved equations. -/

macro "itree_eq" t:ident : tactic => `(tactic|(
  rw [← ieq_iff_eq]
  revert $t
  pcofix cih
  intro t
  pfold
  apply dMatchOn t <;> (intros; rename_i h; subst h)
  · repeat rw [map_ret]
    repeat rw [bind_ret]
    constructor
  · repeat rw [map_tau]
    repeat rw [bind_tau]
    constructor; pleft; apply cih
  · repeat rw [map_vis]
    repeat rw [bind_vis]
    constructor; intros; pleft; apply cih
))

theorem id_map (t : ITree ε α) : map id t = t := by itree_eq t

theorem comp_map (g : α → β) (h : β → γ) (t : ITree ε α) :
    map (h ∘ g) t = map h (map g t) := by itree_eq t

instance : LawfulFunctor (ITree ε) where
  map_const := by simp only [Functor.mapConst, Functor.map, implies_true]
  id_map := id_map
  comp_map := comp_map

/-! ### Monad laws -/

theorem map_const_left (t : ITree ε α) (v : β) :
    map (Function.const α v) t = bind t fun _ => ret v := by
  itree_eq t

theorem map_const_right (t : ITree ε β) (v : α) :
    map (Function.const α id v) t = t := by
  rw [Function.const]
  apply id_map

macro "itree_eq_map_const" x:ident y:ident : tactic => `(tactic|(
  simp only [SeqRight.seqRight, SeqLeft.seqLeft, Seq.seq, Functor.map]
  rw [← ieq_iff_eq]
  revert $x $y
  pcofix cih
  intro x y
  pfold
  apply dMatchOn x <;> (intros; rename_i h; subst h)
  · repeat rw [map_ret]
    repeat rw [bind_ret]
    repeat rw [map_const_left]
    repeat rw [map_const_right]
    apply ieq_rfl
    intros _ _ h
    pright
    pinit at h
    pmon <;> try assumption
    ptop
  · repeat rw [map_tau]
    repeat rw [bind_tau]
    constructor; pleft; apply cih
  · repeat rw [map_vis]
    repeat rw [bind_vis]
    constructor; intros; pleft; apply cih
))

theorem seqLeft_eq (x : ITree ε α) (y : ITree ε β) :
    x <* y = Function.const β <$> x <*> y := by
  itree_eq_map_const x y

theorem seqRight_eq (x : ITree ε α) (y : ITree ε β) :
    x *> y = Function.const α id <$> x <*> y := by
  itree_eq_map_const x y

theorem pure_seq (g : α → β) (x : ITree ε α) : pure g <*> x = g <$> x := by
  simp only [Seq.seq, pure, bind_ret]

theorem bind_pure_comp (f : α → β) (x : ITree ε α) : bind x (pure ∘ f) = map f x := by
  itree_eq x

theorem pure_bind (x : α) (f : α → ITree ε β) : bind (pure x) f = f x := by
  simp only [pure, bind_ret]

theorem bind_assoc (x : ITree ε α) (f : α → ITree ε β) (g : β → ITree ε γ) :
    bind (bind x f) g = bind x fun x => bind (f x) g := by
  rw [← ieq_iff_eq]
  revert x f g
  pcofix cih
  intro x f g
  pfold
  apply dMatchOn x <;> (intros; rename_i h; subst h)
  · repeat rw [bind_ret]
    apply ieq_rfl
    intros _ _ h
    pinit at h
    pright
    pmon <;> try assumption
    ptop
  · repeat rw [bind_tau]
    constructor; pleft; apply cih
  · repeat rw [bind_vis]
    constructor; intros; pleft; apply cih

instance : LawfulMonad (ITree ε) where
  seqLeft_eq := seqLeft_eq
  seqRight_eq := seqRight_eq
  pure_seq := pure_seq
  bind_pure_comp := bind_pure_comp
  bind_map := bind_map
  pure_bind := pure_bind
  bind_assoc := bind_assoc

/-! ### Compatibility with `IEq`

Because `IEq` is exact, these are the equations rewritten through
`ieq_iff_eq`: corresponding inputs and continuations related by `IEq` stay
related after mapping or binding. -/

theorem map_congr {t1 t2 : ITree ε α} (f : α → β) (h : IEq t1 t2) :
    IEq (map f t1) (map f t2) := by
  rw [ieq_iff_eq] at h ⊢
  rw [h]

theorem bind_congr {t1 t2 : ITree ε α} {f g : α → ITree ε β}
    (h : IEq t1 t2) (hf : ∀ a, IEq (f a) (g a)) :
    IEq (bind t1 f) (bind t2 g) := by
  rw [ieq_iff_eq] at h ⊢
  have hf' : f = g := funext (fun a => (ieq_iff_eq _ _).mp (hf a))
  rw [h, hf']

theorem bind_congr_left {t1 t2 : ITree ε α} (f : α → ITree ε β) (h : IEq t1 t2) :
    IEq (bind t1 f) (bind t2 f) :=
  bind_congr h (fun _ => ieq_refl _)

theorem bind_congr_right {t : ITree ε α} {f g : α → ITree ε β}
    (hf : ∀ a, IEq (f a) (g a)) : IEq (bind t f) (bind t g) :=
  bind_congr (ieq_refl _) hf

end

end ITree
