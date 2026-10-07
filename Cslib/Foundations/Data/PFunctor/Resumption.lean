/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Cslib.Foundations.Data.PFunctor.Free.W
public import Cslib.Foundations.Data.PFunctor.M

/-!
# Coinductive resumptions

A resumption `r : PFunctor.Resumption P α` is a possibly non-terminating program that either
returns a value of `α` or performs an operation `a : P.A` and continues with a response
`b : P.B a`. It completes the polynomial tree types: `P.W` and `P.M` are the initial algebra and
final coalgebra of `P`, while `P.FreeM α` and `Resumption P α` are those of `X ↦ α ⊕ P X`, that
is, the W-type and M-type of `C α + P` (`PFunctor.FreeM.equivW`).

The representations are related by
```
P.W        ──── W.toM ────▶  P.M
 │ W.toFreeM                  │ M.toResumption
 ▼                            ▼
P.FreeM α  ── toResumption ─▶ Resumption P α
```
which commutes (`PFunctor.FreeM.toResumption_toFreeM`). The horizontal maps are injective, with
image the well-founded trees (`W.equivM`, `FreeM.equivWellFounded`), and `FreeM.toResumption` is a
monad morphism. The vertical maps are equivalences when `α` is empty (`FreeM.equivWOfIsEmpty`,
`Resumption.equivMOfIsEmpty`).

Resumptions extend free programs by infinite runs. Over the indeterminate `y`, with a single
operation and a unit response, they form Capretta's delay monad [Capretta2005], and they give
semantics to loops whose termination is not structural, such as rejection sampling or the
execution of a machine. This is the resumption monad of [PirogGibbons2014], the identity-monad
case of the coalgebraic resumptions of [GoncharovMiliusRauch2016]. Unlike the cofree comonad,
whose one-step view `α × P X` labels every node, a resumption returns a value only at a leaf.

## Main definitions

- `PFunctor.Resumption.dest`: the one-step view, an equivalence `destEquiv`, with a `cases`
  eliminator into returned values `pure a` and operations `(lift a).bind k`, as for
  `PFunctor.FreeM`.
- `PFunctor.Resumption.corec`: the corecursor, characterized by `corec_unique`.
- `PFunctor.Resumption.bisim`: coinduction through the relation lifting `StepRel`.
- `PFunctor.Resumption.bind`: sequencing, giving a lawful monad.
- `PFunctor.FreeM.toResumption`: the embedding of free programs.
- `PFunctor.Resumption.equivMOfIsEmpty`: resumptions with no return value are M-trees.

## References

* [Piróg and Gibbons, *The Coinductive Resumption Monad*][PirogGibbons2014]
* [Capretta, *General Recursion via Coinductive Types*][Capretta2005]
* [Goncharov, Milius and Rauch, *Complete Elgot Monads and Coalgebraic
  Resumptions*][GoncharovMiliusRauch2016]
-/

@[expose] public section

universe uA uB u v w

namespace PFunctor

/-- Possibly non-terminating programs over `P` returning a value of `α`: the M-type of `C α + P`,
whose W-type is `P.FreeM α`. -/
abbrev Resumption (P : PFunctor.{uA, uB}) (α : Type u) : Type (max u uA uB) :=
  M (C.{u, uB} α + P : PFunctor.{max u uA, uB})

namespace Resumption

variable {P : PFunctor.{uA, uB}} {α : Type u} {β : Type v} {γ : Type w}

/-- One step of a program over `P` returning `α`: a returned value or an operation with its
continuation. -/
def stepEquiv (P : PFunctor.{uA, uB}) (α : Type u) (X : Type v) :
    (C.{u, uB} α + P).Obj X ≃ α ⊕ P.Obj X :=
  (addObjEquiv _ _ X).trans ((constObjEquiv α X).sumCongr (Equiv.refl _))

@[simp]
theorem stepEquiv_mk_inl {X : Type v} (a : α) (f : (C.{u, uB} α + P).B (.inl a) → X) :
    stepEquiv P α X (.mk (.inl a) f) = .inl a := rfl

@[simp]
theorem stepEquiv_mk_inr {X : Type v} (a : P.A) (f : (C.{u, uB} α + P).B (.inr a) → X) :
    stepEquiv P α X (.mk (.inr a) f) = .inr (.mk a f) := rfl

theorem stepEquiv_map {X : Type v} {Y : Type w} (f : X → Y) (x : (C.{u, uB} α + P).Obj X) :
    stepEquiv P α Y ((C α + P).map f x) = Sum.map id (P.map f) (stepEquiv P α X x) := by
  cases x with | mk s g => cases s <;> rfl

/-- The one-step view of a resumption. -/
def destEquiv : Resumption P α ≃ α ⊕ P.Obj (Resumption P α) :=
  M.destEquiv.trans (stepEquiv P α _)

/-- Observe whether a resumption returns a value or performs an operation. -/
def dest (r : Resumption P α) : α ⊕ P.Obj (Resumption P α) :=
  destEquiv r

/-- The resumption returning `a` immediately. -/
protected def pure (a : α) : Resumption P α :=
  destEquiv.symm (.inl a)

/-- The resumption performing the operation `a` and continuing with `k`.

This is an implementation detail; the simp-normal form is `(lift a).bind k` (see `liftBind_eq`). -/
def liftBind (a : P.A) (k : P.B a → Resumption P α) : Resumption P α :=
  destEquiv.symm (.inr (.mk a k))

/-- Perform the operation `a`, returning its response. -/
def lift (a : P.A) : Resumption P (P.B a) :=
  liftBind a .pure

instance : Pure (Resumption P) where
  pure := Resumption.pure

@[simp]
theorem pure_eq_pure : (Resumption.pure : α → Resumption P α) = pure := rfl

@[simp]
theorem dest_mk (x : (C.{u, uB} α + P).Obj (Resumption P α)) :
    dest (M.mk x) = stepEquiv P α _ x := rfl

@[simp]
theorem dest_pure (a : α) : dest (pure a : Resumption P α) = .inl a :=
  destEquiv.apply_symm_apply _

theorem dest_liftBind (a : P.A) (k : P.B a → Resumption P α) :
    dest (liftBind a k) = .inr (.mk a k) :=
  destEquiv.apply_symm_apply _

@[simp]
theorem dest_lift (a : P.A) : dest (lift (P := P) a) = .inr (.mk a pure) :=
  dest_liftBind _ _

theorem dest_injective : Function.Injective (dest : Resumption P α → _) :=
  destEquiv.injective

@[simp]
theorem dest_inj {r s : Resumption P α} : dest r = dest s ↔ r = s :=
  dest_injective.eq_iff

/-- The resumption unfolding from a state by a step function. -/
def corec {X : Type v} (f : X → α ⊕ P.Obj X) : X → Resumption P α :=
  M.corec fun x => (stepEquiv P α X).symm (f x)

@[simp]
theorem dest_corec {X : Type v} (f : X → α ⊕ P.Obj X) (x : X) :
    dest (corec f x) = Sum.map id (P.map (corec f)) (f x) := by
  simp [dest, destEquiv, corec, M.dest_corec, stepEquiv_map]

/-- Finality: `corec f` is the only map into resumptions that unfolds by `f`. -/
theorem corec_unique {X : Type v} (f : X → α ⊕ P.Obj X) (g : X → Resumption P α)
    (hg : ∀ x, dest (g x) = Sum.map id (P.map g) (f x)) : g = corec f :=
  M.corec_unique _ g fun x =>
    (stepEquiv P α _).injective (by rw [stepEquiv_map, Equiv.apply_symm_apply]; exact hg x)

@[simp]
theorem corec_dest : corec (dest : Resumption P α → _) = id :=
  (corec_unique _ _ fun _ => by simp).symm

/-- Corecursion is natural in maps of states that commute with the step functions. -/
theorem corec_comp {X : Type v} {Y : Type w} (f : X → α ⊕ P.Obj X) (g : Y → α ⊕ P.Obj Y)
    (h : X → Y) (hh : ∀ x, g (h x) = Sum.map id (P.map h) (f x)) : corec g ∘ h = corec f :=
  corec_unique f _ fun x => by simp [hh, Sum.map_map]

/-- Lift a relation through one step: both sides return the same value, or perform the same
operation with related continuations. -/
inductive StepRel {X : Type v} {Y : Type w} (R : X → Y → Prop) :
    α ⊕ P.Obj X → α ⊕ P.Obj Y → Prop
  | pure (a : α) : StepRel R (.inl a) (.inl a)
  | liftBind (a : P.A) {k : P.B a → X} {k' : P.B a → Y} (h : ∀ i, R (k i) (k' i)) :
      StepRel R (.inr (.mk a k)) (.inr (.mk a k'))

theorem StepRel.refl {X : Type v} {R : X → X → Prop} (hR : ∀ x, R x x) :
    ∀ s : α ⊕ P.Obj X, StepRel R s s
  | .inl a => .pure a
  | .inr (.mk a _) => .liftBind a fun _ => hR _

/-- Coinduction: related resumptions are equal when related resumptions take related steps. -/
theorem bisim (R : Resumption P α → Resumption P α → Prop)
    (h : ∀ r s, R r s → StepRel R (dest r) (dest s)) {r s : Resumption P α} (hrs : R r s) :
    r = s := by
  have step : ∀ {x y}, StepRel R x y → ∃ a f f', (stepEquiv P α _).symm x = .mk a f ∧
      (stepEquiv P α _).symm y = .mk a f' ∧ ∀ i, R (f i) (f' i) := by
    rintro _ _ (⟨a⟩ | ⟨a, hk⟩)
    exacts [⟨.inl a, PEmpty.elim, PEmpty.elim, rfl, rfl, (·.elim)⟩, ⟨.inr a, _, _, rfl, rfl, hk⟩]
  refine M.bisim R (fun r s hrs => ?_) r s hrs
  rw [← (stepEquiv P α _).symm_apply_apply (M.dest r),
    ← (stepEquiv P α _).symm_apply_apply (M.dest s)]
  exact step (h r s hrs)

/-- The step function of `bind`: run the first resumption, then the continuation of its result. -/
def bindStep (k : α → Resumption P β) :
    Resumption P α ⊕ Resumption P β → β ⊕ P.Obj (Resumption P α ⊕ Resumption P β)
  | .inl r => (dest r).elim (fun a => Sum.map id (P.map .inr) (dest (k a)))
      fun x => .inr (P.map .inl x)
  | .inr r => Sum.map id (P.map .inr) (dest r)

/-- Sequence a resumption with a continuation for its returned value.

The builtin `>>=` notation should be preferred when `α` and `β` are in the same universe. -/
protected def bind (r : Resumption P α) (k : α → Resumption P β) : Resumption P β :=
  corec (bindStep k) (.inl r)

/-- Apply a function to the returned value.

The builtin `<$>` notation should be preferred when `α` and `β` are in the same universe. -/
protected def map (f : α → β) (r : Resumption P α) : Resumption P β :=
  r.bind (pure ∘ f)

@[simp]
theorem corec_bindStep_comp_inr (k : α → Resumption P β) : corec (bindStep k) ∘ Sum.inr = id :=
  (corec_comp dest (bindStep k) Sum.inr fun _ => rfl).trans corec_dest

@[simp]
theorem pure_bind (a : α) (k : α → Resumption P β) : (pure a : Resumption P α).bind k = k a :=
  dest_injective (by simp [Resumption.bind, bindStep, Sum.map_map])

theorem liftBind_bind_eq (a : P.A) (f : P.B a → Resumption P α) (k : α → Resumption P β) :
    (liftBind a f).bind k = liftBind a fun i => (f i).bind k :=
  dest_injective (by simp [Resumption.bind, bindStep, dest_liftBind]; rfl)

@[simp]
theorem liftBind_eq (a : P.A) (k : P.B a → Resumption P α) : liftBind a k = (lift a).bind k := by
  simp [lift, liftBind_bind_eq]

/-- Case analysis on whether a resumption returns a value or performs an operation. -/
@[elab_as_elim, cases_eliminator]
protected theorem cases {motive : Resumption P α → Prop} (pure : ∀ a, motive (pure a))
    (lift_bind : ∀ a k, motive ((lift a).bind k)) (r : Resumption P α) : motive r := by
  rw [← destEquiv.symm_apply_apply r]
  rcases destEquiv r with a | x
  · exact pure a
  · cases x with | mk a k => exact (liftBind_eq a k ▸ lift_bind a k : motive (liftBind a k))

@[simp]
theorem dest_lift_bind (a : P.A) (k : P.B a → Resumption P α) :
    dest ((lift a).bind (α := no_index (P.B a)) k) = .inr (.mk a k) := by
  rw [← liftBind_eq, dest_liftBind]

@[simp]
theorem liftBind_bind (a : P.A) (k : P.B a → Resumption P α) (k' : α → Resumption P β) :
    ((lift a).bind k).bind k' = (lift a).bind fun i => (k i).bind k' := by
  simp only [← liftBind_eq, liftBind_bind_eq]

@[simp]
theorem bind_pure (r : Resumption P α) : r.bind pure = r :=
  bisim (fun x y => x = y.bind pure) (fun _ y h => by
    subst h
    cases y with
    | pure a => simp only [pure_bind, dest_pure]; exact .pure a
    | lift_bind a k => simp only [liftBind_bind, dest_lift_bind]; exact .liftBind a fun _ => rfl)
    rfl

protected theorem bind_assoc (r : Resumption P α) (k : α → Resumption P β)
    (k' : β → Resumption P γ) : (r.bind k).bind k' = r.bind fun a => (k a).bind k' :=
  bisim (fun x y => x = y ∨ ∃ r, x = (r.bind k).bind k' ∧ y = r.bind fun a => (k a).bind k')
    (fun x y h => by
      obtain rfl | ⟨r, rfl, rfl⟩ := h
      · exact StepRel.refl (fun _ => .inl rfl) _
      · cases r with
        | pure a => simp only [pure_bind]; exact StepRel.refl (fun _ => .inl rfl) _
        | lift_bind a f =>
          simp only [liftBind_bind, dest_lift_bind]
          exact .liftBind a fun i => .inr ⟨f i, rfl, rfl⟩)
    (.inr ⟨r, rfl, rfl⟩)

@[simp]
theorem bind_pure_comp (f : α → β) (r : Resumption P α) : r.bind (pure ∘ f) = r.map f := rfl

@[simp]
theorem map_pure (f : α → β) (a : α) : (pure a : Resumption P α).map f = pure (f a) :=
  pure_bind _ _

@[simp]
theorem map_bind (f : β → γ) (r : Resumption P α) (k : α → Resumption P β) :
    (r.bind k).map f = r.bind fun a => (k a).map f :=
  Resumption.bind_assoc _ _ _

section Monad

variable {α β : Type u}

instance : Monad (Resumption P) where
  bind := Resumption.bind
  map := Resumption.map

/-- Note that this lemma does not always apply, as it is universe-constrained by `Bind.bind`. -/
@[simp]
theorem bind_eq_bind : (Resumption.bind : Resumption P α → _ → Resumption P β) = Bind.bind := rfl

/-- Note that this lemma does not always apply, as it is universe-constrained by `Functor.map`. -/
@[simp]
theorem map_eq_map : (Resumption.map : (α → β) → Resumption P α → _) = Functor.map := rfl

instance : LawfulMonad (Resumption P) := LawfulMonad.mk'
  (id_map := bind_pure)
  (pure_bind := pure_bind)
  (bind_assoc := Resumption.bind_assoc)
  (bind_pure_comp := bind_pure_comp)

@[simp]
theorem dest_lift_bind' (a : P.A) {α : Type uB} (k : P.B a → Resumption P α) :
    dest (Bind.bind (α := no_index (P.B a)) (lift a) k) = .inr (.mk a k) :=
  dest_lift_bind a k

end Monad

end Resumption

namespace FreeM

variable {P : PFunctor.{uA, uB}} {α : Type u} {β : Type v}

/-- Regard a free program as a resumption. Free programs are exactly the well-founded
resumptions (`equivWellFounded`). -/
def toResumption (x : P.FreeM α) : Resumption P α :=
  (toW x).toM

@[simp]
theorem toResumption_pure (a : α) : toResumption (pure a : P.FreeM α) = pure a :=
  Resumption.dest_injective (by rw [toResumption, toW_pure, W.toM_mk]; rfl)

theorem toResumption_lift_bind (a : P.A) (cont : P.B a → P.FreeM α) :
    toResumption ((lift a).bind cont) = (Resumption.lift a).bind fun b => toResumption (cont b) :=
  Resumption.dest_injective (by simp [toResumption]; rfl)

@[simp]
theorem toResumption_lift (a : P.A) :
    toResumption (α := no_index (P.B a)) (lift a) = Resumption.lift a := by
  simpa using toResumption_lift_bind a (pure : P.B a → P.FreeM (P.B a))

@[simp]
theorem toResumption_bind (x : P.FreeM α) (f : α → P.FreeM β) :
    toResumption (x.bind f) = (toResumption x).bind fun a => toResumption (f a) := by
  induction x with
  | pure a => simp
  | lift_bind a cont ih => simp [toResumption_lift_bind, ih]

@[simp]
theorem toResumption_map (f : α → β) (x : P.FreeM α) :
    toResumption (x.map f) = (toResumption x).map f := by
  simp [← bind_pure_comp, Resumption.map, Function.comp_def]

theorem isMonadHom_toResumption :
    Cslib.IsMonadHom P.FreeM (Resumption P) toResumption :=
  .mk' toResumption_pure toResumption_bind

@[simp]
theorem toResumption_bind' {α β : Type u} (x : P.FreeM α) (f : α → P.FreeM β) :
    toResumption (x >>= f) = toResumption x >>= fun a => toResumption (f a) :=
  toResumption_bind x f

@[simp]
theorem toResumption_map' {α β : Type u} (f : α → β) (x : P.FreeM α) :
    toResumption (f <$> x) = f <$> toResumption x :=
  toResumption_map f x

/-- `toResumption` interprets each operation as the corresponding resumption operation. -/
theorem toResumption_eq_liftM {α : Type uB} (x : P.FreeM α) :
    toResumption x = x.liftM Resumption.lift := by
  induction x <;> simp [*]

theorem toResumption_injective : Function.Injective (toResumption : P.FreeM α → _) :=
  fun _ _ h => equivW.injective (W.toM_injective h)

theorem isWellFounded_toResumption (x : P.FreeM α) : (toResumption x).IsWellFounded :=
  W.isWellFounded_toM _

/-- Free programs are exactly the well-founded resumptions. -/
def equivWellFounded : P.FreeM α ≃ {r : Resumption P α // r.IsWellFounded} :=
  equivW.trans W.equivM

@[simp]
theorem equivWellFounded_apply (x : P.FreeM α) :
    (equivWellFounded x : Resumption P α) = toResumption x := rfl

end FreeM

/-! ### Resumptions that never return -/

section IsEmpty

variable {P : PFunctor.{uA, uB}} {α : Type u}

/-- Regard an M-tree as a resumption that never returns. -/
def M.toResumption : P.M → Resumption P α :=
  Resumption.corec fun t => .inr (M.dest t)

@[simp]
theorem M.toResumption_mk (a : P.A) (f : P.B a → P.M) :
    (M.mk (.mk a f)).toResumption (α := α) =
      (Resumption.lift a).bind fun i => (f i).toResumption :=
  Resumption.dest_injective (by simp [M.toResumption]; rfl)

/-- Regard a resumption that cannot return as an M-tree. -/
def Resumption.toMOfIsEmpty [IsEmpty α] : Resumption P α → P.M :=
  M.corec fun r => (Resumption.dest r).elim isEmptyElim id

@[simp]
theorem Resumption.toMOfIsEmpty_lift_bind [IsEmpty α] (a : P.A) (k : P.B a → Resumption P α) :
    toMOfIsEmpty ((lift a).bind (α := no_index (P.B a)) k) =
      M.mk (.mk a fun i => toMOfIsEmpty (k i)) :=
  M.dest_injective (by simp [toMOfIsEmpty, M.dest_corec]; rfl)

@[simp]
theorem Resumption.toMOfIsEmpty_lift_bind' {α : Type uB} [IsEmpty α] (a : P.A)
    (k : P.B a → Resumption P α) :
    toMOfIsEmpty (Bind.bind (α := no_index (P.B a)) (lift a) k) =
      M.mk (.mk a fun i => toMOfIsEmpty (k i)) :=
  toMOfIsEmpty_lift_bind a k

@[simp]
theorem Resumption.toMOfIsEmpty_toResumption [IsEmpty α] (t : P.M) :
    toMOfIsEmpty (t.toResumption (α := α)) = t :=
  congrFun ((M.corec_comp M.dest _ M.toResumption fun _ => by simp [M.toResumption]).trans
    M.corec_dest) t

@[simp]
theorem M.toResumption_toMOfIsEmpty [IsEmpty α] (r : Resumption P α) :
    (Resumption.toMOfIsEmpty r).toResumption = r :=
  congrFun ((Resumption.corec_comp Resumption.dest _ Resumption.toMOfIsEmpty fun r => by
    cases r with
    | pure a => exact isEmptyElim a
    | lift_bind a k => simp [Function.comp_def]).trans Resumption.corec_dest) r

/-- With no possible return value, resumptions are exactly the M-trees. -/
@[simps]
def Resumption.equivMOfIsEmpty [IsEmpty α] : Resumption P α ≃ P.M where
  toFun := toMOfIsEmpty
  invFun := M.toResumption
  left_inv := M.toResumption_toMOfIsEmpty
  right_inv := toMOfIsEmpty_toResumption

/-- Embedding W-trees is compatible with the never-returning embeddings into free programs and
resumptions. -/
theorem FreeM.toResumption_toFreeM (w : P.W) :
    (W.toFreeM w : P.FreeM α).toResumption = M.toResumption w.toM := by
  induction w with
  | mk a f ih => simp [ih]

end IsEmpty

end PFunctor
