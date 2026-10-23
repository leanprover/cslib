/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Cslib.Foundations.Control.Monad.Free.Fold
public import Cslib.Foundations.Data.PFunctor.Basic
public import Cslib.Foundations.Data.PFunctor.Free.Fold

/-!
# Indexed effects as polynomial effects

An operation `op : F ι` of a type-indexed effect family `F` is a shape of the polynomial functor
`PFunctor.ofFamily F`, whose directions are the answers `ι`. This file shows that the free monads
`Cslib.FreeM F` and `(PFunctor.ofFamily F).FreeM` are isomorphic, compatibly with folds and
monadic interpretation, so programs over indexed effects can use the `PFunctor.FreeM` API.
The price is the shape universe `max (u + 1) v` of `PFunctor.ofFamily F`.

## Main definitions

- `Cslib.FreeM.toPFunctorFreeM`, `Cslib.FreeM.ofPFunctorFreeM`: the conversions.
- `Cslib.FreeM.equivPFunctorFreeM`: the conversions as an equivalence.

## Main statements

- `Cslib.FreeM.isMonadHom_toPFunctorFreeM`, `Cslib.FreeM.isMonadHom_ofPFunctorFreeM`: both
  conversions are monad morphisms.
- `Cslib.FreeM.foldFreeM_toPFunctorFreeM`, `Cslib.FreeM.liftM_toPFunctorFreeM`: folds and
  interpretations agree on both presentations.
-/

@[expose] public section

universe u v w w' z

namespace Cslib.FreeM

variable {F : Type u → Type v} {α : Type w} {β : Type w'}

/-- Regard a program over the effect family `F` as a program over `PFunctor.ofFamily F`. -/
def toPFunctorFreeM : FreeM F α → (PFunctor.ofFamily F).FreeM α
  | .pure a => .pure a
  | .liftBind (ι := ι) op cont => .liftBind ⟨ι, op⟩ fun b => toPFunctorFreeM (cont b)

/-- Regard a program over `PFunctor.ofFamily F` as a program over the effect family `F`. -/
def ofPFunctorFreeM : (PFunctor.ofFamily F).FreeM α → FreeM F α
  | .pure a => .pure a
  | .liftBind op cont => .liftBind op.2 fun b => ofPFunctorFreeM (cont b)

@[simp]
theorem toPFunctorFreeM_pure (a : α) : toPFunctorFreeM (pure a : FreeM F α) = pure a := rfl

@[simp]
theorem toPFunctorFreeM_lift {ι : Type u} (op : F ι) :
    toPFunctorFreeM (lift op) = PFunctor.FreeM.lift (P := .ofFamily F) ⟨ι, op⟩ := rfl

@[simp]
theorem toPFunctorFreeM_bind (x : FreeM F α) (f : α → FreeM F β) :
    toPFunctorFreeM (x.bind f) = (toPFunctorFreeM x).bind fun a => toPFunctorFreeM (f a) := by
  induction x with
  | pure a => rfl
  | lift_bind op cont ih =>
    exact congrArg (PFunctor.FreeM.liftBind (P := .ofFamily F) ⟨_, op⟩) (funext ih)

@[simp]
theorem toPFunctorFreeM_map (f : α → β) (x : FreeM F α) :
    toPFunctorFreeM (x.map f) = (toPFunctorFreeM x).map f := by
  induction x with
  | pure a => rfl
  | lift_bind op cont ih =>
    exact congrArg (PFunctor.FreeM.liftBind (P := .ofFamily F) ⟨_, op⟩) (funext ih)

@[simp]
theorem toPFunctorFreeM_bind' {α β : Type w} (x : FreeM F α) (f : α → FreeM F β) :
    toPFunctorFreeM (x >>= f) = toPFunctorFreeM x >>= fun a => toPFunctorFreeM (f a) :=
  toPFunctorFreeM_bind x f

@[simp]
theorem toPFunctorFreeM_map' {α β : Type w} (f : α → β) (x : FreeM F α) :
    toPFunctorFreeM (f <$> x) = f <$> toPFunctorFreeM x :=
  toPFunctorFreeM_map f x

@[simp]
theorem ofPFunctorFreeM_pure (a : α) :
    ofPFunctorFreeM (pure a : (PFunctor.ofFamily F).FreeM α) = pure a := rfl

@[simp]
theorem ofPFunctorFreeM_lift (op : (PFunctor.ofFamily F).A) :
    ofPFunctorFreeM (PFunctor.FreeM.lift op) = lift op.2 := rfl

@[simp]
theorem ofPFunctorFreeM_bind (x : (PFunctor.ofFamily F).FreeM α)
    (f : α → (PFunctor.ofFamily F).FreeM β) :
    ofPFunctorFreeM (x.bind f) = (ofPFunctorFreeM x).bind fun a => ofPFunctorFreeM (f a) := by
  induction x with
  | pure a => rfl
  | lift_bind op cont ih => exact congrArg (liftBind op.2) (funext ih)

@[simp]
theorem ofPFunctorFreeM_map (f : α → β) (x : (PFunctor.ofFamily F).FreeM α) :
    ofPFunctorFreeM (x.map f) = (ofPFunctorFreeM x).map f := by
  induction x with
  | pure a => rfl
  | lift_bind op cont ih => exact congrArg (liftBind op.2) (funext ih)

@[simp]
theorem ofPFunctorFreeM_bind' {α β : Type w} (x : (PFunctor.ofFamily F).FreeM α)
    (f : α → (PFunctor.ofFamily F).FreeM β) :
    ofPFunctorFreeM (x >>= f) = ofPFunctorFreeM x >>= fun a => ofPFunctorFreeM (f a) :=
  ofPFunctorFreeM_bind x f

@[simp]
theorem ofPFunctorFreeM_map' {α β : Type w} (f : α → β) (x : (PFunctor.ofFamily F).FreeM α) :
    ofPFunctorFreeM (f <$> x) = f <$> ofPFunctorFreeM x :=
  ofPFunctorFreeM_map f x

@[simp]
theorem ofPFunctorFreeM_toPFunctorFreeM (x : FreeM F α) :
    ofPFunctorFreeM (toPFunctorFreeM x) = x := by
  induction x with
  | pure a => rfl
  | lift_bind op cont ih => exact congrArg (liftBind op) (funext ih)

@[simp]
theorem toPFunctorFreeM_ofPFunctorFreeM (x : (PFunctor.ofFamily F).FreeM α) :
    toPFunctorFreeM (ofPFunctorFreeM x) = x := by
  induction x with
  | pure a => rfl
  | lift_bind op cont ih => exact congrArg (PFunctor.FreeM.liftBind op) (funext ih)

/-- Programs over an effect family are equivalent to programs over its polynomial functor. -/
@[simps]
def equivPFunctorFreeM : FreeM F α ≃ (PFunctor.ofFamily F).FreeM α where
  toFun := toPFunctorFreeM
  invFun := ofPFunctorFreeM
  left_inv := ofPFunctorFreeM_toPFunctorFreeM
  right_inv := toPFunctorFreeM_ofPFunctorFreeM

theorem isMonadHom_toPFunctorFreeM :
    IsMonadHom (FreeM F) (PFunctor.ofFamily F).FreeM toPFunctorFreeM :=
  .mk' toPFunctorFreeM_pure toPFunctorFreeM_bind

theorem isMonadHom_ofPFunctorFreeM :
    IsMonadHom (PFunctor.ofFamily F).FreeM (FreeM F) ofPFunctorFreeM :=
  .mk' ofPFunctorFreeM_pure ofPFunctorFreeM_bind

/-- Folding a program agrees with folding its polynomial presentation. -/
theorem foldFreeM_toPFunctorFreeM {γ : Type z} (onValue : α → γ)
    (onEffect : {ι : Type u} → F ι → (ι → γ) → γ) (x : FreeM F α) :
    (toPFunctorFreeM x).foldFreeM onValue (fun op : (PFunctor.ofFamily F).A => onEffect op.2) =
      x.foldFreeM onValue onEffect := by
  induction x with
  | pure a => rfl
  | lift_bind op cont ih => exact congrArg (onEffect op) (funext ih)

/-- Interpreting a program agrees with interpreting its polynomial presentation. -/
theorem liftM_toPFunctorFreeM {m : Type u → Type z} [Monad m] {α : Type u}
    (interp : {ι : Type u} → F ι → m ι) (x : FreeM F α) :
    (toPFunctorFreeM x).liftM (fun op : (PFunctor.ofFamily F).A => interp op.2) =
      x.liftM interp := by
  rw [PFunctor.FreeM.liftM_eq_foldFreeM, liftM_eq_foldFreeM, ← foldFreeM_toPFunctorFreeM]

theorem liftM_ofPFunctorFreeM {m : Type u → Type z} [Monad m] {α : Type u}
    (interp : {ι : Type u} → F ι → m ι) (x : (PFunctor.ofFamily F).FreeM α) :
    (ofPFunctorFreeM x).liftM interp =
      x.liftM (fun op : (PFunctor.ofFamily F).A => interp op.2) := by
  rw [← liftM_toPFunctorFreeM, toPFunctorFreeM_ofPFunctorFreeM]

end Cslib.FreeM
