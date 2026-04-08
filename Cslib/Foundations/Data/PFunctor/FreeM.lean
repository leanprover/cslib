/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import Cslib.Init
public import Mathlib.Data.PFunctor.Univariate.Basic

/-!
# Free Monad of a Polynomial Functor

We define the free monad on a **polynomial functor** (`PFunctor`), and prove some basic properties.

The free monad `PFunctor.FreeM P` extends the W-type construction with an extra `pure`
constructor, yielding a monad that is free over the polynomial functor `P`.

This construction is ported from the [VCV-io](https://github.com/dtumad/VCV-io) library.

## Main Definitions

- `PFunctor.FreeM`: The free monad on a polynomial functor.
- `PFunctor.FreeM.lift`: Lift an object of the base polynomial functor into the free monad.
- `PFunctor.FreeM.liftA`: Lift a position of the base polynomial functor into the free monad.
- `PFunctor.FreeM.mapM`: Canonical mapping of `FreeM P` into any other monad.
- `PFunctor.FreeM.inductionOn`: Induction principle for `FreeM P`.
- `PFunctor.FreeM.construct`: Dependent eliminator for `FreeM P`.
-/

@[expose] public section

universe u v uA uB

namespace PFunctor

/-- The free monad on a polynomial functor.
This extends the `W`-type construction with an extra `pure` constructor. -/
inductive FreeM (P : PFunctor.{uA, uB}) : Type v → Type (max uA uB v)
  /-- A leaf node wrapping a pure value. -/
  | protected pure {α} (a : α) : FreeM P α
  /-- Invoke the operation `a : P.A` with continuation `cont : P.B a → FreeM P α`. -/
  | liftBind {α} (a : P.A) (cont : P.B a → FreeM P α) : FreeM P α
deriving Inhabited

namespace FreeM

variable {P : PFunctor.{uA, uB}} {α β γ : Type v}

instance : Pure (FreeM P) where pure := .pure

@[simp]
theorem pure_eq_pure : (pure : α → FreeM P α) = FreeM.pure := rfl

/-- Lift an object of the base polynomial functor into the free monad. -/
def lift (x : P.Obj α) : FreeM P α := FreeM.liftBind x.1 (fun y ↦ FreeM.pure (x.2 y))

/-- Lift a position of the base polynomial functor into the free monad. -/
def liftA (a : P.A) : FreeM P (P.B a) := lift ⟨a, id⟩

instance : MonadLift P (FreeM P) where
  monadLift x := FreeM.lift x

@[simp] lemma lift_ne_pure (x : P α) (y : α) :
    (lift x : FreeM P α) ≠ PFunctor.FreeM.pure y := by simp [lift]

@[simp] lemma pure_ne_lift (x : P α) (y : α) :
    PFunctor.FreeM.pure y ≠ (lift x : FreeM P α) := by simp [lift]

lemma monadLift_eq_lift (x : P.Obj α) : (x : FreeM P α) = FreeM.lift x := rfl

/-- Bind operator on `FreeM P` used in the monad definition. -/
protected def bind : FreeM P α → (α → FreeM P β) → FreeM P β
  | FreeM.pure a, f => f a
  | FreeM.liftBind a cont, f => FreeM.liftBind a (fun u ↦ FreeM.bind (cont u) f)

protected theorem bind_assoc (x : FreeM P α) (f : α → FreeM P β) (g : β → FreeM P γ) :
    (x.bind f).bind g = x.bind (fun a => (f a).bind g) := by
  induction x with
  | pure a => rfl
  | liftBind a cont ih =>
    simp [FreeM.bind] at *
    simp [ih]

instance : Bind (FreeM P) where bind := .bind

@[simp]
theorem bind_eq_bind {α β : Type v} :
    Bind.bind = (FreeM.bind : FreeM P α → _ → FreeM P β) := rfl

/-- Map a function over a `FreeM` computation. -/
@[simp]
def map (f : α → β) : FreeM P α → FreeM P β
  | .pure a => .pure (f a)
  | .liftBind a cont => .liftBind a fun u => FreeM.map f (cont u)

@[simp]
theorem id_map : ∀ x : FreeM P α, map id x = x
  | .pure a => rfl
  | .liftBind a cont => by simp_all [map, id_map]

theorem comp_map (h : β → γ) (g : α → β) :
    ∀ x : FreeM P α, map (h ∘ g) x = map h (map g x)
  | .pure a => rfl
  | .liftBind a cont => by simp_all [map, comp_map]

instance : Functor (FreeM P) where
  map := .map

@[simp]
theorem map_eq_map {α β : Type v} :
    Functor.map = FreeM.map (P := P) (α := α) (β := β) := rfl

/-- `.pure a` followed by `bind` collapses immediately. -/
@[simp]
lemma pure_bind (a : α) (f : α → FreeM P β) :
    (FreeM.pure a).bind f = f a := rfl

@[simp]
lemma bind_pure : ∀ x : FreeM P α, x.bind (.pure) = x
  | .pure a => rfl
  | .liftBind a cont => by simp [FreeM.bind, bind_pure]

@[simp]
lemma bind_pure_comp (f : α → β) : ∀ x : FreeM P α, x.bind (.pure ∘ f) = map f x
  | .pure a => rfl
  | .liftBind a cont => by simp only [FreeM.bind, map, bind_pure_comp]

@[simp]
lemma liftBind_bind (a : P.A) (cont : P.B a → FreeM P β) (f : β → FreeM P γ) :
    (FreeM.liftBind a cont).bind f = FreeM.liftBind a (fun u ↦ (cont u).bind f) := rfl

@[simp]
lemma lift_bind (x : P.Obj α) (f : α → FreeM P β) :
    (FreeM.lift x).bind f = FreeM.liftBind x.1 (fun a ↦ f (x.2 a)) := rfl

@[simp] lemma bind_eq_pure_iff (x : FreeM P α) (f : α → FreeM P β) (b : β) :
    x.bind f = FreeM.pure b ↔ ∃ a, x = pure a ∧ f a = pure b := by
  cases x <;> simp

@[simp] lemma pure_eq_bind_iff (x : FreeM P α) (f : α → FreeM P β) (b : β) :
    FreeM.pure b = x.bind f ↔ ∃ a, x = pure a ∧ pure b = f a := by
  cases x <;> simp

instance : LawfulFunctor (FreeM P) where
  map_const := rfl
  id_map := id_map
  comp_map _ _ := comp_map _ _

instance : Monad (FreeM P) where

instance : LawfulMonad (FreeM P) := LawfulMonad.mk'
  (bind_pure_comp := bind_pure_comp)
  (id_map := id_map)
  (pure_bind := pure_bind)
  (bind_assoc := FreeM.bind_assoc)

lemma pure_inj (a b : α) : FreeM.pure (P := P) a = FreeM.pure b ↔ a = b := by simp

@[simp] lemma liftBind_inj (a a' : P.A)
    (cont : P.B a → P.FreeM α) (cont' : P.B a' → P.FreeM α) :
    FreeM.liftBind a cont = FreeM.liftBind a' cont' ↔ ∃ h : a = a', h ▸ cont = cont' := by
  simp
  by_cases ha : a = a'
  · cases ha
    simp
  · simp [ha]

/-- Proving a predicate `C` of `FreeM P α` requires two cases:
* `pure a` for some `a : α`
* `liftBind a cont h` for some `a : P.A`, `cont : P.B a → FreeM P α`,
  and `h : ∀ y, C (cont y)` -/
@[elab_as_elim]
protected def inductionOn {C : FreeM P α → Prop}
    (pure : ∀ a, C (pure a))
    (liftBind : (a : P.A) → (cont : P.B a → FreeM P α) → (∀ y, C (cont y)) →
      C (FreeM.liftBind a cont)) :
    (x : FreeM P α) → C x
  | FreeM.pure a => pure a
  | FreeM.liftBind a cont =>
    liftBind a _ (fun u ↦ FreeM.inductionOn pure liftBind (cont u))

section construct

/-- Dependent eliminator for `FreeM P`. -/
@[elab_as_elim]
protected def construct {C : FreeM P α → Type*}
    (pure : (a : α) → C (pure a))
    (liftBind : (a : P.A) → (cont : P.B a → FreeM P α) → ((y : P.B a) → C (cont y)) →
      C (FreeM.liftBind a cont)) :
    (x : FreeM P α) → C x
  | .pure a => pure a
  | .liftBind a cont =>
    liftBind a _ (fun u ↦ FreeM.construct pure liftBind (cont u))

variable {C : FreeM P α → Type*} (h_pure : (a : α) → C (pure a))
  (h_liftBind : (a : P.A) → (cont : P.B a → FreeM P α) → ((y : P.B a) → C (cont y)) →
    C (FreeM.liftBind a cont))

@[simp]
lemma construct_pure (a : α) :
    FreeM.construct h_pure h_liftBind (pure a) = h_pure a := rfl

@[simp]
lemma construct_liftBind (a : P.A) (cont : P.B a → FreeM P α) :
    (FreeM.construct h_pure h_liftBind (FreeM.liftBind a cont) :
      C (FreeM.liftBind a cont)) =
      (h_liftBind a cont (fun u => FreeM.construct h_pure h_liftBind (cont u))) := rfl

end construct

section mapM

variable {m : Type uB → Type v} {α : Type uB}

/-- Canonical mapping of `FreeM P` into any other monad, given an interpretation
`interp : (a : P.A) → m (P.B a)`. -/
protected def mapM [Pure m] [Bind m] (interp : (a : P.A) → m (P.B a)) : FreeM P α → m α
  | .pure a => Pure.pure a
  | .liftBind a cont => (interp a) >>= (fun u ↦ (cont u).mapM interp)

variable [Monad m] (interp : (a : P.A) → m (P.B a))

@[simp]
lemma mapM_pure' (a : α) : (FreeM.pure a : FreeM P α).mapM interp = Pure.pure a := rfl

@[simp]
lemma mapM_liftBind (a : P.A) (cont : P.B a → FreeM P α) :
    (FreeM.liftBind a cont).mapM interp = interp a >>= fun u => (cont u).mapM interp := rfl

@[simp]
lemma mapM_pure (a : α) : (Pure.pure a : FreeM P α).mapM interp = Pure.pure a := rfl

variable [LawfulMonad m]

@[simp]
lemma mapM_bind {α β : Type uB} (x : FreeM P α) (f : α → FreeM P β) :
    (x.bind f).mapM interp = x.mapM interp >>= fun u => (f u).mapM interp := by
  induction x using FreeM.inductionOn with
  | pure _ => simp
  | liftBind a cont h => simp [h]

@[simp]
lemma mapM_bind' {α β : Type uB} (x : FreeM P α) (f : α → FreeM P β) :
    (x >>= f).mapM interp = x.mapM interp >>= fun u => (f u).mapM interp :=
  mapM_bind _ _ _

@[simp]
lemma mapM_map {α β : Type uB} (x : FreeM P α) (f : α → β) :
    FreeM.mapM interp (map f x) = f <$> FreeM.mapM interp x := by
  induction x using FreeM.inductionOn with
  | pure _ => simp
  | liftBind a cont h => simp [h]

@[simp]
lemma mapM_seq {α β : Type uB}
    (interp : (a : P.A) → m (P.B a)) (x : FreeM P (α → β)) (y : FreeM P α) :
    FreeM.mapM interp (x <*> y) = (FreeM.mapM interp x) <*> (FreeM.mapM interp y) := by
  simp only [seq_eq_bind_map, mapM_bind', map_eq_map, mapM_map]

@[simp]
lemma mapM_seqLeft {α β : Type uB}
    (interp : (a : P.A) → m (P.B a)) (x : FreeM P α) (y : FreeM P β) :
    FreeM.mapM interp (x <* y) = FreeM.mapM interp x <* FreeM.mapM interp y := by
  simp only [seqLeft_eq_bind, mapM_bind', mapM_pure]

@[simp]
lemma mapM_seqRight {α β : Type uB}
    (interp : (a : P.A) → m (P.B a)) (x : FreeM P α) (y : FreeM P β) :
    FreeM.mapM interp (x *> y) = FreeM.mapM interp x *> FreeM.mapM interp y := by
  simp only [seqRight_eq_bind, mapM_bind']

@[simp]
lemma mapM_lift (interp : (a : P.A) → m (P.B a)) (x : P.Obj α) :
    FreeM.mapM interp (FreeM.lift x) = x.2 <$> interp x.1 := by
  simp [lift]

@[simp]
lemma mapM_liftA (interp : (a : P.A) → m (P.B a)) (a : P.A) :
    FreeM.mapM interp (FreeM.liftA a) = interp a := by simp [liftA]

end mapM

end FreeM

end PFunctor
