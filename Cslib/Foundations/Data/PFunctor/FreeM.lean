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

This construction is ported from the [VCV-io](https://github.com/Verified-zkEVM/VCV-io) library.

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
  | pure {α} (a : α) : FreeM P α
  /-- A node with shape `a : P.A` and subtrees given by the continuation
  `cont : P.B a → FreeM P α`. -/
  | roll {α} (a : P.A) (cont : P.B a → FreeM P α) : FreeM P α
deriving Inhabited

namespace FreeM

variable {P : PFunctor.{uA, uB}} {α β γ : Type v}

/-- Lift an object of the base polynomial functor into the free monad. -/
@[always_inline, inline, reducible]
def lift (x : P.Obj α) : FreeM P α := FreeM.roll x.1 (fun y ↦ FreeM.pure (x.2 y))

/-- Lift a position of the base polynomial functor into the free monad. -/
@[always_inline, inline, reducible]
def liftA (a : P.A) : FreeM P (P.B a) := lift ⟨a, id⟩

instance : MonadLift P (FreeM P) where
  monadLift x := FreeM.lift x

@[simp] lemma lift_ne_pure (x : P α) (y : α) :
    (lift x : FreeM P α) ≠ PFunctor.FreeM.pure y := by simp [lift]

@[simp] lemma pure_ne_lift (x : P α) (y : α) :
    PFunctor.FreeM.pure y ≠ (lift x : FreeM P α) := by simp [lift]

lemma monadLift_eq_lift (x : P.Obj α) : (x : FreeM P α) = FreeM.lift x := rfl

/-- Bind operator on `FreeM P` used in the monad definition. -/
@[always_inline, inline]
protected def bind : FreeM P α → (α → FreeM P β) → FreeM P β
  | FreeM.pure a, f => f a
  | FreeM.roll a cont, f => FreeM.roll a (fun u ↦ FreeM.bind (cont u) f)

@[simp]
lemma bind_pure (a : α) (f : α → FreeM P β) :
    FreeM.bind (FreeM.pure a) f = f a := rfl

@[simp]
lemma bind_roll (a : P.A) (cont : P.B a → FreeM P β) (f : β → FreeM P γ) :
    FreeM.bind (FreeM.roll a cont) f = FreeM.roll a (fun u ↦ FreeM.bind (cont u) f) := rfl

@[simp]
lemma bind_lift (x : P.Obj α) (f : α → FreeM P β) :
    FreeM.bind (FreeM.lift x) f = FreeM.roll x.1 (fun a ↦ f (x.2 a)) := rfl

@[simp] lemma bind_eq_pure_iff (x : FreeM P α) (f : α → FreeM P β) (b : β) :
    FreeM.bind x f = FreeM.pure b ↔ ∃ a, x = pure a ∧ f a = pure b := by
  cases x <;> simp

@[simp] lemma pure_eq_bind_iff (x : FreeM P α) (f : α → FreeM P β) (b : β) :
    FreeM.pure b = FreeM.bind x f ↔ ∃ a, x = pure a ∧ pure b = f a := by
  cases x <;> simp

instance : Monad (FreeM P) where
  pure := FreeM.pure
  bind := FreeM.bind

lemma monad_pure_def (a : α) : (pure a : FreeM P α) = FreeM.pure a := rfl

lemma monad_bind_def (x : FreeM P α) (f : α → FreeM P β) :
    x >>= f = FreeM.bind x f := rfl

instance : LawfulMonad (FreeM P) :=
  LawfulMonad.mk' (FreeM P)
    (fun x ↦ by
      induction x with
      | pure _ => rfl
      | roll a _ h => refine congr_arg (FreeM.roll a) (funext fun i ↦ h i))
    (fun x f ↦ rfl)
    (fun x f g ↦ by
      induction x with
      | pure _ => rfl
      | roll a _ h => refine congr_arg (FreeM.roll a) (funext fun i ↦ h i))

lemma pure_inj (a b : α) : FreeM.pure (P := P) a = FreeM.pure b ↔ a = b := by simp

@[simp] lemma roll_inj (a a' : P.A)
    (cont : P.B a → P.FreeM α) (cont' : P.B a' → P.FreeM α) :
    FreeM.roll a cont = FreeM.roll a' cont' ↔ ∃ h : a = a', h ▸ cont = cont' := by
  simp
  by_cases ha : a = a'
  · cases ha
    simp
  · simp [ha]

/-- Proving a predicate `C` of `FreeM P α` requires two cases:
* `pure a` for some `a : α`
* `roll a cont h` for some `a : P.A`, `cont : P.B a → FreeM P α`, and `h : ∀ y, C (cont y)` -/
@[elab_as_elim]
protected def inductionOn {C : FreeM P α → Prop}
    (pure : ∀ a, C (pure a))
    (roll : (a : P.A) → (cont : P.B a → FreeM P α) → (∀ y, C (cont y)) →
      C (FreeM.roll a cont)) :
    (x : FreeM P α) → C x
  | FreeM.pure a => pure a
  | FreeM.roll a cont => roll a _ (fun u ↦ FreeM.inductionOn pure roll (cont u))

section construct

/-- Dependent eliminator for `FreeM P`. -/
@[elab_as_elim]
protected def construct {C : FreeM P α → Type*}
    (pure : (a : α) → C (pure a))
    (roll : (a : P.A) → (cont : P.B a → FreeM P α) → ((y : P.B a) → C (cont y)) →
      C (FreeM.roll a cont)) :
    (x : FreeM P α) → C x
  | .pure a => pure a
  | .roll a cont => roll a _ (fun u ↦ FreeM.construct pure roll (cont u))

variable {C : FreeM P α → Type*} (h_pure : (a : α) → C (pure a))
  (h_roll : (a : P.A) → (cont : P.B a → FreeM P α) → ((y : P.B a) → C (cont y)) →
    C (FreeM.roll a cont))

@[simp]
lemma construct_pure (a : α) : FreeM.construct h_pure h_roll (pure a) = h_pure a := rfl

@[simp]
lemma construct_roll (a : P.A) (cont : P.B a → FreeM P α) :
    (FreeM.construct h_pure h_roll (FreeM.roll a cont) : C (FreeM.roll a cont)) =
      (h_roll a cont (fun u => FreeM.construct h_pure h_roll (cont u))) := rfl

end construct

section mapM

variable {m : Type uB → Type v} {α : Type uB}

/-- Canonical mapping of `FreeM P` into any other monad, given a map `s : (a : P.A) → m (P.B a)`.
-/
protected def mapM [Pure m] [Bind m] (s : (a : P.A) → m (P.B a)) : FreeM P α → m α
  | .pure a => Pure.pure a
  | .roll a cont => (s a) >>= (fun u ↦ (cont u).mapM s)

variable [Monad m] (s : (a : P.A) → m (P.B a))

@[simp]
lemma mapM_pure' (a : α) : (FreeM.pure a : FreeM P α).mapM s = Pure.pure a := rfl

@[simp]
lemma mapM_roll (a : P.A) (cont : P.B a → FreeM P α) :
    (FreeM.roll a cont).mapM s = s a >>= fun u => (cont u).mapM s := rfl

@[simp] lemma mapM_pure (a : α) : (Pure.pure a : FreeM P α).mapM s = Pure.pure a := rfl

variable [LawfulMonad m]

@[simp]
lemma mapM_bind {α β : Type uB} (x : FreeM P α) (f : α → FreeM P β) :
    (FreeM.bind x f).mapM s = x.mapM s >>= fun u => (f u).mapM s := by
  induction x using FreeM.inductionOn with
  | pure _ => simp
  | roll a cont h => simp [h]

@[simp]
lemma mapM_bind' {α β : Type uB} (x : FreeM P α) (f : α → FreeM P β) :
    (x >>= f).mapM s = x.mapM s >>= fun u => (f u).mapM s :=
  mapM_bind _ _ _

@[simp]
lemma mapM_map {α β : Type uB} (x : FreeM P α) (f : α → β) :
    FreeM.mapM s (f <$> x) = f <$> FreeM.mapM s x := by
  simp [← bind_pure_comp]

@[simp]
lemma mapM_seq {α β : Type uB}
    (s : (a : P.A) → m (P.B a)) (x : FreeM P (α → β)) (y : FreeM P α) :
    FreeM.mapM s (x <*> y) = (FreeM.mapM s x) <*> (FreeM.mapM s y) := by
  simp [seq_eq_bind_map]

@[simp]
lemma mapM_lift (s : (a : P.A) → m (P.B a)) (x : P.Obj α) :
    FreeM.mapM s (FreeM.lift x) = s x.1 >>= (fun u ↦ (pure (x.2 u)).mapM s) := by
  simp [FreeM.mapM]

@[simp]
lemma mapM_liftA (s : (a : P.A) → m (P.B a)) (a : P.A) :
    FreeM.mapM s (FreeM.liftA a) = s a := by simp [liftA]

end mapM

end FreeM

end PFunctor
