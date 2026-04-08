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

## Comparison with `Cslib.FreeM`

`Cslib.FreeM F` (in `Cslib.Foundations.Control.Monad.Free`) builds a free monad over an
arbitrary type constructor `F : Type u → Type v`, using a single `liftBind` constructor that
existentially quantifies the intermediate type:
```
| liftBind {ι : Type u} (op : F ι) (cont : ι → FreeM F α) : FreeM F α
```
Here the intermediate type `ι` is hidden, so `F` need not be a `Functor`.

`PFunctor.FreeM P` instead takes a polynomial functor `P : PFunctor`, where the shapes
`P.A` and children `P.B a` are given explicitly.
Its `liftBind` constructor carries the shape and continuation without existential quantification:
```
| liftBind (a : P.A) (cont : P.B a → FreeM P α) : FreeM P α
```

When the effect signature is naturally polynomial (a fixed set of operations, each with a
known return type), `PFunctor.FreeM` gives stronger eliminators and avoids the universe
bump that the existential in `Cslib.FreeM` introduces.

This construction is ported from the [VCV-io](https://github.com/dtumad/VCV-io) library.

## Main Definitions

- `PFunctor.FreeM`: The free monad on a polynomial functor.
- `PFunctor.FreeM.lift`: Lift an object of the base polynomial functor into the free monad.
- `PFunctor.FreeM.liftA`: Lift a position of the base polynomial functor into the free monad.
- `PFunctor.FreeM.liftM`: Interpret `FreeM P` into any other monad.
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
theorem pure_eq_pure : (FreeM.pure : α → FreeM P α) = pure := rfl

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
lemma bind_pure : ∀ x : FreeM P α, x.bind pure = x
  | .pure a => rfl
  | .liftBind a cont => by
    simp only [FreeM.bind]; congr 1; funext u; exact bind_pure (cont u)

@[simp]
lemma bind_pure_comp (f : α → β) : ∀ x : FreeM P α, x.bind (pure ∘ f) = map f x
  | .pure a => rfl
  | .liftBind a cont => by simp only [FreeM.bind, map, bind_pure_comp]

@[simp]
lemma liftBind_bind (a : P.A) (cont : P.B a → FreeM P β) (f : β → FreeM P γ) :
    (FreeM.liftBind a cont).bind f = FreeM.liftBind a (fun u ↦ (cont u).bind f) := rfl

@[simp]
lemma lift_bind (x : P.Obj α) (f : α → FreeM P β) :
    (FreeM.lift x).bind f = FreeM.liftBind x.1 (fun a ↦ f (x.2 a)) := rfl

@[simp] lemma bind_eq_pure_iff (x : FreeM P α) (f : α → FreeM P β) (b : β) :
    x.bind f = pure b ↔ ∃ a, x = pure a ∧ f a = pure b := by
  cases x with
  | pure a => exact ⟨fun h => ⟨a, rfl, h⟩, fun ⟨_, h, hf⟩ => by rwa [FreeM.pure.inj h]⟩
  | liftBind a cont => simp [FreeM.bind]

@[simp] lemma pure_eq_bind_iff (x : FreeM P α) (f : α → FreeM P β) (b : β) :
    pure b = x.bind f ↔ ∃ a, x = pure a ∧ pure b = f a := by
  cases x with
  | pure a => exact ⟨fun h => ⟨a, rfl, h⟩, fun ⟨_, h, hf⟩ => by rwa [FreeM.pure.inj h]⟩
  | liftBind a cont => simp [FreeM.bind]

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

lemma pure_inj (a b : α) : (pure a : FreeM P α) = pure b ↔ a = b := by
  constructor
  · exact FreeM.pure.inj
  · rintro rfl; rfl

@[simp] lemma liftBind_inj (a a' : P.A)
    (cont : P.B a → P.FreeM α) (cont' : P.B a' → P.FreeM α) :
    FreeM.liftBind a cont = FreeM.liftBind a' cont' ↔ ∃ h : a = a', h ▸ cont = cont' := by
  simp
  by_cases ha : a = a'
  · cases ha
    simp
  · simp [ha]

section liftM

variable {m : Type uB → Type v} {α : Type uB}

/-- Interpret a `FreeM P` computation into any monad `m` by providing an interpretation
`interp : (a : P.A) → m (P.B a)` for each operation. -/
protected def liftM [Pure m] [Bind m] (interp : (a : P.A) → m (P.B a)) : FreeM P α → m α
  | .pure a => Pure.pure a
  | .liftBind a cont => (interp a) >>= (fun u ↦ (cont u).liftM interp)

variable [Monad m] (interp : (a : P.A) → m (P.B a))

@[simp]
lemma liftM_pure' (a : α) : (FreeM.pure a : FreeM P α).liftM interp = Pure.pure a := rfl

@[simp]
lemma liftM_liftBind (a : P.A) (cont : P.B a → FreeM P α) :
    (FreeM.liftBind a cont).liftM interp = interp a >>= fun u => (cont u).liftM interp := rfl

@[simp]
lemma liftM_pure (a : α) : (Pure.pure a : FreeM P α).liftM interp = Pure.pure a := rfl

variable [LawfulMonad m]

@[simp]
lemma liftM_bind {α β : Type uB} (x : FreeM P α) (f : α → FreeM P β) :
    (x.bind f).liftM interp = x.liftM interp >>= fun u => (f u).liftM interp := by
  induction x with
  | pure _ => simp [FreeM.bind, FreeM.liftM]
  | liftBind a cont h => simp [h]

@[simp]
lemma liftM_bind' {α β : Type uB} (x : FreeM P α) (f : α → FreeM P β) :
    (x >>= f).liftM interp = x.liftM interp >>= fun u => (f u).liftM interp :=
  liftM_bind _ _ _

@[simp]
lemma liftM_map {α β : Type uB} (x : FreeM P α) (f : α → β) :
    FreeM.liftM interp (map f x) = f <$> FreeM.liftM interp x := by
  induction x with
  | pure _ => simp [map, FreeM.liftM]
  | liftBind a cont h => simp [h]

@[simp]
lemma liftM_seq {α β : Type uB}
    (interp : (a : P.A) → m (P.B a)) (x : FreeM P (α → β)) (y : FreeM P α) :
    FreeM.liftM interp (x <*> y) = (FreeM.liftM interp x) <*> (FreeM.liftM interp y) := by
  simp only [seq_eq_bind_map, liftM_bind', map_eq_map, liftM_map]

@[simp]
lemma liftM_seqLeft {α β : Type uB}
    (interp : (a : P.A) → m (P.B a)) (x : FreeM P α) (y : FreeM P β) :
    FreeM.liftM interp (x <* y) = FreeM.liftM interp x <* FreeM.liftM interp y := by
  simp only [seqLeft_eq_bind, liftM_bind', liftM_pure]

@[simp]
lemma liftM_seqRight {α β : Type uB}
    (interp : (a : P.A) → m (P.B a)) (x : FreeM P α) (y : FreeM P β) :
    FreeM.liftM interp (x *> y) = FreeM.liftM interp x *> FreeM.liftM interp y := by
  simp only [seqRight_eq_bind, liftM_bind']

@[simp]
lemma liftM_lift (interp : (a : P.A) → m (P.B a)) (x : P.Obj α) :
    FreeM.liftM interp (FreeM.lift x) = x.2 <$> interp x.1 := by
  simp [lift]

@[simp]
lemma liftM_liftA (interp : (a : P.A) → m (P.B a)) (a : P.A) :
    FreeM.liftM interp (FreeM.liftA a) = interp a := by simp [liftA]

end liftM

end FreeM

end PFunctor
