/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Quang Dao
-/

module

public import Cslib.Foundations.Data.PFunctor.Free

/-!
# Folding polynomial free monads

`PFunctor.FreeM.foldFreeM` evaluates a free polynomial tree in an algebra given by handlers
for values and operations. It satisfies the same universal property and substitution laws
as `Cslib.FreeM.foldFreeM`.
-/

@[expose] public section

universe v uA uB

namespace PFunctor.FreeM

variable {P : PFunctor.{uA, uB}} {α β γ : Type*}

/-- Fold a free polynomial tree into an algebra of its signature. -/
def foldFreeM (onValue : α → β) (onEffect : (a : P.A) → (P.B a → β) → β) : P.FreeM α → β
  | .pure a => onValue a
  | .liftBind a cont => onEffect a fun b => foldFreeM onValue onEffect (cont b)

@[simp]
theorem foldFreeM_pure (onValue : α → β) (onEffect : (a : P.A) → (P.B a → β) → β) (a : α) :
    foldFreeM onValue onEffect (pure a) = onValue a := rfl

@[simp]
theorem foldFreeM_lift_bind (onValue : α → β) (onEffect : (a : P.A) → (P.B a → β) → β)
    (a : P.A) (cont : P.B a → P.FreeM α) :
    foldFreeM onValue onEffect ((lift a).bind (α := no_index (P.B a)) cont) =
      onEffect a (fun b => foldFreeM onValue onEffect (cont b)) := rfl

-- `no_index` lets simp find these equations for concrete response types such as `Fin n`.
@[simp]
theorem foldFreeM_lift_bind' {α : Type uB} (onValue : α → β)
    (onEffect : (a : P.A) → (P.B a → β) → β) (a : P.A) (cont : P.B a → P.FreeM α) :
    foldFreeM onValue onEffect (Bind.bind (α := no_index (P.B a)) (lift a) cont) =
      onEffect a (fun b => foldFreeM onValue onEffect (cont b)) := rfl

@[simp]
theorem foldFreeM_lift (a : P.A) (onValue : P.B a → β)
    (onEffect : (a : P.A) → (P.B a → β) → β) :
    foldFreeM (α := no_index (P.B a)) onValue onEffect (lift a) = onEffect a onValue := rfl

/-- A function agreeing with the algebra on values and operations is the fold. -/
theorem foldFreeM_unique (onValue : α → β) (onEffect : (a : P.A) → (P.B a → β) → β)
    (h : P.FreeM α → β) (h_pure : ∀ a, h (pure a) = onValue a)
    (h_lift_bind : ∀ (a : P.A) (cont : P.B a → P.FreeM α),
      h ((lift a).bind cont) = onEffect a (fun b => h (cont b))) :
    h = foldFreeM onValue onEffect := by
  funext x
  induction x with
  | pure a => exact h_pure a
  | lift_bind a cont ih =>
    exact (h_lift_bind a cont).trans (congrArg (onEffect a) (funext ih))

/-- Sequencing substitutes the fold of the continuation for the value handler. -/
theorem foldFreeM_bind (onValue : β → γ) (onEffect : (a : P.A) → (P.B a → γ) → γ)
    (x : P.FreeM α) (k : α → P.FreeM β) :
    foldFreeM onValue onEffect (x.bind k) =
      foldFreeM (fun a => foldFreeM onValue onEffect (k a)) onEffect x := by
  induction x with
  | pure a => rfl
  | lift_bind a cont ih => exact congrArg (onEffect a) (funext ih)

theorem foldFreeM_map (onValue : β → γ) (onEffect : (a : P.A) → (P.B a → γ) → γ)
    (f : α → β) (x : P.FreeM α) :
    foldFreeM onValue onEffect (map f x) = foldFreeM (onValue ∘ f) onEffect x := by
  rw [← bind_pure_comp, foldFreeM_bind]
  rfl

/-- Monadic interpretation is the fold whose effect handler uses `bind`. -/
theorem liftM_eq_foldFreeM {m : Type uB → Type v} [Monad m] {α : Type uB}
    (interp : (a : P.A) → m (P.B a)) :
    FreeM.liftM interp (α := α) = foldFreeM pure (fun a k => interp a >>= k) :=
  foldFreeM_unique _ _ _ (liftM_pure interp) (fun _ _ => rfl)

end PFunctor.FreeM
