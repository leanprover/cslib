/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

import Cslib.Foundations.Control.Monad.Free.Fold
import Cslib.Foundations.Data.PFunctor.Free.Fold
import Cslib.Foundations.Data.PFunctor.Free.W

/-! Tests for polynomial free monads across independent universes and ordinary module imports. -/

universe uA uB u v w

namespace CslibTests.PFunctorFree

open PFunctor

variable {P : PFunctor.{uA, uB}} {α : Type u} {β : Type v} {γ : Type w}

example (f : α → β) (a : α) : FreeM.map f (pure a : P.FreeM α) = pure (f a) := by
  simp

example (f : β → γ) (x : P.FreeM α) (cont : α → P.FreeM β) :
    FreeM.map f (x.bind cont) = x.bind fun a => (cont a).map f := by
  simp

-- When the universes agree, simplification continues to use the usual monad API.
example (f : α → α) (x : P.FreeM α) (cont : α → P.FreeM α) :
    f <$> (x >>= cont) = x >>= fun a => f <$> cont a := by
  simp

-- Folding and mapping preserve independent shape, child, result, and algebra universes.
example (onValue : β → γ) (onEffect : (a : P.A) → (P.B a → γ) → γ)
    (a : P.A) (cont : P.B a → P.FreeM α) (f : α → β) :
    FreeM.foldFreeM onValue onEffect (FreeM.map f ((FreeM.lift a).bind cont)) =
      onEffect a (fun b => FreeM.foldFreeM (onValue ∘ f) onEffect (cont b)) := by
  rw [FreeM.foldFreeM_map]
  simp

-- The dependent result type must not prevent simp from finding the lift equation.
example (n : Nat) (onValue : Fin n → Nat) (onEffect : (n : Nat) → (Fin n → Nat) → Nat) :
    FreeM.foldFreeM onValue onEffect (FreeM.lift (P := ⟨Nat, Fin⟩) n) =
      onEffect n onValue := by
  simp

example (n : Nat) (onEffect : (n : Nat) → (Fin n → Nat) → Nat) :
    FreeM.foldFreeM ULift.down onEffect
        ((FreeM.lift (P := ⟨Nat, Fin⟩) n).bind (fun b => pure (ULift.up b.val : ULift.{1} Nat))) =
      onEffect n Fin.val := by
  rw [FreeM.foldFreeM_bind, FreeM.foldFreeM_lift]
  rfl

example (n : Nat) (cont : Fin n → (⟨Nat, Fin⟩ : PFunctor).FreeM Nat)
    (onEffect : (n : Nat) → (Fin n → Nat) → Nat) :
    FreeM.foldFreeM id onEffect (FreeM.lift (P := ⟨Nat, Fin⟩) n >>= cont) =
      onEffect n (fun b => FreeM.foldFreeM id onEffect (cont b)) := by
  simp

example (n : Nat) (cont : Fin n → (⟨Nat, Fin⟩ : PFunctor).FreeM (ULift.{1} Nat))
    (onEffect : (n : Nat) → (Fin n → Nat) → Nat) :
    FreeM.foldFreeM ULift.down onEffect ((FreeM.lift (P := ⟨Nat, Fin⟩) n).bind cont) =
      onEffect n (fun b => FreeM.foldFreeM ULift.down onEffect (cont b)) := by
  simp

-- Both free monads expose the same connection between handler composition and folding.
example {Q : PFunctor.{u, uB}} {m : Type uB → Type v} [Monad m] [LawfulMonad m]
    {δ : Type uB} (x : P.FreeM δ)
    (first : (a : P.A) → Q.FreeM (P.B a)) (second : (a : Q.A) → m (Q.B a)) :
    (x.liftM first).liftM second =
      FreeM.foldFreeM pure (fun a k => (first a).liftM second >>= k) x := by
  rw [FreeM.liftM_comp, FreeM.liftM_eq_foldFreeM]

example {F : Type u → Type v} {G : Type u → Type w}
    {m : Type u → Type uA} [Monad m] [LawfulMonad m] {δ : Type u} (x : Cslib.FreeM F δ)
    (first : {ι : Type u} → F ι → Cslib.FreeM G ι) (second : {ι : Type u} → G ι → m ι) :
    (x.liftM first).liftM second =
      Cslib.FreeM.foldFreeM pure (fun op k => (first op).liftM second >>= k) x := by
  rw [Cslib.FreeM.liftM_comp, Cslib.FreeM.liftM_eq_foldFreeM]

-- A nullary operation makes these W-type checks nonvacuous.
private abbrev arity : PFunctor := ⟨Nat, Fin⟩

private def leaf : arity.W := W.mk (.mk 0 Fin.elim0)

example (n : Nat) (cont : Fin n → arity.FreeM PEmpty) :
    FreeM.toWOfIsEmpty (FreeM.lift (P := arity) n >>= cont) =
      W.mk (.mk n fun b => FreeM.toWOfIsEmpty (cont b)) := by
  simp

example : FreeM.toWOfIsEmpty (W.toFreeM (α := PEmpty.{u + 1}) leaf) = leaf := by simp

example (x : arity.FreeM PEmpty) :
    W.toFreeM (FreeM.equivWOfIsEmpty x) = x := by
  simp

-- Embedding a W-type does not require the result type to be empty.
example : W.toFreeM (α := Nat) leaf = (FreeM.lift (P := arity) 0).bind (fun b => Fin.elim0 b) := by
  rw [leaf, W.toFreeM_mk]
  congr 1
  funext b
  exact Fin.elim0 b

end CslibTests.PFunctorFree
