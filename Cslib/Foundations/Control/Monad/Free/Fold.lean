/-
Copyright (c) 2025 Tanner Duve. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tanner Duve
-/

module

public import Cslib.Foundations.Control.Monad.Free

@[expose] public section

/-!
# Free Monad Catamorphism

This file defines the fold operation for free monads and proves its universal property.

In computer science terms, `foldFreeM` provides **interpreters** for effectful syntax trees.
Given any "target algebra" (a type with handlers for values and effects), `foldFreeM`
constructs the unique interpreter that transforms `FreeM` programs into that target.

The theory is based on the fact that `FreeM F α` is the initial algebra for a specific functor, and
`foldFreeM` provides the unique way to eliminate free monad computations into any
algebra of this functor.

## Main Definitions

- `FreeM.foldFreeM`: Fold operation for free monads
- `FreeM.foldFreeM_unique`: Universal property showing uniqueness of the fold

## Universal Property

`FreeM F α` is the initial algebra of the functor `φ_F(β) = α ⊕ Σ_ι (F ι × (ι → β))`.

An algebra of this functor consists of a type `β` and functions:
- `onValue : α → β` (handles pure values)
- `onEffect : {ι : Type u} → F ι → (ι → β) → β` (handles effects with continuations)

For any such algebra, `foldFreeM onValue onEffect` is the unique algebra morphism
from the initial algebra `FreeM F α` to `(β, onValue, onEffect)`.
-/

namespace Cslib

universe u v w w'

namespace FreeM
variable {F : Type u → Type v} {ι : Type u} {α : Type w} {β : Type w'}

/-- Fold function for the `FreeM` monad -/
def foldFreeM
    (onValue : α → β)
    (onEffect : {ι : Type u} → F ι → (ι → β) → β) :
    FreeM F α → β
  | .pure a => onValue a
  | .liftBind op k => onEffect op (fun x => foldFreeM onValue onEffect (k x))

@[simp]
theorem foldFreeM_pure
    (onValue : α → β)
    (onEffect : {ι : Type u} → F ι → (ι → β) → β)
    (a : α) : foldFreeM onValue onEffect (pure a) = onValue a := rfl

@[simp]
theorem foldFreeM_lift_bind
    (onValue : α → β)
    (onEffect : {ι : Type u} → F ι → (ι → β) → β)
    (op : F ι) (k : ι → FreeM F α) :
      foldFreeM onValue onEffect ((lift op).bind k)
      = onEffect op (fun x => foldFreeM onValue onEffect (k x)) := rfl

/--
**Universal Property**: If `h : FreeM F α → β` satisfies:
* `h (pure a) = onValue a`
* `h ((lift op).bind k) = onEffect op (fun x => h (k x))`

then `h` is equal to `foldFreeM onValue onEffect`.
-/
theorem foldFreeM_unique
    (onValue : α → β)
    (onEffect : {ι : Type u} → F ι → (ι → β) → β)
    (h : FreeM F α → β)
    (h_pure : ∀ a, h (pure a) = onValue a)
    (h_liftBind : ∀ {ι} (op : F ι) (k : ι → FreeM F α),
      h ((lift op).bind k) = onEffect op (fun x => h (k x))) :
    h = foldFreeM onValue onEffect := by
  funext x
  induction x with
  | pure a =>
    rw [foldFreeM_pure, h_pure]
  | lift_bind op k ih =>
    rw [foldFreeM_lift_bind, h_liftBind]
    grind

end FreeM

end Cslib
