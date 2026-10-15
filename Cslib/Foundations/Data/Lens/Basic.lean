/-
Copyright (c) 2026 Mateo Petel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mateo Petel
-/

module

public import Cslib.Init

/-!
# Lawful lenses

A small lens API for verified access and update of structured state.

## Main definitions

- `Lens`: a getter and setter focusing on a component of a larger state.
- `LawfulLens`: a lens satisfying the standard get-set, set-get, and set-set laws.
- `Lens.over`: update the focused component with a function.
- `Lens.comp`: compose nested lenses.

## Main results

- `Lens.compLawful`: composition of lawful lenses is lawful.
-/

@[expose] public section

namespace Cslib

universe u v w

/-- A lens focuses on a component `A` inside a state `S`. -/
structure Lens (S : Type u) (A : Type v) where
  /-- Read the focused component. -/
  get : S → A
  /-- Replace the focused component. -/
  set : S → A → S

/-- A lens bundled with the standard get-set, set-get, and set-set laws. -/
structure LawfulLens (S : Type u) (A : Type v) extends Lens S A where
  /-- Reading immediately after writing returns the written value. -/
  get_set : ∀ s a, get (set s a) = a
  /-- Writing the value already present leaves the state unchanged. -/
  set_get : ∀ s, set s (get s) = s
  /-- Consecutive writes to the same focus retain only the final value. -/
  set_set : ∀ s a b, set (set s a) b = set s b

attribute [simp] LawfulLens.get_set LawfulLens.set_get LawfulLens.set_set

namespace Lens

variable {S : Type u} {A : Type v} {B : Type w}

/-- Update the focused component with a function. -/
def over (l : Lens S A) (f : A → A) (s : S) : S :=
  l.set s (f (l.get s))

/-- Compose nested lenses: first focus from `S` to `A`, then from `A` to `B`. -/
def comp (l₁ : Lens S A) (l₂ : Lens A B) : Lens S B :=
  ⟨l₂.get ∘ l₁.get, fun s b => l₁.set s (l₂.set (l₁.get s) b)⟩

@[simp]
theorem comp_get (l₁ : Lens S A) (l₂ : Lens A B) (s : S) :
    (comp l₁ l₂).get s = l₂.get (l₁.get s) := rfl

@[simp]
theorem comp_set (l₁ : Lens S A) (l₂ : Lens A B) (s : S) (b : B) :
    (comp l₁ l₂).set s b = l₁.set s (l₂.set (l₁.get s) b) := rfl

instance : Coe (LawfulLens S A) (Lens S A) := ⟨LawfulLens.toLens⟩

/-- Composition of lawful lenses is lawful. -/
def compLawful (l₁ : LawfulLens S A) (l₂ : LawfulLens A B) : LawfulLens S B where
  get := l₂.get ∘ l₁.get
  set := fun s b => l₁.set s (l₂.set (l₁.get s) b)
  get_set := by
    intro s b
    simp
  set_get := by
    intro s
    simp
  set_set := by
    intro s a b
    simp

end Lens

end Cslib
