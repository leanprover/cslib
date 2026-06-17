/-
Copyright (c) 2026 Mateo Petel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mateo Petel
-/

module

public import Cslib.Init

/-!
# Lawful lenses

Minimal lens API for verified access and update of record-shaped state.

## Main definitions

- `Lens` / `LawfulLens`: getter, setter, and the standard `get_set`, `set_get`, `set_set` laws
- `Lens.over`: update the focused component with a function
- `Lens.comp` (`∘ₗ`): compose nested field access

## Main results

- `Lens.comp_lawful`: composition of lawful lenses is lawful
-/

@[expose] public section

namespace Cslib

universe u

/-- A lens focuses on a component `A` inside a whole state `S`. -/
structure Lens (S A : Type u) where
  /-- Read the focused component. -/
  get : S → A
  /-- Replace the focused component, leaving the rest of `S` unchanged. -/
  set : S → A → S

/-- A `LawfulLens` bundles the standard lens laws stated in `get`/`set` vocabulary. -/
structure LawfulLens (S A : Type u) extends Lens S A where
  /-- `get (set s a) = a` -/
  get_set : ∀ s a, get (set s a) = a
  /-- `set s (get s) = s` -/
  set_get : ∀ s, set s (get s) = s
  /-- `set (set s a) b = set s b` -/
  set_set : ∀ s a b, set (set s a) b = set s b

namespace Lens

/-- Update the focused component with a function. -/
def over (l : Lens S A) (f : A → A) : S → S :=
  fun s => l.set s (f (l.get s))

/-- Compose nested lenses: outer `l₁` then inner `l₂`. -/
def comp (l₁ : Lens S A) (l₂ : Lens A B) : Lens S B :=
  ⟨l₂.get ∘ l₁.get, fun s b => l₁.set s (l₂.set (l₁.get s) b)⟩

infixl:80 " ∘ₗ " => comp

instance : Coe (LawfulLens S A) (Lens S A) := ⟨LawfulLens.toLens⟩

/-- Build a lawful lens from getter, setter, and law proofs. -/
def mkLawful (get : S → A) (set : S → A → S)
    (get_set : ∀ s a, get (set s a) = a)
    (set_get : ∀ s, set s (get s) = s)
    (set_set : ∀ s a b, set (set s a) b = set s b) : LawfulLens S A :=
  { get, set, get_set, set_get, set_set }

@[simp] theorem lawful_get_set (l : LawfulLens S A) (s : S) (a : A) :
    l.get (l.set s a) = a :=
  l.get_set s a

@[simp] theorem lawful_set_get (l : LawfulLens S A) (s : S) :
    l.set s (l.get s) = s :=
  l.set_get s

@[simp] theorem lawful_set_set (l : LawfulLens S A) (s : S) (a b : A) :
    l.set (l.set s a) b = l.set s b :=
  l.set_set s a b

/-- Composition preserves lawfulness. -/
theorem comp_lawful (l₁ : LawfulLens S A) (l₂ : LawfulLens A B) :
    LawfulLens (comp l₁ l₂) where
  get_set := by
    intro s b
    dsimp [comp]
    rw [l₁.get_set, l₂.get_set]
  set_get := by
    intro s
    dsimp [comp]
    rw [l₂.set_get, l₁.set_get]
  set_set := by
    intro s a b
    dsimp [comp]
    rw [l₁.get_set, l₂.set_set, l₁.set_set]

end Lens

end Cslib
