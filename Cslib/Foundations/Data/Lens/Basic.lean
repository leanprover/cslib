/-
Copyright (c) 2026 Mateo Petel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mateo Petel
-/

module

public import Cslib.Init

/-! # Lawful lenses

Minimal lens API for verified access and update of record-shaped state.
-/

namespace Cslib

universe u

/-- A lens focuses on a component `A` inside a whole state `S`. -/
structure Lens (S A : Type u) where
  /-- Read the focused component. -/
  get : S → A
  /-- Replace the focused component, leaving the rest of `S` unchanged. -/
  set : S → A → S

/--
A `LawfulLens` bundles the standard lens laws stated in `get`/`set` vocabulary.
-/
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

instance : Coe (LawfulLens S A) (Lens S A) := ⟨fun l => l.toLens⟩

end Lens

end Cslib
