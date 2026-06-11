/-
Copyright (c) 2026 Fabrizio Montesi, Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi, Benjamin Brast-McKie
-/

module

import Cslib.Init
public import Cslib.Logics.Modal.Basic
public import Cslib.Foundations.Logic.LogicalEquivalence

/-! # Logical Equivalence in Modal Logic

This module defines logical equivalence for modal propositions.
The definitions are parametric on the class of models under consideration.

We also instantiate `LogicalEquivalence` for Modal Logic K, i.e., equivalence
for the class of all models.
-/

@[expose] public section

namespace Cslib.Logic.Modal

open scoped InferenceSystem Proposition Satisfies

/-- The modal propositions `φ₁` and `φ₂` are equivalent in the class of models `S`. -/
def Proposition.Equiv (S : Set (Model World Atom)) (φ₁ φ₂ : Proposition Atom)
    : Prop :=
  ∀ m ∈ S, ∀ w : World, ⇓Modal[m,w ⊨ φ₁ ↔ φ₂]

@[inherit_doc]
scoped notation φ₁ " ≡[" S "] " φ₂ => Proposition.Equiv S φ₁ φ₂

@[inherit_doc]
scoped notation φ₁ " ≡ " φ₂ => Proposition.Equiv Set.univ φ₁ φ₂

@[scoped grind =]
theorem Proposition.equiv_def (S : Set (Model World Atom)) (φ₁ φ₂ : Proposition Atom) :
    (φ₁ ≡[S] φ₂) ↔
    (∀ m ∈ S, ∀ w : World, ⇓Modal[m,w ⊨ φ₁ ↔ φ₂]) := by rfl

@[scoped grind =]
theorem Proposition.equiv_iff (S : Set (Model World Atom)) (φ₁ φ₂ : Proposition Atom) :
    (φ₁ ≡[S] φ₂) ↔
    (∀ m ∈ S, ∀ w : World, ⇓Modal[m,w ⊨ φ₁] ↔ ⇓Modal[m,w ⊨ φ₂]) := by
  simp [Proposition.equiv_def, Satisfies.iff_iff_iff]

theorem Proposition.equiv_valid (S : Set (Model World Atom))
    (φ₁ φ₂ : Proposition Atom) (h : φ₁ ≡[S] φ₂) :
    (φ₁.valid S ↔ φ₂.valid S) := by
  grind

/-- A one-hole context for `Proposition`. Each constructor corresponds to a recursive position
in `Proposition`: `impL` is the left argument of `imp`, `impR` is the right argument, and `box`
is the argument of `box`. The `hole` constructor marks the position to be filled. -/
inductive Proposition.Context (Atom : Type u) : Type u where
  /-- The position to substitute. -/
  | hole
  /-- Context in the left argument of `imp`. -/
  | impL (c : Context Atom) (φ : Proposition Atom)
  /-- Context in the right argument of `imp`. -/
  | impR (φ : Proposition Atom) (c : Context Atom)
  /-- Context under `box`. -/
  | box (c : Context Atom)

/-- Fill the hole in a context with a proposition. -/
def Proposition.Context.fill : Proposition.Context Atom → Proposition Atom → Proposition Atom
  | .hole, φ => φ
  | .impL c ψ, φ => c.fill φ → ψ
  | .impR ψ c, φ => ψ → c.fill φ
  | .box c, φ => □(c.fill φ)

instance : HasContext (Proposition Atom) := ⟨Proposition.Context Atom, Proposition.Context.fill⟩

@[scoped grind =_]
lemma Proposition.Context.fill_def {Γ : HasContext.Context (Proposition Atom)} :
    Γ.fill φ = Γ<[φ] := rfl

open scoped Proposition.Context

/-- Logical equivalence is an equivalence relation. -/
instance {World Atom} (S : Set (Model World Atom)) :
    IsEquiv (Proposition Atom) (Proposition.Equiv S) := by
  rw [← equivalence_iff_isEquiv]
  grind [Equivalence]

/-- Logical equivalence is a congruence. -/
instance {World Atom} (S : Set (Model World Atom)) :
    Congruence (Proposition Atom) (Proposition.Equiv S) where
  elim ctx φ₁ φ₂ heqv m hₘ w := by
    induction ctx generalizing w
    case hole => grind
    case impL c _ ih =>
      simp only [Proposition.Context.fill, Satisfies.iff_iff_iff]
      constructor
      · intro hf ha; exact hf ((ih w).mpr ha)
      · intro hf ha; exact hf ((ih w).mp ha)
    case impR _ c ih =>
      simp only [Proposition.Context.fill, Satisfies.iff_iff_iff]
      constructor
      · intro hf ha; exact (ih w).mp (hf ha)
      · intro hf ha; exact (ih w).mpr (hf ha)
    case box c ih =>
      simp only [Proposition.Context.fill, Satisfies.iff_iff_iff]
      constructor
      · intro hf w' hr; exact (ih w').mp (hf w' hr)
      · intro hf w' hr; exact (ih w').mpr (hf w' hr)

/-- Judgemental contexts. -/
structure Satisfies.Context (World Atom : Type*) where
  /-- The model to consider. -/
  m : Model World Atom
  /-- The world to check propositions against. -/
  w : World

/-- Fills a judgemental context with a proposition. -/
def Satisfies.Context.fill (c : Satisfies.Context World Atom) (φ : Proposition Atom) :
    Judgement World Atom := Modal[c.m, c.w ⊨ φ]

instance judgementalContext :
    HasHContext (Judgement World Atom) (Proposition Atom) :=
  ⟨Satisfies.Context World Atom, Satisfies.Context.fill⟩

@[scoped grind =_]
lemma Satisfies.Context.fill_def {c : Satisfies.Context World Atom} :
    Modal[c.m,c.w ⊨ φ] = c<[φ] := rfl

open scoped Satisfies.Context

/-- Logical equivalence for Modal Logic K. That is, no assumptions on models are made. -/
instance : LogicalEquivalence
    (Proposition Atom) (Judgement World Atom) Satisfies.Bundled where
  eqv := Proposition.Equiv Set.univ
  eqvFillValid heqv c h := by
    specialize heqv c.m
    grind

end Cslib.Logic.Modal
