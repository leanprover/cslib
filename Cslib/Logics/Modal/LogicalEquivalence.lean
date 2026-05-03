/-
Copyright (c) 2026 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi
-/

module

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

theorem Proposition.equiv_valid (S : Set (Model World Atom))
    (φ₁ φ₂ : Proposition Atom) (h : φ₁ ≡[S] φ₂) :
    (φ₁.valid S ↔ φ₂.valid S) := by
  apply Iff.intro <;> intro h'
  · simp_all only [valid]
    intro m hin w
    specialize h m hin w
    grind
  · simp_all only [valid]
    intro m hin w
    specialize h m hin w
    grind

/-- Propositional contexts. -/
inductive Proposition.Context (Atom : Type u) : Type u where
  | hole
  | not (c : Context Atom)
  | andL (c : Context Atom) (φ : Proposition Atom)
  | andR (φ : Proposition Atom) (c : Context Atom)
  | diamond (c : Context Atom)

/-- Replaces a hole in a propositional context with a proposition. -/
@[scoped grind =]
def Proposition.Context.fill (c : Context Atom) (φ : Proposition Atom) :=
  match c with
  | hole => φ
  | not c => .not (c.fill φ)
  | andL c φ' => (c.fill φ).and φ'
  | andR φ' c => φ'.and (c.fill φ)
  | diamond c => .diamond (c.fill φ)

instance : HasContext (Proposition Atom) := ⟨Proposition.Context Atom, Proposition.Context.fill⟩

open scoped Proposition Proposition.Context

/-- Logical equivalence is an equivalence relation. -/
instance (S : Set (Model World Atom)) :
    IsEquiv (Proposition Atom) (Proposition.Equiv (Atom := Atom) S) where
  refl := by grind
  symm := by
    intro φ₁ φ₂ h m hₘ w
    specialize h m hₘ w
    grind
  trans := by
    intro φ₁ φ₂ φ₃ h₁ h₂ m hₘ w
    specialize h₁ m hₘ w
    specialize h₂ m hₘ w
    grind

/-- Logical equivalence is a congruence. -/
instance (S : Set (Model World Atom)) :
    Congruence (Proposition Atom) (Proposition.Equiv (Atom := Atom) S) where
  elim :
      Covariant (Proposition.Context Atom) (Proposition Atom) (Proposition.Context.fill)
      (Proposition.Equiv S) := by
    intro ctx φ₁ φ₂ heqv m hₘ w
    specialize heqv m hₘ
    induction ctx generalizing w
    case hole => grind
    case not c ih | andL c ih | andR c ih =>
      specialize ih w
      grind
    case diamond c ih =>
      simp only [Satisfies.iff_iff_iff]
      apply Iff.intro
      all_goals
        intro h
        rcases h with ⟨w', h⟩
        specialize ih w'
        grind

/-- Judgemental contexts. -/
structure Satisfies.Context (World Atom : Type*) where
  /-- The model to consider. -/
  m : Model World Atom
  /-- The world to check propositions against. -/
  w : World

/-- Fills a judgemental context with a proposition. -/
def Satisfies.Context.fill (c : Satisfies.Context World Atom) (φ : Proposition Atom) :
    Judgement World Atom where
  m := c.m
  w := c.w
  φ := φ

instance judgementalContext :
    HasHContext (Judgement World Atom) (Proposition Atom) :=
  ⟨Satisfies.Context World Atom, Satisfies.Context.fill⟩

/-- Logical equivalence for Modal Logic K. That is, no assumptions on models are made. -/
instance : LogicalEquivalence
    (Proposition Atom) (Judgement World Atom) Satisfies.Bundled where
  eqv := Proposition.Equiv Set.univ
  eqv_fill_valid {φ₁ φ₂ : Proposition Atom} (heqv : φ₁ ≡[Set.univ] φ₂)
      (c : HasHContext.Context (Judgement World Atom) (Proposition Atom))
      (h : ⇓c<[φ₁]) : ⇓c<[φ₂] := by
    simp only [HasHContext.fill, Satisfies.Context.fill] at ⊢ h
    specialize heqv c.m
    grind

end Cslib.Logic.Modal
