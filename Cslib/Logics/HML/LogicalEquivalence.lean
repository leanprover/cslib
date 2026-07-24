/-
Copyright (c) 2026 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi
-/

module

public import Cslib.Logics.HML.Basic
public import Cslib.Foundations.Logic.LogicalEquivalence

/-! # Logical Equivalence in HML

This module defines logical equivalence for HML propositions and instantiates `LogicalEquivalence`.
-/

@[expose] public section

namespace Cslib.Logic.HML

open scoped InferenceSystem

/-- The HML propositions `φ₁` and `φ₂` are logically equivalent under the LTS `lts`. -/
def Proposition.Equiv (lts : LTS State Label) (φ₁ φ₂ : Proposition Label) : Prop :=
  ∀ (s : State), ⇓HML[lts,s ⊨ φ₁ ↔ φ₂]

@[scoped grind =]
theorem Proposition.equiv_def (lts : LTS State Label) (φ₁ φ₂ : Proposition Label) :
    (φ₁.Equiv lts φ₂) ↔
    ∀ (s : State), ⇓HML[lts,s ⊨ φ₁ ↔ φ₂] := by rfl

@[scoped grind =]
theorem Proposition.equiv_iff (lts : LTS State Label) (φ₁ φ₂ : Proposition Label) :
    (φ₁.Equiv lts φ₂) ↔
    (∀ (s : State), ⇓HML[lts,s ⊨ φ₁] ↔ ⇓HML[lts,s ⊨ φ₂]) := by
  simp [Proposition.equiv_def, Satisfies.iff_iff_iff]

/-- Propositional contexts. -/
inductive Proposition.Context (Label : Type u) : Type u where
  | hole
  | andL (c : Context Label) (φ : Proposition Label)
  | andR (φ : Proposition Label) (c : Context Label)
  | not (c : Context Label)
  | diamond (μ : Label) (c : Context Label)

/-- Replaces a hole in a propositional context with a proposition. -/
@[scoped grind =]
def Proposition.Context.fill (c : Context Label) (φ : Proposition Label) :=
  match c with
  | hole => φ
  | andL c φ' => (c.fill φ).and φ'
  | andR φ' c => φ'.and (c.fill φ)
  | not c => .not (c.fill φ)
  | diamond μ c => .diamond μ (c.fill φ)

instance : HasContext (Proposition Label) := ⟨Proposition.Context.fill⟩

open scoped Proposition Proposition.Context Satisfies

/-- Logical equivalence is an equivalence relation. -/
instance (lts : LTS State Label) : IsEquiv (Proposition Label) (Proposition.Equiv lts) := by
  rw [← equivalence_iff_isEquiv]
  grind [Equivalence]

instance : Congruence (Proposition.Equiv lts) := ⟨⟩

/-- Logical equivalence is a lawful congruence. -/
instance (lts : LTS State Label) :
    LawfulCongruence (Proposition.Equiv lts) where
  elim :
      Covariant (Proposition.Context Label) (Proposition Label) (Proposition.Context.fill)
      (Proposition.Equiv lts) := by
    intro ctx
    induction ctx <;> grind

instance (lts : LTS State Label) : LogicalEquivalence (Judgement := Judgement State Label) InferenceSystem.Default (Proposition.Equiv lts) where
  eqv := Proposition.EquivUniv
  eqvFillValid heqv c h := by
    specialize heqv c.lts c.state
    simp only [HasHContext.fill, Satisfies.Context.fill] at ⊢ h
    grind

/-- Judgemental contexts. -/
structure Satisfies.Context State Label where
  /-- The labelled transition system to consider. -/
  lts : LTS State Label
  /-- The state to check propositions against. -/
  state : State

/-- Fills a judgemental context with a proposition. -/
def Satisfies.Context.fill (c : Satisfies.Context State Label) (φ : Proposition Label) :
    Judgement State Label where
  lts := c.lts
  state := c.state
  φ := φ

instance : HasHContext (Judgement State Label) (Proposition Label) :=
  ⟨Satisfies.Context.fill⟩

/-- Universal logical equivalence: logical equivalence under all LTSs. -/
abbrev Proposition.EquivUniv (φ₁ φ₂ : Proposition Label) : Prop :=
  ∀ {State : Type*} (lts : LTS State Label), φ₁.Equiv lts φ₂

/-- Universal logical equivalence is an equivalence relation. -/
instance : IsEquiv (Proposition Label) Proposition.EquivUniv := by
  rw [← equivalence_iff_isEquiv]
  constructor
  · grind
  · intro φ₁ φ₂ h State lts
    grind [h lts]
  · intro φ₁ φ₂ φ₃ h₁ h₂ State lts
    grind [h₁ lts, h₂ lts]

@[default_congruence]
instance : Congruence (α := Proposition Label) Proposition.EquivUniv := ⟨⟩

/-- Universal logical equivalence is a lawful congruence. -/
instance : LawfulCongruence (α := Proposition Label) Proposition.EquivUniv where
  elim :
      Covariant (Proposition.Context Label) (Proposition Label) Proposition.Context.fill
      Proposition.EquivUniv := by
    intro ctx φ₁ φ₂ h State lts
    induction ctx <;> grind

instance : HasLogicalEquivalence (Proposition Label) Proposition.EquivUniv where
  eqv := Proposition.EquivUniv
  eqvFillValid heqv c h := by
    specialize heqv c.lts c.state
    simp only [HasHContext.fill, Satisfies.Context.fill] at ⊢ h
    grind

theorem Proposition.false_and_false_eqv_false : (⊥ ∧ ⊥ : Proposition Label).EquivUniv ⊥ := by
  grind

theorem Proposition.false_and_false_eqv_false' : LogicalEquivalence.eqv InferenceSystem.Default (Judgement State Label) (⊥ ∧ ⊥ : Proposition Label) (⊥ : Proposition Label) := by
  grind

scoped notation a " ≡?[" J "] " b => LogicalEquivalence.eqv InferenceSystem.Default J a b

theorem Proposition.false_and_false_eqv_false'' : (⊥ ∧ ⊥ : Proposition Label) ≡?[(Judgement State Label)] (⊥ : Proposition Label) := by
  intro State
  grind

end Cslib.Logic.HML
