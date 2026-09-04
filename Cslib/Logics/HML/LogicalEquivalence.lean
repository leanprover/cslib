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

open scoped InferenceSystem Satisfies

section Theory

/-! ## Theory of logical equivalence -/

/-- The HML propositions `φ₁` and `φ₂` are logically equivalent under the LTS `lts`. -/
def Proposition.Equiv (lts : LTS State Label) (φ₁ φ₂ : Proposition Label) : Prop :=
  ∀ (s : State), ⇓HML[lts,s ⊨ φ₁ ↔ φ₂]

instance : Congruence (Proposition.Equiv lts) := ⟨⟩

@[scoped grind =]
theorem Proposition.equiv_def (lts : LTS State Label) (φ₁ φ₂ : Proposition Label) :
    (φ₁.Equiv lts φ₂) ↔ φ₁ ≡[Equiv lts] φ₂ := by rfl

@[scoped grind ⇒]
theorem Proposition.equiv_forall_der (lts : LTS State Label) (φ₁ φ₂ : Proposition Label)
    (h : φ₁ ≡[Equiv lts] φ₂) : ∀ (s : State), ⇓HML[lts,s ⊨ φ₁ ↔ φ₂] := by
  intro s
  specialize h s
  assumption

theorem Proposition.forall_der_equiv (lts : LTS State Label) (φ₁ φ₂ : Proposition Label)
    (h : ∀ (s : State), ⇓HML[lts,s ⊨ φ₁ ↔ φ₂]) :
    φ₁ ≡[Equiv lts] φ₂ := by
  intro s
  specialize h s
  assumption

@[scoped grind ⇒]
theorem Proposition.equiv_iff {lts : LTS State Label} {φ₁ φ₂ : Proposition Label}
    (h : φ₁ ≡[Equiv lts] φ₂) (s : State) :
    ⇓HML[lts,s ⊨ φ₁] ↔ ⇓HML[lts,s ⊨ φ₂] := by
  grind [=_ Satisfies.iff_iff_iff]

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

@[scoped grind =]
lemma Proposition.Context.fill_def {c : HasContext.Context (Proposition Atom)} :
    c.fill φ = c<[φ] := rfl

open scoped Proposition Proposition.Context

/-- Logical equivalence is an equivalence relation. -/
instance : IsEquiv (Proposition Label) (Proposition.Equiv lts) := by
  rw [← equivalence_iff_isEquiv]
  grind [Equivalence, Proposition.Equiv]

/-- Logical equivalence is a lawful congruence. -/
instance (lts : LTS State Label) :
    LawfulCongruence (Proposition.Equiv lts) where
  elim ctx φ₁ φ₂ heqv := by
    induction ctx
    case hole =>
      grind [=_ Proposition.Context.fill_def]
    case not c ih | andL c ih | andR c ih =>
      intro s
      grind [=_ Proposition.Context.fill_def]
    case diamond c ih =>
      intro s
      rw [Satisfies.iff_iff_iff]
      apply Iff.intro
      · grind [=_ Proposition.Context.fill_def]
      · rintro ⟨w', h⟩
        specialize ih w'
        grind [=_ Proposition.Context.fill_def]

/-- Judgemental contexts. -/
structure Judgement.Context State Label where
  /-- The labelled transition system to consider. -/
  lts : LTS State Label
  /-- The state to check propositions against. -/
  state : State

/-- Fills a judgemental context with a proposition. -/
def Judgement.Context.fill (c : Judgement.Context State Label) (φ : Proposition Label) :
    Judgement State Label where
  lts := c.lts
  state := c.state
  φ := φ

instance : HasHContext (Judgement State Label) (Proposition Label) :=
  ⟨Judgement.Context.fill⟩

@[scoped grind =]
lemma Judgement.Context.fill_def {c : Judgement.Context World Atom} {φ : Proposition Atom} :
    HML[c.lts,c.state ⊨ φ] = c<[φ] := rfl

/-- Universal logical equivalence: logical equivalence under all LTSs. -/
def Proposition.UEquiv.{u, v} {Label : Type v} (φ₁ φ₂ : Proposition Label) : Prop :=
  ∀ ⦃State : Type u⦄ (lts : LTS State Label), φ₁ ≡[Equiv lts] φ₂

instance : DefaultCongruence (Proposition Label) (Proposition.UEquiv (Label := Label)) := ⟨⟩

@[scoped grind =]
theorem Proposition.uEquiv_def.{u, v} : UEquiv.{u, v} φ₁ φ₂ ↔ φ₁ ≡[UEquiv.{u, v}] φ₂ := by
  simp [Congruence.r]

@[scoped grind =]
theorem Proposition.uEquiv_iff_forall_equiv.{u, v} {Label : Type v} (φ₁ φ₂ : Proposition Label) :
    (φ₁ ≡[UEquiv.{u, v}] φ₂) ↔ ∀ {State : Type u} (lts : LTS State Label), φ₁ ≡[Equiv lts] φ₂ := by
  rfl

/-- Universal logical equivalence is an equivalence relation. -/
instance : IsEquiv (Proposition Label) Proposition.UEquiv := by
  rw [← equivalence_iff_isEquiv]
  constructor
  · intro φ State lts s
    grind
  · intro φ₁ φ₂ h State lts s
    grind [h lts]
  · intro φ₁ φ₂ φ₃ h₁ h₂ State lts
    grind [h₁ lts, h₂ lts, Proposition.forall_der_equiv lts]

/-- Universal logical equivalence is a lawful congruence. -/
instance {Label} : LawfulCongruence (Proposition.UEquiv (Label := Label)) where
  elim :
      Covariant (Proposition.Context Label) (Proposition Label) Proposition.Context.fill
      Proposition.UEquiv := by
    intro ctx φ₁ φ₂ h State lts
    induction ctx <;> grind [h lts, Proposition.forall_der_equiv lts]

instance : LogicalEquivalence (Judgement := Judgement State Label) InferenceSystem.Default
    (Proposition.UEquiv (Label := Label)) where
  eqvFillValid heqv c h := by
    specialize heqv c.lts c.state
    grind [=_ Judgement.Context.fill_def, HasHContext.fill, Judgement.Context.fill]

end Theory

section Equivalences

/-! ## Database of logical equivalences -/

namespace Proposition

theorem false_and_false_eqv_false :
    (⊥ ∧ ⊥ : Proposition Label) ≡ (⊥ : Proposition Label) := by
  intro State lts
  have := forall_der_equiv lts
  grind

/-- The dual axiom (reformulated for HML from modal logic). -/
theorem dual (μ : Label) (φ : Proposition Label) :
    (d⟨μ⟩φ) ≡ (¬d[μ]¬φ) := by
  intro State lts s
  grind

end Proposition

end Equivalences

end Cslib.Logic.HML
