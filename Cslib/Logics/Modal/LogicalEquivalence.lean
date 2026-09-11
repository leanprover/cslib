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

/-- The modal propositions `φ₁` and `φ₂` are equivalent in the model `m`. -/
def Proposition.Equiv (m : Model World Atom) (φ₁ φ₂ : Proposition Atom) : Prop :=
  ∀ (w : World), ⇓Modal[m,w ⊨ φ₁ ↔ φ₂]

instance : Congruence (Proposition.Equiv m) := ⟨⟩

@[scoped grind =]
theorem Proposition.equiv_def (m : Model World Atom) (φ₁ φ₂ : Proposition Atom) :
    (φ₁.Equiv m φ₂) ↔ φ₁ ≡[Equiv m] φ₂ := by rfl

@[scoped grind ⇒]
theorem Proposition.equiv_iff_forall_der (m : Model World Atom) (φ₁ φ₂ : Proposition Atom)
    : (φ₁ ≡[Equiv m] φ₂) ↔ ∀ (w : World), ⇓Modal[m,w ⊨ φ₁ ↔ φ₂] := by rfl

@[scoped grind ⇒]
theorem Proposition.equiv_iff_forall_iff {m : Model World Atom} {φ₁ φ₂ : Proposition Atom} :
    (φ₁ ≡[Equiv m] φ₂) ↔ ∀ (w : World), ⇓Modal[m,w ⊨ φ₁] ↔ ⇓Modal[m,w ⊨ φ₂] := by
  grind [=_ Satisfies.iff_iff_iff]

/-- A class of models, defined as a set. -/
abbrev ModelClass World Atom := Set (Model World Atom)

/-- The modal propositions `φ₁` and `φ₂` are equivalent in the model class `S`. -/
def Proposition.EquivWithin (S : ModelClass World Atom) (φ₁ φ₂ : Proposition Atom) :=
  ∀ m ∈ S, φ₁ ≡[Equiv m] φ₂

instance : Congruence (Proposition.EquivWithin S) := ⟨⟩

@[scoped grind =]
theorem Proposition.equivWithin_def (S : ModelClass World Atom) (φ₁ φ₂ : Proposition Atom) :
    φ₁.EquivWithin S φ₂ ↔ (φ₁ ≡[EquivWithin S] φ₂) := by rfl

@[scoped grind ⇒]
theorem Proposition.equiv_of_EquivWithin {S : ModelClass World Atom} (h : φ₁ ≡[EquivWithin S] φ₂)
    (m : Model World Atom) (hm : m ∈ S) : φ₁ ≡[Equiv m] φ₂ := h m hm

/-- Logical equivalence preserves validity. -/
theorem Proposition.equivWithin_valid (S : ModelClass World Atom)
    (φ₁ φ₂ : Proposition Atom) (h : φ₁ ≡[EquivWithin S] φ₂) :
    (φ₁.valid S ↔ φ₂.valid S) := by
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

instance : HasContext (Proposition Atom) := ⟨Proposition.Context.fill⟩

@[scoped grind =]
lemma Proposition.Context.fill_def {c : HasContext.Context (Proposition Atom)} :
    c.fill φ = c<[φ] := rfl

open scoped Proposition Proposition.Context

/-- Logical equivalence is an equivalence relation. -/
instance (m : Model World Atom) : IsEquiv (Proposition Atom) (Proposition.Equiv m) := by
  rw [← equivalence_iff_isEquiv]
  constructor
  case refl => grind [Proposition.Equiv]
  case symm =>
    grind
  case trans =>
    grind

/-- Logical equivalence within a class is an equivalence relation. -/
instance {World Atom} (S : ModelClass World Atom) :
    IsEquiv (Proposition Atom) (Proposition.EquivWithin S) := by
  rw [← equivalence_iff_isEquiv]
  unfold Proposition.EquivWithin
  constructor
  case refl =>
    grind [Proposition.Equiv]
  case symm =>
    grind
  case trans =>
    grind

/-- Logical equivalence is a congruence. -/
instance (m : Model World Atom) : LawfulCongruence (Proposition.Equiv m) where
  elim ctx φ₁ φ₂ heqv w := by
    induction ctx generalizing w
    case hole => apply heqv
    case not c ih | andL c ih | andR c ih =>
      specialize ih w
      grind [=_ Proposition.Context.fill_def]
    case diamond c ih =>
      rw [Satisfies.iff_iff_iff]
      apply Iff.intro
      all_goals
        rintro ⟨w', h⟩
        specialize ih w'
        grind [=_ Proposition.Context.fill_def]

/-- Logical equivalence within a class is a congruence. -/
instance (S : ModelClass World Atom) :
    LawfulCongruence (Proposition.EquivWithin S) where
  elim ctx _ _ h m hm :=
    LawfulCongruence.covariant.elim ctx (h m hm)

/-- Judgemental contexts. -/
structure Satisfies.Context (World Atom : Type*) where
  /-- The model to consider. -/
  m : Model World Atom
  /-- The world to check propositions against. -/
  w : World

/-- Fills a judgemental context with a proposition. -/
def Satisfies.Context.fill (c : Satisfies.Context World Atom) (φ : Proposition Atom) :
    Judgement World Atom := Modal[c.m, c.w ⊨ φ]

instance : HasHContext (Judgement World Atom) (Proposition Atom) := ⟨Satisfies.Context.fill⟩

@[scoped grind =]
lemma Satisfies.Context.fill_def {c : Satisfies.Context World Atom} :
    Modal[c.m,c.w ⊨ φ] = c<[φ] := rfl

open scoped Satisfies.Context

/-- Logical equivalence for Modal Logic K. That is, no assumptions on models are made. -/
instance : LogicalEquivalence
    (α := Proposition Atom)
    (Judgement := Judgement World Atom) InferenceSystem.Default
    (Proposition.EquivWithin (Set.univ (α := Model World Atom))) where
  eqvFillValid heqv c h := by
    specialize heqv c.m
    grind [=_ Satisfies.Context.fill_def]

/-- Correspondence of equivalence and axiom validity. -/
theorem Proposition.axiom_iff_forall_equiv (r : α → α → Prop) (φ₁ φ₂ : Proposition Atom) :
    (Axiom r⇓(φ₁ ↔ φ₂)) ↔ ∀ v, φ₁ ≡[Equiv ⟨r, v⟩] φ₂ := Iff.rfl

open Relation in
/-- In a transitive diamond model, possibility distributes over conjunction for propositions
whose satisfaction is preserved along accessibility. -/
@[scoped grind ⇒]
theorem Proposition.diamond_and_equiv_of_preserves {m : Model World Atom} [IsTrans World m.r]
    {φ₁ φ₂ : Proposition Atom} (hd : Diamond m.r) (h₁ : Preserves m.r (⇓Modal[m,· ⊨ φ₁]))
    (h₂ : Preserves m.r (⇓Modal[m,· ⊨ φ₂])) :
    ◇(φ₁ ∧ φ₂) ≡[Equiv m] (◇φ₁ ∧ ◇φ₂) := by
  rw [equiv_iff_forall_iff]
  intro a
  constructor
  case mp => grind
  case mpr =>
    rintro ⟨⟨b, hab, hb⟩, ⟨c, hac, hc⟩⟩
    rcases hd hab hac with ⟨d, hbd, hcd⟩
    use d, IsTrans.trans _ _ _ hab hbd
    exact ⟨h₁ hbd hb, h₂ hcd hc⟩

/-- In a reflexive and transitive model, diamond absorbs itself (idempotency). -/
theorem Proposition.diamond_diamond_equiv {m : Model World Atom} [Std.Refl m.r] [IsTrans World m.r]
    (φ : Proposition Atom) : ◇◇φ ≡[Equiv m] ◇φ := by
  rw [equiv_iff_forall_iff]
  intro w
  constructor <;> rw [← Satisfies.imp_iff_imp]
  · grind [Satisfies.four]
  · grind [Satisfies.t]

end Cslib.Logic.Modal
