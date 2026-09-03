/-
Copyright (c) 2026 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi
-/

module

public import Cslib.Logics.Modal.Semantics
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
def Proposition.Equiv (m : Model World τ Atom) (φ₁ φ₂ : Proposition τ Atom) : Prop :=
  ∀ (w : World), ⇓Modal[m,w ⊨ φ₁ ↔ φ₂]

instance : Congruence (Proposition.Equiv m) := ⟨⟩

@[scoped grind =]
theorem Proposition.equiv_def (m : Model World τ Atom) (φ₁ φ₂ : Proposition τ Atom) :
    (φ₁.Equiv m φ₂) ↔ φ₁ ≡[Equiv m] φ₂ := by rfl

@[scoped grind ⇒]
theorem Proposition.equiv_iff_forall_der (m : Model World τ Atom) (φ₁ φ₂ : Proposition τ Atom)
    : (φ₁ ≡[Equiv m] φ₂) ↔ ∀ (w : World), ⇓Modal[m,w ⊨ φ₁ ↔ φ₂] := by rfl

@[scoped grind ⇒]
theorem Proposition.equiv_iff_forall_iff {m : Model World τ Atom} {φ₁ φ₂ : Proposition τ Atom} :
    (φ₁ ≡[Equiv m] φ₂) ↔ ∀ (w : World), ⇓Modal[m,w ⊨ φ₁] ↔ ⇓Modal[m,w ⊨ φ₂] := by
  grind [=_ Satisfies.iff_iff_iff]

/-- A class of models, defined as a set. -/
abbrev ModelClass (World : Type*) (τ : PFunctor) (Atom : Type*) := Set (Model World τ Atom)

/-- The modal propositions `φ₁` and `φ₂` are equivalent in the model class `S`. -/
def Proposition.EquivWithin (S : ModelClass World τ Atom) (φ₁ φ₂ : Proposition τ Atom) :=
  ∀ m ∈ S, φ₁ ≡[Equiv m] φ₂

instance : Congruence (Proposition.EquivWithin S) := ⟨⟩

@[scoped grind =]
theorem Proposition.equivWithin_def (S : ModelClass World τ Atom) (φ₁ φ₂ : Proposition τ Atom) :
    φ₁.EquivWithin S φ₂ ↔ (φ₁ ≡[EquivWithin S] φ₂) := by rfl

@[scoped grind ⇒]
theorem Proposition.equiv_of_EquivWithin {S : ModelClass World τ Atom} (h : φ₁ ≡[EquivWithin S] φ₂)
    (m : Model World τ Atom) (hm : m ∈ S) : φ₁ ≡[Equiv m] φ₂ := h m hm

/-- Logical equivalence preserves validity. -/
theorem Proposition.equivWithin_valid (S : ModelClass World τ Atom)
    (φ₁ φ₂ : Proposition τ Atom) (h : φ₁ ≡[EquivWithin S] φ₂) :
    (φ₁.valid S ↔ φ₂.valid S) := by
  grind

/-- A proposition map missing a particular case (index). -/
abbrev PropositionMap.Without (τ : PFunctor) (Atom : Type*) (op : τ.A) (i : τ.B op) :=
  {j : τ.B op // j ≠ i} → Proposition τ Atom

/-- Propositional contexts. -/
inductive Proposition.Context (τ : PFunctor) (Atom : Type u) : Type u where
  | hole
  | not (c : Context τ Atom)
  | andL (c : Context τ Atom) (φ : Proposition τ Atom)
  | andR (φ : Proposition τ Atom) (c : Context τ Atom)
  | triangle (op : τ.A) (i : τ.B op) (c : Context τ Atom)
    (φs : PropositionMap.Without τ Atom op i)

/-- Replaces a hole in a propositional context with a proposition. -/
@[scoped grind =]
def Proposition.Context.fill {τ : PFunctor} [τ.DecidableEqChildren] {Atom : Type*}
    (c : Context τ Atom) (φ : Proposition τ Atom) :=
  match c with
  | hole => φ
  | not c => .not (c.fill φ)
  | andL c φ' => (c.fill φ).and φ'
  | andR φ' c => φ'.and (c.fill φ)
  | .triangle op i c φs => .triangle op fun j =>
    if h : j = i then
      c.fill φ
    else
      φs ⟨j, h⟩

instance {τ : PFunctor} [τ.DecidableEqChildren] {Atom : Type*} :
    HasContext (Proposition τ Atom) := ⟨Proposition.Context.fill⟩

@[scoped grind =]
lemma Proposition.Context.fill_def {τ : PFunctor} [τ.DecidableEqChildren] {Atom : Type*}
    {c : HasContext.Context (Proposition τ Atom)} {φ : Proposition τ Atom} :
  c.fill φ = c<[φ] := rfl

open scoped Proposition Proposition.Context

/-- Logical equivalence is an equivalence relation. -/
instance (m : Model World τ Atom) : IsEquiv (Proposition τ Atom) (Proposition.Equiv m) := by
  rw [← equivalence_iff_isEquiv]
  constructor
  case refl => grind [Proposition.Equiv]
  case symm =>
    grind
  case trans =>
    grind

/-- Logical equivalence within a class is an equivalence relation. -/
instance {World Atom} (S : ModelClass World τ Atom) :
    IsEquiv (Proposition τ Atom) (Proposition.EquivWithin S) := by
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
instance {τ : PFunctor} [τ.DecidableEqChildren] {Atom : Type*} (m : Model World τ Atom) :
    LawfulCongruence (Proposition.Equiv m) where
  elim ctx φ₁ φ₂ heqv w := by
    induction ctx generalizing w
    case hole => apply heqv
    case not c ih | andL c ih | andR c ih =>
      specialize ih w
      grind [=_ Proposition.Context.fill_def]
    case triangle op i c φs ih =>
      rw [Satisfies.iff_iff_iff]
      constructor
      all_goals
        intro h
        obtain ⟨ws, hr, hs⟩ := h
        refine ⟨ws, hr, ?_⟩
        intro j
        by_cases j = i
        · subst j
          specialize ih (ws i)
          grind
        · grind

/-- Logical equivalence within a class is a congruence. -/
instance {τ : PFunctor} [τ.DecidableEqChildren] {Atom : Type*}
    (S : ModelClass World τ Atom) : LawfulCongruence (Proposition.EquivWithin S) where
  elim ctx _ _ h m hm :=
    LawfulCongruence.covariant.elim ctx (h m hm)

/-- Judgemental contexts. -/
structure Satisfies.Context (World : Type*) (τ : PFunctor) (Atom : Type*) where
  /-- The model to consider. -/
  m : Model World τ Atom
  /-- The world to check propositions against. -/
  w : World

/-- Fills a judgemental context with a proposition. -/
def Satisfies.Context.fill (c : Satisfies.Context World τ Atom) (φ : Proposition τ Atom) :
    Judgement World τ Atom := Modal[c.m, c.w ⊨ φ]

instance {World : Type*} {τ : PFunctor} {Atom : Type*} :
    HasHContext (Judgement World τ Atom) (Proposition τ Atom) := ⟨Satisfies.Context.fill⟩

@[scoped grind =]
lemma Satisfies.Context.fill_def {c : Satisfies.Context World τ Atom} :
    Modal[c.m,c.w ⊨ φ] = c<[φ] := rfl

open scoped Satisfies.Context

/-- Logical equivalence for Modal Logic K. That is, no assumptions on models are made. -/
instance {τ : PFunctor} [τ.DecidableEqChildren] : LogicalEquivalence
    (α := Proposition τ Atom)
    (Judgement := Judgement World τ Atom) InferenceSystem.Default
    (Proposition.EquivWithin (Set.univ (α := Model World τ Atom))) where
  eqvFillValid heqv c h := by
    specialize heqv c.m
    grind [=_ Satisfies.Context.fill_def]

/-- Correspondence of equivalence and axiom validity. -/
theorem Proposition.axiom_iff_forall_equiv (f : Frame World τ) (φ₁ φ₂ : Proposition τ Atom) :
    (Axiom f⇓(φ₁ ↔ φ₂)) ↔ ∀ v, φ₁ ≡[Equiv ⟨f, v⟩] φ₂ := Iff.rfl

end Cslib.Logic.Modal
