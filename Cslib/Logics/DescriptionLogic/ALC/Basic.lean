/-
Copyright (c) 2026 Alexandre Rademaker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexandre Rademaker, Guilherme Lima
-/

module

public import Cslib.Logics.Modal.Denotation
public import Cslib.Logics.Modal.Unary.Basic

/-! # The Description Logic ALC

ALC is a notational variant of the multimodal logic `K_m` [Schild1991]: role names are unary
modal operators, concept names are atoms, `∀R.C` is `d[R]C` and `∃R.C` is `d⟨R⟩C`. We therefore
define ALC concepts as modal propositions over the signature `mkUnary Role`, and an interpretation
as the corresponding Kripke structure. Instance checking is modal satisfaction, written
`ALC[I,x ⊨ C]`, so that the correspondence of [Schild1991, Theorem 1] holds by construction.

## Main definitions

- `Concept`: ALC concepts.
- `Interpretation`: DL interpretations `(Δ, ·ᴵ)`, and `Interpretation.toModal`, the corresponding
  Kripke structure.
- `ALC[I,x ⊨ C]`: the individual `x` is an instance of `C` in `I`.
- `TAxiom`, `TBox`: concept inclusions `C ⊑ D` and concept equalities `C ≡ D`. A concept equality
  holds in `I` iff `C` and `D` are logically equivalent (`Proposition.Equiv`) in `I.toModal`.
- `Entails`: global consequence of a terminological axiom from a TBox.
- `Assertion`, `ABox`: concept and role assertions about named individuals.

## References

* [K. Schild, *A Correspondence Theory for Terminological Logics: Preliminary
  Report*][Schild1991]
* [F. Baader et al. (eds.), *The Description Logic Handbook*, 2nd ed.][Baader2007]
-/

@[expose] public section

namespace Cslib.Logic.DL

open PFunctor Modal
open scoped InferenceSystem Modal.Proposition Satisfies Frame

/-- ALC concepts are multimodal propositions whose operators are role names and whose atoms are
concept names. -/
abbrev Concept (Role ConceptName : Type*) := Modal.Proposition (mkUnary Role) ConceptName

/-- A DL interpretation over the domain `Δ`. -/
structure Interpretation (Δ Role ConceptName : Type*) where
  /-- Extension of concept names. -/
  conc : ConceptName → Set Δ
  /-- Extension of role names. -/
  role : Role → Δ → Δ → Prop

/-- The Kripke structure corresponding to an interpretation. -/
def Interpretation.toModal (I : Interpretation Δ Role ConceptName) :
    Modal.Model Δ (mkUnary Role) ConceptName :=
  ⟨Frame.ofRelations I.role, fun x A => x ∈ I.conc A⟩

/-- `ALC[I,x ⊨ C]`: the individual `x` is an instance of the concept `C` in `I`. -/
scoped notation "ALC[" I "," x " ⊨ " C "]" => Modal[Interpretation.toModal I, x ⊨ C]

variable {I : Interpretation Δ Role ConceptName} {C D : Concept Role ConceptName}

@[simp]
theorem Interpretation.toModal_v {A : ConceptName} : I.toModal.v x A ↔ x ∈ I.conc A := .rfl

@[scoped grind =, modal =]
theorem Satisfies.alc_atom_iff {A : ConceptName} :
    ⇓ALC[I,x ⊨ (.atom A : Concept Role ConceptName)] ↔ x ∈ I.conc A := by rfl

/-- Existential restriction `∃R.C`. -/
@[scoped grind =, modal =]
theorem Satisfies.alc_exists_iff {R : Role} :
    ⇓ALC[I,x ⊨ d⟨R⟩C] ↔ ∃ y, I.role R x y ∧ ⇓ALC[I,y ⊨ C] := by
  rw [Satisfies.dynDiamond_iff_exists]
  simp [Interpretation.toModal, Frame.diagonal, Frame.ofRelations]

/-- Value restriction `∀R.C`. -/
@[scoped grind =, modal =]
theorem Satisfies.alc_forall_iff {R : Role} :
    ⇓ALC[I,x ⊨ d[R]C] ↔ ∀ y, I.role R x y → ⇓ALC[I,y ⊨ C] := by
  rw [Satisfies.dynBox_iff_forall]
  simp [Interpretation.toModal, Frame.diagonal, Frame.ofRelations]

/-- The extension `Cᴵ` of a concept, given by its modal denotation. -/
abbrev Concept.ext (I : Interpretation Δ Role ConceptName) (C : Concept Role ConceptName) :
    Set Δ :=
  C.denotation I.toModal

/-- The set-based reading of instance checking. -/
theorem Concept.mem_ext_iff : x ∈ Concept.ext I C ↔ ⇓ALC[I,x ⊨ C] :=
  satisfies_mem_denotation

/-- Terminological axioms. -/
inductive TAxiom (Role ConceptName : Type*) where
  /-- Concept inclusion `C ⊑ D`. -/
  | incl (C D : Concept Role ConceptName)
  /-- Concept equality `C ≡ D`. -/
  | equiv (C D : Concept Role ConceptName)

open scoped Congruence in
/-- An interpretation satisfies a terminological axiom. -/
def Interpretation.Sat (I : Interpretation Δ Role ConceptName) :
    TAxiom Role ConceptName → Prop
  | .incl C D => ∀ x, ⇓ALC[I,x ⊨ C → D]
  | .equiv C D => C ≡[Proposition.Equiv I.toModal] D

/-- A TBox is a set of terminological axioms. -/
abbrev TBox (Role ConceptName : Type*) := Set (TAxiom Role ConceptName)

/-- An interpretation is a model of a TBox if it satisfies all of its axioms. -/
def Interpretation.IsModel (I : Interpretation Δ Role ConceptName)
    (T : TBox Role ConceptName) : Prop :=
  ∀ ax ∈ T, I.Sat ax

/-- Global consequence: every model of `T` over the domain `Δ` satisfies `ax`. -/
def Entails (Δ : Type*) (T : TBox Role ConceptName) (ax : TAxiom Role ConceptName) : Prop :=
  ∀ I : Interpretation Δ Role ConceptName, I.IsModel T → I.Sat ax

/-- Subsumption with respect to the empty TBox is validity of `C → D` in `K_m`. -/
theorem entails_empty_iff :
    Entails Δ (∅ : TBox Role ConceptName) (.incl C D) ↔
      ∀ I : Interpretation Δ Role ConceptName, ∀ x, ⇓ALC[I,x ⊨ C → D] := by
  simp [Entails, Interpretation.IsModel, Interpretation.Sat]

/-- Assertions about named individuals. -/
inductive Assertion (Role ConceptName Individual : Type*) where
  /-- Concept assertion `C(a)`. -/
  | concept (C : Concept Role ConceptName) (a : Individual)
  /-- Role assertion `R(a, b)`. -/
  | role (R : Role) (a b : Individual)

/-- An ABox is a set of assertions. -/
abbrev ABox (Role ConceptName Individual : Type*) := Set (Assertion Role ConceptName Individual)

/-- An interpretation, together with an interpretation `ι` of individuals, satisfies an
assertion. -/
def Interpretation.SatAssertion (I : Interpretation Δ Role ConceptName) (ι : Individual → Δ) :
    Assertion Role ConceptName Individual → Prop
  | .concept C a => ⇓ALC[I,ι a ⊨ C]
  | .role R a b => I.role R (ι a) (ι b)

end Cslib.Logic.DL
