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
- `Interpretation`: DL interpretations `(Δ, ·ᴵ)` over a nonempty domain `Δ`, and
  `Interpretation.toModal`, the corresponding Kripke structure.
- `ALC[I,x ⊨ C]`: the individual `x` is an instance of `C` in `I`.
- `∃ R . C`, `∀ R . C`: notations for the restrictions `d⟨R⟩C` and `d[R]C`.
- `TAxiom`, `TBox`: concept inclusions `C ⊑ D` and concept equalities `C ≡ D`. A concept equality
  holds in `I` iff `C` and `D` are logically equivalent (`Proposition.Equiv`) in `I.toModal`.
- `Entails`: global consequence of a terminological axiom from a TBox.
- `Consistent`: a TBox is consistent if it has a model.
- `Assertion`, `ABox`: concept and role assertions about named individuals.

## References

* [K. Schild, *A Correspondence Theory for Terminological Logics: Preliminary
  Report*][Schild1991]
* [F. Baader et al. (eds.), *The Description Logic Handbook*, 2nd ed.][Baader2007]
* [F. Baader, I. Horrocks, C. Lutz, U. Sattler, *An Introduction to Description Logic*][Baader2017]
-/

@[expose] public section

namespace Cslib.Logic.DL

open PFunctor Modal
open scoped InferenceSystem Modal.Proposition Satisfies Frame

/-- ALC concepts are multimodal propositions whose operators are role names and whose atoms are
concept names. -/
abbrev Concept (Role ConceptName : Type*) := Modal.Proposition (mkUnary Role) ConceptName

/-- A DL interpretation. The domain `Δᴵ` is the type `Δ` itself rather than a subset of some
universe, so `⊤ᴵ = Set.univ` (`Interpretation.interpret_top`); it is required to be nonempty.
Concept names are interpreted as subsets of `Δ` and role names as binary relations on `Δ`. -/
structure Interpretation (Δ Role ConceptName : Type*) where
  /-- Extension of concept names. -/
  conc : ConceptName → Set Δ
  /-- Extension of role names. -/
  role : Role → Δ → Δ → Prop
  /-- The domain is nonempty. -/
  nonempty : Nonempty Δ := by infer_instance

/-- The Kripke structure corresponding to an interpretation. -/
def Interpretation.toModal (I : Interpretation Δ Role ConceptName) :
    Modal.Model Δ (mkUnary Role) ConceptName :=
  ⟨Frame.ofRelations I.role, fun x A => x ∈ I.conc A⟩

/-- `ALC[I,x ⊨ C]`: the individual `x` is an instance of the concept `C` in `I`. -/
scoped notation "ALC[" I "," x " ⊨ " C "]" => Modal[Interpretation.toModal I, x ⊨ C]

/-- Existential restriction `∃R.C`, i.e. `d⟨R⟩C`. A space is needed before the dot, since
`R.C` would be read as a single dotted identifier. -/
scoped notation:max "∃" R:max "." C:max => HasDynamicDiamond.dynDiamond R C

/-- Value restriction `∀R.C`, i.e. `d[R]C`. A space is needed before the dot, since `R.C` would
be read as a single dotted identifier. -/
scoped notation:max "∀" R:max "." C:max => HasDynamicBox.dynBox R C

variable {I : Interpretation Δ Role ConceptName} {C D : Concept Role ConceptName}

@[simp]
theorem Interpretation.toModal_v_iff_conc {A : ConceptName} :
    I.toModal.v x A ↔ x ∈ I.conc A := .rfl

@[scoped grind =, modal =]
theorem Satisfies.alc_atom_iff_conc {A : ConceptName} :
    ⇓ALC[I,x ⊨ (.atom A : Concept Role ConceptName)] ↔ x ∈ I.conc A := by rfl

/-- Existential restriction `∃R.C`. -/
@[scoped grind =, modal =]
theorem Satisfies.alc_exists_iff {R : Role} :
    ⇓ALC[I,x ⊨ ∃ R . C] ↔ ∃ y, I.role R x y ∧ ⇓ALC[I,y ⊨ C] := by
  rw [Satisfies.dynDiamond_iff_exists]
  simp [Interpretation.toModal, Frame.diagonal, Frame.ofRelations]

/-- Value restriction `∀R.C`. -/
@[scoped grind =, modal =]
theorem Satisfies.alc_forall_iff {R : Role} :
    ⇓ALC[I,x ⊨ ∀ R . C] ↔ ∀ y, I.role R x y → ⇓ALC[I,y ⊨ C] := by
  rw [Satisfies.dynBox_iff_forall]
  simp [Interpretation.toModal, Frame.diagonal, Frame.ofRelations]

/-- The interpretation `Cᴵ` of a concept under `I`, given by its modal denotation. In the DL
literature, `Cᴵ` is also called the *extension* of `C` [Baader2017, Chapter 2]. -/
abbrev Interpretation.interpret (I : Interpretation Δ Role ConceptName)
    (C : Concept Role ConceptName) : Set Δ :=
  C.denotation I.toModal

/-- The set-based reading of instance checking. -/
theorem Interpretation.mem_interpret_iff : x ∈ I.interpret C ↔ ⇓ALC[I,x ⊨ C] :=
  satisfies_mem_denotation

@[simp]
theorem Interpretation.interpret_top : I.interpret (⊤ : Concept Role ConceptName) = Set.univ := by
  ext x
  simp [Interpretation.mem_interpret_iff, Satisfies.true]

@[simp]
theorem Interpretation.interpret_bot : I.interpret (⊥ : Concept Role ConceptName) = ∅ := by
  ext x
  simp [Interpretation.mem_interpret_iff, Satisfies.false]

/-- Terminological axioms. -/
inductive TAxiom (Role ConceptName : Type*) where
  /-- Concept inclusion `C ⊑ D`. -/
  | incl (C D : Concept Role ConceptName)
  /-- Concept equality `C ≡ D`. -/
  | equiv (C D : Concept Role ConceptName)

open scoped Congruence in
/-- An interpretation satisfies a terminological axiom. -/
def Interpretation.SatisfiesTAxiom (I : Interpretation Δ Role ConceptName) :
    TAxiom Role ConceptName → Prop
  | .incl C D => ∀ x, ⇓ALC[I,x ⊨ C → D]
  | .equiv C D => C ≡[Proposition.Equiv I.toModal] D

/-- A TBox is a set of terminological axioms. -/
abbrev TBox (Role ConceptName : Type*) := Set (TAxiom Role ConceptName)

/-- An interpretation satisfies a TBox if it satisfies all of its axioms; such an interpretation
is called a *model* of the TBox [Baader2007, Chapter 2, p. 56]. -/
def Interpretation.SatisfiesTBox (I : Interpretation Δ Role ConceptName)
    (T : TBox Role ConceptName) : Prop :=
  ∀ ax ∈ T, I.SatisfiesTAxiom ax

/-- Global consequence: every model of `T` over the domain `Δ` satisfies `ax`. -/
def Entails (Δ : Type*) (T : TBox Role ConceptName) (ax : TAxiom Role ConceptName) : Prop :=
  ∀ I : Interpretation Δ Role ConceptName, I.SatisfiesTBox T → I.SatisfiesTAxiom ax

/-- A TBox is consistent over the domain `Δ` if it has a model over `Δ`. -/
def Consistent (Δ : Type*) (T : TBox Role ConceptName) : Prop :=
  ∃ I : Interpretation Δ Role ConceptName, I.SatisfiesTBox T

/-- The TBox `{⊤ ⊑ ⊥}` is inconsistent over every domain. This relies on interpretation domains
being nonempty: over an empty domain every concept inclusion would hold vacuously. -/
theorem not_consistent_top_bot : ¬ Consistent Δ ({.incl ⊤ ⊥} : TBox Role ConceptName) := by
  rintro ⟨I, hI⟩
  obtain ⟨x⟩ := I.nonempty
  have h : ⇓ALC[I,x ⊨ ⊤ → ⊥] := hI _ rfl x
  rw [Satisfies.imp_iff_imp] at h
  exact Satisfies.false.1 (h Satisfies.true)

/-- Subsumption with respect to the empty TBox is validity of `C → D` in `K_m`. -/
theorem entails_empty_iff :
    Entails Δ (∅ : TBox Role ConceptName) (.incl C D) ↔
      ∀ I : Interpretation Δ Role ConceptName, ∀ x, ⇓ALC[I,x ⊨ C → D] := by
  simp [Entails, Interpretation.SatisfiesTBox, Interpretation.SatisfiesTAxiom]

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
def Interpretation.SatisfiesAssertion (I : Interpretation Δ Role ConceptName)
    (ι : Individual → Δ) : Assertion Role ConceptName Individual → Prop
  | .concept C a => ⇓ALC[I,ι a ⊨ C]
  | .role R a b => I.role R (ι a) (ι b)

/-- An interpretation, together with an interpretation `ι` of individuals, satisfies an ABox if it
satisfies all of its assertions. -/
def Interpretation.SatisfiesABox (I : Interpretation Δ Role ConceptName) (ι : Individual → Δ)
    (A : ABox Role ConceptName Individual) : Prop :=
  ∀ α ∈ A, I.SatisfiesAssertion ι α

end Cslib.Logic.DL
