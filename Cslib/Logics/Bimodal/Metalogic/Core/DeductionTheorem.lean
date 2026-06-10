/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module
public import Cslib.Logics.Bimodal.Metalogic.Core.DerivationTree
public import Cslib.Logics.Bimodal.Theorems.Perpetuity.Helpers
public import Cslib.Foundations.Data.ListHelpers
public import Cslib.Foundations.Logic.Metalogic.DeductionHelpers

/-!
# Deduction Theorem - Hilbert System Deduction Infrastructure

This module proves the deduction theorem for the bimodal TM logic Hilbert system.

## Main Results

- `bimodalHilbertTree`: `HasHilbertTree` for bimodal logic (fc-parameterized)
- Generic helpers via `DeductionHelpers`: `deductionAxiom`, `deductionImpSelf`,
  `deductionAssumptionOther`, `deductionMpUnderImp`
- `deductionTheorem`: If `A :: Γ ⊢ B` then `Γ ⊢ A → B`
- `bimodalHasDeductionTheorem`: Instance connecting to generic MCS framework

## Implementation Notes

The deduction theorem for Hilbert systems requires induction on the derivation structure.
We handle each case of the 7-constructor DerivationTree:
- Base case: axiom
- Base case: assumption (splits into same vs other)
- Inductive case: modus ponens
- Inductive case: weakening (reduces to subderivation)
- Modal/temporal necessitation and temporal duality do not apply with non-empty contexts

## References

* Ported from BimodalLogic/Theories/Bimodal/Metalogic/Core/DeductionTheorem.lean
* Cslib/Logics/Temporal/Metalogic/DeductionTheorem.lean — temporal pattern
-/

set_option linter.style.emptyLine false
set_option linter.flexible false

@[expose] public section

namespace Cslib.Logic.Bimodal.Metalogic.Core

open Cslib.Logic
open Cslib.Logic.Bimodal
open Cslib.Logic.Helpers

variable {Atom : Type*}

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## HasHilbertTree Instance -/

/-- `HasHilbertTree` for bimodal logic, parameterized by frame class.
Since the bimodal deduction theorem is polymorphic in `fc`, this is defined as
a function rather than an instance. Use `letI` to bring it into scope.
Note: Bimodal uses swapped axiom names -- `.imp_s` is K and `.imp_k` is S. -/
@[reducible] def bimodalHilbertTree (fc : FrameClass) : HasHilbertTree (Formula Atom) where
  Tree := fun Γ φ => DerivationTree fc Γ φ
  implyK := fun φ ψ => .axiom [] _ (.imp_s φ ψ) trivial
  implyS := fun φ ψ χ => .axiom [] _ (.imp_k φ ψ χ) trivial
  assumption := fun h => .assumption _ _ h
  mp := fun d₁ d₂ => .modus_ponens _ _ _ d₁ d₂
  weakening := fun d h => .weakening _ _ _ d h

/--
Deduction theorem for contexts where A appears in the middle.

If `Γ' ⊢ φ` and `A ∈ Γ'`, then `(removeAll Γ' A) ⊢ A → φ`.

This is the key lemma for handling the weakening case where A appears in Γ'
but not at the front. By recursing on the structure of the derivation (not using
exchange), all recursive calls have strictly smaller height.
-/
def deductionWithMem {fc : FrameClass} (Γ' : Context Atom)
    (A φ : Formula Atom)
    (h : DerivationTree fc Γ' φ) (hA : A ∈ Γ') :
    DerivationTree fc (removeAll Γ' A) (A.imp φ) := by
  letI := bimodalHilbertTree (Atom := Atom) fc
  haveI : Decidable (A ∈ Γ') := Classical.propDecidable _
  match h with
  | DerivationTree.axiom _ ψ h_ax h_fc =>
      exact deductionAxiom (removeAll Γ' A) A (.axiom [] ψ h_ax h_fc)

  | DerivationTree.assumption _ ψ h_mem =>
      by_cases h_eq : ψ = A
      · rw [← h_eq]
        exact deductionImpSelf (removeAll Γ' ψ) ψ
      · have h_mem' : ψ ∈ removeAll Γ' A := by
          simp only [removeAll, List.mem_filter, decide_eq_true_eq]
          exact ⟨h_mem, h_eq⟩
        exact deductionAssumptionOther (removeAll Γ' A) A ψ h_mem'

  | DerivationTree.modus_ponens _ ψ χ h1 h2 =>
      have ih1 := deductionWithMem Γ' A (ψ.imp χ) h1 hA
      have ih2 := deductionWithMem Γ' A ψ h2 hA
      exact deductionMpUnderImp (removeAll Γ' A) A ψ χ ih1 ih2

  | DerivationTree.necessitation ψ h_deriv =>
      simp at hA

  | DerivationTree.temporal_necessitation ψ h_deriv =>
      simp at hA

  | DerivationTree.temporal_duality ψ h_deriv =>
      simp at hA

  | DerivationTree.weakening Γ'' _ ψ h1 h2 =>
      haveI : Decidable (A ∈ Γ'') := Classical.propDecidable _
      by_cases hA' : A ∈ Γ''
      · have ih := deductionWithMem Γ'' A ψ h1 hA'
        have h_sub : removeAll Γ'' A ⊆ removeAll Γ' A := by
          intro x hx
          simp only [removeAll, List.mem_filter, decide_eq_true_eq] at hx ⊢
          exact ⟨h2 hx.1, hx.2⟩
        exact DerivationTree.weakening (removeAll Γ'' A) (removeAll Γ' A) (A.imp ψ) ih h_sub
      · have h_sub : Γ'' ⊆ removeAll Γ' A := by
          intro x hx
          simp only [removeAll, List.mem_filter, decide_eq_true_eq]
          exact ⟨h2 hx, by intro h_eq; subst h_eq; exact absurd hx hA'⟩
        have h_weak := DerivationTree.weakening Γ'' (removeAll Γ' A) ψ h1 h_sub
        have s_ax : DerivationTree fc [] (ψ.imp (A.imp ψ)) :=
          DerivationTree.axiom [] _ (Axiom.imp_s ψ A) trivial
        have s_weak :=
          DerivationTree.weakening [] (removeAll Γ' A) _ s_ax (List.nil_subset _)
        exact DerivationTree.modus_ponens (removeAll Γ' A) ψ (A.imp ψ) s_weak h_weak

termination_by h.height
decreasing_by
  · exact DerivationTree.mp_height_gt_left h1 h2
  · exact DerivationTree.mp_height_gt_right h1 h2
  · exact DerivationTree.subderiv_height_lt h1 h2

/-! ## Main Deduction Theorem -/

/--
The Deduction Theorem: If `A :: Γ ⊢ B` then `Γ ⊢ A → B`.

This fundamental metatheorem allows converting derivations with assumptions
into implicational theorems.

**Proof Strategy**: Well-founded recursion on derivation height.
- Axiom case: Use S axiom to weaken
- Assumption case: Identity if same, S axiom if different
- Modus ponens case: Use K axiom distribution with recursive calls
- Weakening case: Handle three subcases:
  1. `Γ' = A :: Γ`: Apply recursion directly
  2. `A ∉ Γ'`: Use S axiom (A not needed)
  3. `A ∈ Γ'` but `Γ' ≠ A :: Γ`: Use deductionWithMem helper
- Modal/temporal necessitation: Cannot occur (require empty context)
- Temporal duality: Cannot occur (requires empty context)
-/
def deductionTheorem {fc : FrameClass} (Γ : Context Atom) (A B : Formula Atom)
    (h : DerivationTree fc (A :: Γ) B) :
    DerivationTree fc Γ (A.imp B) := by
  letI := bimodalHilbertTree (Atom := Atom) fc
  haveI : Decidable (A ∈ Γ) := Classical.propDecidable _
  match h with
  | DerivationTree.axiom _ φ h_ax h_fc =>
      exact deductionAxiom Γ A (.axiom [] φ h_ax h_fc)

  | DerivationTree.assumption _ φ h_mem =>
      by_cases h_eq : φ = A
      · subst h_eq
        exact deductionImpSelf Γ φ
      · have h_tail : φ ∈ Γ := by
          cases h_mem with
          | head => exact absurd rfl h_eq
          | tail _ h => exact h
        exact deductionAssumptionOther Γ A φ h_tail

  | DerivationTree.modus_ponens _ φ ψ h1 h2 =>
      have ih1 := deductionTheorem Γ A (φ.imp ψ) h1
      have ih2 := deductionTheorem Γ A φ h2
      exact deductionMpUnderImp Γ A φ ψ ih1 ih2

  | DerivationTree.weakening Γ' _ φ h1 h2 =>
      by_cases h_eq : Γ' = A :: Γ
      · exact deductionTheorem Γ A φ (h_eq ▸ h1)
      · haveI : Decidable (A ∈ Γ') := Classical.propDecidable _
        by_cases hA : A ∈ Γ'
        · have ih := deductionWithMem Γ' A φ h1 hA
          have h_sub : removeAll Γ' A ⊆ Γ :=
            removeAll_sub_of_sub h2 hA
          exact DerivationTree.weakening (removeAll Γ' A) Γ (A.imp φ) ih h_sub
        · have h_sub : Γ' ⊆ Γ := by
            intro x hx
            have h_mem := h2 hx
            simp only [List.mem_cons] at h_mem
            cases h_mem with
            | inl h_eq => subst h_eq; exact absurd hx hA
            | inr h_mem => exact h_mem
          have h_weak := DerivationTree.weakening Γ' Γ φ h1 h_sub
          have s_ax : DerivationTree fc [] (φ.imp (A.imp φ)) :=
            DerivationTree.axiom [] _ (Axiom.imp_s φ A) trivial
          have s_weak :=
            DerivationTree.weakening [] Γ _ s_ax (List.nil_subset Γ)
          exact DerivationTree.modus_ponens Γ φ (A.imp φ) s_weak h_weak

termination_by h.height
decreasing_by
  · exact DerivationTree.mp_height_gt_left _ _
  · exact DerivationTree.mp_height_gt_right _ _
  · have heq : (h_eq ▸ h1).height = h1.height := by subst h_eq; rfl
    rw [heq]
    exact DerivationTree.subderiv_height_lt h1 h2

/-! ## Generic MCS Framework Connection -/

/--
The bimodal deduction theorem wrapped for the generic MCS framework.

This witnesses that `bimodalDerivationSystem` satisfies the `HasDeductionTheorem`
property, enabling use of generic MCS closure properties (closed_under_derivation,
implication_property, negation_complete) from `Consistency.lean`.
-/
def bimodalHasDeductionTheorem :
    Metalogic.HasDeductionTheorem (bimodalDerivationSystem (Atom := Atom)) := by
  intro Γ φ ψ h
  show Bimodal.Deriv Γ (φ.imp ψ)
  obtain ⟨d⟩ := (h : Bimodal.Deriv (φ :: Γ) ψ)
  exact ⟨deductionTheorem Γ φ ψ d⟩

end -- noncomputable section

end Cslib.Logic.Bimodal.Metalogic.Core
