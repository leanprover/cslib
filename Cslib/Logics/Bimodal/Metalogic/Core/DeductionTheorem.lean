/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/
import Cslib.Logics.Bimodal.Metalogic.Core.DerivationTree
import Cslib.Logics.Bimodal.Theorems.Perpetuity.Helpers

/-!
# Deduction Theorem - Hilbert System Deduction Infrastructure

This module proves the deduction theorem for the bimodal TM logic Hilbert system.

## Main Results

- `deduction_axiom`: If φ is an axiom, then `Γ ⊢ A → φ`
- `deduction_assumption_same`: `Γ ⊢ A → A` (identity)
- `deduction_assumption_other`: If `B ∈ Γ`, then `Γ ⊢ A → B`
- `deduction_mp`: Modus ponens under implication
- `deduction_theorem`: If `A :: Γ ⊢ B` then `Γ ⊢ A → B`
- `bimodal_has_deduction_theorem`: Instance connecting to generic MCS framework

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

namespace Cslib.Logic.Bimodal.Metalogic.Core

open Cslib.Logic.Bimodal
open Cslib.Logic.Bimodal.Theorems.Perpetuity (identity)

variable {Atom : Type*}

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## Helper Lemmas -/

/--
Helper: Apply implication introduction pattern.
If `⊢ φ` then `⊢ A → φ` for any A.

This uses the S axiom (weakening): `φ → (A → φ)`.
-/
def weaken_under_imp {fc : FrameClass} {φ A : Formula Atom}
    (h : DerivationTree fc [] φ) : DerivationTree fc [] (A.imp φ) := by
  have s_ax : DerivationTree fc [] (φ.imp (A.imp φ)) :=
    DerivationTree.axiom [] _ (Axiom.imp_s φ A) trivial
  exact DerivationTree.modus_ponens [] φ (A.imp φ) s_ax h

/--
Helper: Lift weakening to contexts.
If `Γ ⊢ φ` then `Γ ⊢ A → φ` for formulas φ that are axioms.
-/
def weaken_under_imp_ctx {fc : FrameClass} {Γ : Context Atom} {φ A : Formula Atom}
    (h : Axiom φ) (h_fc : h.minFrameClass ≤ fc) :
    DerivationTree fc Γ (A.imp φ) := by
  have ax_deriv : DerivationTree fc [] φ := DerivationTree.axiom [] φ h h_fc
  have weakened : DerivationTree fc [] (A.imp φ) := weaken_under_imp ax_deriv
  exact DerivationTree.weakening [] Γ (A.imp φ) weakened (List.nil_subset Γ)

/--
Helper: Remove an element from a list.

Returns the list with all occurrences of `a` removed.
-/
def removeAll {α : Type _} [DecidableEq α] (l : List α) (a : α) : List α :=
  l.filter (· ≠ a)

/--
Helper: If `A ∈ Γ'` and `Γ' ⊆ A :: Γ`, then `removeAll Γ' A ⊆ Γ`.

This shows that removing A from Γ' gives a subset of Γ.
-/
theorem removeAll_subset {A : Formula Atom} {Γ Γ' : Context Atom}
    (_h_mem : A ∈ Γ')
    (h_sub : Γ' ⊆ A :: Γ) :
    removeAll Γ' A ⊆ Γ := by
  intro x hx
  unfold removeAll at hx
  simp only [removeAll, List.mem_filter, decide_eq_true_eq] at hx
  have ⟨h_in, h_ne⟩ := hx
  have h_mem := h_sub h_in
  simp only [List.mem_cons] at h_mem
  cases h_mem with
  | inl h_eq =>
    exact absurd h_eq h_ne
  | inr h_mem => exact h_mem

/-! ## Deduction Theorem Cases -/

/--
Deduction case for axioms: If φ is an axiom, then `Γ ⊢ A → φ`.

**Strategy**: Use S axiom to weaken φ under implication A.
-/
def deduction_axiom {fc : FrameClass} (Γ : Context Atom) (A φ : Formula Atom) (h_ax : Axiom φ)
    (h_fc : h_ax.minFrameClass ≤ fc) :
    DerivationTree fc Γ (A.imp φ) := by
  exact weaken_under_imp_ctx h_ax h_fc

/--
Deduction case for same assumption: `Γ ⊢ A → A`.

**Strategy**: Use identity theorem (already proven in Perpetuity/Helpers.lean).
-/
def deduction_assumption_same {fc : FrameClass} (Γ : Context Atom)
    (A : Formula Atom) :
    DerivationTree fc Γ (A.imp A) := by
  have id : DerivationTree FrameClass.Base [] (A.imp A) := identity A
  have id_fc : DerivationTree fc [] (A.imp A) :=
    DerivationTree.lift (fc₁ := .Base) trivial id
  exact DerivationTree.weakening [] Γ (A.imp A) id_fc (List.nil_subset Γ)

/--
Deduction case for other assumptions: If `B ∈ Γ`, then `Γ ⊢ A → B`.

**Strategy**: Use S axiom to weaken assumption B under implication A.
-/
def deduction_assumption_other {fc : FrameClass} (Γ : Context Atom) (A B : Formula Atom)
    (h_mem : B ∈ Γ) : DerivationTree fc Γ (A.imp B) := by
  have b_deriv : DerivationTree fc Γ B := DerivationTree.assumption Γ B h_mem
  have s_ax : DerivationTree fc [] (B.imp (A.imp B)) :=
    DerivationTree.axiom [] _ (Axiom.imp_s B A) trivial
  have s_weak : DerivationTree fc Γ (B.imp (A.imp B)) :=
    DerivationTree.weakening [] Γ (B.imp (A.imp B)) s_ax (List.nil_subset Γ)
  exact DerivationTree.modus_ponens Γ B (A.imp B) s_weak b_deriv

/--
Deduction case for modus ponens:
If `Γ ⊢ A → (C → D)` and `Γ ⊢ A → C` then `Γ ⊢ A → D`.

**Strategy**: Use K axiom distribution: `(A → C → D) → ((A → C) → (A → D))`.
-/
def deduction_mp {fc : FrameClass} (Γ : Context Atom) (A C D : Formula Atom)
    (h1 : DerivationTree fc Γ (A.imp (C.imp D)))
    (h2 : DerivationTree fc Γ (A.imp C)) :
    DerivationTree fc Γ (A.imp D) := by
  -- K axiom: (A → C → D) → ((A → C) → (A → D))
  have k_ax : DerivationTree fc [] ((A.imp (C.imp D)).imp ((A.imp C).imp (A.imp D))) :=
    DerivationTree.axiom [] _ (Axiom.imp_k A C D) trivial
  have k_weak : DerivationTree fc Γ ((A.imp (C.imp D)).imp ((A.imp C).imp (A.imp D))) :=
    DerivationTree.weakening [] Γ _ k_ax (List.nil_subset Γ)
  -- Apply modus ponens twice
  have step1 : DerivationTree fc Γ ((A.imp C).imp (A.imp D)) :=
    DerivationTree.modus_ponens Γ (A.imp (C.imp D)) ((A.imp C).imp (A.imp D)) k_weak h1
  exact DerivationTree.modus_ponens Γ (A.imp C) (A.imp D) step1 h2

/--
Deduction theorem for contexts where A appears in the middle.

If `Γ' ⊢ φ` and `A ∈ Γ'`, then `(removeAll Γ' A) ⊢ A → φ`.

This is the key lemma for handling the weakening case where A appears in Γ'
but not at the front. By recursing on the structure of the derivation (not using
exchange), all recursive calls have strictly smaller height.
-/
def deduction_with_mem {fc : FrameClass} (Γ' : Context Atom)
    (A φ : Formula Atom)
    (h : DerivationTree fc Γ' φ) (hA : A ∈ Γ') :
    DerivationTree fc (removeAll Γ' A) (A.imp φ) := by
  haveI : Decidable (A ∈ Γ') := Classical.propDecidable _
  match h with
  | DerivationTree.axiom _ ψ h_ax h_fc =>
      exact deduction_axiom (removeAll Γ' A) A ψ h_ax h_fc

  | DerivationTree.assumption _ ψ h_mem =>
      by_cases h_eq : ψ = A
      · rw [← h_eq]
        exact deduction_assumption_same (removeAll Γ' ψ) ψ
      · have h_mem' : ψ ∈ removeAll Γ' A := by
          simp only [removeAll, List.mem_filter, decide_eq_true_eq]
          exact ⟨h_mem, h_eq⟩
        exact deduction_assumption_other (removeAll Γ' A) A ψ h_mem'

  | DerivationTree.modus_ponens _ ψ χ h1 h2 =>
      have ih1 := deduction_with_mem Γ' A (ψ.imp χ) h1 hA
      have ih2 := deduction_with_mem Γ' A ψ h2 hA
      exact deduction_mp (removeAll Γ' A) A ψ χ ih1 ih2

  | DerivationTree.necessitation ψ h_deriv =>
      simp at hA

  | DerivationTree.temporal_necessitation ψ h_deriv =>
      simp at hA

  | DerivationTree.temporal_duality ψ h_deriv =>
      simp at hA

  | DerivationTree.weakening Γ'' _ ψ h1 h2 =>
      haveI : Decidable (A ∈ Γ'') := Classical.propDecidable _
      by_cases hA' : A ∈ Γ''
      · have ih := deduction_with_mem Γ'' A ψ h1 hA'
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
  3. `A ∈ Γ'` but `Γ' ≠ A :: Γ`: Use deduction_with_mem helper
- Modal/temporal necessitation: Cannot occur (require empty context)
- Temporal duality: Cannot occur (requires empty context)
-/
def deduction_theorem {fc : FrameClass} (Γ : Context Atom) (A B : Formula Atom)
    (h : DerivationTree fc (A :: Γ) B) :
    DerivationTree fc Γ (A.imp B) := by
  haveI : Decidable (A ∈ Γ) := Classical.propDecidable _
  match h with
  | DerivationTree.axiom _ φ h_ax h_fc =>
      exact deduction_axiom Γ A φ h_ax h_fc

  | DerivationTree.assumption _ φ h_mem =>
      by_cases h_eq : φ = A
      · subst h_eq
        exact deduction_assumption_same Γ φ
      · have h_tail : φ ∈ Γ := by
          cases h_mem with
          | head => exact absurd rfl h_eq
          | tail _ h => exact h
        exact deduction_assumption_other Γ A φ h_tail

  | DerivationTree.modus_ponens _ φ ψ h1 h2 =>
      have ih1 := deduction_theorem Γ A (φ.imp ψ) h1
      have ih2 := deduction_theorem Γ A φ h2
      exact deduction_mp Γ A φ ψ ih1 ih2

  | DerivationTree.weakening Γ' _ φ h1 h2 =>
      by_cases h_eq : Γ' = A :: Γ
      · exact deduction_theorem Γ A φ (h_eq ▸ h1)
      · haveI : Decidable (A ∈ Γ') := Classical.propDecidable _
        by_cases hA : A ∈ Γ'
        · have ih := deduction_with_mem Γ' A φ h1 hA
          have h_sub : removeAll Γ' A ⊆ Γ :=
            removeAll_subset hA h2
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
def bimodal_has_deduction_theorem :
    Metalogic.HasDeductionTheorem (bimodalDerivationSystem (Atom := Atom)) := by
  intro Γ φ ψ h
  show Bimodal.Deriv Γ (φ.imp ψ)
  obtain ⟨d⟩ := (h : Bimodal.Deriv (φ :: Γ) ψ)
  exact ⟨deduction_theorem Γ φ ψ d⟩

end -- noncomputable section

end Cslib.Logic.Bimodal.Metalogic.Core
