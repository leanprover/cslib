/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Temporal.Metalogic.DerivationTree
public import Cslib.Foundations.Data.ListHelpers
public import Cslib.Foundations.Logic.Metalogic.DeductionHelpers

/-! # Deduction Theorem for Temporal Logic BX

This module proves the deduction theorem for the temporal BX Hilbert system:
if `A :: Γ ⊢ B` then `Γ ⊢ A → B`.

## Main Results

- `deductionTheorem`: The core metatheorem, by well-founded recursion on derivation height.
- `deductionWithMem`: Helper for the weakening case where the deduction hypothesis
  appears in the middle of the context.
- `temporal_has_deduction_theorem`: The `HasDeductionTheorem` instance for the generic
  MCS framework.

## Implementation

The proof follows the modal metalogic pattern with well-founded recursion on
`DerivationTree.height`. The temporal version handles 6 constructors (vs. 5 for modal):
both `temporal_necessitation` and `temporal_duality` require empty context, making them
vacuously impossible when the context is `A :: Gamma`.

## References

* Cslib/Logics/Modal/Metalogic/DeductionTheorem.lean — direct template
* Cslib/Foundations/Logic/Metalogic/Consistency.lean
-/

set_option linter.flexible false
set_option linter.style.multiGoal false
set_option linter.unusedTactic false
set_option linter.style.setOption false

@[expose] public section

namespace Cslib.Logic.Temporal

open Cslib.Logic
open Cslib.Logic.Helpers

variable {Atom : Type*}

attribute [local instance] Classical.propDecidable

/-! ## HasHilbertTree Instance -/

/-- `HasHilbertTree` instance for temporal logic at `FrameClass.Base`.
Note: Temporal uses swapped axiom names -- `.imp_s` is K (weakening) and
`.imp_k` is S (distribution). -/
noncomputable instance : HasHilbertTree (Formula Atom) where
  Tree := fun Γ φ => DerivationTree FrameClass.Base Γ φ
  implyK := fun φ ψ => .axiom [] _ (.imp_s φ ψ) trivial
  implyS := fun φ ψ χ => .axiom [] _ (.imp_k φ ψ χ) trivial
  assumption := fun h => .assumption _ _ h
  mp := fun d₁ d₂ => .modus_ponens _ _ _ d₁ d₂
  weakening := fun d h => .weakening _ _ _ d h

/-! ## Core: deductionWithMem -/

/-- The key helper for the weakening case: if `Γ' ⊢ φ` and `A ∈ Γ'`, then
`removeAll Γ' A ⊢ A → φ`. -/
noncomputable def deductionWithMem
    (Γ' : Context Atom) (A φ : Formula Atom)
    (d : DerivationTree FrameClass.Base Γ' φ) (hA : A ∈ Γ') :
    DerivationTree FrameClass.Base (removeAll Γ' A) (A → φ) := by
  match d with
  | .axiom _ ψ h_ax h_fc =>
    exact deductionAxiom (removeAll Γ' A) A (.axiom [] ψ h_ax h_fc)
  | .assumption _ ψ h_mem =>
    by_cases h_eq : ψ = A
    · subst h_eq
      exact deductionImpSelf (removeAll Γ' ψ) ψ
    · have h_mem' : ψ ∈ removeAll Γ' A := mem_removeAll_of_mem_of_ne h_mem h_eq
      exact deductionAssumptionOther (removeAll Γ' A) A ψ h_mem'
  | .modus_ponens _ ψ χ d₁ d₂ =>
    have ih₁ := deductionWithMem Γ' A (ψ → χ) d₁ hA
    have ih₂ := deductionWithMem Γ' A ψ d₂ hA
    exact deductionMpUnderImp (removeAll Γ' A) A ψ χ ih₁ ih₂
  | .temporal_necessitation ψ _d' =>
    simp at hA
  | .temporal_duality ψ _d' =>
    simp at hA
  | .weakening Γ'' _ ψ d' h_sub =>
    by_cases hA' : A ∈ Γ''
    · have ih := deductionWithMem Γ'' A ψ d' hA'
      exact .weakening (removeAll Γ'' A) (removeAll Γ' A) (A → ψ) ih
        (removeAll_sub_removeAll h_sub)
    · have h_sub' : Γ'' ⊆ removeAll Γ' A := by
        intro x hx
        exact mem_removeAll_of_mem_of_ne (h_sub hx) (fun h_eq => hA' (h_eq ▸ hx))
      have d_weak := DerivationTree.weakening Γ'' (removeAll Γ' A) ψ d' h_sub'
      have k_ax : DerivationTree FrameClass.Base [] (ψ.imp (A.imp ψ)) :=
        .axiom [] _ (.imp_s ψ A) trivial
      have k_weak := DerivationTree.weakening [] (removeAll Γ' A) _ k_ax
        (List.nil_subset _)
      exact .modus_ponens (removeAll Γ' A) ψ (A.imp ψ) k_weak d_weak
termination_by d.height
decreasing_by
  all_goals simp_wf
  · exact DerivationTree.height_modus_ponens_left d₁ d₂
  · exact DerivationTree.height_modus_ponens_right d₁ d₂
  · exact DerivationTree.height_weakening d' h_sub

/-! ## Main Deduction Theorem -/

/-- **Deduction Theorem**: If `A :: Γ ⊢ B` then `Γ ⊢ A → B`.

Proof by well-founded recursion on derivation tree height. Handles all 6 constructors. -/
noncomputable def deductionTheorem (Γ : Context Atom) (A B : Formula Atom)
    (d : DerivationTree FrameClass.Base (A :: Γ) B) :
    DerivationTree FrameClass.Base Γ (A → B) := by
  match d with
  | .axiom _ φ h_ax h_fc =>
    exact deductionAxiom Γ A (.axiom [] φ h_ax h_fc)
  | .assumption _ φ h_mem =>
    by_cases h_eq : φ = A
    · subst h_eq
      exact deductionImpSelf Γ φ
    · have h_tail : φ ∈ Γ := by
        cases h_mem with
        | head => exact absurd rfl h_eq
        | tail _ h => exact h
      exact deductionAssumptionOther Γ A φ h_tail
  | .modus_ponens _ φ ψ d₁ d₂ =>
    have ih₁ := deductionTheorem Γ A (φ → ψ) d₁
    have ih₂ := deductionTheorem Γ A φ d₂
    exact deductionMpUnderImp Γ A φ ψ ih₁ ih₂
  | .weakening Γ' _ φ d' h_sub =>
    by_cases h_eq : Γ' = A :: Γ
    · exact deductionTheorem Γ A φ (h_eq ▸ d')
    · by_cases hA : A ∈ Γ'
      · have ih := deductionWithMem Γ' A φ d' hA
        exact .weakening (removeAll Γ' A) Γ (A → φ) ih
          (removeAll_sub_of_sub h_sub hA)
      · have h_sub' : Γ' ⊆ Γ := by
          intro x hx
          have := h_sub hx
          simp [List.mem_cons] at this
          rcases this with rfl | h
          · exact absurd hx hA
          · exact h
        have d_weak := DerivationTree.weakening Γ' Γ φ d' h_sub'
        have k_ax : DerivationTree (Atom := Atom) FrameClass.Base []
            (φ.imp (A.imp φ)) := .axiom [] _ (.imp_s φ A) trivial
        have k_weak := DerivationTree.weakening [] Γ _ k_ax (List.nil_subset _)
        exact .modus_ponens Γ φ (A.imp φ) k_weak d_weak
termination_by d.height
decreasing_by
  · exact DerivationTree.height_modus_ponens_left d₁ d₂
  · exact DerivationTree.height_modus_ponens_right d₁ d₂
  · have h1 : (h_eq ▸ d').height = d'.height := by subst h_eq; rfl
    simp [h1, DerivationTree.height]

/-! ## HasDeductionTheorem Instance -/

/-- The deduction theorem wrapped for the generic MCS framework. -/
theorem temporal_has_deduction_theorem :
    Metalogic.HasDeductionTheorem (@temporalDerivationSystem Atom) := by
  intro Γ φ ψ h
  unfold temporalDerivationSystem Temporal.Deriv at h ⊢
  simp at h ⊢
  obtain ⟨d⟩ := h
  exact ⟨deductionTheorem Γ φ ψ d⟩

end Cslib.Logic.Temporal
