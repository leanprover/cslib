/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

import Cslib.Logics.Temporal.Metalogic.DerivationTree

/-! # Deduction Theorem for Temporal Logic BX

This module proves the deduction theorem for the temporal BX Hilbert system:
if `A :: Γ ⊢ B` then `Γ ⊢ A → B`.

## Main Results

- `deduction_theorem`: The core metatheorem, by well-founded recursion on derivation height.
- `deduction_with_mem`: Helper for the weakening case where the deduction hypothesis
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

namespace Cslib.Logic.Temporal

open Cslib.Logic

variable {Atom : Type*}

attribute [local instance] Classical.propDecidable

/-! ## Helper: removeAll -/

/-- Remove all occurrences of `a` from a list. -/
def removeAll [DecidableEq α] (l : List α) (a : α) : List α :=
  l.filter (· ≠ a)

private theorem removeAll_sub_of_sub [DecidableEq α] {A : α} {Γ' Δ : List α}
    (h_sub : Γ' ⊆ A :: Δ) (h_mem : A ∈ Γ') :
    removeAll Γ' A ⊆ Δ := by
  intro x hx
  simp [removeAll, List.mem_filter] at hx
  obtain ⟨hx_in, hx_ne⟩ := hx
  have := h_sub hx_in
  simp [List.mem_cons] at this
  rcases this with rfl | h
  · exact absurd rfl hx_ne
  · exact h

private theorem mem_removeAll_of_mem_of_ne [DecidableEq α] {a x : α} {l : List α}
    (h_mem : x ∈ l) (h_ne : x ≠ a) : x ∈ removeAll l a := by
  simp [removeAll, List.mem_filter]
  exact ⟨h_mem, h_ne⟩

private theorem removeAll_sub_removeAll [DecidableEq α] {a : α} {l₁ l₂ : List α}
    (h : l₁ ⊆ l₂) : removeAll l₁ a ⊆ removeAll l₂ a := by
  intro x hx
  simp [removeAll, List.mem_filter] at hx ⊢
  exact ⟨h hx.1, hx.2⟩

/-! ## Deduction Theorem Helper Cases -/

/-- If `φ` is an axiom, then `Γ ⊢ A → φ`. -/
noncomputable def deduction_axiom (Γ : Context Atom) (A φ : Formula Atom)
    (h_ax : Axiom φ) (h_fc : h_ax.minFrameClass ≤ FrameClass.Base) :
    DerivationTree FrameClass.Base Γ (A.imp φ) := by
  have ax_deriv : DerivationTree FrameClass.Base [] φ := .axiom [] φ h_ax h_fc
  have k_ax : DerivationTree FrameClass.Base [] (φ.imp (A.imp φ)) :=
    .axiom [] _ (.imp_s φ A) trivial
  have result : DerivationTree FrameClass.Base [] (A.imp φ) :=
    .modus_ponens [] φ (A.imp φ) k_ax ax_deriv
  exact .weakening [] Γ (A.imp φ) result (List.nil_subset _)

/-- `Γ ⊢ A → A` (identity / self-implication). -/
noncomputable def deduction_imp_self (Γ : Context Atom) (A : Formula Atom) :
    DerivationTree FrameClass.Base Γ (A.imp A) := by
  let s := DerivationTree.axiom (Atom := Atom) (fc := FrameClass.Base) [] _
    (.imp_k A (.imp A A) A) trivial
  let k1 := DerivationTree.axiom (Atom := Atom) (fc := FrameClass.Base) [] _
    (.imp_s A (.imp A A)) trivial
  let k2 := DerivationTree.axiom (Atom := Atom) (fc := FrameClass.Base) [] _
    (.imp_s A A) trivial
  let step1 := DerivationTree.modus_ponens [] _ _ s k1
  let result := DerivationTree.modus_ponens [] _ _ step1 k2
  exact .weakening [] Γ _ result (List.nil_subset _)

/-- If `B ∈ Γ`, then `Γ ⊢ A → B`. -/
noncomputable def deduction_assumption_other (Γ : Context Atom)
    (A B : Formula Atom) (h_mem : B ∈ Γ) :
    DerivationTree FrameClass.Base Γ (A.imp B) := by
  have b_deriv : DerivationTree FrameClass.Base Γ B :=
    DerivationTree.assumption Γ B h_mem
  have k_ax : DerivationTree FrameClass.Base [] (B.imp (A.imp B)) :=
    .axiom [] _ (.imp_s B A) trivial
  have k_weak := DerivationTree.weakening [] Γ _ k_ax (List.nil_subset _)
  exact .modus_ponens Γ B (A.imp B) k_weak b_deriv

/-- Modus ponens under implication: from `Γ ⊢ A → (C → D)` and `Γ ⊢ A → C`,
derive `Γ ⊢ A → D`. -/
noncomputable def deduction_mp (Γ : Context Atom)
    (A C D : Formula Atom)
    (h₁ : DerivationTree FrameClass.Base Γ (A.imp (C.imp D)))
    (h₂ : DerivationTree FrameClass.Base Γ (A.imp C)) :
    DerivationTree FrameClass.Base Γ (A.imp D) := by
  have s_ax : DerivationTree FrameClass.Base []
      ((A.imp (C.imp D)).imp ((A.imp C).imp (A.imp D))) :=
    .axiom [] _ (.imp_k A C D) trivial
  have s_weak := DerivationTree.weakening [] Γ _ s_ax (List.nil_subset _)
  have step1 := DerivationTree.modus_ponens Γ _ _ s_weak h₁
  exact .modus_ponens Γ _ _ step1 h₂

/-! ## Core: deduction_with_mem -/

/-- The key helper for the weakening case: if `Γ' ⊢ φ` and `A ∈ Γ'`, then
`removeAll Γ' A ⊢ A → φ`. -/
noncomputable def deduction_with_mem
    (Γ' : Context Atom) (A φ : Formula Atom)
    (d : DerivationTree FrameClass.Base Γ' φ) (hA : A ∈ Γ') :
    DerivationTree FrameClass.Base (removeAll Γ' A) (A.imp φ) := by
  match d with
  | .axiom _ ψ h_ax h_fc =>
    exact deduction_axiom (removeAll Γ' A) A ψ h_ax h_fc
  | .assumption _ ψ h_mem =>
    by_cases h_eq : ψ = A
    · subst h_eq
      exact deduction_imp_self (removeAll Γ' ψ) ψ
    · have h_mem' : ψ ∈ removeAll Γ' A := mem_removeAll_of_mem_of_ne h_mem h_eq
      exact deduction_assumption_other (removeAll Γ' A) A ψ h_mem'
  | .modus_ponens _ ψ χ d₁ d₂ =>
    have ih₁ := deduction_with_mem Γ' A (ψ.imp χ) d₁ hA
    have ih₂ := deduction_with_mem Γ' A ψ d₂ hA
    exact deduction_mp (removeAll Γ' A) A ψ χ ih₁ ih₂
  | .temporal_necessitation ψ _d' =>
    simp at hA
  | .temporal_duality ψ _d' =>
    simp at hA
  | .weakening Γ'' _ ψ d' h_sub =>
    by_cases hA' : A ∈ Γ''
    · have ih := deduction_with_mem Γ'' A ψ d' hA'
      exact .weakening (removeAll Γ'' A) (removeAll Γ' A) (A.imp ψ) ih
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
noncomputable def deduction_theorem (Γ : Context Atom) (A B : Formula Atom)
    (d : DerivationTree FrameClass.Base (A :: Γ) B) :
    DerivationTree FrameClass.Base Γ (A.imp B) := by
  match d with
  | .axiom _ φ h_ax h_fc =>
    exact deduction_axiom Γ A φ h_ax h_fc
  | .assumption _ φ h_mem =>
    by_cases h_eq : φ = A
    · subst h_eq
      exact deduction_imp_self Γ φ
    · have h_tail : φ ∈ Γ := by
        cases h_mem with
        | head => exact absurd rfl h_eq
        | tail _ h => exact h
      exact deduction_assumption_other Γ A φ h_tail
  | .modus_ponens _ φ ψ d₁ d₂ =>
    have ih₁ := deduction_theorem Γ A (φ.imp ψ) d₁
    have ih₂ := deduction_theorem Γ A φ d₂
    exact deduction_mp Γ A φ ψ ih₁ ih₂
  | .weakening Γ' _ φ d' h_sub =>
    by_cases h_eq : Γ' = A :: Γ
    · exact deduction_theorem Γ A φ (h_eq ▸ d')
    · by_cases hA : A ∈ Γ'
      · have ih := deduction_with_mem Γ' A φ d' hA
        exact .weakening (removeAll Γ' A) Γ (A.imp φ) ih
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
  exact ⟨deduction_theorem Γ φ ψ d⟩

end Cslib.Logic.Temporal
