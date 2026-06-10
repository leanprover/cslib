/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Modal.Metalogic.DerivationTree
public import Cslib.Foundations.Logic.Helpers.ListHelpers

/-! # Deduction Theorem for S5 Modal Logic

This module proves the deduction theorem for the S5 modal logic Hilbert system:
if `A :: Γ ⊢ B` then `Γ ⊢ A → B`.

## Main Results

- `deduction_theorem`: The core metatheorem, by well-founded recursion on derivation height.
- `deduction_with_mem`: Helper for the weakening case where the deduction hypothesis
  appears in the middle of the context.
- `modal_has_deduction_theorem`: The `HasDeductionTheorem` instance for the generic MCS
  framework.

## Implementation

The proof follows the BimodalLogic pattern with well-founded recursion on
`DerivationTree.height`. The key insight is the `deduction_with_mem` helper that
handles the weakening case without introducing non-terminating exchange patterns.

The modal version is simpler than the bimodal one because there are only 5 constructors
(no temporal necessitation or temporal duality), and the necessitation case is trivially
impossible when the context is non-empty.

## References

* BimodalLogic/Theories/Bimodal/Metalogic/Core/DeductionTheorem.lean
* Cslib/Foundations/Logic/Metalogic/Consistency.lean
-/

@[expose] public section

namespace Cslib.Logic.Modal

open Cslib.Logic
open Cslib.Logic.Helpers

variable {Atom : Type*}

attribute [local instance] Classical.propDecidable

/-! ## Deduction Theorem Helper Cases -/

/-- If `φ` is an axiom, then `Γ ⊢ A → φ`. Uses the weakening axiom `implyK`. -/
noncomputable def deduction_axiom (Γ : List (Proposition Atom)) (A φ : Proposition Atom)
    (h_ax : ModalAxiom φ) : DerivationTree Γ (A.imp φ) := by
  -- φ is derivable (from empty context via axiom, weakened to Γ)
  -- Then use implyK: φ → (A → φ) to get A → φ
  have ax_deriv : DerivationTree [] φ := .ax [] φ h_ax
  have k_ax : DerivationTree [] (φ.imp (A.imp φ)) := .ax [] _ (.implyK φ A)
  have result : DerivationTree [] (A.imp φ) := .modus_ponens [] φ (A.imp φ) k_ax ax_deriv
  exact .weakening [] Γ (A.imp φ) result (fun _ h => nomatch h)

/-- `Γ ⊢ A → A` (identity / self-implication). -/
noncomputable def deduction_imp_self (Γ : List (Proposition Atom)) (A : Proposition Atom) :
    DerivationTree Γ (A.imp A) := by
  -- Proof: Use implyS, implyK, implyK to build A → A
  -- 1. implyS: (A → (A → A) → A) → ((A → A → A) → (A → A))
  -- 2. implyK: A → (A → A) → A
  -- 3. implyK: A → A → A
  -- MP(1,2): (A → A → A) → (A → A)
  -- MP(above, 3): A → A
  let s := DerivationTree.ax (Atom := Atom) [] _ (.implyS A (.imp A A) A)
  let k1 := DerivationTree.ax (Atom := Atom) [] _ (.implyK A (.imp A A))
  let k2 := DerivationTree.ax (Atom := Atom) [] _ (.implyK A A)
  let step1 := DerivationTree.modus_ponens [] _ _ s k1
  let result := DerivationTree.modus_ponens [] _ _ step1 k2
  exact .weakening [] Γ _ result (fun _ h => nomatch h)

/-- If `B ∈ Γ`, then `Γ ⊢ A → B`. Uses weakening axiom `implyK`. -/
noncomputable def deduction_assumption_other (Γ : List (Proposition Atom))
    (A B : Proposition Atom) (h_mem : B ∈ Γ) : DerivationTree Γ (A.imp B) := by
  have b_deriv := DerivationTree.assumption Γ B h_mem
  have k_ax : DerivationTree [] (B.imp (A.imp B)) := .ax [] _ (.implyK B A)
  have k_weak := DerivationTree.weakening [] Γ _ k_ax (fun _ h => nomatch h)
  exact .modus_ponens Γ B (A.imp B) k_weak b_deriv

/-- Modus ponens under implication: from `Γ ⊢ A → (C → D)` and `Γ ⊢ A → C`,
derive `Γ ⊢ A → D`. Uses the `implyS` axiom. -/
noncomputable def deduction_mp (Γ : List (Proposition Atom))
    (A C D : Proposition Atom)
    (h₁ : DerivationTree Γ (A.imp (C.imp D)))
    (h₂ : DerivationTree Γ (A.imp C)) :
    DerivationTree Γ (A.imp D) := by
  -- implyS: (A → C → D) → ((A → C) → (A → D))
  have s_ax : DerivationTree [] ((A.imp (C.imp D)).imp ((A.imp C).imp (A.imp D))) :=
    .ax [] _ (.implyS A C D)
  have s_weak := DerivationTree.weakening [] Γ _ s_ax
    (fun _ h => nomatch h)
  have step1 := DerivationTree.modus_ponens Γ _ _ s_weak h₁
  exact .modus_ponens Γ _ _ step1 h₂

/-! ## Core: deduction_with_mem -/

/-- The key helper for the weakening case: if `Γ' ⊢ φ` and `A ∈ Γ'`, then
`removeAll Γ' A ⊢ A → φ`.

This recurses on the derivation structure. All recursive calls are on derivations
with strictly smaller height, ensuring termination. -/
noncomputable def deduction_with_mem
    (Γ' : List (Proposition Atom)) (A φ : Proposition Atom)
    (d : DerivationTree Γ' φ) (hA : A ∈ Γ') :
    DerivationTree (removeAll Γ' A) (A.imp φ) := by
  match d with
  | .ax _ ψ h_ax =>
    exact deduction_axiom (removeAll Γ' A) A ψ h_ax
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
  | .necessitation ψ _d' =>
    -- Γ' = [], but A ∈ Γ' = [] is impossible
    simp at hA
  | .weakening Γ'' _ ψ d' h_sub =>
    by_cases hA' : A ∈ Γ''
    · -- A ∈ Γ'', recurse on d'
      have ih := deduction_with_mem Γ'' A ψ d' hA'
      have h_sub' : ∀ x ∈ removeAll Γ'' A, x ∈ removeAll Γ' A :=
        removeAll_subset_removeAll h_sub
      exact .weakening (removeAll Γ'' A) (removeAll Γ' A) (A.imp ψ) ih h_sub'
    · -- A ∉ Γ'', so Γ'' ⊆ removeAll Γ' A
      have h_sub' : ∀ x ∈ Γ'', x ∈ removeAll Γ' A := by
        intro x hx
        exact mem_removeAll_of_mem_of_ne (h_sub x hx) (fun h_eq => hA' (h_eq ▸ hx))
      have d_weak := DerivationTree.weakening Γ'' (removeAll Γ' A) ψ d' h_sub'
      -- Use implyK: ψ → (A → ψ)
      have k_ax : DerivationTree [] (ψ.imp (A.imp ψ)) := .ax [] _ (.implyK ψ A)
      have k_weak := DerivationTree.weakening [] (removeAll Γ' A) _ k_ax
        (fun _ h => nomatch h)
      exact .modus_ponens (removeAll Γ' A) ψ (A.imp ψ) k_weak d_weak
termination_by d.height
decreasing_by
  simp_wf
  · exact DerivationTree.height_modus_ponens_left d₁ d₂
  · exact DerivationTree.height_modus_ponens_right d₁ d₂
  · exact DerivationTree.height_weakening d' h_sub

/-! ## Main Deduction Theorem -/

/-- **Deduction Theorem**: If `A :: Γ ⊢ B` then `Γ ⊢ A → B`.

Proof by well-founded recursion on derivation tree height. Handles all 5 constructors:
- `ax`: Use `implyK` to weaken the axiom under implication.
- `assumption` (same): Produce `A → A` via `deduction_imp_self`.
- `assumption` (other): Use `implyK` with the other assumption.
- `modus_ponens`: Recurse on both subderivations, combine via `implyS`.
- `necessitation`: Impossible (requires empty context, but `A :: Γ` is non-empty).
- `weakening`: Three subcases -- context equality, `A ∈ Γ'` (uses `deduction_with_mem`),
  or `A ∉ Γ'` (uses `implyK`). -/
noncomputable def deduction_theorem (Γ : List (Proposition Atom)) (A B : Proposition Atom)
    (d : DerivationTree (A :: Γ) B) :
    DerivationTree Γ (A.imp B) := by
  match d with
  | .ax _ φ h_ax =>
    exact deduction_axiom Γ A φ h_ax
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
      · -- A ∈ Γ' but Γ' ≠ A :: Γ -- use deduction_with_mem
        have ih := deduction_with_mem Γ' A φ d' hA
        have h_sub' : ∀ x ∈ removeAll Γ' A, x ∈ Γ :=
          removeAll_subset_of_subset h_sub hA
        exact .weakening (removeAll Γ' A) Γ (A.imp φ) ih h_sub'
      · -- A ∉ Γ', so Γ' ⊆ Γ
        have h_sub' : ∀ x ∈ Γ', x ∈ Γ := by
          intro x hx
          have := h_sub x hx
          simp [List.mem_cons] at this
          rcases this with rfl | h
          · exact absurd hx hA
          · exact h
        have d_weak := DerivationTree.weakening Γ' Γ φ d' h_sub'
        have k_ax : DerivationTree (Atom := Atom) [] (φ.imp (A.imp φ)) := .ax [] _ (.implyK φ A)
        have k_weak := DerivationTree.weakening [] Γ _ k_ax
          (fun _ h => nomatch h)
        exact .modus_ponens Γ φ (A.imp φ) k_weak d_weak
termination_by d.height
decreasing_by
  simp_wf
  · exact DerivationTree.height_modus_ponens_left d₁ d₂
  · exact DerivationTree.height_modus_ponens_right d₁ d₂
  · have : (h_eq ▸ d').height = d'.height := by subst h_eq; rfl
    simp [this]
    exact DerivationTree.height_weakening d' h_sub

/-! ## HasDeductionTheorem Instance -/

/-- The deduction theorem wrapped for the generic MCS framework.

`HasDeductionTheorem (@modalDerivationSystem Atom)` states that for any
`Γ`, `φ`, `ψ`, if `φ :: Γ ⊢ ψ` then `Γ ⊢ φ → ψ`. -/
theorem modal_has_deduction_theorem :
    Metalogic.HasDeductionTheorem (@modalDerivationSystem Atom) := by
  intro Γ φ ψ h
  unfold modalDerivationSystem Deriv at h ⊢
  simp at h ⊢
  obtain ⟨d⟩ := h
  exact ⟨deduction_theorem Γ φ ψ d⟩

end Cslib.Logic.Modal
