/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Propositional.ProofSystem.Derivation
public import Cslib.Foundations.Data.ListHelpers
public import Cslib.Foundations.Logic.Metalogic.DeductionHelpers

/-! # Deduction Theorem for Propositional Logic

This module proves the deduction theorem for the propositional Hilbert system:
if `A :: Γ ⊢ B` then `Γ ⊢ A → B`.

## Main Results

- `deduction_theorem`: The core metatheorem, by well-founded recursion on derivation height.
- `deduction_with_mem`: Helper for the weakening case where the deduction hypothesis
  appears in the middle of the context.
- `prop_has_deduction_theorem`: The `HasDeductionTheorem` instance for the generic MCS
  framework.

## Implementation

The proof follows the Modal pattern with well-founded recursion on
`DerivationTree.height`. The propositional version is simpler than the modal one
because there are only 4 constructors (no necessitation), eliminating the impossible
empty-context case entirely.

## References

* Cslib/Logics/Modal/Metalogic/DeductionTheorem.lean -- modal deduction theorem
* Cslib/Foundations/Logic/Metalogic/Consistency.lean
-/

@[expose] public section

namespace Cslib.Logic.PL

open Cslib.Logic
open Cslib.Logic.Helpers

variable {Atom : Type*}

attribute [local instance] Classical.propDecidable

/-! ## HasHilbertTree Instance -/

/-- `HasHilbertTree` instance for propositional logic. Maps PL's `.implyK`/`.implyS`
axiom constructors to the generic typeclass fields. -/
noncomputable instance : HasHilbertTree (PL.Proposition Atom) where
  Tree := fun Γ φ => DerivationTree Γ φ
  implyK := fun φ ψ => .ax [] _ (.implyK φ ψ)
  implyS := fun φ ψ χ => .ax [] _ (.implyS φ ψ χ)
  assumption := fun h => .assumption _ _ h
  mp := fun d₁ d₂ => .modus_ponens _ _ _ d₁ d₂
  weakening := fun d h => .weakening _ _ _ d h

/-! ## Core: deduction_with_mem -/

/-- The key helper for the weakening case: if `Γ' ⊢ φ` and `A ∈ Γ'`, then
`removeAll Γ' A ⊢ A → φ`.

This recurses on the derivation structure. All recursive calls are on derivations
with strictly smaller height, ensuring termination. -/
noncomputable def deduction_with_mem
    (Γ' : List (PL.Proposition Atom)) (A φ : PL.Proposition Atom)
    (d : DerivationTree Γ' φ) (hA : A ∈ Γ') :
    DerivationTree (removeAll Γ' A) (A.imp φ) := by
  match d with
  | .ax _ ψ h_ax =>
    exact deduction_axiom (removeAll Γ' A) A (.ax [] ψ h_ax)
  | .assumption _ ψ h_mem =>
    by_cases h_eq : ψ = A
    · subst h_eq
      exact deduction_imp_self (removeAll Γ' ψ) ψ
    · have h_mem' : ψ ∈ removeAll Γ' A := mem_removeAll_of_mem_of_ne h_mem h_eq
      exact deduction_assumption_other (removeAll Γ' A) A ψ h_mem'
  | .modus_ponens _ ψ χ d₁ d₂ =>
    have ih₁ := deduction_with_mem Γ' A (ψ.imp χ) d₁ hA
    have ih₂ := deduction_with_mem Γ' A ψ d₂ hA
    exact deduction_mp_under_imp (removeAll Γ' A) A ψ χ ih₁ ih₂
  | .weakening Γ'' _ ψ d' h_sub =>
    by_cases hA' : A ∈ Γ''
    · have ih := deduction_with_mem Γ'' A ψ d' hA'
      have h_sub' : ∀ x ∈ removeAll Γ'' A, x ∈ removeAll Γ' A :=
        removeAll_subset_removeAll h_sub
      exact .weakening (removeAll Γ'' A) (removeAll Γ' A) (A.imp ψ) ih h_sub'
    · have h_sub' : ∀ x ∈ Γ'', x ∈ removeAll Γ' A := by
        intro x hx
        exact mem_removeAll_of_mem_of_ne (h_sub x hx) (fun h_eq => hA' (h_eq ▸ hx))
      have d_weak := DerivationTree.weakening Γ'' (removeAll Γ' A) ψ d' h_sub'
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

Proof by well-founded recursion on derivation tree height. Handles all 4 constructors:
- `ax`: Use `implyK` to weaken the axiom under implication.
- `assumption` (same): Produce `A → A` via `deduction_imp_self`.
- `assumption` (other): Use `implyK` with the other assumption.
- `modus_ponens`: Recurse on both subderivations, combine via `implyS`.
- `weakening`: Three subcases -- context equality, `A ∈ Γ'` (uses `deduction_with_mem`),
  or `A ∉ Γ'` (uses `implyK`). -/
noncomputable def deduction_theorem (Γ : List (PL.Proposition Atom)) (A B : PL.Proposition Atom)
    (d : DerivationTree (A :: Γ) B) :
    DerivationTree Γ (A.imp B) := by
  match d with
  | .ax _ φ h_ax =>
    exact deduction_axiom Γ A (.ax [] φ h_ax)
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
    exact deduction_mp_under_imp Γ A φ ψ ih₁ ih₂
  | .weakening Γ' _ φ d' h_sub =>
    by_cases h_eq : Γ' = A :: Γ
    · exact deduction_theorem Γ A φ (h_eq ▸ d')
    · by_cases hA : A ∈ Γ'
      · have ih := deduction_with_mem Γ' A φ d' hA
        have h_sub' : ∀ x ∈ removeAll Γ' A, x ∈ Γ :=
          removeAll_subset_of_subset h_sub hA
        exact .weakening (removeAll Γ' A) Γ (A.imp φ) ih h_sub'
      · have h_sub' : ∀ x ∈ Γ', x ∈ Γ := by
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

`HasDeductionTheorem (@propDerivationSystem Atom)` states that for any
`Γ`, `φ`, `ψ`, if `φ :: Γ ⊢ ψ` then `Γ ⊢ φ → ψ`. -/
theorem prop_has_deduction_theorem :
    Metalogic.HasDeductionTheorem (@propDerivationSystem Atom) := by
  intro Γ φ ψ h
  unfold propDerivationSystem Deriv at h ⊢
  simp at h ⊢
  obtain ⟨d⟩ := h
  exact ⟨deduction_theorem Γ φ ψ d⟩

end Cslib.Logic.PL
