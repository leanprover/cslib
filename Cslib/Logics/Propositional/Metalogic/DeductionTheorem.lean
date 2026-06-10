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

- `deductionTheorem`: The core metatheorem, by well-founded recursion on derivation height.
- `deductionWithMem`: Helper for the weakening case where the deduction hypothesis
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

/-! ## Core: deductionWithMem -/

/-- The key helper for the weakening case: if `Γ' ⊢ φ` and `A ∈ Γ'`, then
`removeAll Γ' A ⊢ A → φ`.

This recurses on the derivation structure. All recursive calls are on derivations
with strictly smaller height, ensuring termination. -/
noncomputable def deductionWithMem
    (Γ' : List (PL.Proposition Atom)) (A φ : PL.Proposition Atom)
    (d : DerivationTree Γ' φ) (hA : A ∈ Γ') :
    DerivationTree (removeAll Γ' A) (A.imp φ) := by
  match d with
  | .ax _ ψ h_ax =>
    exact deductionAxiom (removeAll Γ' A) A (.ax [] ψ h_ax)
  | .assumption _ ψ h_mem =>
    by_cases h_eq : ψ = A
    · subst h_eq
      exact deductionImpSelf (removeAll Γ' ψ) ψ
    · have h_mem' : ψ ∈ removeAll Γ' A := mem_removeAll_of_mem_of_ne h_mem h_eq
      exact deductionAssumptionOther (removeAll Γ' A) A ψ h_mem'
  | .modus_ponens _ ψ χ d₁ d₂ =>
    have ih₁ := deductionWithMem Γ' A (ψ.imp χ) d₁ hA
    have ih₂ := deductionWithMem Γ' A ψ d₂ hA
    exact deductionMpUnderImp (removeAll Γ' A) A ψ χ ih₁ ih₂
  | .weakening Γ'' _ ψ d' h_sub =>
    by_cases hA' : A ∈ Γ''
    · have ih := deductionWithMem Γ'' A ψ d' hA'
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
  · exact DerivationTree.height_modus_ponens_left d₁ d₂
  · exact DerivationTree.height_modus_ponens_right d₁ d₂
  · exact DerivationTree.height_weakening d' h_sub

/-! ## Main Deduction Theorem -/

/-- **Deduction Theorem**: If `A :: Γ ⊢ B` then `Γ ⊢ A → B`.

Proof by well-founded recursion on derivation tree height. Handles all 4 constructors:
- `ax`: Use `implyK` to weaken the axiom under implication.
- `assumption` (same): Produce `A → A` via `deductionImpSelf`.
- `assumption` (other): Use `implyK` with the other assumption.
- `modus_ponens`: Recurse on both subderivations, combine via `implyS`.
- `weakening`: Three subcases -- context equality, `A ∈ Γ'` (uses `deductionWithMem`),
  or `A ∉ Γ'` (uses `implyK`). -/
noncomputable def deductionTheorem (Γ : List (PL.Proposition Atom)) (A B : PL.Proposition Atom)
    (d : DerivationTree (A :: Γ) B) :
    DerivationTree Γ (A.imp B) := by
  match d with
  | .ax _ φ h_ax =>
    exact deductionAxiom Γ A (.ax [] φ h_ax)
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
    have ih₁ := deductionTheorem Γ A (φ.imp ψ) d₁
    have ih₂ := deductionTheorem Γ A φ d₂
    exact deductionMpUnderImp Γ A φ ψ ih₁ ih₂
  | .weakening Γ' _ φ d' h_sub =>
    by_cases h_eq : Γ' = A :: Γ
    · exact deductionTheorem Γ A φ (h_eq ▸ d')
    · by_cases hA : A ∈ Γ'
      · have ih := deductionWithMem Γ' A φ d' hA
        have h_sub' : ∀ x ∈ removeAll Γ' A, x ∈ Γ :=
          removeAll_subset_of_subset h_sub hA
        exact .weakening (removeAll Γ' A) Γ (A.imp φ) ih h_sub'
      · have h_sub' : ∀ x ∈ Γ', x ∈ Γ := by
          intro x hx
          have := h_sub x hx
          simp only [List.mem_cons] at this
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
  · exact DerivationTree.height_modus_ponens_left d₁ d₂
  · exact DerivationTree.height_modus_ponens_right d₁ d₂
  · have : (h_eq ▸ d').height = d'.height := by subst h_eq; rfl
    simp only [this]
    exact DerivationTree.height_weakening d' h_sub

/-! ## HasDeductionTheorem Instance -/

/-- The deduction theorem wrapped for the generic MCS framework.

`HasDeductionTheorem (@propDerivationSystem Atom)` states that for any
`Γ`, `φ`, `ψ`, if `φ :: Γ ⊢ ψ` then `Γ ⊢ φ → ψ`. -/
theorem prop_has_deduction_theorem :
    Metalogic.HasDeductionTheorem (@propDerivationSystem Atom) := by
  intro Γ φ ψ h
  unfold propDerivationSystem Deriv at h ⊢
  simp only [] at h ⊢
  obtain ⟨d⟩ := h
  exact ⟨deductionTheorem Γ φ ψ d⟩

end Cslib.Logic.PL
