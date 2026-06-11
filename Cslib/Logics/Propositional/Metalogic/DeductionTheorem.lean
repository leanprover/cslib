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

/-- `HasHilbertTree` instance for propositional logic, fixed at `PropositionalAxiom`
for backward compatibility. Maps PL's `.implyK`/`.implyS` axiom constructors to the
generic typeclass fields. -/
noncomputable instance : HasHilbertTree (PL.Proposition Atom) where
  Tree := fun Γ φ => DerivationTree PropositionalAxiom Γ φ
  implyK := fun φ ψ => .ax [] _ (.implyK φ ψ)
  implyS := fun φ ψ χ => .ax [] _ (.implyS φ ψ χ)
  assumption := fun h => .assumption _ _ h
  mp := fun d₁ d₂ => .modus_ponens _ _ _ d₁ d₂
  weakening := fun d h => .weakening _ _ _ d h

/-! ## Core: deductionWithMem -/

/-- The key helper for the weakening case: if `Γ' ⊢ φ` and `A ∈ Γ'`, then
`removeAll Γ' A ⊢ A → φ`.

Parameterized over `Axioms` with explicit proofs that `Axioms` includes implyK
and implyS. -/
noncomputable def deductionWithMem
    {Axioms : PL.Proposition Atom → Prop}
    (h_implyK : ∀ (φ ψ : PL.Proposition Atom), Axioms (φ.imp (ψ.imp φ)))
    (h_implyS : ∀ (φ ψ χ : PL.Proposition Atom),
      Axioms ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ))))
    (Γ' : List (PL.Proposition Atom)) (A φ : PL.Proposition Atom)
    (d : DerivationTree Axioms Γ' φ) (hA : A ∈ Γ') :
    DerivationTree Axioms (removeAll Γ' A) (A.imp φ) := by
  -- Build the HasHilbertTree instance for Axioms to use generic helpers
  letI : HasHilbertTree (PL.Proposition Atom) := {
    Tree := fun Γ φ => DerivationTree Axioms Γ φ
    implyK := fun φ ψ => .ax [] _ (h_implyK φ ψ)
    implyS := fun φ ψ χ => .ax [] _ (h_implyS φ ψ χ)
    assumption := fun h => .assumption _ _ h
    mp := fun d₁ d₂ => .modus_ponens _ _ _ d₁ d₂
    weakening := fun d h => .weakening _ _ _ d h
  }
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
    have ih₁ := deductionWithMem h_implyK h_implyS Γ' A (ψ.imp χ) d₁ hA
    have ih₂ := deductionWithMem h_implyK h_implyS Γ' A ψ d₂ hA
    exact deductionMpUnderImp (removeAll Γ' A) A ψ χ ih₁ ih₂
  | .weakening Γ'' _ ψ d' h_sub =>
    by_cases hA' : A ∈ Γ''
    · have ih := deductionWithMem h_implyK h_implyS Γ'' A ψ d' hA'
      have h_sub' : ∀ x ∈ removeAll Γ'' A, x ∈ removeAll Γ' A :=
        removeAll_subset_removeAll h_sub
      exact .weakening (removeAll Γ'' A) (removeAll Γ' A) (A.imp ψ) ih h_sub'
    · have h_sub' : ∀ x ∈ Γ'', x ∈ removeAll Γ' A := by
        intro x hx
        exact mem_removeAll_of_mem_of_ne (h_sub x hx) (fun h_eq => hA' (h_eq ▸ hx))
      have d_weak := DerivationTree.weakening Γ'' (removeAll Γ' A) ψ d' h_sub'
      have k_ax : DerivationTree Axioms [] (ψ.imp (A.imp ψ)) :=
        .ax [] _ (h_implyK ψ A)
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

Parameterized over `Axioms` with explicit proofs that `Axioms` includes
implyK and implyS. -/
noncomputable def deductionTheorem
    {Axioms : PL.Proposition Atom → Prop}
    (h_implyK : ∀ (φ ψ : PL.Proposition Atom), Axioms (φ.imp (ψ.imp φ)))
    (h_implyS : ∀ (φ ψ χ : PL.Proposition Atom),
      Axioms ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ))))
    (Γ : List (PL.Proposition Atom)) (A B : PL.Proposition Atom)
    (d : DerivationTree Axioms (A :: Γ) B) :
    DerivationTree Axioms Γ (A.imp B) := by
  -- Build the HasHilbertTree instance for Axioms to use generic helpers
  letI : HasHilbertTree (PL.Proposition Atom) := {
    Tree := fun Γ φ => DerivationTree Axioms Γ φ
    implyK := fun φ ψ => .ax [] _ (h_implyK φ ψ)
    implyS := fun φ ψ χ => .ax [] _ (h_implyS φ ψ χ)
    assumption := fun h => .assumption _ _ h
    mp := fun d₁ d₂ => .modus_ponens _ _ _ d₁ d₂
    weakening := fun d h => .weakening _ _ _ d h
  }
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
    have ih₁ := deductionTheorem h_implyK h_implyS Γ A (φ.imp ψ) d₁
    have ih₂ := deductionTheorem h_implyK h_implyS Γ A φ d₂
    exact deductionMpUnderImp Γ A φ ψ ih₁ ih₂
  | .weakening Γ' _ φ d' h_sub =>
    by_cases h_eq : Γ' = A :: Γ
    · exact deductionTheorem h_implyK h_implyS Γ A φ (h_eq ▸ d')
    · by_cases hA : A ∈ Γ'
      · have ih := deductionWithMem h_implyK h_implyS Γ' A φ d' hA
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
        have k_ax : DerivationTree Axioms (Atom := Atom) [] (φ.imp (A.imp φ)) :=
          .ax [] _ (h_implyK φ A)
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

Parameterized over `Axioms` with explicit proofs that `Axioms` includes
implyK and implyS. -/
theorem prop_has_deduction_theorem
    {Axioms : PL.Proposition Atom → Prop}
    (h_implyK : ∀ (φ ψ : PL.Proposition Atom), Axioms (φ.imp (ψ.imp φ)))
    (h_implyS : ∀ (φ ψ χ : PL.Proposition Atom),
      Axioms ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ)))) :
    Metalogic.HasDeductionTheorem (propDerivationSystem Axioms) := by
  intro Γ φ ψ h
  unfold propDerivationSystem Deriv at h ⊢
  simp only [] at h ⊢
  obtain ⟨d⟩ := h
  exact ⟨deductionTheorem h_implyK h_implyS Γ φ ψ d⟩

/-! ## Classical backward-compatible wrapper -/

/-- Classical deduction theorem: the deduction theorem for the classical axiom set. -/
theorem cl_prop_has_deduction_theorem :
    Metalogic.HasDeductionTheorem (propDerivationSystem (@PropositionalAxiom Atom)) :=
  prop_has_deduction_theorem
    (fun φ ψ => .implyK φ ψ)
    (fun φ ψ χ => .implyS φ ψ χ)

end Cslib.Logic.PL
