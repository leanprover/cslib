/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Bimodal.Metalogic.Core.RestrictedMCS
public import Cslib.Logics.Bimodal.Metalogic.Core.MCSProperties
public import Cslib.Logics.Bimodal.Syntax.SubformulaClosure

/-!
# Closure MCS Infrastructure for FMP

This module provides the Maximal Consistent Set infrastructure restricted to
subformula closure, which is foundational for the Finite Model Property (FMP).

## Overview

For the FMP construction via filtration, we need MCS restricted to the subformula
closure of the target formula. This ensures:
1. The canonical model construction terminates
2. Equivalence classes are determined by finitely many formulas
3. The filtered model has bounded cardinality

## Main Definitions

- `ClosureMCS`: Re-export of `RestrictedMCS` specialized for FMP usage
- Projection theorems for full MCS to closure MCS
- Cardinality bounds

## References

- Ported from BimodalLogic/Theories/Bimodal/Metalogic/Decidability/FMP/ClosureMCS.lean
-/

set_option linter.style.emptyLine false

@[expose] public section

namespace Cslib.Logic.Bimodal.Metalogic.Decidability.FMP

open Cslib.Logic.Bimodal
open Cslib.Logic.Bimodal.Metalogic.Core

variable {Atom : Type*} [DecidableEq Atom]

/-!
## Core Closure MCS Definitions

We re-export and specialize the RestrictedMCS infrastructure for FMP usage.
-/

/--
A Closure MCS is a maximal consistent set restricted to the closure of a formula.
This is an alias for RestrictedMCS with explicit documentation for FMP context.

**Properties**:
- Closed under logical consequence within closure
- Negation complete for closure formulas
- Finite (bounded by 2 * |subformulaClosure phi|)
-/
abbrev ClosureMCS (phi : Formula Atom) (Omega : Set (Formula Atom)) : Prop :=
  RestrictedMCS phi Omega

/--
Closure consistency: a set is closure-consistent if it's a subset of
closureWithNeg and is set-consistent.
-/
abbrev ClosureConsistent (phi : Formula Atom) (Omega : Set (Formula Atom)) : Prop :=
  RestrictedConsistent phi Omega

/-!
## Projection from Full MCS to Closure MCS

Key theorem: any full MCS projected to the closure yields a closure MCS.
-/

/--
Project a set to the closure by intersection.
-/
def projectToClosure (phi : Formula Atom) (Omega : Set (Formula Atom)) :
    Set (Formula Atom) :=
  Omega ∩ (closureWithNeg phi : Set (Formula Atom))

/--
Projection to closure is closure-restricted.
-/
theorem projectToClosure_restricted (phi : Formula Atom) (Omega : Set (Formula Atom)) :
    ClosureRestricted phi (projectToClosure phi Omega) := by
  intro psi h
  exact Set.mem_of_mem_inter_right h

/--
Projection preserves consistency.
-/
theorem projectToClosure_preserves_consistency (phi : Formula Atom)
    (Omega : Set (Formula Atom))
    (h_cons : SetConsistent FrameClass.Base Omega) :
    SetConsistent FrameClass.Base (projectToClosure phi Omega) := by
  intro L hL
  apply h_cons L
  intro psi hpsi
  have := hL psi hpsi
  exact Set.mem_of_mem_inter_left this

/--
If Omega is a full SetMaximalConsistent set, then its projection to closure
is closure-consistent.
-/
theorem full_mcs_projection_consistent (phi : Formula Atom) (Omega : Set (Formula Atom))
    (h_mcs : SetMaximalConsistent FrameClass.Base Omega) :
    ClosureConsistent phi (projectToClosure phi Omega) :=
  ⟨projectToClosure_restricted phi Omega,
   projectToClosure_preserves_consistency phi Omega h_mcs.1⟩

/-!
## Key Properties for FMP

Properties that connect closure MCS to the filtration construction.
-/

/--
For any closure MCS and any formula psi in the subformula closure,
either psi or neg psi is in the MCS.

This is the negation completeness property essential for filtration.
-/
theorem closure_mcs_negation_complete {phi : Formula Atom}
    {Omega : Set (Formula Atom)}
    (h_mcs : ClosureMCS phi Omega) (psi : Formula Atom)
    (h_psi : psi ∈ subformulaClosure phi) :
    psi ∈ Omega ∨ psi.neg ∈ Omega :=
  restricted_mcs_negation_complete h_mcs psi h_psi

/--
A closure MCS contains either phi or neg phi.
-/
theorem closure_mcs_formula_decided {phi : Formula Atom}
    {Omega : Set (Formula Atom)}
    (h_mcs : ClosureMCS phi Omega) :
    phi ∈ Omega ∨ phi.neg ∈ Omega :=
  closure_mcs_negation_complete h_mcs phi (self_mem_subformulaClosure phi)

/--
A closure MCS is set-consistent.
-/
theorem closure_mcs_consistent {phi : Formula Atom}
    {Omega : Set (Formula Atom)}
    (h_mcs : ClosureMCS phi Omega) :
    SetConsistent FrameClass.Base Omega :=
  restricted_mcs_is_consistent h_mcs

/--
A closure MCS is bounded by the closure.
-/
theorem closure_mcs_bounded {phi : Formula Atom}
    {Omega : Set (Formula Atom)}
    (h_mcs : ClosureMCS phi Omega) :
    Omega ⊆ (closureWithNeg phi : Set (Formula Atom)) :=
  restricted_mcs_is_closure_restricted h_mcs

/-!
## Deductive Closure Property

Closure MCS is deductively closed for closure formulas.
-/

/--
If Γ ⊆ Omega and Γ ⊢ chi and chi ∈ closureWithNeg phi, then chi ∈ Omega.
-/
theorem closure_mcs_deductively_closed {phi : Formula Atom}
    {Omega : Set (Formula Atom)}
    (h_mcs : ClosureMCS phi Omega)
    {Γ : List (Formula Atom)} {chi : Formula Atom}
    (h_Γ_sub : ∀ ψ ∈ Γ, ψ ∈ Omega)
    (h_deriv : DerivationTree FrameClass.Base Γ chi)
    (h_chi_clos : chi ∈ closureWithNeg phi) :
    chi ∈ Omega := by
  by_contra h_chi_not
  -- By maximality, insert chi Omega is inconsistent
  have h_incons := h_mcs.2 chi h_chi_clos h_chi_not
  -- Show insert chi Omega is consistent, contradiction
  apply h_incons
  intro L hL ⟨d⟩
  -- d : DerivationTree FrameClass.Base L Formula.bot
  -- L ⊆ insert chi Omega
  let L' := L.filter (· ≠ chi)
  have hL'_in_Omega : ∀ ψ ∈ L', ψ ∈ Omega := by
    intro ψ hψ
    have hψ' := List.mem_filter.mp hψ
    have hψne : ψ ≠ chi := by simpa using hψ'.2
    specialize hL ψ hψ'.1
    cases Set.mem_insert_iff.mp hL with
    | inl h_eq => exact absurd h_eq hψne
    | inr h_in => exact h_in
  have hL_sub : L ⊆ chi :: L' := by
    intro ψ hψ
    by_cases h : ψ = chi
    · simp [h]
    · simp only [List.mem_cons]; right
      exact List.mem_filter.mpr ⟨hψ, by simpa⟩
  have d' : DerivationTree FrameClass.Base (chi :: L') Formula.bot :=
    DerivationTree.weakening L (chi :: L') Formula.bot d hL_sub
  have d_neg : DerivationTree FrameClass.Base L' chi.neg :=
    deductionTheorem L' chi Formula.bot d'
  -- Weaken Γ ⊢ chi to L' ++ Γ ⊢ chi
  have h_deriv' : DerivationTree FrameClass.Base (L' ++ Γ) chi :=
    DerivationTree.weakening Γ (L' ++ Γ) chi h_deriv
      (List.subset_append_right L' Γ)
  -- Weaken d_neg to L' ++ Γ
  have d_neg' : DerivationTree FrameClass.Base (L' ++ Γ) chi.neg :=
    DerivationTree.weakening L' (L' ++ Γ) chi.neg d_neg
      (List.subset_append_left L' Γ)
  -- Combine to get ⊥
  have d_bot : DerivationTree FrameClass.Base (L' ++ Γ) Formula.bot :=
    derivesBotFromPhiNegPhi h_deriv' d_neg'
  -- But L' ++ Γ ⊆ Omega, contradicting consistency
  have h_LΓ_in_Omega : ∀ ψ ∈ L' ++ Γ, ψ ∈ Omega := by
    intro ψ hψ
    simp only [List.mem_append] at hψ
    cases hψ with
    | inl h => exact hL'_in_Omega ψ h
    | inr h => exact h_Γ_sub ψ h
  exact h_mcs.1.2 (L' ++ Γ) h_LΓ_in_Omega ⟨d_bot⟩

/-!
## Constructing Closure MCS

Helper functions for constructing closure MCS containing specific formulas.
-/

/--
If phi is satisfiable (not a theorem that neg phi), then there exists a
closure MCS containing phi.
-/
theorem closure_mcs_exists_from_consistent_formula (phi : Formula Atom)
    (h_cons : ¬Nonempty (DerivationTree FrameClass.Base [] phi.neg)) :
    ∃ Omega : Set (Formula Atom), phi ∈ Omega ∧ ClosureMCS phi Omega :=
  restricted_mcs_from_formula phi h_cons

/--
For any formula in closureWithNeg phi that is consistent (singleton is consistent),
there exists a closure MCS containing it.
-/
theorem closure_mcs_exists_containing (phi psi : Formula Atom)
    (h_psi_clos : psi ∈ closureWithNeg phi)
    (h_cons : SetConsistent FrameClass.Base ({psi} : Set (Formula Atom))) :
    ∃ Omega : Set (Formula Atom), psi ∈ Omega ∧ ClosureMCS phi Omega :=
  restricted_mcs_exists_containing phi psi h_psi_clos h_cons

/--
Extend any closure-consistent set to a closure MCS.
-/
theorem closure_mcs_extension (phi : Formula Atom) (Omega : Set (Formula Atom))
    (h_restricted : ClosureRestricted phi Omega)
    (h_cons : SetConsistent FrameClass.Base Omega) :
    ∃ M : Set (Formula Atom), Omega ⊆ M ∧ ClosureMCS phi M :=
  restricted_lindenbaum phi Omega h_restricted h_cons

/-!
## Cardinality Bounds

The closure MCS has bounded cardinality.
-/

/--
Any closure MCS is bounded by closureWithNeg, which is finite.
-/
theorem closure_mcs_finite_bound {phi : Formula Atom}
    {Omega : Set (Formula Atom)}
    (h_mcs : ClosureMCS phi Omega) :
    Omega ⊆ (closureWithNeg phi : Set (Formula Atom)) :=
  closure_mcs_bounded h_mcs

/--
The cardinality bound for closure MCS.
Since Omega ⊆ closureWithNeg phi, we have |Omega| ≤ |closureWithNeg phi|.
And |closureWithNeg phi| ≤ 2 * |subformulaClosure phi|.
-/
theorem closure_mcs_card_bound (phi : Formula Atom) :
    (closureWithNeg phi).card ≤ 2 * (subformulaClosure phi).card := by
  unfold closureWithNeg
  calc (subformulaClosure phi ∪
      (subformulaClosure phi).image Formula.neg).card
      ≤ (subformulaClosure phi).card +
        ((subformulaClosure phi).image Formula.neg).card := by
        exact Finset.card_union_le _ _
    _ ≤ (subformulaClosure phi).card + (subformulaClosure phi).card := by
        apply Nat.add_le_add_left
        exact Finset.card_image_le
    _ = 2 * (subformulaClosure phi).card := by omega

end Cslib.Logic.Bimodal.Metalogic.Decidability.FMP
