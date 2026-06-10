/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Bimodal.Metalogic.Core.MaximalConsistent
public import Cslib.Logics.Bimodal.Metalogic.Core.MCSProperties
public import Cslib.Logics.Bimodal.Syntax.SubformulaClosure
public import Mathlib.Data.Finset.Basic
public import Mathlib.Order.Zorn

/-!
# Closure-Restricted Maximal Consistent Sets and Lindenbaum Construction

This module provides Maximal Consistent Set construction restricted to a finite
subformula closure. This is essential for the Finite Model Property proof
because it ensures the filtration quotient is finite.

## Overview

The key insight is that standard Lindenbaum's lemma produces MCS that may contain
arbitrary formulas. For FMP, we need MCS restricted to the subformula closure of
the target formula.

## Main Definitions

- `ClosureRestricted`: A set is closure-restricted if it's a subset of closureWithNeg
- `RestrictedConsistent`: Closure-restricted and set-consistent
- `RestrictedMCS`: Maximal consistent within closureWithNeg
- `restricted_lindenbaum`: Extends consistent closure-subset to closure-restricted MCS

## Key Properties

- `restricted_mcs_negation_complete`: For phi in closure, either phi or neg phi is in MCS
- `restricted_mcs_from_formula`: Constructs an MCS containing a consistent formula

## References

* Ported from BimodalLogic/Theories/Bimodal/Metalogic/Core/RestrictedMCS/Basic.lean
-/

set_option linter.style.emptyLine false

@[expose] public section

namespace Cslib.Logic.Bimodal.Metalogic.Core

open Cslib.Logic.Bimodal

/-!
## Closure-Restricted Consistency

Consistency restricted to formulas within the subformula closure.
-/

variable {Atom : Type*} [DecidableEq Atom]

variable (phi : Formula Atom)

/--
A set is closure-restricted if all its elements are in closureWithNeg phi.
-/
def ClosureRestricted (Omega : Set (Formula Atom)) : Prop :=
  Omega ⊆ (closureWithNeg phi : Set (Formula Atom))

/--
A closure-restricted set that is also set-consistent.
-/
def RestrictedConsistent (Omega : Set (Formula Atom)) : Prop :=
  ClosureRestricted phi Omega ∧ SetConsistent FrameClass.Base Omega

/--
Maximal consistent within the closure: cannot be extended within closure
while remaining consistent.
-/
def RestrictedMCS (Omega : Set (Formula Atom)) : Prop :=
  RestrictedConsistent phi Omega ∧
  ∀ psi ∈ closureWithNeg phi, psi ∉ Omega →
    ¬SetConsistent FrameClass.Base (insert psi Omega)

variable {phi : Formula Atom}

/-!
## Basic Properties
-/

/--
A restricted consistent set is closure-restricted.
-/
theorem restricted_consistent_is_restricted {Omega : Set (Formula Atom)}
    (h : RestrictedConsistent phi Omega) : ClosureRestricted phi Omega :=
  h.1

/--
A restricted consistent set is set-consistent.
-/
theorem restricted_consistent_is_consistent {Omega : Set (Formula Atom)}
    (h : RestrictedConsistent phi Omega) : SetConsistent FrameClass.Base Omega :=
  h.2

/--
A restricted MCS is restricted consistent.
-/
theorem restricted_mcs_is_restricted_consistent {Omega : Set (Formula Atom)}
    (h : RestrictedMCS phi Omega) : RestrictedConsistent phi Omega :=
  h.1

/--
A restricted MCS is set-consistent.
-/
theorem restricted_mcs_is_consistent {Omega : Set (Formula Atom)}
    (h : RestrictedMCS phi Omega) : SetConsistent FrameClass.Base Omega :=
  h.1.2

/--
A restricted MCS is closure-restricted.
-/
theorem restricted_mcs_is_closure_restricted {Omega : Set (Formula Atom)}
    (h : RestrictedMCS phi Omega) : ClosureRestricted phi Omega :=
  h.1.1

/-!
## Negation Completeness

For formulas in the subformula closure, restricted MCS has negation completeness.
-/

/--
For psi in subformulaClosure phi, either psi or psi.neg is in any restricted MCS.

**Proof Strategy**:
1. Both psi and psi.neg are in closureWithNeg phi
2. By maximality, at least one must be in Omega
3. If neither were in Omega, we could add either one, contradicting maximality
-/
theorem restricted_mcs_negation_complete {Omega : Set (Formula Atom)}
    (h_mcs : RestrictedMCS phi Omega) (psi : Formula Atom)
    (h_psi_clos : psi ∈ subformulaClosure phi) :
    psi ∈ Omega ∨ psi.neg ∈ Omega := by
  by_cases h : psi ∈ Omega
  · left; exact h
  · right
    -- psi ∈ subformulaClosure phi implies both psi and psi.neg in closureWithNeg phi
    have h_psi_closneg : psi ∈ closureWithNeg phi :=
      subformulaClosure_subset_closureWithNeg phi h_psi_clos
    have h_neg_closneg : psi.neg ∈ closureWithNeg phi :=
      neg_mem_closureWithNeg phi psi h_psi_clos
    -- By maximality: since psi ∉ Omega and psi ∈ closureWithNeg, insert psi Omega is inconsistent
    have h_incons := h_mcs.2 psi h_psi_closneg h
    -- Now we need to show psi.neg ∈ Omega
    by_contra h_neg_not
    -- From h_incons: ¬SetConsistent FrameClass.Base (insert psi Omega)
    unfold SetConsistent at h_incons
    push_neg at h_incons
    obtain ⟨L, h_L_sub, h_L_incons⟩ := h_incons
    -- L is inconsistent, so L ⊢ ⊥
    have h_bot : Nonempty (DerivationTree FrameClass.Base L Formula.bot) :=
      inconsistent_derives_bot h_L_incons
    obtain ⟨d_bot⟩ := h_bot
    -- Define Γ = L.filter (· ≠ psi)
    let Γ := L.filter (· ≠ psi)
    -- Show Γ ⊆ Omega
    have h_Γ_in_Omega : ∀ χ ∈ Γ, χ ∈ Omega := by
      intro χ hχ
      have hχ' := List.mem_filter.mp hχ
      have hχL := hχ'.1
      have hχne : χ ≠ psi := by simpa using hχ'.2
      specialize h_L_sub χ hχL
      simp [Set.mem_insert_iff] at h_L_sub
      rcases h_L_sub with rfl | h_in
      · exact absurd rfl hχne
      · exact h_in
    -- L ⊆ psi :: Γ
    have h_L_sub_psiGamma : L ⊆ psi :: Γ := by
      intro χ hχ
      by_cases hχpsi : χ = psi
      · simp [hχpsi]
      · simp only [List.mem_cons]
        right
        exact List.mem_filter.mpr ⟨hχ, by simpa⟩
    -- Weaken derivation from L to psi :: Γ
    have d_bot' : DerivationTree FrameClass.Base (psi :: Γ) Formula.bot :=
      DerivationTree.weakening L (psi :: Γ) Formula.bot d_bot h_L_sub_psiGamma
    -- By deduction theorem, Γ ⊢ psi.neg
    have d_neg : DerivationTree FrameClass.Base Γ psi.neg :=
      deductionTheorem Γ psi Formula.bot d_bot'
    -- Since psi.neg ∉ Omega and psi.neg ∈ closureWithNeg, by maximality
    -- insert psi.neg Omega is inconsistent
    have h_incons_neg := h_mcs.2 psi.neg h_neg_closneg h_neg_not
    -- So there exists L' ⊆ insert psi.neg Omega with ¬Consistent L'
    unfold SetConsistent at h_incons_neg
    push_neg at h_incons_neg
    obtain ⟨L', h_L'_sub, h_L'_incons⟩ := h_incons_neg
    -- L' is inconsistent, so L' ⊢ ⊥
    have h_bot'' : Nonempty (DerivationTree FrameClass.Base L' Formula.bot) :=
      inconsistent_derives_bot h_L'_incons
    obtain ⟨d_bot''⟩ := h_bot''
    -- Define Δ = L'.filter (· ≠ psi.neg)
    let Δ := L'.filter (· ≠ psi.neg)
    -- Show Δ ⊆ Omega
    have h_Δ_in_Omega : ∀ χ ∈ Δ, χ ∈ Omega := by
      intro χ hχ
      have hχ' := List.mem_filter.mp hχ
      have hχL' := hχ'.1
      have hχne : χ ≠ psi.neg := by simpa using hχ'.2
      specialize h_L'_sub χ hχL'
      simp [Set.mem_insert_iff] at h_L'_sub
      rcases h_L'_sub with rfl | h_in
      · exact absurd rfl hχne
      · exact h_in
    -- L' ⊆ psi.neg :: Δ
    have h_L'_sub_psiΔ : L' ⊆ psi.neg :: Δ := by
      intro χ hχ
      by_cases hχpsi : χ = psi.neg
      · simp [hχpsi]
      · simp only [List.mem_cons]
        right
        exact List.mem_filter.mpr ⟨hχ, by simpa⟩
    -- Weaken derivation from L' to psi.neg :: Δ
    have d_bot''' : DerivationTree FrameClass.Base (psi.neg :: Δ) Formula.bot :=
      DerivationTree.weakening L' (psi.neg :: Δ) Formula.bot d_bot'' h_L'_sub_psiΔ
    -- By deduction theorem, Δ ⊢ psi.neg.neg
    have d_neg_neg : DerivationTree FrameClass.Base Δ psi.neg.neg :=
      deductionTheorem Δ psi.neg Formula.bot d_bot'''
    -- Combine Γ and Δ
    let ΓΔ := Γ ++ Δ
    have h_ΓΔ_in_Omega : ∀ χ ∈ ΓΔ, χ ∈ Omega := by
      intro χ hχ
      simp only [ΓΔ, List.mem_append] at hχ
      rcases hχ with hχΓ | hχΔ
      · exact h_Γ_in_Omega χ hχΓ
      · exact h_Δ_in_Omega χ hχΔ
    -- Weaken both derivations to ΓΔ
    have d_neg' : DerivationTree FrameClass.Base ΓΔ psi.neg :=
      DerivationTree.weakening Γ ΓΔ _ d_neg (List.subset_append_left Γ Δ)
    have d_neg_neg' : DerivationTree FrameClass.Base ΓΔ psi.neg.neg :=
      DerivationTree.weakening Δ ΓΔ _ d_neg_neg (List.subset_append_right Γ Δ)
    -- Combine to get ⊥ from psi.neg and psi.neg.neg
    have d_bot_final : DerivationTree FrameClass.Base ΓΔ Formula.bot :=
      derivesBotFromPhiNegPhi d_neg' d_neg_neg'
    -- This contradicts consistency of Omega
    exact h_mcs.1.2 ΓΔ h_ΓΔ_in_Omega ⟨d_bot_final⟩

/-!
## Restricted Lindenbaum Construction

Extend a consistent set to a closure-restricted MCS.
-/

/--
The set of closure-restricted consistent extensions of a base set.
Used for Zorn's lemma application.
-/
def RestrictedConsistentSupersets (phi : Formula Atom)
    (Omega : Set (Formula Atom)) : Set (Set (Formula Atom)) :=
  {T | Omega ⊆ T ∧ RestrictedConsistent phi T}

/--
A restricted consistent set is in its own restricted consistent supersets.
-/
lemma self_mem_restricted_consistent_supersets {Omega : Set (Formula Atom)}
    (h : RestrictedConsistent phi Omega) :
    Omega ∈ RestrictedConsistentSupersets phi Omega :=
  ⟨Set.Subset.refl Omega, h⟩

/--
Chain union lemma: The union of a chain of restricted consistent sets is
restricted consistent.
-/
theorem restricted_consistent_chain_union {phi : Formula Atom}
    {C : Set (Set (Formula Atom))}
    (hchain : IsChain (· ⊆ ·) C) (hCne : C.Nonempty)
    (hcons : ∀ Theta ∈ C, RestrictedConsistent phi Theta) :
    RestrictedConsistent phi (⋃₀ C) := by
  constructor
  · -- Closure-restricted: ⋃₀ C ⊆ closureWithNeg phi
    intro psi h_mem
    obtain ⟨Theta, hTheta, hpsi⟩ := Set.mem_sUnion.mp h_mem
    exact (hcons Theta hTheta).1 hpsi
  · -- Set-consistent: use finite_list_in_chain_member
    intro L hL
    obtain ⟨Theta, hThetaC, hLTheta⟩ :=
      Metalogic.finite_list_in_chain_member hchain hCne L hL
    exact (hcons Theta hThetaC).2 L hLTheta

/--
Restricted Lindenbaum's Lemma: Every closure-restricted consistent set can be
extended to a closure-restricted maximal consistent set.

**Key Insight**: Since closureWithNeg phi is finite (it's a Finset), the extension
process terminates. This is the critical property that enables FMP construction.

**Proof Strategy**:
1. Apply Zorn's lemma to RestrictedConsistentSupersets
2. Chain union is restricted consistent (by restricted_consistent_chain_union)
3. Maximal element is a RestrictedMCS
-/
theorem restricted_lindenbaum (phi : Formula Atom) (Omega : Set (Formula Atom))
    (h_restricted : ClosureRestricted phi Omega)
    (h_cons : SetConsistent FrameClass.Base Omega) :
    ∃ M : Set (Formula Atom), Omega ⊆ M ∧ RestrictedMCS phi M := by
  -- Define the collection of restricted consistent supersets
  let RCS := RestrictedConsistentSupersets phi Omega
  -- Show RCS satisfies the chain condition for Zorn's lemma
  have hchain : ∀ C ⊆ RCS, IsChain (· ⊆ ·) C → C.Nonempty →
      ∃ ub ∈ RCS, ∀ T ∈ C, T ⊆ ub := by
    intro C hCsub hCchain hCne
    -- The upper bound is the union of the chain
    use ⋃₀ C
    constructor
    · -- Show ⋃₀ C ∈ RCS
      constructor
      · -- Omega ⊆ ⋃₀ C: Since C is nonempty, pick any T ∈ C, then Omega ⊆ T ⊆ ⋃₀ C
        obtain ⟨T, hT⟩ := hCne
        have hOmegaT : Omega ⊆ T := (hCsub hT).1
        exact Set.Subset.trans hOmegaT (Set.subset_sUnion_of_mem hT)
      · -- RestrictedConsistent phi (⋃₀ C)
        apply restricted_consistent_chain_union hCchain hCne
        intro T hT
        exact (hCsub hT).2
    · -- Show ∀ T ∈ C, T ⊆ ⋃₀ C
      intro T hT
      exact Set.subset_sUnion_of_mem hT
  -- Omega is restricted consistent
  have h_Omega_rc : RestrictedConsistent phi Omega := ⟨h_restricted, h_cons⟩
  -- Omega ∈ RCS
  have hOmegaMem : Omega ∈ RCS := self_mem_restricted_consistent_supersets h_Omega_rc
  -- Apply Zorn's lemma
  obtain ⟨M, hOmegaM, hmax⟩ := zorn_subset_nonempty RCS hchain Omega hOmegaMem
  -- hmax : Maximal (fun x => x ∈ RCS) M
  have hMmem : M ∈ RCS := hmax.prop
  obtain ⟨_, hMrc⟩ := hMmem
  -- M is maximal in RCS. Show it's RestrictedMCS.
  use M
  constructor
  · exact hOmegaM
  · -- Show RestrictedMCS phi M
    constructor
    · exact hMrc
    · -- Show ∀ psi ∈ closureWithNeg phi, psi ∉ M → ¬SetConsistent (insert psi M)
      intro psi h_psi_clos h_psi_not_M hcons_insert
      -- If insert psi M were consistent, then insert psi M ∈ RCS
      have h_insert_restricted : ClosureRestricted phi (insert psi M) := by
        intro chi h_mem
        cases Set.mem_insert_iff.mp h_mem with
        | inl h_eq => exact h_eq ▸ h_psi_clos
        | inr h_in_M => exact hMrc.1 h_in_M
      have h_insert_mem : insert psi M ∈ RCS := by
        constructor
        · exact Set.Subset.trans hOmegaM (Set.subset_insert psi M)
        · exact ⟨h_insert_restricted, hcons_insert⟩
      -- M is maximal: if insert psi M ∈ RCS and M ⊆ insert psi M, then
      -- insert psi M ⊆ M
      have h_le : M ⊆ insert psi M := Set.subset_insert psi M
      have h_subset : insert psi M ⊆ M := hmax.le_of_ge h_insert_mem h_le
      have h_psi_M : psi ∈ M := h_subset (Set.mem_insert psi M)
      exact h_psi_not_M h_psi_M

/-!
## Constructing Restricted MCS from a Formula

Helper functions for building restricted MCS containing specific formulas.
-/

/--
If psi is in closureWithNeg phi and {psi} is consistent, then we can extend
to a RestrictedMCS containing psi.
-/
theorem restricted_mcs_exists_containing (phi psi : Formula Atom)
    (h_psi_clos : psi ∈ closureWithNeg phi)
    (h_cons : SetConsistent FrameClass.Base ({psi} : Set (Formula Atom))) :
    ∃ M : Set (Formula Atom), psi ∈ M ∧ RestrictedMCS phi M := by
  -- {psi} is closure-restricted since psi ∈ closureWithNeg
  have h_restricted : ClosureRestricted phi ({psi} : Set (Formula Atom)) := by
    intro chi h_mem
    simp only [Set.mem_singleton_iff] at h_mem
    exact h_mem ▸ h_psi_clos
  -- Apply restricted Lindenbaum
  obtain ⟨M, hOmegaM, hMCS⟩ :=
    restricted_lindenbaum phi {psi} h_restricted h_cons
  use M
  exact ⟨hOmegaM (Set.mem_singleton psi), hMCS⟩

/--
If phi is consistent (not derivable from empty context), then we can construct
a RestrictedMCS containing phi.

This is the key entry point for FMP construction.
-/
theorem restricted_mcs_from_formula (phi : Formula Atom)
    (h_cons : ¬Nonempty (DerivationTree FrameClass.Base [] phi.neg)) :
    ∃ M : Set (Formula Atom), phi ∈ M ∧ RestrictedMCS phi M := by
  -- phi is in closureWithNeg phi
  have h_phi_clos : phi ∈ closureWithNeg phi := self_mem_closureWithNeg phi
  -- {phi} is consistent (follows from phi.neg not being a theorem)
  have h_singleton_cons :
      SetConsistent FrameClass.Base ({phi} : Set (Formula Atom)) := by
    intro L hL
    intro ⟨d⟩
    by_cases h_phi_in_L : phi ∈ L
    · -- Derive [phi] ⊢ ⊥ by weakening
      have h_weak : ∀ x ∈ L, x ∈ [phi] := by
        intro x hx
        have := hL x hx
        simp only [Set.mem_singleton_iff] at this
        simp [this]
      have d_phi : DerivationTree FrameClass.Base [phi] Formula.bot :=
        DerivationTree.weakening L [phi] _ d h_weak
      -- By deduction theorem: ⊢ phi → ⊥ = ⊢ phi.neg
      have d_neg : DerivationTree FrameClass.Base [] phi.neg :=
        deductionTheorem [] phi Formula.bot d_phi
      exact h_cons ⟨d_neg⟩
    · -- phi ∉ L, so L ⊆ {phi} means L = []
      have h_L_empty : L = [] := by
        cases L with
        | nil => rfl
        | cons x xs =>
          exfalso
          have hx := hL x List.mem_cons_self
          simp only [Set.mem_singleton_iff] at hx
          rw [hx] at h_phi_in_L
          exact h_phi_in_L List.mem_cons_self
      -- [] ⊢ ⊥ means bot is a theorem
      rw [h_L_empty] at d
      -- But ⊢ ⊥ implies ⊢ phi.neg (weakening)
      have d_neg : DerivationTree FrameClass.Base [] phi.neg := by
        have d_efq := DerivationTree.axiom (fc := FrameClass.Base)
          [] (Formula.bot.imp phi.neg) (Axiom.efq phi.neg) trivial
        exact DerivationTree.modus_ponens [] _ _ d_efq d
      exact h_cons ⟨d_neg⟩
  exact restricted_mcs_exists_containing phi phi h_phi_clos h_singleton_cons

end Cslib.Logic.Bimodal.Metalogic.Core
