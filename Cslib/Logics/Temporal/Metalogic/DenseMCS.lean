/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Temporal.Metalogic.MCS

/-! # FC-Parameterized MCS Infrastructure for Temporal Logic

This module provides frame-class-parameterized versions of the temporal
derivability and MCS infrastructure. The base versions in `DerivationTree.lean`
and `MCS.lean` are hardcoded to `FrameClass.Base`. Here we define versions
parameterized by an arbitrary `fc : FrameClass`, enabling dense and discrete
completeness proofs.

## Main Definitions

- `Temporal.DerivFc`: Prop-valued derivability at frame class `fc`
- `Temporal.ThDerivableFc`: Theorem derivability at frame class `fc`
- `temporalDerivationSystemFc`: `DerivationSystem` instance at frame class `fc`
- `Temporal.SetConsistentFc`, `Temporal.SetMaximalConsistentFc`: FC-parameterized MCS

## Main Results

- `temporal_lindenbaum_fc`: Lindenbaum lemma at arbitrary frame class
- `temporal_has_deduction_theorem_fc`: Deduction theorem at arbitrary frame class
- `dense_mcs_implies_base_mcs`: Dense-MCS is also a Base-MCS
- `theoremInMcsFc`: Theorems at `fc` belong to every fc-MCS

## References

* `Cslib/Logics/Temporal/Metalogic/MCS.lean` — Base-specific versions
* `Cslib/Foundations/Logic/Metalogic/Consistency.lean` — generic MCS framework
-/

set_option linter.style.setOption false
set_option linter.dupNamespace false
set_option linter.flexible false
set_option maxHeartbeats 3200000

@[expose] public section

namespace Cslib.Logic.Temporal

open Cslib.Logic
open Cslib.Logic.Helpers

variable {Atom : Type*}

attribute [local instance] Classical.propDecidable

/-! ## FC-Parameterized Derivability -/

/-- Prop-valued derivability at frame class `fc`. -/
def Temporal.DerivFc (fc : FrameClass) (Gamma : List (Formula Atom))
    (phi : Formula Atom) : Prop :=
  Nonempty (DerivationTree fc Gamma phi)

/-- Theorem derivability at frame class `fc` (from empty context). -/
def Temporal.ThDerivableFc (fc : FrameClass) (phi : Formula Atom) : Prop :=
  Temporal.DerivFc fc [] phi

/-! ## Basic Combinators -/

theorem mp_deriv_fc {fc : FrameClass} {Γ : List (Formula Atom)}
    {φ ψ : Formula Atom}
    (h₁ : Temporal.DerivFc fc Γ (φ → ψ))
    (h₂ : Temporal.DerivFc fc Γ φ) :
    Temporal.DerivFc fc Γ ψ := by
  obtain ⟨d₁⟩ := h₁; obtain ⟨d₂⟩ := h₂
  exact ⟨.modus_ponens Γ φ ψ d₁ d₂⟩

theorem weakening_deriv_fc {fc : FrameClass} {Γ Δ : List (Formula Atom)}
    {φ : Formula Atom}
    (h : Temporal.DerivFc fc Γ φ) (hsub : ∀ x ∈ Γ, x ∈ Δ) :
    Temporal.DerivFc fc Δ φ := by
  obtain ⟨d⟩ := h
  exact ⟨.weakening Γ Δ φ d hsub⟩

theorem assumption_deriv_fc {fc : FrameClass} {Γ : List (Formula Atom)}
    {φ : Formula Atom}
    (h : φ ∈ Γ) : Temporal.DerivFc fc Γ φ :=
  ⟨.assumption Γ φ h⟩

/-! ## DerivationSystem Instance -/

/-- The temporal derivation system at frame class `fc`. -/
def temporalDerivationSystemFc (fc : FrameClass) :
    Metalogic.DerivationSystem (Formula Atom) where
  Deriv := Temporal.DerivFc fc
  weakening := fun hd hsub => weakening_deriv_fc hd hsub
  assumption := fun hmem => assumption_deriv_fc hmem
  mp := fun h₁ h₂ => mp_deriv_fc h₁ h₂

/-! ## FC-Parameterized MCS Abbreviations -/

/-- Set consistency at frame class `fc`. -/
abbrev Temporal.SetConsistentFc (fc : FrameClass)
    (Ω : Set (Formula Atom)) : Prop :=
  Metalogic.SetConsistent (temporalDerivationSystemFc fc) Ω

/-- Set maximal consistency at frame class `fc`. -/
abbrev Temporal.SetMaximalConsistentFc (fc : FrameClass)
    (Ω : Set (Formula Atom)) : Prop :=
  Metalogic.SetMaximalConsistent (temporalDerivationSystemFc fc) Ω

/-! ## FC-Parameterized Deduction Theorem Helpers

The deduction theorem at arbitrary fc works identically to the Base version.
All propositional axioms used (`imp_s`, `imp_k`) have `minFrameClass = .Base`,
and `Base <= fc` for any fc by `FrameClass.base_le`. -/

/-- Imp-K axiom tree at arbitrary fc. -/
noncomputable def impKFc (fc : FrameClass) (φ ψ : Formula Atom) :
    DerivationTree fc [] (φ.imp (ψ.imp φ)) :=
  .axiom [] _ (.imp_s φ ψ) (FrameClass.base_le fc)

/-- Imp-S axiom tree at arbitrary fc. -/
noncomputable def impSFc (fc : FrameClass) (φ ψ χ : Formula Atom) :
    DerivationTree fc []
      ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ))) :=
  .axiom [] _ (.imp_k φ ψ χ) (FrameClass.base_le fc)

/-- FC version of `deductionAxiom`. -/
noncomputable def deductionAxiomFc {fc : FrameClass}
    (Γ : Context Atom) (A : Formula Atom) {φ : Formula Atom}
    (d_empty : DerivationTree fc [] φ) :
    DerivationTree fc Γ (A.imp φ) :=
  let k := impKFc fc φ A
  let step := DerivationTree.modus_ponens [] φ (A.imp φ) k d_empty
  .weakening [] Γ _ step (fun _ h => nomatch h)

/-- FC version of `deductionImpSelf`. -/
noncomputable def deductionImpSelfFc {fc : FrameClass}
    (Γ : Context Atom) (A : Formula Atom) :
    DerivationTree fc Γ (A.imp A) :=
  let s := impSFc fc A (A.imp A) A
  let k1 := impKFc fc A (A.imp A)
  let k2 := impKFc fc A A
  let step1 := DerivationTree.modus_ponens [] _ _ s k1
  let result := DerivationTree.modus_ponens [] _ _ step1 k2
  .weakening [] Γ _ result (fun _ h => nomatch h)

/-- FC version of `deductionAssumptionOther`. -/
noncomputable def deductionAssumptionOtherFc {fc : FrameClass}
    (Γ : Context Atom) (A B : Formula Atom)
    (h_mem : B ∈ Γ) : DerivationTree fc Γ (A.imp B) :=
  let b_deriv := DerivationTree.assumption Γ B h_mem
  let k := impKFc fc B A
  let k_weak := DerivationTree.weakening [] Γ _ k (fun _ h => nomatch h)
  .modus_ponens Γ B (A.imp B) k_weak b_deriv

/-- FC version of `deductionMpUnderImp`. -/
noncomputable def deductionMpUnderImpFc {fc : FrameClass}
    (Γ : Context Atom) (A C D : Formula Atom)
    (d1 : DerivationTree fc Γ (A.imp (C.imp D)))
    (d2 : DerivationTree fc Γ (A.imp C)) :
    DerivationTree fc Γ (A.imp D) :=
  let s := impSFc fc A C D
  let s_weak := DerivationTree.weakening [] Γ _ s (fun _ h => nomatch h)
  let step := DerivationTree.modus_ponens Γ _ _ s_weak d1
  .modus_ponens Γ _ _ step d2

/-! ## FC-Parameterized Deduction Theorem -/

/-- FC version of `deductionWithMem`. -/
noncomputable def deductionWithMemFc {fc : FrameClass}
    (Γ' : Context Atom) (A φ : Formula Atom)
    (d : DerivationTree fc Γ' φ) (hA : A ∈ Γ') :
    DerivationTree fc (removeAll Γ' A) (A.imp φ) := by
  match d with
  | .axiom _ ψ h_ax h_fc =>
    exact deductionAxiomFc (removeAll Γ' A) A (.axiom [] ψ h_ax h_fc)
  | .assumption _ ψ h_mem =>
    by_cases h_eq : ψ = A
    · subst h_eq
      exact deductionImpSelfFc (removeAll Γ' ψ) ψ
    · have h_mem' : ψ ∈ removeAll Γ' A := mem_removeAll_of_mem_of_ne h_mem h_eq
      exact deductionAssumptionOtherFc (removeAll Γ' A) A ψ h_mem'
  | .modus_ponens _ ψ χ d₁ d₂ =>
    have ih₁ := deductionWithMemFc Γ' A (ψ.imp χ) d₁ hA
    have ih₂ := deductionWithMemFc Γ' A ψ d₂ hA
    exact deductionMpUnderImpFc (removeAll Γ' A) A ψ χ ih₁ ih₂
  | .temporal_necessitation ψ _d' =>
    simp at hA
  | .temporal_duality ψ _d' =>
    simp at hA
  | .weakening Γ'' _ ψ d' h_sub =>
    by_cases hA' : A ∈ Γ''
    · have ih := deductionWithMemFc Γ'' A ψ d' hA'
      exact .weakening (removeAll Γ'' A) (removeAll Γ' A) (A.imp ψ) ih
        (removeAll_sub_removeAll h_sub)
    · have h_sub' : Γ'' ⊆ removeAll Γ' A := by
        intro x hx
        exact mem_removeAll_of_mem_of_ne (h_sub hx) (fun h_eq => hA' (h_eq ▸ hx))
      have d_weak := DerivationTree.weakening Γ'' (removeAll Γ' A) ψ d' h_sub'
      have k_ax : DerivationTree fc [] (ψ.imp (A.imp ψ)) :=
        impKFc fc ψ A
      have k_weak := DerivationTree.weakening [] (removeAll Γ' A) _ k_ax
        (List.nil_subset _)
      exact .modus_ponens (removeAll Γ' A) ψ (A.imp ψ) k_weak d_weak
termination_by d.height
decreasing_by
  · exact DerivationTree.height_modus_ponens_left d₁ d₂
  · exact DerivationTree.height_modus_ponens_right d₁ d₂
  · exact DerivationTree.height_weakening d' h_sub

/-- **Deduction Theorem at arbitrary fc**: If `A :: Γ ⊢[fc] B` then `Γ ⊢[fc] A → B`. -/
noncomputable def deductionTheoremFc {fc : FrameClass}
    (Γ : Context Atom) (A B : Formula Atom)
    (d : DerivationTree fc (A :: Γ) B) :
    DerivationTree fc Γ (A.imp B) := by
  match d with
  | .axiom _ φ h_ax h_fc =>
    exact deductionAxiomFc Γ A (.axiom [] φ h_ax h_fc)
  | .assumption _ φ h_mem =>
    by_cases h_eq : φ = A
    · subst h_eq
      exact deductionImpSelfFc Γ φ
    · have h_tail : φ ∈ Γ := by
        cases h_mem with
        | head => exact absurd rfl h_eq
        | tail _ h => exact h
      exact deductionAssumptionOtherFc Γ A φ h_tail
  | .modus_ponens _ φ ψ d₁ d₂ =>
    have ih₁ := deductionTheoremFc Γ A (φ.imp ψ) d₁
    have ih₂ := deductionTheoremFc Γ A φ d₂
    exact deductionMpUnderImpFc Γ A φ ψ ih₁ ih₂
  | .weakening Γ' _ φ d' h_sub =>
    by_cases h_eq : Γ' = A :: Γ
    · exact deductionTheoremFc Γ A φ (h_eq ▸ d')
    · by_cases hA : A ∈ Γ'
      · have ih := deductionWithMemFc Γ' A φ d' hA
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
        have k_ax : DerivationTree (Atom := Atom) fc []
            (φ.imp (A.imp φ)) := impKFc fc φ A
        have k_weak := DerivationTree.weakening [] Γ _ k_ax (List.nil_subset _)
        exact .modus_ponens Γ φ (A.imp φ) k_weak d_weak
termination_by d.height
decreasing_by
  · exact DerivationTree.height_modus_ponens_left d₁ d₂
  · exact DerivationTree.height_modus_ponens_right d₁ d₂
  · have h1 : (h_eq ▸ d').height = d'.height := by subst h_eq; rfl
    simp [h1, DerivationTree.height]

/-! ## Deduction Theorem Wrapper -/

/-- The deduction theorem wrapped for the generic MCS framework at fc. -/
theorem temporal_has_deduction_theorem_fc (fc : FrameClass) :
    Metalogic.HasDeductionTheorem (temporalDerivationSystemFc (Atom := Atom) fc) := by
  intro Γ φ ψ h
  unfold temporalDerivationSystemFc Temporal.DerivFc at h ⊢
  simp at h ⊢
  obtain ⟨d⟩ := h
  exact ⟨deductionTheoremFc Γ φ ψ d⟩

/-! ## FC-Parameterized MCS Properties -/

/-- Lindenbaum lemma at frame class `fc`. -/
theorem temporal_lindenbaum_fc {fc : FrameClass} {Ω : Set (Formula Atom)}
    (hS : Temporal.SetConsistentFc fc Ω) :
    ∃ M : Set (Formula Atom), Ω ⊆ M ∧ Temporal.SetMaximalConsistentFc fc M :=
  Metalogic.set_lindenbaum (temporalDerivationSystemFc fc) hS

/-- Closed under derivation at fc. -/
theorem temporal_closed_under_derivation_fc
    {fc : FrameClass}
    {Ω : Set (Formula Atom)} (h_mcs : Temporal.SetMaximalConsistentFc fc Ω)
    {L : List (Formula Atom)} (h_sub : ∀ ψ ∈ L, ψ ∈ Ω)
    {φ : Formula Atom} (h_deriv : (temporalDerivationSystemFc fc).Deriv L φ) :
    φ ∈ Ω :=
  Metalogic.SetMaximalConsistent.closed_under_derivation
    (temporalDerivationSystemFc fc)
    (temporal_has_deduction_theorem_fc fc) h_mcs h_sub h_deriv

/-- Implication property at fc. -/
theorem temporal_implication_property_fc
    {fc : FrameClass}
    {Ω : Set (Formula Atom)} (h_mcs : Temporal.SetMaximalConsistentFc fc Ω)
    {φ ψ : Formula Atom} (h_imp : Formula.imp φ ψ ∈ Ω) (h_phi : φ ∈ Ω) :
    ψ ∈ Ω :=
  Metalogic.SetMaximalConsistent.implication_property
    (temporalDerivationSystemFc fc)
    (temporal_has_deduction_theorem_fc fc) h_mcs h_imp h_phi

/-- Negation completeness at fc. -/
theorem temporal_negation_complete_fc
    {fc : FrameClass}
    {Ω : Set (Formula Atom)} (h_mcs : Temporal.SetMaximalConsistentFc fc Ω)
    (φ : Formula Atom) : φ ∈ Ω ∨ Formula.neg φ ∈ Ω :=
  Metalogic.SetMaximalConsistent.negation_complete
    (temporalDerivationSystemFc fc)
    (temporal_has_deduction_theorem_fc fc) h_mcs φ

/-- Theorems at fc belong to every fc-MCS. -/
noncomputable def theoremInMcsFc {fc : FrameClass}
    {M : Set (Formula Atom)} {phi : Formula Atom}
    (h_mcs : Temporal.SetMaximalConsistentFc fc M)
    (h_deriv : DerivationTree fc [] phi) : phi ∈ M :=
  temporal_closed_under_derivation_fc h_mcs
    (L := []) (fun _ h => by simp at h)
    ⟨h_deriv⟩

/-! ## Negation Lemmas at fc -/

theorem mcs_bot_not_mem_fc
    {fc : FrameClass}
    {Ω : Set (Formula Atom)} (h_mcs : Temporal.SetMaximalConsistentFc fc Ω) :
    Formula.bot ∉ Ω := by
  intro h_bot
  exact h_mcs.1 [Formula.bot]
    (fun x hx => by simp [List.mem_cons] at hx; exact hx ▸ h_bot)
    (by simp [temporalDerivationSystemFc, Temporal.DerivFc]
        exact ⟨.assumption _ _ (List.mem_cons.mpr (Or.inl rfl))⟩)

theorem mcs_neg_of_not_mem_fc
    {fc : FrameClass}
    {Ω : Set (Formula Atom)} (h_mcs : Temporal.SetMaximalConsistentFc fc Ω)
    {φ : Formula Atom} (h_not : φ ∉ Ω) : Formula.neg φ ∈ Ω := by
  rcases temporal_negation_complete_fc h_mcs φ with h | h
  · exact absurd h h_not
  · exact h

theorem mcs_not_mem_of_neg_fc
    {fc : FrameClass}
    {Ω : Set (Formula Atom)} (h_mcs : Temporal.SetMaximalConsistentFc fc Ω)
    {φ : Formula Atom} (h_neg : Formula.neg φ ∈ Ω) : φ ∉ Ω := by
  intro h_phi
  exact mcs_bot_not_mem_fc h_mcs
    (temporal_implication_property_fc h_mcs h_neg h_phi)

/-- Consistency: phi and neg phi cannot both be in an fc-consistent set. -/
theorem set_consistent_fc_not_both
    {fc : FrameClass}
    {Ω : Set (Formula Atom)} (h_cons : Temporal.SetConsistentFc fc Ω)
    {φ : Formula Atom} (h_phi : φ ∈ Ω) (h_neg : Formula.neg φ ∈ Ω) : False := by
  apply h_cons [φ, Formula.neg φ]
  · intro x hx
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl <;> assumption
  · simp [temporalDerivationSystemFc, Temporal.DerivFc]
    exact ⟨.modus_ponens _ φ Formula.bot
      (.assumption _ (Formula.neg φ) (by simp))
      (.assumption _ φ (by simp))⟩

/-! ## Key Enabler: Dense-MCS implies Base-MCS -/

/-- A Dense-MCS is also a Base-MCS.

Proof: Dense-consistent implies Base-consistent (via frame class monotonicity:
every Base derivation lifts to Dense since `Base <= Dense`). Dense-MCS negation
completeness gives Base-maximality: if `φ ∉ M`, then `¬φ ∈ M` (Dense negation
complete), so `M ∪ {φ}` contains both `φ` and `¬φ` and is Base-inconsistent. -/
theorem dense_mcs_implies_base_mcs
    {M : Set (Formula Atom)}
    (h_mcs : Temporal.SetMaximalConsistentFc FrameClass.Dense M) :
    Temporal.SetMaximalConsistent M := by
  constructor
  · -- Dense-consistent => Base-consistent
    -- If M is Base-inconsistent, there exist L ⊆ M with L ⊢[Base] ⊥.
    -- Since Base <= Dense, L ⊢[Dense] ⊥ by lifting.
    -- This contradicts Dense-consistency of M.
    intro L hL hd
    apply h_mcs.1 L hL
    unfold temporalDerivationSystemFc Temporal.DerivFc
    unfold temporalDerivationSystem Temporal.Deriv at hd
    obtain ⟨d⟩ := hd
    exact ⟨d.lift (FrameClass.base_le .Dense)⟩
  · -- For Base-maximality: for all φ, either φ ∈ M or insert φ M is Base-inconsistent
    intro φ h_not_mem
    -- By Dense negation completeness, ¬φ ∈ M
    have h_neg := mcs_neg_of_not_mem_fc h_mcs h_not_mem
    -- Show ¬ SetConsistent temporalDerivationSystem (insert φ M)
    intro h_cons
    -- h_cons : ∀ L, (∀ x ∈ L, x ∈ insert φ M) → ¬ Temporal.Deriv L ⊥
    -- Contradiction: L = [φ, ¬φ] ⊆ insert φ M and [φ, ¬φ] ⊢[Base] ⊥
    apply h_cons [φ, Formula.neg φ]
    · intro x hx
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
      rcases hx with rfl | rfl
      · exact Set.mem_insert _ M
      · exact Set.mem_insert_of_mem _ h_neg
    · unfold temporalDerivationSystem Temporal.Deriv
      exact ⟨.modus_ponens _ φ Formula.bot
        (.assumption _ (Formula.neg φ) (by simp))
        (.assumption _ φ (by simp))⟩

end Cslib.Logic.Temporal
