/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module
public import Cslib.Logics.Bimodal.FrameConditions.Validity
public import Cslib.Logics.Bimodal.Metalogic.Soundness.Soundness

/-!
# Parameterized Soundness

Soundness theorems for the TM proof system using typeclass constraints.
-/

set_option linter.style.emptyLine false
set_option linter.style.longLine false

@[expose] public section

namespace Cslib.Logic.Bimodal.FrameConditions

open Cslib.Logic.Bimodal

variable {Atom : Type*}

/-! ## Parameterized Soundness -/

def soundnessOver (D : Type) [AddCommGroup D] [LinearOrder D] [IsOrderedAddMonoid D]
    [Nontrivial D] (Γ : Context Atom) (φ : Formula Atom)
    (d : DerivationTree FrameClass.Base Γ φ) :
    ∀ (ℱ : TaskFrame D) (M : TaskModel Atom ℱ)
      (Omega : Set (WorldHistory ℱ)) (_ : ShiftClosed Omega)
      (τ : WorldHistory ℱ) (_ : τ ∈ Omega) (t : D),
      (∀ ψ ∈ Γ, truthAt M Omega τ t ψ) → truthAt M Omega τ t φ :=
  fun ℱ M Omega h_sc τ h_mem t h_ctx =>
    Metalogic.soundness Γ φ d D ℱ M Omega h_sc τ h_mem t h_ctx

/-! ## Frame-Class Soundness Theorems -/

theorem soundness_linear {Γ : Context Atom} {φ : Formula Atom}
    (d : DerivationTree FrameClass.Base Γ φ)
    (D : Type) [AddCommGroup D] [LinearOrder D] [IsOrderedAddMonoid D]
    [Nontrivial D] [LinearTemporalFrame D] :
    ∀ (ℱ : TaskFrame D) (M : TaskModel Atom ℱ)
      (Omega : Set (WorldHistory ℱ)) (_ : ShiftClosed Omega)
      (τ : WorldHistory ℱ) (_ : τ ∈ Omega) (t : D),
      (∀ ψ ∈ Γ, truthAt M Omega τ t ψ) → truthAt M Omega τ t φ :=
  soundnessOver D Γ φ d

theorem soundness_dense_fc {Γ : Context Atom} {φ : Formula Atom}
    (d : DerivationTree FrameClass.Dense Γ φ)
    (D : Type) [AddCommGroup D] [LinearOrder D] [IsOrderedAddMonoid D]
    [Nontrivial D] [NoMaxOrder D] [NoMinOrder D] [DenselyOrdered D]
    [DenseTemporalFrame D] :
    ∀ (ℱ : TaskFrame D) (M : TaskModel Atom ℱ)
      (Omega : Set (WorldHistory ℱ)) (_ : ShiftClosed Omega)
      (τ : WorldHistory ℱ) (_ : τ ∈ Omega) (t : D),
      (∀ ψ ∈ Γ, truthAt M Omega τ t ψ) → truthAt M Omega τ t φ :=
  fun ℱ M Omega h_sc τ h_mem t h_ctx =>
    Metalogic.soundness_dense Γ φ d D ℱ M Omega h_sc τ h_mem t h_ctx

theorem soundness_discrete_fc {Γ : Context Atom} {φ : Formula Atom}
    (d : DerivationTree FrameClass.Discrete Γ φ)
    (D : Type) [AddCommGroup D] [LinearOrder D] [IsOrderedAddMonoid D]
    [Nontrivial D] [NoMaxOrder D] [NoMinOrder D] [SuccOrder D] [PredOrder D]
    [IsSuccArchimedean D] [IsPredArchimedean D]
    [DiscreteTemporalFrame D] :
    ∀ (ℱ : TaskFrame D) (M : TaskModel Atom ℱ)
      (Omega : Set (WorldHistory ℱ)) (_ : ShiftClosed Omega)
      (τ : WorldHistory ℱ) (_ : τ ∈ Omega) (t : D),
      (∀ ψ ∈ Γ, truthAt M Omega τ t ψ) → truthAt M Omega τ t φ :=
  fun ℱ M Omega h_sc τ h_mem t h_ctx =>
    Metalogic.soundness_discrete Γ φ d D ℱ M Omega h_sc τ h_mem t h_ctx

/-! ## Axiom Validity by Frame Class -/

theorem axiom_base_valid_linear {φ : Formula Atom} (ax : Axiom φ)
    (h_fc : ax.minFrameClass ≤ FrameClass.Base)
    (D : Type) [AddCommGroup D] [LinearOrder D] [IsOrderedAddMonoid D]
    [Nontrivial D] [LinearTemporalFrame D] :
    validOver D φ := by
  intro ℱ M Omega h_sc τ h_mem t
  exact Metalogic.axiom_valid ax h_fc D ℱ M Omega h_sc τ h_mem t

theorem axiom_dense_valid_fc {φ : Formula Atom} (ax : Axiom φ)
    (h_fc : ax.minFrameClass ≤ FrameClass.Dense)
    (D : Type) [AddCommGroup D] [LinearOrder D] [IsOrderedAddMonoid D]
    [Nontrivial D] [NoMaxOrder D] [NoMinOrder D] [DenselyOrdered D]
    [DenseTemporalFrame D] :
    validOver D φ := by
  intro ℱ M Omega h_sc τ h_mem t
  exact Metalogic.axiom_dense_valid ax h_fc D ℱ M Omega h_sc τ h_mem t

theorem axiom_discrete_valid_fc {φ : Formula Atom} (ax : Axiom φ)
    (h_fc : ax.minFrameClass ≤ FrameClass.Discrete)
    (D : Type) [AddCommGroup D] [LinearOrder D] [IsOrderedAddMonoid D]
    [Nontrivial D] [NoMaxOrder D] [NoMinOrder D] [SuccOrder D] [PredOrder D] [IsSuccArchimedean D]
    [DiscreteTemporalFrame D] :
    validOver D φ := by
  intro ℱ M Omega h_sc τ h_mem t
  exact Metalogic.axiom_discrete_valid ax h_fc D ℱ M Omega h_sc τ h_mem t

/-! ## Soundness over Int -/

theorem soundness_Int {Γ : Context Atom} {φ : Formula Atom}
    (d : DerivationTree FrameClass.Discrete Γ φ) :
    ∀ (ℱ : TaskFrame Int) (M : TaskModel Atom ℱ)
      (Omega : Set (WorldHistory ℱ)) (_ : ShiftClosed Omega)
      (τ : WorldHistory ℱ) (_ : τ ∈ Omega) (t : Int),
      (∀ ψ ∈ Γ, truthAt M Omega τ t ψ) → truthAt M Omega τ t φ :=
  fun ℱ M Omega h_sc τ h_mem t h_ctx =>
    Metalogic.soundness_discrete Γ φ d Int ℱ M Omega h_sc τ h_mem t h_ctx

end Cslib.Logic.Bimodal.FrameConditions
