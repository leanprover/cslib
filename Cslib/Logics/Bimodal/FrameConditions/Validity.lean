/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Bimodal.FrameConditions.FrameClass
public import Cslib.Logics.Bimodal.Semantics.Validity

/-!
# Parameterized Validity

Parameterized validity definitions for TM formulas across different frame classes.
-/

set_option linter.style.emptyLine false
set_option linter.style.longLine false

@[expose] public section

namespace Cslib.Logic.Bimodal.FrameConditions

open Cslib.Logic.Bimodal

variable {Atom : Type*}

/-! ## Parameterized Validity -/

/-- A formula is valid over temporal domain D. -/
def valid_over (D : Type) [AddCommGroup D] [LinearOrder D] [IsOrderedAddMonoid D]
    (φ : Formula Atom) : Prop :=
  ∀ (ℱ : TaskFrame D) (M : TaskModel Atom ℱ)
    (Omega : Set (WorldHistory ℱ)) (_ : ShiftClosed Omega)
    (τ : WorldHistory ℱ) (_ : τ ∈ Omega) (t : D),
    truth_at M Omega τ t φ

notation:50 "⊨[" D "] " φ:50 => valid_over D φ

/-! ## Frame-Class Specific Validity -/

def valid_linear (φ : Formula Atom) : Prop :=
  ∀ (D : Type) [AddCommGroup D] [LinearOrder D] [IsOrderedAddMonoid D]
    [Nontrivial D] [LinearTemporalFrame D], valid_over D φ

def valid_dense_fc (φ : Formula Atom) : Prop :=
  ∀ (D : Type) [AddCommGroup D] [LinearOrder D] [IsOrderedAddMonoid D]
    [Nontrivial D] [NoMaxOrder D] [NoMinOrder D] [DenselyOrdered D]
    [DenseTemporalFrame D], valid_over D φ

def valid_discrete_fc (φ : Formula Atom) : Prop :=
  ∀ (D : Type) [AddCommGroup D] [LinearOrder D] [IsOrderedAddMonoid D]
    [Nontrivial D] [NoMaxOrder D] [NoMinOrder D] [SuccOrder D] [PredOrder D] [IsSuccArchimedean D]
    [DiscreteTemporalFrame D], valid_over D φ

/-! ## Equivalence with Existing Definitions -/

theorem valid_of_forall_valid_over {φ : Formula Atom}
    (h : ∀ (D : Type) [AddCommGroup D] [LinearOrder D] [IsOrderedAddMonoid D], valid_over D φ) :
    valid φ := by
  intro D _ _ _ _ ℱ M Omega h_sc τ h_mem t
  exact h D ℱ M Omega h_sc τ h_mem t

theorem valid_over_of_valid {D : Type} [AddCommGroup D] [LinearOrder D] [IsOrderedAddMonoid D]
    [Nontrivial D] {φ : Formula Atom} (h : valid φ) : valid_over D φ := by
  intro ℱ M Omega h_sc τ h_mem t
  exact h D ℱ M Omega h_sc τ h_mem t

theorem valid_dense_of_valid_dense_fc {φ : Formula Atom} (h : valid_dense_fc φ) : valid_dense φ := by
  intro D _ _ _ _ _ ℱ M Omega h_sc τ h_mem t
  haveI : DenseTemporalFrame D := {}
  exact h D ℱ M Omega h_sc τ h_mem t

theorem valid_dense_fc_of_valid_dense {φ : Formula Atom} (h : valid_dense φ) : valid_dense_fc φ := by
  intro D _ _ _ _ _ _ _ _ ℱ M Omega h_sc τ h_mem t
  exact h D ℱ M Omega h_sc τ h_mem t

theorem valid_dense_fc_iff_valid_dense {φ : Formula Atom} :
    valid_dense_fc φ ↔ valid_dense φ :=
  ⟨valid_dense_of_valid_dense_fc, valid_dense_fc_of_valid_dense⟩

theorem valid_discrete_fc_of_valid_discrete {φ : Formula Atom} (h : valid_discrete φ) :
    valid_discrete_fc φ := by
  intro D _ _ _ _ _ _ _ _ _ _ ℱ M Omega h_sc τ h_mem t
  exact h D ℱ M Omega h_sc τ h_mem t

/-! ## Relationship Between Frame Classes -/

theorem valid_linear_of_valid {φ : Formula Atom} (h : valid φ) : valid_linear φ := by
  intro D _ _ _ _ _ ℱ M Omega h_sc τ h_mem t
  exact h D ℱ M Omega h_sc τ h_mem t

theorem valid_dense_fc_of_valid_linear {φ : Formula Atom} (h : valid_linear φ) : valid_dense_fc φ := by
  intro D _ _ _ _ _ _ _ _ ℱ M Omega h_sc τ h_mem t
  haveI : LinearTemporalFrame D := {}
  exact h D ℱ M Omega h_sc τ h_mem t

theorem valid_discrete_fc_of_valid_linear {φ : Formula Atom} (h : valid_linear φ) :
    valid_discrete_fc φ := by
  intro D _ _ _ _ _ _ _ _ _ _ ℱ M Omega h_sc τ h_mem t
  haveI : LinearTemporalFrame D := {}
  exact h D ℱ M Omega h_sc τ h_mem t

/-! ## Validity over Int -/

abbrev valid_over_Int (φ : Formula Atom) : Prop := valid_over Int φ

theorem valid_over_Int_of_valid_discrete {φ : Formula Atom} (h : valid_discrete φ) :
    valid_over_Int φ := by
  intro ℱ M Omega h_sc τ h_mem t
  exact h Int ℱ M Omega h_sc τ h_mem t

end Cslib.Logic.Bimodal.FrameConditions
