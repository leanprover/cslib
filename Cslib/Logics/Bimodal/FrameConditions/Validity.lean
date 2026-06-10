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
def validOver (D : Type) [AddCommGroup D] [LinearOrder D] [IsOrderedAddMonoid D]
    (φ : Formula Atom) : Prop :=
  ∀ (ℱ : TaskFrame D) (M : TaskModel Atom ℱ)
    (Omega : Set (WorldHistory ℱ)) (_ : ShiftClosed Omega)
    (τ : WorldHistory ℱ) (_ : τ ∈ Omega) (t : D),
    truthAt M Omega τ t φ

notation:50 "⊨[" D "] " φ:50 => validOver D φ

/-! ## Frame-Class Specific Validity -/

def validLinear (φ : Formula Atom) : Prop :=
  ∀ (D : Type) [AddCommGroup D] [LinearOrder D] [IsOrderedAddMonoid D]
    [Nontrivial D] [LinearTemporalFrame D], validOver D φ

def validDenseFc (φ : Formula Atom) : Prop :=
  ∀ (D : Type) [AddCommGroup D] [LinearOrder D] [IsOrderedAddMonoid D]
    [Nontrivial D] [NoMaxOrder D] [NoMinOrder D] [DenselyOrdered D]
    [DenseTemporalFrame D], validOver D φ

def validDiscreteFc (φ : Formula Atom) : Prop :=
  ∀ (D : Type) [AddCommGroup D] [LinearOrder D] [IsOrderedAddMonoid D]
    [Nontrivial D] [NoMaxOrder D] [NoMinOrder D] [SuccOrder D] [PredOrder D] [IsSuccArchimedean D]
    [DiscreteTemporalFrame D], validOver D φ

/-! ## Equivalence with Existing Definitions -/

theorem valid_of_forall_valid_over {φ : Formula Atom}
    (h : ∀ (D : Type) [AddCommGroup D] [LinearOrder D] [IsOrderedAddMonoid D], validOver D φ) :
    valid φ := by
  intro D _ _ _ _ ℱ M Omega h_sc τ h_mem t
  exact h D ℱ M Omega h_sc τ h_mem t

theorem valid_over_of_valid {D : Type} [AddCommGroup D] [LinearOrder D] [IsOrderedAddMonoid D]
    [Nontrivial D] {φ : Formula Atom} (h : valid φ) : validOver D φ := by
  intro ℱ M Omega h_sc τ h_mem t
  exact h D ℱ M Omega h_sc τ h_mem t

theorem valid_dense_of_valid_dense_fc {φ : Formula Atom} (h : validDenseFc φ) : validDense φ := by
  intro D _ _ _ _ _ ℱ M Omega h_sc τ h_mem t
  haveI : DenseTemporalFrame D := {}
  exact h D ℱ M Omega h_sc τ h_mem t

theorem valid_dense_fc_of_valid_dense {φ : Formula Atom} (h : validDense φ) : validDenseFc φ := by
  intro D _ _ _ _ _ _ _ _ ℱ M Omega h_sc τ h_mem t
  exact h D ℱ M Omega h_sc τ h_mem t

theorem valid_dense_fc_iff_valid_dense {φ : Formula Atom} :
    validDenseFc φ ↔ validDense φ :=
  ⟨valid_dense_of_valid_dense_fc, valid_dense_fc_of_valid_dense⟩

theorem valid_discrete_fc_of_valid_discrete {φ : Formula Atom} (h : validDiscrete φ) :
    validDiscreteFc φ := by
  intro D _ _ _ _ _ _ _ _ _ _ ℱ M Omega h_sc τ h_mem t
  exact h D ℱ M Omega h_sc τ h_mem t

/-! ## Relationship Between Frame Classes -/

theorem valid_linear_of_valid {φ : Formula Atom} (h : valid φ) : validLinear φ := by
  intro D _ _ _ _ _ ℱ M Omega h_sc τ h_mem t
  exact h D ℱ M Omega h_sc τ h_mem t

theorem valid_dense_fc_of_valid_linear {φ : Formula Atom} (h : validLinear φ) : validDenseFc φ := by
  intro D _ _ _ _ _ _ _ _ ℱ M Omega h_sc τ h_mem t
  haveI : LinearTemporalFrame D := {}
  exact h D ℱ M Omega h_sc τ h_mem t

theorem valid_discrete_fc_of_valid_linear {φ : Formula Atom} (h : validLinear φ) :
    validDiscreteFc φ := by
  intro D _ _ _ _ _ _ _ _ _ _ ℱ M Omega h_sc τ h_mem t
  haveI : LinearTemporalFrame D := {}
  exact h D ℱ M Omega h_sc τ h_mem t

/-! ## Validity over Int -/

abbrev validOverInt (φ : Formula Atom) : Prop := validOver Int φ

theorem valid_over_Int_of_valid_discrete {φ : Formula Atom} (h : validDiscrete φ) :
    validOverInt φ := by
  intro ℱ M Omega h_sc τ h_mem t
  exact h Int ℱ M Omega h_sc τ h_mem t

end Cslib.Logic.Bimodal.FrameConditions
