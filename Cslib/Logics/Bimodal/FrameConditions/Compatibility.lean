/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module
public import Cslib.Logics.Bimodal.FrameConditions.Soundness
public import Cslib.Logics.Bimodal.ProofSystem.Axioms

/-!
# Axiom Compatibility Typeclasses

Typeclasses expressing which axioms are valid on which frame classes.
-/

set_option linter.style.emptyLine false
set_option linter.style.longLine false

@[expose] public section

namespace Cslib.Logic.Bimodal.FrameConditions

open Cslib.Logic.Bimodal

variable {Atom : Type*}

/-! ## Axiom Compatibility Typeclasses -/

/-- An axiom is linear-compatible if it is valid on all linear temporal frames. -/
class AxiomLinearCompatible {φ : Formula Atom} (ax : Axiom φ) : Prop where
  valid : ∀ (D : Type) [AddCommGroup D] [LinearOrder D] [IsOrderedAddMonoid D]
            [Nontrivial D] [LinearTemporalFrame D], validOver D φ

/-- An axiom is dense-compatible if it is valid on all dense temporal frames. -/
class AxiomDenseCompatible {φ : Formula Atom} (ax : Axiom φ) : Prop where
  valid : ∀ (D : Type) [AddCommGroup D] [LinearOrder D] [IsOrderedAddMonoid D]
            [Nontrivial D] [NoMaxOrder D] [NoMinOrder D] [DenselyOrdered D]
            [DenseTemporalFrame D], validOver D φ

/-- An axiom is discrete-compatible if it is valid on all discrete temporal frames. -/
class AxiomDiscreteCompatible {φ : Formula Atom} (ax : Axiom φ) : Prop where
  valid : ∀ (D : Type) [AddCommGroup D] [LinearOrder D] [IsOrderedAddMonoid D]
            [Nontrivial D] [NoMaxOrder D] [NoMinOrder D] [SuccOrder D] [PredOrder D] [IsSuccArchimedean D]
            [DiscreteTemporalFrame D], validOver D φ

/-! ## Monotonicity: Linear -> Dense/Discrete -/

instance {φ : Formula Atom} (ax : Axiom φ) [h : AxiomLinearCompatible ax] :
    AxiomDenseCompatible ax where
  valid := fun D _ _ _ _ _ _ _ _ => h.valid D

instance {φ : Formula Atom} (ax : Axiom φ) [h : AxiomLinearCompatible ax] :
    AxiomDiscreteCompatible ax where
  valid := fun D _ _ _ _ _ _ _ _ _ _ => h.valid D

/-! ## Base Axiom Instances -/

instance (φ ψ χ : Formula Atom) : AxiomLinearCompatible (Axiom.imp_k φ ψ χ) where
  valid := fun D _ _ _ _ _ => axiom_base_valid_linear (Axiom.imp_k φ ψ χ) (le_refl _) D

instance (φ ψ : Formula Atom) : AxiomLinearCompatible (Axiom.imp_s φ ψ) where
  valid := fun D _ _ _ _ _ => axiom_base_valid_linear (Axiom.imp_s φ ψ) (le_refl _) D

instance (φ : Formula Atom) : AxiomLinearCompatible (Axiom.modal_t φ) where
  valid := fun D _ _ _ _ _ => axiom_base_valid_linear (Axiom.modal_t φ) (le_refl _) D

instance (φ : Formula Atom) : AxiomLinearCompatible (Axiom.modal_4 φ) where
  valid := fun D _ _ _ _ _ => axiom_base_valid_linear (Axiom.modal_4 φ) (le_refl _) D

instance (φ : Formula Atom) : AxiomLinearCompatible (Axiom.modal_b φ) where
  valid := fun D _ _ _ _ _ => axiom_base_valid_linear (Axiom.modal_b φ) (le_refl _) D

instance (φ : Formula Atom) : AxiomLinearCompatible (Axiom.modal_5_collapse φ) where
  valid := fun D _ _ _ _ _ => axiom_base_valid_linear (Axiom.modal_5_collapse φ) (le_refl _) D

instance (φ : Formula Atom) : AxiomLinearCompatible (Axiom.efq φ) where
  valid := fun D _ _ _ _ _ => axiom_base_valid_linear (Axiom.efq φ) (le_refl _) D

instance (φ ψ : Formula Atom) : AxiomLinearCompatible (Axiom.peirce φ ψ) where
  valid := fun D _ _ _ _ _ => axiom_base_valid_linear (Axiom.peirce φ ψ) (le_refl _) D

instance (φ ψ : Formula Atom) : AxiomLinearCompatible (Axiom.modal_k_dist φ ψ) where
  valid := fun D _ _ _ _ _ => axiom_base_valid_linear (Axiom.modal_k_dist φ ψ) (le_refl _) D

instance : AxiomLinearCompatible (Axiom.serial_future (Atom := Atom)) where
  valid := fun D _ _ _ _ _ => axiom_base_valid_linear Axiom.serial_future (le_refl _) D

instance : AxiomLinearCompatible (Axiom.serial_past (Atom := Atom)) where
  valid := fun D _ _ _ _ _ => axiom_base_valid_linear Axiom.serial_past (le_refl _) D

instance (φ : Formula Atom) : AxiomLinearCompatible (Axiom.modal_future φ) where
  valid := fun D _ _ _ _ _ => axiom_base_valid_linear (Axiom.modal_future φ) (le_refl _) D

/-! ## Compatibility Theorems -/

/-- Any axiom whose minimum frame class is at most Base is linear-compatible. -/
theorem axiom_base_implies_linear_compatible {φ : Formula Atom} (ax : Axiom φ)
    (h : ax.minFrameClass ≤ FrameClass.Base) :
    AxiomLinearCompatible ax := by
  constructor
  intro D _ _ _ _ _
  exact axiom_base_valid_linear ax h D

end Cslib.Logic.Bimodal.FrameConditions
