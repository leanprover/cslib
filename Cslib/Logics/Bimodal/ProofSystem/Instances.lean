/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/
import Cslib.Logics.Bimodal.ProofSystem.Derivable
import Cslib.Foundations.Logic.ProofSystem

/-! # Instance Registration for Bimodal.HilbertTM

This module registers `InferenceSystem`, `PropositionalHilbert`,
`Necessitation`, `ModalS5Hilbert`, `TemporalNecessitation`,
all 22 `HasAxiom*`, `HasAxiomMF`, and `BimodalTMHilbert` instances
for the `Bimodal.HilbertTM` tag type, connecting the abstract typeclass
hierarchy to the concrete derivation tree.

## Architecture

The `InferenceSystem` instance maps `HilbertTM=>phi` to
`DerivationTree .Base [] phi`. This makes
`InferenceSystem.DerivableIn HilbertTM phi =
  Nonempty (DerivationTree .Base [] phi)`.

## Naming Note

BimodalLogic uses swapped names: `prop_k` = distribution (cslib's
`ImplyS`), `prop_s` = weakening (cslib's `ImplyK`). The instances
below map correctly.
-/

-- Do not open Cslib.Logic.Bimodal to avoid scoped notation conflicts
open Cslib.Logic

variable {Atom : Type u}

section BimodalInstances

/-! ## InferenceSystem Instance -/

instance : InferenceSystem Bimodal.HilbertTM
    (Bimodal.Formula Atom) where
  derivation phi := Bimodal.DerivationTree Bimodal.FrameClass.Base
    ([] : Bimodal.Context Atom) phi

/-! ## ModusPonens Instance -/

instance :
    ModusPonens Bimodal.HilbertTM
      (F := Bimodal.Formula Atom) where
  mp := fun h1 h2 => by
    obtain ⟨d1⟩ := h1; obtain ⟨d2⟩ := h2
    exact ⟨Bimodal.DerivationTree.modus_ponens
      [] _ _ d1 d2⟩

/-! ## Necessitation Instance (Modal Box) -/

instance :
    Necessitation Bimodal.HilbertTM
      (F := Bimodal.Formula Atom) where
  nec := fun h => by
    obtain ⟨d⟩ := h
    exact ⟨Bimodal.DerivationTree.necessitation _ d⟩

/-! ## Propositional Axiom Instances -/

-- prop_s (weakening) -> cslib ImplyK,
-- prop_k (distribution) -> cslib ImplyS
instance :
    HasAxiomImplyK Bimodal.HilbertTM
      (F := Bimodal.Formula Atom) where
  implyK := ⟨Bimodal.DerivationTree.axiom [] _
    (Bimodal.Axiom.imp_s _ _) trivial⟩

instance :
    HasAxiomImplyS Bimodal.HilbertTM
      (F := Bimodal.Formula Atom) where
  implyS := ⟨Bimodal.DerivationTree.axiom [] _
    (Bimodal.Axiom.imp_k _ _ _) trivial⟩

instance :
    HasAxiomEFQ Bimodal.HilbertTM
      (F := Bimodal.Formula Atom) where
  efq := ⟨Bimodal.DerivationTree.axiom [] _
    (Bimodal.Axiom.efq _) trivial⟩

instance :
    HasAxiomPeirce Bimodal.HilbertTM
      (F := Bimodal.Formula Atom) where
  peirce := ⟨Bimodal.DerivationTree.axiom [] _
    (Bimodal.Axiom.peirce _ _) trivial⟩

/-! ## PropositionalHilbert Instance -/

instance :
    PropositionalHilbert Bimodal.HilbertTM
      (F := Bimodal.Formula Atom) where

/-! ## Modal Axiom Instances -/

instance :
    HasAxiomK Bimodal.HilbertTM
      (F := Bimodal.Formula Atom) where
  K := ⟨Bimodal.DerivationTree.axiom [] _
    (Bimodal.Axiom.modal_k_dist _ _) trivial⟩

instance :
    HasAxiomT Bimodal.HilbertTM
      (F := Bimodal.Formula Atom) where
  T := ⟨Bimodal.DerivationTree.axiom [] _
    (Bimodal.Axiom.modal_t _) trivial⟩

instance :
    HasAxiom4 Bimodal.HilbertTM
      (F := Bimodal.Formula Atom) where
  four := ⟨Bimodal.DerivationTree.axiom [] _
    (Bimodal.Axiom.modal_4 _) trivial⟩

instance :
    HasAxiomB Bimodal.HilbertTM
      (F := Bimodal.Formula Atom) where
  B := ⟨Bimodal.DerivationTree.axiom [] _
    (Bimodal.Axiom.modal_b _) trivial⟩

/-! ## ModalHilbert and ModalS5Hilbert Instances -/

instance :
    ModalHilbert Bimodal.HilbertTM
      (F := Bimodal.Formula Atom) where

instance :
    ModalS5Hilbert Bimodal.HilbertTM
      (F := Bimodal.Formula Atom) where

/-! ## TemporalNecessitation Instance -/

instance :
    TemporalNecessitation Bimodal.HilbertTM
      (F := Bimodal.Formula Atom) where
  tempNec := fun h => by
    obtain ⟨d⟩ := h
    exact ⟨Bimodal.DerivationTree.temporal_necessitation
      _ d⟩
  tempNecPast := fun {phi}
      (h : InferenceSystem.DerivableIn
        Bimodal.HilbertTM phi) => by
    obtain ⟨d⟩ := h
    let d_swap :=
      Bimodal.DerivationTree.temporal_duality _ d
    let g_swap :=
      Bimodal.DerivationTree.temporal_necessitation
        _ d_swap
    let d_final :=
      Bimodal.DerivationTree.temporal_duality _ g_swap
    have h_eq :
        phi.swap_temporal.all_future.swap_temporal =
          phi.all_past := by
      simp only [Bimodal.Formula.all_past,
        Bimodal.Formula.some_past,
        Bimodal.Formula.neg,
        Bimodal.Formula.top,
        Bimodal.Formula.swap_temporal,
        Bimodal.Formula.swap_temporal_involution]
    exact ⟨InferenceSystem.rwConclusion h_eq d_final⟩

/-! ## Temporal Axiom Instances (22) -/

instance :
    HasAxiomSerialFuture Bimodal.HilbertTM
      (F := Bimodal.Formula Atom) where
  serialFuture := ⟨Bimodal.DerivationTree.axiom [] _
    Bimodal.Axiom.serial_future trivial⟩

instance :
    HasAxiomSerialPast Bimodal.HilbertTM
      (F := Bimodal.Formula Atom) where
  serialPast := ⟨Bimodal.DerivationTree.axiom [] _
    Bimodal.Axiom.serial_past trivial⟩

instance :
    HasAxiomLeftMonoUntilG Bimodal.HilbertTM
      (F := Bimodal.Formula Atom) where
  leftMonoUntilG := ⟨Bimodal.DerivationTree.axiom [] _
    (Bimodal.Axiom.left_mono_until_G _ _ _) trivial⟩

instance :
    HasAxiomLeftMonoSinceH Bimodal.HilbertTM
      (F := Bimodal.Formula Atom) where
  leftMonoSinceH := ⟨Bimodal.DerivationTree.axiom [] _
    (Bimodal.Axiom.left_mono_since_H _ _ _) trivial⟩

instance :
    HasAxiomRightMonoUntil Bimodal.HilbertTM
      (F := Bimodal.Formula Atom) where
  rightMonoUntil := ⟨Bimodal.DerivationTree.axiom [] _
    (Bimodal.Axiom.right_mono_until _ _ _) trivial⟩

instance :
    HasAxiomRightMonoSince Bimodal.HilbertTM
      (F := Bimodal.Formula Atom) where
  rightMonoSince := ⟨Bimodal.DerivationTree.axiom [] _
    (Bimodal.Axiom.right_mono_since _ _ _) trivial⟩

instance :
    HasAxiomConnectFuture Bimodal.HilbertTM
      (F := Bimodal.Formula Atom) where
  connectFuture := ⟨Bimodal.DerivationTree.axiom [] _
    (Bimodal.Axiom.connect_future _) trivial⟩

instance :
    HasAxiomConnectPast Bimodal.HilbertTM
      (F := Bimodal.Formula Atom) where
  connectPast := ⟨Bimodal.DerivationTree.axiom [] _
    (Bimodal.Axiom.connect_past _) trivial⟩

instance :
    HasAxiomEnrichmentUntil Bimodal.HilbertTM
      (F := Bimodal.Formula Atom) where
  enrichmentUntil := ⟨Bimodal.DerivationTree.axiom [] _
    (Bimodal.Axiom.enrichment_until _ _ _) trivial⟩

instance :
    HasAxiomEnrichmentSince Bimodal.HilbertTM
      (F := Bimodal.Formula Atom) where
  enrichmentSince := ⟨Bimodal.DerivationTree.axiom [] _
    (Bimodal.Axiom.enrichment_since _ _ _) trivial⟩

instance :
    HasAxiomSelfAccumUntil Bimodal.HilbertTM
      (F := Bimodal.Formula Atom) where
  selfAccumUntil := ⟨Bimodal.DerivationTree.axiom [] _
    (Bimodal.Axiom.self_accum_until _ _) trivial⟩

instance :
    HasAxiomSelfAccumSince Bimodal.HilbertTM
      (F := Bimodal.Formula Atom) where
  selfAccumSince := ⟨Bimodal.DerivationTree.axiom [] _
    (Bimodal.Axiom.self_accum_since _ _) trivial⟩

instance :
    HasAxiomAbsorbUntil Bimodal.HilbertTM
      (F := Bimodal.Formula Atom) where
  absorbUntil := ⟨Bimodal.DerivationTree.axiom [] _
    (Bimodal.Axiom.absorb_until _ _) trivial⟩

instance :
    HasAxiomAbsorbSince Bimodal.HilbertTM
      (F := Bimodal.Formula Atom) where
  absorbSince := ⟨Bimodal.DerivationTree.axiom [] _
    (Bimodal.Axiom.absorb_since _ _) trivial⟩

instance :
    HasAxiomLinearUntil Bimodal.HilbertTM
      (F := Bimodal.Formula Atom) where
  linearUntil := ⟨Bimodal.DerivationTree.axiom [] _
    (Bimodal.Axiom.linear_until _ _ _ _) trivial⟩

instance :
    HasAxiomLinearSince Bimodal.HilbertTM
      (F := Bimodal.Formula Atom) where
  linearSince := ⟨Bimodal.DerivationTree.axiom [] _
    (Bimodal.Axiom.linear_since _ _ _ _) trivial⟩

instance :
    HasAxiomUntilF Bimodal.HilbertTM
      (F := Bimodal.Formula Atom) where
  untilF := ⟨Bimodal.DerivationTree.axiom [] _
    (Bimodal.Axiom.until_F _ _) trivial⟩

instance :
    HasAxiomSinceP Bimodal.HilbertTM
      (F := Bimodal.Formula Atom) where
  sinceP := ⟨Bimodal.DerivationTree.axiom [] _
    (Bimodal.Axiom.since_P _ _) trivial⟩

instance :
    HasAxiomTempLinearity Bimodal.HilbertTM
      (F := Bimodal.Formula Atom) where
  tempLinearity := ⟨Bimodal.DerivationTree.axiom [] _
    (Bimodal.Axiom.temp_linearity _ _) trivial⟩

instance :
    HasAxiomTempLinearityPast Bimodal.HilbertTM
      (F := Bimodal.Formula Atom) where
  tempLinearityPast := ⟨Bimodal.DerivationTree.axiom [] _
    (Bimodal.Axiom.temp_linearity_past _ _) trivial⟩

instance :
    HasAxiomFUntilEquiv Bimodal.HilbertTM
      (F := Bimodal.Formula Atom) where
  fUntilEquiv := ⟨Bimodal.DerivationTree.axiom [] _
    (Bimodal.Axiom.F_until_equiv _) trivial⟩

instance :
    HasAxiomPSinceEquiv Bimodal.HilbertTM
      (F := Bimodal.Formula Atom) where
  pSinceEquiv := ⟨Bimodal.DerivationTree.axiom [] _
    (Bimodal.Axiom.P_since_equiv _) trivial⟩

/-! ## TemporalBXHilbert Instance -/

instance :
    TemporalBXHilbert Bimodal.HilbertTM
      (F := Bimodal.Formula Atom) where

/-! ## Modal-Future Interaction Instance -/

instance :
    HasAxiomMF Bimodal.HilbertTM
      (F := Bimodal.Formula Atom) where
  MF := ⟨Bimodal.DerivationTree.axiom [] _
    (Bimodal.Axiom.modal_future _) trivial⟩

/-! ## BimodalTMHilbert Instance -/

/-- The bundled `BimodalTMHilbert` instance for
    `Bimodal.HilbertTM`. -/
instance :
    BimodalTMHilbert Bimodal.HilbertTM
      (F := Bimodal.Formula Atom) where

end BimodalInstances
