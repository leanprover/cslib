/-
Copyright (c) 2026 Benjamin Brastmckie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brastmckie
-/
import Cslib.Logics.Temporal.ProofSystem.Derivable
import Cslib.Foundations.Logic.ProofSystem

/-! # Instance Registration for Temporal.HilbertBX

This module registers `InferenceSystem`, `PropositionalHilbert`, `TemporalNecessitation`,
all 22 `HasAxiom*`, and `TemporalBXHilbert` instances for the `Temporal.HilbertBX` tag type,
connecting the abstract typeclass hierarchy to the concrete derivation tree.

## Architecture

The `InferenceSystem` instance maps `HilbertBX⇓φ` to `DerivationTree .Base [] φ`.
This makes `InferenceSystem.DerivableIn HilbertBX φ = Nonempty (DerivationTree .Base [] φ)`.

## Naming Note

BimodalLogic uses swapped names: `prop_k` = distribution (cslib's `ImplyS`),
`prop_s` = weakening (cslib's `ImplyK`). The instances below map correctly.
-/

-- Do not open Cslib.Logic.Temporal to avoid scoped notation conflicts
-- (F, G, H, P, S, U are all scoped notation for temporal operators)
open Cslib.Logic

variable {Atom : Type u}

section TempInstances

/-! ## InferenceSystem Instance -/

noncomputable instance : InferenceSystem Temporal.HilbertBX (Temporal.Formula Atom) where
  derivation φ := Temporal.DerivationTree Temporal.FrameClass.Base
    ([] : Temporal.Context Atom) φ

/-! ## ModusPonens Instance -/

noncomputable instance :
    ModusPonens Temporal.HilbertBX (F := Temporal.Formula Atom) where
  mp := fun h1 h2 => by
    obtain ⟨d1⟩ := h1; obtain ⟨d2⟩ := h2
    exact ⟨Temporal.DerivationTree.modus_ponens [] _ _ d1 d2⟩

/-! ## Propositional Axiom Instances -/

-- prop_s (weakening) -> cslib ImplyK, prop_k (distribution) -> cslib ImplyS
noncomputable instance :
    HasAxiomImplyK Temporal.HilbertBX (F := Temporal.Formula Atom) where
  implyK := ⟨Temporal.DerivationTree.axiom [] _ (Temporal.Axiom.imp_s _ _) trivial⟩

noncomputable instance :
    HasAxiomImplyS Temporal.HilbertBX (F := Temporal.Formula Atom) where
  implyS := ⟨Temporal.DerivationTree.axiom [] _ (Temporal.Axiom.imp_k _ _ _) trivial⟩

noncomputable instance :
    HasAxiomEFQ Temporal.HilbertBX (F := Temporal.Formula Atom) where
  efq := ⟨Temporal.DerivationTree.axiom [] _ (Temporal.Axiom.efq _) trivial⟩

noncomputable instance :
    HasAxiomPeirce Temporal.HilbertBX (F := Temporal.Formula Atom) where
  peirce := ⟨Temporal.DerivationTree.axiom [] _ (Temporal.Axiom.peirce _ _) trivial⟩

/-! ## PropositionalHilbert Instance -/

noncomputable instance :
    PropositionalHilbert Temporal.HilbertBX (F := Temporal.Formula Atom) where

/-! ## TemporalNecessitation Instance -/

noncomputable instance :
    TemporalNecessitation Temporal.HilbertBX (F := Temporal.Formula Atom) where
  tempNec := fun h => by
    obtain ⟨d⟩ := h
    exact ⟨Temporal.DerivationTree.temporal_necessitation _ d⟩

/-! ## Temporal Axiom Instances (22) -/

noncomputable instance :
    HasAxiomSerialFuture Temporal.HilbertBX (F := Temporal.Formula Atom) where
  serialFuture := ⟨Temporal.DerivationTree.axiom [] _ Temporal.Axiom.serial_future trivial⟩

noncomputable instance :
    HasAxiomSerialPast Temporal.HilbertBX (F := Temporal.Formula Atom) where
  serialPast := ⟨Temporal.DerivationTree.axiom [] _ Temporal.Axiom.serial_past trivial⟩

noncomputable instance :
    HasAxiomLeftMonoUntilG Temporal.HilbertBX (F := Temporal.Formula Atom) where
  leftMonoUntilG :=
    ⟨Temporal.DerivationTree.axiom [] _ (Temporal.Axiom.left_mono_until_G _ _ _) trivial⟩

noncomputable instance :
    HasAxiomLeftMonoSinceH Temporal.HilbertBX (F := Temporal.Formula Atom) where
  leftMonoSinceH :=
    ⟨Temporal.DerivationTree.axiom [] _ (Temporal.Axiom.left_mono_since_H _ _ _) trivial⟩

noncomputable instance :
    HasAxiomRightMonoUntil Temporal.HilbertBX (F := Temporal.Formula Atom) where
  rightMonoUntil :=
    ⟨Temporal.DerivationTree.axiom [] _ (Temporal.Axiom.right_mono_until _ _ _) trivial⟩

noncomputable instance :
    HasAxiomRightMonoSince Temporal.HilbertBX (F := Temporal.Formula Atom) where
  rightMonoSince :=
    ⟨Temporal.DerivationTree.axiom [] _ (Temporal.Axiom.right_mono_since _ _ _) trivial⟩

noncomputable instance :
    HasAxiomConnectFuture Temporal.HilbertBX (F := Temporal.Formula Atom) where
  connectFuture :=
    ⟨Temporal.DerivationTree.axiom [] _ (Temporal.Axiom.connect_future _) trivial⟩

noncomputable instance :
    HasAxiomConnectPast Temporal.HilbertBX (F := Temporal.Formula Atom) where
  connectPast :=
    ⟨Temporal.DerivationTree.axiom [] _ (Temporal.Axiom.connect_past _) trivial⟩

noncomputable instance :
    HasAxiomEnrichmentUntil Temporal.HilbertBX (F := Temporal.Formula Atom) where
  enrichmentUntil :=
    ⟨Temporal.DerivationTree.axiom [] _ (Temporal.Axiom.enrichment_until _ _ _) trivial⟩

noncomputable instance :
    HasAxiomEnrichmentSince Temporal.HilbertBX (F := Temporal.Formula Atom) where
  enrichmentSince :=
    ⟨Temporal.DerivationTree.axiom [] _ (Temporal.Axiom.enrichment_since _ _ _) trivial⟩

noncomputable instance :
    HasAxiomSelfAccumUntil Temporal.HilbertBX (F := Temporal.Formula Atom) where
  selfAccumUntil :=
    ⟨Temporal.DerivationTree.axiom [] _ (Temporal.Axiom.self_accum_until _ _) trivial⟩

noncomputable instance :
    HasAxiomSelfAccumSince Temporal.HilbertBX (F := Temporal.Formula Atom) where
  selfAccumSince :=
    ⟨Temporal.DerivationTree.axiom [] _ (Temporal.Axiom.self_accum_since _ _) trivial⟩

noncomputable instance :
    HasAxiomAbsorbUntil Temporal.HilbertBX (F := Temporal.Formula Atom) where
  absorbUntil :=
    ⟨Temporal.DerivationTree.axiom [] _ (Temporal.Axiom.absorb_until _ _) trivial⟩

noncomputable instance :
    HasAxiomAbsorbSince Temporal.HilbertBX (F := Temporal.Formula Atom) where
  absorbSince :=
    ⟨Temporal.DerivationTree.axiom [] _ (Temporal.Axiom.absorb_since _ _) trivial⟩

noncomputable instance :
    HasAxiomLinearUntil Temporal.HilbertBX (F := Temporal.Formula Atom) where
  linearUntil :=
    ⟨Temporal.DerivationTree.axiom [] _ (Temporal.Axiom.linear_until _ _ _ _) trivial⟩

noncomputable instance :
    HasAxiomLinearSince Temporal.HilbertBX (F := Temporal.Formula Atom) where
  linearSince :=
    ⟨Temporal.DerivationTree.axiom [] _ (Temporal.Axiom.linear_since _ _ _ _) trivial⟩

noncomputable instance :
    HasAxiomUntilF Temporal.HilbertBX (F := Temporal.Formula Atom) where
  untilF :=
    ⟨Temporal.DerivationTree.axiom [] _ (Temporal.Axiom.until_F _ _) trivial⟩

noncomputable instance :
    HasAxiomSinceP Temporal.HilbertBX (F := Temporal.Formula Atom) where
  sinceP :=
    ⟨Temporal.DerivationTree.axiom [] _ (Temporal.Axiom.since_P _ _) trivial⟩

noncomputable instance :
    HasAxiomTempLinearity Temporal.HilbertBX (F := Temporal.Formula Atom) where
  tempLinearity :=
    ⟨Temporal.DerivationTree.axiom [] _ (Temporal.Axiom.temp_linearity _ _) trivial⟩

noncomputable instance :
    HasAxiomTempLinearityPast Temporal.HilbertBX (F := Temporal.Formula Atom) where
  tempLinearityPast :=
    ⟨Temporal.DerivationTree.axiom [] _ (Temporal.Axiom.temp_linearity_past _ _) trivial⟩

noncomputable instance :
    HasAxiomFUntilEquiv Temporal.HilbertBX (F := Temporal.Formula Atom) where
  fUntilEquiv :=
    ⟨Temporal.DerivationTree.axiom [] _ (Temporal.Axiom.F_until_equiv _) trivial⟩

noncomputable instance :
    HasAxiomPSinceEquiv Temporal.HilbertBX (F := Temporal.Formula Atom) where
  pSinceEquiv :=
    ⟨Temporal.DerivationTree.axiom [] _ (Temporal.Axiom.P_since_equiv _) trivial⟩

/-! ## TemporalBXHilbert Instance -/

/-- The bundled `TemporalBXHilbert` instance for `Temporal.HilbertBX`. -/
noncomputable instance :
    TemporalBXHilbert Temporal.HilbertBX (F := Temporal.Formula Atom) where

end TempInstances
