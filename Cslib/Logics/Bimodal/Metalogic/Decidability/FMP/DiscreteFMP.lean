/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Bimodal.Metalogic.Decidability.FMP.FMP
public import Mathlib.Order.SuccPred.Basic

/-!
# Discrete FMP - Finite Model Property for Discrete Time

This module proves that the Finite Model Property holds for discrete temporal orders.

## Overview

For discretely ordered temporal types (e.g., `Int`, `Nat`), the FMP ensures that
satisfiable formulas have finite countermodels. Like the dense case, the MCS-based
filtration works regardless of the frame's discreteness property.

## Main Results

- `discrete_mcs_finite_model_property`: FMP for discrete frames
- `discrete_fmp_contrapositive`: Completeness via finite model for discrete frames

## References

- Blackburn, de Rijke, Venema: Modal Logic (Ch 2.3)
- Ported from BimodalLogic/Theories/Bimodal/Metalogic/Decidability/FMP/DiscreteFMP.lean
-/

@[expose] public section

namespace Cslib.Logic.Bimodal.Metalogic.Decidability.FMP

open Cslib.Logic.Bimodal
open Cslib.Logic.Bimodal.Metalogic.Core

variable {Atom : Type} [DecidableEq Atom]

/--
Discrete FMP: If φ is not provable, then there exists a finite model
(in the filtration sense) where φ fails.

This is the same as the base FMP - the discreteness condition on the temporal
order does not affect the MCS-based construction.
-/
theorem discrete_mcs_finite_model_property (phi : Formula Atom)
    (h_not_provable : ¬Nonempty (DerivationTree FrameClass.Base
      ([] : List (Formula Atom)) phi)) :
    ∃ (Omega : ClosureMCSBundle phi), phi ∉ Omega.carrier ∧
    Finite (FilteredWorld phi) :=
  mcs_finite_model_property phi h_not_provable

/--
Discrete FMP contrapositive: If φ holds in all closure MCS, then φ is provable.
-/
theorem discrete_fmp_contrapositive (phi : Formula Atom)
    (h_all_mcs : ∀ (Omega : ClosureMCSBundle phi), phi ∈ Omega.carrier) :
    Nonempty (DerivationTree FrameClass.Base ([] : List (Formula Atom)) phi) :=
  fmp_contrapositive phi h_all_mcs

/--
Record that filtered worlds exist and are finite for any formula,
regardless of whether we're considering dense or discrete frames.
-/
theorem filtered_model_exists_discrete (phi : Formula Atom) :
    Finite (FilteredWorld phi) :=
  FilteredWorld.finite phi

end Cslib.Logic.Bimodal.Metalogic.Decidability.FMP
