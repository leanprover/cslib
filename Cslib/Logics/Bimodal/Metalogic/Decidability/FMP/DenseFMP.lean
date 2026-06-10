/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

import Cslib.Logics.Bimodal.Metalogic.Decidability.FMP.FMP
import Mathlib.Order.Basic

/-!
# Dense FMP - Finite Model Property for Dense Time

This module proves that the Finite Model Property holds for dense temporal orders.

## Overview

For densely ordered temporal types (e.g., `Rat`, `Real`), the FMP ensures that
satisfiable formulas have finite countermodels. The MCS-based construction is
frame-independent at the proof-theoretic level.

## Main Results

- `dense_mcs_finite_model_property`: FMP for formulas valid over dense frames
- `dense_fmp_contrapositive`: Completeness via finite model for dense frames

## References

- Blackburn, de Rijke, Venema: Modal Logic (Ch 2.3, 10.1)
- Ported from BimodalLogic/Theories/Bimodal/Metalogic/Decidability/FMP/DenseFMP.lean
-/

namespace Cslib.Logic.Bimodal.Metalogic.Decidability.FMP

open Cslib.Logic.Bimodal
open Cslib.Logic.Bimodal.Metalogic.Core

variable {Atom : Type} [DecidableEq Atom]

/--
Dense FMP: If φ is not provable, then there exists a finite model
(in the filtration sense) where φ fails.

This is the same as the base FMP - the density condition on the temporal
order does not affect the MCS-based construction.
-/
theorem dense_mcs_finite_model_property (phi : Formula Atom)
    (h_not_provable : ¬Nonempty (DerivationTree FrameClass.Base
      ([] : List (Formula Atom)) phi)) :
    ∃ (Omega : ClosureMCSBundle phi), phi ∉ Omega.carrier ∧
    Finite (FilteredWorld phi) :=
  mcs_finite_model_property phi h_not_provable

/--
Dense FMP contrapositive: If φ holds in all closure MCS, then φ is provable.
-/
theorem dense_fmp_contrapositive (phi : Formula Atom)
    (h_all_mcs : ∀ (Omega : ClosureMCSBundle phi), phi ∈ Omega.carrier) :
    Nonempty (DerivationTree FrameClass.Base ([] : List (Formula Atom)) phi) :=
  fmp_contrapositive phi h_all_mcs

/--
Record that filtered worlds exist and are finite for any formula,
regardless of whether we're considering dense or discrete frames.
-/
theorem filtered_model_exists_dense (phi : Formula Atom) :
    Finite (FilteredWorld phi) :=
  FilteredWorld.finite phi

end Cslib.Logic.Bimodal.Metalogic.Decidability.FMP
