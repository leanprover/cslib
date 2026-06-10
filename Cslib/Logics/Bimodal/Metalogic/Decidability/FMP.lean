/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

import Cslib.Logics.Bimodal.Metalogic.Decidability.FMP.ClosureMCS
import Cslib.Logics.Bimodal.Metalogic.Decidability.FMP.Filtration
import Cslib.Logics.Bimodal.Metalogic.Decidability.FMP.FiniteModel
import Cslib.Logics.Bimodal.Metalogic.Decidability.FMP.TruthPreservation
import Cslib.Logics.Bimodal.Metalogic.Decidability.FMP.FMP
import Cslib.Logics.Bimodal.Metalogic.Decidability.FMP.DenseFMP
import Cslib.Logics.Bimodal.Metalogic.Decidability.FMP.DiscreteFMP

/-!
# Finite Model Property -- Barrel Import

This module re-exports all components of the Finite Model Property (FMP)
infrastructure for TM bimodal logic:

- **ClosureMCS**: Closure-restricted maximal consistent sets
- **Filtration**: MCS filtration equivalence, setoid, and filtered world quotient
- **FiniteModel**: Finiteness theorem via characteristic set injection
- **TruthPreservation**: Truth preservation (filtration lemma) for all operators
- **FMP**: Main FMP theorem and contrapositive
- **DenseFMP**: FMP specialized for dense temporal orders
- **DiscreteFMP**: FMP specialized for discrete temporal orders

## Key Theorems

- `mcs_finite_model_property`: If φ not provable, ∃ finite world where φ fails
- `fmp_contrapositive`: If φ true in all finite worlds → φ provable
- `FilteredWorld.finite`: The filtered world type is finite
- `filtration_lemma_membership`: Truth preservation through quotient
-/
