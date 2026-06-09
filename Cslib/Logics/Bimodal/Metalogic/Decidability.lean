/-
Copyright (c) 2026 Benjamin Brastmckie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brastmckie
-/

import Cslib.Logics.Bimodal.Metalogic.Decidability.SignedFormula
import Cslib.Logics.Bimodal.Metalogic.Decidability.TraceCertificate
import Cslib.Logics.Bimodal.Metalogic.Decidability.Tableau
import Cslib.Logics.Bimodal.Metalogic.Decidability.AxiomMatcher
import Cslib.Logics.Bimodal.Metalogic.Decidability.Closure
import Cslib.Logics.Bimodal.Metalogic.Decidability.Saturation
import Cslib.Logics.Bimodal.Metalogic.Decidability.CountermodelExtraction
import Cslib.Logics.Bimodal.Metalogic.Decidability.ProofExtraction
import Cslib.Logics.Bimodal.Metalogic.Decidability.DecisionProcedure
import Cslib.Logics.Bimodal.Metalogic.Decidability.FMP
import Cslib.Logics.Bimodal.Metalogic.Decidability.Correctness

/-!
# Decidability Module -- Barrel Import

This module re-exports all components of the tableau-based decision procedure
for TM bimodal logic:

- **SignedFormula**: Foundation types (Sign, SignedFormula, Branch, Label, subformulaClosure)
- **TraceCertificate**: Trace instrumentation types for tableau expansion
- **Tableau**: 30 tableau expansion rules and the rule application engine
- **AxiomMatcher**: Minimal axiom pattern-matching (matchAxiom for 42 axiom schemata)
- **Closure**: Branch closure detection (contradiction, botPos, axiomNeg)
- **Saturation**: Fuel-bounded tableau expansion with soundness theorem
- **CountermodelExtraction**: Countermodel extraction from open branches with branchTruthLemma
- **ProofExtraction**: Multi-strategy proof term extraction from closed tableaux
- **DecisionProcedure**: Main `decide` function tying together all components
- **Correctness**: Soundness theorems and classical decidability results

## Key Theorems

- `expandBranchWithFuel_sound`: Soundness of tableau expansion
- `branchTruthLemma`: Correctness of countermodel extraction
- `decide_sound`: If derivable, then semantically valid
- `validity_decidable`: `(⊨ φ) ∨ ¬(⊨ φ)` (classical)
- `decide_result_exclusive`: Decision results are mutually exclusive
-/
