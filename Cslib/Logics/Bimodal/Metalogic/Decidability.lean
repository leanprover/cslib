/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Bimodal.Metalogic.Decidability.SignedFormula
public import Cslib.Logics.Bimodal.Metalogic.Decidability.TraceCertificate
public import Cslib.Logics.Bimodal.Metalogic.Decidability.Tableau
public import Cslib.Logics.Bimodal.Metalogic.Decidability.AxiomMatcher
public import Cslib.Logics.Bimodal.Metalogic.Decidability.Closure
public import Cslib.Logics.Bimodal.Metalogic.Decidability.Saturation
public import Cslib.Logics.Bimodal.Metalogic.Decidability.CountermodelExtraction
public import Cslib.Logics.Bimodal.Metalogic.Decidability.ProofExtraction
public import Cslib.Logics.Bimodal.Metalogic.Decidability.DecisionProcedure
public import Cslib.Logics.Bimodal.Metalogic.Decidability.FMP
public import Cslib.Logics.Bimodal.Metalogic.Decidability.Correctness

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

@[expose] public section

