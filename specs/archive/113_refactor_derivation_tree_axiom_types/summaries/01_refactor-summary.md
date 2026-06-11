# Implementation Summary: Refactor Propositional DerivationTree to Axiom-Parameterized Form

- **Task**: 113
- **Status**: Implemented
- **Plan**: plans/01_refactor-plan.md

## Changes Made

### Phase 1: Axiom Types and Core Parameterization
- Added `IntPropAxiom` (implyK, implyS, efq) and `MinPropAxiom` (implyK, implyS) inductive types to `Axioms.lean`
- Added subsumption proofs: `MinPropAxiom.toIntProp` and `IntPropAxiom.toProp`
- Parameterized `DerivationTree` from `DerivationTree Gamma phi` to `DerivationTree (Axioms : PL.Proposition Atom -> Prop) Gamma phi`
- Parameterized `Deriv`, `Derivable`, `mp_deriv`, `weakening_deriv`, `assumption_deriv`, `propDerivationSystem`
- Added backward-compat aliases: `ClDerivationTree`, `ClDeriv`, `ClDerivable`, `clPropDerivationSystem`

### Phase 2: Deduction Theorem Parameterization
- Updated `HasHilbertTree` global instance to use `DerivationTree PropositionalAxiom`
- Parameterized `deductionWithMem` and `deductionTheorem` with `{Axioms}`, `h_implyK`, `h_implyS` following the modal pattern (with `letI : HasHilbertTree`)
- Parameterized `prop_has_deduction_theorem` to take `h_implyK`/`h_implyS`
- Added `cl_prop_has_deduction_theorem` backward-compat wrapper

### Phase 3: MCS Parameterization
- Parameterized `PropSetConsistent` and `PropSetMaximalConsistent` by `Axioms`
- Parameterized all MCS theorems (`prop_lindenbaum`, `prop_closed_under_derivation`, `prop_implication_property`, `prop_negation_complete`, `prop_mcs_bot_not_mem`, `prop_mcs_neg_of_not_mem`, `prop_mcs_not_mem_of_neg`, `prop_mcs_mem_iff_neg_not_mem`) with `{Axioms}` and `h_implyK`/`h_implyS` where the deduction theorem is needed

### Phase 4: Instance Updates and IntMinInstances
- Updated `Instances.lean`: `InferenceSystem` for `HilbertCl` now uses `DerivationTree PropositionalAxiom`
- Created `IntMinInstances.lean` with:
  - `HilbertInt` instances: `InferenceSystem`, `ModusPonens`, `HasAxiomImplyK`, `HasAxiomImplyS`, `HasAxiomEFQ`, `IntuitionisticHilbert`
  - `HilbertMin` instances: `InferenceSystem`, `ModusPonens`, `HasAxiomImplyK`, `HasAxiomImplyS`, `MinimalHilbert`
- Registered `IntMinInstances.lean` in `Cslib.lean`

### Phase 5: NaturalDeduction Backward Compatibility
- Fixed `FromHilbert.lean`: all `DerivationTree`/`Deriv` references fixed at `PropositionalAxiom`; `impI` now passes explicit `h_implyK`/`h_implyS` to `deductionTheorem`
- Fixed `HilbertDerivedRules.lean`: all type signatures fixed at `PropositionalAxiom`
- Fixed `Equivalence.lean`: all references fixed at `PropositionalAxiom`; `ndToHilbert` passes explicit axiom proofs to `deductionTheorem`

### Phase 6: Full Build and Verification
- Full `lake build` succeeds with no errors
- Zero sorries in all modified files
- Zero vacuous definitions
- No new axioms introduced
- Completeness.lean (already adapted to parameterized API) continues to compile

## Files Modified
- `Cslib/Logics/Propositional/ProofSystem/Axioms.lean`
- `Cslib/Logics/Propositional/ProofSystem/Derivation.lean`
- `Cslib/Logics/Propositional/ProofSystem/Instances.lean`
- `Cslib/Logics/Propositional/Metalogic/DeductionTheorem.lean`
- `Cslib/Logics/Propositional/Metalogic/MCS.lean`
- `Cslib/Logics/Propositional/NaturalDeduction/FromHilbert.lean`
- `Cslib/Logics/Propositional/NaturalDeduction/HilbertDerivedRules.lean`
- `Cslib/Logics/Propositional/NaturalDeduction/Equivalence.lean`
- `Cslib.lean`

## Files Created
- `Cslib/Logics/Propositional/ProofSystem/IntMinInstances.lean`

## Plan Deviations
- None (implementation followed plan)

## Verification Results
- **sorry_count**: 0
- **vacuous_count**: 0
- **axiom_count**: 0 (in propositional files)
- **build_passed**: true
- **compliance_check**: passed
