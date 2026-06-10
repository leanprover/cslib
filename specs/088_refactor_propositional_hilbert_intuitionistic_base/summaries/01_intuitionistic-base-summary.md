# Implementation Summary: Refactor Propositional Hilbert to Intuitionistic Base

- **Task**: 88 - Refactor propositional Hilbert system to intuitionistic base with uniform extension architecture
- **Status**: Implemented
- **Session**: sess_1781134578_b4e200
- **Plan**: plans/01_intuitionistic-base-plan.md

## Changes Made

### Phase 1: Define New Typeclasses and Tag Types
- **File**: `Cslib/Foundations/Logic/ProofSystem.lean`
- Introduced three-level hierarchy:
  - `MinimalHilbert` (MP, K, S)
  - `IntuitionisticHilbert` extends `MinimalHilbert` (+ EFQ)
  - `ClassicalHilbert` extends `IntuitionisticHilbert` (+ Peirce)
- Updated `ModalHilbert` and `TemporalBXHilbert` to extend `ClassicalHilbert`
- Added tag types `Propositional.HilbertMin` and `Propositional.HilbertInt`
- Removed dead code `HasAxiomDNE` (declared but never used)
- Updated module docstring

### Phase 2: Weaken Combinators.lean to MinimalHilbert
- **File**: `Cslib/Foundations/Logic/Theorems/Combinators.lean`
- Changed `variable [PropositionalHilbert S (F := F)]` to `[MinimalHilbert S (F := F)]`
- All 10 theorems (imp_trans, identity, b_combinator, flip, app1, app2, pairing, dni, combine_imp_conj, combine_imp_conj_3) compile with minimal logic only

### Phase 3: Stratify Core.lean and Connectives.lean
- **File**: `Cslib/Foundations/Logic/Theorems/Propositional/Core.lean`
  - Minimal section: `lem`
  - Intuitionistic section: `efq_axiom`, `raa`, `efq_neg`
  - Classical section: `peirce_axiom`, `double_negation`, `rcp`, `lce_imp`, `rce_imp`
- **File**: `Cslib/Foundations/Logic/Theorems/Propositional/Connectives.lean`
  - Minimal section: `contrapose_imp`, `contraposition`, `iff_intro`, `iff_neg_intro`
  - Classical section: `classical_merge`, `contrapose_iff`, all De Morgan laws

### Phase 4: Update Downstream Extensions and BigConj
- Updated `ClassicalHilbert` instances in:
  - `Cslib/Logics/Propositional/ProofSystem/Instances.lean`
  - `Cslib/Logics/Temporal/ProofSystem/Instances.lean`
  - `Cslib/Logics/Bimodal/ProofSystem/Instances.lean`
- Updated `BigConj.lean` from `[PropositionalHilbert S]` to `[ClassicalHilbert S]`
- Updated `Theorems.lean` aggregator documentation
- Removed backward-compatibility `PropositionalHilbert` alias

### Phase 5: Final Verification
- Full `lake build` passes (only pre-existing error in unrelated DerivedRules.lean)
- Zero `PropositionalHilbert` references remain in source
- Zero sorries, zero vacuous definitions, zero new axioms
- All plan compliance checks pass

## Plan Deviations

- `raa` and `efq_neg` were placed in the Intuitionistic section instead of Classical as the plan specified. Analysis showed they only require EFQ (not Peirce), so intuitionistic is their correct minimal strength level. This is a strict improvement over the plan.

## Final Hierarchy

```
MinimalHilbert (K, S, MP)
  -> IntuitionisticHilbert (+ EFQ)
    -> ClassicalHilbert (+ Peirce)
      -> ModalHilbert (+ Necessitation, K)
        -> ModalS5Hilbert (+ T, 4, B)
      -> TemporalBXHilbert (+ TempNec, 22 temporal axioms)
      -> BimodalTMHilbert (via ModalS5 + TemporalBX + MF)
```

## Files Modified

| File | Change |
|------|--------|
| `Cslib/Foundations/Logic/ProofSystem.lean` | New hierarchy, tag types, remove HasAxiomDNE |
| `Cslib/Foundations/Logic/Theorems/Combinators.lean` | Weaken to MinimalHilbert |
| `Cslib/Foundations/Logic/Theorems/Propositional/Core.lean` | Stratify into 3 sections |
| `Cslib/Foundations/Logic/Theorems/Propositional/Connectives.lean` | Stratify into 2 sections |
| `Cslib/Foundations/Logic/Theorems/BigConj.lean` | ClassicalHilbert constraint |
| `Cslib/Foundations/Logic/Theorems.lean` | Doc updates |
| `Cslib/Logics/Propositional/ProofSystem/Instances.lean` | ClassicalHilbert instance |
| `Cslib/Logics/Temporal/ProofSystem/Instances.lean` | ClassicalHilbert instance |
| `Cslib/Logics/Bimodal/ProofSystem/Instances.lean` | ClassicalHilbert instance |

## Verification Results

- **Build**: Passes (pre-existing DerivedRules.lean error unrelated to this task)
- **Sorry count**: 0
- **Vacuous definitions**: 0
- **New axioms**: 0
- **PropositionalHilbert references**: 0
- **Compliance check**: Passed
