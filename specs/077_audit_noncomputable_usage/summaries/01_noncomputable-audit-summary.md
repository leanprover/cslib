# Implementation Summary: Noncomputable Usage Audit

- **Task**: 77 - audit_noncomputable_usage
- **Status**: Implemented
- **Phases**: 4/4 completed

## Changes Made

### Phase 1: Bimodal Consolidation (22 files modified)
- Added shared `theorem_in_mcs_fc` definition to `Cslib/Logics/Bimodal/Metalogic/Core/MCSProperties.lean`
- Removed 22 private local copies of `theorem_in_mcs_fc` / `theorem_in_mcs_fc'` / `theorem_in_mcs_fc''` / `theorem_in_mcs` across:
  - 12 BXCanonical files (TruthLemma, Frame, CanonicalChain, CanonicalModel, OrderedSeedConsistency, Construction, DefectChain, ChronicleTypes, ChronicleConstruction, ChronicleToCountermodel, ChronicleToCountermodelBasic, Dense)
  - 6 Bundle files (CanonicalFrame, ModalSaturation, SuccRelation, TemporalCoherence, TemporalContent, WitnessSeed)
  - 2 Algebraic files (ParametricTruthLemma, RestrictedParametricTruthLemma)
  - 3 Chronicle files (RRelation, PointInsertion, CounterexampleElimination)
- All renamed call sites compile correctly

### Phase 2: Temporal Consolidation (10 files modified)
- Added shared `theorem_in_mcs` definition to `Cslib/Logics/Temporal/Metalogic/MCS.lean`
- Removed 10 private local copies across Chronicle and Metalogic modules
- Renamed variant call sites (`theorem_in_mcs'`, `theorem_in_mcs_local`) to `theorem_in_mcs`

### Phase 3: Noncomputable Removal Attempts
- `propositions` (HML/Basic.lean): FAILED - depends on `Finset.toList` (noncomputable in Mathlib)
- `chooseEquiv` (CLL/Basic.lean): FAILED - depends on `DerivableIn.toDerivation` (noncomputable)
- `LogicalEquivalence` instance (CLL/Basic.lean): SKIPPED - depends on `chooseEquiv`
- All 13 `noncomputable section` blocks verified as correctly scoped (no overly broad scope found)

### Phase 4: Verification
- All modified modules build successfully
- Pre-existing top-level `Cslib.lean` module import error (unrelated to this task)

## Counts

| Metric | Before | After | Change |
|--------|--------|-------|--------|
| Total `noncomputable` occurrences | 390 | 359 | -31 (7.9%) |
| Private `theorem_in_mcs*` definitions | 32 | 0 | -32 |
| Shared `theorem_in_mcs*` definitions | 1 | 3 | +2 |

## Plan Deviations

- Phase 1: Shared definition placed in MCSProperties.lean instead of MaximalConsistent.lean (better type alignment with fc-parametric SetMaximalConsistent)
- Phase 2: Plan listed 5 Temporal files; actual count was 10 (research undercount)
- Phase 2: Shared definition named `theorem_in_mcs` (without tick) for naming convention consistency
- Phase 4: No top-level `lake build` possible due to pre-existing module import error; verified all modified modules individually

## Files Modified

### Bimodal (23 files)
- `Cslib/Logics/Bimodal/Metalogic/Core/MCSProperties.lean` (added shared definition)
- 22 consumer files (private definitions removed, call sites updated)

### Temporal (11 files)
- `Cslib/Logics/Temporal/Metalogic/MCS.lean` (added shared definition)
- 10 consumer files (private definitions removed, call sites updated)

### Unchanged
- `Cslib/Logics/HML/Basic.lean` (removal attempt reverted)
- `Cslib/Logics/LinearLogic/CLL/Basic.lean` (removal attempt reverted)
