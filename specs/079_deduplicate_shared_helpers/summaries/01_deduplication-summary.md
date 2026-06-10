# Implementation Summary: Task #79

- **Task**: 79 - Systematic deduplication audit and consolidation across Logics/
- **Status**: Implemented
- **Plan**: specs/079_deduplicate_shared_helpers/plans/01_deduplication-plan.md

## What Was Done

### Phase 1: Extract Shared Utilities and Consolidate Bimodal unwrap
- Created `Cslib/Foundations/Logic/Helpers/ListHelpers.lean` with `removeAll`, `removeAll_subset_of_subset`, `mem_removeAll_of_mem_of_ne`, `removeAll_subset_removeAll`, and `List.Subset` aliases (`removeAll_sub_of_sub`, `removeAll_sub_removeAll`)
- Updated all 4 DeductionTheorem files (Propositional, Modal, Temporal, Bimodal) to import from ListHelpers and remove local `removeAll` definitions
- Consolidated `unwrap`/`wrap` within Bimodal: canonical location in `Perpetuity/Helpers.lean`, removed duplicate definitions from `Combinators.lean` and `Propositional/Core.lean`, converted `wrap'`/`unwrap'` in `Connectives.lean` to `abbrev` aliases

### Phase 2: Replace Temporal PropositionalHelpers with Foundations Delegation
- Replaced 11 re-proved propositional theorems (233 lines) with 1-line delegations via wrap/unwrap bridge pattern (117 lines)
- Created Temporal `wrap`/`unwrap` bridge functions for `Temporal.HilbertBX`
- Delegated: `double_negation`, `efq_axiom`, `imp_trans`, `pairing`, `lce_imp`, `rce_imp`, `dni`, `identity`, `demorgan_disj_neg_backward`
- All 3 consumers verified: `Metalogic.lean`, `ChronicleTypes.lean`, `WitnessSeed.lean`

### Phase 3: Delegate Temporal GeneralizedNecessitation Propositional Lemmas
- Replaced `imp_trans_base` with delegation to `imp_trans` from PropositionalHelpers
- Replaced `contrapose_imp` and `contraposition` with delegations to Foundations via wrap/unwrap
- Temporal-specific theorems (`generalized_temporal_k`, `generalized_past_k`, etc.) preserved unchanged

### Phase 4: Migrate Bimodal TemporalDerived to Foundations
- Delegated 10 compound temporal theorems to Foundations TemporalDerived via wrap/unwrap:
  - `G_distribution`, `H_distribution`
  - `G_and_intro`, `H_and_intro`
  - `G_imp_trans`, `H_imp_trans`
  - `G_contrapose`, `H_contrapose`
  - `connect_future_G`, `connect_past_H`
- Bimodal-specific theorems preserved: `temp_4_derived`, `dne_lift_F`, `formula_or_comm`, etc.
- MCSProperties kept as-is (see Plan Deviations)

## Metrics

| Metric | Before | After |
|--------|--------|-------|
| `removeAll` definitions | 4 | 1 |
| `unwrap`/`wrap` in Bimodal | 3/1 + 1/1 primed | 1/1 + abbrevs |
| PropositionalHelpers.lean lines | 233 | 117 |
| GeneralizedNecessitation propositional lines | ~30 | ~10 |
| Total lines removed (approx) | - | ~200 |

## Verification

- `lake build` passes (all 2914 jobs)
- No new sorries introduced
- No new axioms introduced
- No vacuous definitions introduced
- `removeAll` defined in exactly 1 location (ListHelpers.lean)
- `unwrap`/`wrap` defined in exactly 1 location within Bimodal (Perpetuity/Helpers.lean)

## Files Modified

### New Files
- `Cslib/Foundations/Logic/Helpers/ListHelpers.lean`

### Modified Files
- `Cslib/Logics/Propositional/Metalogic/DeductionTheorem.lean` -- removed local removeAll
- `Cslib/Logics/Modal/Metalogic/DeductionTheorem.lean` -- removed local removeAll
- `Cslib/Logics/Temporal/Metalogic/DeductionTheorem.lean` -- removed local removeAll
- `Cslib/Logics/Bimodal/Metalogic/Core/DeductionTheorem.lean` -- removed local removeAll
- `Cslib/Logics/Bimodal/Theorems/Combinators.lean` -- removed local unwrap, imports Perpetuity
- `Cslib/Logics/Bimodal/Theorems/Propositional/Core.lean` -- removed local unwrap
- `Cslib/Logics/Bimodal/Theorems/Propositional/Connectives.lean` -- wrap'/unwrap' to abbrevs
- `Cslib/Logics/Temporal/Metalogic/PropositionalHelpers.lean` -- full rewrite to delegations
- `Cslib/Logics/Temporal/Metalogic/GeneralizedNecessitation.lean` -- propositional delegations
- `Cslib/Logics/Bimodal/Theorems/TemporalDerived.lean` -- temporal theorem delegations

## Plan Deviations

- **Phase 1**: ListHelpers imported directly by DeductionTheorem files rather than added to a root import file (no root import file exists)
- **Phase 1**: `wrap`/`unwrap` canonical location kept in Perpetuity/Helpers.lean rather than moved to ProofSystem/Derivation.lean (existing location was natural; avoids import hierarchy disruption)
- **Phase 4**: MCSProperties migration skipped -- the fc-parameterized `SetConsistent`/`SetMaximalConsistent` definitions are incompatible with the generic Foundations framework, which uses a single `DerivationSystem` at Base level. Full delegation would require creating DerivationSystem instances per FrameClass with corresponding HasDeductionTheorem proofs, with significant refactoring risk for completeness proof consumers.
- **Phase 4**: Only compound temporal theorems delegated in TemporalDerived; simple 1-line axiom wrappers kept as-is (delegation would add complexity without reducing duplication)
