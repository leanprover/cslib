# Implementation Plan: Task #79

- **Task**: 79 - Systematic deduplication audit and consolidation across Logics/
- **Status**: [NOT STARTED]
- **Effort**: 6 hours
- **Dependencies**: Task 78 (module keyword migration, completed)
- **Research Inputs**: specs/079_deduplicate_shared_helpers/reports/01_deduplication-survey.md
- **Artifacts**: plans/01_deduplication-plan.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: lean4
- **Lean Intent**: false

## Overview

Consolidate duplicated code across Logics/ (Propositional, Modal, Temporal, Bimodal) and Foundations/Logic/ based on the systematic deduplication survey (task 77). The survey identified 12 duplication categories across 202 Lean files (74,280 lines). This plan addresses the top 6 priority items organized into three phases of increasing risk, targeting approximately 700 lines of recoverable code. The DeductionTheorem generalization (category B+C, ~800 additional lines) has been separated into its own task (task 80) due to the design work required.

### Research Integration

The deduplication survey (report 01) identified these key findings integrated into this plan:

- **Category E**: Temporal/PropositionalHelpers re-proves 11 theorems from scratch that exist generically in Foundations (~200 lines). Bimodal already delegates via wrap/unwrap pattern.
- **Category I**: `unwrap` bridge function defined 3 times within Bimodal alone (~15 lines).
- **Category A**: `removeAll` + 3 list helper lemmas duplicated identically in 4 DeductionTheorem files (~75 lines extractable).
- **Category G**: Bimodal MCSProperties re-implements `SetConsistent`, `SetMaximalConsistent`, `closed_under_derivation`, etc. from Foundations/Consistency (~200 lines).
- **Category F**: Bimodal TemporalDerived partially duplicates Foundations/Temporal/TemporalDerived (~150 lines).
- **Category L**: Temporal GeneralizedNecessitation re-proves propositional lemmas from Foundations (~60 lines).
- **Categories B+C**: DeductionTheorem proof follows identical structure in all 4 logics (~800 lines), but requires a shared DerivationTree interface. Separated into task 80.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

This plan advances the "Abstract shared completeness infrastructure" roadmap item by reducing duplication between logic domains and strengthening the Foundations-based shared infrastructure. It also improves the import hierarchy discipline: Foundations -> Propositional -> {Modal, Temporal} -> Bimodal.

## Goals & Non-Goals

**Goals**:
- Eliminate exact duplicates (removeAll, unwrap) by extracting to shared locations
- Replace Temporal's re-proved propositional theorems with Foundations delegations
- Migrate Bimodal MCSProperties to use Foundations DerivationSystem framework
- Delegate common temporal theorems in Bimodal TemporalDerived to Foundations
- Delegate propositional lemmas in Temporal GeneralizedNecessitation to Foundations
- Verify `lake build` passes after each phase

**Non-Goals**:
- Chronicle parallel file factoring (Temporal vs Bimodal, ~15K lines -- too risky)
- Formula type parameterization (would require redesigning inductive types)
- HML vs Modal deduplication (different type-level choices: Finset vs Set)
- Generic DeductionTheorem proof (separated into task 80)

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Temporal PropositionalHelpers consumers break when switching to delegation | H | M | Check all 3 consumers (Metalogic.lean, ChronicleTypes.lean, WitnessSeed.lean) for direct DerivationTree usage vs Nonempty-based usage |
| Bimodal MCSProperties FrameClass parameterization incompatible with generic framework | H | M | The generic framework in Foundations uses DerivationSystem without FrameClass; Bimodal needs fc-parameterized versions. May need to keep fc-specific wrappers |
| removeAll extraction causes name collisions with Mathlib List operations | M | L | Use a dedicated namespace (e.g., `Cslib.Logic.Helpers`) to avoid collisions |
| Build time regression from additional imports | L | M | Monitor `lake build` times; Foundations imports should be lightweight |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1, 2 | -- |
| 2 | 3 | 1 |
| 3 | 4 | -- |

Phases within the same wave can execute in parallel.

---

### Phase 1: Extract Shared Utilities and Consolidate Bimodal unwrap [COMPLETED]

**Goal**: Eliminate exact duplicates -- extract `removeAll` + list helpers to a shared module and consolidate the `unwrap` bridge function within Bimodal.

**Tasks**:
- [x] Create `Cslib/Foundations/Logic/Helpers/ListHelpers.lean` with `removeAll`, `removeAll_subset_of_subset` (alias `removeAll_sub_of_sub`), `mem_removeAll_of_mem_of_ne`, and `removeAll_subset_removeAll` (alias `removeAll_sub_removeAll`)
- [x] Add `ListHelpers` to `Cslib/Foundations/Logic.lean` (or appropriate root import file) *(deviation: altered -- no root import file exists; DeductionTheorem files import ListHelpers directly)*
- [x] Update `Cslib/Logics/Propositional/Metalogic/DeductionTheorem.lean` to import and use shared `removeAll`; remove local definitions
- [x] Update `Cslib/Logics/Modal/Metalogic/DeductionTheorem.lean` to import and use shared `removeAll`; remove local definitions
- [x] Update `Cslib/Logics/Temporal/Metalogic/DeductionTheorem.lean` to import and use shared `removeAll`; remove local definitions
- [x] Update `Cslib/Logics/Bimodal/Metalogic/Core/DeductionTheorem.lean` to import and use shared `removeAll`; remove local definitions
- [x] Move `unwrap` (and `wrap`) to `Cslib/Logics/Bimodal/ProofSystem/Derivation.lean` (or a new `Bridge.lean` file alongside it) as the single canonical definition *(deviation: altered -- kept canonical wrap/unwrap in Perpetuity/Helpers.lean (existing location) rather than moving to Derivation.lean, to avoid disrupting the existing import hierarchy)*
- [x] Update `Cslib/Logics/Bimodal/Theorems/Combinators.lean` to import shared `unwrap`/`wrap`; remove local definitions
- [x] Update `Cslib/Logics/Bimodal/Theorems/Perpetuity/Helpers.lean` to import shared `unwrap`/`wrap`; remove local definitions *(deviation: altered -- Perpetuity/Helpers.lean IS the canonical location, so no changes needed here)*
- [x] Update `Cslib/Logics/Bimodal/Theorems/Propositional/Core.lean` to import shared `unwrap`/`wrap`; remove local definitions
- [x] Check `Cslib/Logics/Bimodal/Theorems/Propositional/Connectives.lean` for `wrap'`/`unwrap'` variants and consolidate if possible
- [x] Run `lake build` and fix any compilation errors

**Timing**: 1.5 hours

**Depends on**: none

**Files to modify**:
- `Cslib/Foundations/Logic/Helpers/ListHelpers.lean` - new file with shared list utilities
- `Cslib/Logics/Propositional/Metalogic/DeductionTheorem.lean` - remove local removeAll, import shared
- `Cslib/Logics/Modal/Metalogic/DeductionTheorem.lean` - remove local removeAll, import shared
- `Cslib/Logics/Temporal/Metalogic/DeductionTheorem.lean` - remove local removeAll, import shared
- `Cslib/Logics/Bimodal/Metalogic/Core/DeductionTheorem.lean` - remove local removeAll, import shared
- `Cslib/Logics/Bimodal/ProofSystem/Derivation.lean` (or new Bridge.lean) - canonical unwrap/wrap
- `Cslib/Logics/Bimodal/Theorems/Combinators.lean` - remove local unwrap/wrap
- `Cslib/Logics/Bimodal/Theorems/Perpetuity/Helpers.lean` - remove local unwrap/wrap
- `Cslib/Logics/Bimodal/Theorems/Propositional/Core.lean` - remove local unwrap/wrap

**Verification**:
- `lake build` completes without errors
- `grep -rn "def removeAll" Cslib/` returns exactly 1 result (in ListHelpers.lean)
- `grep -rn "def unwrap" Cslib/Logics/Bimodal/` returns exactly 1 result (in canonical location)

---

### Phase 2: Replace Temporal PropositionalHelpers with Foundations Delegation [IN PROGRESS]

**Goal**: Replace the 11 re-proved propositional theorems in `Temporal/Metalogic/PropositionalHelpers.lean` with thin delegation wrappers that call the generic Foundations versions, following the pattern already established in `Bimodal/Theorems/Perpetuity/Helpers.lean`.

**Tasks**:
- [ ] Verify that `Temporal/ProofSystem/Instances.lean` provides `InferenceSystem` and `PropositionalHilbert` instances for `Temporal.HilbertBX`
- [ ] Add `import Cslib.Foundations.Logic.Theorems.Propositional.Core` and `import Cslib.Foundations.Logic.Theorems.Combinators` to `PropositionalHelpers.lean`
- [ ] Create `wrap`/`unwrap` bridge functions in PropositionalHelpers.lean (or import from a shared location if Temporal already has them)
- [ ] Replace `double_negation` (78 lines of direct proof) with 1-line delegation via wrap/unwrap
- [ ] Replace `efq_axiom` with delegation
- [ ] Replace `imp_trans` with delegation
- [ ] Replace `pairing` with delegation
- [ ] Replace `lce_imp` / `rce_imp` with delegation
- [ ] Replace `dni` with delegation
- [ ] Replace `identity` with delegation
- [ ] Replace `demorgan_disj_neg_backward` with delegation
- [ ] Verify all 3 consumers still compile: `Metalogic.lean`, `ChronicleTypes.lean`, `WitnessSeed.lean`
- [ ] Run `lake build` and fix any type mismatches between DerivationTree and Nonempty-based APIs

**Timing**: 1.5 hours

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Temporal/Metalogic/PropositionalHelpers.lean` - rewrite from direct proofs to delegations (~200 lines removed, ~30 lines added)

**Verification**:
- `lake build` completes without errors
- `wc -l Cslib/Logics/Temporal/Metalogic/PropositionalHelpers.lean` shows significant line reduction (target: under 80 lines)
- All Chronicle files that import PropositionalHelpers still compile

---

### Phase 3: Delegate Temporal GeneralizedNecessitation Propositional Lemmas [NOT STARTED]

**Goal**: Replace the re-proved propositional lemmas (`contrapose_imp`, `contraposition`) in `Temporal/Metalogic/GeneralizedNecessitation.lean` with delegations to Foundations, keeping the temporal-specific content.

**Tasks**:
- [ ] Identify which propositional lemmas in `Temporal/Metalogic/GeneralizedNecessitation.lean` duplicate Foundations
- [ ] Add imports for Foundations propositional theorems (Connectives.lean)
- [ ] Use the wrap/unwrap bridge from Phase 2 to delegate `contrapose_imp` and `contraposition`
- [ ] Keep temporal-specific content (`generalized_temporal_k`, `generalized_past_k`, etc.) unchanged
- [ ] Run `lake build` and fix any compilation errors

**Timing**: 0.5 hours

**Depends on**: 2 (needs the Temporal wrap/unwrap bridge established in Phase 2)

**Files to modify**:
- `Cslib/Logics/Temporal/Metalogic/GeneralizedNecessitation.lean` - delegate propositional lemmas (~60 lines removed)

**Verification**:
- `lake build` completes without errors
- Temporal-specific generalized necessitation theorems still present and unchanged

---

### Phase 4: Migrate Bimodal MCSProperties and TemporalDerived to Foundations [NOT STARTED]

**Goal**: Refactor Bimodal MCSProperties to use the generic DerivationSystem framework from Foundations (as Modal, Propositional, and Temporal already do), and delegate common temporal theorems in Bimodal TemporalDerived to Foundations.

**Tasks**:

*MCSProperties migration (Category G):*
- [ ] Study how `Modal/Metalogic/MCS.lean` and `Temporal/Metalogic/MCS.lean` instantiate the generic `DerivationSystem` framework
- [ ] Determine whether Bimodal's FrameClass parameterization is compatible with the generic framework, or whether fc-specific wrappers are needed
- [ ] If compatible: create a `bimodalDerivationSystem` instance mapping Bimodal derivation to the generic `DerivationSystem` structure
- [ ] If not directly compatible: create thin wrapper functions that bridge the fc-parameterized Bimodal API to the generic framework
- [ ] Replace re-proved `SetConsistent`, `SetMaximalConsistent`, `closed_under_derivation`, `implication_property`, `negation_complete`, `set_consistent_not_both` with instantiations or delegations
- [ ] Keep Bimodal-specific extensions: `temp_4_derived`, `temp_4_past`, `allFuture_allFuture`, `allPast_allPast`, `neg_excludes`
- [ ] Run `lake build` and verify all Bimodal Metalogic files still compile

*TemporalDerived delegation (Category F):*
- [ ] Identify which of the 12 shared theorems in `Bimodal/Theorems/TemporalDerived.lean` can delegate to `Foundations/Logic/Theorems/Temporal/TemporalDerived.lean`
- [ ] For each delegatable theorem (`until_mono_guard`, `since_mono_guard`, `until_mono_event`, `since_mono_event`, `until_implies_someFuture`, `since_implies_somePast`, `F_mono`, `P_mono`, `G_distribution`, `H_distribution`, `connect_future_thm`, `connect_past_thm`): replace with wrap/unwrap delegation
- [ ] Keep Bimodal-specific extensions (`temp_4_derived`, `dne_lift_F`, etc.)
- [ ] Run `lake build` and verify

**Timing**: 2.5 hours

**Depends on**: none (independent of Phases 1-3; operates on Bimodal files only)

**Files to modify**:
- `Cslib/Logics/Bimodal/Metalogic/Core/MCSProperties.lean` - delegate generic MCS theory to Foundations (~200 lines removed)
- `Cslib/Logics/Bimodal/Theorems/TemporalDerived.lean` - delegate common temporal theorems to Foundations (~150 lines removed)

**Verification**:
- `lake build` completes without errors
- Bimodal MCS-dependent files (MaximalConsistent.lean, RestrictedMCS.lean, Separation/, Bundle/, BXCanonical/) still compile
- Bimodal-specific theorems (temp_4_derived, dne_lift_F) still present

---

## Testing & Validation

- [ ] `lake build` passes after Phase 1 (shared utilities extraction)
- [ ] `lake build` passes after Phase 2 (Temporal PropositionalHelpers delegation)
- [ ] `lake build` passes after Phase 3 (Temporal GeneralizedNecessitation delegation)
- [ ] `lake build` passes after Phase 4 (Bimodal MCS + TemporalDerived migration)
- [ ] Verify no regressions in downstream consumers: Chronicle files, Completeness proofs, Soundness proofs
- [ ] Verify `removeAll` is defined in exactly 1 location after Phase 1
- [ ] Verify `unwrap`/`wrap` are defined in exactly 1 location within Bimodal after Phase 1
- [ ] Verify no remaining exact duplicates in the targeted categories

## Artifacts & Outputs

- `specs/079_deduplicate_shared_helpers/plans/01_deduplication-plan.md` (this file)
- `specs/079_deduplicate_shared_helpers/summaries/01_deduplication-summary.md` (post-implementation)
- New file: `Cslib/Foundations/Logic/Helpers/ListHelpers.lean`
- Modified files across Logics/ (Propositional, Modal, Temporal, Bimodal)

## Rollback/Contingency

Each phase is independently revertible via `git revert` on its commit. If a phase causes widespread build failures:

1. Revert the phase commit
2. Mark the phase as [BLOCKED] with the specific failure reason
3. Proceed with the next independent phase (Phases 1, 2, and 4 are independent)
4. Log the failure in errors.json for future investigation

If the Bimodal MCSProperties migration (Phase 4) proves incompatible due to FrameClass parameterization, the fallback is to keep the current Bimodal-specific MCS code and only delegate the TemporalDerived theorems. Document the incompatibility for future reference.
