# Implementation Plan: Task #48

- **Task**: 48 - Temporal counterexample elimination and chronicle construction
- **Status**: [NOT STARTED]
- **Effort**: 16 hours
- **Dependencies**: Task 47 (completed)
- **Research Inputs**: specs/048_temporal_chronicle_construction/reports/01_research-report.md
- **Artifacts**: plans/01_implementation-plan.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: lean4
- **Lean Intent**: false

## Overview

Port the omega-step chronicle construction from bimodal to temporal logic. This task creates two new files -- `CounterexampleElimination.lean` (~2200-2800 lines) and `ChronicleConstruction.lean` (~1200-1500 lines) -- that enumerate all C5/C6 counterexamples, iteratively insert points to eliminate them, and assemble the chronicle as the directed limit of all finite stages. The bimodal source has zero sorry stubs and the transfer rate is genuinely ~95%, with changes limited to namespace/import rewrites and FrameClass parameter removal. A small set of prerequisites (Adjacent definition, Chronicle structure, chronicle conditions, two propositional helpers) must be added to existing temporal files first.

### Research Integration

The research report (01_research-report.md) confirms:
- Zero sorry stubs in bimodal CounterexampleElimination.lean (3529 lines) and ChronicleConstruction.lean (1531 lines)
- `[Denumerable (Formula Atom)]` instance exists at `Temporal/Syntax/Formula.lean:208`
- All point insertion lemmas exist in temporal PointInsertion.lean (2888 lines)
- Missing: `Adjacent` definition, `Chronicle` structure, chronicle conditions (c0-c5'), `ChronicleInvariant` bundle, `demorgan_disj_neg_backward` helper, `identity` combinator
- `eliminate_g_prop_counterexample` / `eliminate_h_prop_counterexample` are defined in bimodal but never called -- can be omitted from temporal
- g/h duality theorems (`h_content_sub_imp_g_content_sub'`, `g_content_sub_imp_h_content_sub'`) already exist in temporal PointInsertion.lean -- no need to duplicate in ChronicleConstruction

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No ROADMAP.md found.

## Goals & Non-Goals

**Goals**:
- Create temporal `CounterexampleElimination.lean` with all elimination types (C4/C4'/C5/C5')
- Create temporal `ChronicleConstruction.lean` with omega-chain, limit chronicle, and C0-C5 satisfaction proofs
- Add prerequisite definitions to existing temporal files (Adjacent, Chronicle, chronicle conditions)
- Zero sorry stubs in all new code
- All new files build cleanly with `lake build`

**Non-Goals**:
- Abstracting shared code between bimodal and temporal (that is Task 41's scope)
- Truth lemma and completeness assembly (that is Task 49's scope)
- Porting `eliminate_g_prop_counterexample` / `eliminate_h_prop_counterexample` (unused in omega chain)
- Re-proving g/h duality theorems that already exist in PointInsertion.lean

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Private helpers in PointInsertion.lean inaccessible to CounterexampleElimination | M | M | Re-derive locally or make non-private if few references |
| maxHeartbeats exceeded on large tactic proofs | M | M | Set `maxHeartbeats 3200000` (matching PointInsertion.lean); increase if needed |
| `temporal_lindenbaum` signature differs from bimodal `set_lindenbaum_fc` | L | L | Adapt call sites -- no `fc` parameter needed, simplifies signature |
| Bimodal theorem references (demorgan, identity, temp_k_dist) fail to translate | M | L | Phase 1 creates all helpers first; test each before proceeding |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3 | 2 |
| 4 | 4 | 3 |
| 5 | 5 | 4 |
| 6 | 6 | 5 |

Phases within the same wave can execute in parallel.

---

### Phase 1: Chronicle Infrastructure Prerequisites [COMPLETED]

**Goal**: Add all missing type definitions and propositional helpers that CounterexampleElimination.lean depends on.

**Tasks**:
- [ ] Add `Adjacent` definition to temporal `ChronicleTypes.lean`: `def Adjacent (dom : Finset Rat) (x y : Rat) : Prop`
- [ ] Add `Chronicle` structure to temporal `ChronicleTypes.lean`: `structure Chronicle (Atom : Type*) where f : Rat -> Set (Formula Atom); g : Rat -> Rat -> Set (Formula Atom); dom : Finset Rat`
- [ ] Add chronicle conditions `c0`, `c1`, `c2'`, `c3`, `c4`, `c4'`, `c5`, `c5'` (no FrameClass parameter; use `Temporal.SetMaximalConsistent` for c0, `BurgessR3Maximal` for c2')
- [ ] Add `ChronicleInvariant` structure bundling c0, c1, c2', c3
- [ ] Add C3 consequence theorems: `c3_interval_subset_point`, `c3_interval_subset_left`, `c3_interval_subset_right`
- [ ] Add `demorgan_disj_neg_backward` to `PropositionalHelpers.lean`: type `(A.neg.and B.neg).imp (A.or B).neg`
- [ ] Add `identity` combinator to `PropositionalHelpers.lean`: type `A.imp A`
- [ ] Run `lake build Cslib.Logics.Temporal.Metalogic.Chronicle.ChronicleTypes` and `lake build Cslib.Logics.Temporal.Metalogic.PropositionalHelpers` to verify

**Timing**: 2 hours

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Temporal/Metalogic/Chronicle/ChronicleTypes.lean` - Add Adjacent, Chronicle, conditions, ChronicleInvariant (~120 lines)
- `Cslib/Logics/Temporal/Metalogic/PropositionalHelpers.lean` - Add demorgan_disj_neg_backward, identity (~40 lines)

**Verification**:
- `lake build Cslib.Logics.Temporal.Metalogic.Chronicle.ChronicleTypes` succeeds
- `lake build Cslib.Logics.Temporal.Metalogic.PropositionalHelpers` succeeds
- `grep -c "sorry" ChronicleTypes.lean PropositionalHelpers.lean` returns 0

---

### Phase 2: CounterexampleElimination -- Helpers and Structures (lines 1-700) [COMPLETED]

**Goal**: Port the first section of CounterexampleElimination.lean: counterexample structures, rational helpers, BurgessR3Maximal helpers, and type definitions.

**Tasks**:
- [ ] Create `Cslib/Logics/Temporal/Metalogic/Chronicle/CounterexampleElimination.lean` with imports and namespace
- [ ] Port `theorem_in_mcs` private helper (adapt for temporal -- no `fc`)
- [ ] Port `C5Counterexample` and `C5'Counterexample` structures (remove `fc` from types)
- [ ] Port rational helpers: `exists_rat_gt_finset`, `exists_rat_lt_finset`, `exists_rat_between_not_in_finset`
- [ ] Port `BurgessR3Maximal_g_content_sub` (replace bimodal references: `until_F_mcs`, `some_future_all_future_neg_absurd`, `temp_k_dist_derived`, `identity`, `liftBase`)
- [ ] Port `BurgessR3Maximal_sdc`, `BurgessR3Maximal_bot_not_mem`, `c2'_preserved_on_old_adjacent`
- [ ] Port `burgessR3Maximal_from_h_content_sub` (backward mirror)
- [ ] Skip `eliminate_g_prop_counterexample` and `eliminate_h_prop_counterexample` (unused in temporal)
- [ ] Port `PotentialCounterexampleKind` (identical 4-case enum)
- [ ] Port `PotentialCounterexample` structure, `EliminationResult` structure (remove `fc` parameter)
- [ ] Port `C5ForwardWalkResult` and `C5BackwardWalkResult` structures (remove `fc`)
- [ ] Run `lake build Cslib.Logics.Temporal.Metalogic.Chronicle.CounterexampleElimination` to verify partial build

**Timing**: 3 hours

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/Temporal/Metalogic/Chronicle/CounterexampleElimination.lean` - Create new file (~500-600 lines)

**Verification**:
- File compiles without errors (all definitions type-check)
- Zero sorry stubs
- `grep -c "FrameClass\|liftBase\|Bimodal" CounterexampleElimination.lean` returns 0

---

### Phase 3: CounterexampleElimination -- Recursive Walks (lines 700-1850) [COMPLETED]

**Goal**: Port the recursive forward and backward walks that insert points to satisfy C5/C5' conditions.

**Tasks**:
- [ ] Port `c5_forward_walk` (recursive, ~550 lines): replace `fc` parameter, `liftBase` calls, bimodal theorem references with temporal equivalents; reference temporal `lemma_2_4_with_guard`, `lemma_2_6_splitting`, `lemma_2_7`, `lemma_2_8`
- [ ] Port `c5_backward_walk` (mirror, ~550 lines): same mechanical changes for Since direction; reference `lemma_2_7_since`, `lemma_2_8_since`, `lemma_2_4_with_guard` (since variant)
- [ ] Replace all `demorgan_disj_neg_backward` references with temporal version from PropositionalHelpers
- [ ] Replace `Combinators.identity` with temporal `identity` from PropositionalHelpers
- [ ] Replace `set_lindenbaum_fc` calls with `temporal_lindenbaum`
- [ ] Set `maxHeartbeats` appropriately (start with 3200000, increase if needed)
- [ ] Run build to verify

**Timing**: 4 hours

**Depends on**: 2

**Files to modify**:
- `Cslib/Logics/Temporal/Metalogic/Chronicle/CounterexampleElimination.lean` - Add recursive walks (~1100 lines)

**Verification**:
- `c5_forward_walk` and `c5_backward_walk` compile without errors
- Termination proofs accepted by Lean
- Zero sorry stubs

---

### Phase 4: CounterexampleElimination -- Main Elimination Function (lines 1850-3529) [COMPLETED]

**Goal**: Port the main `eliminate_potential_counterexample` function that dispatches on the 4 counterexample kinds and orchestrates the walks.

**Tasks**:
- [ ] Port `eliminate_potential_counterexample` (the largest single function, ~1700 lines): dispatches to `c5_forward_walk`, `c5_backward_walk`, `eliminate_C5_counterexample`, `eliminate_C5'_counterexample` depending on `PotentialCounterexampleKind`
- [ ] Port `eliminate_C5_counterexample` and `eliminate_C5'_counterexample` helper functions
- [ ] Replace all bimodal-specific references: `FrameClass`, `liftBase`, bimodal theorem paths
- [ ] Verify all EliminationResult fields are satisfied for each case
- [ ] Run full module build: `lake build Cslib.Logics.Temporal.Metalogic.Chronicle.CounterexampleElimination`

**Timing**: 4 hours

**Depends on**: 3

**Files to modify**:
- `Cslib/Logics/Temporal/Metalogic/Chronicle/CounterexampleElimination.lean` - Complete the file (~1600-1700 lines added)

**Verification**:
- Full CounterexampleElimination.lean compiles
- `wc -l CounterexampleElimination.lean` is in range 2200-2800
- `grep -c "sorry" CounterexampleElimination.lean` returns 0
- `grep -c "Bimodal\|FrameClass\|liftBase" CounterexampleElimination.lean` returns 0

---

### Phase 5: ChronicleConstruction.lean -- Full Port [NOT STARTED]

**Goal**: Port ChronicleConstruction.lean in full: singleton chronicle, omega chain, limit chronicle, and all satisfaction proofs.

**Tasks**:
- [ ] Create `Cslib/Logics/Temporal/Metalogic/Chronicle/ChronicleConstruction.lean` with imports
- [ ] Port singleton chronicle: `singleton_chronicle`, `singleton_c0`, `singleton_dom`, `singleton_f_zero`, `singleton_invariant`, `singleton_c2'`, `singleton_c4`, `singleton_c4'`
- [ ] Port countability instances: `Countable`, `Infinite`, `Denumerable` for `PotentialCounterexample`
- [ ] Port omega chain: `counterexample_enum`, `counterexample_enum_surjective`, `counterexample_enum_surjective_above`, `omega_chain`, `omega_chain_val`, `omega_chain_c0`, `omega_chain_c2'`
- [ ] Port omega chain accessors: `omega_chain_elim_result`, `omega_chain_f_eq_elim`, `omega_chain_dom_eq_elim`, `omega_chain_dom_mono`, `omega_chain_f_agrees`, `omega_chain_dom_mono_le`, `omega_chain_f_agrees_le`, `omega_chain_g_eq_elim`, `omega_chain_g_agrees`, `omega_chain_g_agrees_le`
- [ ] Port omega chain witness lifting: `omega_chain_c5_witness`, `omega_chain_c5'_witness`, `omega_chain_c4_witness`, `omega_chain_c4'_witness`
- [ ] Port limit chronicle: `limit_dom`, `limit_f`, `limit_f_eq`, `limit_c0`, `limit_f_zero`, `zero_mem_limit_dom`
- [ ] Port limit C5 satisfaction: `limit_satisfies_c5_weak`, `limit_satisfies_c5'_weak`, `limit_F_resolution`, `limit_P_resolution`
- [ ] Port limit C4 satisfaction: `limit_satisfies_c4`, `limit_satisfies_c4'`
- [ ] Port limit interval function: `limit_g`, `limit_c3`, `limit_c3_interval_subset_*`
- [ ] Reference temporal PointInsertion's `h_content_sub_imp_g_content_sub'` and `g_content_sub_imp_h_content_sub'` instead of re-proving g/h duality
- [ ] Port forward G / backward H: `limit_forward_G`, `limit_backward_H`
- [ ] Port `chronicle_model_exists`
- [ ] Port omega chain single-point insertion: `omega_chain_dom_new_unique`, `omega_chain_c5_forward_resolved_no_new`, `omega_chain_c5_backward_resolved_no_new`
- [ ] Port omega chain g-value lifting: `omega_chain_g_sub_f_insert`, `omega_chain_g_sub_g_new`
- [ ] Port adjacent pair g-value propagation: `adj_g_mem_f_at_stage`, `adj_g_mem_limit_f`
- [ ] Port `exists_containing_adjacent` helper
- [ ] Port strong C5: `limit_satisfies_c5_strong`, `limit_satisfies_c5'_strong`
- [ ] Run `lake build Cslib.Logics.Temporal.Metalogic.Chronicle.ChronicleConstruction`

**Timing**: 4 hours

**Depends on**: 4

**Files to modify**:
- `Cslib/Logics/Temporal/Metalogic/Chronicle/ChronicleConstruction.lean` - Create new file (~1200-1500 lines)

**Verification**:
- Full ChronicleConstruction.lean compiles
- `wc -l ChronicleConstruction.lean` is in range 1200-1500
- `grep -c "sorry" ChronicleConstruction.lean` returns 0
- `grep -c "Bimodal\|FrameClass\|liftBase" ChronicleConstruction.lean` returns 0

---

### Phase 6: Build Verification and Cleanup [NOT STARTED]

**Goal**: Run full project build, verify zero sorry stubs across all new/modified files, and perform cleanup.

**Tasks**:
- [ ] Run `lake build` (full project build) to verify no regressions
- [ ] Verify zero sorry stubs: `grep -rn "sorry" Cslib/Logics/Temporal/Metalogic/Chronicle/CounterexampleElimination.lean Cslib/Logics/Temporal/Metalogic/Chronicle/ChronicleConstruction.lean`
- [ ] Verify no bimodal references leaked: `grep -rn "Bimodal\|FrameClass\|liftBase" CounterexampleElimination.lean ChronicleConstruction.lean`
- [ ] Verify line counts are in expected ranges
- [ ] Review consistency of names: all temporal versions should use temporal naming conventions (no `fc` parameter, `Temporal.SetMaximalConsistent` not `SetMaximalConsistent fc`)

**Timing**: 1 hour

**Depends on**: 5

**Files to modify**:
- No new files -- verification only. Minor cleanups if needed.

**Verification**:
- `lake build` succeeds with zero errors
- Total new code: ~3400-4300 lines across 2 new files + ~160 lines added to 2 existing files
- Zero sorry stubs in all task files

## Testing & Validation

- [ ] `lake build Cslib.Logics.Temporal.Metalogic.Chronicle.ChronicleTypes` succeeds
- [ ] `lake build Cslib.Logics.Temporal.Metalogic.PropositionalHelpers` succeeds
- [ ] `lake build Cslib.Logics.Temporal.Metalogic.Chronicle.CounterexampleElimination` succeeds
- [ ] `lake build Cslib.Logics.Temporal.Metalogic.Chronicle.ChronicleConstruction` succeeds
- [ ] `lake build` (full project) succeeds with zero errors
- [ ] Zero `sorry` stubs in all new/modified files
- [ ] No bimodal namespace references in temporal files
- [ ] `chronicle_model_exists` theorem compiles (final result providing the chronicle for any MCS)

## Artifacts & Outputs

- `specs/048_temporal_chronicle_construction/plans/01_implementation-plan.md` (this plan)
- `Cslib/Logics/Temporal/Metalogic/Chronicle/CounterexampleElimination.lean` (new, ~2200-2800 lines)
- `Cslib/Logics/Temporal/Metalogic/Chronicle/ChronicleConstruction.lean` (new, ~1200-1500 lines)
- `Cslib/Logics/Temporal/Metalogic/Chronicle/ChronicleTypes.lean` (extended, ~120 lines added)
- `Cslib/Logics/Temporal/Metalogic/PropositionalHelpers.lean` (extended, ~40 lines added)

## Rollback/Contingency

All changes are additive (new files + additions to existing files). To rollback:
1. Delete `CounterexampleElimination.lean` and `ChronicleConstruction.lean`
2. Revert additions to `ChronicleTypes.lean` and `PropositionalHelpers.lean`
3. `lake build` should pass unchanged (no existing code depends on new definitions)

If specific theorems fail to compile after porting:
- Check if private helpers from PointInsertion.lean need to be made public or re-derived
- Try increasing `maxHeartbeats` (up to 6400000)
- Fall back to constructing temporal-specific proofs for the ~5% of content that does not transfer mechanically
