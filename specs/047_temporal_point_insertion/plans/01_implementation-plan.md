# Implementation Plan: Task #47 -- Temporal Point Insertion

- **Task**: 47 - Temporal Point Insertion
- **Status**: [NOT STARTED]
- **Effort**: 10 hours
- **Dependencies**: Task 46 (completed)
- **Research Inputs**: specs/047_temporal_point_insertion/reports/01_research-report.md
- **Artifacts**: plans/01_implementation-plan.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: lean4
- **Lean Intent**: true

## Overview

Port the point insertion machinery (Burgess Lemmas 2.4-2.8) from bimodal `BXCanonical/Chronicle/PointInsertion.lean` (3556 lines) and missing RRelation helpers from bimodal `RRelation.lean` (1695 lines) to the temporal logic module. The temporal version eliminates the `FrameClass` parameter (fixed to `FrameClass.Base`), drops `liftBase` calls, and replaces bimodal API calls with temporal standalone function equivalents. No box-specific cases exist in PointInsertion.lean, so all 3556 lines transfer with mechanical changes.

### Research Integration

The research report (01_research-report.md) provides:
- Complete inventory of Task 46 infrastructure (ChronicleTypes 216 lines, RRelation 424 lines, Frame 254 lines, etc.)
- Transfer analysis identifying 14 systematic API replacements (SetMaximalConsistent fc -> Temporal.SetMaximalConsistent, etc.)
- Identification of 6 missing lemmas in RRelation.lean (monotonicity helpers + duality lemmas)
- Phase decomposition with line count estimates: 2150-2950 lines total
- Risk assessment with mitigations for MCS API mismatch, FrameClass removal, and missing combinators

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No ROADMAP.md found.

## Goals & Non-Goals

**Goals**:
- Extend `RRelation.lean` with left monotonicity helpers (`untl_left_mono_G`, `snce_left_mono_H`, theorem-level variants) and Burgess 2.3 duality lemmas (`burgessR_implies_burgessRSince`, `burgessRSince_implies_burgessR`)
- Create `PointInsertion.lean` with all MCS-level axiom helpers, DCS/R3Maximal properties, Xu Lemmas 2.3 and 3.2.1, and Burgess Lemmas 2.4-2.8 in both Until and Since directions
- Each phase must pass `lake build` for the target module

**Non-Goals**:
- Do NOT add chronicle conditions C0-C5 to ChronicleTypes.lean (belongs to Task 48)
- Do NOT modify existing definitions in ChronicleTypes.lean or RRelation.lean -- only add new lemmas
- Do NOT port CounterexampleElimination.lean or ChronicleConstruction.lean (Task 48 scope)

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| MCS API mismatch (`SetMaximalConsistent fc` methods vs standalone temporal functions) | M | M | Systematic substitution table from research report; verify each helper compiles before proceeding |
| Missing propositional combinators (`identity`, `theorem_flip`, `mp`) | L | M | Define locally or add to `PropositionalHelpers.lean`; bimodal equivalents are simple 5-10 line derivations |
| Heartbeat limits on large proofs (Lemma 2.7 seed consistency is ~200 lines) | M | M | Set `maxHeartbeats 3200000` at file level; split into helper lemmas if needed |
| `deduction_theorem` location / import mismatches | L | L | Already imported transitively via existing Chronicle modules |
| Lean 4 term elaboration differences from bimodal branch | L | L | Use `lean_goal` and `lean_multi_attempt` to verify tactic steps |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 0 | -- |
| 2 | 1 | 0 |
| 3 | 2 | 1 |
| 4 | 3 | 2 |
| 5 | 4 | 3 |

Phases are strictly sequential: each phase builds on definitions and lemmas from the prior phase.

### Phase 0: RRelation Extensions [COMPLETED]

**Goal**: Add missing left monotonicity helpers and Burgess 2.3 duality lemmas to `RRelation.lean`, unblocking all subsequent PointInsertion work.

**Tasks**:
- [ ] Add `untl_left_mono_G`: `G(phi -> psi) -> untl(event, phi) -> untl(event, psi)` at MCS level using BX2G (`left_mono_until_G`)
- [ ] Add `untl_left_mono_thm`: theorem-level version using temporal_necessitation + `untl_left_mono_G`
- [ ] Add `snce_left_mono_H`: `H(phi -> psi) -> snce(event, phi) -> snce(event, psi)` at MCS level using BX2H (`left_mono_since_H`)
- [ ] Add `snce_left_mono_thm`: theorem-level version using `past_necessitation` + `snce_left_mono_H`
- [ ] Add duality helpers: `neg_all_past_neg_to_some_past`, `neg_all_future_neg_to_some_future`, `some_future_H_neg_G_P_absurd`, `some_past_G_neg_H_F_absurd`
- [ ] Add `burgessR_implies_burgessRSince`: Burgess Lemma 2.3 forward direction (burgessR -> burgessRSince)
- [ ] Add `burgessRSince_implies_burgessR`: Burgess Lemma 2.3 backward direction (mirror)
- [ ] Add `deductiveClosure_singleton_imp` (for singleton deductive closure): if phi in DC({eta}), then |- eta -> phi
- [ ] Add `burgessR_of_deductiveClosure_singleton` and `burgessRSince_of_deductiveClosure_singleton`: propagation through deductive closure
- [ ] Add `burgessR3Maximal_exists_from_seed`: existence from a seed element satisfying both directions
- [ ] Run `lake build Cslib.Logics.Temporal.Metalogic.Chronicle.RRelation`

**Timing**: 2.5 hours

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Temporal/Metalogic/Chronicle/RRelation.lean` - append ~450 lines of new lemmas

**Verification**:
- `lake build Cslib.Logics.Temporal.Metalogic.Chronicle.RRelation` succeeds with no errors
- All new lemmas are sorry-free

---

### Phase 1: PointInsertion Core Helpers [COMPLETED]

**Goal**: Create `PointInsertion.lean` with MCS-level axiom wrappers, Lemmas 2.4-2.6, DCS/R3Maximal properties, and BurgessR3Maximal infrastructure.

**Tasks**:
- [ ] Create `Cslib/Logics/Temporal/Metalogic/Chronicle/PointInsertion.lean` with imports and namespace
- [ ] Port `F_neg_of_G_not` and `P_neg_of_H_not` (from G(phi) not in A derive F(neg phi) in A)
- [ ] Port `lemma_2_4` (Until witness endpoint construction): seed consistency + Lindenbaum + BurgessR3Maximal
- [ ] Port MCS-level axiom helpers: `until_F_mcs`, `self_accum_until_mcs`, `self_accum_since_mcs`, `connect_future_mcs`, `conj_mcs`, `or_elim_mcs`
- [ ] Port `linear_until_mcs` and `linear_since_mcs` (BX7/BX7' at MCS level)
- [ ] Port `lemma_2_5b` and `lemma_2_5b_past` (g_content/h_content ordering transitivity)
- [ ] Port `lemma_2_6` (counterexample insertion: delta not in C -> MCS D with neg delta)
- [ ] Port `conj_left_mcs`, `conj_right_mcs`, `G_implies_F_mcs`, `H_implies_P_mcs`
- [ ] Port `dcs_neg_union_consistent`, `r3Maximal_neg_of_not_mem`, `R3Maximal_is_mcs`, `mcs_no_proper_dcs_extension`
- [ ] Port `dc_delta_B_controlled`, `BurgessR3Maximal_extension_fails`, `dc_delta_B_burgessR3`
- [ ] Port inconsistent-extension helpers: `burgessR3_univ_of_inconsistent_ext`, `g_content_sub` proof, `h_content_sub_imp_g_content_sub'`, `g_content_sub_imp_h_content_sub'`
- [ ] Run `lake build Cslib.Logics.Temporal.Metalogic.Chronicle.PointInsertion`

**Timing**: 2.5 hours

**Depends on**: 0

**Files to modify**:
- `Cslib/Logics/Temporal/Metalogic/Chronicle/PointInsertion.lean` (new file, ~700 lines)

**Verification**:
- `lake build Cslib.Logics.Temporal.Metalogic.Chronicle.PointInsertion` succeeds
- All ported lemmas are sorry-free

---

### Phase 2: Xu Lemmas and Enrichment Structures [COMPLETED]

**Goal**: Port Xu Lemma 2.3 (top-guard presence), derivation-level monotonicity helpers, enrichment structures, list conjunction helpers, and Xu Lemma 3.2.1 (full guard strengthening).

**Tasks**:
- [ ] Port `xu_lemma_2_3_since_top` (if R(A,B,C) then snce(alpha, top) in B for all alpha in A)
- [ ] Port `xu_lemma_2_3_until_top` (if R(A,B,C) then untl(gamma, top) in B for all gamma in C)
- [ ] Port derivation-level monotonicity: `untl_left_mono_deriv`, `snce_left_mono_deriv`, `untl_right_mono_deriv`, `snce_right_mono_deriv`
- [ ] Port `right_mono_until_mcs`, `right_mono_since_mcs` (BX3/BX3' at MCS level)
- [ ] Port `enrichment_until_mcs`, `enrichment_since_mcs` (BX13/BX13' at MCS level)
- [ ] Port `F_mono_mcs`, `P_mono_mcs` (F/P monotonicity at MCS level)
- [ ] Port `list_conj`, `list_conj_implies_elem`, `list_conj_mem_dcs`, `list_conj_mem_mcs`
- [ ] Port `EnrichedEvent` structure, `iterated_enrichment` (BX13 iterated enrichment for Until)
- [ ] Port `EnrichedEventSince` structure, `iterated_enrichment_since` (BX13' for Since)
- [ ] Port `xu_lemma_3_2_1_until` (full guard: untl(gamma, beta) in B for all beta in B, gamma in C)
- [ ] Port `xu_lemma_3_2_1_since` (mirror: snce(alpha, beta) in B for all beta in B, alpha in A)
- [ ] Run `lake build Cslib.Logics.Temporal.Metalogic.Chronicle.PointInsertion`

**Timing**: 2 hours

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/Temporal/Metalogic/Chronicle/PointInsertion.lean` - append ~600 lines

**Verification**:
- `lake build Cslib.Logics.Temporal.Metalogic.Chronicle.PointInsertion` succeeds
- Xu Lemmas 2.3 and 3.2.1 are sorry-free in both Until and Since directions

---

### Phase 3: Burgess Lemmas 2.6 Splitting and 2.7 Until [PARTIAL]

**Goal**: Port Lemma 2.6 splitting (BurgessR3Maximal interval insertion) and Lemma 2.7 (Until-formula splitting) including the seed consistency proof and all helper infrastructure.

**Tasks**:
- [ ] Port `lemma_2_6_splitting` (given R3M(A,B,C) and beta not in B, produce D with neg-beta and decomposed R3M)
- [ ] Port Lemma 2.7 seed definition (`lemma_2_7_seed`) and guard extraction helpers (`l27_guard`, `l27_collect_guards`, `l27_a_event_list`)
- [ ] Port `derivation_from_implied` (list-level cut / substitution principle)
- [ ] Port `consistent_of_F_mem`, `consistent_of_P_mem`, `inconsistent_singleton_false`
- [ ] Port `lemma_2_7_seed_consistent` (BX5+BX7+BX13 chain for seed consistency)
- [ ] Port `lemma_2_7` main theorem (Until-formula splitting: R3M(A,B,C) with U(xi,eta) in A and eta not in B gives D with xi in D and decomposed R3Ms)
- [ ] Port `lemma_2_8` if present (variant of 2.7 with additional hypothesis)
- [ ] Port `lemma_2_4_with_guard` (strengthened version of 2.4 returning guard membership)
- [ ] Run `lake build Cslib.Logics.Temporal.Metalogic.Chronicle.PointInsertion`

**Timing**: 2 hours

**Depends on**: 2

**Files to modify**:
- `Cslib/Logics/Temporal/Metalogic/Chronicle/PointInsertion.lean` - append ~700 lines

**Verification**:
- `lake build Cslib.Logics.Temporal.Metalogic.Chronicle.PointInsertion` succeeds
- Lemmas 2.6 splitting and 2.7 are sorry-free

---

### Phase 4: Since-Direction Mirrors [NOT STARTED]

**Goal**: Port the Since-direction mirrors of Lemmas 2.7 and 2.8, plus `lemma_2_4_since_with_guard`, completing the full point insertion machinery.

**Tasks**:
- [ ] Port `lemma_2_7_since_seed` definition and guard extraction helpers (Since-direction seed)
- [ ] Port `lemma_2_7_since_seed_consistent` (Since-direction seed consistency using BX5'+BX7'+BX13')
- [ ] Port `lemma_2_7_since` main theorem (Since-formula splitting: R3M(A,B,C) with S(xi,eta) in C and eta not in B gives D with xi in D and decomposed R3Ms)
- [ ] Port `lemma_2_8_since` if present (Since variant of 2.8)
- [ ] Port `lemma_2_4_since_with_guard` (Since-direction of 2.4 with guard membership)
- [ ] Final `lake build Cslib.Logics.Temporal.Metalogic.Chronicle.PointInsertion`
- [ ] Verify no sorries in the file: `grep -n "sorry" Cslib/Logics/Temporal/Metalogic/Chronicle/PointInsertion.lean`
- [ ] Verify no sorries in RRelation additions: `grep -n "sorry" Cslib/Logics/Temporal/Metalogic/Chronicle/RRelation.lean`

**Timing**: 1 hour

**Depends on**: 3

**Files to modify**:
- `Cslib/Logics/Temporal/Metalogic/Chronicle/PointInsertion.lean` - append ~500 lines

**Verification**:
- `lake build` succeeds for the full project (or at minimum the temporal module)
- `grep -c sorry` returns 0 for both PointInsertion.lean and the new sections of RRelation.lean
- Total line count of PointInsertion.lean is in the 2000-2800 range

## Testing & Validation

- [ ] `lake build Cslib.Logics.Temporal.Metalogic.Chronicle.RRelation` succeeds after Phase 0
- [ ] `lake build Cslib.Logics.Temporal.Metalogic.Chronicle.PointInsertion` succeeds after each of Phases 1-4
- [ ] No `sorry` in any new code (grep verification)
- [ ] No `def X := True` or other vacuous definitions (prohibited per lean4 rules)
- [ ] All bimodal API calls replaced with temporal equivalents (no references to `Cslib.Logic.Bimodal.*`)
- [ ] No `FrameClass` parameter in any temporal definition or theorem
- [ ] `lean_verify` on key theorems (lemma_2_4, xu_lemma_3_2_1_until, lemma_2_7) to check axiom usage

## Artifacts & Outputs

- `Cslib/Logics/Temporal/Metalogic/Chronicle/RRelation.lean` - extended with ~450 lines (monotonicity + duality + existence)
- `Cslib/Logics/Temporal/Metalogic/Chronicle/PointInsertion.lean` - new file, ~2500 lines (Burgess 2.4-2.8 + Xu 2.3, 3.2.1)
- `specs/047_temporal_point_insertion/plans/01_implementation-plan.md` - this plan

## Rollback/Contingency

- Phase 0 only appends to RRelation.lean; can be reverted by removing appended lines
- PointInsertion.lean is a new file; deletion reverts all of Phases 1-4
- If a specific lemma (e.g., 2.7 seed consistency) hits heartbeat limits, split into helper lemmas or increase maxHeartbeats
- If MCS API mismatch causes widespread failures, create an adapter module with `abbrev` definitions mapping bimodal-style methods to temporal standalone functions
