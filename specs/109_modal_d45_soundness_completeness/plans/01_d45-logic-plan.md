# Implementation Plan: Task #109 - Modal D45 Soundness and Completeness

- **Task**: 109 - Modal D45 Soundness and Completeness
- **Status**: [NOT STARTED]
- **Effort**: 2 hours
- **Dependencies**: Task 100 (shared infrastructure, completed)
- **Research Inputs**: specs/109_modal_d45_soundness_completeness/reports/01_d45-logic-research.md
- **Artifacts**: plans/01_d45-logic-plan.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: lean4
- **Lean Intent**: true

## Overview

Prove soundness and completeness for modal logic D45 (K + D + 4 + 5) over serial + transitive + Euclidean Kripke frames. D45 is a hybrid of the D-family (seriality via axiom D) and the K45-family (transitivity + Euclideanness via axioms 4 + 5). The implementation creates two new Lean files and adds two import lines to the module aggregator. All required infrastructure (D45Axiom, typeclass instances, parameterized canonical lemmas, truth lemma) already exists from prior tasks.

### Research Integration

Key findings from the research report (01_d45-logic-research.md):

1. **D45Axiom has 8 constructors**: implyK, implyS, efq, peirce, modalK, modalD, modalFour, modalFive -- all required constructors for every parameterized lemma are present.
2. **Truth lemma choice**: Must use `truth_lemma_d` (D-specific), NOT `truth_lemma` (requires axiom T that D45 lacks) and NOT `k_truth_lemma` (works but `truth_lemma_d` is preferred for D-family consistency).
3. **Euclideanness lemma choice**: Must use `canonical_eucl_from_5` (requires only axiom 5), NOT `canonical_eucl` (requires B + T + 4, which D45 lacks).
4. **Structural pattern**: D45 soundness = D4 soundness + modalFive case from K45. D45 completeness = D4 completeness + canonical_eucl_from_5 from K45. Both are mechanical combinations.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No ROADMAP.md found.

## Goals & Non-Goals

**Goals**:
- Prove `d45_axiom_sound`: all 8 D45Axiom schemata valid on serial + transitive + Euclidean frames
- Prove `d45_soundness` and `d45_soundness_derivable`: wrapper theorems for context and derivable soundness
- Prove `d45_completeness`: if phi valid on all serial + transitive + Euclidean frames, then phi is D45-derivable
- Add D45Soundness and D45Completeness imports to Metalogic.lean aggregator
- Verify `lake build` passes with zero errors and zero sorries

**Non-Goals**:
- Creating new infrastructure (D45Axiom, HilbertD45, instances already exist from task 100)
- Proving new canonical lemmas (canonical_serial, canonical_trans, canonical_eucl_from_5 already exist)
- Modifying existing proof files

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Type mismatch with truth_lemma_d instantiation | M | Very Low | D45Axiom has all 6 required constructors; verified against DCompleteness signatures in research |
| canonical_eucl_from_5 instantiation mismatch | M | Very Low | D45Axiom has all 4 required constructors; verified against Completeness signatures |
| Universe polymorphism issues in completeness | M | Very Low | Follow existing `universe u` pattern from D4Completeness and K45Completeness |
| Build regression from new imports | L | Very Low | New files are purely additive; only Metalogic.lean import list changes |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |

Phases within the same wave can execute in parallel.

---

### Phase 1: D45 Soundness [COMPLETED]

**Goal**: Create D45Soundness.lean with soundness proof for D45 over serial + transitive + Euclidean frames.

**Tasks**:
- [ ] Create `Cslib/Logics/Modal/Metalogic/D45Soundness.lean` with copyright header and module declaration
- [ ] Implement `d45_axiom_sound`: case analysis on D45Axiom with 8 cases
  - Cases implyK, implyS, efq, peirce, modalK: identical to D4Soundness (valid on all frames)
  - Case modalD: uses seriality hypothesis `h_serial` (identical to D4Soundness line 70-72)
  - Case modalFour: uses transitivity hypothesis `h_trans` (identical to D4Soundness line 76-77)
  - Case modalFive: uses Euclideanness hypothesis `h_eucl` (identical to K45Soundness lines 79-81)
- [ ] Implement `d45_soundness`: wrapper using parameterized `soundness` with 3 frame hypotheses
- [ ] Implement `d45_soundness_derivable`: wrapper using parameterized `soundness_derivable` with 3 frame hypotheses
- [ ] Verify with `lake build Cslib.Logics.Modal.Metalogic.D45Soundness`

**Timing**: 45 minutes

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Modal/Metalogic/D45Soundness.lean` - New file (~110 lines)

**Verification**:
- `lake build Cslib.Logics.Modal.Metalogic.D45Soundness` passes with zero errors
- `lean_verify` confirms no sorry or axiom usage

---

### Phase 2: D45 Completeness and Integration [COMPLETED]

**Goal**: Create D45Completeness.lean with completeness proof and update Metalogic.lean aggregator.

**Tasks**:
- [ ] Create `Cslib/Logics/Modal/Metalogic/D45Completeness.lean` with copyright header, imports from both Completeness and DCompleteness
- [ ] Implement `d45_completeness` following the canonical model pattern:
  - Contrapositive setup: `by_contra h_not_deriv`
  - Consistency argument: show `{neg phi}` is D45-consistent (~30 lines boilerplate, identical to D4Completeness)
  - Lindenbaum extension: `modal_lindenbaum h_cons`
  - Canonical world construction
  - Canonical seriality: `canonical_serial` with D45Axiom constructors (implyK, implyS, efq, modalK, modalD)
  - Final contradiction block assembling:
    - `truth_lemma_d` with 6 constructor arguments (implyK, implyS, efq, peirce, modalK, modalD)
    - `canonical_trans` with 3 constructor arguments (implyK, implyS, modalFour)
    - `canonical_eucl_from_5` with 4 constructor arguments (implyK, implyS, modalK, modalFive)
    - `mcs_not_mem_of_neg` for final contradiction
- [ ] Add 2 import lines to `Cslib/Logics/Modal/Metalogic.lean`:
  - `public import Cslib.Logics.Modal.Metalogic.D45Soundness`
  - `public import Cslib.Logics.Modal.Metalogic.D45Completeness`
- [ ] Update module docstring in Metalogic.lean to include D45 in the logic list
- [ ] Verify with `lake build Cslib.Logics.Modal.Metalogic`

**Timing**: 1 hour 15 minutes

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/Modal/Metalogic/D45Completeness.lean` - New file (~150 lines)
- `Cslib/Logics/Modal/Metalogic.lean` - Add 2 import lines, update docstring

**Verification**:
- `lake build Cslib.Logics.Modal.Metalogic` passes with zero errors
- `lean_verify` on `d45_completeness` confirms no sorry or axiom usage
- `lean_verify` on `d45_axiom_sound` confirms no sorry or axiom usage

## Testing & Validation

- [ ] `lake build Cslib.Logics.Modal.Metalogic.D45Soundness` builds without errors
- [ ] `lake build Cslib.Logics.Modal.Metalogic.D45Completeness` builds without errors
- [ ] `lake build Cslib.Logics.Modal.Metalogic` builds without errors (full aggregator)
- [ ] `lean_verify` on `Cslib.Logic.Modal.d45_axiom_sound` shows no sorry/axiom
- [ ] `lean_verify` on `Cslib.Logic.Modal.d45_completeness` shows no sorry/axiom
- [ ] No regressions in existing modal logic proofs

## Artifacts & Outputs

- `Cslib/Logics/Modal/Metalogic/D45Soundness.lean` - New file (~110 lines)
- `Cslib/Logics/Modal/Metalogic/D45Completeness.lean` - New file (~150 lines)
- `Cslib/Logics/Modal/Metalogic.lean` - Modified (2 import lines + docstring update)
- `specs/109_modal_d45_soundness_completeness/plans/01_d45-logic-plan.md` - This plan

## Rollback/Contingency

Delete the two new files and revert the Metalogic.lean import changes:
```bash
rm Cslib/Logics/Modal/Metalogic/D45Soundness.lean
rm Cslib/Logics/Modal/Metalogic/D45Completeness.lean
git checkout Cslib/Logics/Modal/Metalogic.lean
```
No existing files are modified beyond the aggregator, so rollback is clean.
