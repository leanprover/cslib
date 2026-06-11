# Implementation Plan: D5 Soundness and Completeness

- **Task**: 108 - Modal D5 Soundness and Completeness
- **Status**: [NOT STARTED]
- **Effort**: 1 hour
- **Dependencies**: Task 100 infrastructure (complete)
- **Research Inputs**: specs/108_modal_d5_soundness_completeness/reports/01_d5-logic-research.md
- **Artifacts**: plans/01_d5-logic-plan.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: lean4
- **Lean Intent**: true

## Overview

Prove soundness and completeness for modal logic D5 (K + D + 5) over serial + Euclidean Kripke frames. D5 combines axiom D (seriality) and axiom 5 (Euclideanness) but does NOT have axiom T (reflexivity), which determines the truth lemma choice: `truth_lemma_d` (not `truth_lemma`). The implementation is a mechanical hybrid of D4Soundness/D4Completeness (D-family structure) and K5Soundness/K5Completeness (axiom 5 handling). All infrastructure from task 100 is complete.

### Research Integration

Research report `01_d5-logic-research.md` confirms:
- D5Axiom inductive type already defined in `Instances.lean` (lines 370-395) with 7 constructors: 4 propositional (implyK, implyS, efq, peirce) + 3 modal (modalK, modalD, modalFive)
- All typeclass instances registered in `Instances.lean` (lines 1299-1371)
- Required canonical model lemmas verified: `canonical_serial` (DCompleteness.lean), `canonical_eucl_from_5` (Completeness.lean), `truth_lemma_d` (DCompleteness.lean)
- No novel proof ideas needed -- every building block exists and is verified

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No ROADMAP.md found.

## Goals & Non-Goals

**Goals**:
- Create `D5Soundness.lean` proving every D5Axiom is valid over serial + Euclidean frames
- Create `D5Completeness.lean` proving completeness via canonical model construction
- Both files build successfully with `lake build`

**Non-Goals**:
- Novel proof strategies (this is pattern application, not research)
- Changes to existing infrastructure files
- Additional axiom systems beyond D5

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| `canonical_eucl_from_5` signature mismatch with D5Axiom constructors | M | L | Verify exact parameter order via `lean_hover_info` before writing |
| `truth_lemma_d` requires additional constructors not in D5Axiom | H | L | D4 uses identical truth_lemma_d with same constructor set; verified in research |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |

Phases within the same wave can execute in parallel.

### Phase 1: D5 Soundness [COMPLETED]

**Goal**: Create `D5Soundness.lean` proving all D5 axioms are valid over serial + Euclidean frames.

**Tasks**:
- [ ] Create `Cslib/Logics/Modal/Metalogic/D5Soundness.lean` following D4Soundness pattern
- [ ] Module header with `public import Cslib.Logics.Modal.Metalogic.Soundness` and `public import Cslib.Logics.Modal.ProofSystem.Instances`
- [ ] Implement `d5_axiom_sound` with case analysis on all 7 D5Axiom constructors:
  - Propositional cases (implyK, implyS, efq, peirce): identical to D4Soundness
  - modalK: standard K distribution (identical to D4Soundness)
  - modalD: seriality witness case (copy from D4Soundness lines 67-72, uses `h_serial`)
  - modalFive: Euclidean argument (copy from K5Soundness lines 62-69, uses `h_eucl`)
- [ ] Implement `d5_soundness` wrapper (DerivationTree version) with both `h_serial` and `h_eucl` hypotheses
- [ ] Implement `d5_soundness_derivable` wrapper (Derivable version) with both frame conditions
- [ ] Verify: `lake build Cslib.Logics.Modal.Metalogic.D5Soundness`

**Timing**: 20 minutes

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Modal/Metalogic/D5Soundness.lean` - create new file

**Verification**:
- `lake build Cslib.Logics.Modal.Metalogic.D5Soundness` succeeds with no errors or sorries

---

### Phase 2: D5 Completeness [NOT STARTED]

**Goal**: Create `D5Completeness.lean` proving completeness for D5 over serial + Euclidean frames via canonical model construction.

**Tasks**:
- [ ] Create `Cslib/Logics/Modal/Metalogic/D5Completeness.lean` following D4Completeness pattern
- [ ] Module header with `public import Cslib.Logics.Modal.Metalogic.Completeness` and `public import Cslib.Logics.Modal.Metalogic.DCompleteness`
- [ ] Implement `d5_completeness` theorem with signature:
  ```
  theorem d5_completeness (phi : Proposition Atom)
      (h_valid : forall (World : Type u) (m : Model World Atom),
        Relation.Serial m.r ->
        (forall w1 w2 w3, m.r w1 w2 -> m.r w1 w3 -> m.r w2 w3) ->
        forall w, Satisfies m w phi) :
      Derivable D5Axiom phi
  ```
- [ ] Contrapositive setup (`by_contra h_not_deriv`)
- [ ] Consistency proof for `{neg phi}` using D5Axiom constructors (identical boilerplate to D4Completeness with D5Axiom substituted)
- [ ] Lindenbaum extension via `modal_lindenbaum`
- [ ] Canonical seriality via `canonical_serial` with D5Axiom constructors (implyK, implyS, efq, modalK, modalD)
- [ ] Final contradiction combining:
  - `truth_lemma_d` with D5Axiom constructors (implyK, implyS, efq, peirce, modalK, modalD)
  - `canonical_eucl_from_5` with D5Axiom constructors (implyK, implyS, modalK, modalFive) -- replacing D4's `canonical_trans` with `.modalFour`
  - `mcs_not_mem_of_neg` for the contradiction
- [ ] Verify: `lake build Cslib.Logics.Modal.Metalogic.D5Completeness`

**Timing**: 40 minutes

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/Modal/Metalogic/D5Completeness.lean` - create new file

**Verification**:
- `lake build Cslib.Logics.Modal.Metalogic.D5Completeness` succeeds with no errors or sorries
- `lean_verify` confirms no sorry or axiom usage beyond standard foundations

## Testing & Validation

- [ ] `lake build Cslib.Logics.Modal.Metalogic.D5Soundness` -- no errors
- [ ] `lake build Cslib.Logics.Modal.Metalogic.D5Completeness` -- no errors
- [ ] `lean_verify` on `d5_soundness_derivable` -- no sorry
- [ ] `lean_verify` on `d5_completeness` -- no sorry

## Artifacts & Outputs

- `Cslib/Logics/Modal/Metalogic/D5Soundness.lean` - Soundness proof for D5
- `Cslib/Logics/Modal/Metalogic/D5Completeness.lean` - Completeness proof for D5
- `specs/108_modal_d5_soundness_completeness/plans/01_d5-logic-plan.md` - This plan
- `specs/108_modal_d5_soundness_completeness/summaries/01_d5-logic-summary.md` - Execution summary (generated during implementation)

## Rollback/Contingency

If implementation fails:
1. Delete `D5Soundness.lean` and `D5Completeness.lean`
2. No existing files are modified, so no rollback of other files needed
3. If `canonical_eucl_from_5` signature does not match D5Axiom constructors, check `lean_hover_info` for exact parameter types and adjust constructor mappings
