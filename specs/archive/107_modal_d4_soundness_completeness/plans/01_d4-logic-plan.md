# Implementation Plan: Task #107

- **Task**: 107 - Modal D4 Soundness and Completeness
- **Status**: [NOT STARTED]
- **Effort**: 2 hours
- **Dependencies**: None (task 100 infrastructure created inline)
- **Research Inputs**: specs/107_modal_d4_soundness_completeness/reports/01_d4-logic-research.md
- **Artifacts**: plans/01_d4-logic-plan.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: lean4
- **Lean Intent**: true

## Overview

Prove soundness and completeness for modal logic D4 (K + D + 4) over serial + transitive Kripke frames. D4 combines the seriality axiom (D) from DSoundness/DCompleteness with the transitivity axiom (4) from S4Soundness/S4Completeness, but critically lacks axiom T. This means the completeness proof must use `truth_lemma_d` (the D-specific truth lemma) rather than `truth_lemma` (the T-based truth lemma). The implementation creates two new Lean files (D4Soundness.lean, D4Completeness.lean) and modifies three existing files (ProofSystem.lean, Instances.lean, Metalogic.lean) for infrastructure and module registration.

### Research Integration

The research report (01_d4-logic-research.md) identifies the critical design choice: D4 must use `truth_lemma_d` and `mcs_box_witness_d` because D4 lacks axiom T. The report confirms all required parameterized lemmas (`canonical_serial`, `canonical_trans`, `truth_lemma_d`) already exist and accept the constructor references that D4Axiom provides. The D4Axiom inductive type requires 7 constructors (4 propositional + 3 modal: K, D, 4). Estimated total is ~250-300 lines of new Lean code across 5 files.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No ROADMAP.md found.

## Goals & Non-Goals

**Goals**:
- Define `D4Axiom` inductive type with 7 constructors (implyK, implyS, efq, peirce, modalK, modalD, modalFour)
- Add `Modal.HilbertD4` tag type and `ModalD4Hilbert` bundled class to ProofSystem.lean
- Register all typeclass instances for D4 in Instances.lean
- Prove `d4_axiom_sound`: every D4 axiom is valid on serial + transitive frames
- Prove `d4_soundness` and `d4_soundness_derivable`: soundness wrapper theorems
- Prove `d4_completeness`: completeness via canonical model with `truth_lemma_d` + `canonical_serial` + `canonical_trans`
- Update Metalogic.lean module aggregator with D4Soundness and D4Completeness imports

**Non-Goals**:
- Refactoring existing D or S4 proofs
- Adding D4 to the broader modal cube dependency graph (that is task 100/111 scope)
- Proving decidability or finite model property for D4

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| D4Axiom conflicts with task 100 definitions | L | L | D4Axiom is self-contained; task 100 can deduplicate later |
| truth_lemma_d instantiation mismatch with D4Axiom | H | Very Low | D4Axiom has all required constructors; verified against parameter signatures |
| canonical_trans expects different parameter shape | H | Very Low | canonical_trans is parameterized and tested with S4Axiom; D4Axiom provides identical modalFour constructor |
| Build regression in other modules | M | Very Low | New files are additive; only Metalogic.lean import list changes |
| Universe polymorphism issues | M | L | Follow existing `universe u` pattern from DCompleteness.lean |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |

Phases within the same wave can execute in parallel.

### Phase 1: D4 Infrastructure + Soundness [COMPLETED]

**Goal**: Define D4Axiom, add tag type and bundled class, register instances, and prove soundness.

**Tasks**:
- [x] **Task 1.1**: Add `Modal.HilbertD4` tag type to `Cslib/Foundations/Logic/ProofSystem.lean` (after `Modal.HilbertD`) *(deviation: skipped -- already created by task 100)*
- [x] **Task 1.2**: Add `ModalD4Hilbert` bundled class to `Cslib/Foundations/Logic/ProofSystem.lean` extending `ModalDHilbert` with `HasAxiom4` *(deviation: skipped -- already created by task 100)*
- [x] **Task 1.3**: Define `D4Axiom` inductive type in `Cslib/Logics/Modal/ProofSystem/Instances.lean` with 7 constructors: implyK, implyS, efq, peirce, modalK, modalD, modalFour *(deviation: skipped -- already created by task 100)*
- [x] **Task 1.4**: Register all typeclass instances for `Modal.HilbertD4` in Instances.lean: InferenceSystem, ModusPonens, Necessitation, HasAxiomImplyK, HasAxiomImplyS, HasAxiomEFQ, HasAxiomPeirce, HasAxiomK, HasAxiomD, HasAxiom4, ModalHilbert, ModalDHilbert, ModalD4Hilbert *(deviation: skipped -- already created by task 100)*
- [x] **Task 1.5**: Create `Cslib/Logics/Modal/Metalogic/D4Soundness.lean` following DSoundness.lean pattern
- [x] **Task 1.6**: Prove `d4_axiom_sound`: case analysis on D4Axiom with 7 cases -- propositional + modalK cases identical to DSoundness, modalD uses seriality (from DSoundness), modalFour uses transitivity (from S4Soundness)
- [x] **Task 1.7**: Prove `d4_soundness` and `d4_soundness_derivable` wrapper theorems using parameterized `soundness` and `soundness_derivable`
- [x] **Task 1.8**: Run `lake build Cslib.Logics.Modal.Metalogic.D4Soundness` to verify

**Timing**: 45 minutes

**Depends on**: none

**Files to modify**:
- `Cslib/Foundations/Logic/ProofSystem.lean` -- add HilbertD4 tag type and ModalD4Hilbert bundled class
- `Cslib/Logics/Modal/ProofSystem/Instances.lean` -- add D4Axiom inductive type and ~13 instance registrations

**Files to create**:
- `Cslib/Logics/Modal/Metalogic/D4Soundness.lean` -- ~90 lines: d4_axiom_sound, d4_soundness, d4_soundness_derivable

**Verification**:
- `lake build Cslib.Logics.Modal.Metalogic.D4Soundness` passes with zero errors
- `grep -r sorry Cslib/Logics/Modal/Metalogic/D4Soundness.lean` returns no matches
- `lean_verify` on `d4_axiom_sound`, `d4_soundness`, `d4_soundness_derivable` confirms no axiom usage

---

### Phase 2: D4 Completeness + Module Integration [COMPLETED]

**Goal**: Prove completeness for D4 over serial + transitive frames using D-specific truth lemma and canonical frame properties; update module aggregator.

**Tasks**:
- [x] **Task 2.1**: Create `Cslib/Logics/Modal/Metalogic/D4Completeness.lean` importing `Completeness` and `DCompleteness`
- [x] **Task 2.2**: Prove `d4_completeness` following the d_completeness pattern (DCompleteness.lean:382-451) with these key differences:
  - Consistency argument: identical boilerplate using D4Axiom constructors (~30 lines, adapt from d_completeness)
  - Canonical seriality: instantiate `canonical_serial` at D4Axiom constructors (.implyK, .implyS, .efq, .modalK, .modalD)
  - Canonical transitivity: instantiate `canonical_trans` at D4Axiom constructors (.implyK, .implyS, .modalFour)
  - Truth lemma: instantiate `truth_lemma_d` at D4Axiom constructors (.implyK, .implyS, .efq, .peirce, .modalK, .modalD)
  - Validity hypothesis takes both Relation.Serial and transitivity
  - Final contradiction via `mcs_not_mem_of_neg`
- [x] **Task 2.3**: Update `Cslib/Logics/Modal/Metalogic.lean` to add imports for D4Soundness and D4Completeness
- [x] **Task 2.4**: Run `lake build Cslib.Logics.Modal.Metalogic` to verify full module builds
- [x] **Task 2.5**: Verify no sorries: `grep -r sorry Cslib/Logics/Modal/Metalogic/D4Completeness.lean`

**Timing**: 1 hour 15 minutes

**Depends on**: 1

**Files to create**:
- `Cslib/Logics/Modal/Metalogic/D4Completeness.lean` -- ~80 lines: d4_completeness theorem

**Files to modify**:
- `Cslib/Logics/Modal/Metalogic.lean` -- add two public import lines for D4Soundness and D4Completeness

**Verification**:
- `lake build Cslib.Logics.Modal.Metalogic` passes with zero errors
- `grep -r sorry Cslib/Logics/Modal/Metalogic/D4Completeness.lean` returns no matches
- `lean_verify` on `d4_completeness` confirms no axiom usage
- All existing tests continue to pass (no regressions)

## Testing & Validation

- [ ] `lake build Cslib.Logics.Modal.Metalogic.D4Soundness` -- soundness file compiles
- [ ] `lake build Cslib.Logics.Modal.Metalogic.D4Completeness` -- completeness file compiles
- [ ] `lake build Cslib.Logics.Modal.Metalogic` -- full module aggregator compiles
- [ ] Zero sorry occurrences in D4Soundness.lean and D4Completeness.lean
- [ ] `lean_verify` passes for d4_axiom_sound, d4_soundness, d4_soundness_derivable, d4_completeness
- [ ] No build regressions in existing modules

## Artifacts & Outputs

- `Cslib/Logics/Modal/Metalogic/D4Soundness.lean` -- soundness theorem for D4 over serial + transitive frames
- `Cslib/Logics/Modal/Metalogic/D4Completeness.lean` -- completeness theorem for D4 over serial + transitive frames
- `Cslib/Foundations/Logic/ProofSystem.lean` -- (modified) HilbertD4 tag type + ModalD4Hilbert bundled class
- `Cslib/Logics/Modal/ProofSystem/Instances.lean` -- (modified) D4Axiom + instance registrations
- `Cslib/Logics/Modal/Metalogic.lean` -- (modified) import aggregator updated

## Rollback/Contingency

All changes are additive (new files + new definitions appended to existing files). Rollback by:
1. Delete `D4Soundness.lean` and `D4Completeness.lean`
2. Remove the D4-related additions from ProofSystem.lean (tag type + bundled class)
3. Remove D4Axiom and instance registrations from Instances.lean
4. Remove the two import lines from Metalogic.lean
No existing code is modified, only extended.
