# Implementation Plan: Task #104 -- Modal K45 Soundness and Completeness

- **Task**: 104 - Modal K45 Soundness and Completeness
- **Status**: [NOT STARTED]
- **Effort**: 3 hours
- **Dependencies**: Task 100 (modal cube shared infrastructure) -- soft dependency, mitigated by inline definitions
- **Research Inputs**: specs/104_modal_k45_soundness_completeness/reports/01_k45-logic-research.md
- **Artifacts**: plans/01_k45-logic-plan.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: lean4
- **Lean Intent**: true

## Overview

Prove soundness and completeness for modal logic K45 (K + axiom 4 + axiom 5) over transitive and Euclidean frames, following the completeness-via-canonicity method from Blackburn et al. Chapter 4. K45 lacks axiom T, so the completeness proof must use `k_truth_lemma` (from KCompleteness.lean) instead of `truth_lemma` (which requires T). Soundness validates axiom 4 on transitive frames and axiom 5 on Euclidean frames. Completeness combines `k_truth_lemma` + `canonical_trans` + a new `canonical_eucl_from_5` lemma that derives Euclideanness from axiom 5 alone.

### Research Integration

Key findings from the research report integrated into this plan:

- K45 uses `k_truth_lemma` (not `truth_lemma`) because there is no axiom T (Section 5 of report)
- `canonical_eucl_from_5` proof uses the diamond characterization of the canonical relation: from R(S,U) and phi in U, derive diamond phi in S; apply axiom 5 to get box diamond phi in S; from R(S,T), conclude diamond phi in T (Section 4 of report)
- The `modalFive` soundness case follows the `Satisfies.five` pattern from Basic.lean line 329 (Section 2 of report)
- Task 100 dependency is soft: K45Axiom definition and canonical_eucl_from_5 can be proved inline (~35 lines total) to avoid blocking

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No ROADMAP.md found.

## Goals & Non-Goals

**Goals**:
- Define `K45Axiom` inductive type with 7 constructors (4 propositional + K + 4 + 5)
- Prove `k45_axiom_sound`: every K45 axiom is valid on transitive + Euclidean frames
- Prove `k45_soundness` and `k45_soundness_derivable`: compositional soundness theorems
- Prove `canonical_eucl_from_5`: Euclideanness of canonical frame from axiom 5 alone
- Prove `k45_completeness`: if phi valid on all transitive + Euclidean frames, then K45-derivable
- Add `HilbertK45` tag type and typeclass instances
- Register new files in Metalogic.lean barrel

**Non-Goals**:
- Modifying existing shared infrastructure in Completeness.lean or MCS.lean (that is task 100 scope)
- Proving properties for other modal logics in the K45 family (KB, K4B, etc.)
- Adding semantic frame condition typeclasses beyond what exists

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Task 100 completes first and defines K45Axiom/HilbertK45 differently | M | L | If task 100 lands first, refactor to use its definitions; if this task lands first, task 100 can reuse our K45Axiom |
| `canonical_eucl_from_5` proof has unexpected complexity in Lean encoding | M | L | The proof is ~15 lines following BRV; the diamond encoding is well-understood from existing `mcs_box_diamond` |
| `modalFive` soundness case encoding issues with double-negation diamond | L | L | Research report Section 2 worked out the exact unfolded proof term |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |

Phases within the same wave can execute in parallel.

---

### Phase 1: K45 Soundness [COMPLETED]

**Goal**: Create K45Axiom definition and prove soundness of all K45 axioms over transitive + Euclidean frames.

**Tasks**:
- [x] **Task 1.1**: Define `K45Axiom` inductive type in `Instances.lean` with 7 constructors *(deviation: skipped -- already completed by task 100)*
- [x] **Task 1.2**: Add `HilbertK45` opaque tag type in `ProofSystem.lean` *(deviation: skipped -- already completed by task 100)*
- [x] **Task 1.3**: Add `ModalK45Hilbert` bundled class in `ProofSystem.lean` *(deviation: skipped -- already completed by task 100)*
- [x] **Task 1.4**: Register typeclass instances for K45 in `Instances.lean` *(deviation: skipped -- already completed by task 100)*
- [x] **Task 1.5**: Create `K45Soundness.lean` with `k45_axiom_sound`, `k45_soundness`, `k45_soundness_derivable` *(completed)*

**Timing**: 1.5 hours

**Depends on**: none

**Files to modify**:
- `Cslib/Foundations/Logic/ProofSystem.lean` -- add `HilbertK45` tag type and `ModalK45Hilbert` class
- `Cslib/Logics/Modal/ProofSystem/Instances.lean` -- add `K45Axiom` inductive and instances
- `Cslib/Logics/Modal/Metalogic/K45Soundness.lean` -- create new file

**Verification**:
- `lake build Cslib.Logics.Modal.Metalogic.K45Soundness` compiles without errors or sorries
- `lean_verify` confirms no axiom usage beyond the standard foundations

---

### Phase 2: K45 Completeness [COMPLETED]

**Goal**: Prove `canonical_eucl_from_5` and the K45 completeness theorem, then register imports.

**Tasks**:
- [x] **Task 2.1**: Create `K45Completeness.lean` importing KCompleteness and Completeness *(completed)*
- [x] **Task 2.2**: Prove `canonical_eucl_from_5` *(deviation: skipped -- already completed by task 100 in Completeness.lean; reused via import)*
- [x] **Task 2.3**: Prove `k45_completeness` using `k_truth_lemma` + `canonical_trans` + `canonical_eucl_from_5` *(completed)*
- [x] **Task 2.4**: Add imports to `Metalogic.lean` barrel file *(completed)*
- [x] **Task 2.5**: Run `lake build` to verify full project compilation *(completed -- 2936 jobs, no errors)*

**Timing**: 1.5 hours

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/Modal/Metalogic/K45Completeness.lean` -- create new file
- `Cslib/Logics/Modal/Metalogic.lean` -- add K45 imports to barrel file

**Verification**:
- `lake build Cslib.Logics.Modal.Metalogic.K45Completeness` compiles without errors or sorries
- `lake build` full project passes
- `lean_verify` on `k45_completeness` and `k45_soundness_derivable` confirms no axiom leaks

## Testing & Validation

- [ ] `lake build Cslib.Logics.Modal.Metalogic.K45Soundness` -- soundness module compiles
- [ ] `lake build Cslib.Logics.Modal.Metalogic.K45Completeness` -- completeness module compiles
- [ ] `lake build` -- full project compiles with new imports
- [ ] `lean_verify Cslib.Logic.Modal.k45_axiom_sound` -- no sorry, no unexpected axioms
- [ ] `lean_verify Cslib.Logic.Modal.k45_completeness` -- no sorry, no unexpected axioms
- [ ] `lean_verify Cslib.Logic.Modal.canonical_eucl_from_5` -- no sorry, no unexpected axioms

## Artifacts & Outputs

- `Cslib/Logics/Modal/ProofSystem/Instances.lean` -- K45Axiom definition + typeclass instances
- `Cslib/Foundations/Logic/ProofSystem.lean` -- HilbertK45 tag type + ModalK45Hilbert class
- `Cslib/Logics/Modal/Metalogic/K45Soundness.lean` -- new file (~60 lines)
- `Cslib/Logics/Modal/Metalogic/K45Completeness.lean` -- new file (~120 lines)
- `Cslib/Logics/Modal/Metalogic.lean` -- updated barrel imports

## Rollback/Contingency

If implementation fails:
- Delete the two new files (K45Soundness.lean, K45Completeness.lean)
- Revert changes to Instances.lean, ProofSystem.lean, and Metalogic.lean
- `git checkout` the modified files to restore original state
- If `canonical_eucl_from_5` proves intractable inline, mark task [BLOCKED] on task 100 and wait for shared infrastructure
