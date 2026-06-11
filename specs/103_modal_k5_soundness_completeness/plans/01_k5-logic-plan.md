# Implementation Plan: Task #103 -- Modal K5 Soundness and Completeness

- **Task**: 103 - Modal K5 Soundness and Completeness
- **Status**: [NOT STARTED]
- **Effort**: 3 hours
- **Dependencies**: Task 100 (shared infrastructure) for K5Axiom predicate; if incomplete, define K5Axiom locally
- **Research Inputs**: specs/103_modal_k5_soundness_completeness/reports/01_k5-logic-research.md
- **Artifacts**: plans/01_k5-logic-plan.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: lean4
- **Lean Intent**: true

## Overview

Prove soundness and completeness for modal logic K5 (K + axiom 5: diamond(phi) -> box(diamond(phi))) over Euclidean frames. This requires creating two new files: K5Soundness.lean and K5Completeness.lean in `Cslib/Logics/Modal/Metalogic/`. Soundness follows the established DSoundness pattern with one new modal case (modalFive). Completeness follows the KCompleteness pattern (using `k_truth_lemma` since K5 lacks axiom T), with the key new content being `canonical_eucl_from_5` -- proving the canonical relation is Euclidean from axiom 5 alone.

### Research Integration

The research report (01_k5-logic-research.md) provides:
- **K5Axiom structure**: 6 constructors (4 propositional + modalK + modalFive), matching the DAxiom pattern
- **Soundness strategy**: Manual proof for modalFive case using explicit Euclideanness hypothesis (not typeclass), ~5 lines
- **Completeness strategy**: Contrapositive argument using `canonical_eucl_from_5` + `k_truth_lemma`
- **canonical_eucl_from_5 proof**: Detailed MCS-level proof requiring derivation tree construction for DNI inside box, axiom 5 application, and contradiction assembly; estimated ~40-60 lines
- **Truth lemma choice**: K5 uses `k_truth_lemma` (no axiom T or D needed)
- **Task 100 dependency**: K5Axiom can be defined locally if task 100 is not yet done (task 100 status: researched, not implemented)

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No ROADMAP.md found.

## Goals & Non-Goals

**Goals**:
- Prove `k5_axiom_sound`: every K5 axiom is valid on Euclidean frames
- Prove `k5_soundness` and `k5_soundness_derivable`: parameterized soundness wrappers
- Prove `canonical_eucl_from_5`: the canonical relation is Euclidean from axiom 5 alone
- Prove `k5_completeness`: if phi is valid on all Euclidean frames, then phi is K5-derivable
- Define K5Axiom locally if task 100 has not yet added it to Instances.lean

**Non-Goals**:
- Modifying existing infrastructure files (Soundness.lean, KCompleteness.lean, etc.)
- Adding HilbertK5 tag type or bundled class instances (task 100 scope)
- Proving properties about K5 beyond soundness and completeness
- Creating a new truth lemma variant (k_truth_lemma is reused directly)

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| canonical_eucl_from_5 derivation tree complexity | M | M | Follow existing canonical_eucl pattern (lines 95-141 of Completeness.lean); use mcs_mp_axiom, derive_box_from_box_context helpers |
| Diamond encoding (neg neg phi vs phi under box) | M | M | Build explicit DNI derivation tree as documented in research; the pattern is standard (~10 lines) |
| Task 100 not done (no K5Axiom in Instances.lean) | L | H | Define K5Axiom locally in K5Soundness.lean; K5Completeness imports K5Soundness |
| Soundness proof for modalFive case | L | L | Research provides explicit 5-line proof sketch; follows DSoundness.modalD pattern |
| DNE consistency boilerplate in completeness | L | L | Direct copy from KCompleteness lines 274-307 with K5Axiom substitution |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |

Phases within the same wave can execute in parallel.

---

### Phase 1: K5Soundness.lean [COMPLETED]

**Goal**: Create K5Soundness.lean with K5Axiom definition (if needed), axiom soundness, and parameterized soundness wrappers.

**Tasks**:
- [x] Check if K5Axiom exists in Instances.lean; if not, define it locally in K5Soundness.lean with 6 constructors (implyK, implyS, efq, peirce, modalK, modalFive) *(deviation: skipped -- K5Axiom already exists in Instances.lean from task 100)*
- [x] Implement `k5_axiom_sound`: prove each K5 axiom valid on Euclidean frames
  - Cases implyK, implyS, efq, peirce, modalK: identical to `k_axiom_sound` (no frame condition needed)
  - Case modalFive: prove diamond(phi) -> box(diamond(phi)) on Euclidean frames using explicit `h_eucl` hypothesis; the proof unfolds to showing `(forall w'', R w w'' -> phi at w'' -> False) -> False` implies `forall w', R w w' -> (forall w'', R w' w'' -> phi at w'' -> False) -> False`, using Euclideanness to transfer the witness
- [x] Implement `k5_soundness`: wrapper calling `soundness` with `k5_axiom_sound`
- [x] Implement `k5_soundness_derivable`: wrapper calling `soundness_derivable` with `k5_axiom_sound`
- [x] Verify with `lake build Cslib.Logics.Modal.Metalogic.K5Soundness`

**Timing**: 45 minutes

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Modal/Metalogic/K5Soundness.lean` - Create new file (~60-70 lines)

**Verification**:
- `lake build Cslib.Logics.Modal.Metalogic.K5Soundness` succeeds with no errors or sorries
- `lean_verify` confirms no sorry or axiom usage beyond standard foundations

---

### Phase 2: K5Completeness.lean [NOT STARTED]

**Goal**: Create K5Completeness.lean with `canonical_eucl_from_5` and the completeness theorem.

**Tasks**:
- [ ] Implement `canonical_eucl_from_5`: prove canonical relation is Euclidean from axiom 5
  - Given R(w,v) and R(w,u) (Lemma 4.19 form: forall phi, box phi in S -> phi in T)
  - Take box(phi) in v, show phi in u
  - By contradiction: assume phi not in u, so neg(phi) = (phi -> bot) in u
  - From R(w,u) and (phi -> bot) in u, derive diamond(phi -> bot) in w (contrapositive of canonical relation using MCS properties)
  - Apply axiom 5 to (phi -> bot): diamond(phi -> bot) -> box(diamond(phi -> bot)) in w, so box(diamond(phi -> bot)) in w
  - From R(w,v): diamond(phi -> bot) in v
  - From box(phi) in v, derive box(neg(neg(phi))) in v via DNI inside box (build derivation tree: phi -> ((phi->bot)->bot) is tautology, NEC + K gives box(phi) -> box((phi->bot)->bot))
  - diamond(phi -> bot) in v = (box((phi->bot)->bot) -> bot) in v, combined with box((phi->bot)->bot) in v gives bot in v -- contradiction
- [ ] Implement helper `mcs_mem_diamond_of_canonical_rel`: given R(w,u) and psi in u, derive diamond(psi) in w (reusable helper for the canonical_eucl_from_5 proof)
- [ ] Implement `k5_completeness`: completeness theorem following KCompleteness/DCompleteness pattern
  - Contrapositive: assume not derivable
  - {neg phi} is K5-consistent (DNE boilerplate, copied from KCompleteness)
  - Lindenbaum gives MCS M containing neg phi
  - Canonical model is Euclidean via canonical_eucl_from_5
  - Apply validity hypothesis to canonical model
  - Apply k_truth_lemma to get phi in M
  - Contradiction with neg phi in M
- [ ] Verify with `lake build Cslib.Logics.Modal.Metalogic.K5Completeness`

**Timing**: 2 hours

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/Modal/Metalogic/K5Completeness.lean` - Create new file (~150-180 lines)

**Verification**:
- `lake build Cslib.Logics.Modal.Metalogic.K5Completeness` succeeds with no errors or sorries
- `lean_verify` confirms no sorry or axiom usage beyond standard foundations
- Both K5Soundness and K5Completeness build together: `lake build`

## Testing & Validation

- [ ] `lake build Cslib.Logics.Modal.Metalogic.K5Soundness` passes
- [ ] `lake build Cslib.Logics.Modal.Metalogic.K5Completeness` passes
- [ ] Full project `lake build` passes with no regressions
- [ ] `lean_verify` on `k5_axiom_sound`, `k5_soundness`, `k5_soundness_derivable`, `canonical_eucl_from_5`, `k5_completeness` -- all axiom-free (no sorry)
- [ ] K5Axiom has exactly 6 constructors matching the research specification
- [ ] k5_completeness uses `k_truth_lemma` (not `truth_lemma` or `truth_lemma_d`)

## Artifacts & Outputs

- `Cslib/Logics/Modal/Metalogic/K5Soundness.lean` - Soundness for K5 over Euclidean frames
- `Cslib/Logics/Modal/Metalogic/K5Completeness.lean` - Completeness for K5 over Euclidean frames
- `specs/103_modal_k5_soundness_completeness/plans/01_k5-logic-plan.md` - This plan

## Rollback/Contingency

Both files are new additions with no modifications to existing code. Rollback is trivial: delete K5Soundness.lean and K5Completeness.lean. If canonical_eucl_from_5 proves intractable, the phase can be marked [BLOCKED] with the specific derivation tree construction that fails documented. In that case, the soundness file (Phase 1) remains valid independently.
