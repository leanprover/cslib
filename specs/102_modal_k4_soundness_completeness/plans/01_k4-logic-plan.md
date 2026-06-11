# Implementation Plan: Task #102 -- Modal K4 Soundness and Completeness

- **Task**: 102 - Modal K4 Soundness and Completeness
- **Status**: [NOT STARTED]
- **Effort**: 3 hours
- **Dependencies**: None (task 100 infrastructure added inline)
- **Research Inputs**: specs/102_modal_k4_soundness_completeness/reports/01_k4-logic-research.md
- **Artifacts**: plans/01_k4-logic-plan.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: lean4
- **Lean Intent**: true

## Overview

Prove soundness and completeness for modal logic K4 (K + axiom 4) over transitive frames. K4 has the 4 propositional axioms, K distribution, and axiom 4 (`box phi -> box (box phi)`) but lacks axiom T. This means soundness follows S4Soundness.lean (minus the reflexivity case) and completeness must use `k_truth_lemma` (from KCompleteness.lean, which does not require axiom T) combined with `canonical_trans` (from Completeness.lean, which requires only axiom 4). Since task 100 (shared infrastructure) is not started, K4-specific infrastructure (K4Axiom predicate, HilbertK4 tag type, bundled class, and instance registrations) is added as Phase 1.

### Research Integration

The research report (01_k4-logic-research.md) confirms:
- K4 reuses the K truth lemma exactly (both lack axiom T)
- The only addition over K completeness is `canonical_trans` for the frame property
- Soundness is a direct copy of S4Soundness with the modalT case removed and h_refl removed
- All required infrastructure (`k_truth_lemma`, `canonical_trans`, `soundness`, `soundness_derivable`) already exists
- K4Axiom needs 6 constructors: 4 propositional + modalK + modalFour

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No ROADMAP.md found.

## Goals & Non-Goals

**Goals**:
- Define K4Axiom inductive predicate with 6 constructors in Instances.lean
- Add HilbertK4 tag type in ProofSystem.lean and ModalK4Hilbert bundled class
- Register all typeclass instances for HilbertK4
- Prove `k4_axiom_sound`: each K4 axiom is valid on transitive frames
- Prove `k4_soundness` and `k4_soundness_derivable`: parametric wrappers
- Prove `k4_completeness`: completeness via canonical model with `k_truth_lemma` + `canonical_trans`
- Add imports to Metalogic.lean aggregator
- Verify with `lake build`

**Non-Goals**:
- Proving completeness for other modal cube systems (tasks 101, 103-111)
- Adding all 10 axiom predicates from task 100 (only K4 is added here)
- Modifying existing soundness/completeness infrastructure

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| K4Axiom conflicts with future task 100 bulk addition | M | M | Define K4Axiom in same location (Instances.lean) so task 100 can skip it or merge cleanly |
| `k_truth_lemma` instantiation mismatch | L | L | K4Axiom constructor names match KAxiom pattern exactly; verified in research |
| Consistency proof boilerplate errors | L | M | Copy directly from KCompleteness.lean, changing only axiom constructor names |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3 | 2 |

Phases within the same wave can execute in parallel.

### Phase 1: K4 Infrastructure (K4Axiom + HilbertK4 + Instances) [COMPLETED]

**Goal**: Define the K4Axiom predicate, HilbertK4 tag type, ModalK4Hilbert bundled class, and register all typeclass instances so that K4Soundness.lean and K4Completeness.lean can reference them.

**Tasks**:
- [x] Add `K4Axiom` inductive type to `Cslib/Logics/Modal/ProofSystem/Instances.lean` *(completed by task 100)*
- [x] Add `opaque Modal.HilbertK4 : Type := Empty` to `Cslib/Foundations/Logic/ProofSystem.lean` *(completed by task 100)*
- [x] Add `ModalK4Hilbert` bundled class to `Cslib/Foundations/Logic/ProofSystem.lean` *(completed by task 100)*
- [x] Add instance registrations for `HilbertK4` in `Cslib/Logics/Modal/ProofSystem/Instances.lean` *(completed by task 100)*
- [x] Verify with `lake build Cslib.Logics.Modal.ProofSystem.Instances` *(completed by task 100)*

**Timing**: 45 minutes

**Depends on**: none

**Files to modify**:
- `Cslib/Foundations/Logic/ProofSystem.lean` - Add HilbertK4 tag type and ModalK4Hilbert class
- `Cslib/Logics/Modal/ProofSystem/Instances.lean` - Add K4Axiom predicate and instance registrations

**Verification**:
- `lake build Cslib.Logics.Modal.ProofSystem.Instances` compiles without errors
- `K4Axiom` type has exactly 6 constructors
- All 11 instances registered and resolve correctly

---

### Phase 2: K4 Soundness and Completeness Proofs [COMPLETED]

**Goal**: Create K4Soundness.lean and K4Completeness.lean with the core theorems.

**Tasks**:
- [x] Create `Cslib/Logics/Modal/Metalogic/K4Soundness.lean`
- [x] Create `Cslib/Logics/Modal/Metalogic/K4Completeness.lean`
- [x] Verify each file compiles: `lake build Cslib.Logics.Modal.Metalogic.K4Soundness` and `lake build Cslib.Logics.Modal.Metalogic.K4Completeness`

**Timing**: 1.5 hours

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/Modal/Metalogic/K4Soundness.lean` - New file (~50 lines)
- `Cslib/Logics/Modal/Metalogic/K4Completeness.lean` - New file (~120 lines)

**Verification**:
- Both files compile without errors or warnings
- `k4_axiom_sound` handles all 6 K4Axiom cases
- `k4_completeness` uses `k_truth_lemma` (not `truth_lemma`) and `canonical_trans`
- No `sorry` or vacuous definitions
- `lean_verify` on `k4_soundness`, `k4_soundness_derivable`, `k4_completeness` shows no axioms used

---

### Phase 3: Integration and Final Verification [NOT STARTED]

**Goal**: Add K4 imports to the module aggregator and verify the full build.

**Tasks**:
- [ ] Add to `Cslib/Logics/Modal/Metalogic.lean` (after S4Completeness import):
  ```
  public import Cslib.Logics.Modal.Metalogic.K4Soundness
  public import Cslib.Logics.Modal.Metalogic.K4Completeness
  ```
- [ ] Update module docstring to mention K4 alongside K, T, D, S4, S5
- [ ] Run `lake build` to verify full project builds
- [ ] Run `lean_verify` on `Cslib.Logic.Modal.k4_soundness`, `Cslib.Logic.Modal.k4_soundness_derivable`, `Cslib.Logic.Modal.k4_completeness` to confirm no sorry/axioms

**Timing**: 30 minutes

**Depends on**: 2

**Files to modify**:
- `Cslib/Logics/Modal/Metalogic.lean` - Add K4Soundness and K4Completeness imports; update docstring

**Verification**:
- `lake build` passes with zero errors
- `lean_verify` confirms no sorry or axioms in K4 theorems
- Module aggregator includes all K4 imports

## Testing & Validation

- [ ] `lake build Cslib.Logics.Modal.ProofSystem.Instances` -- K4 infrastructure compiles
- [ ] `lake build Cslib.Logics.Modal.Metalogic.K4Soundness` -- K4 soundness compiles
- [ ] `lake build Cslib.Logics.Modal.Metalogic.K4Completeness` -- K4 completeness compiles
- [ ] `lake build` -- full project builds without errors
- [ ] `lean_verify` on `k4_soundness`, `k4_soundness_derivable`, `k4_completeness` -- no sorry/axioms
- [ ] `grep -rn sorry Cslib/Logics/Modal/Metalogic/K4Soundness.lean Cslib/Logics/Modal/Metalogic/K4Completeness.lean` -- zero matches

## Artifacts & Outputs

- `Cslib/Logics/Modal/Metalogic/K4Soundness.lean` -- K4 soundness theorem (~50 lines)
- `Cslib/Logics/Modal/Metalogic/K4Completeness.lean` -- K4 completeness theorem (~120 lines)
- `Cslib/Foundations/Logic/ProofSystem.lean` -- HilbertK4 tag type + ModalK4Hilbert class (additions)
- `Cslib/Logics/Modal/ProofSystem/Instances.lean` -- K4Axiom + instance registrations (additions)
- `Cslib/Logics/Modal/Metalogic.lean` -- Updated module aggregator (additions)

## Rollback/Contingency

All changes are additive (new files + additions to existing files). Rollback:
1. Delete `K4Soundness.lean` and `K4Completeness.lean`
2. Revert additions to `Instances.lean`, `ProofSystem.lean`, and `Metalogic.lean`
3. No existing functionality is modified, so rollback has zero risk to existing code
