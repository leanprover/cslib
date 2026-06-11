# Implementation Plan: Task #106

- **Task**: 106 - Modal KB5 Soundness and Completeness
- **Status**: [NOT STARTED]
- **Effort**: 3 hours
- **Dependencies**: Task 100 (modal cube shared infrastructure -- canonical_symm, canonical_eucl_from_5, KB5Axiom, HilbertKB5)
- **Research Inputs**: specs/106_modal_kb5_soundness_completeness/reports/01_kb5-logic-research.md
- **Artifacts**: plans/01_kb5-logic-plan.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: lean4
- **Lean Intent**: true

## Overview

Prove soundness and completeness for modal logic KB5 (K + B + 5) over symmetric + Euclidean frames. KB5 is axiomatized by the K distribution axiom, the B symmetry axiom (phi -> box(diamond phi)), and the 5 Euclidean axiom (diamond phi -> box(diamond phi)). This is the first logic in the modal cube that combines BOTH new canonical lemmas from task 100: `canonical_symm` (symmetry from axiom B alone) and `canonical_eucl_from_5` (Euclideanness from axiom 5 alone). KB5 does NOT have axiom T, so the completeness proof uses `k_truth_lemma` (K-style, no reflexivity) rather than the S5-style `truth_lemma`.

### Research Integration

The research report (01_kb5-logic-research.md) provides:
- Complete `KB5Axiom` inductive definition with 7 constructors (4 propositional + 3 modal: K, B, Five)
- Detailed soundness proof strategy: case analysis on `h_ax` with explicit `h_symm` for B and `h_eucl` for Five
- Completeness proof structure: contrapositive via `k_truth_lemma` + `canonical_symm` + `canonical_eucl_from_5`
- Confirmation that K-style truth lemma (no `h_T`) is the correct choice since KB5 lacks axiom T
- BRV Chapter 4 citations: Definition 4.9 (soundness), Theorem 4.28 clause 2 (B canonicity), Theorem 4.22 pattern (completeness)

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No ROADMAP.md found.

## Goals & Non-Goals

**Goals**:
- Create `KB5Soundness.lean` with `kb5_axiom_sound`, `kb5_soundness`, `kb5_soundness_derivable`
- Create `KB5Completeness.lean` with `kb5_completeness`
- Update `Metalogic.lean` module aggregator with new imports
- All theorems sorry-free with `lean_verify` confirmation

**Non-Goals**:
- Implementing `canonical_symm` or `canonical_eucl_from_5` (task 100 scope)
- Implementing `KB5Axiom` inductive type (task 100 scope)
- Implementing `HilbertKB5` tag type or typeclass instances (task 100 scope)
- Bundled typeclass proofs for KB5 (future task)

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Task 100 not yet complete -- `canonical_symm` / `canonical_eucl_from_5` unavailable | H | M | Soundness can proceed independently; completeness blocked until task 100 delivers. If blocked, define KB5Axiom locally in soundness file. |
| Signature mismatch on `canonical_symm` / `canonical_eucl_from_5` | M | L | Research report details expected signatures; adapt instantiation if parameter order differs. |
| `k_truth_lemma` parameter instantiation issues | L | L | Pattern is identical to `KCompleteness.lean` -- direct copy with constructor name changes. |
| Axiom 5 soundness proof tricky with raw diamond encoding | M | L | Research report provides detailed step-by-step proof; `apply`/`intro`/`exact` with `h_eucl` transfer. |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |

Phases within the same wave can execute in parallel.

### Phase 1: KB5 Soundness [COMPLETED]

**Goal**: Create `KB5Soundness.lean` proving every KB5 axiom is valid on symmetric + Euclidean frames, and wrapping with the parameterized `soundness` theorem.

**Tasks**:
- [x] Create `Cslib/Logics/Modal/Metalogic/KB5Soundness.lean` with module header
- [x] Define `KB5Axiom` locally if not yet available from task 100 (7 constructors: implyK, implyS, efq, peirce, modalK, modalB, modalFive) *(deviation: skipped -- KB5Axiom already available from task 100 in Instances.lean)*
- [x] Prove `kb5_axiom_sound`: case analysis on `h_ax` with frame hypotheses `h_symm : forall w1 w2, m.r w1 w2 -> m.r w2 w1` and `h_eucl : forall w1 w2 w3, m.r w1 w2 -> m.r w1 w3 -> m.r w2 w3`
  - Propositional cases (implyK, implyS, efq, peirce): identical to all other logics
  - modalK case: identical to all other logics
  - modalB case: `intro h_phi w' hr h_box_neg; exact h_box_neg w (h_symm w w' hr) h_phi`
  - modalFive case: `intro h_diam w' hr h_box_neg_w'; apply h_diam; intro w'' hr'' h_phi; exact h_box_neg_w' w'' (h_eucl w w' w'' hr hr'') h_phi`
- [x] Prove `kb5_soundness`: wrapper using parameterized `soundness` theorem
- [x] Prove `kb5_soundness_derivable`: wrapper using `soundness_derivable`
- [x] Verify with `lean_goal` at key proof positions
- [x] Run `lake build Cslib.Logics.Modal.Metalogic.KB5Soundness`

**Timing**: 1 hour

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Modal/Metalogic/KB5Soundness.lean` - new file (soundness theorems)

**Verification**:
- `lake build Cslib.Logics.Modal.Metalogic.KB5Soundness` passes with zero errors
- `lean_verify` confirms no sorry or axiom usage in `kb5_axiom_sound`, `kb5_soundness`, `kb5_soundness_derivable`

---

### Phase 2: KB5 Completeness + Module Integration [NOT STARTED]

**Goal**: Create `KB5Completeness.lean` proving completeness for KB5 via the canonical model construction using `k_truth_lemma`, `canonical_symm`, and `canonical_eucl_from_5`. Update the `Metalogic.lean` aggregator.

**Tasks**:
- [ ] Create `Cslib/Logics/Modal/Metalogic/KB5Completeness.lean` with module header
- [ ] Import `KCompleteness` (for `k_truth_lemma`), `Completeness` (for `canonical_symm`, `canonical_eucl_from_5`, `CanonicalModel`, `CanonicalWorld`), and `Instances`
- [ ] Prove `kb5_completeness`:
  - Contrapositive setup: `by_contra h_not_deriv`
  - Show `{neg phi}` is KB5-consistent (standard double-negation elimination via implyK, implyS, efq, peirce -- identical pattern to K/S4/D completeness proofs)
  - Lindenbaum extension: `obtain <M, hM_sup, hM_mcs> := modal_lindenbaum h_cons`
  - Canonical world: `let w : CanonicalWorld (@KB5Axiom Atom) := <M, hM_mcs>`
  - Apply `k_truth_lemma` instantiated at KB5Axiom constructors (implyK, implyS, efq, peirce, modalK)
  - Apply `h_valid` with frame property proofs:
    - Symmetry via `canonical_symm` instantiated at KB5Axiom.modalB
    - Euclideanness via `canonical_eucl_from_5` instantiated at KB5Axiom.modalFive
  - Contradiction via `mcs_not_mem_of_neg`
- [ ] Verify `kb5_completeness` with `lean_goal` at key positions
- [ ] Update `Cslib/Logics/Modal/Metalogic.lean` to add:
  - `public import Cslib.Logics.Modal.Metalogic.KB5Soundness`
  - `public import Cslib.Logics.Modal.Metalogic.KB5Completeness`
- [ ] Run `lake build Cslib.Logics.Modal.Metalogic.KB5Completeness`
- [ ] Run `lake build Cslib.Logics.Modal.Metalogic` (full module)
- [ ] `lean_verify` on `kb5_completeness`

**Timing**: 2 hours

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/Modal/Metalogic/KB5Completeness.lean` - new file (completeness theorem)
- `Cslib/Logics/Modal/Metalogic.lean` - add 2 new import lines

**Verification**:
- `lake build Cslib.Logics.Modal.Metalogic` passes with zero errors
- `lean_verify` confirms no sorry or axiom usage in `kb5_completeness`
- `grep -r sorry Cslib/Logics/Modal/Metalogic/KB5Soundness.lean Cslib/Logics/Modal/Metalogic/KB5Completeness.lean` returns empty

## Testing & Validation

- [ ] `lake build Cslib.Logics.Modal.Metalogic.KB5Soundness` -- zero errors
- [ ] `lake build Cslib.Logics.Modal.Metalogic.KB5Completeness` -- zero errors
- [ ] `lake build Cslib.Logics.Modal.Metalogic` -- full module aggregator passes
- [ ] `lean_verify Cslib.Logic.Modal.kb5_axiom_sound` -- no sorry, no axiom
- [ ] `lean_verify Cslib.Logic.Modal.kb5_soundness` -- no sorry, no axiom
- [ ] `lean_verify Cslib.Logic.Modal.kb5_soundness_derivable` -- no sorry, no axiom
- [ ] `lean_verify Cslib.Logic.Modal.kb5_completeness` -- no sorry, no axiom
- [ ] No `sorry` occurrences in either new file

## Artifacts & Outputs

- `Cslib/Logics/Modal/Metalogic/KB5Soundness.lean` -- KB5 soundness theorems
- `Cslib/Logics/Modal/Metalogic/KB5Completeness.lean` -- KB5 completeness theorem
- `Cslib/Logics/Modal/Metalogic.lean` -- updated module aggregator (2 new imports)
- `specs/106_modal_kb5_soundness_completeness/plans/01_kb5-logic-plan.md` -- this plan
- `specs/106_modal_kb5_soundness_completeness/summaries/01_kb5-logic-summary.md` -- implementation summary (created during /implement)

## Rollback/Contingency

- If task 100 is not complete when implementation begins:
  - Phase 1 can proceed by defining `KB5Axiom` locally in `KB5Soundness.lean` (self-contained, following the `KAxiom` pattern)
  - Phase 2 will be BLOCKED until `canonical_symm` and `canonical_eucl_from_5` are available
  - Mark phase 2 as `[BLOCKED]` with dependency note
- If `canonical_symm` / `canonical_eucl_from_5` signatures differ from research expectations:
  - Adapt the instantiation in `kb5_completeness` to match actual parameters
  - The core proof structure is unchanged; only the lambda wrapper for constructor matching changes
- Full rollback: `git revert` the implementation commit; no other files are modified
