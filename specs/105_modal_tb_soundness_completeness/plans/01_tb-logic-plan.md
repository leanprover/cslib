# Implementation Plan: Task #105 - Modal TB Soundness and Completeness

- **Task**: 105 - Modal TB Soundness and Completeness
- **Status**: [NOT STARTED]
- **Effort**: 3 hours
- **Dependencies**: Task 100 (modal cube shared infrastructure -- provides TBAxiom, canonical_symm, HilbertTB tag, ModalTBHilbert class, TB typeclass instances)
- **Research Inputs**: specs/105_modal_tb_soundness_completeness/reports/01_tb-logic-research.md
- **Artifacts**: plans/01_tb-logic-plan.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: lean4
- **Lean Intent**: true

## Overview

Prove soundness and completeness for modal logic TB (K + T + B) over reflexive and symmetric frames. TB is the normal modal logic axiomatized by the propositional tautologies, the K distribution axiom, axiom T (reflexivity: box phi -> phi), and axiom B (symmetry: phi -> box(diamond phi)). Soundness is proved by case analysis on the axiom predicate, showing each axiom is valid on reflexive + symmetric frames. Completeness follows the canonical model method (BRV Theorem 4.28): the canonical frame for TB is reflexive (from axiom T, via existing canonical_refl) and symmetric (from axiom B, via canonical_symm from task 100), so the truth lemma gives a countermodel for any non-derivable formula.

### Research Integration

Key findings from the research report (01_tb-logic-research.md):

- TB uses the T-based `truth_lemma` (NOT `k_truth_lemma`) because TBAxiom includes axiom T, which enables `mcs_box_witness`.
- Soundness for axiom B on symmetric frames follows the pattern: given `h_phi : Satisfies m w phi` and `w'` with `m.r w w'`, use symmetry to get `m.r w' w`, then witness the diamond with `w` and `h_phi`.
- Completeness combines `canonical_refl` (from axiom T) and `canonical_symm` (from axiom B) -- exactly two frame properties, parallel to S4 which uses `canonical_refl` + `canonical_trans`.
- The consistency boilerplate in the completeness proof is identical across all systems (T, S4, S5, and now TB).

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No ROADMAP.md found.

## Goals & Non-Goals

**Goals**:
- Create `TBSoundness.lean` with `tb_axiom_sound`, `tb_soundness`, `tb_soundness_derivable`
- Create `TBCompleteness.lean` with `tb_truth_lemma`, `tb_canonical_refl`, `tb_canonical_symm`, `tb_completeness`
- Add imports for both files to `Metalogic.lean` aggregator

**Non-Goals**:
- Defining `TBAxiom`, `HilbertTB` tag, `ModalTBHilbert` class, or TB typeclass instances (task 100 scope)
- Proving `canonical_symm` (task 100 scope -- parameterized lemma in Completeness.lean)
- Proving decidability or finite model property for TB

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Task 100 not completed (TBAxiom, canonical_symm missing) | H | M | Phase 1 (soundness) can proceed if TBAxiom is defined inline; Phase 2 blocks on canonical_symm. Check task 100 status at implementation time. |
| canonical_symm proof complexity | M | L | Research report provides detailed proof strategy following canonical_eucl pattern; the proof is well-understood. |
| Satisfies unfolding for diamond in soundness | L | L | Pattern is identical to S5 Soundness modalB case -- use symmetry hypothesis directly. |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |

Phases within the same wave can execute in parallel.

---

### Phase 1: TB Soundness [COMPLETED]

**Goal**: Create `TBSoundness.lean` proving that every TB axiom is valid on reflexive + symmetric frames, and derive soundness for TB derivations.

**Tasks**:
- [x] Create `Cslib/Logics/Modal/Metalogic/TBSoundness.lean` with module header and imports *(completed)*
- [x] Implement `tb_axiom_sound`: case analysis on `TBAxiom`, proving each of the 7 constructors is valid on reflexive + symmetric frames *(completed)*
  - Cases `implyK`, `implyS`, `efq`, `peirce`, `modalK`: identical to all existing soundness proofs (valid on all frames)
  - Case `modalT`: uses reflexivity -- `intro h_box; exact h_box w (h_refl w)` (identical to TSoundness)
  - Case `modalB`: uses symmetry -- given `h_phi` and `w'` with `m.r w w'`, apply `h_symm` to get `m.r w' w`, then construct diamond witness (follows S5 Soundness modalB pattern but uses direct symmetry instead of eucl+refl)
- [x] Implement `tb_soundness`: wrapper delegating to parameterized `soundness` with `tb_axiom_sound` *(completed)*
- [x] Implement `tb_soundness_derivable`: wrapper delegating to `soundness_derivable` with `tb_axiom_sound` *(completed)*
- [x] Verify with `lake build Cslib.Logics.Modal.Metalogic.TBSoundness` *(completed)*

**Timing**: 1 hour

**Depends on**: none (but requires TBAxiom from task 100 to exist)

**Files to modify**:
- `Cslib/Logics/Modal/Metalogic/TBSoundness.lean` - NEW: TB soundness theorem (~90 lines)

**Verification**:
- `lake build Cslib.Logics.Modal.Metalogic.TBSoundness` passes with zero errors
- `lean_verify` confirms no sorry or axiom usage
- All 7 axiom cases handled in `tb_axiom_sound`

---

### Phase 2: TB Completeness and Integration [COMPLETED]

**Goal**: Create `TBCompleteness.lean` proving TB completeness via the canonical model method, and update the Metalogic.lean aggregator.

**Tasks**:
- [x] Create `Cslib/Logics/Modal/Metalogic/TBCompleteness.lean` with module header and imports *(completed)*
- [x] Implement `tb_canonical_refl`: thin wrapper instantiating `canonical_refl` at `TBAxiom` with constructors `.implyK`, `.implyS`, `.modalT` *(completed)*
- [x] Implement `tb_canonical_symm`: thin wrapper instantiating `canonical_symm` at `TBAxiom` with constructors `.implyK`, `.implyS`, `.modalK`, `.modalB` *(deviation: altered -- argument order is h_K before h_B per canonical_symm signature)*
- [x] Implement `tb_truth_lemma`: thin wrapper instantiating `truth_lemma` at `TBAxiom` with constructors `.implyK`, `.implyS`, `.efq`, `.peirce`, `.modalK`, `.modalT` *(completed)*
- [x] Implement `tb_completeness`: main completeness theorem by contrapositive *(completed)*
  - Assume `phi` not TB-derivable
  - Show `{neg phi}` is TB-consistent (identical boilerplate to S4Completeness/TCompleteness)
  - Lindenbaum extension to MCS `M`
  - Canonical world `w = (M, hM_mcs)`
  - Apply `h_valid` to canonical model with `tb_canonical_refl` and `tb_canonical_symm`
  - Use `tb_truth_lemma` to convert satisfaction to membership
  - Contradiction via `mcs_not_mem_of_neg`
- [x] Verify with `lake build Cslib.Logics.Modal.Metalogic.TBCompleteness` *(completed)*
- [x] Add imports to `Cslib/Logics/Modal/Metalogic.lean`: `TBSoundness` and `TBCompleteness` *(completed)*
- [x] Verify full module build: `lake build Cslib.Logics.Modal.Metalogic` *(completed)*

**Timing**: 2 hours

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/Modal/Metalogic/TBCompleteness.lean` - NEW: TB completeness theorem (~135 lines)
- `Cslib/Logics/Modal/Metalogic.lean` - ADD: two import lines for TBSoundness and TBCompleteness

**Verification**:
- `lake build Cslib.Logics.Modal.Metalogic` passes with zero errors
- `lean_verify` confirms no sorry or axiom usage in `tb_completeness`
- `tb_completeness` type signature matches: `forall phi, (forall World m, refl -> symm -> forall w, Satisfies m w phi) -> Derivable TBAxiom phi`

## Testing & Validation

- [ ] `lake build Cslib.Logics.Modal.Metalogic.TBSoundness` passes (Phase 1)
- [ ] `lake build Cslib.Logics.Modal.Metalogic.TBCompleteness` passes (Phase 2)
- [ ] `lake build Cslib.Logics.Modal.Metalogic` passes with new imports (Phase 2)
- [ ] No `sorry` in either new file: `grep -r sorry Cslib/Logics/Modal/Metalogic/TBSoundness.lean Cslib/Logics/Modal/Metalogic/TBCompleteness.lean`
- [ ] `lean_verify` on `Cslib.Logic.Modal.tb_completeness` and `Cslib.Logic.Modal.tb_soundness_derivable` shows no axiom usage

## Artifacts & Outputs

- `Cslib/Logics/Modal/Metalogic/TBSoundness.lean` - TB soundness proofs
- `Cslib/Logics/Modal/Metalogic/TBCompleteness.lean` - TB completeness proof
- `Cslib/Logics/Modal/Metalogic.lean` - Updated aggregator with TB imports

## Rollback/Contingency

If task 100 has not been completed when implementation begins:
1. Check whether `TBAxiom` and `canonical_symm` exist in the codebase
2. If missing, implementation must wait for task 100 or include those definitions inline (with a note that they will be deduplicated when task 100 is implemented)
3. If only `canonical_symm` is missing but `TBAxiom` exists, Phase 1 can proceed while Phase 2 blocks

If implementation fails:
- Delete `TBSoundness.lean` and `TBCompleteness.lean`
- Revert import additions in `Metalogic.lean`
- No other files are modified, so rollback is clean
