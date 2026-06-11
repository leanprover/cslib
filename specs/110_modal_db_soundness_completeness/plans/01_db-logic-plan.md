# Implementation Plan: Task #110 - Modal DB Soundness and Completeness

- **Task**: 110 - Modal DB Soundness and Completeness
- **Status**: [NOT STARTED]
- **Effort**: 2 hours
- **Dependencies**: Task 100 (shared infrastructure, completed)
- **Research Inputs**: specs/110_modal_db_soundness_completeness/reports/01_db-logic-research.md
- **Artifacts**: plans/01_db-logic-plan.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: lean4
- **Lean Intent**: true

## Overview

Prove soundness and completeness for modal logic DB (K + D + B) over serial + symmetric Kripke frames. DB combines the seriality axiom D (box phi -> diamond phi) with the symmetry axiom B (phi -> box diamond phi) but does NOT include axiom T. This requires creating two new Lean files: DBSoundness.lean (~70 lines, 7-case axiom validity proof) and DBCompleteness.lean (~90 lines, canonical model construction using truth_lemma_d). Additionally, the Metalogic.lean aggregator must be updated with import lines for both new files.

### Research Integration

The research report confirms that all infrastructure components are already in place:
- `DBAxiom` with 7 constructors (Instances.lean:439-463)
- `canonical_serial` (DCompleteness.lean) and `canonical_symm` (Completeness.lean)
- `truth_lemma_d` (DCompleteness.lean) -- critical: DB uses D-based truth lemma, not T-based
- All typeclass instances registered (Instances.lean:1457-1529)

The implementation is pure assembly from existing parameterized theorems with zero new lemmas needed.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

This task advances the Modal Logic metalogic phase of the CSLib port, specifically completing one of the 12 modal cube logic systems from task 99's expansion.

## Goals & Non-Goals

**Goals**:
- Prove `db_axiom_sound`: all 7 DBAxiom cases valid over serial + symmetric frames
- Prove `db_soundness` and `db_soundness_derivable`: soundness wrappers
- Prove `db_completeness`: completeness via canonical model with truth_lemma_d
- Update Metalogic.lean aggregator with import lines
- Verify all theorems are sorry-free and axiom-free via lean_verify

**Non-Goals**:
- Modifying any existing infrastructure files
- Creating new lemmas or helper theorems beyond the main results
- Proving decidability or finite model property for DB

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Constructor name mismatch in DBAxiom | M | L | Research report lists all 7 constructors; verify with lean_hover_info |
| truth_lemma_d parameter mismatch | H | L | Follow D4Completeness.lean exactly; same parameter signature |
| canonical_symm argument order differs from research | M | L | Check BSoundness/Completeness.lean patterns; use lean_hover_info |
| Build failure due to import ordering | L | L | Follow existing Metalogic.lean import order |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |

Phases within the same wave can execute in parallel.

### Phase 1: DBSoundness.lean [COMPLETED]

**Goal**: Create the soundness proof for DB logic over serial + symmetric frames.

**Tasks**:
- [x] Create `Cslib/Logics/Modal/Metalogic/DBSoundness.lean` with module header and imports (`Soundness`, `Instances`)
- [x] Implement `db_axiom_sound` with 7 cases: implyK, implyS, efq, peirce, modalK, modalD (seriality witness), modalB (symmetry flip)
- [x] Implement `db_soundness` wrapper using generic `soundness` theorem
- [x] Implement `db_soundness_derivable` wrapper using generic `soundness_derivable` theorem
- [x] Verify with `lake build Cslib.Logics.Modal.Metalogic.DBSoundness`
- [x] Run `lean_verify` on `db_axiom_sound`, `db_soundness`, `db_soundness_derivable`

**Timing**: 45 minutes

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Modal/Metalogic/DBSoundness.lean` - NEW file (~70 lines)

**Verification**:
- `lake build Cslib.Logics.Modal.Metalogic.DBSoundness` succeeds
- `lean_verify` confirms zero sorry, zero axioms for all three theorems

---

### Phase 2: DBCompleteness.lean + Aggregator Update [NOT STARTED]

**Goal**: Create the completeness proof for DB logic and register both new files in the aggregator.

**Tasks**:
- [ ] Create `Cslib/Logics/Modal/Metalogic/DBCompleteness.lean` with module header and imports (`Completeness`, `DCompleteness`)
- [ ] Implement `db_completeness` theorem following D4Completeness pattern:
  - Contrapositive setup (`by_contra h_not_deriv`)
  - Consistency of `{neg phi}` via standard DNE derivation (deductionTheorem + peirce)
  - Lindenbaum extension (`modal_lindenbaum`)
  - Canonical world construction
  - Seriality via `canonical_serial` with constructors: `.implyK`, `.implyS`, `.efq`, `.modalK`, `.modalD`
  - Symmetry via `canonical_symm` with constructors: `.implyK`, `.implyS`, `.modalK`, `.modalB`
  - Apply `truth_lemma_d` (NOT `truth_lemma`) with constructors: `.implyK`, `.implyS`, `.efq`, `.peirce`, `.modalK`, `.modalD`
  - Contradiction via `mcs_not_mem_of_neg`
- [ ] Verify with `lake build Cslib.Logics.Modal.Metalogic.DBCompleteness`
- [ ] Run `lean_verify` on `db_completeness`
- [ ] Add import lines to `Cslib/Logics/Modal/Metalogic/Metalogic.lean`:
  - `public import Cslib.Logics.Modal.Metalogic.DBSoundness`
  - `public import Cslib.Logics.Modal.Metalogic.DBCompleteness`
- [ ] Full project build: `lake build`

**Timing**: 1 hour 15 minutes

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/Modal/Metalogic/DBCompleteness.lean` - NEW file (~90 lines)
- `Cslib/Logics/Modal/Metalogic/Metalogic.lean` - Add 2 import lines

**Verification**:
- `lake build Cslib.Logics.Modal.Metalogic.DBCompleteness` succeeds
- `lean_verify` confirms zero sorry, zero axioms for `db_completeness`
- `lake build` (full project) succeeds with no regressions

## Testing & Validation

- [ ] `lake build Cslib.Logics.Modal.Metalogic.DBSoundness` -- module compiles
- [ ] `lake build Cslib.Logics.Modal.Metalogic.DBCompleteness` -- module compiles
- [ ] `lean_verify Cslib.Logic.Modal.db_axiom_sound` -- zero sorry, zero axioms
- [ ] `lean_verify Cslib.Logic.Modal.db_soundness` -- zero sorry, zero axioms
- [ ] `lean_verify Cslib.Logic.Modal.db_soundness_derivable` -- zero sorry, zero axioms
- [ ] `lean_verify Cslib.Logic.Modal.db_completeness` -- zero sorry, zero axioms
- [ ] `lake build` -- full project builds with no regressions

## Artifacts & Outputs

- `Cslib/Logics/Modal/Metalogic/DBSoundness.lean` - Soundness proof (~70 lines)
- `Cslib/Logics/Modal/Metalogic/DBCompleteness.lean` - Completeness proof (~90 lines)
- `Cslib/Logics/Modal/Metalogic/Metalogic.lean` - Updated aggregator (2 new imports)
- `specs/110_modal_db_soundness_completeness/summaries/01_db-logic-summary.md` - Execution summary

## Rollback/Contingency

If implementation fails:
1. Delete `DBSoundness.lean` and `DBCompleteness.lean`
2. Remove import lines from `Metalogic.lean`
3. Run `lake build` to confirm project reverts cleanly
4. The task has no side effects on existing files beyond the aggregator imports
