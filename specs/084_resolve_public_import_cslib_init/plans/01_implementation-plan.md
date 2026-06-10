# Implementation Plan: Resolve public import Cslib.Init

- **Task**: 84 - Resolve public import Cslib.Init in Foundations/Logic files
- **Status**: [NOT STARTED]
- **Effort**: 0.5 hours
- **Dependencies**: None
- **Research Inputs**: specs/084_resolve_public_import_cslib_init/reports/01_public-import-analysis.md
- **Artifacts**: plans/01_implementation-plan.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: lean4
- **Lean Intent**: true

## Overview

Downgrade `public import Cslib.Init` to `import Cslib.Init` in 3 Foundations/Logic files (Connectives.lean, InferenceSystem.lean, FrameConditions.lean) while adding compensating `import Cslib.Init` to 5 downstream files that currently receive it transitively. This is a mechanical, zero-semantic-change edit set totaling 8 file modifications, confirmed by `lake shake`. Task 70 previously attempted this but was reverted because it omitted the compensating imports -- this plan addresses that exact failure mode by adding compensating imports first.

### Research Integration

Key findings from the research report (01_public-import-analysis.md):
- All 3 `public import Cslib.Init` declarations can be safely downgraded
- 5 downstream files need compensating `import Cslib.Init` additions
- Task 70 failed because it omitted compensating imports -- the fix is to add them atomically
- `lake shake` confirms the exact change set
- No Logics/ files are affected (they all already have their own `Cslib.Init` imports)

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

This task advances import hygiene for the Foundations/Logic module, supporting clean PR submission for PR 1.

## Goals & Non-Goals

**Goals**:
- Remove all `public import Cslib.Init` from Foundations/Logic files
- Add explicit `import Cslib.Init` to all files that relied on transitive access
- Pass `lake build` with zero errors
- Pass `lake shake` with no warnings for these files

**Non-Goals**:
- Downgrading the 3 Mathlib `public import` declarations in FrameConditions.lean (separate concern)
- Modifying any Logics/ files (they already have their own imports)
- Changing any code semantics

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Missed compensating import | H | L | Research identified all 5 files; `lake build` catches immediately |
| Phase ordering causes transient build failure | M | L | Add compensating imports first (Phase 1), then downgrade (Phase 2) |
| Repeat of task 70 revert | H | L | Explicit Phase 1 compensating imports prevent the exact failure mode |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3 | 2 |
| 4 | 4 | 3 |

Phases are strictly sequential to ensure build correctness at each step.

### Phase 1: Add compensating imports to 5 downstream files [COMPLETED]

**Goal**: Add explicit `import Cslib.Init` to every file that currently receives it transitively through `public import` in Connectives.lean, InferenceSystem.lean, or FrameConditions.lean.

**Tasks**:
- [x] Add `import Cslib.Init` to `Cslib/Foundations/Logic/Axioms.lean`
- [x] Add `import Cslib.Init` to `Cslib/Foundations/Logic/Metalogic/DeductionHelpers.lean`
- [x] Add `import Cslib.Init` to `Cslib/Foundations/Logic/ProofSystem.lean`
- [x] Add `import Cslib.Init` to `Cslib/Foundations/Logic/Theorems/Combinators.lean`
- [x] Add `import Cslib.Init` to `Cslib/Foundations/Logic/Theorems.lean`
- [x] Add `import Cslib.Init` to `Cslib/Foundations/Logic/Theorems/Propositional/Core.lean` *(deviation: altered -- research missed this file; uses @[expose] from Cslib.Init)*
- [x] Add `import Cslib.Init` to `Cslib/Foundations/Logic/Theorems/Propositional/Connectives.lean` *(deviation: altered -- research missed this file; uses @[expose] from Cslib.Init)*
- [x] Add `import Cslib.Init` to `Cslib/Foundations/Logic/Theorems/Modal/Basic.lean` *(deviation: altered -- research missed this file; uses @[expose] from Cslib.Init)*
- [x] Add `import Cslib.Init` to `Cslib/Foundations/Logic/Theorems/Modal/S5.lean` *(deviation: altered -- research missed this file; uses @[expose] from Cslib.Init)*
- [x] Add `import Cslib.Init` to `Cslib/Foundations/Logic/Theorems/BigConj.lean` *(deviation: altered -- research missed this file; uses @[expose] from Cslib.Init)*
- [x] Add `import Cslib.Init` to `Cslib/Foundations/Logic/Theorems/Temporal/TemporalDerived.lean` *(deviation: altered -- research missed this file; uses @[expose] from Cslib.Init)*
- [x] Add `import Cslib.Init` to `Cslib/Foundations/Logic/Metalogic/Consistency.lean` *(deviation: altered -- research missed this file; uses @[expose] from Cslib.Init)*

**Timing**: 10 minutes

**Depends on**: none

**Files to modify**:
- `Cslib/Foundations/Logic/Axioms.lean` - Add `import Cslib.Init` in import block
- `Cslib/Foundations/Logic/Metalogic/DeductionHelpers.lean` - Add `import Cslib.Init` in import block
- `Cslib/Foundations/Logic/ProofSystem.lean` - Add `import Cslib.Init` in import block
- `Cslib/Foundations/Logic/Theorems/Combinators.lean` - Add `import Cslib.Init` in import block
- `Cslib/Foundations/Logic/Theorems.lean` - Add `import Cslib.Init` in import block

**Verification**:
- `lake build` passes (compensating imports are additive, cannot break anything)

---

### Phase 2: Downgrade public import in 3 target files [COMPLETED]

**Goal**: Change `public import Cslib.Init` to `import Cslib.Init` in all 3 target files.

**Tasks**:
- [x] Change `public import Cslib.Init` to `import Cslib.Init` in `Cslib/Foundations/Logic/Connectives.lean`
- [x] Change `public import Cslib.Init` to `import Cslib.Init` in `Cslib/Foundations/Logic/InferenceSystem.lean`
- [x] Change `public import Cslib.Init` to `import Cslib.Init` in `Cslib/Foundations/Logic/Theorems/Temporal/FrameConditions.lean`

**Timing**: 5 minutes

**Depends on**: 1

**Files to modify**:
- `Cslib/Foundations/Logic/Connectives.lean` - `public import Cslib.Init` -> `import Cslib.Init`
- `Cslib/Foundations/Logic/InferenceSystem.lean` - `public import Cslib.Init` -> `import Cslib.Init`
- `Cslib/Foundations/Logic/Theorems/Temporal/FrameConditions.lean` - `public import Cslib.Init` -> `import Cslib.Init`

**Verification**:
- `lake build` passes with zero errors

---

### Phase 3: Build verification [COMPLETED]

**Goal**: Confirm the complete change set builds cleanly with no regressions.

**Tasks**:
- [x] Run `lake build` and verify zero errors
- [x] Spot-check that downstream files (Axioms.lean, Combinators.lean, etc.) still compile

**Timing**: 5 minutes (build time)

**Depends on**: 2

**Files to modify**: None

**Verification**:
- `lake build` exits with code 0
- No new warnings related to `Cslib.Init`

---

### Phase 4: Import hygiene verification [NOT STARTED]

**Goal**: Run `lake shake` to confirm no remaining import hygiene warnings for `Cslib.Init` in the modified files.

**Tasks**:
- [ ] Run `lake shake` on the project
- [ ] Verify no warnings for `public import Cslib.Init` in any of the 3 target files
- [ ] Verify no warnings about missing imports in the 5 compensating files

**Timing**: 5 minutes

**Depends on**: 3

**Files to modify**: None (unless `lake shake` reveals additional needed changes)

**Verification**:
- `lake shake` shows no `Cslib.Init`-related warnings for any of the 8 modified files
- If additional warnings appear, address them before completing

## Testing & Validation

- [ ] `lake build` passes with zero errors after all edits
- [ ] `lake shake` shows no `public import Cslib.Init` warnings for the 3 target files
- [ ] `lake shake` shows no missing import warnings for the 5 compensating files
- [ ] No behavioral or semantic changes to any proofs or definitions

## Artifacts & Outputs

- `specs/084_resolve_public_import_cslib_init/plans/01_implementation-plan.md` (this file)
- 8 modified Lean source files (3 downgrades + 5 compensating imports)
- Implementation summary after completion

## Rollback/Contingency

If the build breaks after Phase 2, revert the 3 downgrade edits in Phase 2 while keeping the compensating imports from Phase 1 (they are harmless additive changes). If the issue is a missed file, add the compensating import and retry. As a last resort, `git checkout` the 8 modified files to restore the pre-change state.
