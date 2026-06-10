# Implementation Plan: Task #78 - Module Keyword and Private Declaration Audit

- **Task**: 78 - Module keyword and private declaration audit across Logics/
- **Status**: [NOT STARTED]
- **Effort**: 3 hours
- **Dependencies**: Task 76 (reverted), Task 77 (consolidated shared helpers)
- **Research Inputs**: specs/078_module_keyword_and_private_audit/reports/01_module-keyword-audit.md
- **Artifacts**: plans/01_module-keyword-audit.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: lean4
- **Lean Intent**: false

## Overview

Mechanically migrate all 155 non-module Lean files in `Cslib/Logics/` to use the Lean 4 `module` keyword, resolving the build failure caused by the root `Cslib.lean` (which already uses `module`) attempting to import non-module files. The migration requires two preparatory steps: removing `private` from all `private def`/`private abbrev` declarations (which break inside `@[expose] public section` in module files), and then applying the `module` + `public import` + `@[expose] public section` transformation to each file. One additional file (`Temporal/Syntax/Formula.lean`) already has `module` but contains a `private noncomputable def` that also needs fixing.

### Research Integration

Key findings from the research report (01_module-keyword-audit.md):

- **`private theorem` works in `@[expose] public section`**, but `private def`, `private abbrev`, and `private noncomputable def` do NOT (Lean 4.31.0-rc1 behavior).
- Only 105 `private def`/`private abbrev` declarations across 24 files need `private` removed. The 202 `private theorem` declarations are safe and require no changes.
- Zero name collisions exist when removing `private` -- all duplicated names are in different namespaces.
- Task 77 already consolidated the most-duplicated helper (`theorem_in_mcs_fc`) into a public definition.
- 32 Logics/ files already have the `module` keyword with `@[expose] public section` and work correctly.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

This task advances the overall Logics/ infrastructure by enabling all 187 Lean files in `Cslib/Logics/` to compile as modules, which is required for the root `Cslib.lean` module import. This is foundational infrastructure for all remaining roadmap items (discrete completeness, continuous extension completeness, dense/discrete/continuous temporal completeness).

## Goals & Non-Goals

**Goals**:
- Remove `private` from all `private def`/`private abbrev`/`private noncomputable def` declarations that would break in `@[expose] public section`
- Add `module` + `public import` + `@[expose] public section` to all 155 non-module files
- Fix the one existing module file with a `private noncomputable def` (`Temporal/Syntax/Formula.lean`)
- Achieve a clean `lake build` with zero errors

**Non-Goals**:
- Renaming any declarations (no collisions exist, so unnecessary)
- Modifying `private theorem` declarations (they work in `@[expose] public section`)
- Changing `private lemma` in LinearLogic files (already have `module`, already work)
- Restructuring or refactoring any proof logic

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Edge case files with unusual structure (multiple namespaces, nested sections) | M | L | Verify each directory batch with `lake build` before proceeding |
| `private theorem` breaks in some untested configuration | H | L | Research experimentally verified this works; catch in build verification |
| Uncommitted task 77 changes conflict with edits | M | L | Check git status before starting; commit or stash task 77 changes |
| Sed/find-replace corrupts file content | H | L | Use targeted replacements; verify with `lake build` after each batch |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3 | 2 |
| 4 | 4 | 3 |

Phases are sequential because each builds on the previous: private removal must precede module addition, and verification must follow each transformation.

---

### Phase 1: Remove `private` from def/abbrev declarations [COMPLETED]

**Goal**: Remove the `private` keyword from all `private def`, `private noncomputable def`, and `private abbrev` declarations across Logics/ files (including the one in `Temporal/Syntax/Formula.lean` which already has `module`).

**Tasks**:
- [ ] Verify git working tree is clean (or stash/commit any pending changes)
- [ ] Run `find` + `sed` to replace `private def ` with `def ` across all Logics/ `.lean` files
- [ ] Run `find` + `sed` to replace `private noncomputable def ` with `noncomputable def ` across all Logics/ `.lean` files
- [ ] Run `find` + `sed` to replace `private abbrev ` with `abbrev ` across all Logics/ `.lean` files
- [ ] Verify no `private def` or `private abbrev` remain in Logics/ (excluding LinearLogic `private lemma` which is fine)
- [ ] Spot-check 3-5 modified files to confirm replacements are correct and no content was corrupted

**Timing**: 30 minutes

**Depends on**: none

**Files to modify**:
- ~24 files across `Cslib/Logics/Bimodal/`, `Cslib/Logics/Temporal/`, `Cslib/Logics/Modal/`, `Cslib/Logics/Propositional/` containing `private def`/`private abbrev`/`private noncomputable def`

**Verification**:
- `grep -r 'private def\|private abbrev' Cslib/Logics/` returns zero matches (excluding `private lemma` in LinearLogic)
- Modified files parse correctly (no syntax errors introduced)

---

### Phase 2: Add module keyword to Propositional, Modal, and HML files (21 files) [NOT STARTED]

**Goal**: Apply the `module` + `public import` + `@[expose] public section` transformation to the smaller directories first (Propositional: 5 files, Modal: 6 files, HML: 0 files already done) and verify with `lake build`.

**Tasks**:
- [ ] For each of the 5 non-module Propositional files: add `module` after copyright header, change `import` to `public import`, add `@[expose] public section` before first `namespace`
- [ ] For each of the 6 non-module Modal files: same transformation
- [ ] Run `lake build` and verify these 11 files compile without errors
- [ ] Fix any issues that arise (unexpected `private` patterns, missing `end` statements, etc.)

**Timing**: 45 minutes

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/Propositional/` - 5 files without `module`
- `Cslib/Logics/Modal/` - 6 files without `module`

**Verification**:
- All Propositional and Modal files have `module` keyword
- `lake build` succeeds (or at least these modules compile without errors)

---

### Phase 3: Add module keyword to Temporal and Bimodal files (144 files) [NOT STARTED]

**Goal**: Apply the same `module` + `public import` + `@[expose] public section` transformation to the remaining 144 non-module files (Temporal: 27 files, Bimodal: 117 files). These are the largest directories and contain the most complex dependency chains.

**Tasks**:
- [ ] For each of the 27 non-module Temporal files: add `module` after copyright header, change `import` to `public import`, add `@[expose] public section` before first `namespace`
- [ ] Run `lake build` to verify Temporal files compile
- [ ] Fix any Temporal-specific issues
- [ ] For each of the 117 non-module Bimodal files: same transformation
- [ ] Run `lake build` to verify Bimodal files compile
- [ ] Fix any Bimodal-specific issues (these files are the most complex with Chronicle, Decidability, etc.)

**Timing**: 1.5 hours

**Depends on**: 2

**Files to modify**:
- `Cslib/Logics/Temporal/` - 27 files without `module`
- `Cslib/Logics/Bimodal/` - 117 files without `module`

**Verification**:
- All 187 Logics/ files have `module` keyword
- Each subdirectory's files compile successfully

---

### Phase 4: Full build verification and cleanup [NOT STARTED]

**Goal**: Run a complete `lake build` to confirm zero errors across the entire project, and verify the root `Cslib.lean` module import chain works.

**Tasks**:
- [ ] Run `lake build` from project root
- [ ] Verify zero errors (the "cannot import non-module" error from `Cslib.lean` should be resolved)
- [ ] Verify total count: all 187 Logics/ files now have `module` keyword
- [ ] Verify no remaining `private def` or `private abbrev` in Logics/ (except `private lemma` in LinearLogic)
- [ ] Spot-check that `private theorem` declarations still work correctly in a few files

**Timing**: 15 minutes (build time + verification)

**Depends on**: 3

**Files to modify**:
- None (verification only)

**Verification**:
- `lake build` exits with code 0
- `grep -rl '^module' Cslib/Logics/ | wc -l` returns 187
- No regressions in any module

## Testing & Validation

- [ ] `lake build` completes with zero errors
- [ ] All 187 Logics/ files contain `module` keyword
- [ ] No `private def` or `private abbrev` remain in Logics/ (only `private theorem` and `private lemma` in LinearLogic)
- [ ] Root `Cslib.lean` can import all Logics/ modules without "cannot import non-module" errors
- [ ] Spot-check: `private theorem` declarations still resolve correctly within their files

## Artifacts & Outputs

- `specs/078_module_keyword_and_private_audit/plans/01_module-keyword-audit.md` (this file)
- `specs/078_module_keyword_and_private_audit/summaries/01_module-keyword-audit-summary.md` (after implementation)

## Rollback/Contingency

The entire migration is mechanical and easily reversible:
- `git checkout -- Cslib/Logics/` reverts all changes
- If partial rollback is needed, individual directories can be reverted independently
- The `private` removal and `module` addition are independent operations -- rolling back `module` addition alone is possible by reverting import/section changes while keeping `private` removal
