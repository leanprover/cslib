# Implementation Plan: Add module keyword to 10 Foundations/Logic theorem files

- **Task**: 68 - Add module keyword to 10 Foundations/Logic theorem files
- **Status**: [NOT STARTED]
- **Effort**: 1.5 hours
- **Dependencies**: Task 59 (PR 1 submitted, branch exists)
- **Research Inputs**: specs/068_add_module_keyword_theorem_files/reports/01_module-keyword-research.md
- **Artifacts**: plans/01_module-keyword-plan.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: lean4
- **Lean Intent**: false

## Overview

Add the `module` keyword and convert all `import` statements to `public import` in 10 Foundations/Logic files that are currently not importable from `Cslib.lean` (which is itself a `module` file). The transformation is mechanical: insert `module` on its own line after the copyright header closing `-/`, separated by blank lines, then prefix every `import` with `public`. After all edits, regenerate `Cslib.lean` with `lake exe mk_all --module` and verify the build passes.

### Research Integration

Research report (01_module-keyword-research.md) confirmed:
- The 5 existing core definition files establish the pattern: `module` on its own line after copyright header, blank line, then `public import` for all imports
- No `@[expose] public section` is needed for theorem files (only used in definition files)
- `private` declarations in TemporalDerived.lean and Consistency.lean are unaffected by `module`
- All 10 file edits are independent (no ordering constraints)
- Mathlib imports becoming `public import` preserves pre-existing transitive visibility behavior

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No ROADMAP.md found.

## Goals & Non-Goals

**Goals**:
- Add `module` keyword to all 10 affected Foundations/Logic files
- Convert all `import` to `public import` in those files
- Regenerate `Cslib.lean` to include the newly visible module files
- Pass `lake build` with zero errors

**Non-Goals**:
- Adding `@[expose] public section` (not needed for theorem files)
- Fixing linter warnings (separate task 69)
- Removing unused imports (separate task 70)
- Modifying any file content beyond the module/import declarations

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Transitive Mathlib imports cause build conflicts | M | L | Pre-existing behavior; `public import` matches non-module semantics |
| `lake exe mk_all --module` generates unexpected entries | L | L | Review diff of Cslib.lean before building |
| Build failure after transformation | M | L | Edits are independent; can bisect by reverting individual files |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |

Phases within the same wave can execute in parallel.

### Phase 1: Add module keyword and public imports to all 10 files [COMPLETED]

**Goal**: Transform all 10 affected files by inserting `module` after the copyright header and converting `import` to `public import`.

**Tasks**:
- [ ] Transform `Cslib/Foundations/Logic/Theorems/Combinators.lean`: insert `module`, change 1 import to `public import`
- [ ] Transform `Cslib/Foundations/Logic/Theorems/Propositional/Core.lean`: insert `module`, change 1 import to `public import`
- [ ] Transform `Cslib/Foundations/Logic/Theorems/Propositional/Connectives.lean`: insert `module`, change 1 import to `public import`
- [ ] Transform `Cslib/Foundations/Logic/Theorems/BigConj.lean`: insert `module`, change 1 import to `public import`
- [ ] Transform `Cslib/Foundations/Logic/Theorems/Modal/Basic.lean`: insert `module`, change 4 imports to `public import`
- [ ] Transform `Cslib/Foundations/Logic/Theorems/Modal/S5.lean`: insert `module`, change 5 imports to `public import`
- [ ] Transform `Cslib/Foundations/Logic/Theorems/Temporal/TemporalDerived.lean`: insert `module`, change 2 imports to `public import`
- [ ] Transform `Cslib/Foundations/Logic/Theorems/Temporal/FrameConditions.lean`: insert `module`, change 4 imports to `public import`
- [ ] Transform `Cslib/Foundations/Logic/Metalogic/Consistency.lean`: insert `module`, change 2 imports to `public import`
- [ ] Transform `Cslib/Foundations/Logic/Theorems.lean`: insert `module`, change 8 imports to `public import`

**Timing**: 1 hour

**Depends on**: none

**Files to modify**:
- `Cslib/Foundations/Logic/Theorems/Combinators.lean` - add `module` + `public import`
- `Cslib/Foundations/Logic/Theorems/Propositional/Core.lean` - add `module` + `public import`
- `Cslib/Foundations/Logic/Theorems/Propositional/Connectives.lean` - add `module` + `public import`
- `Cslib/Foundations/Logic/Theorems/BigConj.lean` - add `module` + `public import`
- `Cslib/Foundations/Logic/Theorems/Modal/Basic.lean` - add `module` + `public import`
- `Cslib/Foundations/Logic/Theorems/Modal/S5.lean` - add `module` + `public import`
- `Cslib/Foundations/Logic/Theorems/Temporal/TemporalDerived.lean` - add `module` + `public import`
- `Cslib/Foundations/Logic/Theorems/Temporal/FrameConditions.lean` - add `module` + `public import`
- `Cslib/Foundations/Logic/Metalogic/Consistency.lean` - add `module` + `public import`
- `Cslib/Foundations/Logic/Theorems.lean` - add `module` + `public import`

**Transformation pattern** (apply to each file):
1. After the copyright header closing `-/`, ensure a blank line, then add `module` on its own line, then a blank line
2. Change every `import X` to `public import X`
3. Leave everything else unchanged (namespaces, `open`, `set_option`, `private` decls) *(deviation: altered -- `@[expose] public section` was added to 9 of 10 files because `module` makes declarations private by default; without it, downstream importers cannot resolve declarations)*

**Verification**:
- Each file has `module` on its own line after the copyright header
- Every `import` in all 10 files uses `public import`
- No other content was changed

---

### Phase 2: Regenerate Cslib.lean and verify build [COMPLETED]

**Goal**: Update `Cslib.lean` to include the 10 newly visible module files, then verify the full project builds.

**Tasks**:
- [ ] Run `lake exe mk_all --module` to regenerate `Cslib.lean`
- [ ] Review the diff of `Cslib.lean` to confirm the 10 new entries are present
- [ ] Run `lake build` and verify zero errors

**Timing**: 0.5 hours

**Depends on**: 1

**Files to modify**:
- `Cslib.lean` - auto-regenerated by `lake exe mk_all --module`

**Verification**:
- `Cslib.lean` includes all 10 new module paths (Theorems/Combinators, Theorems/Propositional/Core, Theorems/Propositional/Connectives, Theorems/BigConj, Theorems/Modal/Basic, Theorems/Modal/S5, Theorems/Temporal/TemporalDerived, Theorems/Temporal/FrameConditions, Metalogic/Consistency, Theorems)
- `lake build` completes with zero errors

## Testing & Validation

- [ ] All 10 files have `module` keyword after copyright header
- [ ] All imports in all 10 files use `public import`
- [ ] `lake exe mk_all --module` succeeds and updates `Cslib.lean`
- [ ] `Cslib.lean` now includes all 10 new module paths
- [ ] `lake build` passes with no errors
- [ ] No `@[expose] public section` was added to any theorem file

## Artifacts & Outputs

- plans/01_module-keyword-plan.md (this file)
- summaries/01_module-keyword-summary.md (after implementation)
- 10 modified `.lean` source files
- Updated `Cslib.lean`

## Rollback/Contingency

Revert all changes with `git checkout -- Cslib/Foundations/Logic/ Cslib.lean`. Since each file edit is independent, individual files can also be reverted in isolation if a specific transformation causes issues.
