# Implementation Plan: Fix @[simp] Linter Warnings

- **Task**: 67 - Fix 7 @[simp] linter warnings in PR-scope files
- **Status**: [COMPLETED]
- **Effort**: 0.5 hours
- **Dependencies**: None
- **Research Inputs**: specs/067_fix_simp_linter_warnings/reports/01_simp-linter-research.md
- **Artifacts**: plans/01_fix-simp-warnings.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: lean4
- **Lean Intent**: false

## Overview

Remove the `@[simp]` attribute from 7 lemmas across 2 files where the simpNF linter correctly flags the LHS as redundant. All 7 lemmas target derived connectives defined via `abbrev`, causing simp to unfold the LHS before the lemma can match. No downstream code uses these lemmas via bare `simp` -- all usages are `simp only` or explicit `.mp`/`.mpr` calls, which work regardless of `@[simp]` status.

### Research Integration

The research report (01_simp-linter-research.md) confirmed:
- Root cause: `abbrev`-defined connectives (`neg`, `some_future`, `some_past`, `all_future`, `all_past`) unfold transparently, making their simp lemmas unreachable by the default simp set.
- Fix: Remove `@[simp]` from all 7 lemmas (the only viable approach).
- Zero downstream breakage risk: all usages are via `simp only` or explicit calls.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

This task advances PR readiness for Task 59 (PR 1: Foundations/Logic), which depends on tasks 66 and 67 completing before submission. Fixing linter warnings is a prerequisite for CI compliance.

## Goals & Non-Goals

**Goals**:
- Eliminate all 7 simpNF linter warnings in PR-scope files
- Maintain full build and test compatibility (zero breakage)

**Non-Goals**:
- Changing connective definitions from `abbrev` to `def`
- Restructuring lemma LHS to match canonical simp form
- Addressing linter warnings outside PR-scope files

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Bare `simp` call depends on removed lemma | H | Very Low | Research confirmed zero bare `simp` usages; `lake build` will catch any |
| Task 66 renames change lemma names | L | Medium | Fix is independent of naming; apply to whatever names exist at implementation time |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |

Phases within the same wave can execute in parallel.

### Phase 1: Remove @[simp] Annotations [COMPLETED]

**Goal**: Delete the `@[simp]` attribute from all 7 flagged lemmas across 2 files.

**Tasks**:
- [x] Remove `@[simp]` from `neg_iff` in `Cslib/Logics/Temporal/Semantics/Satisfies.lean`
- [x] Remove `@[simp]` from `some_future_iff` in `Cslib/Logics/Temporal/Semantics/Satisfies.lean`
- [x] Remove `@[simp]` from `some_past_iff` in `Cslib/Logics/Temporal/Semantics/Satisfies.lean`
- [x] Remove `@[simp]` from `all_future_iff` in `Cslib/Logics/Temporal/Semantics/Satisfies.lean`
- [x] Remove `@[simp]` from `all_past_iff` in `Cslib/Logics/Temporal/Semantics/Satisfies.lean`
- [x] Remove `@[simp]` from `toModal_neg` in `Cslib/Logics/Propositional/Embedding.lean`
- [x] Remove `@[simp]` from `toTemporal_neg` in `Cslib/Logics/Propositional/Embedding.lean`

**Timing**: 10 minutes

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Temporal/Semantics/Satisfies.lean` - Remove `@[simp]` from 5 lemmas (neg_iff, some_future_iff, some_past_iff, all_future_iff, all_past_iff)
- `Cslib/Logics/Propositional/Embedding.lean` - Remove `@[simp]` from 2 lemmas (toModal_neg, toTemporal_neg)

**Verification**:
- Each file saves without syntax errors
- Grep confirms no `@[simp]` on the 7 target lemmas

---

### Phase 2: Build Verification [COMPLETED]

**Goal**: Confirm the full project builds cleanly with zero new errors or warnings.

**Tasks**:
- [x] Run `lake build` and verify zero errors
- [x] Confirm `Cslib/Logics/Temporal/Metalogic/Soundness.lean` still builds (heaviest downstream consumer)
- [x] Verify the 7 simpNF warnings no longer appear in linter output

**Timing**: 20 minutes

**Depends on**: 1

**Files to modify**: None (verification only)

**Verification**:
- `lake build` exits with code 0
- No new errors or warnings introduced

## Testing & Validation

- [x] `lake build` succeeds with zero errors
- [x] Soundness.lean `simp only` calls continue to work
- [x] No new linter warnings introduced
- [x] The 7 original simpNF warnings are eliminated

## Artifacts & Outputs

- `specs/067_fix_simp_linter_warnings/plans/01_fix-simp-warnings.md` (this plan)
- `specs/067_fix_simp_linter_warnings/summaries/01_fix-simp-warnings-summary.md` (post-implementation)

## Rollback/Contingency

Revert the 7 annotation removals by re-adding `@[simp]` before each affected lemma. Since the change is purely attribute deletion with no proof content changes, rollback is trivial via `git checkout` of the two modified files.
