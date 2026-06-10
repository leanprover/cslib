# Implementation Plan: Fix Lint Naming Conventions

- **Task**: 66 - fix_lint_naming_conventions
- **Status**: [NOT STARTED]
- **Effort**: 3 hours
- **Dependencies**: None
- **Research Inputs**: reports/01_lint-naming-research.md
- **Artifacts**: plans/01_fix-lint-naming.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: lean4
- **Lean Intent**: true

## Overview

Rename 16 unique snake_case `def`/`abbrev` identifiers across 6 definition files to lowerCamelCase, satisfying the Mathlib `defsWithUnderscore` linter. The scope spans ~2,903 references across 95 Lean files in Temporal, Bimodal, Foundations, and ConservativeExtension modules, plus ~162 compound theorem/lemma names that embed these identifiers. A sed-based batch replacement strategy (longest compound matches first) is the recommended approach, verified safe against substring false positives by the research report. Done when `lake build` passes with zero new errors.

### Research Integration

Integrated findings from `reports/01_lint-naming-research.md`:
- 16 unique snake_case def/abbrev identifiers across 6 source files (not 19 as originally estimated)
- No substring false positives found -- sed global replacement is safe
- Critical ordering constraint: longest compound matches must be processed before shorter ones (e.g., `swap_temporal_some_future` before `swap_temporal` or `some_future`)
- 8 scoped notation bindings reference these defs and must also be updated
- ~273 additional snake_case defs exist outside task scope (future work)

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

This task is a code quality / lint compliance task. It does not directly advance any ROADMAP.md component but improves codebase hygiene across all completed Temporal and Bimodal modules.

## Goals & Non-Goals

**Goals**:
- Rename all 16 snake_case `def`/`abbrev` identifiers to lowerCamelCase
- Update all ~162 compound theorem/lemma names that embed these identifiers
- Update all 8 scoped notation bindings
- Update all ~2,903 downstream references across 95 files
- Pass `lake build` with no regressions

**Non-Goals**:
- Renaming the ~273 additional snake_case defs outside the temporal operator scope (separate future task)
- Adding `@[deprecated]` migration aliases (this is a private project, not an external library)
- Changing theorem/lemma naming convention (these remain snake_case per Mathlib convention)

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Partial sed replacement corrupts compound names | H | L | Process longest compound matches first; verify with `grep` for leftover snake_case |
| Missed reference causes build failure | M | L | Run `lake build` after each phase; grep audit for residual snake_case |
| Comments or doc strings contain informal usage of identifiers | L | M | Accept cosmetic residuals in comments if they do not affect compilation |
| Git conflict with concurrent work on same files | M | L | Create dedicated branch before starting; rebase if needed |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3 | 2 |
| 4 | 4 | 3 |

Phases within the same wave can execute in parallel.

### Phase 1: Tier 2 and Tier 3 Renames (Low-Impact Identifiers) [NOT STARTED]

**Goal**: Rename the 11 low-reference identifiers as a safe first pass to validate the sed approach and catch any unexpected issues before touching the high-impact identifiers.

**Tasks**:
- [ ] Create a git branch `task-66-lint-naming` from current HEAD
- [ ] Rename Tier 2 identifiers in definition files and all downstream references using sed:
  - `weak_future_left` -> `weakFutureLeft` (must precede `weak_future`)
  - `weak_future_right` -> `weakFutureRight` (must precede `weak_future`)
  - `weak_past_left` -> `weakPastLeft` (must precede `weak_past`)
  - `weak_past_right` -> `weakPastRight` (must precede `weak_past`)
  - `strong_release` -> `strongRelease`
  - `strong_trigger` -> `strongTrigger`
  - `weak_future` -> `weakFuture`
  - `weak_past` -> `weakPast`
  - `weak_until` -> `weakUntil`
  - `weak_since` -> `weakSince`
  - `neg_bigconj` -> `negBigconj` (includes `neg_bigconj_def` -> `negBigconj_def`)
- [ ] Verify no residual snake_case references for these 11 identifiers: `grep -rn 'weak_future\|weak_past\|weak_until\|weak_since\|strong_release\|strong_trigger\|neg_bigconj' Cslib/ --include="*.lean"`
- [ ] Run `lake build` and confirm zero new errors

**Timing**: 45 minutes

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Temporal/Syntax/Formula.lean` - 6 def renames (weak_future, weak_past, weak_until, weak_since, strong_release, strong_trigger)
- `Cslib/Logics/Temporal/Syntax/BigConj.lean` - 1 def rename (neg_bigconj)
- `Cslib/Foundations/Logic/Theorems/BigConj.lean` - 1 def rename (neg_bigconj)
- `Cslib/Logics/Bimodal/Theorems/TemporalDerived.lean` - 4 def renames (weak_future_left/right, weak_past_left/right)
- Downstream files referencing these identifiers (~5-10 files)

**Verification**:
- `grep` confirms zero residual snake_case matches for Tier 2/3 identifiers
- `lake build` succeeds

---

### Phase 2: Compound Theorem Name Renames (swap_temporal_*) [NOT STARTED]

**Goal**: Rename all compound theorem/lemma names that embed `swap_temporal` combined with other Tier 1 identifiers, before the simple identifier renames in Phase 3. This prevents partial replacements where `swap_temporal` would be renamed inside a compound name before the full compound is processed.

**Tasks**:
- [ ] Rename compound names that combine `swap_temporal` with other target identifiers (must be done before Phase 3):
  - `swap_temporal_strong_release` -> `swapTemporal_strongRelease`
  - `swap_temporal_strong_trigger` -> `swapTemporal_strongTrigger`
  - `swap_temporal_some_future` -> `swapTemporal_someFuture`
  - `swap_temporal_some_past` -> `swapTemporal_somePast`
  - `swap_temporal_all_future` -> `swapTemporal_allFuture`
  - `swap_temporal_all_past` -> `swapTemporal_allPast`
- [ ] Rename remaining `swap_temporal_*` compound theorem names (these do not contain other target identifiers, so ordering is flexible but must precede the simple `swap_temporal` rename):
  - `swap_temporal_involution` -> `swapTemporal_involution`
  - `swap_temporal_neg` -> `swapTemporal_neg`
  - `swap_temporal_diamond` -> `swapTemporal_diamond`
  - `swap_temporal_next` -> `swapTemporal_next`
  - `swap_temporal_prev` -> `swapTemporal_prev`
  - `swap_temporal_int_truth` -> `swapTemporal_int_truth`
  - `swap_temporal_derives` -> `swapTemporal_derives`
  - `swap_temporal_dual` -> `swapTemporal_dual`
  - `swap_temporal_subst` -> `swapTemporal_subst`
  - `provEquiv_swap_temporal_congr` -> `provEquiv_swapTemporal_congr`
  - `atoms_swap_temporal` -> `atoms_swapTemporal`
  - `embedFormula_swap_temporal` -> `embedFormula_swapTemporal`
  - `substFormula_swap_temporal` -> `substFormula_swapTemporal`
  - `substFreshWith_swap_temporal` -> `substFreshWith_swapTemporal`
  - `unembed_swap_temporal` -> `unembed_swapTemporal`
  - `liftFormula_swap_temporal` -> `liftFormula_swapTemporal`
- [ ] Verify no compound `swap_temporal_*` names remain: `grep -rn 'swap_temporal_' Cslib/ --include="*.lean"`
- [ ] Do NOT yet rename simple `swap_temporal` -- that happens in Phase 3

**Timing**: 30 minutes

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/Temporal/Syntax/Formula.lean` - theorem renames
- `Cslib/Logics/Bimodal/Syntax/Formula.lean` - theorem renames
- `Cslib/Logics/Bimodal/ProofSystem/Substitution.lean` - swap_temporal_subst
- `Cslib/Logics/Bimodal/Metalogic/Separation/Duality.lean` - swap_temporal_int_truth
- `Cslib/Logics/Bimodal/Metalogic/Algebraic/LindenbaumQuotient.lean` - swap_temporal_derives, provEquiv_swap_temporal_congr
- `Cslib/Logics/Bimodal/Metalogic/ConservativeExtension/Lifting.lean` - liftFormula_swap_temporal
- `Cslib/Logics/Temporal/Metalogic/Soundness.lean` - swap_temporal_dual
- All downstream files referencing these compound names (~15-25 files)

**Verification**:
- `grep -rn 'swap_temporal_' Cslib/ --include="*.lean"` returns zero results
- Build is NOT expected to succeed yet (simple `swap_temporal` still references old name)

---

### Phase 3: Core Identifier Renames (Tier 1) [NOT STARTED]

**Goal**: Rename the 5 high-impact Tier 1 identifiers (`swap_temporal`, `some_future`, `all_future`, `some_past`, `all_past`) and update all notation bindings. After this phase, every target identifier has been renamed.

**Tasks**:
- [ ] Rename the 5 core identifiers across all 95 affected files:
  - `swap_temporal` -> `swapTemporal` (~515 references across 33 files)
  - `some_future` -> `someFuture` (~581 references across 63 files)
  - `all_future` -> `allFuture` (~701 references across 78 files)
  - `some_past` -> `somePast` (~495 references across 56 files)
  - `all_past` -> `allPast` (~611 references across 70 files)
- [ ] Verify notation bindings were updated (these are handled by the sed since they reference `Formula.some_future` etc.):
  - `Cslib/Logics/Temporal/Syntax/Formula.lean` lines 84-87
  - `Cslib/Logics/Bimodal/Syntax/Formula.lean` lines 89-92
- [ ] Verify no residual snake_case references for any of the 16 target identifiers: `grep -rn 'some_future\|all_future\|some_past\|all_past\|swap_temporal' Cslib/ --include="*.lean"`
- [ ] Run `lake build` and confirm zero new errors

**Timing**: 45 minutes

**Depends on**: 2

**Files to modify**:
- `Cslib/Logics/Temporal/Syntax/Formula.lean` - 5 def renames + 4 notation bindings
- `Cslib/Logics/Bimodal/Syntax/Formula.lean` - 5 def renames + 4 notation bindings
- `Cslib/Logics/Bimodal/Metalogic/ConservativeExtension/ExtFormula.lean` - 5 def renames
- All 95 downstream files with references

**Verification**:
- Combined `grep` for all 16 original snake_case names returns zero matches
- `lake build` succeeds with no new errors

---

### Phase 4: Final Audit and Cleanup [NOT STARTED]

**Goal**: Comprehensive verification that all renames are complete, no regressions exist, and the codebase is clean.

**Tasks**:
- [ ] Run comprehensive grep audit for all 16 original identifiers across entire Cslib directory (including comments and doc strings)
- [ ] Run `lake build` as final confirmation
- [ ] Inspect any residual matches in comments/doc strings and update if they reference identifier names (not natural language)
- [ ] Verify the `defsWithUnderscore` linter no longer flags any of the 16 renamed identifiers
- [ ] Commit all changes on the task branch

**Timing**: 30 minutes

**Depends on**: 3

**Files to modify**:
- Any files with residual snake_case references in comments or doc strings

**Verification**:
- `lake build` passes cleanly
- `grep -rn 'some_future\|all_future\|some_past\|all_past\|swap_temporal\|weak_future\|weak_past\|weak_until\|weak_since\|strong_release\|strong_trigger\|neg_bigconj' Cslib/ --include="*.lean"` returns zero results (or only genuinely unrelated matches)
- No `defsWithUnderscore` warnings for the 16 renamed identifiers

## Testing & Validation

- [ ] `lake build` passes after Phase 1 (Tier 2/3 renames)
- [ ] `lake build` passes after Phase 3 (all renames complete)
- [ ] `lake build` passes after Phase 4 (final audit)
- [ ] grep audit for all 16 original snake_case identifiers returns zero matches
- [ ] No regressions in existing theorem proofs (verified by successful build)

## Artifacts & Outputs

- `specs/066_fix_lint_naming_conventions/plans/01_fix-lint-naming.md` (this plan)
- `specs/066_fix_lint_naming_conventions/summaries/01_fix-lint-naming-summary.md` (post-implementation)

## Rollback/Contingency

- Git branch `task-66-lint-naming` isolates all changes from main
- If sed produces incorrect results: `git checkout -- Cslib/` restores all files to pre-rename state
- If `lake build` fails after rename: inspect error messages to identify missed references, apply targeted fixes, re-run build
- Worst case: `git reset --hard HEAD~1` on the task branch to undo the last commit and retry
