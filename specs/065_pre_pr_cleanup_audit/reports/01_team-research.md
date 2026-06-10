# Research Report: Task #65

**Task**: Audit repo for pre-PR cleanup and create refactoring tasks
**Date**: 2026-06-09
**Mode**: Team Research (4 teammates)

## Summary

The repo is in better shape than the task description implies. Most cleanup categories are already handled by CI or prior work (task 57). The critical insight is **scope narrowing**: cleanup should target only the ~47 PR-scope files (Foundations/Logic + Logics/Modal + Logics/Temporal), not the entire 343-file repo. Bimodal (50K+ lines, 25 sorries) is not going to PR review and cleanup there is wasted effort.

The actual PR blockers are few: 1 sorry in PR scope, 2 missing copyright headers, a disabled `lake shake` in CI, and ~740 lines of commented-out code to remove. The biggest structural issue — ~21K lines of code duplication between Temporal and Bimodal — is real but should be deferred (task 41 already tracks it, and refactoring before PRs land carries regression risk).

## Key Findings

### 1. Sorry Instances: 26 Total, But Only 1 in PR Scope (HIGH — CI BLOCKER)

All 4 teammates identified sorry instances. The critical finding is the **scope distinction**:

- **1 sorry in PR scope**: `Cslib/Logics/Temporal/Metalogic/Chronicle/Frame.lean:105` (`t_le_refl`) — this will fail CI (`--wfail` treats sorry warnings as errors). This is in PR5 (Chronicle infrastructure) scope.
- **25 sorries in Bimodal** (not going to PR): 12 in ChronicleToCountermodel (task 36 dependency), 7 in SuccRelation, 2 in UntilSinceCoherence, 1 in BXCanonical/Frame, 1 in Dense, 1 in ChronicleToCountermodelBasic, 1 in PointInsertion.

Task 58 (`ci_prep_sorry_fix_baseline`) already covers this. The sorry fix is a prerequisite for all PRs.

### 2. Scope Should Be PR-Target Files Only (~47 Files)

Teammate D's strongest finding, validated by C's PR feasibility analysis. The 47 files break down as:
- `Foundations/Logic/`: 16 files (~3,675 lines)
- `Logics/Modal/`: 11 files (~2,068 lines)
- `Logics/Temporal/`: 32 files (not yet fully quantified but includes Chronicle pipeline)

Cleaning Bimodal, Computability, Crypto, Languages, etc. does not advance PR readiness.

### 3. Commented-Out Code: ~740 Lines Across 19 Files (MEDIUM)

Teammate A found significant commented-out blocks that signal incomplete refactoring:

| File | Lines | Nature |
|------|-------|--------|
| `Temporal/Metalogic/MCS.lean` | 193 | Old proof strategies |
| `Temporal/Chronicle/PointInsertion.lean` | 167 | Abandoned proof attempts |
| `Modal/Metalogic/Completeness.lean` | 144 | Legacy code |
| `Temporal/Chronicle/CounterexampleElimination.lean` | 57 | Abandoned approaches |
| `Bimodal/Chronicle/CounterexampleElimination.lean` | 47 | Abandoned approaches |

Only the first 4 are in PR scope. These should be removed — they add no value and will attract reviewer comments.

### 4. Missing Copyright Headers: 2 in PR Scope (MEDIUM — CI Risk)

Teammate C identified 2 barrel files in PR scope lacking Mathlib-style copyright headers:
- `Cslib/Logics/Modal/Metalogic.lean`
- `Cslib/Logics/Temporal/Metalogic.lean`

Teammate B found 4 additional missing headers in Bimodal (out of PR scope). The `lint-style-action` CI step may reject files without headers.

### 5. Linter Suppression Overrides: 61 in PR Modules (MEDIUM-HIGH)

Across PR-relevant modules:
- `longLine` suppressions: 22 instances
- `emptyLine` suppressions: 14 instances
- `setOption` meta-suppressions: 7 instances
- `flexible`: 7 instances
- `unreachableTactic`: 6 instances
- `dupNamespace`: 5 instances

Nearly 48% of logic files suppress `longLine` or `emptyLine` linters. PR reviewers will push back on blanket `set_option linter.style.longLine false` at file scope. These should be fixed (shorten lines) rather than suppressed.

### 6. `lake shake` Disabled in CI (MEDIUM)

Both C and D independently flagged that `lake shake` is commented out in CI (`lean_action_ci.yml`). Unused imports are not enforced. Reviewers may run shake manually and find issues. Running `lake shake --fix` locally before submission would pre-empt this.

### 7. Code Duplication: ~21K Lines Across Modal/Temporal/Bimodal (LOW for PRs, HIGH long-term)

Teammate B's most significant structural finding. Three categories:

| Component | Files Duplicated | Lines |
|-----------|-----------------|-------|
| Chronicle pipeline (Temporal vs Bimodal) | 6 file pairs | ~21,580 |
| DeductionTheorem | 3 copies | ~750 |
| DerivationTree | 3 copies | ~300 |
| MCS theory | 3 copies | ~600 |
| TemporalContent/WitnessSeed | 2 copies each | ~400 |
| GeneralizedNecessitation | 2 copies | ~200 |

However, Teammate D correctly argues this is a Tier 3 item: the Bimodal copies use `FrameClass` parameterization that makes deduplication non-trivial, and aggressive refactoring before PRs land carries regression risk. Task 41 already tracks shared completeness infrastructure.

### 8. PR1 File Count Wrong (MEDIUM)

Teammate C found that task 59 lists 9 files for PR1 but there are actually 16 `.lean` files in `Foundations/Logic/`. The 7 unlisted files are transitive dependencies required for compilation. The PR description needs updating.

### 9. Temporal Metalogic Barrel Incomplete (LOW)

`Cslib/Logics/Temporal/Metalogic.lean` is missing imports for `ChronicleConstruction` and `CounterexampleElimination`. CI still passes because `Cslib.lean` imports them directly, but the barrel is incomplete.

### 10. `set_option maxHeartbeats` Overrides: 50 instances, 34 files at 8x+ (LOW-MEDIUM)

Teammate A found 50 maxHeartbeats overrides, with the worst at 32x default (`CounterexampleElimination.lean` at 6,400,000). These indicate proofs that may need optimization for CI performance. Most are in Bimodal (out of PR scope), but any in PR-scope files should be reviewed.

## Synthesis

### Conflicts Resolved

1. **Sorry count disagreement (26 vs 1)**: Not a real conflict — A reported the repo-wide total (26), D scoped to PR-target files (1). Both are correct. The actionable number is 1 (the `t_le_refl` sorry in Frame.lean).

2. **Copyright header count (6 vs 2)**: B reported 6 repo-wide, C scoped to PR-relevant (2). Following D's scope-narrowing recommendation, 2 is the actionable number. The 4 Bimodal barrel files can wait.

3. **Duplication priority**: B rates code duplication as HIGH priority; D rates it as Tier 3 (defer). Resolution: D is correct for PR readiness — refactoring ~21K lines before PRs land is high-risk, low-reward. The duplication is between Temporal (going to PR) and Bimodal (not going to PR), so reviewers won't see both copies in the same PR. Task 41 already tracks this for later.

4. **`def` vs `theorem` inconsistency**: B flagged this as MEDIUM. Resolution: This is architecturally intentional — Bimodal returns concrete `DerivationTree` terms (data, hence `def`), while Foundations returns existence proofs (hence `theorem`). Document the convention but don't change it.

### Gaps Identified

1. **No test coverage for logic modules** (C): CslibTests/ has 13 test files but none for Modal, Temporal, or Bimodal. While Lean's type checking is self-verifying, reviewers may ask for example computations or integration tests.

2. **No CODEOWNERS entry for logic modules** (C): PRs will route to global maintainers rather than domain experts. Low priority but easy to fix.

3. **`checkInitImports` invariant** (D): New files from task 57 need verification against this CI gate. Should be part of the pre-PR checklist.

4. **Temporal `FrameConditions.lean` sorry** (B): B flagged a potential sorry in `Foundations/Logic/Theorems/Temporal/FrameConditions.lean` that needs verification — this is in PR1 scope if confirmed.

### Recommendations

**Tier 1 — PR Blockers (must fix before any PR submission):**
1. Fix the `t_le_refl` sorry in `Temporal/Chronicle/Frame.lean` (task 58 covers this)
2. Add copyright headers to `Modal/Metalogic.lean` and `Temporal/Metalogic.lean`
3. Run `lake shake` on PR-target files and fix unused imports
4. Verify `lake build --wfail --iofail` produces zero warnings in PR scope
5. Remove commented-out code in PR-scope files (~560 lines across 4 files)

**Tier 2 — Review Friction Reducers:**
6. Fix `longLine` violations in PR-scope files (22 linter suppressions to resolve)
7. Complete the Temporal Metalogic barrel (add missing Chronicle imports)
8. Update PR1 task description to list all 16 files with correct line count
9. Create a `scripts/pre-pr-check.sh` that automates Tier 1 checks

**Tier 3 — Defer (post-PR or separate effort):**
10. Code duplication refactoring (task 41 already tracks this)
11. Bimodal sorry resolution (depends on task 36)
12. Test coverage for logic modules
13. High maxHeartbeats optimization
14. CODEOWNERS entry for logic modules

### Task Expansion Strategy

Create **5-7 subtasks grouped by PR boundary** (not by cleanup category) to avoid cross-PR blocking dependencies:

1. **Sorry fix + CI baseline** — Already task 58; verify it covers Frame.lean
2. **Import cleanup** — Run `lake shake` across PR-target modules, fix results
3. **Commented-out code removal** — Remove ~560 lines from 4 PR-scope files
4. **Copyright + barrel fixes** — Add headers to 2 files, complete Temporal barrel
5. **Linter compliance** — Fix longLine violations in PR-scope files (22 instances)
6. **PR description updates** — Correct file counts and line estimates in tasks 59-64
7. **(Optional) Pre-PR automation** — Create scripts/pre-pr-check.sh

## Teammate Contributions

| Teammate | Angle | Status | Confidence |
|----------|-------|--------|------------|
| A | Implementation quality (sorry, dead code, imports) | completed | high |
| B | Structure & organization (duplication, naming, style) | completed | high |
| C | Blind spots & PR feasibility (CI, tests, imports) | completed | high |
| D | Strategic alignment & scope optimization | completed | high |

## References

- `specs/ROADMAP.md` — Project roadmap and module dependency structure
- `specs/TODO.md` — Tasks 58-64 define the PR submission sequence
- `.github/workflows/lean_action_ci.yml` — CI configuration
- `.github/CODEOWNERS` — Code ownership
- Task 41 — Abstract shared completeness infrastructure (deduplication)
- Task 57 — Theorem organization (completed, resolved misplaced files)
- Task 58 — CI prep sorry fix baseline (covers the 1 PR-scope sorry)
