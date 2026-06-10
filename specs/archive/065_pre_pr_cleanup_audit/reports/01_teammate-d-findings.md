# Teammate D (Horizons): Strategic Alignment and PR Strategy

**Task**: 65 - Audit repo for pre-PR cleanup and create refactoring tasks
**Date**: 2026-06-09
**Role**: Long-term alignment, strategic direction, scope optimization

## Key Findings

### 1. The Cleanup Scope Is Narrower Than It Appears

The task description lists 9 cleanup categories (dead code, unused imports, sorry instances, misplaced files, duplicate code, naming inconsistencies, docstrings, style violations, structural issues). However, several of these are already handled or minimally impactful:

- **Sorry instances**: Only 1 sorry exists across all PR-target code (Foundations + Modal + Temporal) -- in `Temporal/Metalogic/Chronicle/Frame.lean:105` (`t_le_refl`). Task 58 already covers removing it. The 9 sorry-containing files are all in Bimodal, which is excluded from PRs entirely.
- **Misplaced files**: Task 57 (COMPLETED) already moved generic temporal theorems to `Foundations/Logic/Theorems/Temporal/` and refactored Bimodal duplicates to use the bridge pattern. The 610-line duplication issue is resolved -- the files now use `wrap`/`unwrap` delegation.
- **Module docstrings**: 58 of 59 PR-target files already have `/-!` module docstrings. Only `Metalogic.lean` (a barrel file) lacks one -- and barrel files conventionally don't need them.
- **License headers**: All sampled PR-target files have proper Apache 2.0 headers with correct attribution.
- **Style violations**: CI already runs `lint-style-action` and `mathlibStandardSet` linting. The existing CI pipeline (`lean_action_ci.yml`) enforces style compliance.

**Implication**: The audit should focus on what CI *doesn't* catch, not duplicate CI's job.

### 2. The 6-PR Sequential Chain Is the Right Structure But Contains Parallelism

Tasks 58-64 define a dependency chain: 58 -> 59 -> 60 || 61 -> 62 -> 63 -> 64. This is well-thought-out:
- PR 1 (Foundations/Logic, task 59) must go first because Temporal/Modal Metalogic imports `Consistency.lean`
- PRs 2 and 3 (Modal Metalogic + Temporal non-metalogic) are independent and can be submitted in parallel
- PRs 4-6 form a strict chain (Temporal Metalogic -> Chronicle infra -> Completeness theorem)

This structure matches the import dependency graph exactly. Cleanup tasks should NOT disrupt this ordering. Any cleanup that touches files across multiple PR boundaries is a risk.

### 3. Cleanup Should Be Strictly PR-Scoped, Not Repo-Wide

The task description says "audit the entire repo." This is overbroad. The strategic priority is getting PRs 59-64 merged. Cleanup should focus exclusively on the ~47 files across 3 module trees that will be submitted:
- `Foundations/Logic/` (16 files, ~3,675 lines)
- `Logics/Modal/` (11 files, ~2,068 lines)
- `Logics/Temporal/` (32 files, ~14,328 lines)

Cleaning up Bimodal (50,832 lines, 9 sorry files) or other non-PR directories is wasted effort -- those won't face reviewer scrutiny and may change during ongoing porting work. Bimodal cleanup should wait until its sorries are resolved and it's ready for its own PR sequence.

### 4. `lake shake` Is Currently Disabled in CI -- This Is a Hidden Risk

The CI workflow comments out `lake shake` with a note. This means unused imports are NOT currently checked. When PRs are submitted, reviewers may run shake manually and find issues. Running `lake shake` locally and fixing unused imports should be a cleanup task.

### 5. The `checkInitImports` Script Is a Hard Gate

The CI runs `lake exe checkInitImports` which verifies all modules transitively import `Cslib.Init`. The new files from task 57 (`Foundations/Logic/Theorems/Temporal/`) need to be verified against this. Any new barrel files or re-exports must maintain this invariant.

### 6. Naming Convention Consistency Is Good But Should Be Verified

The sampled theorem names use consistent `snake_case` (e.g., `imp_trans`, `temporal_lindenbaum`, `mcs_bot_not_mem`). This matches Mathlib conventions. However, a systematic scan across all 59 PR-target files would catch any outliers that slipped through during porting.

## Recommended Approach

### Ruthless Prioritization: 3 Tiers

**Tier 1 -- PR Blockers (must fix before any PR):**
1. Remove the sole sorry in `Frame.lean` (already covered by task 58)
2. Run `lake shake` on PR-target files and fix unused imports (not in CI, but reviewers will catch)
3. Verify `checkInitImports` passes with current state
4. Run `lake build --wfail --iofail` to confirm zero warnings in PR scope

**Tier 2 -- Review Friction Reducers (fix before first PR submission):**
5. Add docstring to `Temporal/Metalogic.lean` barrel file
6. Verify naming conventions are consistent across all 59 PR-target files
7. Check for any `#check` or `#eval` debug lines left in PR-target files
8. Ensure each PR's file set is self-contained (no dangling imports outside PR scope)

**Tier 3 -- Nice-to-Have (defer or skip):**
9. Repo-wide dead code analysis (only matters for submitted files)
10. Bimodal cleanup (not going to PR review)
11. Cross-module refactoring (risk outweighs benefit before PRs merge)

### Task Expansion Strategy

Create **5-7 subtasks**, grouped by PR boundary rather than cleanup category:

1. **CI baseline + sorry fix** (already task 58 -- don't duplicate, just verify it's complete)
2. **Import cleanup**: Run `lake shake` across PR-target modules, fix results
3. **Naming/style audit**: Systematic check of theorem names, variable names, namespace usage across PR files
4. **Debug artifact cleanup**: Remove any `#check`, `#eval`, `set_option trace.*`, commented-out code in PR files
5. **PR self-containment verification**: For each PR's file set, verify imports resolve within-PR or to already-merged upstream
6. **Docstring gap fill**: Add/improve module docstrings where missing or insufficient (only the barrel file)
7. **(Optional) Bimodal sorry inventory**: Catalog the 9 sorry files with dependency analysis for future PR planning -- but explicitly mark as non-blocking

**Why PR-scoped grouping, not category grouping**: A task like "fix all naming issues" would span 6 PRs and create review-blocking dependencies. A task like "prepare PR 1 files" (Foundations/Logic) can be completed and verified independently.

### Automation Opportunities

- `lake shake --fix` can automatically remove unused imports
- `lake lint` already runs via CI -- no manual task needed
- `lake exe mk_all --check --module` verifies module registration
- A simple `grep -rn '#check\|#eval\|set_option trace' Cslib/` can find debug artifacts
- `grep -rn 'sorry' Cslib/Foundations Cslib/Logics/Modal Cslib/Logics/Temporal` confirms sorry-free status

These should be incorporated into a pre-PR checklist script rather than individual tasks. Consider creating a `scripts/pre-pr-check.sh` that runs all automated checks in sequence.

## Evidence/Examples

| Check | Current Status | Action Needed |
|-------|---------------|---------------|
| Sorry count (PR scope) | 1 (Frame.lean:105) | Fix via task 58 |
| Module docstrings | 58/59 files have them | Add to Metalogic.lean barrel |
| License headers | All checked files pass | Verify remaining |
| `lake shake` | Disabled in CI | Run locally, fix findings |
| `checkInitImports` | Runs in CI | Verify new files pass |
| Naming conventions | Consistent in samples | Full scan needed |
| Task 57 completion | Bridge pattern implemented | Verified -- no remaining duplication |
| Bimodal sorries | 9 files | Not blocking; defer cleanup |

## Confidence Level

**High** for the scoping recommendation (focus on PR-target files only) and prioritization tiers. The evidence strongly supports that most cleanup categories are either already handled or automatable.

**Medium** for the task expansion strategy -- the optimal number of subtasks depends on how much `lake shake` and naming audit actually find, which requires running them first.

**Key strategic risk**: Over-scoping the cleanup to cover the entire repo (including 50K lines of Bimodal code with active sorries) would delay PR submission by weeks with no benefit. The goal is PR readiness for 47 files, not repo perfection.
