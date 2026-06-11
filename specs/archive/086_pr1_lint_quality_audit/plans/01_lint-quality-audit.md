# Implementation Plan: Systematic lint and quality audit of pr1/foundations-logic

- **Task**: 86 - Systematic lint and quality audit of all pr1/foundations-logic additions
- **Status**: [NOT STARTED]
- **Effort**: 1.5 hours
- **Dependencies**: None (task 85 already merged Propositional files onto branch)
- **Research Inputs**: specs/086_pr1_lint_quality_audit/reports/01_lint-quality-audit.md
- **Artifacts**: plans/01_lint-quality-audit.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: lean4
- **Lean Intent**: true

## Overview

Fix all 34 lint and quality issues identified by the research audit across 25 files on the `pr1/foundations-logic` branch. Issues span 6 categories: 9 flexible simp warnings, 2 unused simp_wf tactics, 13 non-minimal imports, 1 double blank line, and 0 issues in defLemma and noncomputable categories. The approach proceeds from trivial mechanical fixes to progressively riskier import chain restructuring, with build verification after each phase to catch breakage early.

### Research Integration

The research report (01_lint-quality-audit.md) cataloged 34 issues from running all 5 CI lint tools (`lake lint`, `lake exe lint-style`, `lake exe checkInitImports`, `lake exe mk_all --module --check`, `lake exe shake`) on the pr1/foundations-logic branch. Key findings: (1) 9 flexible simp calls need `simp only [...]` replacement, (2) 2 dead `simp_wf` lines can be deleted, (3) 13 files have non-minimal imports ranging from safe private removals to risky public chain restructuring, (4) 1 trivial double blank line. The report provides exact file paths, line numbers, and recommended fix strategies. The implementer agent should read the full report for per-file details.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No ROADMAP.md consulted for this plan.

## Goals & Non-Goals

**Goals**:
- Fix all 34 identified lint issues across the 25 files changed on pr1/foundations-logic
- Achieve zero warnings from all 5 CI lint checks on the changed files
- Maintain build correctness throughout (no regressions)

**Non-Goals**:
- Fixing lint issues in files not changed on pr1/foundations-logic
- Refactoring proof strategies or theorem structure
- Adding new features or changing semantics

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| `simp only` replacement introduces proof breakage | M | L | Use `simp?` output directly; verify each file builds after change |
| Import chain restructuring breaks downstream files | H | M | Phase 4 does full `lake build` after each import change; revert individual changes if broken |
| `lake exe shake` reports differ between branches | L | L | Run shake on the branch itself, not main |
| Removing `Cslib.Init` import loses transitive deps | M | M | Phase 3 limited to safe private removals only; full build verification |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3 | 2 |
| 4 | 4 | 3 |
| 5 | 5 | 4 |

Phases are fully sequential because each phase modifies files that later phases also touch, and each phase requires a clean build state before proceeding.

---

### Phase 1: Trivial fixes (double blank line and unused tactics) [COMPLETED]

**Goal**: Remove the 3 simplest issues that require no judgment calls.

**Tasks**:
- [ ] Checkout `pr1/foundations-logic` branch
- [ ] Delete double blank line in `Cslib/Logics/Propositional/ProofSystem/Instances.lean` (line 35)
- [ ] Delete unused `simp_wf` on line 102 of `Cslib/Logics/Propositional/Metalogic/DeductionTheorem.lean`
- [ ] Delete unused `simp_wf` on line 159 of `Cslib/Logics/Propositional/Metalogic/DeductionTheorem.lean`
- [ ] Run `lake build` to verify no breakage

**Timing**: 5 minutes

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Propositional/ProofSystem/Instances.lean` - Remove double blank line at line 35
- `Cslib/Logics/Propositional/Metalogic/DeductionTheorem.lean` - Delete 2 unused `simp_wf` lines

**Verification**:
- `lake build` succeeds with 0 errors
- The 3 deleted lines are confirmed absent

---

### Phase 2: Flexible simp to simp only [COMPLETED]

**Goal**: Replace all 9 flexible `simp` calls with explicit `simp only [...]` using `simp?` suggestions.

**Tasks**:
- [ ] In `Cslib/Foundations/Data/ListHelpers.lean`: replace 4 flexible simp calls with `simp only [...]` using `simp?` output
- [ ] In `Cslib/Logics/Propositional/Metalogic/DeductionTheorem.lean`: replace 3 flexible simp calls with `simp only [...]`
- [ ] In `Cslib/Logics/Propositional/Metalogic/MCS.lean`: replace 2 flexible simp calls with `simp only [...]`
- [ ] Run `lake build` after all replacements to verify correctness

**Timing**: 20 minutes

**Depends on**: 1

**Files to modify**:
- `Cslib/Foundations/Data/ListHelpers.lean` - 4 simp -> simp only replacements
- `Cslib/Logics/Propositional/Metalogic/DeductionTheorem.lean` - 3 simp -> simp only replacements
- `Cslib/Logics/Propositional/Metalogic/MCS.lean` - 2 simp -> simp only replacements

**Verification**:
- `lake build` succeeds
- `lake lint` shows 0 flexible simp warnings for these 3 files

---

### Phase 3: Safe private import removals [COMPLETED]

**Goal**: Remove unused `import Cslib.Init` from 3 Foundations files where it is a private (non-public) import that `lake exe shake` flagged as unnecessary.

**Tasks**:
- [x] Identify the 3 Foundations files with unused private `Cslib.Init` imports (consult research report for exact list) *(completed)*
- [x] **Task 3.2**: Remove the unused `import Cslib.Init` line from each file *(deviation: altered -- Cslib.Init cannot be removed from any Cslib module because checkInitImports CI tool requires all modules to transitively import Cslib.Init; removed unused `public import Mathlib.Data.Finset.Attr` from FrameConditions.lean instead)*
- [x] Run `lake build` after each removal to catch breakage immediately *(completed -- full build passes)*
- [x] Run `lake exe shake` on the modified files to confirm clean *(completed -- shake no longer reports Finset.Attr for FrameConditions; remaining Cslib.Init warnings are false positives due to checkInitImports requirement)*

**Timing**: 10 minutes

**Depends on**: 2

**Files to modify**:
- 3 Foundations/Logic files (exact paths in research report) - Remove unused `import Cslib.Init`

**Verification**:
- `lake build` succeeds after all removals
- `lake exe shake` shows no issues for the modified files

---

### Phase 4: Public import chain restructuring [COMPLETED]

**Goal**: Restructure imports in ~10 Theorems/Logics files to be minimal per `lake exe shake` recommendations.

**Tasks**:
- [x] Read the research report section on non-minimal imports to get the full list of ~10 files and their recommended import changes *(completed)*
- [x] **Task 4.2**: For each file, apply the recommended import simplification *(deviation: altered -- every shake recommendation was tested and found incorrect; all tested changes reverted)*:
  - Theorems/Propositional/Core.lean: replacing Combinators with ProofSystem FAILS (unknown namespace, missing b_combinator/flip/identity)
  - Theorems/Modal/S5.lean: replacing Modal.Basic with ProofSystem FAILS (unknown namespace, missing contraposition)
  - Consistency.lean: replacing Zorn with SetNotation+Chain FAILS (missing zorn_subset_nonempty)
  - Defs.lean: replacing FunLike.Basic+Set.Basic with Set.Operations FAILS (grind failures)
  - MCS.lean: replacing DeductionTheorem with Derivation FAILS (missing prop_has_deduction_theorem)
  - ListHelpers.lean: removing Cslib.Init passes build but FAILS checkInitImports
- [x] Run `lake build` after each file's import change to catch breakage immediately *(completed)*
- [x] If a change breaks the build, revert it and document as "not safe to simplify" *(completed -- all changes reverted)*
- [x] Run `lake exe shake` on all modified files to confirm clean output *(completed -- shake now runs; remaining warnings are all false positives as documented above)*

**Timing**: 30 minutes

**Depends on**: 3

**Files to modify**:
- ~10 Theorems and Logics files (exact paths in research report) - Restructure to minimal imports

**Verification**:
- `lake build` succeeds after all changes
- `lake exe shake` shows no remaining non-minimal imports in changed files

---

### Phase 5: Final CI verification [COMPLETED]

**Goal**: Run the full CI lint suite and confirm zero errors and zero warnings across all 25 changed files.

**Tasks**:
- [x] Run `lake lint` -- verify 0 warnings in changed files *(completed -- 0 errors in Foundations/ and Logics/Propositional/ files; 661 pre-existing errors in Bimodal/Temporal files)*
- [x] Run `lake exe lint-style` -- verify 0 style issues in changed files *(completed -- PASS)*
- [x] Run `lake exe checkInitImports` -- verify clean *(completed -- PASS)*
- [x] Run `lake exe mk_all --module --check` -- verify Cslib.lean is up to date *(completed -- "No update necessary")*
- [x] Run `lake exe shake` -- verify no non-minimal imports in changed files *(completed -- shake runs successfully; upstream CI has shake commented out per commit 2293f615; remaining warnings are false positives that fail when applied: Theorems files need theorem-bearing imports not just ProofSystem, Consistency needs Zorn, Defs needs Set.Basic for grind, MCS needs DeductionTheorem, and all Cslib.Init removals fail checkInitImports; one valid fix applied: removed unused Mathlib.Data.Finset.Attr from FrameConditions.lean)*
- [x] Document any residual warnings that are outside the 25-file scope (pre-existing, not introduced by this task) *(completed -- 661 lint errors in Bimodal/Temporal, 3 push_neg deprecation warnings in ChronicleConstruction.lean, 1 unused variable warning in ChronicleConstruction.lean)*

**Timing**: 5 minutes

**Depends on**: 4

**Files to modify**:
- None (verification only)

**Verification**:
- All 5 CI checks run: lake lint, lint-style, checkInitImports, mk_all pass; shake runs but is commented out in upstream CI (2293f615)
- Zero new warnings in the 25 changed files
- Pre-existing warnings documented above
- Removed noshake.json to match upstream (upstream deleted it in 2293f615 when upgrading to --add-public --keep-implied --keep-prefix flags)

## Testing & Validation

- [ ] `lake build` succeeds with 0 errors after every phase
- [ ] `lake lint` reports 0 flexible simp warnings in changed files
- [ ] `lake exe lint-style` reports 0 style violations in changed files
- [ ] `lake exe shake` reports 0 non-minimal imports in changed files
- [ ] `lake exe checkInitImports` passes clean
- [ ] `lake exe mk_all --module --check` passes clean

## Artifacts & Outputs

- `specs/086_pr1_lint_quality_audit/plans/01_lint-quality-audit.md` (this plan)
- `specs/086_pr1_lint_quality_audit/summaries/01_lint-quality-audit-summary.md` (after implementation)
- All 25 changed files on `pr1/foundations-logic` branch with zero lint issues

## Rollback/Contingency

All changes are on the `pr1/foundations-logic` branch. If any phase introduces unfixable issues:
1. `git stash` or `git checkout -- <file>` to revert individual file changes
2. If the entire phase is problematic, `git reset --hard HEAD` to the last known-good commit
3. Phase 4 (import restructuring) is the highest risk -- individual file changes should be committed separately to enable granular rollback
