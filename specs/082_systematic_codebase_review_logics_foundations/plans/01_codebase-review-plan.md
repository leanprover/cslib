# Implementation Plan: Task #82

- **Task**: 82 - Systematic codebase review of Logics/ and Foundations/ for publication quality
- **Status**: [IMPLEMENTING]
- **Effort**: 10 hours
- **Dependencies**: Task 81 (PR 1 code review, in progress)
- **Research Inputs**: specs/082_systematic_codebase_review_logics_foundations/reports/01_team-research.md
- **Artifacts**: plans/01_codebase-review-plan.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: lean4
- **Lean Intent**: false

## Overview

Bring Logics/ and Foundations/ to publication quality by systematically addressing 10 cross-cutting findings from the team research report. The scope covers 247 Lean files across 5 top-level directories (Foundations/Logic, Logics/Modal, Logics/Temporal, Logics/Bimodal, Logics/Propositional). Task 81 handles PR 1-specific file-by-file cleanup of 15 Foundations/Logic files; this task complements it by covering camelCase convention enforcement (~81+ snake_case defs), documentation gaps, CI validation, ORGANISATION.md rewrite, sorry annotation, section naming, copyright headers, and cross-cutting consistency. All changes must pass `lake build` and no proof logic is altered.

### Research Integration

The team research report (4 teammates, high confidence) identified 10 findings organized by priority. Key quantitative data integrated into this plan:
- 81+ `def`/`abbrev` names in snake_case requiring camelCase rename (Bimodal: 311, Temporal: 65, Propositional: 12, Foundations: 4, Modal: 3)
- 38 sorry stubs across 9 files (all in Bimodal), most blocked on tasks 36-37
- 6 files with critical docstring gaps (37+ undocumented defs each)
- 7 unnamed sections in Foundations/Logic/Theorems/
- 4 barrel files missing copyright headers
- ORGANISATION.md entirely stale (describes flat `Cslib.Logic` namespace)
- CI tools (lake shake, lake lint, lake exe lint-style, lake exe checkInitImports) not yet run

### Prior Plan Reference

Task 81 plan (01_pr1-code-review-plan.md) provides useful calibration: 6 phases, 4 hours, fully sequential. Phases 1-2 are completed. That plan covers formatting, import trimming, file relocation, and coordinated renames within the 15 Foundations/Logic files of PR 1. This plan avoids overlap by focusing on Logics/ files and cross-cutting concerns that span the full 247-file scope.

### Roadmap Alignment

This plan advances the overall porting project toward publication quality. The ROADMAP.md documents the Foundations/Logics split architecture. Completing this task will:
- Align naming conventions with Mathlib standards across all ported modules
- Document the actual namespace/directory structure in ORGANISATION.md
- Validate CI readiness for the first PR submission

## Goals & Non-Goals

**Goals**:
- Rename all snake_case `def`/`abbrev` names to lowerCamelCase across Logics/ and Foundations/
- Add docstrings to the 6 worst-gap files identified in research
- Name all 7 unnamed sections in Foundations/Logic/Theorems/
- Annotate all 38 sorry stubs with blocking-task references
- Add copyright headers to 4 barrel files
- Rewrite ORGANISATION.md to reflect actual Foundations/Logics directory structure
- Run full CI validation suite and fix any issues found
- Maintain zero build errors throughout

**Non-Goals**:
- Changing proof strategies, logic structure, or proof system architecture
- Splitting large files (3000+ lines) -- evaluated as low priority with uncertain feasibility
- Standardizing open statement patterns across all files (low priority, high churn)
- Modifying files already being handled by task 81 (Foundations/Logic PR 1 scope)
- Resolving sorry stubs (blocked on tasks 36-37, out of scope)

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| camelCase renames break downstream references | H | M | Use systematic grep + sed pipeline; verify with `lake build` after each file group |
| Naming overlap with task 81 renames | M | L | Task 81 covers only Foundations/Logic (4 snake_case defs); this task covers Logics/ (391 defs). Minimal overlap. |
| `lake shake` removes imports that are intentionally public | M | M | Run with `--keep-implied --keep-prefix` flags per CONTRIBUTING.md; review removals before accepting |
| `lake lint` / `lake exe lint-style` produce many warnings | M | H | Triage by severity; fix critical/high, document low-priority as future work |
| Docstring additions are low quality without domain expertise | M | M | Follow the excellent patterns in Axioms.lean and Combinators.lean; focus on type signatures and purpose, not proof strategy |
| sorry annotation comments trigger sorry-count confusion | L | L | Use consistent format: `-- sorry: blocked on task N` |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1, 2, 3 | -- |
| 2 | 4, 5 | 1 |
| 3 | 6 | 4, 5 |

Phases within the same wave can execute in parallel.

---

### Phase 1: Sorry annotations, copyright headers, and section naming [COMPLETED]

**Goal**: Address the three smallest, lowest-risk findings (findings 3, 5, 7) that require no name changes and have no downstream impact.

**Tasks**:
- [ ] Annotate all unannotated sorry stubs across 9 Bimodal files with `-- sorry: blocked on task {N}` comments (tasks 36-37)
- [ ] Verify sorry annotation completeness: `grep -rn 'sorry' Cslib/Logics/Bimodal/ --include="*.lean"` should show all sorrys with adjacent comments
- [ ] Add copyright headers to 4 barrel files:
  - `Cslib/Logics/Bimodal/Metalogic/Algebraic/Algebraic.lean`
  - `Cslib/Logics/Bimodal/Metalogic/BXCanonical/BXCanonical.lean`
  - `Cslib/Logics/Bimodal/Metalogic/BXCanonical/Chronicle/ChronicleToCountermodelBasic.lean`
  - `Cslib/Logics/Bimodal/Metalogic/Bundle/Bundle.lean`
- [ ] Name all 7 unnamed sections in Foundations/Logic/Theorems/:
  - `Combinators.lean`: `section` -> `section Combinators`
  - `Propositional/Core.lean`: `section` -> `section Core`
  - `Propositional/Connectives.lean`: `section` -> `section Connectives`
  - `Modal/Basic.lean`: `section` -> `section Basic`
  - `Modal/S5.lean`: `section` -> `section S5`
  - `BigConj.lean`: `section` -> `section BigConj`
  - `Temporal/TemporalDerived.lean`: `section` -> `section TemporalDerived`
- [ ] Run `lake build` to verify

**Timing**: 1 hour

**Depends on**: none

**Files to modify**:
- 9 Bimodal Metalogic files (sorry annotations)
- 4 barrel files (copyright headers)
- 7 Foundations/Logic/Theorems files (section naming)

**Verification**:
- `lake build` passes
- All sorry stubs have adjacent blocking-task comments
- All 4 barrel files have copyright headers
- No bare `section` lines remain in Foundations/Logic/Theorems/

---

### Phase 2: Docstring coverage for worst-gap files [COMPLETED]

**Goal**: Add module-level and definition-level docstrings to the 6 files with critical/severe documentation gaps, following the patterns established in Axioms.lean and Combinators.lean.

**Tasks**:
- [ ] Add module docstring and definition docstrings to `Bimodal/Metalogic/Algebraic/LindenbaumQuotient.lean` (~37 defs, 0 docstrings)
- [ ] Add module docstring and definition docstrings to `Bimodal/Metalogic/Algebraic/UltrafilterMCS.lean` (~25 defs, ~2 docstrings)
- [ ] Add module docstring and definition docstrings to `Bimodal/Metalogic/Algebraic/BooleanStructure.lean` (~21 defs, 0 docstrings)
- [ ] Add module docstring and definition docstrings to `Bimodal/FrameConditions/Compatibility.lean` (~18 defs, 0 docstrings)
- [ ] Add module docstring and definition docstrings to `Foundations/Logic/Theorems/Propositional/Core.lean` (~9 defs, 0 docstrings)
- [ ] Add module docstring and definition docstrings to `Logics/Temporal/Theorems/TemporalDerived.lean` (~10 defs, 0 docstrings) -- note: also covered by task 81 for double-blank-line cleanup but not docstrings
- [ ] Run `lake build` to verify docstrings do not introduce errors

**Timing**: 2 hours

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Bimodal/Metalogic/Algebraic/LindenbaumQuotient.lean` - Add ~37 docstrings
- `Cslib/Logics/Bimodal/Metalogic/Algebraic/UltrafilterMCS.lean` - Add ~23 docstrings
- `Cslib/Logics/Bimodal/Metalogic/Algebraic/BooleanStructure.lean` - Add ~21 docstrings
- `Cslib/Logics/Bimodal/FrameConditions/Compatibility.lean` - Add ~18 docstrings
- `Cslib/Foundations/Logic/Theorems/Propositional/Core.lean` - Add ~9 docstrings
- `Cslib/Logics/Temporal/Theorems/TemporalDerived.lean` - Add ~10 docstrings (if not already covered by task 81)

**Verification**:
- `lake build` passes
- Each of the 6 files has a module-level `/-! ... -/` docstring
- All public `def`/`abbrev`/`theorem` declarations in these files have `/-- ... -/` docstrings

---

### Phase 3: ORGANISATION.md rewrite [COMPLETED]

**Goal**: Rewrite ORGANISATION.md to accurately reflect the current Foundations/Logics directory structure, namespace conventions, and module dependency hierarchy.

**Tasks**:
- [ ] Read current ORGANISATION.md and identify all stale content
- [ ] Rewrite to document:
  - The Foundations/Logics split and its rationale
  - The `Cslib.Logic` namespace spanning both directories (infrastructure at root, specific logics as sub-namespaces)
  - The module dependency structure: Foundations -> Propositional -> Modal/Temporal -> Bimodal
  - The directory tree for both Foundations/Logic/ and Logics/
- [ ] Preserve the existing non-Logic sections (Foundations/Data, Control, Semantics, Languages, Computability) updating only as needed
- [ ] Ensure consistency with the Mermaid diagram in ROADMAP.md

**Timing**: 1 hour

**Depends on**: none

**Files to modify**:
- `ORGANISATION.md` - Full rewrite of Logic section

**Verification**:
- ORGANISATION.md accurately describes the current directory structure
- All directories mentioned in ORGANISATION.md exist on disk
- Module dependency description matches ROADMAP.md Mermaid diagram

---

### Phase 4: camelCase rename -- Foundations and small modules [COMPLETED]

**Goal**: Rename snake_case `def`/`abbrev` names to lowerCamelCase in Foundations/ (4 defs), Logics/Modal/ (3 defs), and Logics/Propositional/ (12 defs), plus propagate all downstream references.

**Tasks**:
- [ ] Inventory all snake_case `def`/`abbrev` names in Foundations/ (~4): `deduction_axiom`, `deduction_imp_self`, `deduction_assumption_other`, `deduction_mp_under_imp` in DeductionHelpers.lean
- [ ] Rename each to lowerCamelCase: `deductionAxiom`, `deductionImpSelf`, `deductionAssumptionOther`, `deductionMpUnderImp`
- [ ] Grep for all downstream references and update them
- [ ] Inventory all snake_case `def`/`abbrev` names in Logics/Modal/ (~3) and rename
- [ ] Inventory all snake_case `def`/`abbrev` names in Logics/Propositional/ (~12) and rename
- [ ] Propagate all reference changes to downstream files (Temporal, Bimodal that reference these)
- [ ] Run `lake build` to verify

**Timing**: 1.5 hours

**Depends on**: 1

**Files to modify**:
- `Cslib/Foundations/Logic/Metalogic/DeductionHelpers.lean` - Rename 4 defs
- `Cslib/Logics/Modal/` - Rename ~3 defs + update references
- `Cslib/Logics/Propositional/` - Rename ~12 defs + update references
- Various downstream files in Logics/ that reference renamed identifiers

**Verification**:
- `lake build` passes
- `grep -rn 'def [a-z][a-zA-Z]*_[a-zA-Z]' Cslib/Foundations/ Cslib/Logics/Modal/ Cslib/Logics/Propositional/ --include="*.lean"` returns only theorem/lemma names (no def/abbrev)
- No broken references

---

### Phase 5: camelCase rename -- Temporal and Bimodal [COMPLETED]

**Goal**: Rename snake_case `def`/`abbrev` names to lowerCamelCase in Logics/Temporal/ (~65 defs) and Logics/Bimodal/ (~311 defs), working file by file with incremental build verification.

**Tasks**:
- [ ] Rename snake_case defs in Logics/Temporal/ (~65 defs across ~15 files)
  - Work directory by directory: Syntax/, Semantics/, ProofSystem/, Theorems/, Metalogic/
  - Run `lake build` after each directory group
- [ ] Rename snake_case defs in Logics/Bimodal/ (~311 defs across ~50 files)
  - Work directory by directory: Syntax/, Semantics/, ProofSystem/, Theorems/, FrameConditions/, Embedding/, Metalogic/
  - Run `lake build` after each major directory group
- [ ] For each rename: grep all files for references to the old name and update
- [ ] Special care for names used across module boundaries (e.g., `theorem_in_mcs` referenced from multiple Metalogic files)

**Timing**: 3.5 hours

**Depends on**: 1

**Files to modify**:
- ~15 files in `Cslib/Logics/Temporal/` - Rename ~65 defs
- ~50 files in `Cslib/Logics/Bimodal/` - Rename ~311 defs
- Cross-references in files that import from renamed modules

**Verification**:
- `lake build` passes
- `grep -rn '^\(noncomputable \)\?\(def\|abbrev\) [a-z][a-zA-Z]*_[a-zA-Z]' Cslib/Logics/Temporal/ Cslib/Logics/Bimodal/ --include="*.lean"` returns zero results
- No broken references across module boundaries

---

### Phase 6: CI validation and fixes [COMPLETED]

**Goal**: Run the full CI validation suite mandated by CONTRIBUTING.md and fix any issues discovered.

**Tasks**:
- [ ] Run `lake exe mk_all --module` and fix any discrepancies
- [ ] Run `lake exe checkInitImports` and ensure `Cslib.Init` is properly imported by all files
- [ ] Run `lake exe lint-style` and fix reported issues (use `--fix` flag where available)
- [ ] Run `lake lint` and triage warnings by severity
- [ ] Run `lake shake --add-public --keep-implied --keep-prefix` and evaluate import minimization suggestions
  - Accept safe removals
  - Document any intentionally kept imports
- [ ] Run final `lake build` to verify all fixes
- [ ] Document any remaining lint warnings as known issues (if low-priority)

**Timing**: 1 hour

**Depends on**: 4, 5

**Files to modify**:
- Potentially any file in Cslib/ depending on CI tool output
- `Cslib.lean` - May need updates from `mk_all`

**Verification**:
- `lake build` passes with zero errors
- `lake exe mk_all --module` reports no changes needed
- `lake exe checkInitImports` passes
- `lake exe lint-style` reports zero fixable issues
- `lake lint` warnings are either fixed or documented

---

## Testing & Validation

- [ ] `lake build` passes after each phase (incremental verification)
- [ ] Final `lake build` passes with zero errors
- [ ] No snake_case `def`/`abbrev` names remain (only snake_case `theorem`/`lemma` names, which are correct per Mathlib convention)
- [ ] All sorry stubs have blocking-task annotation comments
- [ ] All 6 docstring-gap files have module and definition docstrings
- [ ] ORGANISATION.md accurately reflects actual directory structure
- [ ] CI tools (`mk_all`, `checkInitImports`, `lint-style`) pass
- [ ] No overlap with task 81 changes (verify via git diff comparison)

## Artifacts & Outputs

- `specs/082_systematic_codebase_review_logics_foundations/plans/01_codebase-review-plan.md` (this file)
- `specs/082_systematic_codebase_review_logics_foundations/summaries/01_codebase-review-summary.md` (after implementation)
- Updated `ORGANISATION.md` (rewritten)
- ~395 renamed definitions across Logics/ and Foundations/
- ~120 docstrings added to 6 files
- CI validation results documented

## Rollback/Contingency

All changes are non-structural edits to existing files (renames, docstring additions, comment additions, header additions). Git provides full rollback via `git stash` or per-file `git checkout`. The phase structure ensures each phase starts from a known-good build state. If a camelCase rename cascade proves too complex in a single file group, that group can be deferred and addressed incrementally. The CI validation phase (Phase 6) runs last because earlier phases may introduce or resolve lint issues; running CI first would produce a misleading baseline.
