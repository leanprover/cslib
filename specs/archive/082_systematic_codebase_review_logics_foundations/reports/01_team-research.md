# Research Report: Task #82

**Task**: Systematic codebase review of Logics/ and Foundations/ for publication quality
**Date**: 2026-06-10
**Mode**: Team Research (4 teammates)
**Scope**: 180 files touched on `feat/foundations-logic` branch across `Cslib/Logics/` and `Cslib/Foundations/`

## Summary

Four parallel research angles converged on a clear picture of what needs attention for publication quality. The codebase infrastructure (typeclasses, proof system hierarchy, module organization) is already publication-quality. The main gaps are surface-level consistency issues — naming conventions, documentation coverage, section structure, and CI validation — that can be addressed systematically without changing any proof logic.

The most impactful finding is that **~81 `def`/`abbrev` names use snake_case where Mathlib convention requires lowerCamelCase** (theorem/lemma names in snake_case are correct). This is the most visible convention violation an external reviewer would flag. Secondary concerns include docstring gaps in several files, unnamed sections, stale ORGANISATION.md, and CI tool validation not yet performed.

**Key decision needed**: Task 82 should complement task 81 (which handles PR 1-specific cleanup) by focusing on cross-cutting consistency, documentation gaps outside PR 1's scope, CI readiness, and alignment with CONTRIBUTING.md requirements.

## Key Findings

### 1. `def` Names in snake_case Need camelCase Rename [HIGH]

**Source**: Teammates B, C (confirmed by A)

Lean 4/Mathlib convention: `lowerCamelCase` for `def`/`abbrev`, `snake_case` for `theorem`/`lemma`. The codebase has ~81 `def` names in snake_case — a clear violation. The 318 snake_case theorem/lemma names are correct.

**Worst offenders**:
- `Foundations/Logic/Metalogic/DeductionHelpers.lean`: `deduction_axiom`, `deduction_imp_self`, `deduction_assumption_other`, `deduction_mp_under_imp`
- `Foundations/Logic/Theorems/BigConj.lean`: `bigconj`, `negBigconj` (lowercase compound)
- Scattered across Bimodal metalogic: `c5_backward_walk`, `hilbert_cut`, etc.

~25 existing camelCase defs (e.g., `collectDerivInl`, `boxDiamondPersistence`) show the convention is known but inconsistently applied.

**Confidence**: High

---

### 2. ORGANISATION.md Is Stale [HIGH]

**Source**: All 4 teammates

ORGANISATION.md describes `Cslib.Logic` as a flat top-level namespace listing `HoareLogic`, `LinearLogic`, etc. The actual structure is:

| Namespace | Directory | Purpose |
|-----------|-----------|---------|
| `Cslib.Logic` | `Cslib/Foundations/Logic/` | Shared infrastructure (typeclasses, axioms, theorems) |
| `Cslib.Logic.Modal` | `Cslib/Logics/Modal/` | Concrete modal logic |
| `Cslib.Logic.PL` | `Cslib/Logics/Propositional/` | Concrete propositional logic |
| `Cslib.Logic.Temporal` | `Cslib/Logics/Temporal/` | Concrete temporal logic |
| `Cslib.Logic.Bimodal` | `Cslib/Logics/Bimodal/` | Concrete bimodal logic |

The `Cslib.Logic` namespace spanning both `Foundations/Logic/` and `Logics/` is coherent (Teammate D argues it's defensible — infrastructure at root, specific logics as sub-namespaces) but undocumented.

**Confidence**: High

---

### 3. Remaining `sorry` Stubs [HIGH]

**Source**: Teammates B, C

38 `sorry` instances across 9 files, concentrated in Bimodal:
- `ChronicleToCountermodel.lean`: 16
- `Bundle/SuccRelation.lean`: 7
- `ChronicleToCountermodelBasic.lean`: 5
- `Completeness/Dense.lean`: 3
- Several files with 1-2 each

Most are blocked on tasks 36-37 (porting upstream results). Some lack annotation — all should have `-- sorry: blocked on task N` comments. For publication, files with `sorry` may need to be excluded from PR scope or explicitly marked as conjectures.

**Confidence**: High

---

### 4. Docstring Coverage Gaps [MEDIUM]

**Source**: Teammates C, D

Several files have significant docstring gaps, violating CONTRIBUTING.md's requirement to "Document your definitions and theorems":

| File | Defs | Docstrings | Gap |
|------|------|------------|-----|
| `Bimodal/Metalogic/Algebraic/LindenbaumQuotient.lean` | 37 | ~0 | Critical |
| `Bimodal/Metalogic/Algebraic/UltrafilterMCS.lean` | 25 | ~2 | Critical |
| `Bimodal/Metalogic/Algebraic/BooleanStructure.lean` | 21 | ~0 | Critical |
| `Bimodal/FrameConditions/Compatibility.lean` | 18 | ~0 | Severe |
| `Foundations/Logic/Theorems/Propositional/Core.lean` | 9 | 0 | Notable |
| `Foundations/Logic/Theorems/Temporal/TemporalDerived.lean` | ~10 | ~0 | Notable |

In contrast, `Foundations/Logic/Axioms.lean`, `ProofSystem.lean`, `Combinators.lean`, and `Modal/Basic.lean` have excellent documentation — these set the standard the others should follow.

**Confidence**: High

---

### 5. Unnamed Sections [MEDIUM]

**Source**: Teammates A, B

7 files in `Foundations/Logic/Theorems/` use bare `section` without names:
- `Combinators.lean`, `Propositional/Core.lean`, `Propositional/Connectives.lean`
- `Modal/Basic.lean`, `Modal/S5.lean`, `BigConj.lean`, `Temporal/TemporalDerived.lean`

Meanwhile `Axioms.lean` in the same directory uses descriptive named sections (`section Abbreviations`, `section Propositional`, `section Modal`). Mathlib style recommends named sections.

Additionally, 9 files across Logics/ have `@[expose] public section` without matching `end` statements (may be intentional with `module` keyword, but explicit `end` improves clarity).

**Confidence**: High (unnamed sections), Medium (missing `end`)

---

### 6. CI Validation Not Yet Performed [MEDIUM]

**Source**: Teammates C, D

CONTRIBUTING.md mandates several CI checks before PR submission:
- `lake shake --add-public --keep-implied --keep-prefix` (import minimization)
- `lake exe checkInitImports` (Cslib.Init imported by all files)
- `lake lint` (environment linters)
- `lake exe lint-style` (text linters, fixable with `--fix`)
- `lake exe mk_all --module` (up to date)

None of these have been run on the current branch. Task 81's Phase 3 trims imports manually, but if `lake shake` disagrees, the PR will fail CI.

**Confidence**: High

---

### 7. Missing Copyright Headers [LOW]

**Source**: Teammate C

4 barrel/re-export files lack the standard copyright header:
- `Bimodal/Metalogic/Algebraic/Algebraic.lean`
- `Bimodal/Metalogic/BXCanonical/BXCanonical.lean`
- `Bimodal/Metalogic/BXCanonical/Chronicle/ChronicleToCountermodelBasic.lean`
- `Bimodal/Metalogic/Bundle/Bundle.lean`

**Confidence**: High

---

### 8. Cross-Cutting Inconsistencies [LOW-MEDIUM]

**Source**: Teammates B, C

**Open statement patterns**: Files use inconsistent open styles — some open full namespaces, others use selective scoped opens, others use fully qualified deep opens. Mathlib style prefers minimal, scoped opens.

**Attribute usage**: `Modal/Basic.lean` uses `@[simp, scoped grind =]` while `Modal/FromPropositional.lean` uses plain `@[simp]`. Convention should be established.

**Variable declarations**: Foundations uses `{F : Type*}` (generic), Logics uses `{Atom : Type*}` (concrete). This is intentional but undocumented at the transition points.

**Confidence**: Medium

---

### 9. Very Large Files [LOW]

**Source**: Teammate B

7 files exceed 1000 lines, 3 exceed 3000:

| File | Lines |
|------|-------|
| `Bimodal/.../PointInsertion.lean` | 3553 |
| `Bimodal/.../CounterexampleElimination.lean` | 3526 |
| `Temporal/.../CounterexampleElimination.lean` | 3234 |
| `Temporal/.../PointInsertion.lean` | 2717 |

Splitting along logical boundaries would improve reviewability, but proofs may be deeply interconnected.

**Confidence**: Medium (splitting feasibility uncertain)

---

### 10. Infrastructure Quality Is Excellent [POSITIVE]

**Source**: Teammates B, D

The typeclass hierarchy (`Connectives`, `ProofSystem`, `InferenceSystem`, `DerivationSystem`, `HasHilbertTree`) is well-designed, composes cleanly, and is publication-quality. The Foundations layer properly abstracts over 4 concrete logic domains. The proof architecture (Hilbert-style derivation without notation/automation) is architecturally correct and well-motivated. No infrastructure changes needed.

**Confidence**: High

## Synthesis

### Conflicts Resolved

1. **Naming convention direction**: Teammate A raised whether to standardize on snake_case or camelCase broadly. Teammates B, C, and D clarified: **theorem names in snake_case are correct per Mathlib**. The issue is specifically `def`/`abbrev` names which should be lowerCamelCase. No systematic theorem rename needed. **Resolved**: camelCase for defs only.

2. **Sorry count**: Teammate B counted 23, Teammate C counted 38. Different search scopes — C was more thorough. **Resolved**: Use 38 as the comprehensive count.

3. **Section issues**: Teammate A flagged missing `end` statements (9 files); Teammate B flagged unnamed `section` keywords (7 files). These are distinct issues. **Resolved**: Both are valid — name sections AND add `end` where appropriate.

4. **Task 82 vs Task 81 scope**: Teammate D identified overlap risk. **Resolved**: Task 82 should focus on cross-cutting consistency, documentation gaps in non-PR1 files, CI readiness, and ORGANISATION.md updates. Task 81 handles PR 1-specific file-by-file cleanup.

### Gaps Identified

1. **Untouched files not audited**: Files in scope directories that weren't touched on this branch may have similar convention violations — these need a sweep.
2. **`Cslib.Init` import coverage**: Only 25 of 247 files directly import `Cslib.Init` — may rely on transitive import. `lake exe checkInitImports` needed to verify.
3. **`private` keyword remnants**: 12 instances remain in Logics/, 16 in Foundations/ — needs verification they're not in touched files (task 78 should have removed them).

### Recommendations

**Phase 1 — High-impact, low-effort** (should block PR):
1. Rename ~81 snake_case `def` names to camelCase
2. Run CI validation suite (`lake shake`, `lake lint`, `lake exe lint-style`, `lake exe checkInitImports`)
3. Annotate all bare `sorry` stubs with blocking-task references
4. Add copyright headers to 4 barrel files

**Phase 2 — Medium-impact, medium-effort** (should be done before publication):
5. Name all unnamed sections in Foundations/Logic/Theorems/
6. Add docstrings to worst-gap files (LindenbaumQuotient, UltrafilterMCS, BooleanStructure, Core.lean)
7. Update ORGANISATION.md to reflect actual Foundations/Logics split
8. Standardize `@[simp]` vs `@[scoped grind]` attribute conventions

**Phase 3 — Lower-priority** (nice to have):
9. Evaluate file splitting for 3000+ line files
10. Standardize open statement patterns across domains
11. Document variable declaration conventions at Foundations/Logics boundary

## Teammate Contributions

| Teammate | Angle | Status | Confidence | Key Contribution |
|----------|-------|--------|------------|-----------------|
| A | Conventions & naming | completed | high | Namespace mismatch identification, section analysis |
| B | Proof quality & structure | completed | high | def naming violations, sorry inventory, file size audit |
| C | Critic (gaps) | completed | high | 81 snake_case defs quantified, docstring gap severity, CI checklist |
| D | Strategic horizons | completed | high | Task scope differentiation, CI readiness, roadmap alignment |

## References

- `CONTRIBUTING.md` — CSLib contribution guidelines and PR checklist
- `NOTATION.md` — Notation conventions
- `ORGANISATION.md` — (stale) namespace organization
- `specs/081_pr1_foundations_logic_code_review/plans/01_pr1-code-review-plan.md` — Companion task plan
- `specs/059_pr1_foundations_logic/pr-description.md` — PR 1 description
