# Teammate C Findings: Critic — Gaps, Blind Spots, and Completeness

**Task**: 82 - Systematic codebase review of Logics/ and Foundations/ for publication quality
**Date**: 2026-06-10
**Angle**: Gaps, blind spots, and cross-cutting concerns
**Confidence Level**: High

## Key Findings

### 1. ORGANISATION.md vs Actual Structure Mismatch (Medium)

ORGANISATION.md documents `Cslib.Logic` (singular, flat under root) as the namespace for logics. The actual codebase uses:
- `Cslib/Logics/` (plural directory) mapped via `module` keyword to `Cslib.Logic.*` namespace
- `Cslib/Foundations/Logic/` for shared infrastructure

This is not a bug — the `module` keyword handles the remapping — but ORGANISATION.md is stale. It shows `Cslib.Logic.HoareLogic`, `Cslib.Logic.LinearLogic`, etc., suggesting the document predates the current Logics/Foundations split. **If this is going to publication, ORGANISATION.md should reflect the actual structure**, including the Foundations/Logic layer and the Logics/{Modal,Temporal,Bimodal,Propositional} hierarchy.

### 2. Naming Convention Violations: 81 `def` Names Use snake_case (High)

Lean 4/Mathlib convention: `lowerCamelCase` for `def`/`abbrev` names, `snake_case` for `theorem`/`lemma` names. The branch introduces **81 new `def` names in snake_case**, which violates Mathlib style:

- `deduction_axiom` → `deductionAxiom`
- `deduction_theorem` → `deductionTheorem`
- `hilbert_cut` → `hilbertCut`
- `c5_backward_walk` → `c5BackwardWalk`
- `neg_imp_implies_antecedent` → `negImpImpliesAntecedent`
- `ex_falso_from_assumption` → `exFalsoFromAssumption`
- etc.

The 318 snake_case `theorem`/`lemma` names are **correct** per Mathlib convention. The issue is specifically with `def` and `abbrev` names. Similarly, ~25 `def` names already use correct camelCase (e.g., `collectDerivInl`, `boxDiamondPersistence`), showing the convention is known but inconsistently applied.

CONTRIBUTING.md says "We generally follow the mathlib style for coding and documentation." This makes the `def` naming a clear actionable item.

### 3. Docstring Coverage Gaps (Medium)

Several touched files have significant docstring gaps. Worst offenders:
- `Bimodal/Metalogic/Algebraic/LindenbaumQuotient.lean`: 37 defs, ~0 docstrings
- `Bimodal/Metalogic/Algebraic/UltrafilterMCS.lean`: 25 defs, ~2 docstrings
- `Bimodal/Metalogic/Algebraic/BooleanStructure.lean`: 21 defs, ~0 docstrings
- `Bimodal/FrameConditions/Compatibility.lean`: 18 defs, ~0 docstrings
- `Bimodal/FrameConditions/Validity.lean`: 14 defs, ~0 docstrings

CONTRIBUTING.md explicitly states: "Document your definitions and theorems to ease both use and reviewing." For publication quality, at minimum all public `def`, `class`, `structure`, and key `theorem` declarations need docstrings.

### 4. Copyright Headers Missing from 4 Files (Low)

Four touched files lack the standard copyright header:
- `Cslib/Logics/Bimodal/Metalogic/Algebraic/Algebraic.lean`
- `Cslib/Logics/Bimodal/Metalogic/BXCanonical/BXCanonical.lean`
- `Cslib/Logics/Bimodal/Metalogic/BXCanonical/Chronicle/ChronicleToCountermodelBasic.lean`
- `Cslib/Logics/Bimodal/Metalogic/Bundle/Bundle.lean`

These are barrel/re-export files but still need copyright headers for publication.

### 5. 38 Remaining `sorry` Instances in 9 Files (High)

The touched files contain 38 `sorry` placeholders, concentrated in Bimodal:
- `ChronicleToCountermodel.lean`: 16 sorries
- `Bundle/SuccRelation.lean`: 7 sorries
- `ChronicleToCountermodelBasic.lean`: 5 sorries
- `Completeness/Dense.lean`: 3 sorries
- Several files with 1-2 each

For publication, these need to be either proved or explicitly marked as conjectures with documentation.

### 6. Cslib.Init Import Not Directly Present in Most Files (Low-Medium)

Only 25 of 247 files in Logics/ and Foundations/ directly import `Cslib.Init`. CONTRIBUTING.md requires "all files import Cslib.Init, which sets up some default linting and tactics." However, this may be satisfied transitively — `Cslib.Init` is imported by `Cslib/Logics/Modal/Basic.lean` via `public import`, so downstream files likely inherit it. **This should be validated**: run `lake exe checkInitImports` to confirm. If transitive import is not sufficient, ~222 files need `import Cslib.Init` added.

### 7. Heavy Import Files (Medium)

Several barrel files have very large import counts:
- `Temporal/Metalogic.lean`: 20 imports
- `Bimodal/Metalogic/BXCanonical/BXCanonical.lean`: 17 imports
- `Bimodal/Metalogic/Separation.lean`: 15 imports

Run `lake shake` to verify all imports are necessary. CONTRIBUTING.md specifies using `lake shake --add-public --keep-implied --keep-prefix` for import minimization.

### 8. Untouched Files That May Need Consistency Updates

Files that exist in scope but were NOT touched on this branch:

**Foundations/Logic/**:
- `LogicalEquivalence.lean` — untouched; verify convention alignment
- `Connectives.lean` — untouched; the naming here appears already clean (no snake_case defs)

**Logics/Modal/**:
- `Cube.lean` — contains snake_case theorem names like `k_subset_d`, `k_subset_b` which are correct for theorems, but should be audited for def names

**Logics/Temporal/**:
- 6 untouched files in `Semantics/` and `Syntax/` subdirectories
- If naming conventions change in touched files, these need consistency review

### 9. `private` Keyword Remnants (Low)

Task 78 removed `private` from definitions. 12 instances of `private` remain in `Cslib/Logics/`, though most are in `LinearLogic/CLL/Basic.lean` (not in our scope) and one is in a comment. 16 instances in `Cslib/Foundations/`. Verify none are in the touched files.

## Cross-Cutting Concerns Per-File Reviews Would Miss

### A. Open Statement Consistency
Files use inconsistent patterns for `open` statements:
- Some use `open Cslib.Logic` (opens the full namespace)
- Some use `open scoped Proposition InferenceSystem` (selective scoped opens)
- Some use `open Cslib.Logic.Bimodal.Metalogic.Core` (fully qualified deep opens)

A consistent convention should be established. The Mathlib style prefers minimal, scoped opens.

### B. Variable Declaration Inconsistency
- Foundations uses `{F : Type*}` (type-class-polymorphic)
- Logics domains use `{Atom : Type*}` (concrete atom type)

This is likely intentional (Foundations is generic, Logics is instantiated), but the transition points should be documented.

### C. Section Usage Patterns
Section usage varies significantly:
- `Foundations/Logic/Axioms.lean`: Named sections (`section Abbreviations`, `section Propositional`, `section Modal`)
- `Foundations/Logic/Theorems/Modal/S5.lean`: Anonymous sections (`section`)
- Most Logics files: No sections at all

Mathlib style recommends named sections. Anonymous sections should be named.

## Questions That Should Be Asked

1. **Is `lake shake` clean?** Import minimization should be verified before any PR.
2. **Is `lake exe checkInitImports` passing?** This is a CI check.
3. **Is `lake exe lint-style` clean?** Text-level linting should be verified.
4. **Is `lake lint` clean?** Environment linters should pass.
5. **Should the `sorry` files be excluded from the PR**, or should they be addressed as part of this review?
6. **What is the Mathlib naming convention for `def` names that are "proof-like"?** Names like `deduction_theorem` are functionally proofs but declared as `def` for `noncomputable` reasons. Should these follow theorem snake_case or def camelCase convention?
7. **Should ORGANISATION.md be updated as part of this work**, or is it maintained separately?

## Recommended Approach

1. **Highest priority**: Address the 81 snake_case `def` names — this is the most visible convention violation and affects API surface.
2. **High priority**: Document the `sorry` situation — either fill them or exclude those files from the review scope.
3. **Medium priority**: Add docstrings to the worst-gap files (LindenbaumQuotient, UltrafilterMCS, BooleanStructure).
4. **Medium priority**: Fix copyright headers in 4 files.
5. **Lower priority**: Standardize section naming, open statement patterns.
6. **Validation**: Run `lake shake`, `lake exe checkInitImports`, `lake exe lint-style`, `lake lint` as final checks.

## Evidence/Examples

### snake_case def example (Axioms.lean)
```lean
-- Current (wrong for def):
noncomputable def deduction_axiom (Γ : List F) (A : F) ...
-- Should be:
noncomputable def deductionAxiom (Γ : List F) (A : F) ...
```

### Missing docstring example (LindenbaumQuotient.lean)
```lean
-- 37 definitions with no /-- ... -/ docstrings
-- E.g., algebraic structures, quotient constructions
```

### Copyright header example (Algebraic.lean)
```lean
-- File starts with:
module
-- Should start with:
/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/
module
```
