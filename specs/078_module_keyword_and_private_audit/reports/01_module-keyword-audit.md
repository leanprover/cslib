# Task 78: Module Keyword and Private Declaration Audit

## Executive Summary

The codebase has 155 non-module Lean files in `Cslib/Logics/` that need `module` keyword migration. The root `Cslib.lean` already uses `module`, causing a build error because it cannot import non-module files. Task 77 (phase 1) has already consolidated the most duplicated private helper (`theorem_in_mcs_fc`) across 22 Bimodal files into a single public definition in `MCSProperties.lean`, with uncommitted changes extending this to Temporal files.

The key technical finding is that **`private def` fails inside `@[expose] public section` in module files**, but **`private theorem` works fine**. This means only 104 `private def` declarations (not all 321 private declarations) need changes. Of these, NONE have actual name collision risk when made public because they reside in different namespaces.

**Recommended approach**: Remove `private` from all `private def` declarations, then add `module` + `public import` + `@[expose] public section` to all 155 files. No renaming needed.

## Current Build Status

**Build fails** with error:
```
error: Cslib.lean:1:0: cannot import non-`module` Cslib.Logics.Bimodal.FrameConditions.Compatibility from `module`
```

All 2912 out of 2913 modules compile successfully. Only the root `Cslib` module fails because it uses `module` but imports 155 non-module files from `Cslib/Logics/`.

## Module Keyword Status

| Category | Count | Status |
|----------|-------|--------|
| Total Lean files in project | 333 | - |
| Files with `module` keyword | 178 | No changes needed |
| Files without `module` keyword | 155 | All in `Cslib/Logics/` |
| Non-module files with `private` | 66 | Need private audit |
| Non-module files without `private` | 89 | Trivial migration |

### Files with `module` by area

| Area | With `module` | Without `module` |
|------|---------------|-------------------|
| Foundations/ (all) | 58 | 0 |
| Logics/Bimodal/Semantics, Syntax, Embedding | 10 | 0 |
| Logics/Temporal/Syntax, Semantics | 7 | 0 |
| Logics/Modal/Basic, Cube, etc. | 4 | 0 |
| Logics/Propositional/Defs, NatDed, Axioms | 3 | 0 |
| Logics/HML/ | 2 | 0 |
| Logics/LinearLogic/ | 5 | 0 |
| Other (Algorithms, Crypto, etc.) | 89 | 0 |
| **Logics/ (remaining)** | **0** | **155** |

## Key Technical Finding: `private def` vs `private theorem`

Experimentally verified with Lean 4.31.0-rc1:

| Pattern | In `@[expose] public section` | Without `@[expose] public section` |
|---------|-------------------------------|--------------------------------------|
| `private theorem` | **WORKS** - visible within same file | WORKS |
| `private def` | **FAILS** - "would need to be public" | WORKS |
| `private noncomputable def` | **FAILS** | WORKS |
| `private abbrev` | **FAILS** | WORKS |
| `private lemma` | NOT VALID in module mode | N/A |
| `private structure` | **FAILS** (if referenced later) | WORKS |

**Error message**: `Unknown identifier 'X'. Note: A private declaration 'X' (from the current module) exists but would need to be public to access here.`

**Root cause**: In Lean 4 module mode, `@[expose] public section` creates a public visibility scope. `private theorem` is special-cased (possibly because Prop-typed declarations are treated differently), but `private def` declarations become completely inaccessible even within the same file.

This means the Foundations/Logic files that already use `module` + `@[expose] public section` + `private theorem` work correctly -- confirming the pattern is safe for theorem declarations.

## Private Declaration Inventory

### Total Counts (current working tree state)

| Declaration Type | Count | Action Needed |
|-----------------|-------|---------------|
| `private theorem` | 202 | **None** - works in `@[expose] public section` |
| `private def` (incl. `noncomputable`) | 104 | **Remove `private`** |
| `private lemma` | 11 | All in LinearLogic (already has `module`), no action |
| `private abbrev` | 1 | **Remove `private`** |
| **Total** | **321** | **105 need changes** |

### Private Declarations by Directory

| Directory | `private def` | `private theorem` | `private lemma` | `private abbrev` | Total |
|-----------|---------------|-------------------|-----------------|------------------|-------|
| Bimodal/ | 73 | 97 | 0 | 0 | 170 |
| Temporal/ | 23 | 81 | 0 | 0 | 104 |
| Modal/ | 6 | 6 | 0 | 0 | 12 |
| Propositional/ | 5 | 5 | 0 | 1 | 11 |
| LinearLogic/ | 0 | 0 | 11 | 0 | 11 |
| HML/ | 0 | 0 | 0 | 0 | 0 |

### Top Files by Private Declaration Count

| File | `private def` | `private theorem` | Total |
|------|---------------|-------------------|-------|
| Bimodal/.../Chronicle/PointInsertion.lean | 33 | 23 | 56 |
| Temporal/.../Chronicle/PointInsertion.lean | 30 | 25 | 55 |
| Bimodal/.../ConservativeExtension/Lifting.lean | 11 | 13 | 24 |
| Bimodal/.../Decidability/CountermodelExtraction.lean | 0 | 11 | 11 |
| Bimodal/Theorems/TemporalDerived.lean | 8 | 0 | 8 |
| Temporal/Metalogic/CompletenessHelpers.lean | 4 | 6 | 10 |
| Bimodal/.../Decidability/Saturation.lean | 4 | 3 | 7 |
| DeductionTheorem files (4 files) | 5 each | 4 each | 9 each |

## Name Collision Analysis

### Duplicated `private def` Names

27 names appear in multiple files (62 total occurrences):

**DeductionTheorem helpers** (4 logic domains, different namespaces, NO collision):
- `removeAll` (4 files): Bimodal.Core, Modal, PL, Temporal
- `deduction_with_mem` (4 files): same domains
- `deduction_axiom`, `deduction_imp_self`, `deduction_mp`, `deduction_assumption_other` (3 files each): Modal, PL, Temporal

**PointInsertion duplicates** (Bimodal vs Temporal, different namespaces, NO collision):
- 18 names each appearing in both `Bimodal/.../PointInsertion.lean` and `Temporal/.../PointInsertion.lean`
- Namespaces: `Cslib.Logic.Bimodal.Metalogic.BXCanonical.Chronicle` vs `Cslib.Logic.Temporal.Metalogic.Chronicle`
- No imports from Temporal to Bimodal (import direction is Bimodal -> Temporal only)

**Algebraic helpers** (same Bimodal subtree, different namespace suffixes, NO collision):
- `neg_imp_implies_antecedent` (2 files): `...ParametricTruthLemma` vs `...RestrictedParametricTruthLemma`
- `neg_imp_implies_neg_consequent` (2 files): same

**Theorem helpers** (different namespaces, NO collision):
- `unwrap` (2 files): `Combinators` vs `Propositional`

### Collision Risk Summary

**Zero actual name collisions exist.** All duplicated `private def` names are either:
1. In completely separate logic domains with no cross-imports (DeductionTheorem, PointInsertion)
2. In different namespace suffixes within the same domain (Algebraic)

This means removing `private` from all `private def` declarations will NOT cause name collisions, because:
- Each file uses a distinct namespace
- The fully qualified names differ even for same unqualified names
- The Lean 4 module system resolves names by full qualification

### Prior Consolidation (already done)

Task 77 phase 1 (commit `c603927`) has already:
- Created public `theorem_in_mcs_fc` in `MCSProperties.lean`
- Removed all 22 private `theorem_in_mcs_fc` copies from Bimodal files
- Created public `theorem_in_mcs` in `Temporal/Metalogic/MCS.lean` (uncommitted)
- Removed private `theorem_in_mcs`/`theorem_in_mcs'` copies from 8 Temporal files (uncommitted)

## Recommended Implementation Approach

### Phase 1: Remove `private` from `private def` declarations (105 changes in 50 files)

For every `private def` and `private abbrev` in the 155 non-module Logics/ files:
- Replace `private def` with `def`
- Replace `private noncomputable def` with `noncomputable def`
- Replace `private abbrev` with `abbrev`

No renaming is needed because no name collisions exist.

**Files affected**: 50 files (the 66 files with private declarations minus 16 files that only have `private theorem`)

### Phase 2: Convert `private lemma` to `private theorem` (0 changes needed)

All `private lemma` declarations are in LinearLogic files that already have `module`. They use `@[local grind .]` attributes and are not referenced by name. No changes needed.

### Phase 3: Add `module` keyword to 155 files

For each of the 155 non-module files:
1. Add `module` after the copyright header
2. Change `import` to `public import`
3. Add `@[expose] public section` before the first `namespace`

This is the same mechanical transformation that task 76 performed, but now safe because the `private def` issue has been resolved.

### Phase 4: Build verification

Run `lake build` to verify zero errors.

## Risk Assessment

| Risk | Severity | Mitigation |
|------|----------|------------|
| Name collision from removing `private` | **None** | Verified: all names unique within their namespaces |
| `private theorem` fails in `@[expose] public section` | **None** | Experimentally verified: `private theorem` works |
| `lemma` keyword rejected in module mode | **Low** | Only affects LinearLogic (already has `module`, already works) |
| Uncommitted task 77 changes conflict | **Low** | Commit or incorporate before starting |
| Missing `end` for `@[expose] public section` | **Low** | Some files have multiple namespace blocks; need end at EOF |

## Estimated Complexity

| Phase | Files | Changes | Difficulty |
|-------|-------|---------|------------|
| Phase 1: Remove `private` from defs | 50 | 105 | Mechanical (sed/find-replace) |
| Phase 2: lemma conversion | 0 | 0 | None needed |
| Phase 3: Add `module` keyword | 155 | ~465 (3 per file) | Mechanical |
| Phase 4: Build verification | 1 | N/A | Build + fix any issues |
| **Total** | **155** | **~570** | **Low** |

The implementation is almost entirely mechanical and could be done with a script. The main risk is edge cases in files with unusual structure (multiple namespaces, nested sections, etc.).

## Appendix: Files Requiring `private def` Removal

### Bimodal (31 files, 73 `private def` declarations)

- `Metalogic/BXCanonical/Chronicle/PointInsertion.lean` (33 private defs)
- `Metalogic/ConservativeExtension/Lifting.lean` (11)
- `Theorems/TemporalDerived.lean` (8)
- `Metalogic/Core/DeductionTheorem.lean` (5)
- `Metalogic/Decidability/Saturation.lean` (4)
- `Metalogic/Algebraic/ParametricTruthLemma.lean` (2)
- `Metalogic/Algebraic/RestrictedParametricTruthLemma.lean` (2)
- `Theorems/Propositional/Connectives.lean` (2)
- `Metalogic/BXCanonical/Chronicle/CounterexampleElimination.lean` (2)
- `Theorems/GeneralizedNecessitation.lean` (1)
- `Theorems/Combinators.lean` (1)
- `Theorems/Propositional/Core.lean` (1)
- `Theorems/Perpetuity/Principles.lean` (1)
- `Metalogic/Decidability/Tableau.lean` (1)

### Temporal (13 files, 23 `private def` declarations)

- `Metalogic/Chronicle/PointInsertion.lean` (30 private defs)
- `Metalogic/DeductionTheorem.lean` (5)
- `Metalogic/CompletenessHelpers.lean` (4)
- `Metalogic/GeneralizedNecessitation.lean` (3)
- `Metalogic/Chronicle/CounterexampleElimination.lean` (2)
- `Metalogic/MCS.lean` (1)
- `Syntax/Formula.lean` (1 -- already has `module`)

### Modal (3 files, 6 `private def` declarations)

- `Metalogic/DeductionTheorem.lean` (5)
- `Metalogic/MCS.lean` (1)

### Propositional (3 files, 6 `private def` declarations)

- `Metalogic/DeductionTheorem.lean` (5)
- `NaturalDeduction/FromHilbert.lean` (0 defs, 1 theorem only)
- `Metalogic/MCS.lean` (0 defs, only theorems)
