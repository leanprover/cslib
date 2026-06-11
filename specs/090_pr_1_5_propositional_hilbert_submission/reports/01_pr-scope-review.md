# PR 1.5 Scope Review: Propositional Hilbert Submission

## Executive Summary

PR 1.5 captures all propositional/Hilbert proof system work done since PR 1
(#629, `pr1/foundations-logic` branch). This includes tasks 86-89: lint
cleanup, ND-Hilbert equivalence, intuitionistic base refactoring, and derived
connective rules. The propositional files are sorry-free, compile cleanly, and
are well-documented. One gap exists: three new files are missing from
`Cslib.lean` root imports.

## 1. PR 1 Baseline (PR #629)

PR 1 (`pr1/foundations-logic` -> upstream `main`) includes 25 files:

**Foundations/Logic/** (generic typeclass framework):
- `Axioms.lean` -- axiom formula definitions
- `Connectives.lean` -- `PropositionalConnectives`, `ModalConnectives`, etc.
- `InferenceSystem.lean` -- generic `InferenceSystem` typeclass
- `ProofSystem.lean` -- bundled `PropositionalHilbert` class (pre-refactor)
- `Theorems.lean` -- barrel import file
- `Theorems/BigConj.lean` -- big conjunction
- `Theorems/Combinators.lean` -- I/B/C/S combinators
- `Theorems/Propositional/Core.lean` -- LEM, DNE, raa, etc.
- `Theorems/Propositional/Connectives.lean` -- De Morgan, etc.
- `Theorems/Modal/Basic.lean` -- modal box distribution
- `Theorems/Modal/S5.lean` -- S5-specific theorems
- `Theorems/Temporal/FrameConditions.lean` -- temporal frame conditions
- `Theorems/Temporal/TemporalDerived.lean` -- temporal derived facts
- `Metalogic/Consistency.lean` -- consistency definitions
- `Metalogic/DeductionHelpers.lean` -- helper lemmas

**Logics/Propositional/** (concrete propositional logic):
- `Defs.lean` -- `Proposition` type, `Theory`, connectives
- `ProofSystem/Axioms.lean` -- `PropositionalAxiom` inductive
- `ProofSystem/Derivation.lean` -- `DerivationTree` inductive
- `ProofSystem/Instances.lean` -- `PropositionalHilbert` instance
- `Metalogic/DeductionTheorem.lean` -- deduction theorem
- `Metalogic/MCS.lean` -- maximal consistent sets
- `NaturalDeduction/Basic.lean` -- ND system
- `NaturalDeduction/FromHilbert.lean` -- Hilbert-to-ND bridge

**Other**:
- `Foundations/Data/ListHelpers.lean` -- `removeAll` utility
- `Cslib.lean` -- root import file

## 2. New/Modified Content for PR 1.5

### 2.1 New Files (3)

| File | Lines | Description |
|------|-------|-------------|
| `NaturalDeduction/DerivedRules.lean` | 387 | ND derived rules: negI/E, topI, andI/E1/E2, orI1/I2/E, dne, iffI/E1/E2 + DerivableIn wrappers |
| `NaturalDeduction/Equivalence.lean` | 169 | ND-Hilbert extensional equivalence (`hilbert_iff_nd`) |
| `NaturalDeduction/HilbertDerivedRules.lean` | 448 | Hilbert derived rules: hilbertNegI/E, hilbertTopI, hilbertDne, hilbertAndI/E1/E2, hilbertOrI1/I2/E, hilbertIffI/E1/E2 + Deriv wrappers |

### 2.2 Modified Files (13)

| File | Change Type | Summary |
|------|------------|---------|
| `Foundations/Logic/ProofSystem.lean` | **Major refactor** | `PropositionalHilbert` split into 3-level hierarchy: `MinimalHilbert` -> `IntuitionisticHilbert` -> `ClassicalHilbert`; removed `HasAxiomDNE` class; added `HilbertMin`/`HilbertInt` tag types |
| `Foundations/Logic/Theorems/Propositional/Core.lean` | **Major refactor** | Theorems stratified by strength: Minimal (lem), Intuitionistic (efq_axiom, raa, efq_neg), Classical (peirce_axiom, double_negation, rcp, lce_imp, rce_imp) |
| `Foundations/Logic/Theorems/Propositional/Connectives.lean` | **Major refactor** | Theorems stratified: Minimal (contrapose_imp, contraposition, iff_intro, iff_neg_intro), Classical (classical_merge, De Morgan laws) |
| `Foundations/Logic/Theorems/Combinators.lean` | **Variable rename** | `[PropositionalHilbert S]` -> `[MinimalHilbert S]` |
| `Foundations/Logic/Theorems/BigConj.lean` | **Variable rename** | `[PropositionalHilbert S]` -> `[ClassicalHilbert S]` |
| `Foundations/Logic/Theorems.lean` | **Doc update** | Module description updated for 3-level hierarchy |
| `Foundations/Logic/Theorems/Temporal/FrameConditions.lean` | **Import cleanup** | Removed `import Mathlib.Data.Finset.Attr` |
| `Foundations/Data/ListHelpers.lean` | **Lint fix** | `simp` -> `simp only` in 3 lemmas |
| `Logics/Propositional/Defs.lean` | **Addition** | Added `Proposition.iff` biconditional abbreviation |
| `Logics/Propositional/ProofSystem/Instances.lean` | **Rename** | `PropositionalHilbert` -> `ClassicalHilbert` instance |
| `Logics/Propositional/Metalogic/DeductionTheorem.lean` | **Lint fix** | `simp` -> `simp only`, removed `simp_wf` |
| `Logics/Propositional/Metalogic/MCS.lean` | **Lint fix** | `simp` -> `simp only` |
| `Cslib.lean` | **Mixed** | Root imports (includes both propositional and non-propositional additions) |

### 2.3 Net Changes

- **+1,231 lines** / **-173 lines** in propositional/Foundations scope
- 3 entirely new files, 13 modified files
- The rename `PropositionalHilbert` -> `ClassicalHilbert` propagates to
  all downstream consumers (Modal, Temporal, Bimodal)

## 3. Quality Assessment

### 3.1 Sorry Count

**Zero.** All propositional/Hilbert files are sorry-free.

```
grep -rn "sorry" Cslib/Logics/Propositional/   => (none)
grep -rn "sorry" Cslib/Foundations/Logic/       => (none)
```

### 3.2 Debug Artifacts

**None.** No `#check`, `#eval`, or `#print` in any propositional/Foundations file.

### 3.3 TODO/FIX/NOTE Comments

**One minor issue.** `NaturalDeduction/Basic.lean` line 219 contains a docstring
with "TODO: this implementation is not capture avoiding." This is a known
design limitation documented inline, not a code defect.

### 3.4 Compilation Status

**Clean.** Full `lake build` succeeds (2915 jobs). The only warnings in
propositional scope:

1. `FromHilbert.lean:210` -- `hilbertSubstitutionDeriv` has unused
   `[DecidableEq Atom']` hypothesis. This is a minor lint issue; the fix is
   to remove the explicit `[DecidableEq Atom']` and use `open scoped Classical`
   instead, or disable the linter locally.

### 3.5 Linting

All flexible `simp` calls in propositional scope have been converted to
`simp only [...]` (task 86). No remaining lint violations.

## 4. Gaps and Recommended Pre-Submission Work

### 4.1 Missing Root Imports (MUST FIX)

Three new files are not registered in `Cslib.lean`:

```lean
-- Missing entries:
public import Cslib.Logics.Propositional.NaturalDeduction.DerivedRules
public import Cslib.Logics.Propositional.NaturalDeduction.Equivalence
public import Cslib.Logics.Propositional.NaturalDeduction.HilbertDerivedRules
```

These should be added after line 295 (after `FromHilbert`).

### 4.2 Unused DecidableEq Warning (SHOULD FIX)

`hilbertSubstitutionDeriv` in `FromHilbert.lean:210-217` has `[DecidableEq Atom']`
in its type but doesn't use it. Fix: remove the `[DecidableEq Atom']` parameter
and add `open scoped Classical in` before the definition.

### 4.3 TODO in Docstring (LOW PRIORITY)

The "TODO: this implementation is not capture avoiding" in
`NaturalDeduction/Basic.lean:219` is a design note, not actionable for this PR.
It documents a known limitation of the substitution operation.

### 4.4 No Additional Missing Theorems Detected

The PR 1.5 content is self-contained and complete:
- ND derived rules cover all Lukasiewicz connectives (neg, top, and, or, iff, dne)
- Hilbert derived rules mirror the ND rules
- Extensional equivalence between the two systems is proven
- The 3-level hierarchy (Minimal/Intuitionistic/Classical) is fully implemented
- All downstream consumers (Modal, Temporal, Bimodal) compile against the refactored API

## 5. PR Boundary: PR 1.5 vs PR 2

### 5.1 PR 1.5 Scope (Propositional/Foundations)

All files under:
- `Cslib/Logics/Propositional/**` (11 files)
- `Cslib/Foundations/Logic/**` (16 files)
- `Cslib/Foundations/Data/ListHelpers.lean` (1 file)
- `Cslib.lean` (root imports -- propositional entries only)

### 5.2 PR 2 Scope (Modal/Temporal/Bimodal)

All files under:
- `Cslib/Logics/Modal/**` (9 files -- all new since upstream)
- `Cslib/Logics/Temporal/**` (30+ files -- all new since upstream)
- `Cslib/Logics/Bimodal/**` (90+ files -- all new since upstream)
- `Cslib.lean` (root imports -- modal/temporal/bimodal entries)

### 5.3 Coupling Between PR 1.5 and PR 2

The propositional refactoring (task 88: `PropositionalHilbert` -> `ClassicalHilbert`)
is a **cross-cutting rename** that affects both propositional and modal/temporal
files. All modal/temporal/bimodal files already reference `ClassicalHilbert` --
there is no remaining reference to `PropositionalHilbert` anywhere in the
codebase.

**Important**: PR 1.5 introduces API-breaking changes (the typeclass rename and
hierarchy restructuring) that the modal/temporal/bimodal files depend on.
This means:
- PR 1.5 MUST be merged before PR 2
- PR 2 files are already written against the PR 1.5 API
- If PR 1.5 lands cleanly, PR 2 will not need propositional-related adjustments

### 5.4 Modal Logic Leakage Check

**No modal leakage detected.** The propositional files contain:
- No imports of Modal/Temporal/Bimodal modules
- No references to `HasBox`, `HasUntil`, `HasSince`, `Necessitation`
- No modal axiom usage (K, T, 4, B, 5, D)

The `ProofSystem.lean` file defines modal typeclasses (`ModalHilbert`, etc.)
and tag types, but these are part of the generic Foundations layer that was
already in PR 1. The refactoring merely renames their base class.

## 6. Recommended PR 1.5 Submission Strategy

### Option A: Standalone Propositional PR (Recommended)

Create a branch from upstream/main containing only:
1. All Foundations/Logic changes (14 files)
2. All Logics/Propositional changes (11 files)
3. ListHelpers.lean
4. Cslib.lean (propositional entries only)

**Risk**: Modal/Temporal/Bimodal files on main reference `ClassicalHilbert`
but upstream still has `PropositionalHilbert`. PR 2 must be rebased after
PR 1.5 merges.

### Option B: Update PR 1 In-Place

Cherry-pick or rebase the task 86-89 changes onto the existing
`pr1/foundations-logic` branch, updating PR #629 to include the new content.

**Advantage**: No new PR needed; fewer review cycles.
**Risk**: PR 1 scope creep; reviewers may need re-review.

### Option C: Amend PR 1 + Create Separate PR 1.5

Leave PR 1 as-is. Create PR 1.5 as a separate PR targeting upstream/main
that depends on PR 1 being merged first.

**Advantage**: Clean separation of review scope.
**Risk**: Merge ordering dependency.

## 7. Summary of Action Items

| Priority | Item | Effort |
|----------|------|--------|
| MUST | Add 3 missing `Cslib.lean` imports | 1 min |
| SHOULD | Fix `DecidableEq` warning in `FromHilbert.lean` | 5 min |
| DECIDE | Choose submission strategy (A/B/C) | -- |
| OPTIONAL | Clean up docstring TODO in `Basic.lean` | 2 min |
