# Research Report: Fix Propositional CI Check Failures

**Task**: 122 -- Fix all CONTRIBUTING.md CI check failures in propositional metalogic files
**Session**: sess_1781194255_b2a0c0
**Date**: 2026-06-11

## Executive Summary

Four categories of CI failures need fixing across 14 propositional files. All fixes are code-level changes (renaming, import adjustment, annotation removal, parameter removal). No CI configuration or linter settings should be modified. The propositional files are identical on both `main` and `pr1/foundations-logic`, so fix on main then cherry-pick to pr1.

---

## Issue 1: defsWithUnderscore Lint Violations (8 defs)

### Background

The `defsWithUnderscore` environment linter (from Mathlib) checks `.isDefinition` declarations for underscore-containing names. It only flags `def` declarations and structure field projections -- NOT `theorem` or `lemma`. This explains why exactly 8 violations are reported despite many more theorems having snake_case names.

### Rename Map

| # | Current Name | New Name | File | Line | Type |
|---|-------------|----------|------|------|------|
| 1 | `int_canonical_val` | `intCanonicalVal` | IntCompleteness.lean | 54 | def |
| 2 | `int_neg_phi_imp_psi` | `intNegPhiImpPsi` | IntLindenbaum.lean | 79 | noncomputable def |
| 3 | `int_deductive_closure` | `intDeductiveClosure` | IntLindenbaum.lean | 203 | def |
| 4 | `min_canonical_val` | `minCanonicalVal` | MinCompleteness.lean | 61 | def |
| 5 | `min_bot_forces` | `minBotForces` | MinCompleteness.lean | 71 | def |
| 6 | `min_deductive_closure` | `minDeductiveClosure` | MinLindenbaum.lean | 186 | def |
| 7 | `lift_min_to_cl` | `liftMinToCl` | MinLindenbaum.lean | 233 | noncomputable def |
| 8 | `bot_forces` | `botForces` | Kripke.lean | 63 | structure field |

### Call Site Map (all within propositional directory, no external references)

**1. `int_canonical_val` -> `intCanonicalVal`** (IntCompleteness.lean only)
- Line 54: def declaration
- Line 58: `int_canonical_val_upward_closed` theorem name (references it, but theorem names are NOT linted)
- Line 60: `(hv : int_canonical_val w p) : int_canonical_val w' p` -- parameter types
- Line 66: docstring reference (update doc)
- Line 72: `(IForces int_canonical_val ...` -- call site
- Line 111: `IForces int_canonical_val ...` -- call site
- Line 113: `IForces int_canonical_val ...` -- call site
- Line 114: `h_valid ... int_canonical_val` -- call site

**2. `int_neg_phi_imp_psi` -> `intNegPhiImpPsi`** (IntLindenbaum.lean only)
- Line 79: def declaration
- Line 99: `⟨int_neg_phi_imp_psi φ ψ⟩` -- call site in `int_neg_phi_imp_psi_deriv`

**3. `int_deductive_closure` -> `intDeductiveClosure`** (IntLindenbaum.lean only)
- Line 203: def declaration
- Line 210: `S ⊆ int_deductive_closure S` -- in `int_subset_deductive_closure`
- Line 218: `x ∈ int_deductive_closure S` -- in `int_deductive_closure_dccs_closed`
- Line 220: `φ ∈ int_deductive_closure S` -- in `int_deductive_closure_dccs_closed`
- Line 226: `PropSetConsistent ... (int_deductive_closure S)` -- in `int_deductive_closure_consistent`
- Line 235: `IntDCCS (int_deductive_closure S)` -- in `int_deductive_closure_is_dccs`
- Line 259: `int_deductive_closure (S ∪ {φ})` -- in `int_imp_witness`

**4. `min_canonical_val` -> `minCanonicalVal`** (MinCompleteness.lean only)
- Line 61: def declaration
- Line 67: parameter types in `min_canonical_val_upward_closed`
- Line 83: docstring
- Line 90: `IForces min_canonical_val ...`
- Line 125, 127, 128: `IForces min_canonical_val ...`

**5. `min_bot_forces` -> `minBotForces`** (MinCompleteness.lean only)
- Line 71: def declaration
- Line 77: parameter/return type in `min_bot_forces_upward_closed`
- Line 83: docstring
- Line 90: `IForces ... min_bot_forces ...`
- Line 125, 127, 128, 130: call sites in `min_completeness`

**6. `min_deductive_closure` -> `minDeductiveClosure`** (MinLindenbaum.lean only)
- Line 186: def declaration
- Line 193: `S ⊆ min_deductive_closure S`
- Line 200: `MinTheory (min_deductive_closure S)`
- Line 217: `min_deductive_closure (S ∪ {φ})`

**7. `lift_min_to_cl` -> `liftMinToCl`** (MinLindenbaum.lean only)
- Line 233: def declaration
- Line 240: recursive call `lift_min_to_cl d₁`
- Line 240: recursive call `lift_min_to_cl d₂`
- Line 242: recursive call `lift_min_to_cl d'`
- Line 251: `lift_min_to_cl d` -- in `min_consistent`

**8. `bot_forces` -> `botForces`** (Kripke.lean: structure field + widespread parameter name)

This is the most complex rename. The structure field at line 63 generates a projection `KripkeModel.bot_forces` which the linter flags. However, `bot_forces` is also used extensively as a **local parameter name** throughout Kripke.lean, IntSoundness.lean, MinSoundness.lean, and MinCompleteness.lean.

**Structure field (must rename):**
- Kripke.lean line 63: `bot_forces : World → Prop` (structure field)
- Kripke.lean line 66-67: docstring + `bf_upward_closed` field refers to `bot_forces`

**CRITICAL: Local parameter names (do NOT need renaming for lint, but consider for consistency):**
Local variables and function parameters named `bot_forces` are NOT flagged by `defsWithUnderscore` (it only checks `.isDefinition` declarations). These include:
- IForces definition (line 80): `(bot_forces : World → Prop)` -- local parameter
- iforces_persistence (line 94): `{bot_forces : World → Prop}` -- local parameter
- MValid definition (line 119): `(bot_forces : World → Prop)` -- local parameter
- MinSoundness.lean: multiple `bot_forces` local parameters
- MinCompleteness.lean: references to `min_bot_forces` (already covered above)

**Recommendation**: Only the structure field MUST be renamed. Local parameter names can optionally be renamed for consistency but are not required by the linter. Renaming them would be a larger change with more risk.

**NOTE**: The fields `v_upward_closed` and `bf_upward_closed` also contain underscores but may or may not be flagged. Structure field projections may be excluded by the `isAutoDecl` check. Verify during implementation by running `lake lint` after renaming only `bot_forces`.

### Dependent Theorems (NOT linted but should be renamed for consistency)

The following theorems reference the renamed defs in their names. The linter does NOT flag them (it only checks `.isDefinition`), but renaming them for consistency is good practice:

- `int_canonical_val_upward_closed` -> `intCanonicalVal_upward_closed` (IntCompleteness.lean:58)
- `int_neg_phi_imp_psi_deriv` -> `intNegPhiImpPsi_deriv` (IntLindenbaum.lean:97)
- `int_deductive_closure_dccs_closed` -> `intDeductiveClosure_dccs_closed` (IntLindenbaum.lean:216)
- `int_deductive_closure_consistent` -> `intDeductiveClosure_consistent` (IntLindenbaum.lean:224)
- `int_deductive_closure_is_dccs` -> `intDeductiveClosure_is_dccs` (IntLindenbaum.lean:233)
- `int_subset_deductive_closure` -> `int_subset_deductiveClosure` (IntLindenbaum.lean:209)
- `min_canonical_val_upward_closed` -> `minCanonicalVal_upward_closed` (MinCompleteness.lean:65)
- `min_bot_forces_upward_closed` -> `minBotForces_upward_closed` (MinCompleteness.lean:75)
- `min_deductive_closure_is_theory` -> `minDeductiveClosure_is_theory` (MinLindenbaum.lean:199)
- `min_subset_deductive_closure` -> `min_subset_deductiveClosure` (MinLindenbaum.lean:192)

**Decision point for planner**: Renaming these dependent theorems is optional (linter does not require it) but recommended for naming consistency. The planner should decide whether to include them in scope.

---

## Issue 2: simpNF Violation (1 violation)

### Location
- **File**: `Cslib/Logics/Propositional/NaturalDeduction/Equivalence.lean`
- **Line 74-77**: `@[simp] theorem mem_hilbertAxiomTheory`

### Root Cause
`HilbertAxiomTheory` is defined as an `abbrev` for `AxiomTheory PropositionalAxiom` (line 70-71). The `@[simp]` lemma `mem_axiomTheory` (line 62-66) already applies to `HilbertAxiomTheory` because `abbrev` is transparent to `simp`. So `mem_hilbertAxiomTheory` is redundant -- the `simpNF` linter detects that `simp` can already prove it.

### Fix
Remove `@[simp]` from `mem_hilbertAxiomTheory`. Keep the theorem itself (it may serve as documentation / explicit name), just remove the simp attribute.

**Change**: Line 74, change `@[simp]` to nothing (delete the line).

### Usage Check
`mem_hilbertAxiomTheory` is only defined at line 75, never referenced elsewhere. No call sites to update.

---

## Issue 3: lake shake Import Fixes (9 files)

### Background
`lake shake --add-public --keep-implied --keep-prefix` checks for minimal imports. The core issue: `Derivation.lean` currently imports `Axioms.lean` but only needs `Defs.lean` (which `Axioms.lean` re-exports). This creates a cascade: files that imported `Axioms` transitively through `Derivation` now need their own direct `Axioms` import.

### Import Change Map

| # | File | Remove Import | Add Import | Reason |
|---|------|--------------|------------|--------|
| 1 | ProofSystem/Derivation.lean | `Axioms` | `Defs` | Only uses `PL.Proposition`, not axiom predicates |
| 2 | Metalogic/DeductionTheorem.lean | -- | `Axioms` | Uses `PropositionalAxiom` (line 56), `.implyK`/`.implyS` |
| 3 | Metalogic/Soundness.lean | -- | `Axioms` | Uses `PropositionalAxiom` |
| 4 | Metalogic/IntSoundness.lean | -- | `Axioms` | Uses `IntPropAxiom` |
| 5 | Metalogic/MinSoundness.lean | -- | `Axioms` | Uses `MinPropAxiom` |
| 6 | Metalogic/MinLindenbaum.lean | `MCS` | -- | Imports MCS but uses nothing from it |
| 7 | NaturalDeduction/DerivedRules.lean | -- | `BVDecide.Normalize` | Transitive dependency from `simp` lemmas |
| 8 | ProofSystem/Instances.lean | -- | `Axioms` | Uses `PropositionalAxiom` |
| 9 | ProofSystem/IntMinInstances.lean | -- | `Axioms` | Uses `IntPropAxiom`, `MinPropAxiom` |

### Detailed Changes

**1. Derivation.lean** (lines 8-10):
```
-- Current:
public import Cslib.Logics.Propositional.ProofSystem.Axioms
public import Cslib.Foundations.Logic.Metalogic.Consistency

-- After:
public import Cslib.Logics.Propositional.Defs
public import Cslib.Foundations.Logic.Metalogic.Consistency
```

**2-5,8-9. DeductionTheorem, Soundness, IntSoundness, MinSoundness, Instances, IntMinInstances**: Add one line each:
```
public import Cslib.Logics.Propositional.ProofSystem.Axioms
```
These files use concrete axiom predicates (`PropositionalAxiom`, `IntPropAxiom`, `MinPropAxiom`) which are defined in Axioms.lean. They currently get them transitively through Derivation -> Axioms, but after removing Axioms from Derivation, they need the direct import.

**6. MinLindenbaum.lean** (line 10): Remove the import:
```
-- Remove this line:
public import Cslib.Logics.Propositional.Metalogic.MCS
```
MinLindenbaum has no reference to any MCS definition (`MaxConsistentSet`, `mcs`, etc.).

**7. DerivedRules.lean**: Add:
```
public import Std.Tactic.BVDecide.Normalize
```
This is a transitive dependency required by `simp` lemmas used in the file (e.g., `Finset.mem_insert`, `Finset.subset_insert`). The exact import path should be verified with `lake shake --fix` during implementation, as the path may differ.

### Verification Note
The exact import path for BVDecide.Normalize should be confirmed by running `lake shake --fix` since the module path syntax can vary. The task description says "add BVDecide.Normalize" which might mean `Std.Tactic.BVDecide.Normalize` or just `import BVDecide.Normalize`.

---

## Issue 4: Unused DecidableEq Hypothesis (1 warning)

### Location
- **File**: `Cslib/Logics/Propositional/NaturalDeduction/FromHilbert.lean`
- **Line 291**: `[DecidableEq Atom']` in `hilbertSubstitutionDeriv`
- **Line 269**: `[DecidableEq Atom']` in `hilbertSubstitution` (ALSO unused)

### Root Cause
The parameterized `hilbertSubstitution` (line 268) and `hilbertSubstitutionDeriv` (line 290) both carry `[DecidableEq Atom']`, but neither function body uses `DecidableEq`. The `DerivationTree` type and its constructors (`.ax`, `.assumption`, `.modus_ponens`, `.weakening`) do not require `DecidableEq`. The `List.mem_map` lemma used in the proofs also does not require it.

### Fix
Remove `[DecidableEq Atom']` from BOTH functions:
1. Line 269: Remove `[DecidableEq Atom']` from `hilbertSubstitution`
2. Line 291: Remove `[DecidableEq Atom']` from `hilbertSubstitutionDeriv`

**Prior Art**: Commit `d48cb841` on `pr1/foundations-logic` already did exactly this fix for the pre-parameterized version of these functions. The current code on main reintroduced the parameter during axiom parameterization.

### Call Site Impact
- `hilbertSubstitution` is only called recursively (lines 283, 285) and by `hilbertSubstitutionDeriv` (line 300) -- all in the same file
- `hilbertSubstitutionDeriv` is not called anywhere in the codebase

No call site updates needed since neither function is called externally.

---

## Issue 5: Branch Strategy

### Current State
- `main` and `pr1/foundations-logic` have **identical** propositional files (zero diff)
- pr1 has additional commits (propositional additions, FromPropositional removals)
- pr1 is ahead of main by ~10 commits; main is ahead of pr1 by ~10 commits

### Recommended Strategy
1. Fix all issues on `main` in a single commit
2. Cherry-pick the fix commit to `pr1/foundations-logic`
3. Since propositional files are identical on both branches, the cherry-pick should apply cleanly

---

## Issue 6: No CI Pipeline Changes Required

All fixes are code-level:
- Renaming definitions (Issue 1)
- Removing a `@[simp]` annotation (Issue 2)
- Adjusting import statements (Issue 3)
- Removing unused type class parameters (Issue 4)

No changes to any files in `.github/workflows/`, no changes to linter configuration, no changes to `lakefile.lean` or `lean-toolchain`.

---

## Implementation Complexity Assessment

| Issue | Files Affected | Risk | Complexity |
|-------|---------------|------|------------|
| 1. Rename defs | 4 files (IntCompleteness, IntLindenbaum, MinCompleteness, MinLindenbaum) + Kripke.lean | Medium | ~50 search-replace operations |
| 2. simpNF | 1 file (Equivalence.lean) | Low | Delete 1 line |
| 3. Imports | 9 files | Low | Add/remove import lines |
| 4. DecidableEq | 1 file (FromHilbert.lean) | Low | Remove 2 parameters |

**Total estimated scope**: 14 files modified, ~60 edits

### Recommended Phase Structure

**Phase 1**: Import fixes (Issue 3) -- independent, mechanical, low risk
**Phase 2**: Rename defs (Issue 1) -- largest change, requires careful find-replace
**Phase 3**: simpNF fix (Issue 2) + DecidableEq fix (Issue 4) -- trivial
**Phase 4**: Verify with full CI suite: `lake build`, `lake lint`, `lake shake --add-public --keep-implied --keep-prefix`, `lake exe mk_all --module`
**Phase 5**: Cherry-pick to pr1/foundations-logic

---

## Files Inventory

All files are under `Cslib/Logics/Propositional/`:

| File | Issues | Lines |
|------|--------|-------|
| Semantics/Kripke.lean | #1 (bot_forces field) | 134 |
| Metalogic/IntCompleteness.lean | #1 (int_canonical_val) | 127 |
| Metalogic/IntLindenbaum.lean | #1 (int_neg_phi_imp_psi, int_deductive_closure) | 325 |
| Metalogic/MinCompleteness.lean | #1 (min_canonical_val, min_bot_forces) | 143 |
| Metalogic/MinLindenbaum.lean | #1 (min_deductive_closure, lift_min_to_cl), #3 (remove MCS) | 276 |
| NaturalDeduction/Equivalence.lean | #2 (simpNF) | 232 |
| NaturalDeduction/FromHilbert.lean | #4 (DecidableEq) | 302 |
| ProofSystem/Derivation.lean | #3 (imports) | ~150 |
| Metalogic/DeductionTheorem.lean | #3 (imports) | ~220 |
| Metalogic/Soundness.lean | #3 (imports) | ~85 |
| Metalogic/IntSoundness.lean | #3 (imports) | ~100 |
| Metalogic/MinSoundness.lean | #3 (imports) | ~95 |
| NaturalDeduction/DerivedRules.lean | #3 (imports) | ~270 |
| ProofSystem/Instances.lean | #3 (imports) | ~65 |
| ProofSystem/IntMinInstances.lean | #3 (imports) | ~100 |
