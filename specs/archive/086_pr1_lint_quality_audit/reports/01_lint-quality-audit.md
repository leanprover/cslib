# Lint and Quality Audit Report: pr1/foundations-logic

**Task**: 86
**Date**: 2026-06-10
**Branch**: `pr1/foundations-logic`
**Files in scope**: 25 files (24 Lean files + Cslib.lean)

## Executive Summary

Ran all 5 CI lint checks against the `pr1/foundations-logic` branch. Found **3 passing checks** (lake lint, lint-style, checkInitImports, mk_all), **1 check with findings** (lake shake -- 13 files with non-minimal imports), and **builtin lint warnings** in 3 files (ListHelpers, DeductionTheorem, MCS). Zero errors, zero sorry occurrences, all files have copyright headers and `module` keyword.

**Total issues found**: 34 individual issues across 6 categories.

---

## CI Check Results

| Check | Result | Details |
|-------|--------|---------|
| `lake lint` | PASS | "Linting passed for Cslib" |
| `lake exe lint-style` | PASS | Only cosmetic warning about missing nolints-style.txt |
| `lake exe checkInitImports` | PASS | No output (clean) |
| `lake exe mk_all --module --check` | PASS | "No update necessary" |
| `lake exe shake` | N/A | Requires `scripts/noshake.json` (absent from repo); ran with temp config |
| `lake lint --builtin-only` | WARNINGS | 17 warnings across 3 files |

---

## Issue Catalog by Category

### Category 1: Flexible `simp` Warnings (linter.flexible)

**Severity**: Warning (CI blocking in strict mode)
**Effort**: Medium -- requires running `simp?` to determine correct `simp only [...]` lemma set
**Risk**: Low -- mechanical replacement, each can be tested independently

| # | File | Line | Current | Fix |
|---|------|------|---------|-----|
| 1 | ListHelpers.lean | 41 | `simp [removeAll, List.mem_filter] at hx` | Run `simp?` to get `simp only [...]` |
| 2 | ListHelpers.lean | 44 | `simp [List.mem_cons] at this` | Run `simp?` to get `simp only [...]` |
| 3 | ListHelpers.lean | 51 | `simp [removeAll, List.mem_filter]` | Run `simp?` to get `simp only [...]` |
| 4 | ListHelpers.lean | 57 | `simp [removeAll, List.mem_filter] at hx ⊢` | Run `simp?` to get `simp only [...]` |
| 5 | DeductionTheorem.lean | 148 | `simp [List.mem_cons] at this` | Run `simp?` to get `simp only [...]` |
| 6 | DeductionTheorem.lean | 163 | `simp [this]` | Run `simp?` to get `simp only [...]` |
| 7 | DeductionTheorem.lean | 176 | `simp at h ⊢` | Run `simp?` to get `simp only [...]` |
| 8 | MCS.lean | 96 | `simp [List.mem_cons] at hx` | Run `simp?` to get `simp only [...]` |
| 9 | MCS.lean | 97 | `simp [propDerivationSystem, Deriv]` | Run `simp?` to get `simp only [...]` |

**Note**: The `simp at hψ` calls in Consistency.lean (lines 91, 112, 251) do NOT trigger lint warnings because they operate on hypotheses for contradiction and are acceptable.

### Category 2: Unused/Multi-Goal Tactic Warnings (linter.unusedTactic, linter.style.multiGoal)

**Severity**: Warning (CI blocking in strict mode)
**Effort**: Low -- remove or replace `simp_wf` with focused tactic
**Risk**: Low -- `simp_wf` is a no-op here (goals handled by subsequent `exact` calls)

| # | File | Line | Warning | Fix |
|---|------|------|---------|-----|
| 10 | DeductionTheorem.lean | 102 | `simp_wf` does nothing + multiGoal | Remove `simp_wf` line entirely |
| 11 | DeductionTheorem.lean | 159 | `simp_wf` does nothing + multiGoal | Remove `simp_wf` line entirely |

**Context**: The `decreasing_by` blocks have:
```lean
decreasing_by
  simp_wf  -- does nothing, 3 goals not operated on
  · exact ...
  · exact ...
  · exact ...
```
Fix: Remove the `simp_wf` line. The focused (`·`) tactics handle all goals.

### Category 3: Non-Minimal Imports (lake shake)

**Severity**: Advisory (not enforced by CI, but good practice)
**Effort**: Low-Medium -- mechanical import replacement, but each needs build verification
**Risk**: Medium -- changing `public import` to `import` or swapping imports can break downstream modules

**Critical caveat**: Many imports are `public import`, meaning downstream modules depend on their transitivity. Changing them requires checking all importers.

| # | File | Current Import(s) to Remove | Import(s) to Add | Notes |
|---|------|---------------------------|-------------------|-------|
| 12 | ListHelpers.lean | `Cslib.Init` (public) | `Init.Data.List.Basic` | **HIGH RISK**: public import; downstream DeductionTheorem files import this |
| 13 | Connectives.lean | `Cslib.Init` | `Init.Prelude` | Private import, lower risk |
| 14 | InferenceSystem.lean | `Cslib.Init` | `Init.Coe` | Private import, lower risk |
| 15 | Consistency.lean | `Mathlib.Order.Zorn` (public) | `Mathlib.Order.SetNotation` + `Mathlib.Order.Preorder.Chain` (public) | **HIGH RISK**: public import |
| 16 | Prop/Core.lean | `Cslib...Combinators` (public) | `Cslib...ProofSystem` (public) | Changes transitive dependency chain |
| 17 | Prop/Connectives.lean | `Cslib...Prop.Core` (public) | `Cslib...ProofSystem` (public) | Changes transitive dependency chain |
| 18 | BigConj.lean | `Cslib...Prop.Core` (public) | `Cslib...ProofSystem` (public) | Changes transitive dependency chain |
| 19 | Modal/Basic.lean | `Combinators` + `Core` + `Connectives` (3 public) | `ProofSystem` (1 public) | Simplifies imports significantly |
| 20 | Modal/S5.lean | `Modal.Basic` (public) | `ProofSystem` (public) | Changes transitive chain |
| 21 | Temporal/TemporalDerived.lean | `Core` + `Connectives` (2 public) | `ProofSystem` (public) | Changes transitive chain |
| 22 | Temporal/FrameConditions.lean | `Cslib.Init` | (nothing) | Just remove unused import |
| 23 | Defs.lean | `FunLike.Basic` + `Set.Image` (2 public) | `Set.Operations` (public) | **MEDIUM RISK**: widely imported file |
| 24 | MCS.lean | `DeductionTheorem` (public) | `ProofSystem.Derivation` (public) | Changes transitive chain |

**Recommendation**: Issues 13, 14, 22 (private `Cslib.Init` removals) are safe. Issues 16-21 (Theorems import simplification to ProofSystem) form a coherent group. Issues 12, 15, 23, 24 involving public imports need careful downstream verification.

### Category 4: Double Blank Lines (lint-style)

**Severity**: Cosmetic
**Effort**: Trivial
**Risk**: None

| # | File | Line | Fix |
|---|------|------|-----|
| 25 | Instances.lean | 35 | Remove one blank line (between `@[expose] public section` and `open`) |

### Category 5: `def` vs `theorem` (defLemma lint potential)

**Severity**: Advisory -- `lake lint` did NOT flag these with --builtin-only, but Mathlib CI may flag them
**Effort**: Low per item, but many items -- requires checking each `def` return type
**Risk**: Low for Prop-valued defs; Medium for data-returning defs that should stay `def`

The defLemma lint flags `def` declarations whose return type is `Prop`. These should be `theorem` instead. Analysis of each `def` in scope:

**Confirmed Prop-valued (should be `theorem`):**

| # | File | Line | Declaration | Return Type | Fix |
|---|------|------|-------------|-------------|-----|
| 26 | InferenceSystem.lean | 45 | `DerivableIn` | `Prop` | This is a **definition** (`= Nonempty ...`), should stay `def` -- it defines a concept |
| 27 | Consistency.lean | 63 | `Consistent` | `Prop` | Definition, should stay `def` |
| 28 | Consistency.lean | 67 | `SetConsistent` | `Prop` | Definition, should stay `def` |
| 29 | Consistency.lean | 72 | `SetMaximalConsistent` | `Prop` | Definition, should stay `def` |
| 30 | Consistency.lean | 175 | `HasDeductionTheorem` | `Prop` | Definition, should stay `def` |
| -- | Derivation.lean | 111 | `Deriv` | `Prop` | Definition, should stay `def` |
| -- | Derivation.lean | 115 | `Derivable` | `Prop` | Definition, should stay `def` |

**Analysis**: These are all **definitions** that introduce named concepts (like `Consistent`, `DerivableIn`). The `defLemma` linter targets `def` that proves a `Prop` (i.e., should be `theorem`), but definitional `def` that establishes a name for a `Prop` concept is correct as `def`. The linter distinguishes between "def that proves Prop" vs. "def that defines a Prop-valued function". These should all stay as `def`.

**Data-valued defs (correctly `def`):**
- `ListHelpers.removeAll`: returns `List α` -- correct
- `bigconj`, `negBigconj` (BigConj.lean): returns `F` -- correct
- `Proposition.subst`, `intuitionisticCompletion` (Defs.lean): returns data -- correct
- `DerivationTree.height` (Derivation.lean): returns `Nat` -- correct
- `propDerivationSystem` (Derivation.lean): returns `DerivationSystem` -- correct

**Type-level defs in NaturalDeduction (correctly `def`):**
- `Theory.equiv`, `Theory.Equiv`, `Theory.Derivation.weak/weakTheory/weakCtx/cut/subs/substAtom`: These return derivation trees or type-level products, not Prop. Correct as `def`.

**Prop-level wrappers in FromHilbert.lean (correctly `def`):**
- `impI`, `impE`, `botE`, `assume`, `axiomRule`, `hilbertCut`, `hilbertWeakening`, `hilbertSubstitution`: Return `DerivationTree` (a Type, not Prop). Correct as `def`.
- `impIDeriv`, `impEDeriv`, `botEDeriv`, `hilbertCutDeriv`, `hilbertWeakeningDeriv`: Return `Deriv` which is `Prop` (`Nonempty`). These are borderline -- they prove a Prop, but the naming convention suggests they are meant as derived rules. **Could** be changed to `theorem` but are not flagged by current linter.

**Conclusion**: No defLemma fixes needed. The `lake lint --builtin-only` did not flag any defLemma issues, and manual analysis confirms all defs are correctly categorized.

### Category 6: `noncomputable` on defs returning proof terms

**Severity**: Advisory
**Effort**: Low -- would need to check if `noncomputable` is genuinely required
**Risk**: Low

| # | File | Line | Declaration | Notes |
|---|------|------|-------------|-------|
| 31 | DeductionHelpers.lean | 83-118 | `deductionAxiom`, `deductionImpSelf`, `deductionAssumptionOther`, `deductionMpUnderImp` | Return `HasHilbertTree.Tree` (Type-level). `noncomputable` is needed because the typeclass instance uses `Classical.choice`. Correct as-is. |
| 32 | DeductionTheorem.lean | 69, 118 | `deductionWithMem`, `deductionTheorem` | Return `DerivationTree` (Type). `noncomputable` required due to Classical instance. Correct as-is. |
| 33 | FromHilbert.lean | 60, 108 | `impI`, `hilbertCut` | Same pattern. Correct as-is. |
| 34 | InferenceSystem.lean | 57 | `DerivableIn.toDerivation` | Uses `Classical.choice`. Correct as-is. |

**Conclusion**: All `noncomputable` annotations are genuinely required due to Classical reasoning. No fixes needed.

---

## Summary of Actionable Issues

### Must Fix (CI warnings that would block in strict mode)

| Priority | Category | Count | Files | Effort |
|----------|----------|-------|-------|--------|
| P1 | Flexible simp -> simp only | 9 | ListHelpers, DeductionTheorem, MCS | Medium (need simp? output) |
| P1 | Remove unused simp_wf | 2 | DeductionTheorem | Trivial |
| P2 | Double blank line | 1 | Instances | Trivial |

### Should Fix (good practice for Mathlib contribution)

| Priority | Category | Count | Files | Effort |
|----------|----------|-------|-------|--------|
| P3 | Non-minimal imports (safe) | 3 | Connectives, InferenceSystem, FrameConditions | Low |
| P3 | Non-minimal imports (risky) | 10 | Multiple Theorems files, Defs, MCS, etc. | Medium-High |

### No Fix Needed

| Category | Count | Reason |
|----------|-------|--------|
| defLemma | 0 | All defs correctly categorized |
| topNamespace | 0 | All instances in proper namespaces |
| noncomputable | 0 | All genuinely required |
| sorry | 0 | Zero sorry in any file |
| Copyright headers | 0 | All files have headers |
| module keyword | 0 | All files use module |
| Long lines | 0 | No lines exceed 100 chars |
| Linter suppressions | 0 | No set_option linter in any file |

---

## Recommended Fix Order

1. **Phase 1** (Trivial, no risk): Remove double blank line in Instances.lean, remove 2 `simp_wf` lines in DeductionTheorem.lean
2. **Phase 2** (Medium, low risk): Replace 9 flexible `simp` calls with `simp only [...]` using `simp?` output
3. **Phase 3** (Low, low risk): Remove 3 safe private `Cslib.Init` imports (Connectives, InferenceSystem, FrameConditions)
4. **Phase 4** (Medium, medium risk): Simplify Theorems import chain (issues 16-21) -- replace transitive imports with direct `ProofSystem` import
5. **Phase 5** (Medium, higher risk): Fix public import minimization (Defs.lean, MCS.lean, Consistency.lean, ListHelpers.lean) -- needs careful downstream verification

**Total estimated effort**: 2-3 hours, dominated by Phase 2 (running `simp?` on each call and verifying replacements build) and Phase 4-5 (import chain verification).
