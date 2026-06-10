# Research Report: Public Import Cslib.Init Analysis

- **Task**: 84 - Resolve public import Cslib.Init in Foundations/Logic files
- **Session**: sess_1781118126_4901e1
- **Date**: 2026-06-10

## Executive Summary

The `public import Cslib.Init` in all three target files (Connectives.lean, InferenceSystem.lean, FrameConditions.lean) **can be downgraded to plain `import Cslib.Init`**, but only if `import Cslib.Init` is simultaneously added to 5 downstream Foundations/Logic files that currently receive it transitively. This is a safe, mechanical change confirmed by `lake shake`. The previous attempt (task 70) was reverted because it did not add the compensating imports to downstream files.

## Background

### What Cslib.Init Provides

`Cslib.Init` imports three things:
1. `Cslib.Foundations.Lint.Basic` -- custom CSLib linters (e.g., `topNamespace`)
2. `Mathlib.Init` -- Mathlib initialization
3. `Mathlib.Tactic.Common` -- common Mathlib tactics

These provide linter infrastructure and tactics needed by virtually all CSLib files. The file itself contains no declarations -- it is purely an import aggregator.

### Why `public` Matters

In Lean 4 module files, `public import X` makes `X`'s declarations available to any file that imports the current file. A plain `import X` makes `X` available only within the current file. When `Connectives.lean` has `public import Cslib.Init`, any file importing `Connectives` automatically gets `Cslib.Init`'s contents (linters, tactics).

### Task 70 History

Task 70 attempted this exact downgrade and was reverted (commit `96e8bda`). The revert message states: "Task 70's import downgrades broke transitive access chain for downstream theorem files." The root cause was that the downgrade was applied without adding compensating `import Cslib.Init` lines to files that relied on transitive access.

## Analysis of Each Target File

### 1. Connectives.lean

**Current import**: `public import Cslib.Init` (line 9)

**Direct usage**: Connectives.lean defines typeclasses (`HasBot`, `HasImp`, `HasBox`, etc.) using only core Lean features (`class`, `Type*`, `abbrev`). It does not use Mathlib tactics or Cslib linters directly. However, `Cslib.Init` is still needed (not removable) because it provides `Mathlib.Init` which the Lean environment depends on for tactic infrastructure.

**Downstream files importing Connectives** (7 files):

| File | Has own `Cslib.Init`? | Impact of downgrade |
|------|----------------------|---------------------|
| `Axioms.lean` | NO | Needs `import Cslib.Init` added |
| `Metalogic/DeductionHelpers.lean` | NO | Needs `import Cslib.Init` added |
| `Metalogic/Consistency.lean` | NO | Needs `import Cslib.Init` added |
| `Bimodal/Syntax/Formula.lean` | YES | No impact |
| `Temporal/Syntax/Formula.lean` | YES | No impact |
| `Modal/Basic.lean` | YES | No impact |
| `Propositional/Defs.lean` | YES | No impact |

**Verdict**: CAN downgrade. Only 3 internal Foundations/Logic files need compensating imports. All 4 Logics/ files already have their own `public import Cslib.Init`.

### 2. InferenceSystem.lean

**Current import**: `public import Cslib.Init` (line 9)

**Direct usage**: Defines `InferenceSystem` typeclass, `DerivableIn`, and related infrastructure. Uses `Classical.choice` (from Mathlib/core), `Nonempty`, `Coe`, scoped notation. Requires `Cslib.Init` for tactic/environment support.

**Downstream files importing InferenceSystem** (5 files):

| File | Has own `Cslib.Init`? | Impact of downgrade |
|------|----------------------|---------------------|
| `ProofSystem.lean` | NO | Needs `import Cslib.Init` added |
| `Modal/Basic.lean` | YES | No impact |
| `LinearLogic/CLL/MLL.lean` | (via CLL/Basic) | Indirect; Basic.lean has own `Cslib.Init` |
| `LinearLogic/CLL/Basic.lean` | YES | No impact |
| `Propositional/NaturalDeduction/Basic.lean` | (via Defs.lean) | Defs.lean has own `Cslib.Init` |

**Verdict**: CAN downgrade. Only `ProofSystem.lean` needs a compensating import (it already gets `Cslib.Init` transitively via both Connectives and InferenceSystem, but would lose both if both are downgraded).

### 3. FrameConditions.lean (Theorems/Temporal/FrameConditions.lean)

**Current imports**:
```
public import Cslib.Init
public import Mathlib.Algebra.Order.Group.Defs
public import Mathlib.Algebra.Order.Group.Int
public import Mathlib.Data.Int.SuccPred
public import Mathlib.Order.SuccPred.LinearLocallyFinite
```

**Direct usage**: Defines temporal frame condition typeclasses (`LinearTemporalFrame`, `SerialFrame`, `DenseTemporalFrame`, `DiscreteTemporalFrame`) and `Int` instances. Uses `AddCommGroup`, `LinearOrder`, `IsOrderedAddMonoid`, `Nontrivial`, `NoMaxOrder`, `NoMinOrder`, `DenselyOrdered`, `SuccOrder`, `PredOrder`, `IsSuccArchimedean` from Mathlib.

**lake shake recommendation**: Remove `public` from `Cslib.Init` plus remove 3 of 4 Mathlib public imports (`Algebra.Order.Group.Defs`, `Algebra.Order.Group.Int`, `Order.SuccPred.LinearLocallyFinite`). Add `import Mathlib.Data.Finset.Attr` and change to `import Cslib.Init`.

**Downstream files importing FrameConditions** (2 files):

| File | Has own `Cslib.Init`? | Impact of downgrade |
|------|----------------------|---------------------|
| `Temporal/Theorems.lean` (barrel) | NO | Needs `import Cslib.Init` added |
| `Foundations/Logic/Theorems.lean` (barrel) | NO | Needs `import Cslib.Init` added |

**Verdict**: CAN downgrade `Cslib.Init` to plain import. The 2 barrel files need compensating imports. Note: the 3 Mathlib public import downgrades are a separate concern (scope of this task focuses on `Cslib.Init`).

## Complete Change Set

### Phase 1: Downgrade public to import in target files (3 edits)

1. `Cslib/Foundations/Logic/Connectives.lean`: `public import Cslib.Init` -> `import Cslib.Init`
2. `Cslib/Foundations/Logic/InferenceSystem.lean`: `public import Cslib.Init` -> `import Cslib.Init`
3. `Cslib/Foundations/Logic/Theorems/Temporal/FrameConditions.lean`: `public import Cslib.Init` -> `import Cslib.Init`

### Phase 2: Add compensating imports (5 edits)

These files currently receive `Cslib.Init` transitively and need explicit imports:

1. `Cslib/Foundations/Logic/Axioms.lean`: Add `import Cslib.Init`
2. `Cslib/Foundations/Logic/Metalogic/DeductionHelpers.lean`: Add `import Cslib.Init`
3. `Cslib/Foundations/Logic/ProofSystem.lean`: Add `import Cslib.Init`
4. `Cslib/Foundations/Logic/Theorems/Combinators.lean`: Add `import Cslib.Init`
5. `Cslib/Foundations/Logic/Theorems.lean`: Add `import Cslib.Init`

**Note**: `Metalogic/Consistency.lean` also needs `import Cslib.Init` per `lake shake`, but it gets Cslib.Init transitively through `Mathlib.Order.Zorn` (which depends on core infrastructure). Regardless, adding it explicitly is good practice and `lake shake` recommends it.

### Phase 3: Verification

- `lake build` to confirm no breakage
- `lake shake` to confirm no further `public import` warnings for `Cslib.Init` in these files

## Why Task 70 Failed and How to Avoid the Same Mistake

Task 70 downgraded the `public` keyword in 4 files (Connectives, Axioms, InferenceSystem, ProofSystem) but did NOT add compensating `import Cslib.Init` lines to downstream files. When a file like `Combinators.lean` (which imports `ProofSystem.lean` which imports `Axioms.lean` which imports `Connectives.lean`) lost its transitive access to `Cslib.Init`, the build broke.

The fix is straightforward: Phase 1 (downgrade) and Phase 2 (compensating imports) must be done atomically. Both phases are mechanical edits with no semantic changes.

## Risk Assessment

**Risk Level**: Low

- The changes are purely about import visibility, not code semantics
- `lake shake` confirms the exact set of changes needed
- `lake build` will catch any missed files immediately
- The pattern is well-established in the CSLib codebase (many files already have explicit `import Cslib.Init`)
- No downstream Logics/ files are affected (they all already have their own `Cslib.Init` imports)

## Recommendation

Proceed with implementation. The 8 edits (3 downgrades + 5 compensating imports) form a clean, mechanical change set. This resolves the `lake shake` warnings while maintaining full build correctness.
