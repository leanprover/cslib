# Research Report: Port Frame Semantics (PR 2) to Cslib

**Task**: 3 -- Port TaskFrame, WorldHistory, TaskModel, Truth, Validity to Cslib/Logics/Bimodal/Semantics/
**Session**: sess_1780970224_ba1435_3
**Date**: 2026-06-08

## Executive Summary

This report analyzes the porting of 5 source files (~1,822 lines) from `BimodalLogic/Theories/Bimodal/Semantics/` to `Cslib/Logics/Bimodal/Semantics/`. The port is feasible with well-understood transformation patterns. The primary challenge is adapting from the source's concrete `Atom` type to cslib's polymorphic `Formula Atom` pattern. All Mathlib dependencies are already available in cslib's dependency graph.

## Source File Analysis

### File Inventory

| File | Lines | Purpose | Dependencies |
|------|-------|---------|--------------|
| TaskFrame.lean | 302 | Task frame structure + finite frames | Mathlib.Algebra.Order.Group.Defs, Mathlib.Data.Fintype.Basic |
| WorldHistory.lean | 418 | World histories with convex domains, time-shift | TaskFrame.lean |
| TaskModel.lean | 93 | Model = frame + valuation | TaskFrame.lean, WorldHistory.lean, Formula.lean |
| Truth.lean | 694 | Truth evaluation, time-shift preservation | TaskModel.lean, WorldHistory.lean, Formula.lean |
| Validity.lean | 315 | Validity, consequence, satisfiability | Truth.lean, Context.lean, Mathlib.Order.SuccPred.{Basic,Archimedean} |
| **Total** | **1,822** | | |

### Dependency Graph (Import Order)

```
TaskFrame.lean          (standalone, only Mathlib imports)
    |
    v
WorldHistory.lean       (imports TaskFrame)
    |
    v
TaskModel.lean          (imports TaskFrame, WorldHistory, Formula)
    |
    v
Truth.lean              (imports TaskModel, WorldHistory, Formula)
    |
    v
Validity.lean           (imports Truth, Context, Mathlib.Order.SuccPred)
```

This is a clean linear dependency chain. Files should be ported in this exact order.

## Architectural Differences: Source vs. Target

### 1. Formula Type Parametrization (CRITICAL)

**Source** (`BimodalLogic`):
- `Formula : Type` -- concrete type, `Atom` is a specific structure with `base : String` and `fresh_index : Option Nat`
- `namespace Bimodal.Syntax`

**Target** (`cslib`):
- `Formula (Atom : Type u) : Type u` -- universe-polymorphic over atom type
- `namespace Cslib.Logic.Bimodal`

**Impact**: Every definition that mentions `Formula` or `Atom` must be parameterized. Specifically:
- `TaskModel.valuation : F.WorldState -> Atom -> Prop` becomes `valuation : F.WorldState -> Atom -> Prop` with `Atom` as a type parameter
- `truth_at` must carry `Atom` as a parameter
- `valid`, `semantic_consequence`, `satisfiable` must quantify over or be parameterized by `Atom`

**Recommendation**: Use `variable {Atom : Type*}` and thread `Formula Atom` throughout. The source's `open Bimodal.Syntax` becomes unnecessary since cslib uses the `Cslib.Logic.Bimodal` namespace directly.

### 2. Namespace Convention

| Component | Source | Target |
|-----------|--------|--------|
| Top namespace | `Bimodal.Semantics` | `Cslib.Logic.Bimodal` |
| Formula access | `open Bimodal.Syntax` then `Formula` | Direct `Formula Atom` |
| Frame struct | `Bimodal.Semantics.TaskFrame` | `Cslib.Logic.Bimodal.TaskFrame` |

### 3. Module Declaration

cslib files use `module` declaration at top (Lean 4 feature for module-level hygiene). Source files do not. All target files need:
```lean
module
```

### 4. Copyright Header

All cslib files have the Apache 2.0 header:
```lean
/-
Copyright (c) 2026 Benjamin Brastmckie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brastmckie
-/
```

### 5. Import Paths

| Source Import | Target Import |
|---------------|---------------|
| `import Bimodal.Semantics.TaskFrame` | `import Cslib.Logics.Bimodal.Semantics.TaskFrame` |
| `import Bimodal.Semantics.WorldHistory` | `import Cslib.Logics.Bimodal.Semantics.WorldHistory` |
| `import Bimodal.Syntax.Formula` | `import Cslib.Logics.Bimodal.Syntax.Formula` |
| `import Bimodal.Syntax.Context` | Needs Bimodal Context (see below) |
| `import Mathlib.Algebra.Order.Group.Defs` | `import Mathlib.Algebra.Order.Group.Defs` (unchanged) |
| `import Mathlib.Data.Fintype.Basic` | `import Mathlib.Data.Fintype.Basic` (unchanged) |
| `import Mathlib.Order.SuccPred.Basic` | `import Mathlib.Order.SuccPred.Basic` (unchanged) |
| `import Mathlib.Order.SuccPred.Archimedean` | `import Mathlib.Order.SuccPred.Archimedean` (unchanged) |

### 6. `expose` / `public section` Pattern

cslib uses `@[expose] public section` to control symbol visibility. Source files do not. Target files should follow the existing pattern in `Cslib/Logics/Bimodal/Syntax/Formula.lean`.

## Missing Infrastructure in cslib

### 1. Context Type for Bimodal Logic (Required by Validity.lean)

The source `Validity.lean` imports `Bimodal.Syntax.Context` which defines `Context := List Formula`. cslib does not have a Bimodal Context type yet, though it has a Temporal one at `Cslib.Logics.Temporal.Syntax.Context`.

**Options**:
- **(A) Create `Cslib/Logics/Bimodal/Syntax/Context.lean`** mirroring the Temporal pattern: `abbrev Context (Atom : Type u) := List (Formula Atom)`. This is ~20 lines and trivial.
- **(B) Inline the definition** in Validity.lean: `abbrev Context (Atom : Type u) := List (Formula Atom)` locally.
- **(C) Use `List (Formula Atom)` directly** in Validity.lean without an alias.

**Recommendation**: Option (A) -- create a separate Context file. This matches the Temporal pattern and will be needed for proof system porting later. It is a very small addition and should be done as part of this task's implementation.

### 2. `strong_release` / `strong_trigger` (Used by Truth.lean)

The source Truth.lean has `@[simp]` theorems for `Formula.strong_release` and `Formula.strong_trigger`. cslib's Bimodal Formula does NOT currently define these derived connectives (they exist in `Cslib.Logics.Temporal.Syntax.Formula` but not Bimodal).

**Impact**: The `strong_release_iff` and `strong_trigger_iff` theorems in Truth.lean reference these. Two options:
- **(A) Add `strong_release`/`strong_trigger`** to `Cslib/Logics/Bimodal/Syntax/Formula.lean` (2-line definitions each, matching the Temporal pattern).
- **(B) Drop these theorems** from the port since they are convenience lemmas, not core semantics.

**Recommendation**: Option (B) for the initial port. These are derived simp lemmas and can be added later if needed. The core truth definition (`truth_at`) only pattern-matches on 6 constructors and does not reference these derived forms. Alternatively, if the implementer adds them, it's a small 4-line addition to Formula.lean plus the 2 theorems.

### 3. Semantics Directory

`Cslib/Logics/Bimodal/Semantics/` does not exist yet and must be created.

## Mathlib Dependencies Verification

All required Mathlib typeclasses and lemmas are available in cslib's Mathlib dependency:

| Typeclass/Lemma | Status | Location |
|-----------------|--------|----------|
| `AddCommGroup` | Available | Mathlib.Algebra.Group.Defs |
| `LinearOrder` | Available | Mathlib (core) |
| `IsOrderedAddMonoid` | Available | Mathlib.Algebra.Order.Monoid.Defs |
| `Finite` | Available | Mathlib.Data.Fintype.Basic |
| `DenselyOrdered` | Available | Mathlib.Order.Basic |
| `SuccOrder` / `PredOrder` | Available | Mathlib.Order.SuccPred.Basic |
| `IsSuccArchimedean` / `IsPredArchimedean` | Available | Mathlib.Order.SuccPred.Archimedean |
| `Nontrivial` | Available | Lean core |
| `neg_nonneg` | Available | Mathlib.Algebra.Order.Group.Unbundled.Basic |
| `add_sub_add_right_eq_sub` | Available | Mathlib.Algebra.Group.Basic |
| `neg_add_cancel` | Available | Lean core (AddGroup) |

## Key Definitions to Port

### TaskFrame.lean
- `structure TaskFrame (D : Type*)` -- core frame with `WorldState`, `task_rel`, and 3 axioms
- `TaskFrame.nullity` -- derived reflexivity theorem
- `TaskFrame.backward_comp` -- derived backward compositionality
- `TaskFrame.trivial_frame`, `identity_frame`, `nat_frame` -- example frames
- `structure FiniteTaskFrame (D : Type*)` -- frame with `Finite WorldState`

### WorldHistory.lean
- `structure WorldHistory` -- domain, convexity, states, respects_task
- `WorldHistory.universal`, `.trivial`, `.universal_trivialFrame`, `.universal_natFrame` -- constructors
- `WorldHistory.state_at` -- helper
- `WorldHistory.time_shift` -- fundamental construction for soundness
- 10+ lemmas about time-shift (domain_iff, inverse, states_eq, cancellation)
- Order reversal lemmas: `neg_lt_neg_iff`, `neg_le_neg_iff`, `neg_neg_eq`, `neg_injective`

### TaskModel.lean
- `structure TaskModel` -- frame + valuation
- `TaskModel.all_false`, `.all_true` -- trivial models
- `TaskModel.from_list` -- convenience constructor
- `abbrev FiniteTaskModel` -- model over finite frame

### Truth.lean
- `def truth_at` -- recursive truth evaluation (6 cases)
- `Truth.bot_false`, `.imp_iff`, `.atom_iff_of_domain`, `.atom_false_of_not_domain` -- basic lemmas
- `Truth.box_iff`, `.some_future_iff`, `.some_past_iff`, `.future_iff`, `.past_iff` -- operator lemmas
- `Truth.strong_release_iff`, `.strong_trigger_iff` -- derived operator lemmas (may skip, see above)
- `def ShiftClosed` -- set closure under time-shift
- `Set.univ_shift_closed` -- universal set is shift-closed
- `TimeShift.truth_history_eq`, `.truth_double_shift_cancel` -- transport lemmas
- `TimeShift.time_shift_preserves_truth` -- KEY theorem (~250 lines of proof)
- `TimeShift.exists_shifted_history` -- corollary

### Validity.lean
- `def valid` -- universal validity
- `def semantic_consequence` -- Gamma entails phi
- `def satisfiable` -- context satisfiability
- `def satisfiable_abs` -- absolute satisfiability
- `def formula_satisfiable` -- single formula satisfiability
- `def valid_dense` -- validity over dense orders
- `def valid_discrete` -- validity over discrete orders
- 10 theorems: monotonicity, reduction, explosion, etc.

## Porting Transformations Checklist

For each file, apply these transformations:

1. **Add copyright header** (Apache 2.0)
2. **Add `module` declaration**
3. **Rename namespace**: `Bimodal.Semantics` -> `Cslib.Logic.Bimodal`
4. **Update import paths**: `Bimodal.X.Y` -> `Cslib.Logics.Bimodal.X.Y`
5. **Parametrize by Atom**: Add `{Atom : Type*}` where Formula is used
6. **Replace `Formula` with `Formula Atom`** in type signatures
7. **Replace `Atom` type** references (the source's concrete struct) with the type variable
8. **Add `@[expose] public section`** wrapping
9. **Replace `open Bimodal.Syntax`** with appropriate opens/namespacing
10. **Run `lake build`** to verify

### File-Specific Notes

**TaskFrame.lean**: Minimal changes needed. No Formula or Atom dependency. Only namespace and header changes. The `IsOrderedAddMonoid` typeclass constraint pattern is unchanged.

**WorldHistory.lean**: Same as TaskFrame -- no Formula/Atom dependency. Clean port.

**TaskModel.lean**: 
- `valuation : F.WorldState -> Atom -> Prop` -- the source `Atom` here is the concrete struct. In cslib, this becomes parameterized: the `TaskModel` structure needs an `Atom` type parameter.
- `from_list` helper uses `p.base` and `p.fresh_index.isNone` -- these are specific to the source's `Atom` struct. This helper should either be **dropped** or **generalized** (e.g., take a membership predicate). Recommend dropping since it's a testing convenience.

**Truth.lean**:
- `truth_at` pattern matches on `Formula.atom p` -- in cslib this becomes `Formula.atom p` with `p : Atom` where `Atom` is the type variable. The match cases are identical in structure.
- The `strong_release_iff` and `strong_trigger_iff` theorems can be deferred (see above).
- `open Bimodal.Syntax` needs replacement.

**Validity.lean**:
- Needs `Context` type -- either inline or create Context file (recommend create).
- `semantic_consequence` and `satisfiable` use `Context` type.
- All `valid*` definitions quantify over `D : Type` (not `Type*`) to avoid universe issues -- this pattern should be preserved.

## Risk Assessment

| Risk | Severity | Mitigation |
|------|----------|------------|
| Atom parametrization causes universe issues | Medium | Follow existing cslib patterns; use `Type*` for Atom |
| `truth_at` recursion with polymorphic Atom | Low | Pattern matching on inductive constructors is unchanged |
| Missing Context type | Low | Create minimal Context.lean (~20 lines) |
| TimeShift proof complexity (~250 lines) | Low | Proofs are algebraic, independent of Atom type |
| `from_list` helper incompatibility | Low | Drop it; it's test-only convenience |
| `strong_release`/`strong_trigger` absence | Low | Drop these theorems or add 4-line defs to Formula.lean |

## Recommended Implementation Order

1. **TaskFrame.lean** (standalone, no cross-file dependencies)
2. **WorldHistory.lean** (depends only on TaskFrame)
3. **Context.lean** (new file, depends only on Formula -- needed by Validity)
4. **TaskModel.lean** (depends on TaskFrame, WorldHistory, Formula)
5. **Truth.lean** (depends on TaskModel, WorldHistory, Formula)
6. **Validity.lean** (depends on Truth, Context)

## Estimated Effort

| File | Source Lines | Est. Target Lines | Complexity |
|------|-------------|-------------------|------------|
| TaskFrame.lean | 302 | ~290 | Low -- namespace/header changes only |
| WorldHistory.lean | 418 | ~410 | Low -- namespace/header changes only |
| Context.lean (new) | 0 | ~30 | Trivial |
| TaskModel.lean | 93 | ~80 | Low -- drop `from_list`, add Atom param |
| Truth.lean | 694 | ~650 | Medium -- add Atom param, possibly drop 2 simp lemmas |
| Validity.lean | 315 | ~310 | Low -- add Atom param, use new Context |
| **Total** | **1,822** | **~1,770** | |

## Conclusion

The port is straightforward with well-understood transformation patterns. The primary structural change (Atom parametrization) follows established cslib conventions visible in the Formula.lean and embedding files. All Mathlib dependencies are available. The recommended 6-file implementation order respects the dependency chain. No blocking issues were identified.
