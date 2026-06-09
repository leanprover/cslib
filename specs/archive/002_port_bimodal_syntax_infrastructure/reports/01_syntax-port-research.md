# Task 2: Temporal Syntax Port -- Research Report

## Executive Summary

Porting the BimodalLogic `Theories/Bimodal/Syntax/` module (5 files, ~1,427 lines) to `Cslib/Logics/Temporal/Syntax/` is feasible with moderate adaptation. The key complexity is NOT a mechanical namespace rename -- the BimodalLogic Formula has 6 constructors (including `box`) while the cslib Temporal Formula has 5 constructors (no `box`). Every file requires stripping box-related content. Additionally, the BimodalLogic uses a concrete `Atom` structure while cslib parameterizes `Formula` over a generic type variable.

**Verdict**: Feasible, no blockers. Estimated ~1,200 lines of ported code (down from ~1,427 due to box removal and Atom restructuring).

## 1. Source File Analysis

### 1.1 Atom.lean (208 lines)

**Source**: `/home/benjamin/Projects/BimodalLogic/Theories/Bimodal/Syntax/Atom.lean`

**Contents**:
- `Atom` structure: `{ base : String, fresh_index : Option Nat }` with `Repr, DecidableEq, BEq, Hashable`
- `ReflBEq Atom`, `LawfulBEq Atom` instances
- `Atom.mk_base`, `Atom.mk_fresh`, `Atom.fresh_base` constructors
- `Countable Atom` via equivalence with `String x Option Nat`
- `Infinite Atom` via injection from `Nat`
- `Atom.exists_fresh` (freshness property for Finsets)
- Countability prerequisites: `Countable Char`, `Countable String`

**Mathlib imports**: `Mathlib.Data.Finset.Basic`, `Mathlib.Data.Fintype.EquivFin`, `Mathlib.Data.Countable.Basic`, `Mathlib.Tactic.DeriveCountable`, `Mathlib.Logic.Equiv.Basic`, `Mathlib.Logic.Equiv.List`

**Porting Decision**: The cslib Temporal `Formula` is already parameterized over a generic `Atom : Type u`. This means the concrete `Atom` structure from BimodalLogic is NOT needed in cslib. Instead:
- The `Atom` structure and its instances belong to the BimodalLogic project, not to cslib
- Any downstream code that needs countable/infinite atoms should add typeclass constraints like `[Countable Atom] [Infinite Atom]` to their definitions
- The freshness theorem is a direct consequence of `Infinite.exists_notMem_finset` (confirmed available in cslib's Mathlib)

**Recommendation**: Do NOT port Atom.lean as a separate file. Instead, add typeclass constraints on `Atom` where needed in other files. If BimodalLogic-specific atom infrastructure is needed later, it can be provided as an instance in a downstream file.

### 1.2 Formula.lean (737 lines)

**Source**: `/home/benjamin/Projects/BimodalLogic/Theories/Bimodal/Syntax/Formula.lean`

**Existing target**: `/home/benjamin/Projects/cslib/Cslib/Logics/Temporal/Syntax/Formula.lean` (94 lines, already exists)

**Existing content in cslib**:
- 5-constructor `Formula` inductive (atom, bot, imp, untl, snce) -- CORRECT
- Derived operators: `neg`, `top`, `or`, `and`, `some_future`, `all_future`, `some_past`, `all_past`
- Scoped notation for all operators
- `TemporalConnectives` instance

**Content to port from BimodalLogic** (after stripping `box`):
- `Countable Formula` instance (requires `deriving Countable` or manual proof)
- `Infinite Formula` via `Formula.atom_injective`
- `Denumerable Formula` instance
- `Formula.atom_s` helper (string convenience)
- `Formula.complexity` function (strip all box cases and box-related derived operator patterns)
- `ReflBEq Formula`, `LawfulBEq Formula` instances (strip box case from proofs)
- `Formula.beq_refl`, `Formula.eq_of_beq` theorems
- `Formula.modalDepth` -- SKIP (no box in temporal)
- `Formula.temporalDepth` (keep, strip box case)
- `Formula.countImplications` (keep, strip box case)
- `Formula.diamond` -- SKIP (no box in temporal)
- `Formula.always`, `Formula.sometimes` (keep)
- `Formula.next`, `Formula.prev` (keep)
- `Formula.weak_future`, `Formula.weak_past` (keep)
- `Formula.release`, `Formula.trigger` (keep)
- `Formula.weak_until`, `Formula.weak_since` (keep)
- `Formula.strong_release`, `Formula.strong_trigger` (keep)
- `Formula.swap_temporal` and all swap theorems (keep, strip box case)
- `Formula.needsPositiveHypotheses` (keep, strip box case)
- `Formula.atoms` (keep, strip box case)
- `Formula.predFormulas` -- SKIP (box-specific)
- All `#eval` complexity checks need re-validation (different complexity values without box patterns)

**Estimated ported lines**: ~500 lines (down from 737 after stripping box-related content)

### 1.3 Context.lean (204 lines)

**Source**: `/home/benjamin/Projects/BimodalLogic/Theories/Bimodal/Syntax/Context.lean`

**Contents**:
- `Context` type alias: `List Formula`
- `Context.map`, `Context.isEmpty`, `Context.singleton`
- Theorems: `map_length`, `map_comp`, `map_id`, `map_nil`, `map_cons`, `map_append`
- Membership theorems: `mem_map_iff`, `mem_map_of_mem`, `not_mem_nil`, `mem_singleton_iff`
- `isEmpty_iff_eq_nil`, `exists_mem_of_ne_nil`

**Porting changes**: Namespace rename only. No box references in this file. The `Formula` type is referenced as an unqualified name from within the `Bimodal.Syntax` namespace -- must update to use `Temporal.Formula Atom` or import properly.

**Critical issue**: The BimodalLogic `Context` is `List Formula` where `Formula` has a fixed `Atom` type. The cslib `Formula` is `Formula Atom` -- parameterized. So `Context` must become either:
- `abbrev Context (Atom : Type u) := List (Formula Atom)` (parameterized), or
- A more general approach using the foundation `Cslib.HasContext` typeclass

**Recommendation**: Use the parameterized approach (`Context Atom := List (Formula Atom)`) for simplicity and compatibility with BimodalLogic proof structure.

**Estimated ported lines**: ~190 lines

### 1.4 BigConj.lean (49 lines)

**Source**: `/home/benjamin/Projects/BimodalLogic/Theories/Bimodal/Syntax/BigConj.lean`

**Contents**:
- `bigconj : List Formula -> Formula` (fold conjunction, base case top)
- `neg_bigconj`
- `@[simp]` lemmas: `bigconj_nil`, `bigconj_singleton`, `bigconj_cons_cons`, `neg_bigconj_def`

**Porting changes**: Namespace rename and parameterize over `Atom`. No box references. The `Formula.and` and `Formula.neg` used are the same in cslib temporal.

**Estimated ported lines**: ~45 lines

### 1.5 Subformulas.lean (229 lines)

**Source**: `/home/benjamin/Projects/BimodalLogic/Theories/Bimodal/Syntax/Subformulas.lean`

**Contents**:
- `Formula.subformulas : Formula -> List Formula`
- `Formula.subformulaCount`
- `self_mem_subformulas` and per-constructor membership lemmas
- `subformulas_trans` (transitivity)
- Direct membership lemmas: `mem_subformulas_of_imp_left`, `_right`, `_box`, `_all_past`, `_all_future`, `_untl_left`, `_untl_right`, `_snce_left`, `_snce_right`

**Porting changes**: Strip `box` case from `subformulas` function and remove `box_inner_mem_subformulas`, `mem_subformulas_of_box`. Remove `box` branches from `subformulas_trans` induction. Namespace rename and parameterize over `Atom`.

**Mathlib imports**: `Mathlib.Data.List.Basic` -- this import may not be needed at all with modern Lean since most `List` lemmas are in `Init`. Should verify during implementation.

**Estimated ported lines**: ~200 lines

## 2. Dependency Analysis

### 2.1 Internal dependencies (source files)

```
Atom.lean (standalone)
  ^
  |
Formula.lean (imports Atom)
  ^        ^        ^
  |        |        |
Context.lean  BigConj.lean  Subformulas.lean
```

### 2.2 Ported dependency graph

Since Atom.lean is not being ported as a file, the new structure is:

```
Formula.lean (standalone, imports Cslib.Init + Connectives)
  ^        ^        ^
  |        |        |
Context.lean  BigConj.lean  Subformulas.lean
```

### 2.3 External dependencies

All needed Mathlib APIs confirmed available in cslib's Mathlib (rev `eb15debe`):
- `Infinite.exists_notMem_finset` (Mathlib.Data.Fintype.EquivFin)
- `Denumerable` (Mathlib.Logic.Denumerable)
- `nonempty_denumerable` (Mathlib.Logic.Denumerable)
- `String.toList_injective` (Init.Data.String.Basic)
- `List.mem_cons`, `List.mem_append`, `List.map_map` (Init.Data.List.Lemmas)
- `List.eraseDups` (Init.Data.List.Basic)
- `Countable`, `Infinite`, `Function.Injective` (stdlib / Mathlib)

### 2.4 Downstream dependencies in cslib

The existing file `Cslib/Logics/Bimodal/Embedding/TemporalEmbedding.lean` already imports `Cslib.Logics.Temporal.Syntax.Formula`. Any changes to Formula.lean must preserve the existing interface:
- The `Formula` inductive with its 5 constructors (atom, bot, imp, untl, snce)
- The `TemporalConnectives` instance
- All notation definitions

The embedding file does NOT depend on Context, BigConj, or Subformulas.

## 3. Namespace and Convention Analysis

### 3.1 Namespace pattern

Existing cslib convention for logic modules:
- `Cslib.Logic.PL` (Propositional Logic, in `Cslib/Logics/Propositional/`)
- `Cslib.Logic.Modal` (Modal Logic, in `Cslib/Logics/Modal/`)
- `Cslib.Logic.Temporal` (Temporal Logic, in `Cslib/Logics/Temporal/`)
- `Cslib.Logic.Bimodal` (Bimodal Logic, in `Cslib/Logics/Bimodal/`)

Note the convention: file path uses `Logics` (plural) but namespace uses `Logic` (singular).

The existing `Formula.lean` uses `namespace Cslib.Logic.Temporal` -- this is correct per convention.

### 3.2 File header pattern

```lean
/-
Copyright (c) 2026 Benjamin Brastmckie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brastmckie
-/

module

public import Cslib.Init
public import Cslib.Foundations.Logic.Connectives
```

### 3.3 Section and expose pattern

Existing files use `@[expose] public section` to make definitions accessible. This should be followed.

### 3.4 Formula naming

The existing cslib pattern uses `Formula` (not `Proposition`) for temporal and bimodal logic, and `Proposition` for propositional and modal logic. The ported files should use `Formula`.

## 4. Toolchain Compatibility

- **BimodalLogic**: Lean 4.27.0-rc1
- **cslib**: Lean 4.31.0-rc1

Key differences that may affect the port:
- `module` keyword is available and used in cslib (adds `module` at file top)
- `public import` is used instead of bare `import`
- Some tactic behavior may have changed (especially `simp`, `omega`)
- `deriving` clauses should work identically for `DecidableEq`, `BEq`
- Need to verify that `deriving Countable` works on the temporal formula (BimodalLogic uses it on the bimodal formula)

## 5. Porting Checklist Feasibility

| Checklist Item | Status | Notes |
|---|---|---|
| Rename namespace | Feasible | `Bimodal.Syntax` -> `Cslib.Logic.Temporal` |
| Add module declaration | Feasible | Already present in existing Formula.lean |
| Replace Mathlib imports | Feasible | Use `public import Cslib.Init` + specific Mathlib |
| Add Apache 2.0 header | Feasible | Template established |
| Run lake shake | Feasible | Post-implementation step |
| Run Mathlib linter | Feasible | `set_option linter.all true` |
| Verify lake build | Feasible | Post-implementation step |
| Zero sorry | Feasible | Source has zero sorry |

## 6. Risk Assessment

### Low Risk
- Context.lean: Mechanical namespace change + parameterization
- BigConj.lean: Mechanical namespace change + parameterization
- Copyright headers: Template established

### Medium Risk
- Formula.lean complexity function: The pattern matching for derived operators is intricate. Stripping box patterns from the 30+ cases requires careful attention. Some complexity patterns may not apply (e.g., diamond is box-dependent).
- Subformulas.lean: Removing box case from transitivity proof requires re-checking the induction still works cleanly.
- `beq_iff_eq` usage: The lemma name may have shifted between Lean 4.27 and 4.31. The BimodalLogic source uses `beq_iff_eq.mp` -- need to verify this still exists.

### Low Risk (but important)
- The existing Formula.lean in cslib must be EXTENDED, not replaced. It already has 94 lines of correct infrastructure. New content (complexity, BEq, swap_temporal, etc.) should be appended.
- The `Cslib.lean` root import file needs new entries for Context, BigConj, and Subformulas.

## 7. Recommended Implementation Plan

### Phase 1: Extend Formula.lean (~300 lines added)
- Add `deriving Countable` to the Formula inductive (or add as a separate instance)
- Add `Infinite`, `Denumerable` instances
- Add BEq reflexivity and injectivity proofs
- Add `ReflBEq`, `LawfulBEq` instances
- Add `complexity`, `temporalDepth`, `countImplications` functions
- Add derived temporal operators: `always`, `sometimes`, `next`, `prev`, `weak_future`, `weak_past`, `release`, `trigger`, `weak_until`, `weak_since`, `strong_release`, `strong_trigger`
- Add `swap_temporal` and all its theorems
- Add `needsPositiveHypotheses` and simp lemmas
- Add `atoms` function

### Phase 2: Create Context.lean (~190 lines)
- Create `Cslib/Logics/Temporal/Syntax/Context.lean`
- Define `Context Atom := List (Formula Atom)`
- Port all Context operations and theorems

### Phase 3: Create BigConj.lean (~45 lines)
- Create `Cslib/Logics/Temporal/Syntax/BigConj.lean`
- Port bigconj and simp lemmas

### Phase 4: Create Subformulas.lean (~200 lines)
- Create `Cslib/Logics/Temporal/Syntax/Subformulas.lean`
- Port subformulas function (5 constructors instead of 6)
- Port all membership and transitivity theorems

### Phase 5: Integration
- Update `Cslib.lean` root import file with new modules
- Run `lake build` to verify everything compiles
- Run `lake shake` on each file
- Verify zero sorry
- Verify linter passes

## 8. Key Design Decisions for Planner

1. **No Atom.lean port**: The parameterized formula makes a concrete Atom type unnecessary. Add typeclass constraints where needed instead.

2. **Extend, don't replace Formula.lean**: The existing 94-line file is correct and has downstream dependencies (TemporalEmbedding.lean). Append new content.

3. **Parameterize Context over Atom**: Use `Context (Atom : Type u) := List (Formula Atom)` to match the parameterized Formula.

4. **Strip box-related content**: Remove all box-case branches from complexity, swap_temporal, subformulas, etc. Remove diamond, modalDepth, predFormulas entirely.

5. **Use `abbrev` for derived operators**: The existing Formula.lean uses `abbrev` for derived operators (neg, top, or, and, some_future, etc.). New derived operators (always, next, etc.) should use `def` matching the BimodalLogic source (where `always` uses `def`, not `abbrev`).

6. **Complexity function simplification**: Without box, the complexity function has ~20 fewer pattern cases. The derived-operator patterns for diamond should be removed entirely.
