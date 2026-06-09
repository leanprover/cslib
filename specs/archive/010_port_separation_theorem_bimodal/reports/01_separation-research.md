# Research Report: Port Separation Theorem (Task 10)

**Session**: sess_1781007220_8b0662_10
**Date**: 2026-06-09
**Source**: `BimodalLogic/Theories/Bimodal/Metalogic/WeakCanonical/Separation/`
**Target**: `Cslib/Logics/Bimodal/Metalogic/Separation/`

## 1. Source File Inventory

### 1.1 Core Files (in barrel, required for separation theorem)

| # | Source File | Lines | Key Content |
|---|-------------|-------|-------------|
| 1 | `Defs.lean` | 553 | IntStructure, int_truth, int_equiv, is_U_free, is_S_free, is_syntactically_separated, is_separable, junction_depth, structural measures |
| 2 | `FormulaOps.lean` | 235 | subst_formula, IntStructure.withAtom, subst_correctness, Literal/Clause/DNF/CNF, fresh_atom, fresh_atoms |
| 3 | `IntHelpers.lean` | 131 | Integer-specific lemmas for finite intervals and witness constructions |
| 4 | `Duality.lean` | 342 | IntStructure.reverse, swap_temporal_int_truth, dual_equiv, dual_separated, boolean closure for purity predicates |
| 5 | `Distributivity.lean` | 188 | Lemma 10.2.1: U/S distribute over boolean ops (4 theorems) |
| 6 | `NegationEquiv.lean` | 159 | Lemma 10.2.2: neg_until_equiv, neg_since_equiv (Z-dependent) |
| 7 | `Eliminations.lean` | 902 | Lemma 10.2.3: 8 elimination cases (Cases 1-4 direct, Cases 5-8 referenced) |
| 8 | `NormalForm.lean` | 554 | Lemma 10.2.4: Normal form reduction using 8 cases |
| 9 | `DualEliminations.lean` | 101 | Dual of Lemma 10.2.3 (S out of U), follows from all_formulas_separable |
| 10 | `DedekindZ/QLemma.lean` | 459 | K+/K- operators, Q-lemma, Case 3 equivalence for Z |
| 11 | `DedekindZ/Cases.lean` | 1768 | Cases 5-8 separability proofs via replacement and direct formulas |
| 12 | `TemporalClosure.lean` | 674 | replace_box_with_top, has_no_allpast_allfuture (trivially true), no_U/S_nested predicates |
| 13 | `Hierarchy/HierarchyDefs.lean` | 1051 | has_single_U_type, U/S-formula abstraction, junction-depth monotonicity |
| 14 | `Hierarchy/HierarchyCaseSep.lean` | 655 | Case-specific is_separable_with_U_type theorems |
| 15 | `Hierarchy/HierarchyInduction.lean` | 1437 | Substitution-based induction engine (Steps 1-5b) |
| 16 | `Hierarchy/HierarchyCompletion.lean` | 981 | Steps 5c-5d, all_formulas_separable (main theorem) |
| 17 | `SeparationThm.lean` | 354 | Theorem 10.2.9 wrapper, temporal closure corollaries, atom-preserving separation |

**Total core**: 17 files, ~8,544 lines

### 1.2 Supplementary Files (NOT in barrel, bridge to other modules)

| File | Lines | Dependencies Outside Separation | Status |
|------|-------|---------------------------------|--------|
| `SemanticBridge.lean` | 180 | `WeakCanonical.Table` (MonadicFO) | DEFER -- depends on unported Table/MonadicFO infrastructure |
| `KampTranslation.lean` | 164 | `WeakCanonical.NormalForm`, `WeakCanonical.StaviConnectives` | DEFER -- BLOCKED on n-variable Fraisse game (noted in file) |

**Recommendation**: Exclude SemanticBridge and KampTranslation from this port. They depend on the completeness framework (MonadicFO, Table, StaviConnectives) which is not yet ported, and they are not needed for the core separation theorem.

### 1.3 Barrel File

The barrel file `Separation.lean` (38 lines) imports 13 of the 17 core files directly; the remaining 4 (DedekindZ/QLemma, DedekindZ/Cases, TemporalClosure, HierarchyCaseSep) are transitively imported.

## 2. Dependency Graph

```
Defs ─────────────────────────────────────┐
  ├── FormulaOps                          │
  ├── IntHelpers                          │
  ├── Duality ─────────────────┐          │
  ├── Distributivity           │          │
  ├── NegationEquiv ←── Duality + IntHelpers
  ├── Eliminations ←── NegationEquiv + Distributivity + IntHelpers
  │     └── DedekindZ/QLemma ←── Defs + Eliminations + NegationEquiv
  │           └── DedekindZ/Cases ←── QLemma
  ├── NormalForm ←── Eliminations + Distributivity + DedekindZ/Cases
  ├── TemporalClosure ←── Defs + Duality
  ├── Hierarchy/HierarchyDefs ←── NormalForm + TemporalClosure + DedekindZ/Cases + FormulaOps
  │     └── Hierarchy/HierarchyCaseSep ←── HierarchyDefs
  │           └── Hierarchy/HierarchyInduction ←── HierarchyDefs + HierarchyCaseSep
  │                 └── Hierarchy/HierarchyCompletion ←── HierarchyInduction
  ├── SeparationThm ←── Defs + Eliminations + FormulaOps + Distributivity + Duality + HierarchyCompletion
  └── DualEliminations ←── Eliminations + Duality + SeparationThm
```

### 2.1 Suggested Phase Order (topological)

1. **Phase 1**: Defs (foundation)
2. **Phase 2**: FormulaOps, IntHelpers, Duality, Distributivity (parallel, all depend only on Defs)
3. **Phase 3**: NegationEquiv (depends on Duality + IntHelpers)
4. **Phase 4**: Eliminations (depends on NegationEquiv + Distributivity + IntHelpers)
5. **Phase 5**: DedekindZ/QLemma (depends on Defs + Eliminations + NegationEquiv)
6. **Phase 6**: DedekindZ/Cases (depends on QLemma)
7. **Phase 7**: NormalForm, TemporalClosure (parallel; NormalForm depends on Eliminations + Distributivity + DedekindZ/Cases; TemporalClosure depends on Defs + Duality)
8. **Phase 8**: Hierarchy/HierarchyDefs (depends on NormalForm + TemporalClosure + DedekindZ/Cases + FormulaOps)
9. **Phase 9**: Hierarchy/HierarchyCaseSep (depends on HierarchyDefs)
10. **Phase 10**: Hierarchy/HierarchyInduction (depends on HierarchyDefs + HierarchyCaseSep)
11. **Phase 11**: Hierarchy/HierarchyCompletion (depends on HierarchyInduction)
12. **Phase 12**: SeparationThm, DualEliminations, Barrel (final)

## 3. Porting Challenges

### 3.1 Atom Type Parameterization (HIGH IMPACT)

**Source**: Uses concrete `Bimodal.Syntax.Atom` (struct with `base : String` and `fresh_index : Option Nat`)
**Target**: Uses generic `Atom : Type*` with typeclass constraints

**Impact**: Every definition that mentions `Atom` must be parameterized. Specifically:
- `IntStructure` becomes `IntStructure (Atom : Type*)` with `val : Atom → Set ℤ`
- `int_truth`, `int_equiv`, `is_separable` all gain the `Atom` parameter
- `formula_atoms` uses `Set Atom` in source; cslib has `Formula.atoms` returning `Finset Atom` (requires `[DecidableEq Atom]`)

**Freshness**: The source uses `Atom.mk_fresh_injective` and explicit infinite atom construction. For cslib, we need:
- `variable [DecidableEq Atom] [Infinite Atom]`
- Replace `exists_atom_not_in_finset` with `Infinite.exists_notMem_finset`
- Replace `Atom.mk_fresh_injective` proof with the `Infinite` instance

**Files affected**: Defs.lean, FormulaOps.lean, Duality.lean, SeparationThm.lean, all Hierarchy files

### 3.2 Namespace Remapping (MECHANICAL)

| Source Pattern | Target Pattern |
|----------------|----------------|
| `namespace Bimodal.Metalogic.WeakCanonical.Separation` | `namespace Cslib.Logic.Bimodal.Metalogic.Separation` |
| `open Bimodal.Syntax` | `open Cslib.Logic.Bimodal` |
| `import Bimodal.Syntax.Formula` | `import Cslib.Logics.Bimodal.Syntax.Formula` |
| `import Bimodal.Metalogic.WeakCanonical.Separation.X` | `import Cslib.Logics.Bimodal.Metalogic.Separation.X` |
| `Formula` (unparameterized) | `Formula Atom` (parameterized) |

Note: directory is `Cslib/Logics/` but namespace is `Cslib.Logic.` (the final `s` is dropped in namespace).

### 3.3 Formula.swap_temporal (ALREADY PORTED)

The cslib `Cslib/Logics/Bimodal/Syntax/Formula.lean` already defines:
- `Formula.swap_temporal` with the same semantics
- `swap_temporal_involution`
- `swap_temporal_neg`, `swap_temporal_diamond`
- `swap_temporal_some_future/past`, `swap_temporal_all_future/past`
- `atoms_swap_temporal`

The Duality.lean port can reference these directly via `open Cslib.Logic.Bimodal`.

### 3.4 formula_atoms vs Formula.atoms (MEDIUM)

**Source**: Defs.lean defines `formula_atoms : Formula → Set Atom` (returns `Set`)
**cslib**: `Formula.atoms : Formula Atom → Finset Atom` (returns `Finset`, requires `[DecidableEq Atom]`)

The Separation proof primarily uses `formula_atoms` (Set-based) for semantic arguments. We can either:
1. Define a `formula_atoms` as `Set.range` from `Formula.atoms`, or
2. Define a fresh `formula_atoms` returning `Set Atom` (matching source exactly)
3. Use `↑(φ.atoms) : Set Atom` coercion from Finset

**Recommendation**: Option 2 (define `formula_atoms` locally) since the Set-based version is used heavily in semantic proofs and the Finset version would require unnecessary DecidableEq threading in places where it's not needed.

### 3.5 Mathlib API Version Differences (LOW)

Source uses Lean 4.27.0-rc1, target uses 4.31.0-rc1. Key Mathlib imports:
- `Mathlib.Algebra.Order.Group.Int` -- both versions have this
- `Mathlib.Data.Int.Interval` -- both versions have this

Potential issues: Some `simp` lemma names may have changed between Mathlib versions. This is typically caught at build time and fixable with `exact?` or `simp?`.

### 3.6 `module` Declaration (LOW)

Some cslib files use `module` declarations (line 7), while others don't. The metalogic files (DeductionTheorem, MCSProperties) do NOT use `module`. The separation files should follow the same pattern as the existing metalogic files (no `module` declaration).

### 3.7 Linter Settings (LOW)

Existing cslib metalogic files use:
```lean
set_option linter.style.emptyLine false
set_option linter.flexible false
```
The separation files should include these at the top.

### 3.8 Copyright Header (MECHANICAL)

Every file needs the Apache 2.0 copyright header:
```lean
/-
Copyright (c) 2026 Benjamin Brastmckie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brastmckie
-/
```

### 3.9 No Sorry / No Axiom (VERIFIED CLEAN)

The source files contain:
- **0 sorry** occurrences
- **0 axiom** declarations
- **6 noncomputable** declarations (fresh_atom, fresh_atoms, extract_innermost_U_type, extract_U_type, atom_literal, nf_depth0_char_formula -- last two are in KampTranslation which is excluded)

All proofs are complete and axiom-free.

### 3.10 Large File Strategy

Three files exceed 1000 lines:
- `DedekindZ/Cases.lean` (1768 lines) -- the largest, contains Cases 5-8 proofs
- `Hierarchy/HierarchyInduction.lean` (1437 lines) -- substitution induction engine
- `Hierarchy/HierarchyDefs.lean` (1051 lines) -- hierarchy definitions and monotonicity

These will require careful attention during porting to ensure all proof terms translate correctly with the parameterized Atom type.

## 4. Target Structure Analysis

### 4.1 Existing Bimodal Infrastructure (Available for Import)

| Module | Available API |
|--------|---------------|
| `Cslib.Logics.Bimodal.Syntax.Formula` | `Formula Atom` type, `swap_temporal`, `atoms`, all derived connectives |
| `Cslib.Logics.Bimodal.ProofSystem.*` | Derivation, Axioms, Substitution (atom-to-atom only) |
| `Cslib.Logics.Bimodal.Metalogic.Core.*` | DeductionTheorem, MCS, MCSProperties |
| `Cslib.Logics.Bimodal.Theorems.Perpetuity.*` | Derived theorems (identity, contraposition, etc.) |

### 4.2 What the Separation Module Does NOT Depend On

The separation proof is self-contained w.r.t. the proof system. It does NOT use:
- Derivation/Derivable (no syntactic derivations)
- Axioms (no axiom instances)
- MCS/MaximalConsistent (no Lindenbaum construction)
- Soundness (no frame semantics)

It ONLY needs `Formula` (syntax) and its own `IntStructure`/`int_truth` semantics.

### 4.3 Target File Layout

```
Cslib/Logics/Bimodal/Metalogic/Separation/
├── Defs.lean
├── FormulaOps.lean
├── IntHelpers.lean
├── Duality.lean
├── Distributivity.lean
├── NegationEquiv.lean
├── Eliminations.lean
├── NormalForm.lean
├── DualEliminations.lean
├── DedekindZ/
│   ├── QLemma.lean
│   └── Cases.lean
├── TemporalClosure.lean
├── Hierarchy/
│   ├── HierarchyDefs.lean
│   ├── HierarchyCaseSep.lean
│   ├── HierarchyInduction.lean
│   └── HierarchyCompletion.lean
└── SeparationThm.lean
Cslib/Logics/Bimodal/Metalogic/Separation.lean  (barrel)
```

## 5. Key Definitions to Port

### 5.1 Core Types (Defs.lean)

```lean
structure IntStructure (Atom : Type*) where
  val : Atom → Set ℤ

def int_truth [DecidableEq Atom] (M : IntStructure Atom) (t : ℤ) : Formula Atom → Prop

def int_equiv (φ ψ : Formula Atom) : Prop

def is_U_free : Formula Atom → Bool
def is_S_free : Formula Atom → Bool
def is_syntactically_separated : Formula Atom → Bool
def is_separable (φ : Formula Atom) : Prop
def junction_depth : Formula Atom → Nat  -- (mutual with junction_depth_U, junction_depth_S)
def no_S_nested_in_U : Formula Atom → Prop
```

### 5.2 Main Theorem (SeparationThm.lean)

```lean
theorem all_formulas_separable (phi : Formula Atom) : is_separable phi
-- a.k.a. separation_theorem_int: GHR94 Theorem 10.2.9
```

### 5.3 Freshness Infrastructure (FormulaOps.lean)

```lean
-- Requires [Infinite Atom] [DecidableEq Atom]
noncomputable def fresh_atom (phi : Formula Atom) : Atom
theorem fresh_atom_not_in (phi : Formula Atom) : fresh_atom phi ∉ phi.atoms
```

## 6. Risk Assessment

| Risk | Severity | Mitigation |
|------|----------|------------|
| Atom parameterization cascading through all files | Medium | Systematic: add `variable {Atom : Type*}` everywhere |
| Freshness requiring `[Infinite Atom]` constraint | Low | Use `Infinite.exists_notMem_finset` from Mathlib |
| Mathlib API changes between v4.27 and v4.31 | Low | Fix at build time with `exact?`/`simp?` |
| Large files (1000+ lines) causing timeout | Medium | Port in smaller chunks within phases |
| `formula_atoms` (Set) vs `atoms` (Finset) mismatch | Low | Define local `formula_atoms` returning `Set Atom` |
| `open Classical` usage throughout | Low | cslib already uses `attribute [local instance] Classical.propDecidable` |

## 7. Excluded Files Justification

### SemanticBridge.lean
Depends on `WeakCanonical.Table` which imports `WeakCanonical.MonadicFO`. These define `MonadicSignature`, `ZStructure`, `OrderedMonadicStructure`, `temporal_truth` -- none of which are ported to cslib. This file bridges the separation framework to the completeness framework, which is a separate porting effort.

### KampTranslation.lean
- Depends on `WeakCanonical.NormalForm` (MonadicFO normal form theory) and `WeakCanonical.StaviConnectives`
- Explicitly marked as BLOCKED on the n-variable Fraisse game argument in its own documentation
- Not part of the core separation theorem proof

## 8. Summary

The separation theorem port involves 17 core files totaling ~8,544 lines (plus a barrel file). The proof is self-contained, complete (no sorry, no axioms), and depends only on the Formula syntax type and Mathlib integer arithmetic. The main porting challenge is the systematic Atom type parameterization from a concrete `Atom` struct to a generic `Atom : Type*` with `[Infinite Atom]` and `[DecidableEq Atom]` constraints. Two supplementary files (SemanticBridge, KampTranslation) should be deferred as they depend on unported completeness infrastructure.
