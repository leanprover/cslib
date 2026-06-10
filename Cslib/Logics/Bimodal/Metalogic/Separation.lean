/-
Copyright (c) 2025 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Bimodal.Metalogic.Separation.Defs
public import Cslib.Logics.Bimodal.Metalogic.Separation.FormulaOps
public import Cslib.Logics.Bimodal.Metalogic.Separation.IntHelpers
public import Cslib.Logics.Bimodal.Metalogic.Separation.Duality
public import Cslib.Logics.Bimodal.Metalogic.Separation.Distributivity
public import Cslib.Logics.Bimodal.Metalogic.Separation.NegationEquiv
public import Cslib.Logics.Bimodal.Metalogic.Separation.Eliminations
public import Cslib.Logics.Bimodal.Metalogic.Separation.NormalForm
public import Cslib.Logics.Bimodal.Metalogic.Separation.TemporalClosure
public import Cslib.Logics.Bimodal.Metalogic.Separation.Hierarchy.HierarchyDefs
public import Cslib.Logics.Bimodal.Metalogic.Separation.Hierarchy.HierarchyCaseSep
public import Cslib.Logics.Bimodal.Metalogic.Separation.Hierarchy.HierarchyInduction
public import Cslib.Logics.Bimodal.Metalogic.Separation.Hierarchy.HierarchyCompletion
public import Cslib.Logics.Bimodal.Metalogic.Separation.SeparationThm
public import Cslib.Logics.Bimodal.Metalogic.Separation.DualEliminations

/-!
# Separation Theorem (Barrel Import)

This file re-exports all modules comprising the separation theorem
proof for bimodal temporal logic over integer time (GHR94 Chapter 10.2).

## Main Results

- `all_formulas_separable`: Every formula is separable (GHR94 Theorem 10.2.9)
- `all_formulas_properly_separable`: Every formula is properly separable
- `proper_separation_preserves_atoms`: Atom-preserving separation

## References

- GHR94, Chapter 10, Section 10.2 (pp. 569-592)
-/

@[expose] public section

