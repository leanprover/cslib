/-
Copyright (c) 2025 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

import Cslib.Logics.Bimodal.Metalogic.Separation.Defs
import Cslib.Logics.Bimodal.Metalogic.Separation.FormulaOps
import Cslib.Logics.Bimodal.Metalogic.Separation.IntHelpers
import Cslib.Logics.Bimodal.Metalogic.Separation.Duality
import Cslib.Logics.Bimodal.Metalogic.Separation.Distributivity
import Cslib.Logics.Bimodal.Metalogic.Separation.NegationEquiv
import Cslib.Logics.Bimodal.Metalogic.Separation.Eliminations
import Cslib.Logics.Bimodal.Metalogic.Separation.NormalForm
import Cslib.Logics.Bimodal.Metalogic.Separation.TemporalClosure
import Cslib.Logics.Bimodal.Metalogic.Separation.Hierarchy.HierarchyDefs
import Cslib.Logics.Bimodal.Metalogic.Separation.Hierarchy.HierarchyCaseSep
import Cslib.Logics.Bimodal.Metalogic.Separation.Hierarchy.HierarchyInduction
import Cslib.Logics.Bimodal.Metalogic.Separation.Hierarchy.HierarchyCompletion
import Cslib.Logics.Bimodal.Metalogic.Separation.SeparationThm
import Cslib.Logics.Bimodal.Metalogic.Separation.DualEliminations

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
