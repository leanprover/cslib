/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Bimodal.Metalogic.Core.DerivationTree
public import Cslib.Logics.Bimodal.Metalogic.Core.DeductionTheorem
public import Cslib.Logics.Bimodal.Metalogic.Core.MaximalConsistent
public import Cslib.Logics.Bimodal.Metalogic.Core.MCSProperties
public import Cslib.Logics.Bimodal.Metalogic.Core.RestrictedMCS

/-!
# Bimodal Metalogic Core -- Barrel Import

This module re-exports the core metalogic infrastructure for bimodal logic:
- DerivationTree: Prop-level wrapper and DerivationSystem instance
- DeductionTheorem: The deduction theorem for the 7-constructor DerivationTree
- MaximalConsistent: List-based and set-based MCS definitions, Lindenbaum's lemma
- MCSProperties: Set-based MCS closure, temporal 4 properties, consistency lemmas
-/
