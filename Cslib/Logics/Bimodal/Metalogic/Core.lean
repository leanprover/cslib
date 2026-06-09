/-
Copyright (c) 2026 Benjamin Brastmckie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brastmckie
-/

import Cslib.Logics.Bimodal.Metalogic.Core.DerivationTree
import Cslib.Logics.Bimodal.Metalogic.Core.DeductionTheorem
import Cslib.Logics.Bimodal.Metalogic.Core.MaximalConsistent
import Cslib.Logics.Bimodal.Metalogic.Core.MCSProperties

/-!
# Bimodal Metalogic Core -- Barrel Import

This module re-exports the core metalogic infrastructure for bimodal logic:
- DerivationTree: Prop-level wrapper and DerivationSystem instance
- DeductionTheorem: The deduction theorem for the 7-constructor DerivationTree
- MaximalConsistent: List-based and set-based MCS definitions, Lindenbaum's lemma
- MCSProperties: Set-based MCS closure, temporal 4 properties, consistency lemmas
-/
