/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Modal.Metalogic.DerivationTree
public import Cslib.Logics.Modal.Metalogic.DeductionTheorem
public import Cslib.Logics.Modal.Metalogic.MCS
public import Cslib.Logics.Modal.Metalogic.Soundness
public import Cslib.Logics.Modal.Metalogic.Completeness
public import Cslib.Logics.Modal.Metalogic.KSoundness
public import Cslib.Logics.Modal.Metalogic.KCompleteness
public import Cslib.Logics.Modal.Metalogic.TSoundness
public import Cslib.Logics.Modal.Metalogic.TCompleteness
public import Cslib.Logics.Modal.ProofSystem.Instances

/-! # Modal Metalogic Module

Module aggregator for modal metalogic: syntactic proof system,
deduction theorem, maximal consistent sets, soundness, and completeness
for K, T, and S5. Includes typeclass instance registration for all five
modal systems (K, T, D, S4, S5).
-/

@[expose] public section

