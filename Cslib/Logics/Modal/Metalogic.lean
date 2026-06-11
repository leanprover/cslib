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
public import Cslib.Logics.Modal.Metalogic.DSoundness
public import Cslib.Logics.Modal.Metalogic.DCompleteness
public import Cslib.Logics.Modal.Metalogic.S4Soundness
public import Cslib.Logics.Modal.Metalogic.S4Completeness
public import Cslib.Logics.Modal.Metalogic.K4Soundness
public import Cslib.Logics.Modal.Metalogic.K4Completeness
public import Cslib.Logics.Modal.Metalogic.BSoundness
public import Cslib.Logics.Modal.Metalogic.BCompleteness
public import Cslib.Logics.Modal.Metalogic.K45Soundness
public import Cslib.Logics.Modal.Metalogic.K45Completeness
public import Cslib.Logics.Modal.Metalogic.K5Soundness
public import Cslib.Logics.Modal.Metalogic.K5Completeness
public import Cslib.Logics.Modal.Metalogic.D4Soundness
public import Cslib.Logics.Modal.Metalogic.D4Completeness
public import Cslib.Logics.Modal.ProofSystem.Instances

/-! # Modal Metalogic Module

Module aggregator for modal metalogic: syntactic proof system,
deduction theorem, maximal consistent sets, soundness, and completeness
for K, T, D, B, K4, K5, K45, D4, S4, and S5. Includes typeclass instance registration for all
modal systems.
-/

@[expose] public section

