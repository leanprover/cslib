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
public import Cslib.Logics.Modal.Metalogic.Systems.S5.Soundness
public import Cslib.Logics.Modal.Metalogic.Systems.S5.Completeness
public import Cslib.Logics.Modal.Metalogic.Systems.K.Soundness
public import Cslib.Logics.Modal.Metalogic.Systems.K.Completeness
public import Cslib.Logics.Modal.Metalogic.Systems.T.Soundness
public import Cslib.Logics.Modal.Metalogic.Systems.T.Completeness
public import Cslib.Logics.Modal.Metalogic.Systems.D.Soundness
public import Cslib.Logics.Modal.Metalogic.Systems.D.Completeness
public import Cslib.Logics.Modal.Metalogic.Systems.S4.Soundness
public import Cslib.Logics.Modal.Metalogic.Systems.S4.Completeness
public import Cslib.Logics.Modal.Metalogic.Systems.K4.Soundness
public import Cslib.Logics.Modal.Metalogic.Systems.K4.Completeness
public import Cslib.Logics.Modal.Metalogic.Systems.B.Soundness
public import Cslib.Logics.Modal.Metalogic.Systems.B.Completeness
public import Cslib.Logics.Modal.Metalogic.Systems.K45.Soundness
public import Cslib.Logics.Modal.Metalogic.Systems.K45.Completeness
public import Cslib.Logics.Modal.Metalogic.Systems.K5.Soundness
public import Cslib.Logics.Modal.Metalogic.Systems.K5.Completeness
public import Cslib.Logics.Modal.Metalogic.Systems.D4.Soundness
public import Cslib.Logics.Modal.Metalogic.Systems.D4.Completeness
public import Cslib.Logics.Modal.Metalogic.Systems.KB5.Soundness
public import Cslib.Logics.Modal.Metalogic.Systems.KB5.Completeness
public import Cslib.Logics.Modal.Metalogic.Systems.TB.Soundness
public import Cslib.Logics.Modal.Metalogic.Systems.TB.Completeness
public import Cslib.Logics.Modal.Metalogic.Systems.D45.Soundness
public import Cslib.Logics.Modal.Metalogic.Systems.D45.Completeness
public import Cslib.Logics.Modal.Metalogic.Systems.D5.Soundness
public import Cslib.Logics.Modal.Metalogic.Systems.D5.Completeness
public import Cslib.Logics.Modal.Metalogic.Systems.DB.Soundness
public import Cslib.Logics.Modal.Metalogic.Systems.DB.Completeness
public import Cslib.Logics.Modal.ProofSystem.Instances

/-! # Modal Metalogic Module

Module aggregator for modal metalogic: syntactic proof system,
deduction theorem, maximal consistent sets, soundness, and completeness
for K, T, D, B, K4, K5, K45, D4, D45, D5, DB, KB5, TB, S4, and S5. Includes typeclass
instance registration for all modal systems.
-/

@[expose] public section

