/-
Copyright (c) 2026 Benjamin Brastmckie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brastmckie
-/
import Cslib.Logics.Bimodal.Metalogic.Soundness.Soundness
import Cslib.Logics.Bimodal.Semantics.Validity

/-!
# Dense Soundness - Soundness of Dense-Compatible Axioms

Thin wrapper re-exporting dense soundness results.
-/

namespace Cslib.Logic.Bimodal.Metalogic.DenseSoundness

open Cslib.Logic.Bimodal

variable {Atom : Type*}

/-- The density axiom GGφ → Gφ is valid over all densely ordered temporal types. -/
theorem density_sound_dense (φ : Formula Atom) :
    valid_dense ((φ.all_future.all_future).imp φ.all_future) :=
  density_valid φ

/-- All axioms with `minFrameClass ≤ .Dense` are valid over dense temporal orders. -/
theorem axiom_dense_valid' {φ : Formula Atom} (h : Axiom φ) (h_fc : h.minFrameClass ≤ FrameClass.Dense) :
    valid_dense φ :=
  axiom_dense_valid h h_fc

end Cslib.Logic.Bimodal.Metalogic.DenseSoundness
