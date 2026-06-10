/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Bimodal.Metalogic.Soundness.Soundness
public import Cslib.Logics.Bimodal.Semantics.Validity

/-!
# Discrete Soundness - Soundness of Discrete-Compatible Axioms

Thin wrapper re-exporting discrete soundness results.
-/

@[expose] public section

namespace Cslib.Logic.Bimodal.Metalogic.DiscreteSoundness

open Cslib.Logic.Bimodal

variable {Atom : Type*}

/-- All axioms with `minFrameClass ≤ .Discrete` are valid over discrete temporal orders. -/
theorem axiom_discrete_valid' {φ : Formula Atom} (h : Axiom φ)
    (h_fc : h.minFrameClass ≤ FrameClass.Discrete) :
    valid_discrete φ :=
  axiom_discrete_valid h h_fc

end Cslib.Logic.Bimodal.Metalogic.DiscreteSoundness
