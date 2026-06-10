/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

import Cslib.Logics.Bimodal.Metalogic.Core.MCSProperties
import Cslib.Logics.Bimodal.Syntax.Formula

/-!
# FMCS: Family of Maximal Consistent Sets

Defines the `FMCS` (Family of Maximal Consistent Sets) structure that assigns
an MCS to each time point, with temporal coherence conditions.

## References

* Ported from BimodalLogic/Theories/Bimodal/Metalogic/Bundle/FMCSDef.lean
-/

set_option linter.style.emptyLine false
set_option linter.style.longLine false

namespace Cslib.Logic.Bimodal.Metalogic.Bundle

open Cslib.Logic.Bimodal
open Cslib.Logic.Bimodal.Metalogic.Core

variable {Atom : Type*}

/--
A family of maximal consistent sets indexed by time, with temporal coherence.

- `D`: Duration/time type with preorder structure
- `fc`: Frame class (default Base)
- `mcs`: Function assigning an MCS to each time point
- `is_mcs`: Proof that each assigned set is maximal consistent
- `forward_G`: G formulas propagate to strictly future times (t < t')
- `backward_H`: H formulas propagate to strictly past times (t' < t)
-/
structure FMCS (Atom : Type*) (D : Type*) [Preorder D] (fc : FrameClass := FrameClass.Base) where
  mcs : D → Set (Formula Atom)
  is_mcs : ∀ t, SetMaximalConsistent fc (mcs t)
  forward_G : ∀ t t' phi, t < t' → Formula.all_future phi ∈ mcs t → phi ∈ mcs t'
  backward_H : ∀ t t' phi, t' < t → Formula.all_past phi ∈ mcs t → phi ∈ mcs t'

end Cslib.Logic.Bimodal.Metalogic.Bundle
