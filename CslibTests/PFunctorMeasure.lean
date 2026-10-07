/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

import Cslib.Foundations.Data.PFunctor.Resumption.Measure

/-! Tests for output measures of polynomial programs. -/

namespace CslibTests.PFunctorMeasure

open PFunctor MeasureTheory

private def flips : (y^Bool).FreeM Bool := do
  let b ← FreeM.lift ()
  let c ← FreeM.lift ()
  pure (b && !c)

variable (μ : (a : (y^Bool).A) → Measure ((y^Bool).B a))

-- The output measure of a `do` program, which uses `>>=` and `<$>` rather than the
-- universe-polymorphic `bind` and `map`, unfolds to Giry binds of the response measures.
example : flips.toMeasure μ = (μ ()).bind fun b => (μ ()).map fun c => b && !c := by
  simp [flips]

-- Sequencing programs without unfolding them composes their output measures.
example : (do let b ← flips; let c ← flips; pure (b && c)).toMeasure μ =
    (flips.toMeasure μ).bind fun b => (flips.toMeasure μ).map fun c => b && c := by
  simp

end CslibTests.PFunctorMeasure
