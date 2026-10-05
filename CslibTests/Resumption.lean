/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

import Cslib.Foundations.Data.PFunctor.Resumption

/-! Tests for coinductive resumptions. -/

namespace CslibTests.Resumption

open PFunctor

private def flips : (y^ Bool).FreeM Bool := do
  let b ← FreeM.lift ()
  let c ← FreeM.lift ()
  pure (b && !c)

-- Embedding a `do` program, which uses `>>=` and `<$>` rather than the universe-polymorphic
-- `bind` and `map`, gives the same program over resumptions.
example : flips.toResumption = (do
    let b ← Resumption.lift ()
    let c ← Resumption.lift ()
    pure (b && !c)) := by
  simp [flips]

end CslibTests.Resumption
