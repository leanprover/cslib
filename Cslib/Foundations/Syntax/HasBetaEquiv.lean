/-
Copyright (c) 2026 Matt Hunzinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matt Hunzinger
-/

module

public import Cslib.Init

public section

namespace Cslib

/-- Typeclass for the β-equivalence notation `x =β y`. -/
class HasBetaEquiv (α : Type u) where
  /-- β-equivalence relation for type α. -/
  BetaEquiv : α → α → Prop

@[inherit_doc]
notation m:max " =β " n:max => HasBetaEquiv.BetaEquiv m n

end Cslib
