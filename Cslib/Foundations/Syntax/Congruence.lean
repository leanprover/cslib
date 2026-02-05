/-
Copyright (c) 2026 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi
-/

module

public import Cslib.Foundations.Syntax.Context
public import Mathlib.Algebra.Order.Monoid.Unbundled.Defs

@[expose] public section

namespace Cslib

/-- An equivalence relation preserved by all contexts. -/
class Congruence (α : Type*) [HasContext α] (r : α → α → Prop) extends
  IsEquiv α r, covariant : CovariantClass (HasContext.Context α) α (·[·]) r

end Cslib
