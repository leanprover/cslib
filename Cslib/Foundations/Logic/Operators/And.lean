/-
Copyright (c) 2026 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi
-/

module

public import Cslib.Init

/-! # And connective (∧) -/

@[expose] public section

namespace Cslib.Logic

/-- The type `α` has an and connective (`∧`). -/
class HasAnd (α : Type*) where
  /-- `a ∧ b` is the conjunction of `a` and `b`. -/
  and (a b : α) : α

@[inherit_doc] scoped infixr:36 " ∧ " => HasAnd.and

end Cslib.Logic
