/-
Copyright (c) 2026 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi, Thomas Waring
-/

module

public import Cslib.Init

/-! # Or connective (∨) -/

@[expose] public section

namespace Cslib.Logic

/-- The type `α` has an or connective (`∨`). -/
class HasOr (α : Type*) where
  /-- `a ∨ b` is the disjunction of `a` and `b`. -/
  or (a b : α) : α

@[inherit_doc] scoped infixr:30 " ∨ " => HasOr.or

end Cslib.Logic
