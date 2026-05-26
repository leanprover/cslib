/-
Copyright (c) 2026 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi, Thomas Waring
-/

module

public import Cslib.Init

/-! # Impl connective (→) -/

@[expose] public section

namespace Cslib.Logic

/-- The type `α` has an implication connective (`→`). -/
class HasImpl (α : Type*) where
  /-- `a → b` denotes `a` implies `b`. -/
  impl (a b : α) : α

@[inherit_doc] scoped infixr:25 " → " => HasImpl.impl

end Cslib.Logic
