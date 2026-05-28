/-
Copyright (c) 2026 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi, Thomas Waring
-/

module

public import Cslib.Init

/-! # Iff connective (↔) -/

@[expose] public section

namespace Cslib.Logic

/-- The type `α` has a bi-implication connective (`↔`). -/
class HasIff (α : Type*) where
  /-- `a ↔ b` denotes `a` implies `b` and vice-versa. -/
  iff (a b : α) : α

@[inherit_doc] scoped infixr:20 " ↔ " => HasIff.iff

end Cslib.Logic
