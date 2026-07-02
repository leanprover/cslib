/-
Copyright (c) 2026 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi
-/

module

public import Cslib.Init

/-! # Negation connective (¬) -/

@[expose] public section

namespace Cslib.Logic

/-- The type `α` has a negation connective (`¬`). -/
class HasNot (α : Type*) where
  /-- `¬a` is the negation of `a`. -/
  not (a : α) : α

@[inherit_doc] scoped notation:max "¬" p:40 => HasNot.not p

end Cslib.Logic
