/-
Copyright (c) 2025 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi
-/

module

public import Cslib.Init

/-! Notation typeclass for well-formedness. -/

public section

namespace Cslib

/-- Typeclass for types equipped with a well-formedness predicate. -/
class HasWellFormed (α : Type u) where
  /-- Establishes whether `x` is well-formed. -/
  wf (x : α) : Prop

/-- Notation for well-formedness. -/
macro x:term:max noWs "✓" : term => `(HasWellFormed.wf $x)

end Cslib
