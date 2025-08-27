/-
Copyright (c) 2025 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi
-/

/-- Typeclass for types equipped with a well-formedness predicate. -/
class HasWellFormed (α : Type _) where
  /-- Establishes whether `x` is well-formed. -/
  wf (x : α) : Prop

/-- Notation for well-formedness. -/
notation x:max "✓" => HasWellFormed.wf x
