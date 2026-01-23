/-
Copyright (c) 2025 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi
-/

module

public import Cslib.Init

public section

namespace Cslib

/-- Typeclass for substitution relations and access to their notation. -/
class HasSubstitution (α : Type u) (β : Type v) (γ : Type w) where
  /-- Substitution function. Replaces `x` in `t` with `t'`. -/
  subst (t : α) (x : β) (t' : γ) : α

/-- Notation for substitution. -/
notation t:max "[" x ":=" t' "]" => HasSubstitution.subst t x t'

end Cslib
