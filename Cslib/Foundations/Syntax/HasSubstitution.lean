/-
Copyright (c) 2025 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi
-/

module

public import Cslib.Init

/-! Notation typeclass for substitution. -/

public section

namespace Cslib

/-- Typeclass for substitution relations and access to their notation. -/
class HasSubstitution (α : Type u) (β : Type v) (γ : Type w) where
  /-- Substitution function. Replaces `x` in `t` with `t'`. -/
  subst (t : α) (x : β) (t' : γ) : α

/--
Notation for substitution.

The `noWs` guard is intentional: substitution must be written as `t[x := s]`,
not `t [x := s]`. Without the guard, the term parser can attach a bracket from
following syntax, such as an instance-binder field in a structure declaration,
to the preceding term.
-/
syntax:max term noWs "[" term " := " term "]" : term

macro_rules
  | `($t[$x := $s]) => `(HasSubstitution.subst $t $x $s)

/-- Pretty-printer support for `HasSubstitution.subst`. -/
@[app_unexpander HasSubstitution.subst]
meta def unexpandHasSubstitutionSubst : Lean.PrettyPrinter.Unexpander
  | `($_ $t $x $s) => `($t[$x := $s])
  | _ => throw ()

end Cslib
