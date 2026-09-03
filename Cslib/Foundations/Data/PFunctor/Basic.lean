/-
Copyright (c) 2026 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi
-/

module

public import Mathlib.Data.PFunctor.Univariate.Basic

/-! # Additional basic definitions on polynomial functors -/

@[expose] public section

namespace PFunctor

section Unary

/-- A polynomial functor is unary if all child types have exactly one element. -/
class Unary (P : PFunctor) where
  unary (a : P.A) : Unique (P.B a)

attribute [instance_reducible, instance] PFunctor.Unary.unary

theorem Unary.fun_eq_const [Unary P]
    (a : P.A) (f : P.B a → α) : f = fun _ => f default := by
  funext i
  exact congrArg f (Subsingleton.elim i default)

/-- A polynomial functor has children with decidable equality. -/
class DecidableEqChildren (P : PFunctor) where
  decidableEq (a : P.A) : DecidableEq (P.B a)

attribute [instance_reducible, instance] DecidableEqChildren.decidableEq

/-- A unary polynomial functor has decidable child equality. -/
instance (P : PFunctor) [P.Unary] : P.DecidableEqChildren where
  decidableEq _ _ _ := isTrue (Subsingleton.elim _ _)

end Unary

end PFunctor
