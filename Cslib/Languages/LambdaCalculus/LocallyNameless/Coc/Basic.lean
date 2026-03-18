/-
Copyright (c) 2026 Matt Hunzinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matt Hunzinger
-/

module

public import Cslib.Foundations.Data.HasFresh
public import Cslib.Languages.LambdaCalculus.LocallyNameless.Context

@[expose] public section

/-! # Calculus of Constructions

The Calculus of Constructions

## References

* [T. Coquand, *An algorithm for type-checking dependent types*][Coquand1996]

* [A. Chargueraud, *The Locally Nameless Representation*][Chargueraud2012]

-/

namespace Cslib

universe u

namespace LambdaCalculus.LocallyNameless.Coc

/-- Syntax of locally nameless terms, with free variables over `Var`. -/
inductive Term (Var : Type u) : Type u
  /-- Bound term variables using a de-Bruijn index. -/
  | bvar : ℕ → Term Var
  /-- Free term variables. -/
  | fvar : Var → Term Var
  /-- Function application. -/
  | app : Term Var → Term Var → Term Var
  /-- Lambda abstraction. -/
  | abs : Term Var → Term Var → Term Var
  /-- Pi type. -/
  | pi : Term Var → Term Var → Term Var
  /-- Type universe. -/
  | type : ℕ → Term Var
deriving DecidableEq

/-- Free variables. -/
@[scoped grind =]
def Term.fv [DecidableEq Var] : Term Var → Finset Var
  | .bvar _ => ∅
  | .fvar z => {z}
  | .app f a => f.fv ∪ a.fv
  | .abs t b => t.fv ∪ b.fv
  | .pi t b => t.fv ∪ b.fv
  | .type _ => ∅

abbrev Env (Var : Type u) := Context Var (Term Var)

end LambdaCalculus.LocallyNameless.Coc

end Cslib
