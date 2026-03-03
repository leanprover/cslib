/-
Copyright (c) 2026 Matt Hunzinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matt Hunzinger
-/

module

public import Cslib.Foundations.Data.HasFresh
public import Cslib.Foundations.Syntax.HasAlphaEquiv
public import Cslib.Foundations.Syntax.HasSubstitution

@[expose] public section

/-! # Calculus of Constructions

The Calculus of Constructions

## References

* [T. Coquand, *An algorithm for type-checking dependent types*][Coquand1996]

-/

namespace Cslib

universe u

variable {Var : Type u}

namespace LambdaCalculus.Named.Coc

/-- Syntax of terms. -/
inductive Term (Var : Type u) : Type u
  | var : Var → Term Var
  | app : Term Var → Term Var → Term Var
  | lam : Var → Term Var → Term Var → Term Var
  | pi : Var → Term Var → Term Var → Term Var
  | type : Term Var
deriving DecidableEq

end LambdaCalculus.Named.Coc

end Cslib
