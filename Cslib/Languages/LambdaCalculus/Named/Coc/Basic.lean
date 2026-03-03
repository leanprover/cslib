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

namespace Term

/-- Renaming, or variable substitution. `m.rename x y` renames `x` into `y` in `m`. -/
def rename [DecidableEq Var] (m : Term Var) (x : Var) (y : Var) : Term Var := match m with
  | .var z => if z = x then .var y else .var z
  | .app f a => .app (f.rename x y) (a.rename x y)
  | .lam v t b => .lam v (t.rename x y) (b.rename x y)
  | .pi v t b => .pi v (t.rename x y) (b.rename x y)
  | .type => .type

/-- Renaming preserves size. -/
theorem rename.eq_sizeOf {m : Term Var} {x y : Var} [DecidableEq Var] :
    sizeOf (m.rename x y) = sizeOf m := by
  induction m <;> simp_all [Term.rename] ; split <;> simp_all

end Term

end LambdaCalculus.Named.Coc

end Cslib
