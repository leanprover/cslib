/-
Copyright (c) 2026 Maximiliano Onofre Martínez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maximiliano Onofre Martínez
-/

module

public import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.Properties

/-! # Congruence for the λ-calculus -/

public section

namespace Cslib

universe u

variable {Var : Type u}

namespace LambdaCalculus.LocallyNameless.Untyped.Term

/-- Congruence closure of a relation. -/
inductive Xi (R : Term Var → Term Var → Prop) : Term Var → Term Var → Prop
/-- The base relation. -/
| base : R M N → Xi R M N
/-- Left congruence rule for application. -/
| appL: LC Z → Xi R M N → Xi R (app Z M) (app Z N)
/-- Right congruence rule for application. -/
| appR : LC Z → Xi R M N → Xi R (app M Z) (app N Z)
/-- The ξ (xi) rule for lambda terms. -/
| abs (xs : Finset Var) : (∀ x ∉ xs, Xi R (M ^ fvar x) (N ^ fvar x)) → Xi R (abs M) (abs N)

attribute [scoped grind .] Xi.appL Xi.appR Xi.base

namespace Xi

variable {R : Term Var → Term Var → Prop} {M N : Term Var}

/-- The right side of a congruence step is locally closed. -/
@[scoped grind →]
lemma step_lc_r (hR : ∀ {M' N'}, R M' N' → LC N') (step : Xi R M N) : LC N := by
  induction step with
  | base h => exact hR h
  | abs xs _ ih =>
    constructor
    exact ih
  | _ => grind

/-- The left side of a congruence step is locally closed. -/
lemma step_lc_l (hR : ∀ {M' N'}, R M' N' → LC M') (step : Xi R M N) : LC M := by
  induction step with
  | base h => exact hR h
  | appL lc_Z _ ih => exact LC.app lc_Z ih
  | appR lc_Z _ ih => exact LC.app ih lc_Z
  | abs xs _ ih => exact LC.abs xs _ ih

end Xi

end LambdaCalculus.LocallyNameless.Untyped.Term

end Cslib
