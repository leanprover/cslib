/-
Copyright (c) 2026 Maximiliano Onofre Martínez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maximiliano Onofre Martínez
-/

module

public import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.FullBeta
public import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.Properties

/-! # Call-by-Name Evaluation -/

@[expose] public section

set_option linter.unusedDecidableInType false

namespace Cslib

universe u

variable {Var : Type u}

namespace LambdaCalculus.LocallyNameless.Untyped.Term

/-- A single step of Call-by-Name evaluation. -/
@[reduction_sys "ₙ"]
inductive CBN : Term Var → Term Var → Prop
/-- Top-level β-reduction. -/
| base : Beta M N → CBN M N
/-- Evaluates the leftmost term. -/
| app : LC Z → CBN M N → CBN (app M Z) (app N Z)

variable {M N : Term Var}

/-- The left side of a CBN reduction step is locally closed. -/
lemma cbn_lc_l (step : M ⭢ₙ N) : LC M := by
  induction step
  all_goals grind
  induction step with grind
variable [HasFresh Var] [DecidableEq Var]

/-- The right side of a CBN reduction step is locally closed. -/
lemma cbn_lc_r (step : M ⭢ₙ N) : LC N := by
  induction step
  case base beta_step =>
    cases beta_step
    apply beta_lc <;> assumption
  case app lc_z _ lc_n => exact LC.app lc_n lc_z

end LambdaCalculus.LocallyNameless.Untyped.Term

end Cslib
