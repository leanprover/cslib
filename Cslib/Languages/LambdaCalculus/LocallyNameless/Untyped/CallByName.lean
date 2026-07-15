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

variable {M M' N N' : Term Var}

/-- The left side of a Call-by-Name step is locally closed. -/
lemma CBN.lc_l (step : M ⭢ₙ N) : LC M := by
  induction step with grind

/-- A single Call-by-Name step is a full β-reduction. -/
lemma CBN.step_to_redex (step : M ⭢ₙ N) : M ↠βᶠ N := by
  induction step with
  | base h => exact .single (.base h)
  | app lc_Z _ ih => exact FullBeta.redex_app_l_cong ih lc_Z

/-- Call-by-Name reduction is contained in full β-reduction. -/
lemma CBN.to_redex (step : M ↠ₙ N) : M ↠βᶠ N := by
  induction step
  · rfl
  · grind [CBN.step_to_redex, Relation.ReflTransGen.trans]

/-- Left congruence rule for application in Call-by-Name reduction. -/
lemma CBN.steps_app_l_cong (step : M ↠ₙ M') (lc_N : LC N) : Term.app M N ↠ₙ Term.app M' N := by
  induction step
  · rfl
  · grind [CBN.app]

variable [HasFresh Var] [DecidableEq Var]

/-- The right side of a Call-by-Name step is locally closed. -/
lemma CBN.lc_r (step : M ⭢ₙ N) : LC N := by
  induction step with grind

/-- The right side of a Call-by-Name reduction is locally closed. -/
lemma CBN.steps_lc_r (lc_M : LC M) (step : M ↠ₙ N) : LC N := by
  induction step
  · exact lc_M
  · grind [CBN.lc_r]

/-- Substitution preserves a single Call-by-Name step. -/
lemma CBN.step_subst (x : Var) (h : M ⭢ₙ M') (lc_N : LC N) :
    M[x := N] ⭢ₙ M'[x := N] := by
  induction h
  · grind [Term.subst_open, CBN.base]
  · grind [CBN.app]

/-- Substitution preserves Call-by-Name reduction. -/
lemma CBN.steps_subst (x : Var) (step : M ↠ₙ M') (lc_N : LC N) :
    M[x := N] ↠ₙ M'[x := N] := by
  induction step
  · rfl
  · grind [CBN.step_subst]

end LambdaCalculus.LocallyNameless.Untyped.Term

end Cslib
