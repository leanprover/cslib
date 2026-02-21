/-
Copyright (c) 2025 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public meta import Cslib.Foundations.Data.Relation
public import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.Properties

public section

set_option linter.unusedDecidableInType false

/-! # β-reduction for the λ-calculus

## References

* [A. Chargueraud, *The Locally Nameless Representation*] [Chargueraud2012]
* See also https://www.cis.upenn.edu/~plclub/popl08-tutorial/code/, from which
  this is partially adapted

-/

namespace Cslib

universe u

variable {Var : Type u}

namespace LambdaCalculus.LocallyNameless.Untyped.Term

/-- A single β-reduction step. -/
@[reduction_sys "βᶠ"]
inductive FullBeta : Term Var → Term Var → Prop
/-- Reduce an application to a lambda term. -/
| beta : LC (abs M)→ LC N → FullBeta (app (abs M) N) (M ^ N)
/-- Left congruence rule for application. -/
| appL: LC Z → FullBeta M N → FullBeta (app Z M) (app Z N)
/-- Right congruence rule for application. -/
| appR : LC Z → FullBeta M N → FullBeta (app M Z) (app N Z)
/-- Congruence rule for lambda terms. -/
| abs (xs : Finset Var) : (∀ x ∉ xs, FullBeta (M ^ fvar x) (N ^ fvar x)) → FullBeta (abs M) (abs N)

namespace FullBeta

attribute [scoped grind .] appL appR

variable {M M' N N' : Term Var}

/-- The left side of a reduction is locally closed. -/
@[scoped grind →]
lemma step_lc_l (step : M ⭢βᶠ M') : LC M := by
  induction step <;> constructor
  all_goals assumption

/-- Left congruence rule for application in multiple reduction. -/
@[scoped grind ←]
theorem redex_app_l_cong (redex : M ↠βᶠ M') (lc_N : LC N) : app M N ↠βᶠ app M' N := by
  induction redex <;> grind

/-- Right congruence rule for application in multiple reduction. -/
@[scoped grind ←]
theorem redex_app_r_cong (redex : M ↠βᶠ M') (lc_N : LC N) : app N M ↠βᶠ app N M' := by
  induction redex <;> grind

variable [HasFresh Var] [DecidableEq Var]

/-- The right side of a reduction is locally closed. -/
@[scoped grind →]
lemma step_lc_r (step : M ⭢βᶠ M') : LC M' := by
  induction step
  case' abs => constructor; assumption
  all_goals grind

/-- Substitution respects a single reduction step. -/
lemma redex_subst_cong (s s' : Term Var) (x y : Var) (step : s ⭢βᶠ s') :
    s [ x := fvar y ] ⭢βᶠ s' [ x := fvar y ] := by
  induction step
  case beta m n abs_lc n_lc =>
    cases abs_lc with | abs xs _ mem =>
      rw [subst_open x (fvar y) n m (by grind)]
      refine beta ?_ (by grind)
      exact subst_lc (LC.abs xs m mem) (LC.fvar y)
  case abs => grind [abs <| free_union Var]
  all_goals grind

/-- Abstracting then closing preserves a single reduction. -/
lemma step_abs_close {x : Var} (step : M ⭢βᶠ M') : M⟦0 ↜ x⟧.abs ⭢βᶠ M'⟦0 ↜ x⟧.abs := by
  grind [abs ∅, redex_subst_cong]

/-- Abstracting then closing preserves multiple reductions. -/
lemma redex_abs_close {x : Var} (step : M ↠βᶠ M') : (M⟦0 ↜ x⟧.abs ↠βᶠ M'⟦0 ↜ x⟧.abs) :=  by
  induction step using Relation.ReflTransGen.trans_induction_on
  case refl => rfl
  case single ih => exact Relation.ReflTransGen.single (step_abs_close ih)
  case trans l r => exact Relation.ReflTransGen.trans l r

/-- Multiple reduction of opening implies multiple reduction of abstraction. -/
theorem redex_abs_cong (xs : Finset Var) (cofin : ∀ x ∉ xs, (M ^ fvar x) ↠βᶠ (M' ^ fvar x)) :
    M.abs ↠βᶠ M'.abs := by
  have ⟨fresh, _⟩ := fresh_exists <| free_union [fv] Var
  rw [open_close fresh M 0 ?_, open_close fresh M' 0 ?_]
  all_goals grind [redex_abs_close]

end LambdaCalculus.LocallyNameless.Untyped.Term.FullBeta

end Cslib
