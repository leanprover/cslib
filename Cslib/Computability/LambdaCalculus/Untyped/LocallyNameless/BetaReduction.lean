/-
Copyright (c) 2025 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

import Cslib.Computability.LambdaCalculus.Untyped.LocallyNameless.Basic
import Cslib.Computability.LambdaCalculus.Untyped.LocallyNameless.Properties
import Cslib.Semantics.ReductionSystem.Basic

/-! # β-reduction for the λ-calculus

## References

* [A. Chargueraud, *The Locally Nameless Representation*] [Chargueraud2012]
* See also https://www.cis.upenn.edu/~plclub/popl08-tutorial/code/, from which
  this is partially adapted

-/

universe u

variable {Var : Type u} 

namespace LambdaCalculus.LocallyNameless.Term

/-- A single β-reduction step. -/
@[reduction_sys beta_rs "β"]
inductive Step : Term Var → Term Var → Prop
/-- Reduce an application to a lambda term. -/
| β : LC (abs M)→ LC N → Step (app (abs M) N) (M ^ N)
/-- Left congruence rule for application. -/
| ξₗ: LC Z → Step M N → Step (app Z M) (app Z N)
/-- Right congruence rule for application. -/
| ξᵣ : LC Z → Step M N → Step (app M Z) (app N Z)
/-- Congruence rule for lambda terms. -/
| ξ (xs : Finset Var) : (∀ x ∉ xs, Step (M ^ fvar x) (N ^ fvar x)) → Step (abs M) (abs N) 

open Step

variable {M M' N N' : Term Var}

/-- The left side of a reduction is locally closed. -/
lemma step_lc_l (step : M ⭢β M') : LC M := by
  induction step <;> constructor
  all_goals assumption

/-- Left congruence rule for application in multiple reduction.-/
theorem redex_app_l_cong : (M ↠β M') → LC N → (app M N ↠β app M' N) := by
  intros redex lc_N 
  induction' redex
  case refl => rfl
  case tail ih r => exact Relation.ReflTransGen.tail r (ξᵣ lc_N ih)

/-- Right congruence rule for application in multiple reduction.-/
theorem redex_app_r_cong : (M ↠β M') → LC N → (app N M ↠β app N M') := by
  intros redex lc_N 
  induction' redex
  case refl => rfl
  case tail ih r => exact Relation.ReflTransGen.tail r (ξₗ lc_N ih)

variable [HasFresh Var] [DecidableEq Var]

/-- The right side of a reduction is locally closed. -/
lemma step_lc_r (step : M ⭢β M') : LC M' := by
  induction step
  case «β» => apply beta_lc <;> assumption
  all_goals try constructor <;> assumption 

/-- Substitution respects a single reduction step. -/
lemma redex_subst_cong (s s' : Term Var) (x y : Var) : (s ⭢β s') -> (s [ x := fvar y ]) ⭢β (s' [ x := fvar y ]) := by
  intros step
  induction step
  case ξₗ ih => exact ξₗ (subst_lc (by assumption) (by constructor)) ih 
  case ξᵣ ih => exact ξᵣ (subst_lc (by assumption) (by constructor)) ih  
  case «β» m n abs_lc n_lc => 
    cases abs_lc with | abs xs _ mem =>
      simp only [open']
      rw [subst_open x (fvar y) 0 n m (by constructor)]
      refine «β» ?_ (subst_lc n_lc (by constructor))
      exact subst_lc (LC.abs xs m mem) (LC.fvar y)
  case ξ m' m xs mem ih => 
    apply ξ ({x} ∪ xs)
    intros z z_mem
    simp only [open']
    rw [
      subst_def, subst_def,
      ←subst_fresh x (fvar z) (fvar y), ←subst_open x (fvar y) 0 (fvar z) m (by constructor),
      subst_fresh x (fvar z) (fvar y), ←subst_fresh x (fvar z) (fvar y),
      ←subst_open x (fvar y) 0 (fvar z) m' (by constructor), subst_fresh x (fvar z) (fvar y)
    ]
    apply ih
    all_goals aesop

/-- Abstracting then closing preserves a single reduction. -/
lemma step_abs_close {x : Var} : (M ⭢β M') → (abs (M⟦0 ↜ x⟧) ⭢β abs (M'⟦0 ↜ x⟧)) := by
  intros step
  apply ξ ∅
  intros y _
  simp only [open']
  repeat rw [open_close_to_subst]
  exact redex_subst_cong M M' x y step
  exact step_lc_r step
  exact step_lc_l step

/-- Abstracting then closing preserves multiple reductions. -/
lemma redex_abs_close {x : Var} : (M ↠β M') → (abs (M⟦0 ↜ x⟧) ↠β abs (M'⟦0 ↜ x⟧)) :=  by
  intros step
  induction step using Relation.ReflTransGen.trans_induction_on
  case ih₁ => rfl
  case ih₂ ih => exact Relation.ReflTransGen.single (step_abs_close ih)
  case ih₃ l r => trans; exact l; exact r

/-- Multiple reduction of opening implies multiple reduction of abstraction. -/
theorem redex_abs_cong (xs : Finset Var) : (∀ x ∉ xs, (M ^ fvar x) ↠β (M' ^ fvar x)) → abs M ↠β abs M' := by
  intros mem
  have ⟨fresh, union⟩ := fresh_exists (xs ∪ M.fv ∪ M'.fv)
  simp only [Finset.union_assoc, Finset.mem_union, not_or] at union
  obtain ⟨_, _, _⟩ := union
  rw [←open_close fresh M 0 ?_, ←open_close fresh M' 0 ?_]
  refine redex_abs_close (mem fresh ?_)
  all_goals assumption
