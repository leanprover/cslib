/-
Copyright (c) 2026 Maximiliano Onofre Martínez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maximiliano Onofre Martínez
-/

module

public import Cslib.Foundations.Data.Relation
public import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.Properties
public import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.Congruence

public section

/-! # η-reduction for the λ-calculus -/

namespace Cslib

universe u

variable {Var : Type u}

namespace LambdaCalculus.LocallyNameless.Untyped.Term

/-- A single η-reduction step. -/
@[scoped grind]
inductive BaseEta : Term Var → Term Var → Prop
/-- The eta rule: λx. M x ⟶ M, provided x is not free in M. -/
| eta : LC M → BaseEta (abs (app M (bvar 0))) M

/-- Full η-reduction, defined as the congruence closure of the base η-rule. -/
@[reduction_sys "ηᶠ"]
abbrev FullEta : Term Var → Term Var → Prop := Xi BaseEta

namespace FullEta

variable {M M' N N' : Term Var}

/-- The right side of an η-reduction is locally closed. -/
@[scoped grind →]
lemma step_lc_r (step : M ⭢ηᶠ M') : LC M' := by
  refine Xi.step_lc_r ?_ step
  grind

/-- Left congruence rule for application in multiple reduction. -/
@[scoped grind ←]
theorem redex_app_l_cong (redex : M ↠ηᶠ M') (lc_N : LC N) : app M N ↠ηᶠ app M' N := by
  induction redex <;> grind

/-- Right congruence rule for application in multiple reduction. -/
@[scoped grind ←]
theorem redex_app_r_cong (redex : M ↠ηᶠ M') (lc_N : LC N) : app N M ↠ηᶠ app N M' := by
  induction redex <;> grind

/- Single reduction `app M (fvar x) ⭢ηᶠ N` implies `N = app M' (fvar x)` for some M' -/
@[scoped grind →]
lemma invert_step_app_fvar (step : (app M (fvar x)) ⭢ηᶠ N) :
    ∃ M', N = app M' (fvar x) ∧ M ⭢ηᶠ M' := by
  cases step with
  | appR _ step_M => exact ⟨_, rfl, step_M⟩
  | _ => grind [cases Xi]

variable [HasFresh Var] [DecidableEq Var]

/-- An η-reduction step does not introduce new free variables. -/
lemma step_not_fv (step : M ⭢ηᶠ M') (hw : w ∉ M.fv) : w ∉ M'.fv := by
  induction step with
  | base => grind
  | abs =>
    have ⟨x, _⟩ := fresh_exists <| free_union [fv] Var
    have := open_close x
    grind [close_preserve_not_fvar, open_fresh_preserve_not_fvar]
  | _ => grind

/-- Substitution of a fresh variable preserves an η-reduction step. -/
@[scoped grind ←]
lemma eta_subst_fvar {x y : Var} (step : M ⭢ηᶠ M') : M [ x := fvar y ] ⭢ηᶠ M' [ x := fvar y ] := by
  induction step with
  | abs => grind [Xi.abs <| free_union Var]
  | _ => grind

/- Closing a sequence of η-reduction steps over a fresh variable preserves the steps. -/
open Relation in
lemma close_eta_steps (hx_M : x ∉ M.fv) (st_M : ReflGen FullEta (M ^ fvar x) N) :
    ReflGen FullEta M.abs (N ^* x).abs := by
  cases st_M with
  | refl => rw [←open_close_var x M hx_M]
  | single st =>
    exact .single (Xi.abs {x} (by grind))

/- `s ⭢ηᶠ s'` implies `s [ x := N ] ⭢ηᶠ s' [ x := N ]`. -/
lemma step_subst_cong_l {x : Var} (s s' N : Term Var) (step : s ⭢ηᶠ s') (lc_N : LC N) :
    s [ x := N ] ⭢ηᶠ s' [ x := N ] := by
  induction step
  case' base h => cases h with | eta lc => exact Xi.base (.eta (subst_lc lc lc_N))
  case' abs => grind [Xi.abs <| free_union Var, subst_open_var]
  all_goals grind

/- `steps_subst_cong_l` generalizes `step_subst_cong_l` to multiple reductions `s ↠ηᶠ s'`. -/
lemma steps_subst_cong_l {x : Var} (s s' N : Term Var) (steps : s ↠ηᶠ s') (lc_N : LC N) :
    s [ x := N ] ↠ηᶠ s' [ x := N ] := by
  induction steps with
  | refl => rfl
  | tail _ step ih => grind [step_subst_cong_l]

end LambdaCalculus.LocallyNameless.Untyped.Term.FullEta

end Cslib
