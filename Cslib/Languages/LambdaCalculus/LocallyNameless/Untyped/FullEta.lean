/-
Copyright (c) 2026 Maximiliano Onofre Martínez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maximiliano Onofre Martínez
-/

module

public import Cslib.Foundations.Data.Relation
public import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.Properties

public section

/-! # η-reduction for the λ-calculus -/

namespace Cslib

universe u

variable {Var : Type u}

namespace LambdaCalculus.LocallyNameless.Untyped.Term

/-- A single η-reduction step. -/
@[reduction_sys "ηᶠ"]
inductive FullEta : Term Var → Term Var → Prop
/-- The eta rule: λx. M x ⟶ M, provided x is not free in M. -/
| eta : LC M → FullEta (abs (app M (bvar 0))) M
/-- Left congruence rule for application. -/
| appL: LC Z → FullEta M N → FullEta (app Z M) (app Z N)
/-- Right congruence rule for application. -/
| appR : LC Z → FullEta M N → FullEta (app M Z) (app N Z)
/-- Congruence rule for lambda terms. -/
| abs (xs : Finset Var) : (∀ x ∉ xs, FullEta (M ^ fvar x) (N ^ fvar x)) → FullEta (abs M) (abs N)

namespace FullEta

attribute [scoped grind .] appL appR

variable {M M' N N' : Term Var}

/-- The right side of an η-reduction is locally closed. -/
@[scoped grind →]
lemma step_lc_r (step : M ⭢ηᶠ M') : LC M' := by
  induction step
  case abs => constructor; assumption
  all_goals grind

/- Single reduction `app M (fvar x) ⭢ηᶠ N` implies `N = app M' (fvar x)` for some M' -/
@[scoped grind →]
lemma invert_step_app_fvar (step : (app M (fvar x)) ⭢ηᶠ N) :
    ∃ M', N = app M' (fvar x) ∧ M ⭢ηᶠ M' := by
  cases step with
  | appR _ step_M => exact ⟨_, rfl, step_M⟩
  | appL _ step_x => cases step_x

variable [HasFresh Var] [DecidableEq Var]

/-- An η-reduction step does not introduce new free variables. -/
lemma step_not_fv (step : M ⭢ηᶠ M') (hw : w ∉ M.fv) : w ∉ M'.fv := by
  induction step with
  | abs =>
    have ⟨x, _⟩ := fresh_exists <| free_union [fv] Var
    have := open_close x
    grind [close_preserve_not_fvar, open_fresh_preserve_not_fvar]
  | _ => grind

/-- Substitution of a fresh variable preserves an η-reduction step. -/
@[scoped grind ←]
lemma eta_subst_fvar {x y : Var} (step : M ⭢ηᶠ M') : M [ x := fvar y ] ⭢ηᶠ M' [ x := fvar y ] := by
  have lc_fy : LC (fvar y) := by constructor
  induction step with
  | eta lc_M => exact eta (subst_lc lc_M lc_fy)
  | appL lc_Z _ ih => exact appL (subst_lc lc_Z lc_fy) ih
  | appR lc_Z _ ih => exact appR (subst_lc lc_Z lc_fy) ih
  | abs xs _ ih =>
    apply abs (xs ∪ {x, y})
    grind

/- Closing a sequence of η-reduction steps over a fresh variable preserves the steps. -/
open Relation in
lemma close_eta_steps (hx_M : x ∉ M.fv) (st_M : ReflGen FullEta (M ^ fvar x) N) :
    ReflGen FullEta M.abs (N ^* x).abs := by
  cases st_M with
  | refl =>
    have eq_M : M = (M ^ fvar x) ^* x := open_close x M 0 hx_M
    rw [←eq_M]
  | single st =>
    exact .single (.abs {x} fun _ _ => by grind)

end LambdaCalculus.LocallyNameless.Untyped.Term.FullEta

end Cslib
