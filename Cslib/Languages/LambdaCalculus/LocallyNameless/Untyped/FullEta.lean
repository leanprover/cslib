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

attribute [scoped grind .] Xi.appL Xi.appR Xi.base

variable {M M' N N' : Term Var}

/-- The right side of an η-reduction is locally closed. -/
@[scoped grind →]
lemma step_lc_r (step : M ⭢ηᶠ M') : LC M' :=
  refine Xi.step_lc_r ?_ step
  grind [cases BaseEta]

/- Single reduction `app M (fvar x) ⭢ηᶠ N` implies `N = app M' (fvar x)` for some M' -/
@[scoped grind →]
lemma invert_step_app_fvar (step : (app M (fvar x)) ⭢ηᶠ N) :
    ∃ M', N = app M' (fvar x) ∧ M ⭢ηᶠ M' := by
  cases step
  case base h => cases h
  case appR step_M _ => exact ⟨_, rfl, step_M⟩
  case appL lc_M step_x =>
    cases step_x
    case base h => cases h

variable [HasFresh Var] [DecidableEq Var]

/-- An η-reduction step does not introduce new free variables. -/
lemma step_not_fv (step : M ⭢ηᶠ M') (hw : w ∉ M.fv) : w ∉ M'.fv := by
  induction step with
  | base => grind [cases BaseEta]
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
  | base h =>
    cases h
    case eta lc_M => exact .base (.eta (subst_lc lc_M lc_fy))
  | appL lc_Z _ ih => exact .appL (subst_lc lc_Z lc_fy) ih
  | appR lc_Z _ ih => exact .appR (subst_lc lc_Z lc_fy) ih
  | abs xs _ ih =>
    apply Xi.abs (xs ∪ {x, y})
    intro z hz
    have ih_z := ih z (by grind)
    have comm e := subst_open_var z x (fvar y) e (by grind) lc_fy
    simp only [comm] at ih_z
    exact ih_z

/- Closing a sequence of η-reduction steps over a fresh variable preserves the steps. -/
open Relation in
lemma close_eta_steps (hx_M : x ∉ M.fv) (st_M : ReflGen FullEta (M ^ fvar x) N) :
    ReflGen FullEta M.abs (N ^* x).abs := by
  cases st_M with
  | refl => rw [←open_close_var x M hx_M]
  | single st =>
    exact .single (Xi.abs {x} (by grind))

end LambdaCalculus.LocallyNameless.Untyped.Term.FullEta

end Cslib
