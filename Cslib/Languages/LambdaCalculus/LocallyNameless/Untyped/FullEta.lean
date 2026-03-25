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

set_option linter.unusedDecidableInType false

/-! # η-reduction for the λ-calculus -/

namespace Cslib

universe u

variable {Var : Type u}

namespace LambdaCalculus.LocallyNameless.Untyped.Term

/-- A single η-reduction step. -/
@[scoped grind]
inductive Eta : Term Var → Term Var → Prop
/-- The eta rule: λx. M x ⟶ M, provided x is not free in M. -/
| eta : LC M → Eta (abs (app M (bvar 0))) M

/-- Full η-reduction, defined as the congruence closure of the base η-rule. -/
@[reduction_sys "ηᶠ"]
abbrev FullEta : Term Var → Term Var → Prop := Xi Eta

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

/-- Abstracting then closing preserves a single η-reduction step. -/
lemma step_abs_close {x} (step : M ⭢ηᶠ M') (lc_M : LC M) : (M ^* x).abs ⭢ηᶠ (M' ^* x).abs := by
  grind [Xi.abs ∅]

/-- Abstracting then closing preserves multiple reductions. -/
lemma redex_abs_close {x} (steps : M ↠ηᶠ M') (lc_M : LC M) : (M ^* x).abs ↠ηᶠ (M' ^* x).abs := by
  induction steps using Relation.ReflTransGen.head_induction_on
  case refl => exact .refl
  case head b c st_bc _ ih => exact .head (step_abs_close st_bc lc_M) (ih (step_lc_r st_bc))

/-- Multiple reduction of opening implies multiple reduction of abstraction. -/
theorem redex_abs_cong {M M' : Term Var} (xs : Finset Var)
    (cofin : ∀ x ∉ xs, (M ^ fvar x) ↠ηᶠ M' ^ fvar x) (lc_M : LC M.abs) :
    M.abs ↠ηᶠ M'.abs := by
  cases lc_M
  case' abs L hL =>
    have ⟨x, hx⟩ := fresh_exists (xs ∪ M.fv ∪ M'.fv ∪ L)
    simp only [Finset.mem_union, not_or] at hx
    have := redex_abs_close (x := x) (cofin x hx.1.1.1) (hL x hx.2)
    grind [open_close x M 0 hx.1.1.2, open_close x M' 0 hx.1.2]

/- `t ⭢ηᶠ t'` implies `s [ x := t ] ↠ηᶠ s [ x := t' ]`. -/
lemma step_subst_cong_r {x : Var} (s t t' : Term Var) (st : t ⭢ηᶠ t') (lc_s : LC s) (lc_t : LC t) :
    s [ x := t ] ↠ηᶠ s [ x := t' ] := by
  induction lc_s generalizing x t t'
  case fvar y =>
    by_cases h : y = x <;> grind
  case app l r hl hr ih_l ih_r =>
    exact .trans (redex_app_l_cong (ih_l t t' st lc_t) (subst_lc hr lc_t))
                 (redex_app_r_cong (ih_r t t' st lc_t) (subst_lc hl (step_lc_r st)))
  case abs L body h_lc_body ih =>
    apply redex_abs_cong (L ∪ {x})
    · intro z hz
      simp only [Finset.mem_union, Finset.mem_singleton, not_or] at hz
      have hz_x : z ≠ x := hz.2
      have steps_body : (body ^ fvar z)[x:=t] ↠ηᶠ (body ^ fvar z)[x:=t'] :=
        ih z hz.1 t t' st lc_t
      have eq1 := subst_open_var z x t body hz_x.symm lc_t
      have eq2 := subst_open_var z x t' body hz_x.symm (step_lc_r st)
      rw [eq1, eq2] at steps_body
      exact steps_body
    · exact subst_lc (LC.abs L body h_lc_body) lc_t

/- `steps_subst_cong_r` can be generalized to multiple reductions `t ↠ηᶠ t'`. -/
lemma steps_subst_cong_r {x : Var} (s t t' : Term Var) (st : t ↠ηᶠ t') (lc_s : LC s) (lc_t : LC t) :
    s [ x := t ] ↠ηᶠ s [ x := t' ] := by
  induction st using Relation.ReflTransGen.head_induction_on
  case refl => rfl
  case head _ _ st _ ih =>
    exact .trans (step_subst_cong_r s _ _ st lc_s lc_t) (ih (step_lc_r st))

/- `t ⭢ηᶠ t'` implies `s ^ t ↠ηᶠ s ^ t'`. -/
lemma step_open_cong_r {s t t' : Term Var} (lc_s : LC s.abs) (lc_t : LC t) (step : t ⭢ηᶠ t') :
    (s ^ t) ↠ηᶠ s ^ t' := by
  cases lc_s
  case' abs L hL =>
    have ⟨x, hx⟩ := fresh_exists (L ∪ s.fv)
    simp only [Finset.mem_union, not_or] at hx
    have eq1 := subst_intro x t s hx.2 lc_t
    have eq2 := subst_intro x t' s hx.2 (step_lc_r step)
    have subst_step := step_subst_cong_r (x := x) (s ^ fvar x) t t' step (hL x hx.1) lc_t
    rw [eq1, eq2]
    exact subst_step

/- `steps_open_cong_r` can be generalized to multiple reductions `t ↠ηᶠ t'`. -/
lemma steps_open_cong_r {s t t' : Term Var} (lc_s : LC s.abs) (lc_t : LC t) (steps : t ↠ηᶠ t') :
    (s ^ t) ↠ηᶠ s ^ t' := by
  induction steps using Relation.ReflTransGen.head_induction_on
  case refl => rfl
  case head _ _ st _ ih =>
    exact .trans (step_open_cong_r lc_s lc_t st) (ih (step_lc_r st))

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

/- `steps_subst_cong_l` can be generalized to multiple reductions `s ↠ηᶠ s'`. -/
lemma steps_subst_cong_l {x : Var} (s s' N : Term Var) (steps : s ↠ηᶠ s') (lc_N : LC N) :
    s [ x := N ] ↠ηᶠ s' [ x := N ] := by
  induction steps with
  | refl => rfl
  | tail _ step ih => grind [step_subst_cong_l]

end LambdaCalculus.LocallyNameless.Untyped.Term.FullEta

end Cslib
