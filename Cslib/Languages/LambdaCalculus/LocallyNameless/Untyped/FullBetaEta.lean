/-
Copyright (c) 2026 Maximiliano Onofre Martínez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maximiliano Onofre Martínez, Yijun Leng
-/

module

public import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.FullBetaConfluence
public import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.FullEtaConfluence

/-! # βη-Confluence for the λ-calculus

## Reference

* [T. Nipkow, *More Church-Rosser Proofs (in Isabelle/HOL)*][Nipkow2001]

-/

@[expose] public section

set_option linter.unusedDecidableInType false

namespace Cslib

universe u

variable {Var : Type u}

namespace LambdaCalculus.LocallyNameless.Untyped.Term

open Relation

/-- Full βη-reduction. -/
@[reduction_sys "βηᶠ"]
abbrev FullBetaEta : Term Var → Term Var → Prop := FullBeta ⊔ FullEta

namespace FullBetaEta

variable {M M' N N' : Term Var}

theorem step_app_l_cong (step : M ⭢βηᶠ M') (h_lc : LC N) : app M N ⭢βηᶠ app M' N := by
    rcases step with h | h
    · exact join_inl (h.appR h_lc)
    · exact join_inr (h.appR h_lc)

theorem step_app_r_cong (step : M ⭢βηᶠ M') (h_lc : LC N) : app N M ⭢βηᶠ app N M' := by
    rcases step with h | h
    · exact join_inl (h.appL h_lc)
    · exact join_inr (h.appL h_lc)

theorem steps_app_l_cong (steps : M ↠βηᶠ M') (h_lc : LC N) : app M N ↠βηᶠ app M' N := by
  induction steps with
  | refl => grind
  | tail _ h ih => exact ih.tail (step_app_l_cong h h_lc)

theorem steps_app_r_cong (steps : M ↠βηᶠ M') (h_lc : LC N) : app N M ↠βηᶠ app N M' := by
  induction steps with
  | refl => grind
  | tail _ h ih => exact ih.tail (step_app_r_cong h h_lc)

variable [HasFresh Var] [DecidableEq Var]

lemma step_fv (step : M ⭢βηᶠ M') : M'.fv ⊆ M.fv := by
    cases step with
    | inl h => grind [FullBeta.step_not_fv h]
    | inr h => grind [FullEta.step_not_fv h]

lemma steps_fv (steps : M ↠βηᶠ M') : M'.fv ⊆ M.fv := by
  induction steps with
  | refl => grind
  | tail _ step _ => grind [step_fv step]

lemma step_subst_cong_l (x : Var) (step : M ⭢βηᶠ M') (h_lc : LC N) :
    M[x := N] ⭢βηᶠ M'[x := N] := by
  cases step with
  | inl h => exact Or.inl (FullBeta.redex_subst_cong_lc _ _ _ _ h h_lc)
  | inr h => exact Or.inr (FullEta.step_subst_cong_l _ _ _  h h_lc)

lemma steps_subst_cong_l (x : Var) (steps : M ↠βηᶠ M') (h_lc : LC N) :
    M[x := N] ↠βηᶠ M'[x := N] := by
  induction steps with grind [step_subst_cong_l]

end FullBetaEta

end LambdaCalculus.LocallyNameless.Untyped.Term

end Cslib
