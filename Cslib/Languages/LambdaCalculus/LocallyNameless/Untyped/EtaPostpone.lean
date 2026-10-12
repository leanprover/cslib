/-
Copyright (c) 2025 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Leng
-/


module

public import Cslib.Foundations.Relation.Confluence
public import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.FullBetaEtaConfluence
public import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.ParEta

/-!  # η-postpone theorems

This file presents 5 postponement theorems for moving η-reduction behind
β-reduction.

## Main results

* `transgen_postpone_eta_beta`: if `P →ηᶠ Q` and `Q →βᶠ R`, then there is a term
  `S` with `P ↠β+ S` and `S ↠ηᶠ R`.
* `commute_etastar_beta`: if `P ↠ηᶠ Q` and `Q ↠βᶠ R`, then there is a term
  `S` with `P ↠βᶠ S` and `S ↠ηᶠ R`.
* `semiDiamondCommute_eta_beta`: if `P →ηᶠ Q` and `Q ↠β+ R`, then there is a term
  `S` with `P ↠β+ S` and `S ↠ηᶠ R`.
* `diamondcommute_etaplus_betastar`: if `P ↠ηᶠ Q` and `Q ↠β+ R`, then there is
  a term `S` with `P ↠β+ S` and `S ↠ηᶠ R`.
* `eta_postpone`: if `P ↠βηᶠ Q`, then there is a term `S` such that
  `P ↠βᶠ S` and `S ↠ηᶠ Q`.

## Reference

* [Y. Takahashi, *Parallel Reductions in λ-Calculus*][Takahashi1995]

-/

@[expose] public section

set_option linter.unusedDecidableInType false

namespace Cslib

universe u

namespace LambdaCalculus.LocallyNameless.Untyped.Term

open Relation Function

variable {Var : Type u} [DecidableEq Var] [HasFresh Var]

/-- An η-step followed by a β-step can be postponed: if `P →ηᶠ Q` and `Q →βᶠ R`,
then there exists `S` such that `TransGen FullBeta P S` and `S ↠ηᶠ R`. -/
theorem transgen_postpone_eta_beta : TransGenCommute (swap (FullEta (Var := Var))) FullBeta := by
  intros y x z hη hβ
  induction hη generalizing z with
  | base hη => cases hη with | eta h_lc =>
  exact ⟨Term.abs (z.app (bvar 0)),
        FullBeta.transgen_abs_cong ∅ (fun x hx => FullBeta.transgen_app_l (.fvar _)
                  (.single (by rwa [open_lc _ _ _ h_lc, open_lc _ _ _ (FullBeta.step_lc_r hβ)]))),
        .single (.base (.eta (FullBeta.step_lc_r hβ))) ⟩
  | appL _ h ih =>
    cases hβ with
    | base hβ => cases hβ with | beta hm hn =>
        refine ⟨_, .single (.base (.beta hm (FullEta.step_lc_l h))), ?_⟩
        rw [reflTransGen_swap] at *
        exact FullEta.step_open_cong_r hm h
    | appL h1 h2 =>
        obtain ⟨w, hw1, hw2⟩ := ih h2
        refine ⟨_, FullBeta.transgen_app_r h1 hw1, ?_⟩
        rw [reflTransGen_swap] at *
        exact FullEta.redex_app_r_cong hw2 h1
    | appR _ h2 =>  exact ⟨_, .single (.appR (FullEta.step_lc_l h) h2),
                              .single (.appL (FullBeta.step_lc_r h2) h)⟩
  | appR _ h ih =>
    cases hβ with
    | appL _ h2 => exact ⟨_, .single (.appL (FullEta.step_lc_l h) h2),
                             .single (.appR (FullBeta.step_lc_r h2) h)⟩
    | appR h1 h2 =>
        obtain ⟨w, hw1, hw2⟩ := ih h2
        refine ⟨_, FullBeta.transgen_app_l h1 hw1, ?_⟩
        rw [reflTransGen_swap] at *
        exact FullEta.redex_app_l_cong hw2 h1
    | base hβ =>
      cases hβ with | beta hm hz => cases h with
        | abs xs h =>
            refine ⟨_, .single (.base (.beta (FullEta.step_lc_l (Xi.abs xs h)) hz)), ?_⟩
            rw [reflTransGen_swap] at *
            exact FullEta.steps_open_cong_l xs (by grind) hz
        | base h =>
            cases h with | eta h =>
              refine ⟨_, .head (.base (.beta ?_ hz)) (.single (.base (.beta ?_ (by grind)))), ?_⟩
              · rw [<- lcAt_iff_LC] at *
                simp_all only [LcAt, zero_add, Order.lt_one_iff, decide_true, Bool.and_true]
                apply lcAt_le _ _ _ (by omega) hm
              · rw [<- lcAt_iff_LC] at *
                simp_all only [LcAt, zero_add]
                rw [lcAt_openRec_iff_lcAt _ _ _ (lcAt_le _ _ _ (by omega) hz)]
                exact lcAt_le _ _ _ (by omega) hm
              · rw [<- lcAt_iff_LC] at *
                rw [lcAt_openRec_above_lcAt _ _ 1 _ (by omega) (by grind)]
                grind
  | abs xs hx ih =>
      cases hβ with | base hβ => cases hβ | abs ys hy =>
        rename_i _ _ N
        have ⟨x, _⟩ := fresh_exists <| free_union [fv] Var
        obtain ⟨w, hw1, hw2⟩ := ih x (by grind) (hy x (by grind))
        refine ⟨(w ^* x).abs, FullBeta.transgen_abs_cong (free_union [fv] Var) fun c hc => ?_, ?_⟩
        · rw [close_open_to_subst _ _ _ ?_ (by grind)]
          · have g := FullBeta.transgen_subst_cong _ _ (fvar c) x hw1 (by grind)
            rw [subst_open, subst_fvar] at g <;> grind
          · cases hw1 <;> apply FullBeta.step_lc_r <;> assumption
        · rw [open_close_var x N (by grind)]
          rw [reflTransGen_swap] at *
          exact FullEta.redex_abs_close hw2

/-- If `P ↠ηᶠ Q` and `Q ↠βᶠ R`, then there exists `S` such that `P ↠βᶠ S` and `S ↠ηᶠ R`. -/
theorem commute_etastar_beta : Commute (swap FullEta) (FullBeta (Var := Var)) := by
  intros _ _ _ hη hβ
  simp only [<- reflTransGen_parallel_fullBeta] at hβ
  rw [reflTransGen_swap] at hη
  simp only [<- reflTransGen_parallel_fullEta] at hη
  rw [<- reflTransGen_swap] at hη
  obtain ⟨s, _, g⟩ := commute_parEta_parBeta hη hβ
  refine ⟨s, by simp_all [← reflTransGen_parallel_fullBeta], ?_⟩
  rw [reflTransGen_swap] at *
  exact reflTransGen_le_of_le ParEta.le_reflTransGen_fullEta _ _ g

/-- If `P →ηᶠ Q` and `Q ↠β+ R`, then there exists `P'` with `P ↠β+  P'` and `P' ↠ηᶠ R`. -/
theorem semiDiamondCommute_eta_beta : SemiDiamondCommute (swap FullEta) (FullBeta (Var := Var)) :=
  Commute.to_semiDiamondCommute commute_etastar_beta transgen_postpone_eta_beta

/-- If `P ↠ηᶠ Q` and `Q ↠β+ R`, then there exists `P'` with `P ↠β+  P'` and `P' ↠ηᶠ R`. -/
theorem diamondcommute_etaplus_betastar :
    DiamondCommute (ReflTransGen (swap FullEta)) (TransGen (FullBeta (Var := Var))) :=
  SemiDiamondCommute.to_diamond_commute semiDiamondCommute_eta_beta

theorem eta_postpone {M N : Term Var} (h : M ↠βηᶠ N) : ∃ L, M ↠βᶠ L ∧ L ↠ηᶠ N := by
  have g := (commute_equivalents.out 2 4 rfl rfl).mp (commute_etastar_beta (Var := Var)) N M
  rw [sup_comm, reflTransGen_swap] at g
  obtain ⟨L, g, _⟩ := g h
  rw [reflTransGen_swap] at g
  grind

end LambdaCalculus.LocallyNameless.Untyped.Term

end Cslib
