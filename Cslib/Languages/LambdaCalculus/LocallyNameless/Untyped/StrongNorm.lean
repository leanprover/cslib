/-
Copyright (c) 2025 David Wegmann. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Wegmann
-/

module

public import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.FullBeta
public import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.ListFullBeta
public import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.LcAt
public import Cslib.Foundations.Relation.Confluence

/-! Strong normalization (termination) for full beta-reduction of untyped lambda calculus. -/

@[expose] public section

set_option linter.unusedDecidableInType false

namespace Cslib

universe u

namespace LambdaCalculus.LocallyNameless.Untyped.Term

variable {Var : Type u} {t t' : Term Var}

open FullBeta Relation

attribute [grind =] Finset.union_singleton

/-- A single β-reduction step preserves strong normalization. -/
lemma sn_step (t_st_t' : t ⭢βᶠ t') (sn_t : SN FullBeta t) : SN FullBeta t' :=
  sn_t.of_rel t_st_t'

/-- Multiple β-reduction steps also preserve strong normalization. -/
lemma sn_steps (t_st_t' : t ↠βᶠ t') (sn_t : SN FullBeta t) : SN FullBeta t' :=
  sn_t.of_rel_reflTransGen t_st_t'

set_option linter.tacticAnalysis.verifyGrindOnly false in
/-- Free variables are strongly normalizing. -/
lemma sn_fvar {x : Var} : SN FullBeta (fvar x) := by
  rw [SN_iff_SN_of_rel]
  grind only [cases Xi, cases Beta]

/-- An application is strongly normalizing if the left and right terms are strongly normalizing,
    as well as all possible future top level abstraction application beta reductions -/
lemma sn_app (t s : Term Var) (sn_t : SN FullBeta t) (sn_s : SN FullBeta s)
    (hβ : ∀ {t' s' : Term Var}, t ↠βᶠ t'.abs → s ↠βᶠ s' → SN FullBeta (t' ^ s')) :
    SN FullBeta (t.app s) := by
  induction sn_t generalizing s with
  | intro t ht ih_t =>
    induction sn_s with
    | intro s hs ih_s =>
      constructor
      intro u hstep
      cases hstep with
      | base h => cases h; grind
      | appL _ h_s_red => apply ih_s _ h_s_red
                          grind [Relation.ReflTransGen.head]
      | appR _ h_t_red => apply ih_t _ h_t_red _ (SN.intro hs)
                          grind [Relation.ReflTransGen.head]

/-- The left side of a strongly normalizing application is strongly normalizing. -/
lemma sn_app_left (M N : Term Var) (lc_N : Term.LC N) (sn_MN : SN FullBeta (M.app N)) :
    SN FullBeta M := by
  refine sn_MN.onFun_of_image (f := (·.app N)) |>.of_le fun _ _ => ?_
  exact Xi.appR lc_N

/-- The right side of a strongly normalizing application is strongly normalizing. -/
lemma sn_app_right (M N : Term Var) (lc_M : Term.LC M) (sn_MN : SN FullBeta (M.app N)) :
    SN FullBeta N := by
  refine sn_MN.onFun_of_image (f := M.app) |>.of_le fun _ _ => ?_
  exact Xi.appL lc_M

/-- A neutral term is a term of the form v t₁ … t_n where
    v is a variable and t₁ … t_n are strongly normalizing terms. -/
@[scoped grind]
inductive Neutral : Term Var → Prop
/-- Just a bound variable is neutral. -/
| bvar : ∀ n, Neutral (bvar n)
/-- Just a free variable is neutral. -/
| fvar : ∀ x, Neutral (fvar x)
/-- Applying a strongly normalizing term to a neutral term yields a neutral term. -/
| app : ∀ t1 t2, Neutral t1 → SN FullBeta t2 → Neutral (app t1 t2)

--attribute [scoped grind .] Neutral.bvar Neutral.fvar Neutral.app

/-- Neutral terms only reduce to other neutral terms in a single step -/
lemma neutral_step (Hneut : Neutral t) (Hstep : t ⭢βᶠ t') : Neutral t' := by
  induction Hneut generalizing t' with grind only [Neutral, cases Xi, sn_step]

/-- Neutral terms only reduce to other neutral terms in multiple steps -/
lemma neutral_steps (Hneut : Neutral t) (Hsteps : t ↠βᶠ t') : Neutral t' := by
  induction Hsteps <;> grind [neutral_step]

set_option linter.tacticAnalysis.verifyGrindOnly false in
/-- Neutral terms are strongly normalizing. -/
lemma sn_neutral (Hneut : Neutral t) : SN FullBeta t := by
  induction Hneut with
  | app => grind only [→ neutral_steps, sn_app]
  | _ =>
    rw [SN_iff_SN_of_rel]
    grind only [cases Xi]

/-- A lambda abstraction is strongly normalizing if its body is strongly normalizing. -/
lemma sn_abs [DecidableEq Var] [HasFresh Var] {M N : Term Var} (sn_MN : SN FullBeta (M ^ N))
    (lc_N : LC N) : SN FullBeta (abs M) := by
  generalize h : (M ^ N) = M_open at sn_MN
  induction sn_MN generalizing M N with
  | intro =>
    constructor
    intro _ h_step
    cases h_step with
    | abs _ H => grind [step_open_cong_l _ _ _ _ H]
    | base _ => contradiction

/-- A term of the form λ M N P_1 … P_n is strongly normalizing if
      1. N is strongly normalizing,
      1. M ^ N P₁ … Pₙ is strongly normalizing,
      1. N is locally closed,
      1. M ^ N P₁ … Pₙ is locally closed -/
lemma sn_abs_app_multiApp [DecidableEq Var] [HasFresh Var] {Ps : List (Term Var)} {M N : Term Var}
    (sn_N : SN FullBeta N) (sn_MNPs : SN FullBeta (Ps.foldl Term.app (M ^ N)))
    (lc_N : LC N) (lc_MNPs : LC (Ps.foldl app (M ^ N))) :
    SN FullBeta (Ps.foldl app (M.abs.app N)) := by
  induction Ps using List.reverseRecOn with
  | nil =>
    apply sn_app
    · grind [sn_abs]
    · exact sn_N
    · grind [→ steps_open_cong_abs, open_abs_lc, sn_steps]
  | append_singleton Ps P ih =>
    rw [List.foldl_concat]
    apply sn_app
    · grind [cases LC, List.foldl_concat, sn_app_left]
    · grind [List.foldl_concat, sn_app_right]
    · intro Q' P' hstep1 hstep2
      have ⟨M', N', Ps', h_M_red, h_N_red, h_Ps_red, h_cases⟩ := invert_abs_multiApp_mst hstep1
      rcases h_cases with h_P | ⟨h_st1, h_st2⟩
      · induction Ps' using List.reverseRecOn with grind [List.foldl_concat]
      · have innerSteps : Ps.foldl Term.app (M ^ N) ↠βᶠ Ps'.foldl Term.app (M' ^ N') := by
          trans
          · exact steps_multiApp_r h_Ps_red (by grind)
          · apply steps_multiApp_l
            · apply steps_open_cong_abs M M' N N' <;> grind [open_abs_lc]
            · grind [multiApp_steps_lc]
        refine sn_steps ?_ sn_MNPs
        rw [List.foldl_concat]
        · calc (Ps.foldl Term.app (M ^ N)).app P
            _ ↠βᶠ (Ps.foldl Term.app (M ^ N)).app P' := by grind
            _ ↠βᶠ Q'.abs.app P' := redex_app_l_cong (.trans innerSteps h_st2) (by grind)
            _ ↠βᶠ Q' ^ P' := by
              rw [Relation.reflTransGen_iff_eq_or_transGen] at ⊢ innerSteps h_st2
              right
              refine Relation.TransGen.single (Xi.base (Beta.beta ?_ ?_))
              all_goals grind

end LambdaCalculus.LocallyNameless.Untyped.Term

end Cslib
