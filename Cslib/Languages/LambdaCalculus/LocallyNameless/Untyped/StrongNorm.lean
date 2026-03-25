/-
Copyright (c) 2025 David Wegmann. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Wegmann
-/

module

public import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.FullBeta
public import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.MultiApp
public import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.LcAt

@[expose] public section

set_option linter.unusedDecidableInType false

namespace Cslib

universe u

namespace LambdaCalculus.LocallyNameless.Untyped.Term

variable {Var : Type u} {t t' : Term Var}

open FullBeta

attribute [grind =] Finset.union_singleton

/-- A term is strongly normalizing if every reduction sequence terminates at some point.
    This is ensured by the following type as inductive data must always be finite. -/
inductive SN {α} : Term α → Prop
| sn t : (∀ t', t ⭢βᶠ t' → SN t') → SN t

attribute [scoped grind .] SN.sn

/-- A single β-reduction step preserves strong normalization. -/
lemma sn_step (t_st_t' : t ⭢βᶠ t') (sn_t : SN t) : SN t' := by
  grind [cases SN]

/-- Multiple β-reduction steps also preserve strong normalization. -/
lemma sn_steps (t_st_t' : t ↠βᶠ t') (sn_t : SN t) : SN t' := by
  induction t_st_t' with grind [sn_step]

/-- Free variables are strongly normalizing. -/
lemma sn_fvar {x : Var} : SN (fvar x) := by
  grind only [cases Xi, cases Beta, SN]

/-- An application is strongly normalizing if the left and right terms are strongly normalizing,
    as well as all possible future top level abstraction application beta reductions -/
lemma sn_app (t s : Term Var) (sn_t : SN t) (sn_s : SN s)
    (hβ : ∀ {t' s' : Term Var}, t ↠βᶠ t'.abs → s ↠βᶠ s' → SN (t' ^ s')) : SN (t.app s) := by
  induction sn_t generalizing s with
  | sn t ht ih_t =>
    induction sn_s with
    | sn s hs ih_s =>
      constructor
      intro u hstep
      cases hstep with
      | base h => cases h; grind
      | appL _ h_s_red => apply ih_s _ h_s_red
                          grind [Relation.ReflTransGen.head]
      | appR _ h_t_red => apply ih_t _ h_t_red _ (SN.sn s hs)
                          grind [Relation.ReflTransGen.head]

/-- The left side of a strongly normalizing application is strongly normalizing. -/
lemma sn_app_left (M N : Term Var) (lc_N : Term.LC N) (sn_MN : SN (M.app N)) :
    SN M := by
  generalize Heq : M.app N = P
  rw [Heq] at sn_MN
  induction sn_MN generalizing M N with grind

/-- The right side of a strongly normalizing application is strongly normalizing. -/
lemma sn_app_right (M N : Term Var) (lc_N : Term.LC M) (sn_MN : SN (M.app N)) :
    SN N := by
  generalize Heq : M.app N = P
  rw [Heq] at sn_MN
  induction sn_MN generalizing M N with grind

/-- A neutral term is a term of the form v t₁ … t_n where
    v is a variable and t₁ … t_n are strongly normalizing terms. -/
@[scoped grind]
inductive Neutral : Term Var → Prop
/-- Just a bound variable is neutral. -/
| bvar : ∀ n, Neutral (bvar n)
/-- Just a free variable is neutral. -/
| fvar : ∀ x, Neutral (fvar x)
/-- Applying a strongly normalizing term to a neutral term yields a neutral term. -/
| app : ∀ t1 t2, Neutral t1 → SN t2 → Neutral (app t1 t2)

--attribute [scoped grind .] Neutral.bvar Neutral.fvar Neutral.app

/-- Neutral terms only reduce to other neutral terms in a single step -/
lemma neutral_step (Hneut : Neutral t) (Hstep : t ⭢βᶠ t') : Neutral t' := by
  induction Hneut generalizing t' with grind only [Neutral, cases Xi, sn_step]

/-- Neutral terms only reduce to other neutral terms in multiple steps -/
lemma neutral_steps (Hneut : Neutral t) (Hsteps : t ↠βᶠ t') : Neutral t' := by
  induction Hsteps <;> grind [neutral_step]

/-- Neutral terms are strongly normalizing. -/
lemma sn_neutral (Hneut : Neutral t) : SN t := by
  induction Hneut with
  | app => grind [→ neutral_steps, sn_app]
  | _ => grind only [SN, cases Xi]

/-- A lambda abstraction is strongly normalizing if its body is strongly normalizing. -/
lemma sn_abs [DecidableEq Var] [HasFresh Var] {M N : Term Var} (sn_MN : SN (M ^ N)) (lc_N : LC N) :
    SN (abs M) := by
  generalize h : (M ^ N) = M_open at sn_MN
  induction sn_MN generalizing M N with
  | sn =>
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
lemma sn_abs_app_multiApp [DecidableEq Var] [HasFresh Var] {Ps} {M N : Term Var}
    (sn_N : SN N) (sn_MNPs : SN (multiApp (M ^ N) Ps))
    (lc_N : LC N) (lc_MNPs : LC (multiApp (M ^ N) Ps)) : SN (multiApp (M.abs.app N) Ps) := by
  induction Ps with
  | nil =>
    apply sn_app
    · grind [sn_abs]
    · exact sn_N
    · grind [→ steps_open_cong_abs, open_abs_lc, sn_steps]
  | cons P Ps ih =>
    apply sn_app
    · cases lc_MNPs with grind [sn_app_left]
    · grind [sn_app_right]
    · intro Q' P' hstep1 hstep2
      have ⟨M', N', Ps', h_M_red, h_N_red, h_Ps_red, h_cases⟩ := invert_abs_multiApp_mst hstep1
      rcases h_cases with h_P | ⟨h_st1, h_st2⟩
      · cases Ps' with grind
      · have innerSteps : (M ^ N).multiApp Ps ↠βᶠ (M' ^ N').multiApp Ps' := by
          trans
          · exact steps_multiApp_r h_Ps_red (by grind)
          · apply steps_multiApp_l
            · apply steps_open_cong_abs M M' N N' <;> grind [open_abs_lc]
            · grind [multiApp_steps_lc]
        apply sn_steps
        · calc ((M ^ N).multiApp Ps).app P
            _ ↠βᶠ ((M ^ N).multiApp Ps).app P' := by grind
            _ ↠βᶠ Q'.abs.app P' := redex_app_l_cong (.trans innerSteps h_st2) (by grind)
            _ ↠βᶠ Q' ^ P' := by grind
        · grind

end LambdaCalculus.LocallyNameless.Untyped.Term

end Cslib
