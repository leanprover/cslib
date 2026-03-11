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

variable {Var : Type u}


namespace LambdaCalculus.LocallyNameless.Untyped.Term

open FullBeta

attribute [grind =] Finset.union_singleton

/-- A term is strongly normalizing if every reduction sequence terminates at some point.
    This is ensured by the following type as inductive data must always be finite. -/
inductive SN {α} : Term α → Prop
| sn t : (∀ (t' : Term α), (t ⭢βᶠ t') → SN t') → SN t

attribute [scoped grind .] SN.sn

/-- A single β-reduction step preserves strong normalization. -/
@[aesop safe]
lemma sn_step {t t' : Term Var} (t_st_t' : t ⭢βᶠ t') (sn_t : SN t) : SN t' := by
  cases sn_t; grind

/-- Multiple β-reduction steps also preserve strong normalization. -/
@[aesop safe]
lemma sn_steps {t t' : Term Var} (t_st_t' : t ↠βᶠ t') (sn_t : SN t) : SN t' := by
  induction t_st_t' with grind[sn_step]

/-- Free variables are strongly normalizing. -/
lemma sn_fvar {x : Var} : SN (Term.fvar x) := by
  constructor
  intro t' hstep
  cases hstep

/-- An application is strongly normalizing if the left and right terms are strongly normalizing,
    as well as all possible future top level abstraction application beta reductions -/
lemma sn_app (t s : Term Var)
  (sn_t : SN t)
  (sn_s : SN s)
  (hβ : ∀ {t' s' : Term Var}, t ↠βᶠ t'.abs → s ↠βᶠ s' → SN (t' ^ s')) :
    SN (t.app s) := by
  induction sn_t generalizing s with
  | sn t ht ih_t =>
    induction sn_s with
    | sn s hs ih_s =>
      constructor
      intro u hstep
      cases hstep with
      | beta _ _       => grind
      | appL _ h_s_red => apply ih_s _ h_s_red
                          grind[Relation.ReflTransGen.head]
      | appR _ h_t_red => apply ih_t _ h_t_red _ (SN.sn s hs)
                          grind[Relation.ReflTransGen.head]


/-- The left side of a strongly normalizing application is strongly normalizing. -/
lemma sn_app_left (M N : Term Var)
  (lc_N : Term.LC N)
  (sn_MN : SN (M.app N)) :
    SN M := by
  generalize Heq : M.app N = P
  rw[Heq] at sn_MN
  revert M N
  induction sn_MN
  · case sn P h_sn ih =>
    intro M N lc_N Heq
    rw[←Heq] at ih
    constructor
    intro M' h_step
    apply ih (M'.app N)
    apply Term.FullBeta.appR <;> assumption
    · assumption
    · rfl

/-- The right side of a strongly normalizing application is strongly normalizing. -/
lemma sn_app_right (M N : Term Var)
  (lc_N : Term.LC M)
  (sn_MN : SN (M.app N)) :
    SN N := by
  generalize Heq : M.app N = P
  rw[Heq] at sn_MN
  revert M N
  induction sn_MN
  · case sn P h_sn ih =>
    intro M N lc_N Heq
    rw[←Heq] at ih
    constructor
    intro N' h_step
    apply ih (M.app N')
    apply Term.FullBeta.appL <;> assumption
    · assumption
    · rfl


/-- A neutral term is a term of the form v t₁ … t_n where
    v is a variable and t₁ … t_n are strongly normalizing terms. -/
inductive neutral : Term Var → Prop
/-- Just a bound variable is neutral. -/
| bvar : ∀ n, neutral (Term.bvar n)
/-- Just a free variable is neutral. -/
| fvar : ∀ x, neutral (Term.fvar x)
/-- Applying a strongly normalizing term to a neutral term yields a neutral term. -/
| app : ∀ t1 t2, neutral t1 → SN t2 → neutral (Term.app t1 t2)

attribute [scoped grind .] neutral.bvar neutral.fvar neutral.app

/-- Neutral terms only reduce to other neutral terms in a single step -/
lemma neutral_step {t t' : Term Var}
  (Hneut : neutral t) (Hstep : t ⭢βᶠ t') : neutral t' := by
  induction Hneut generalizing t' <;> cases Hstep <;> try grind [sn_step]
  · contradiction

/-- Neutral terms only reduce to other neutral terms in multiple steps -/
lemma neutral_steps {t t' : Term Var}
    (Hneut : neutral t) (Hsteps : t ↠βᶠ t') : neutral t' := by
  induction Hsteps <;> grind [neutral_step]

/-- Neutral terms are strongly normalizing. -/
lemma sn_neutral {t : Term Var} (Hneut : neutral t) : SN t := by
  induction Hneut
  · case bvar n => constructor; intro t' hstep; cases hstep
  · case fvar x => constructor; intro t' hstep; cases hstep
  · case app t1 t'_neut t1_sn t1'_sn =>
      apply sn_app <;> try assumption
      intro t1' t2' hstep1 hstep2
      have H_neut := neutral_steps t'_neut hstep1
      contradiction

/-- A lambda abstraction is strongly normalizing if its body is strongly normalizing. -/
lemma sn_abs [DecidableEq Var] [HasFresh Var] {M N : Term Var}
  (sn_MN : SN (M ^ N)) (lc_N : LC N) : SN (Term.abs M) := by
  generalize h : (M ^ N) = M_open at sn_MN
  revert N M
  induction sn_MN with
  | sn M_open h_sn ih =>
      intro M N lc_N h
      constructor
      intro M' h_step
      cases h_step with
      | @abs h_M_red M' L H =>
        specialize ih (M' ^ N)
        rw[←h] at ih
        apply ih
        · apply FullBeta.step_open_cong_l <;> assumption
        · assumption
        · rfl



/-- A term of the form λ M N P_1 … P_n is strongly normalizing if
      1. N is strongly normalizing,
      1. M ^ N P₁ … Pₙ is strongly normalizing,
      1. N is locally closed,
      1. M ^ N P₁ … Pₙ is locally closed -/
lemma sn_abs_app_multiApp [DecidableEq Var] [HasFresh Var] {Ps} {M N : Term Var}
  (sn_N : SN N)
  (sn_MNPs : SN (multiApp (M ^ N) Ps))
  (lc_N : LC N)
  (lc_MNPs : LC (multiApp (M ^ N) Ps)) :
    SN (multiApp ((Term.abs M).app N) Ps) := by
  induction Ps
  · case nil =>
      apply sn_app
      · grind [sn_abs]
      · assumption
      · intro M' N' hstep1 hstep2
        have Hmst : (M ^ N) ↠βᶠ (M' ^ N') := by
          grind [FullBeta.steps_open_cong_abs, open_abs_lc]
        grind [sn_steps]
  · case cons P Ps ih =>
      cases lc_MNPs
      apply sn_app
      · grind [sn_app_left]
      · grind [sn_app_right]
      · intro Q' P' hstep1 hstep2
        match (Term.invert_abs_multiApp_mst hstep1) with
        | ⟨ M', N', Ps', h_M_red, h_N_red, h_Ps_red, h_cases ⟩ =>
          match h_cases with
          | Or.inl h_P => cases Ps' <;> rw[multiApp] at h_cases <;> contradiction
          | Or.inr ⟨ h_st1, h_st2 ⟩ =>
            have innerSteps :=
              calc
                (M ^ N).multiApp Ps ↠βᶠ (multiApp (M ^ N) Ps') := by
                  grind [steps_multiApp_r, FullBeta.steps_open_cong_abs, open_abs_lc]
                _                   ↠βᶠ (M' ^ N').multiApp Ps' := by
                  grind [steps_multiApp_l,
                         multiApp_steps_lc,
                         multiApp_lc,
                         FullBeta.steps_open_cong_abs,
                         open_abs_lc]
                _                   ↠βᶠ Q'.abs := by
                  grind [steps_multiApp_l]
            have lc_abs_Q' : LC (Q'.abs) := by grind [FullBeta.steps_lc_or_rfl]
            apply sn_steps _ sn_MNPs
            calc
              (multiApp (M ^ N) Ps).app P ↠βᶠ Q'.abs.app P  := by grind
              _                           ↠βᶠ Q'.abs.app P' := by grind
              _                           ↠βᶠ Q' ^ P'       := by grind [FullBeta.beta]

end LambdaCalculus.LocallyNameless.Untyped.Term

end Cslib
