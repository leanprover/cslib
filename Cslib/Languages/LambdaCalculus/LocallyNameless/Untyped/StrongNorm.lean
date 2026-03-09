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

attribute [grind =] Finset.union_singleton

/-- A term is strongly normalizing if every reduction sequence terminates at some point.
    This is ensured by the following type as inductive data must always be finite. -/
inductive SN {α} : Term α → Prop
| sn t : (∀ (t' : Term α), (t ⭢βᶠ t') → SN t') → SN t

/-- A single β-reduction step preserves strong normalization. -/
@[aesop safe]
lemma sn_step {t t' : Term Var} (t_st_t' : t ⭢βᶠ t') (sn_t : SN t) : SN t' := by
  cases sn_t; grind

/-- Multiple β-reduction steps also preserve strong normalization. -/
@[aesop safe]
lemma sn_steps {t t' : Term Var} (t_st_t' : t ↠βᶠ t') (sn_t : SN t) : SN t' := by
  induction t_st_t' <;> grind[sn_step]

/-- Free variables are strongly normalizing. -/
lemma sn_fvar {x : Var} : SN (Term.fvar x) := by
  constructor
  intro t' hstep
  cases hstep

/-- An application is strongly normalizing if the left and right terms are strongly normalizing,
    as well as all possible future top level abstraction application beta reductions -/
lemma sn_app (t s : Term Var) :
  SN t →
  SN s →
  (∀ {t' s' : Term Var}, t ↠βᶠ t'.abs → s ↠βᶠ s' → SN (t' ^ s')) →
  SN (t.app s) := by
  intro h_sn_t h_sn_s hβ
  induction h_sn_t generalizing s with | sn t ht ih_t =>
  induction h_sn_s with | sn s hs ih_s =>
  constructor
  intro u hstep
  cases hstep with
  | beta _ _ => apply hβ <;> rfl
  | appL _ h_s_red =>
    apply ih_s _ h_s_red
    intro t' s'' hstep1 hstep2
    exact hβ hstep1 (Relation.ReflTransGen.head h_s_red hstep2)
  | appR _ h_t_red =>
    apply ih_t _ h_t_red _ (SN.sn s hs)
    intro t' s' hstep1 hstep2
    exact hβ (Relation.ReflTransGen.head h_t_red hstep1) hstep2


/-- The left side of a strongly normalizing application is strongly normalizing. -/
lemma sn_app_left (M N : Term Var) : Term.LC N → SN (M.app N) → SN M := by
  intro lc_N h_sn
  generalize Heq : M.app N = P
  rw[Heq] at h_sn
  revert M N
  induction h_sn
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
lemma sn_app_right (M N : Term Var) : Term.LC M → SN (M.app N) → SN N := by
  intro lc_N h_sn
  generalize Heq : M.app N = P
  rw[Heq] at h_sn
  revert M N
  induction h_sn
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
@[aesop safe]
lemma neutral_step {t t' : Term Var}
  (Hneut : neutral t) (Hstep : t ⭢βᶠ t') : neutral t' := by
  induction Hneut generalizing t' <;> cases Hstep <;> try grind[sn_step]
  · contradiction

/-- Neutral terms only reduce to other neutral terms in multiple steps -/
@[aesop safe]
lemma neutral_steps {t t' : Term Var}
    (Hneut : neutral t) (Hsteps : t ↠βᶠ t') : neutral t' := by
  induction Hsteps <;> grind[neutral_step]

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
lemma sn_abs [DecidableEq Var] [HasFresh Var] : ∀ {M N : Term Var},
  SN (M ^ N) → LC N → SN (Term.abs M) := by
  intro M N sn_M lc_N
  generalize h : (M ^ N) = M_open at sn_M
  revert N M
  induction sn_M with
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
lemma sn_multiApp [DecidableEq Var] [HasFresh Var] : ∀ {Ps} {M N : Term Var},
  SN N →
  SN (multiApp (M ^ N) Ps) →
  LC N →
  LC (multiApp (M ^ N) Ps) →
  -------------------------------------
  SN (multiApp ((Term.abs M).app N) Ps) := by
  intro P
  induction P <;> intros M N sn_N sn_MNPs lc_N lc_MNPs
  · case nil =>
      apply sn_app
      · apply sn_abs at sn_MNPs
        simp_all
      · assumption
      · intro M' N' hstep1 hstep2
        have Hmst : (M ^ N) ↠βᶠ (M' ^ N') := by
          apply FullBeta.steps_open_cong_abs <;> try assumption
          apply open_abs_lc <;> assumption
        apply sn_steps <;> assumption
  · case cons P Ps ih =>
      apply sn_app
      · apply ih <;> try assumption
        · apply sn_app_left at sn_MNPs <;> try grind[Untyped.Term.multiApp_lc]
        · grind[Untyped.Term.multiApp_lc]
      · apply sn_app_right at sn_MNPs
        · assumption
        · cases lc_MNPs
          assumption
      · intro Q' P' hstep1 hstep2
        match (Term.invert_abs_multiApp_mst hstep1) with
        | ⟨ M', N', Ps', h_M_red, h_N_red, h_Ps_red, h_cases ⟩ =>
          match h_cases with
          | Or.inl h_P => cases Ps' <;> rw[multiApp] at h_cases <;> contradiction
          | Or.inr ⟨ h_st1, h_st2 ⟩ =>
            have H1 : (multiApp (M ^ N) Ps).app P ↠βᶠ Q' ^ P' := by
              have H2 : (multiApp (M ^ N) Ps) ↠βᶠ (M' ^ N').multiApp Ps' := by
                transitivity
                · apply steps_multiApp_r
                  · assumption
                  · rw[multiApp_lc] at lc_MNPs
                    simp_all
                · apply steps_multiApp_l
                  · rw[multiApp_lc] at lc_MNPs
                    apply FullBeta.steps_open_cong_abs M M' N N' <;> try assumption
                    · apply open_abs_lc
                      · apply lc_MNPs.1
                  · rw[multiApp_lc] at lc_MNPs
                    apply multiApp_steps_lc at h_Ps_red
                    simp_all
              have H3 : (multiApp (M ^ N) Ps) ↠βᶠ Q'.abs := by
                transitivity <;> try assumption
              have H4 : Q'.abs.app P' ↠βᶠ Q' ^ P' := by
                grind[FullBeta.beta, FullBeta.step_lc_r]
              have H4 : ((M ^ N).multiApp Ps).app P ↠βᶠ Q'.abs.app P' := by
                cases lc_MNPs
                transitivity
                · apply FullBeta.redex_app_r_cong <;> assumption
                · apply FullBeta.redex_app_l_cong <;> grind[FullBeta.step_lc_r]
              transitivity <;> try assumption
            apply sn_steps <;> try assumption


end LambdaCalculus.LocallyNameless.Untyped.Term

end Cslib
