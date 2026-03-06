module

public import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.FullBeta
public import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.MultiApp
public import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.LcAt

@[expose] public section

namespace Cslib

universe u

variable {Var : Type u} [DecidableEq Var] [HasFresh Var]


namespace LambdaCalculus.LocallyNameless.Untyped.Term

attribute [grind =] Finset.union_singleton


inductive SN {α} : Term α → Prop
| sn t : (∀ (t' : Term α), (t ⭢βᶠ t') → SN t') → SN t

@[aesop safe]
lemma sn_step {t t' : Term Var} (t_st_t' : t ⭢βᶠ t') (sn_t : SN t) : SN t' := by
  cases sn_t; grind

@[aesop safe]
lemma sn_mst {t t' : Term Var} (t_st_t' : t ↠βᶠ t') (sn_t : SN t) : SN t' := by
  induction t_st_t' <;> grind[sn_step]

lemma sn_fvar {x : Var} : SN (Term.fvar x) := by
  constructor
  intro t' hstep
  cases hstep

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

@[aesop safe constructors]
inductive neutral : Term Var → Prop
| bvar : ∀ n, neutral (Term.bvar n)
| fvar : ∀ x, neutral (Term.fvar x)
| app : ∀ t1 t2, neutral t1 → SN t2 → neutral (Term.app t1 t2)

@[aesop safe]
lemma neutral_step {t : Term Var} :
  neutral t → ∀ t', t ⭢βᶠ t' → neutral t' := by
  intro Hneut
  induction Hneut <;> intro t' step
  · case bvar n =>
      cases step
  · case fvar x =>
      cases step
  · case app IH Hneut =>
      cases step <;> try aesop
      · contradiction
      constructor
      · assumption
      · apply sn_step <;> assumption

@[aesop safe]
lemma neutral_mst {t t' : Term Var} :
  neutral t → t ↠βᶠ t' → neutral t' := by
  intro Hneut h_red
  induction h_red <;> aesop

lemma neutral_sn {t : Term Var} (Hneut : neutral t) : SN t := by
  induction Hneut
  · case bvar n => constructor; intro t' hstep; cases hstep
  · case fvar x => constructor; intro t' hstep; cases hstep
  · case app t1 t'_neut t1_sn t1'_sn =>
      apply sn_app <;> try assumption
      intro t1' t2' hstep1 hstep2
      have H_neut := neutral_mst t'_neut hstep1
      contradiction

lemma abs_sn : ∀ {M N : Term Var},
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
        · apply FullBeta.step_open_cong1 <;> assumption
        · assumption
        · rfl




lemma multiApp_sn : ∀ {Ps} {M N : Term Var},
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
      · apply abs_sn at sn_MNPs
        simp_all
      · assumption
      · intro M' N' hstep1 hstep2
        have Hmst : (M ^ N) ↠βᶠ (M' ^ N') := by
          apply FullBeta.steps_open_cong_abs <;> try assumption
          apply open_abs_lc <;> assumption
        apply sn_mst <;> assumption
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
        match (Term.invert_multiApp_mst hstep1) with
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
                grind[FullBeta.beta, FullBeta.steps_lc]
              have H4 : ((M ^ N).multiApp Ps).app P ↠βᶠ Q'.abs.app P' := by
                cases lc_MNPs
                transitivity
                · apply FullBeta.redex_app_r_cong <;> assumption
                · apply FullBeta.redex_app_l_cong <;> grind[FullBeta.step_lc_r]
              transitivity <;> try assumption
            apply sn_mst <;> try assumption


end LambdaCalculus.LocallyNameless.Untyped.Term

end Cslib
