/-
Copyright (c) 2026 Maximiliano Onofre Martínez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maximiliano Onofre Martínez
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
variable [HasFresh Var] [DecidableEq Var]

namespace LambdaCalculus.LocallyNameless.Untyped.Term

open Relation

/-- Full βη-reduction. -/
@[reduction_sys "βηᶠ"]
abbrev FullBetaEta : Term Var → Term Var → Prop := FullBeta ⊔ FullEta

open FullEta FullBeta in
/-- η-reduction and β-reduction strongly commute. -/
lemma stronglyCommute_eta_beta : StronglyCommute (@FullEta Var) FullBeta := by
  intro x y₁ y₂ h₁ st_beta
  induction st_beta generalizing y₁
  case base h1_b =>
    cases h1_b
    case beta M N _ _ =>
      cases h₁
      case base h => cases h
      case appL v _ _ =>
        use M ^ v
        grind [step_open_cong_r]
      case appR u st_eta_absM _ =>
        have := step_lc_r st_eta_absM
        cases st_eta_absM
        case base h => use (disch := grind) app u N
        case abs M_eta xs _ =>
          have ⟨_, hz⟩ := fresh_exists (xs ∪ N.fv ∪ M.fv ∪ M_eta.fv)
          use M_eta ^ N
          grind [step_subst_cong_l]
  case appL Z _ N _ _ ih =>
    cases h₁
    case base h => cases h
    case appL _ _ st =>
      use app Z (ih st).choose
      grind [FullEta.redex_app_r_cong]
    case appR z_red _ _ => use (disch := grind) app z_red N
  case appR M _ Z _ _ ih =>
    cases h₁
    case base h => cases h
    case appL z_red _ _ => use (disch := grind) app Z z_red
    case appR _ st _ =>
      use app (ih st).choose M
      grind [FullEta.redex_app_l_cong]
  case abs M N xs st_body_beta ih =>
    cases h₁
    case base h_eta =>
      cases h_eta with | eta =>
        have ⟨w, _⟩ := fresh_exists <| free_union [fv] Var
        have st_beta_w : app y₁ (fvar w) ⭢βᶠ N ^ fvar w := by grind [st_body_beta w]
        rcases invert_step_app_fvar st_beta_w with ⟨u', _, st_u⟩ | ⟨u1, _, _⟩
        · use u'
          grind [open_eq_app ?_ (step_not_fv st_u ?_)]
        · use abs u1
          grind [open_injective w N u1]
    case abs S ys st_body_eta =>
      have ⟨w, _⟩ := fresh_exists <| free_union [fv] Var
      obtain ⟨K, h_beta, h_eta⟩ := ih w (by grind) (st_body_eta w (by grind))
      use abs (K ^* w)
      constructor
      · cases h_beta with
        | refl => grind [open_close]
        | single => exact .single (Xi.abs {w} (by grind [FullBeta.redex_subst_cong]))
      · rw [open_close w N 0 (by grind)]
        exact FullEta.redex_abs_close h_eta (FullBeta.step_lc_r (st_body_beta w (by grind)))

open Commute in
/-- βη-reduction is confluent. -/
theorem confluent_beta_eta : Confluent (@FullBetaEta Var) := by
  apply join_confluent
  · exact confluence_beta
  · exact stronglyConfluent_eta.toConfluent
  exact symmetric stronglyCommute_eta_beta.toCommute

end LambdaCalculus.LocallyNameless.Untyped.Term

end Cslib
