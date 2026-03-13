/-
Copyright (c) 2026 Maximiliano Onofre Martínez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maximiliano Onofre Martínez
-/

module

public import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.FullEta

@[expose] public section

set_option linter.unusedDecidableInType false

/-! # η-confluence for the λ-calculus

## Reference

* [T. Nipkow, *More Church-Rosser Proofs (in Isabelle/HOL)*][Nipkow2001]

-/

namespace Cslib

universe u

variable {Var : Type u}

namespace LambdaCalculus.LocallyNameless.Untyped.Term

open Relation

variable [HasFresh Var] [DecidableEq Var]

open FullEta in
lemma stronglyConfluent_eta : StronglyConfluent (@FullEta Var) := by
  intro _ y z h₁ h₂
  suffices ∃ w, ReflGen FullEta y w ∧ ReflGen FullEta z w by grind
  induction h₁ generalizing z
  case appL Z _ N _ _ ih =>
    cases h₂
    case appL _ _ st =>
      obtain ⟨w, _, _⟩ := ih st
      use (disch := grind) app Z w
      grind
    case appR z_red _ _ =>
      use app z_red N
      grind
  case appR M _ Z _ _ ih =>
    cases h₂
    case appR _ st _ =>
      obtain ⟨w, _, _⟩ := ih st
      use app w M
      grind
    case appL z_red _ _ =>
      use app Z z_red
      grind
  case eta M lc_M =>
    cases h₂
    case eta => exact ⟨M, .refl, .refl⟩
    case abs N L st_body =>
      have ⟨w, hw⟩ := fresh_exists (L ∪ N.fv ∪ M.fv)
      simp only [Finset.mem_union, not_or] at hw
      rcases hw with ⟨⟨hw_L, hw_N⟩, _⟩
      rcases invert_step_app_fvar (st_body w hw_L) with ⟨M', h_eq, st_M_open⟩
      use M'
      constructor
      · grind
      have hw_M_open : w ∉ (M ^ fvar w).fv := by grind
      have hw_M' := step_not_fv st_M_open hw_M_open
      have lc_M' := step_lc_r st_M_open
      rw [open_eq_app hw_N hw_M' lc_M' h_eq]
      exact .single <| eta (step_lc_r st_M_open)
  case abs M N L ih₁ ih₂ =>
    cases h₂
    case eta z _ =>
      have ⟨w, hw⟩ := fresh_exists (L ∪ N.fv ∪ z.fv)
      simp only [Finset.mem_union, not_or] at hw
      rcases hw with ⟨⟨hw_L, hw_N⟩, hw_z⟩
      have st_body := ih₁ w hw_L
      have eq_z : z ^ fvar w = z := by grind
      have eq_app : (app z (bvar 0)) ^ fvar w = app z (fvar w) := by grind
      rw [eq_app] at st_body
      rcases invert_step_app_fvar st_body with ⟨z', h_eq, st_z⟩
      use z'
      constructor
      · have lc_z' := step_lc_r st_z
        have hw_z' := step_not_fv st_z hw_z
        rw [open_eq_app hw_N hw_z' lc_z' h_eq]
        exact .single (eta lc_z')
      · exact .single st_z
    case abs N2 L2 st_M_N2 =>
      have ⟨x, hx⟩ := fresh_exists (L ∪ L2 ∪ N.fv ∪ N2.fv)
      simp only [Finset.mem_union, not_or] at hx
      rcases hx with ⟨⟨⟨hx_L, hx_L2⟩, hx_N⟩, hx_N2⟩
      obtain ⟨w, hw_N, hw_N2⟩ := ih₂ x hx_L (st_M_N2 x hx_L2)
      use abs (w⟦0 ↜ x⟧)
      exact ⟨close_eta_steps hx_N hw_N, close_eta_steps hx_N2 hw_N2⟩

end LambdaCalculus.LocallyNameless.Untyped.Term

end Cslib
