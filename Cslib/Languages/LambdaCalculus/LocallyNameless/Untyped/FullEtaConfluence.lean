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
    case eta => use M
    case abs N L st_body =>
      have ⟨w, _⟩ := fresh_exists <| free_union [fv] Var
      have ⟨M', _⟩ := invert_step_app_fvar <| st_body w <| by grind
      use M'
      grind [→ eta, step_not_fv, open_eq_app]
  case abs M N L ih₁ ih₂ =>
    cases h₂
    case eta z _ =>
      have ⟨w,  _⟩ := fresh_exists <| free_union [fv] Var
      have ⟨z', _⟩ := invert_step_app_fvar <| ih₁ w <| by grind
      use z'
      grind [→ eta, step_not_fv, open_eq_app]
    case abs N2 L2 st_M_N2 =>
      have ⟨x, hx⟩ := fresh_exists (L ∪ L2 ∪ N.fv ∪ N2.fv)
      simp only [Finset.mem_union, not_or] at hx
      rcases hx with ⟨⟨⟨hx_L, hx_L2⟩, hx_N⟩, hx_N2⟩
      obtain ⟨w, hw_N, hw_N2⟩ := ih₂ x hx_L (st_M_N2 x hx_L2)
      use abs (w⟦0 ↜ x⟧)
      exact ⟨close_eta_steps hx_N hw_N, close_eta_steps hx_N2 hw_N2⟩

end LambdaCalculus.LocallyNameless.Untyped.Term

end Cslib
