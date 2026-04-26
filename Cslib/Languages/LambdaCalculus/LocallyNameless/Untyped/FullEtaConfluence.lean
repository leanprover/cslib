/-
Copyright (c) 2026 Maximiliano Onofre Martínez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maximiliano Onofre Martínez
-/

module

public import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.FullEta

/-! # η-confluence for the λ-calculus

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

variable [HasFresh Var] [DecidableEq Var]

open FullEta in
lemma stronglyConfluent_eta : StronglyConfluent (@FullEta Var) := by
  intro _ y z h₁ h₂
  suffices ∃ w, ReflGen FullEta y w ∧ ReflGen FullEta z w by grind
  induction h₁ generalizing z
  case base h1_b =>
    cases h1_b
    case eta M _ =>
      cases h₂
      case base => use (disch := grind) M
      case abs _ _ st_body =>
        have ⟨w, _⟩ := fresh_exists <| free_union [fv] Var
        have ⟨M', _, _⟩ := invert_step_app_fvar <| st_body w <| by grind
        use M'
        grind [→ Eta.eta, step_not_fv, open_eq_app]
  case appL Z _ N _ _ ih =>
    cases h₂
    case base h => cases h
    case appL _ _ st => use (disch := grind) app Z (ih st).choose
    case appR z_red _ _ => use (disch := grind) app z_red N
  case appR M _ Z _ _ ih =>
    cases h₂
    case base h => cases h
    case appR _ st _ => use (disch := grind) app (ih st).choose M
    case appL z_red _ _ => use (disch := grind) app Z z_red
  case abs _ _ _ st_M_N ih =>
    cases h₂
    case base h =>
      cases h with | eta lc_M =>
      have ⟨w, _⟩ := fresh_exists <| free_union [fv] Var
      have ⟨M', _, _⟩ := invert_step_app_fvar <| st_M_N w (by grind)
      use M'
      grind [→ Eta.eta, step_not_fv, open_eq_app]
    case abs N _ st_M_N =>
      have ⟨x, _⟩ := fresh_exists <| free_union [fv] Var
      have ⟨w, _⟩ := ih x (by grind) (z := N ^ fvar x) (st_M_N x (by grind))
      use abs (w ^* x)
      grind [close_eta_steps]

end LambdaCalculus.LocallyNameless.Untyped.Term

end Cslib
