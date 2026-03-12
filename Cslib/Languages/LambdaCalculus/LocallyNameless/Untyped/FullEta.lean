/-
Copyright (c) 2026 Maximiliano Onofre Martínez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maximiliano Onofre Martínez
-/

module

public import Cslib.Foundations.Data.Relation
public import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.Properties

public section

/-! # η-reduction for the λ-calculus -/

namespace Cslib

universe u

variable {Var : Type u}

namespace LambdaCalculus.LocallyNameless.Untyped.Term

/-- A single η-reduction step. -/
@[reduction_sys "ηᶠ"]
inductive FullEta : Term Var → Term Var → Prop
/-- The eta rule: λx. M x ⟶ M, provided x is not free in M. -/
| eta : LC M → FullEta (abs (app M (bvar 0))) M
/-- Left congruence rule for application. -/
| appL: LC Z → FullEta M N → FullEta (app Z M) (app Z N)
/-- Right congruence rule for application. -/
| appR : LC Z → FullEta M N → FullEta (app M Z) (app N Z)
/-- Congruence rule for lambda terms. -/
| abs (xs : Finset Var) : (∀ x ∉ xs, FullEta (M ^ fvar x) (N ^ fvar x)) → FullEta (abs M) (abs N)

namespace FullEta

attribute [scoped grind .] appL appR

variable {M M' : Term Var}

/-- The right side of an η-reduction is locally closed. -/
lemma step_lc_r (step : M ⭢ηᶠ M') : LC M' := by
  induction step
  case abs => constructor; assumption
  all_goals grind

variable [HasFresh Var] [DecidableEq Var]

/-- An η-reduction step does not introduce new free variables. -/
lemma step_not_fv (step : M ⭢ηᶠ M') (hw : w ∉ M.fv) : w ∉ M'.fv := by
  induction step with
  | abs =>
    have ⟨x, _⟩ := fresh_exists <| free_union [fv] Var
    have := open_close x
    grind [close_preserve_not_fvar, open_fresh_preserve_not_fvar]
  | _ => grind

end LambdaCalculus.LocallyNameless.Untyped.Term.FullEta

end Cslib
