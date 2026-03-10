/-
Copyright (c) 2026 Haoxuan Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Haoxuan Yin
-/

module

public import Cslib.Languages.LambdaCalculus.Named.Untyped.Basic

public section

namespace Cslib

universe u

variable {Var : Type u}

namespace LambdaCalculus.Named

open Term

/-- A variable in a term is either free or bound. -/
lemma Term.vars_either_fv_or_bv [DecidableEq Var] (m : Term Var) :
    m.vars = m.fv ∪ m.bv := by
  induction m <;> grind [Term.fv, Term.bv, Term.vars]

/-- Renaming an unused variable has no effect. -/
lemma Term.rename_unused [DecidableEq Var] (m : Term Var) (x y : Var) :
  x ∉ m.vars → m.rename x y = m := by
  induction m <;> grind [Term.vars, Term.rename]

/-- Renaming changes the set of variables. -/
lemma Term.rename_vars [DecidableEq Var] (m : Term Var) (x y : Var) :
  x ∈ m.vars → (m.rename x y).vars = m.vars.erase x ∪ {y} := by
  induction m with
  | var z => grind [Term.vars, Term.rename]
  | abs z m ih =>
    intro hx
    by_cases hxm : x ∈ m.vars <;> grind [Term.vars, Term.rename, Term.rename_unused]
  | app m n ihm ihn =>
    intro hx
    by_cases hxm : x ∈ m.vars
    · by_cases hxn : x ∈ n.vars
      · grind [Term.vars, Term.rename]
      · grind [Term.vars, Term.rename, Term.rename_unused]
    · have hxn : x ∈ n.vars := by
        grind [Term.vars]
      grind [Term.vars, Term.rename, Term.rename_unused]

/-- Concatenation of renaming. -/
lemma Term.rename_concat [DecidableEq Var] (m : Term Var) (x y z : Var) :
  y ∉ m.vars → (m.rename x y).rename y z = m.rename x z := by
  induction m <;> grind [Term.vars, Term.rename]

end LambdaCalculus.Named

end Cslib
