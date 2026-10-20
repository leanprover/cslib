/-
Copyright (c) 2026 Haoxuan Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Haoxuan Yin, Fabrizio Montesi
-/

module

public import Cslib.Languages.LambdaCalculus.Named.Untyped.Basic

/-! # Properties of rename

The untyped λ-calculus, with a named representation of variables. This file contains properties of
α-equivalence and capture-avoiding substitution.
-/

public section

namespace Cslib

universe u

variable {Var : Type u} [DecidableEq Var]

namespace LambdaCalculus.Named.Untyped.Term

/-- A variable in a term is either free or bound. -/
theorem vars_eq_fv_union_bv {m : Term Var} : m.vars = m.fv ∪ m.bv := by
  induction m <;> grind

/-- Renaming an unused variable has no effect. -/
@[simp, scoped grind =]
theorem rename_of_notMem_vars {m : Term Var} {x y : Var} (hx : x ∉ m.vars) :
    m.rename x y = m := by
  induction m <;> grind

/-- Renaming a variable to itself has no effect. -/
@[simp, scoped grind =]
theorem rename_self {m : Term Var} {x : Var} : m.rename x x = m := by
  induction m <;> grind

/-- Renaming a used variable changes the set of variables. -/
theorem vars_rename_of_mem {m : Term Var} {x y : Var} (hx : x ∈ m.vars) :
    (m.rename x y).vars = m.vars.erase x ∪ {y} := by
  induction m with
  | var z => grind
  | abs z m ih => by_cases hxm : x ∈ m.vars <;> grind
  | app m n ihm ihn =>
    by_cases hxm : x ∈ m.vars
    · by_cases hxn : x ∈ n.vars <;> grind
    · grind

/-- Renaming removes the variable. -/
theorem notMem_vars_rename {m : Term Var} {x y : Var} (hxy : x ≠ y) :
    x ∉ (m.rename x y).vars := by
  by_cases hx : x ∈ m.vars <;> grind [vars_rename_of_mem]

/-- The set of variables after renaming. -/
@[simp, scoped grind =]
theorem vars_rename {m : Term Var} {x y : Var} :
    (m.rename x y).vars = m.vars \ {x} ∪ (if x ∈ m.vars then {y} else ∅) := by
  grind [vars_rename_of_mem]

/-- The set of free variables after renaming. -/
theorem fv_rename {m : Term Var} {x y : Var} (hy : y ∉ m.vars) :
    (m.rename x y).fv = m.fv \ {x} ∪ (if x ∈ m.fv then {y} else ∅) := by
  induction m with
  | var z => grind
  | abs z m ih => grind [vars_eq_fv_union_bv]
  | app m n ihm ihn => grind

/-- Concatenation of renaming. -/
@[simp, scoped grind =]
theorem rename_rename {m : Term Var} {x y z : Var} (hy : y ∉ m.vars) :
    (m.rename x y).rename y z = m.rename x z := by
  induction m <;> grind

/-- Commutativity of renaming distinct variables. -/
theorem rename_comm_of_ne {m : Term Var} {x y z w : Var} (hxz : x ≠ z)
    (hy : y ∉ m.vars ∪ {x, z}) (hw : w ∉ m.vars ∪ {x, z}) :
    (m.rename x y).rename z w = (m.rename z w).rename x y := by
  induction m <;> grind

/-- Commutativity of renaming. -/
theorem rename_comm {m : Term Var} {x y z w : Var} (hy : y ∉ m.vars ∪ {x, z})
    (hw : w ∉ m.vars ∪ {x, y, z}) :
    (m.rename x y).rename (if z = x then y else z) w = (m.rename z w).rename x y := by
  grind [rename_comm_of_ne]

end LambdaCalculus.Named.Untyped.Term

end Cslib
