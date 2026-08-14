/-
Copyright (c) 2026 Haoxuan Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Haoxuan Yin, Fabrizio Montesi
-/

module

public import Cslib.Languages.LambdaCalculus.Named.Untyped.Basic

/-! # λ-calculus

The untyped λ-calculus, with a named representation of variables. This file contains properties of
α-equivalence and capture-avoiding substitution.

## Main results

- `AlphaEquiv.refl`: reflexivity of α-equivalence
- `AlphaEquiv.symm`: symmetry of α-equivalence
- `AlphaEquiv.trans`: transitivity of α-equivalence
- `Subst.relation_iff_function`: the relational and functional definition of capture-avoiding
  substitution are equivalent, modulo alpha-equivalence
- `subst.commutativity`: commutativity of substitution, more commonly known as the
  "substitution lemma" (e.g. in [Barendregt1984])
-/

public section

namespace Cslib

universe u

variable {Var : Type u} [DecidableEq Var]

namespace LambdaCalculus.Named.Untyped.Term

/-- A variable in a term is either free or bound. -/
theorem vars_either_fv_or_bv {m : Term Var} : m.vars = m.fv ∪ m.bv := by
  induction m <;> grind

/-- Renaming an unused variable has no effect. -/
@[simp, scoped grind =]
theorem rename_unused {m : Term Var} {x y : Var} : x ∉ m.vars → m.rename x y = m := by
  induction m <;> grind

/-- Renaming a variable to itself has no effect. -/
@[simp, scoped grind =]
theorem rename_same {m : Term Var} {x : Var} : m.rename x x = m := by
  induction m <;> grind

/-- Renaming a used variable changes the set of variables. -/
theorem rename_vars_used {m : Term Var} {x y : Var} : x ∈ m.vars →
    (m.rename x y).vars = m.vars.erase x ∪ {y} := by
  induction m with
  | var z => grind
  | abs z m ih =>
    intro hx
    by_cases hxm : x ∈ m.vars <;> grind
  | app m n ihm ihn =>
    intro hx
    by_cases hxm : x ∈ m.vars
    · by_cases hxn : x ∈ n.vars <;> grind
    · grind

/-- Renaming removes the variable. -/
theorem rename_remove {m : Term Var} {x y : Var} : x ≠ y → x ∉ (m.rename x y).vars := by
  intro hxy
  by_cases hx : x ∈ m.vars <;> grind [rename_vars_used]

/-- The set of variables after renaming. -/
@[simp, scoped grind =]
theorem rename_vars {m : Term Var} {x y : Var} :
    (m.rename x y).vars = m.vars \ {x} ∪ (if x ∈ m.vars then {y} else ∅) := by
  grind [rename_vars_used]

/-- The set of free variables after renaming. -/
theorem rename_fv {m : Term Var} {x y : Var} :
    y ∉ m.vars → (m.rename x y).fv = m.fv \ {x} ∪ (if x ∈ m.fv then {y} else ∅) := by
  induction m with
  | var z => grind
  | abs z m ih => grind [vars_either_fv_or_bv]
  | app m n ihm ihn => grind

/-- Concatenation of renaming. -/
@[simp, scoped grind =]
theorem rename_concat {m : Term Var} {x y z : Var} : y ∉ m.vars →
    (m.rename x y).rename y z = m.rename x z := by
  induction m <;> grind

/-- Commutativity of renaming distinct variables. -/
theorem rename_comm_fresh {m : Term Var} {x y z w : Var} :
    x ≠ z → y ∉ m.vars ∪ {x, z} → w ∉ m.vars ∪ {x, z} →
    (m.rename x y).rename z w = (m.rename z w).rename x y := by
  induction m <;> grind

/-- Commutativity of renaming. -/
theorem rename_comm {m : Term Var} {x y z w : Var} :
    y ∉ m.vars ∪ {x, z} → w ∉ m.vars ∪ {x, y, z} →
    (m.rename x y).rename (if z = x then y else z) w = (m.rename z w).rename x y := by
  grind [rename_comm_fresh]

omit [DecidableEq Var] in
theorem induction_by_sizeOf {C : Term Var → Prop}
    (step : ∀ m : Term Var, (∀ m1 : Term Var, sizeOf m1 < sizeOf m → C m1) → C m ) :
    ∀ m : Term Var, C m :=
  WellFounded.fix (r := sizeOfWFRel.rel) sizeOfWFRel.wf step

end LambdaCalculus.Named.Untyped.Term

end Cslib
