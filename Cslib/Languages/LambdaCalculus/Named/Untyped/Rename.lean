/-
Copyright (c) 2026 Haoxuan Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Haoxuan Yin, Fabrizio Montesi, Chris Anto Fröschl
-/

module

public import Cslib.Languages.LambdaCalculus.Named.Untyped.Basic

/-! # Properties of rename and permute

The untyped λ-calculus, with a named representation of variables. This file contains properties of
the renaming `m.rename x y`, of the permutation action `m.permute π`, and of its special case, the
swap `m.swap x y`. Unlike renaming, swapping exchanges `x` and `y` in both directions, so it is
invertible; using it to define α-equivalence goes back to [Gabbay2002].

## Main results

- `permute_eq_of_eqOn_vars`: Lemma 6.2 part 1 of [Crole2012], permutations that agree on the
  variables of a term act on it in the same way
- `swap_eq_rename_of_notMem_vars`: swapping with an atom that does not occur in a term is renaming

## References

* [Roy L. Crole, *Alpha equivalence equalities*][Crole2012], Sections 2 and 6
* [M. Gabbay and A. Pitts, *A New Approach to Abstract Syntax with Variable
  Binding*][Gabbay2002], Section 2
-/

public section

namespace Cslib

universe u

variable {Var : Type u} [DecidableEq Var]

namespace LambdaCalculus.Named.Untyped.Term

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
    (m.rename x y).vars = m.vars.erase x ∪ (if x ∈ m.vars then {y} else ∅) := by
  grind [vars_rename_of_mem]

/-- The set of free variables after renaming. -/
theorem fv_rename {m : Term Var} {x y : Var} (hy : y ∉ m.vars) :
    (m.rename x y).fv = m.fv.erase x ∪ (if x ∈ m.fv then {y} else ∅) := by
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

omit [DecidableEq Var] in
/-- The identity permutation acts trivially. -/
@[simp]
lemma permute_refl (m : Term Var) : m.permute (Equiv.refl Var) = m := by
  induction m <;> simp_all [permute]

omit [DecidableEq Var] in
/-- Permuting successively by `π` and `π'` is permutation by their composition. -/
lemma permute_permute (m : Term Var) (π π' : Equiv.Perm Var) :
    (m.permute π).permute π' = m.permute (π.trans π') := by
  induction m <;> simp_all [permute]

omit [DecidableEq Var] in
/-- Permuting a term preserves its size. -/
@[simp]
lemma sizeOf_permute (m : Term Var) (π : Equiv.Perm Var) : sizeOf (m.permute π) = sizeOf m := by
  induction m <;> simp_all [permute]

/-- Permuting a term transports its free variables pointwise. -/
lemma fv_permute (m : Term Var) (π : Equiv.Perm Var) :
    (m.permute π).fv = m.fv.image π := by
  induction m with
  | var x => simp [permute, fv]
  | app m n ihm ihn => simp [permute, fv, ihm, ihn, Finset.image_union]
  | abs x m ih => simp [permute, fv, ih, Finset.image_erase π.injective]

/-- Permuting a term transports its variables pointwise. -/
lemma vars_permute (m : Term Var) (π : Equiv.Perm Var) :
    (m.permute π).vars = m.vars.image π := by
  induction m <;> simp_all [permute, Finset.image_union]

/-- Permuting commutes with renaming, up to the action on the renamed variables. -/
lemma permute_rename (m : Term Var) (π : Equiv.Perm Var) (x y : Var) :
    (m.rename x y).permute π = (m.permute π).rename (π x) (π y) := by
  induction m <;> simp_all [permute, rename, apply_ite]

/-- Lemma 6.2 part 1 [Crole2012]: permutations that agree on the variables of a term act on it
in the same way. The paper's hypothesis `occ(E) ⊆ AS(π, π')` is `Set.EqOn π π' m.vars`. -/
lemma permute_eq_of_eqOn_vars (m : Term Var) (π π' : Equiv.Perm Var)
    (h : Set.EqOn π π' m.vars) : m.permute π = m.permute π' := by
  induction m with
  | var x => simpa [permute] using h
  | abs x m ih =>
    simp only [vars, Finset.coe_union, Finset.coe_singleton, Set.eqOn_union,
      Set.eqOn_singleton] at h
    simp [permute, ih h.1, h.2]
  | app m n ihm ihn =>
    simp only [vars, Finset.coe_union, Set.eqOn_union] at h
    simp [permute, ihm h.1, ihn h.2]

/- Most properties of `swap` are instances of the corresponding property of `permute`. -/

/-- A transposition acts on terms in the same way as `Term.swap`. -/
lemma permute_swap (m : Term Var) (x y : Var) : m.permute (Equiv.swap x y) = m.swap x y := rfl

/-- Swapping a variable with itself has no effect. -/
@[simp]
lemma swap_self {m : Term Var} {x : Var} : m.swap x x = m := by
  simp [swap]

/-- Swapping `x` and `y` is the same as swapping `y` and `x`. -/
lemma swap_comm {m : Term Var} {x y : Var} : m.swap x y = m.swap y x := by
  rw [swap, swap, Equiv.swap_comm]

/-- Swapping the same two variables twice has no effect. -/
@[simp]
lemma swap_swap {m : Term Var} {x y : Var} : (m.swap x y).swap x y = m := by
  simp [swap, permute_permute]

/-- Swapping preserves size. -/
@[simp]
lemma sizeOf_swap {m : Term Var} {x y : Var} : sizeOf (m.swap x y) = sizeOf m :=
  sizeOf_permute ..

/-- Swapping two unused variables has no effect. -/
@[simp]
lemma swap_of_notMem_vars {m : Term Var} {x y : Var} (hx : x ∉ m.vars) (hy : y ∉ m.vars) :
    m.swap x y = m := by
  rw [swap, permute_eq_of_eqOn_vars m _ (Equiv.refl Var), permute_refl]
  grind [Set.EqOn]

/-- When `y ∉ m.vars`, `swap x y` and `rename x y` coincide.

This is because `rename x y` only changes `x` to `y` (not `y` to `x`), and when `y` does
not occur in `m`, swapping and renaming produce the same result. -/
lemma swap_eq_rename_of_notMem_vars {m : Term Var} {x y : Var}
    (hy : y ∉ m.vars) : m.swap x y = m.rename x y := by
  induction m <;> grind [swap, rename, vars, permute]

/-- The set of free variables after a swap. -/
lemma fv_swap {m : Term Var} {x y : Var} : (m.swap x y).fv = m.fv.image (Equiv.swap x y) :=
  fv_permute ..

/-- Swapping preserves non-membership in `fv`. -/
lemma notMem_fv_swap {m : Term Var} {x y z : Var} (hzx : z ≠ x) (hzy : z ≠ y) (hzm : z ∉ m.fv) :
    z ∉ (m.swap x y).fv := by
  grind [fv_swap]

/-- The set of vars after a swap. -/
lemma vars_swap {m : Term Var} {x y : Var} : (m.swap x y).vars = m.vars.image (Equiv.swap x y) :=
  vars_permute ..

/-- Swapping preserves non-membership in `vars`. -/
lemma notMem_vars_swap {m : Term Var} {x y z : Var}
    (hzx : z ≠ x) (hzy : z ≠ y) (hzm : z ∉ m.vars) : z ∉ (m.swap x y).vars := by
  grind [vars_swap]

/-- `swap` and `rename` commute (modulo the permutation action on the variable arguments). -/
lemma swap_rename_comm {m : Term Var} {u v x y : Var} :
    (m.swap u v).rename (Equiv.swap u v x) (Equiv.swap u v y) = (m.rename x y).swap u v :=
  (permute_rename ..).symm

/-- Lemma 6.2 part 1 [Crole2012] (specialized to transpositions). -/
lemma swap_comp_eq_of_notMem_vars {m : Term Var} {a u z : Var}
    (hu : u ∉ m.vars) (hz : z ∉ m.vars) :
    (m.swap u a).swap z u = m.swap z a := by
  rw [swap, swap, permute_permute]
  apply permute_eq_of_eqOn_vars
  grind [Set.EqOn]

/-- Term-level conjugation identity: `(m.swap u v).swap v a = (m.swap u a).swap u v`
when `a ∉ {u, v}`.

Unlike `swap_comp_eq_of_notMem_vars`, this holds unconditionally (no freshness needed). -/
lemma swap_comp_eq_of_ne {m : Term Var} {a u v : Var} (hau : a ≠ u) (hav : a ≠ v) :
    (m.swap u v).swap v a = (m.swap u a).swap u v := by
  simp only [swap, permute_permute]
  congr 1
  grind

end LambdaCalculus.Named.Untyped.Term

end Cslib
