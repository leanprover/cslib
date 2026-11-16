/-
Copyright (c) 2026 Chris Anto Fröschl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Anto Fröschl
-/

module

public import Cslib.Languages.LambdaCalculus.Named.Untyped.Basic
public import Cslib.Languages.LambdaCalculus.Named.Untyped.AlphaEquivVariants.Defs
public import Cslib.Languages.LambdaCalculus.Named.Untyped.AlphaEquivProperties

/-! # Properties of permutations and swaps (transpositions) on lambda terms

Lemmas about the permutation action `Term.permute` and its special case `Term.swap`, and their
interaction with `AlphaEquiv`, `rename`, `vars`, and `fv`.

The notion of *atom swapping* (transposition) as the basis for defining α-equivalence
originates from [Gabbay and Pitts, *A New Approach to Abstract Syntax with Variable
Binding*][Gabbay2002] (Section 2, page 3). The key observation is that α-equivalence can
be defined using the notion of atom swapping in lieu of the traditional
renaming/substitution approach.

The swap (transposition) operation `m.swap x y` implements the permutation action
`(x y) · E` from [Crole2012] (Section 2). It simultaneously replaces all occurrences
of `x` with `y` and vice versa throughout a term.

## Main results

- `permute_eq_of_eqOn_vars`: Lemma 6.2 part 1 of [Crole2012], permutations that agree on the
  variables of a term act on it in the same way
- `AlphaEquiv.permute_preserve`: permutations preserve α-equivalence
- `AlphaEquiv.swap_preserve`: Lemma 6.1 of [Crole2012], swapping preserves α-equivalence
- `permute_alphaEquiv_of_eqOn_fv`: Lemma 6.2 part 2 of [Crole2012], permutations that agree on the
  free variables of a term act on it in the same way up to α-equivalence

## References

* [Roy L. Crole, *Alpha equivalence equalities*][Crole2012], Sections 2 and 6
* [M. Gabbay and A. Pitts, *A New Approach to Abstract Syntax with Variable
  Binding*][Gabbay2002], Section 2
-/

@[expose] public section

namespace Cslib

universe u

variable {Var : Type u} [DecidableEq Var]

namespace LambdaCalculus.Named.Untyped.Term

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

/-- A version of `swap_rename_comm` where the target `z` of the renaming is not swapped. -/
lemma swap_rename_comm' {m : Term Var} {u v x z : Var} (hzu : z ≠ u) (hzv : z ≠ v) :
    (m.swap u v).rename (Equiv.swap u v x) z = (m.rename x z).swap u v := by
  rw [← swap_rename_comm (m := m) (u := u) (v := v) (x := x) (y := z),
    Equiv.swap_apply_of_ne_of_ne hzu hzv]

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

/-- If `u` is not among `m`'s variables, then `v` cannot appear in `m.swap u v`
(the only way `v` could show up is as the image of `u`). -/
lemma notMem_swap_target {m : Term Var} {u v : Var} (hu : u ∉ m.vars) : v ∉ (m.swap u v).vars := by
  grind [vars_swap]

/-- Permutations preserve α-equivalence. -/
lemma AlphaEquiv.permute_preserve {m m' : Term Var} (h : m =α m') (π : Equiv.Perm Var) :
    (m.permute π) =α (m'.permute π) := by
  induction h with
  | var => exact .var
  | app _ _ ih1 ih2 => exact .app ih1 ih2
  | @abs z a b m m' hz _ ih =>
    apply AlphaEquiv.abs (y := π z)
    · grind [vars_permute, π.injective]
    · simpa only [permute_rename, AlphaEquiv_def] using ih

/-- Lemma 6.1 [Crole2012]: Swap (transposition) preserves α-equivalence. -/
lemma AlphaEquiv.swap_preserve {m m' : Term Var} {u v : Var} (h : m =α m') :
    (m.swap u v) =α (m'.swap u v) :=
  h.permute_preserve (Equiv.swap u v)

variable [HasFresh Var]

/-- Lemma 6.2 part 2 [Crole2012]: permutations that agree on the free variables of a term act on
it in the same way up to α-equivalence. The paper's hypothesis `free(E) ⊆ AS(π, π')` is
`Set.EqOn π π' m.fv`. -/
lemma permute_alphaEquiv_of_eqOn_fv (m : Term Var) (π π' : Equiv.Perm Var)
    (h : Set.EqOn π π' m.fv) : (m.permute π) =α (m.permute π') := by
  induction m generalizing π π' with
  | var x =>
    have hx : π x = π' x := by simpa using h
    simpa [permute, hx] using AlphaEquiv.var
  | app m n ihm ihn =>
    simp only [fv, Finset.coe_union, Set.eqOn_union] at h
    exact AlphaEquiv.app (ihm π π' h.1) (ihn π π' h.2)
  | abs a m ih =>
    let z := HasFresh.fresh ((m.permute π).vars ∪ (m.permute π').vars ∪ {π a, π' a})
    have hz := HasFresh.fresh_notMem ((m.permute π).vars ∪ (m.permute π').vars ∪ {π a, π' a})
    have hzπ : z ∉ (m.permute π).vars := by grind
    have hzπ' : z ∉ (m.permute π').vars := by grind
    apply AlphaEquiv.abs (y := z) (by grind)
    rw [← swap_eq_rename_of_notMem_vars hzπ, ← swap_eq_rename_of_notMem_vars hzπ', ← permute_swap,
      ← permute_swap, permute_permute, permute_permute]
    apply ih
    intro x hx
    by_cases hxa : x = a
    · grind
    · have hagree : π x = π' x := h (by simp [fv, hx, hxa])
      have hπxa : π x ≠ π a := fun he => hxa (π.injective he)
      have hπ'xa : π' x ≠ π' a := fun he => hxa (π'.injective he)
      have hπxz : π x ≠ z := by
        contrapose hzπ with he
        rw [← he, vars_eq_fv_union_bv, fv_permute]
        exact Finset.mem_union_left _ <| Finset.mem_image_of_mem _ hx
      grind

/-- Lemma 6.2 part 2 [Crole2012] (specialized). -/
lemma swap_comp_alphaEquiv_of_notMem_fv {m : Term Var} {a u z : Var}
    (hu : u ∉ m.fv) (hz : z ∉ m.fv) :
    ((m.swap u a).swap z u) =α (m.swap z a) := by
  simp_rw [← permute_swap, permute_permute]
  apply permute_alphaEquiv_of_eqOn_fv
  grind [Set.EqOn]

end LambdaCalculus.Named.Untyped.Term

end Cslib
