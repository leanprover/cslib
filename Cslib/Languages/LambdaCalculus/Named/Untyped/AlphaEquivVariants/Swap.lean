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
lemma permute_trans (m : Term Var) (π π' : Equiv.Perm Var) :
    (m.permute π).permute π' = m.permute (π.trans π') := by
  induction m <;> simp_all [permute]

omit [DecidableEq Var] in
/-- Permuting a term preserves its size. -/
@[simp]
lemma permute_sizeOf (m : Term Var) (π : Equiv.Perm Var) : sizeOf (m.permute π) = sizeOf m := by
  induction m <;> simp_all [permute]

/-- Permuting a term transports its free variables pointwise. -/
lemma permute_fv (m : Term Var) (π : Equiv.Perm Var) :
    (m.permute π).fv = m.fv.image π := by
  induction m with
  | var x => simp [permute, fv]
  | app m n ihm ihn => simp [permute, fv, ihm, ihn, Finset.image_union]
  | abs x m ih =>
    simp only [permute, fv, ih]
    rw [Finset.image_sdiff _ _ π.injective]
    simp

/-- Permuting a term transports its variables pointwise. -/
lemma permute_vars (m : Term Var) (π : Equiv.Perm Var) :
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
  simp [swap, permute_trans]

/-- Swapping preserves size. -/
@[simp]
lemma swap_preserves_sizeOf {m : Term Var} {x y : Var} : sizeOf (m.swap x y) = sizeOf m :=
  permute_sizeOf ..

/-- Swapping two unused variables has no effect. -/
@[simp]
lemma swap_unused {m : Term Var} {x y : Var} (hx : x ∉ m.vars) (hy : y ∉ m.vars) :
    m.swap x y = m := by
  rw [swap, permute_eq_of_eqOn_vars m _ (Equiv.refl Var), permute_refl]
  intro z hz
  grind

/-- When `y ∉ m.vars`, `swap x y` and `rename x y` coincide.

This is because `rename x y` only changes `x` to `y` (not `y` to `x`), and when `y` does
not occur in `m`, swapping and renaming produce the same result. -/
lemma swap_eq_rename_of_notMem_vars {m : Term Var} {x y : Var}
    (hy : y ∉ m.vars) : m.swap x y = m.rename x y := by
  induction m with
  | var z =>
    unfold swap rename
    grind [Term.vars, permute]
  | abs z m ih =>
    simp_all [Term.swap, Term.rename, Term.vars, permute]
    grind
  | app n1 n2 ih1 ih2 =>
    simp_all [Term.swap, Term.rename, Term.vars, permute]

/-- The set of free variables after a swap. -/
lemma swap_fv {m : Term Var} {x y : Var} : (m.swap x y).fv = m.fv.image (Equiv.swap x y) :=
  permute_fv ..

/-- Swapping preserves non-membership in `fv`. -/
lemma notMem_fv_swap {m : Term Var} {x y z : Var} (hzx : z ≠ x) (hzy : z ≠ y) (hzm : z ∉ m.fv) :
    z ∉ (m.swap x y).fv := by
  rw [swap_fv]
  grind

/-- The set of vars after a swap. -/
lemma swap_vars {m : Term Var} {x y : Var} : (m.swap x y).vars = m.vars.image (Equiv.swap x y) :=
  permute_vars ..

/-- Swapping preserves non-membership in `vars`. -/
lemma notMem_vars_swap {m : Term Var} {x y z : Var}
    (hzx : z ≠ x) (hzy : z ≠ y) (hzm : z ∉ m.vars) : z ∉ (m.swap x y).vars := by
  rw [swap_vars]
  grind

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
  rw [swap, swap, permute_trans]
  apply permute_eq_of_eqOn_vars
  intro x hx
  grind

/-- Term-level conjugation identity: `(m.swap u v).swap v a = (m.swap u a).swap u v`
when `a ∉ {u, v}`.

Unlike `swap_comp_eq_of_notMem_vars`, this holds unconditionally (no freshness needed). -/
lemma swap_comp_eq_of_ne {m : Term Var} {a u v : Var} (hau : a ≠ u) (hav : a ≠ v) :
    (m.swap u v).swap v a = (m.swap u a).swap u v := by
  simp only [swap, permute_trans]
  congr 1
  grind

/-- If `u` is not among `m`'s variables, then `v` cannot appear in `m.swap u v`
(the only way `v` could show up is as the image of `u`). -/
lemma notMem_swap_target {m : Term Var} {u v : Var} (hu : u ∉ m.vars) : v ∉ (m.swap u v).vars := by
  rw [swap_vars]
  grind

/- The following 5 lemmas are representative of non-trivial cases of the 27 cases occurring
in the proof of `AlphaEquiv.swap_preserve`. See Lemma 6.1 [Crole2012]. -/

-- First 4 case examinations in representative case z ≠ u, v
private lemma desired_condition_cases_z_ne_u_or_v {m m' : Term Var} {a b u v z : Var}
    (hm : z ∉ m.vars ∪ m'.vars ∪ {a, b})
    (hbody : ((m.rename a z).swap u v) =α ((m'.rename b z).swap u v))
    (hzu : z ≠ u)
    (hzv : z ≠ v) :
    ((m.swap u v).swap (Equiv.swap u v a) z) =α ((m'.swap u v).swap (Equiv.swap u v b) z) := by
  have hzm : z ∉ (m.swap u v).vars := notMem_vars_swap hzu hzv (by simp_all)
  have hzm' : z ∉ (m'.swap u v).vars := notMem_vars_swap hzu hzv (by simp_all)
  rw [swap_eq_rename_of_notMem_vars hzm, swap_eq_rename_of_notMem_vars hzm']
  rw [← swap_rename_comm' (by grind) (by grind), ← swap_rename_comm' (by grind) (by grind)] at hbody
  have ha : a = u ∨ a = v ∨ (a ≠ u ∧ a ≠ v) := by grind
  have hb : b = u ∨ b = v ∨ (b ≠ u ∧ b ≠ v) := by grind
  rcases ha with h' | h' | ⟨hau, hav⟩
  all_goals rcases hb with h'' | h'' | ⟨hbu, hbv⟩ <;> simp_all

-- representative case: z ≠ u, v
-- Use z as witness.
private lemma alphaEquiv_swap_preserve_abs_fresh {m m' : Term Var} {a b u v z : Var}
    (hm : z ∉ m.vars ∪ m'.vars ∪ {a, b})
    (hbody : ((m.rename a z).swap u v) =α ((m'.rename b z).swap u v))
    (hzu : z ≠ u) (hzv : z ≠ v) :
    ((Term.abs a m).swap u v) =α ((Term.abs b m').swap u v) := by
  have hzm : z ∉ (m.swap u v).vars := notMem_vars_swap hzu hzv (by simp_all)
  have hzm' : z ∉ (m'.swap u v).vars := notMem_vars_swap hzu hzv (by simp_all)
  have hren := desired_condition_cases_z_ne_u_or_v hm hbody hzu hzv
  rw [swap_eq_rename_of_notMem_vars hzm, swap_eq_rename_of_notMem_vars hzm'] at hren
  simp only [Term.swap]
  apply AlphaEquiv.abs (y := z)
  · simp_all [Finset.mem_union, Finset.mem_insert, swap]
    grind
  · exact hren

-- representative case: a ≠ u, v; b ≠ u, v; z = u
private lemma alphaEquiv_swap_preserve_abs_fresh_z_eq_u {m m' : Term Var} {a b u v : Var}
    (hm : u ∉ m.vars ∪ m'.vars ∪ {a, b})
    (hbody : ((m.rename a u).swap u v) =α ((m'.rename b u).swap u v))
    (hau : a ≠ u) (hav : a ≠ v) (hbu : b ≠ u) (hbv : b ≠ v) :
    ((Term.abs a m).swap u v) =α ((Term.abs b m').swap u v) := by
  have hum : u ∉ m.vars := by simp_all
  have hum' : u ∉ m'.vars := by simp_all
  rw [← swap_eq_rename_of_notMem_vars hum, ← swap_eq_rename_of_notMem_vars hum'] at hbody
  rw [swap_comm (m := m) (x := a) (y := u), swap_comm (m := m') (x := b) (y := u)] at hbody
  rw [← swap_comp_eq_of_ne hau hav, ← swap_comp_eq_of_ne hbu hbv] at hbody
  rw [swap_comm (m := m.swap u v) (x := v) (y := a)] at hbody
  rw [swap_comm (m := m'.swap u v) (x := v) (y := b)] at hbody
  have hvm : v ∉ (m.swap u v).vars := notMem_swap_target hum
  have hvm' : v ∉ (m'.swap u v).vars := notMem_swap_target hum'
  rw [swap_eq_rename_of_notMem_vars hvm, swap_eq_rename_of_notMem_vars hvm'] at hbody
  apply AlphaEquiv.abs (y := v) <;> (simp_all [swap]; grind)

-- representative case: a ≠ u, v; b = u; z = v
private lemma alphaEquiv_swap_preserve_abs_b_eq_u {m m' : Term Var} {a u v : Var}
    (hm : v ∉ m.vars ∪ m'.vars ∪ {a})
    (hbody : ((m.rename a v).swap u v) =α ((m'.rename u v).swap u v))
    (hau : a ≠ u) (hav : a ≠ v) (huv : u ≠ v) :
    ((Term.abs a m).swap u v) =α ((Term.abs u m').swap u v) := by
  have hvm : v ∉ m.vars := by simp_all
  have hvm' : v ∉ m'.vars := by simp_all
  have hum : u ∉ (m.swap u v).vars := by rw [swap_comm]; exact notMem_swap_target hvm
  have hum' : u ∉ (m'.swap u v).vars := by rw [swap_comm]; exact notMem_swap_target hvm'
  have hL : (m.swap u v).rename a u = (m.rename a v).swap u v := by
    have h := swap_rename_comm (m := m) (u := u) (v := v) (x := a) (y := v)
    simp_all
    grind
  have hR : (m'.swap u v).rename v u = (m'.rename u v).swap u v := by
    have h := swap_rename_comm (m := m') (u := u) (v := v) (x := u) (y := v)
    simp_all
  have hbody' : ((m.swap u v).rename a u) =α ((m'.swap u v).rename v u) := by
    rw [hL, hR]
    exact hbody
  apply AlphaEquiv.abs (y := u)
  · simp_all [Finset.mem_union, Finset.mem_insert, swap]
    grind
  · simp_all [swap]
    grind

-- representative case: a = u; b = u; z = v
private lemma alphaEquiv_swap_preserve_abs_a_eq_b_eq_u {m m' : Term Var} {u v : Var}
    (hm : v ∉ m.vars ∪ m'.vars ∪ {u})
    (hbody : ((m.rename u v).swap u v) =α ((m'.rename u v).swap u v)) (huv : u ≠ v) :
    ((Term.abs u m).swap u v) =α ((Term.abs u m').swap u v) := by
  have hvm : v ∉ m.vars := by simp_all
  have hvm' : v ∉ m'.vars := by simp_all
  rw [← swap_eq_rename_of_notMem_vars hvm, ← swap_eq_rename_of_notMem_vars hvm'] at hbody
  rw [swap_swap, swap_swap] at hbody
  -- now have hbody : m =α m'
  have hum : u ∉ (m.swap u v).vars := by
    have h := notMem_swap_target (u := v) (v := u) hvm
    rwa [swap_comm] at h
  have hum' : u ∉ (m'.swap u v).vars := by
    have h := notMem_swap_target (u := v) (v := u) hvm'
    rw [swap_comm] at h
    exact h
  apply AlphaEquiv.abs (y := u)
  · simp_all [swap]
  · simp only [Equiv.swap_apply_left]
    change ((m.swap u v).rename v u) =α ((m'.swap u v).rename v u)
    rw [← swap_eq_rename_of_notMem_vars (m := m.swap u v) (x := v) (y := u) hum]
    rw [← swap_eq_rename_of_notMem_vars (m := m'.swap u v) (x := v) (y := u) hum']
    nth_rw 2 [swap_comm]
    nth_rw 4 [swap_comm]
    rw [swap_swap, swap_swap]
    exact hbody

variable [HasFresh Var]

/-- Lemma 6.1 [Crole2012]: Swap (transposition) preserves α-equivalence. -/
lemma AlphaEquiv.swap_preserve {m m' : Term Var} {u v : Var} (h : m =α m') :
    (m.swap u v) =α (m'.swap u v) := by
  by_cases huv : u = v
  · simp_all
  · change u ≠ v at huv
    induction h with
    | var => apply AlphaEquiv.refl
    | @abs z a b m m' hm _ ih =>
      have hza : z ≠ a := by simp_all
      have hzb : z ≠ b := by simp_all
      have ha : a = u ∨ a = v ∨ (a ≠ u ∧ a ≠ v) := by grind
      have hb : b = u ∨ b = v ∨ (b ≠ u ∧ b ≠ v) := by grind
      have hz : z = u ∨ z = v ∨ (z ≠ u ∧ z ≠ v) := by grind
      -- we've got 27 cases to consider
      rcases ha with ha | ha | ⟨hau, hav⟩
      · rcases hb with hb | hb | ⟨hbu, hbv⟩
        · rcases hz with hz | hz | ⟨hzu, hzv⟩
          · simp_all
          -- representative case: a = u; b = u; z = v
          · subst ha hb hz
            exact alphaEquiv_swap_preserve_abs_a_eq_b_eq_u (by simp_all) ih huv
          -- reuse representative case: z ≠ u, v
          · exact alphaEquiv_swap_preserve_abs_fresh hm ih hzu hzv
        · rcases hz with hz | hz | ⟨hzu, hzv⟩
          · simp_all
          · simp_all
          -- reuse representative case: z ≠ u, v
          · exact alphaEquiv_swap_preserve_abs_fresh hm ih hzu hzv
        · rcases hz with hz | hz | ⟨hzu, hzv⟩
          · simp_all
          -- reuse representative case: a ≠ u, v; b = u; z = v
          · subst ha hz
            apply AlphaEquiv.symm
            exact
              (alphaEquiv_swap_preserve_abs_b_eq_u (by simp_all) (AlphaEquiv.symm ih) hbu hbv huv)
          -- reuse representative case: z ≠ u, v
          · exact alphaEquiv_swap_preserve_abs_fresh hm ih hzu hzv
      · rcases hb with hb | hb | ⟨hbu, hbv⟩
        · rcases hz with hz | hz | ⟨hzu, hzv⟩
          · simp_all
          · simp_all
          -- reuse representative case: z ≠ u, v
          · exact alphaEquiv_swap_preserve_abs_fresh hm ih hzu hzv
        · rcases hz with hz | hz | ⟨hzu, hzv⟩
          -- reuse representative case: a = u; b = u; z = v
          · subst ha hb hz
            nth_rw 1 [swap_comm]
            nth_rw 2 [swap_comm]
            symm at hzb
            nth_rw 1 [swap_comm] at ih
            nth_rw 2 [swap_comm] at ih
            apply alphaEquiv_swap_preserve_abs_a_eq_b_eq_u (by simp_all) ih hzb
          · simp_all
          -- reuse representative case: z ≠ u, v
          · exact alphaEquiv_swap_preserve_abs_fresh hm ih hzu hzv
        · rcases hz with hz | hz | ⟨hzu, hzv⟩
          -- reuse representative case: a ≠ u, v; b = u; z = v
          · subst ha hz
            nth_rw 1 [swap_comm]
            nth_rw 2 [swap_comm]
            apply AlphaEquiv.symm
            symm at huv
            apply alphaEquiv_swap_preserve_abs_b_eq_u (by simp_all) _ hbv hbu huv
            apply AlphaEquiv.symm
            nth_rw 1 [swap_comm]
            nth_rw 2 [swap_comm]
            exact ih
          · simp_all
          -- reuse representative case: z ≠ u, v
          · exact alphaEquiv_swap_preserve_abs_fresh hm ih hzu hzv
      · rcases hb with hb | hb | ⟨hbu, hbv⟩
        · rcases hz with hz | hz | ⟨hzu, hzv⟩
          · simp_all
          -- representative case: a ≠ u, v; b = u; z = v
          · subst hb; subst hz
            exact alphaEquiv_swap_preserve_abs_b_eq_u (by simp_all) ih hau hav huv
          -- reuse representative case: z ≠ u, v
          · exact alphaEquiv_swap_preserve_abs_fresh hm ih hzu hzv
        · rcases hz with hz | hz | ⟨hzu, hzv⟩
          -- reuse representative case: a ≠ u, v; b = u; z = v
          · subst hb hz
            nth_rw 1 [swap_comm]
            nth_rw 2 [swap_comm]
            symm at huv
            apply alphaEquiv_swap_preserve_abs_b_eq_u (by simp_all) _ hav hau huv
            nth_rw 1 [swap_comm]
            nth_rw 2 [swap_comm]
            exact ih
          · simp_all
          -- reuse representative case: z ≠ u, v
          · exact alphaEquiv_swap_preserve_abs_fresh hm ih hzu hzv
        · rcases hz with hz | hz | ⟨hzu, hzv⟩
          -- representative case: a ≠ u, v; b ≠ u, v; z = u
          -- use z' = v
          · subst hz
            exact alphaEquiv_swap_preserve_abs_fresh_z_eq_u hm ih hau hav hbu hbv
          -- reuse representative case: a ≠ u, v; b ≠ u, v; z = u
          -- after adjusting via swap commutativity and choosing z' = u
          · rw [swap_comm (m := Term.abs a m) (x := u) (y := v),
                swap_comm (m := Term.abs b m') (x := u) (y := v)]
            subst hz
            nth_rw 1 [swap_comm] at ih
            nth_rw 2 [swap_comm] at ih
            exact alphaEquiv_swap_preserve_abs_fresh_z_eq_u hm ih hav hau hbv hbu
          -- representative case: z ≠ u, v
          -- use z' = z
          · exact alphaEquiv_swap_preserve_abs_fresh hm ih hzu hzv
    | app _ _ ih1 ih2 => exact AlphaEquiv.app ih1 ih2

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
    have hzπ : z ∉ (m.permute π).vars := by simp_all [z]
    have hzπ' : z ∉ (m.permute π').vars := by simp_all [z]
    have hbody : (m.permute (π.trans (Equiv.swap (π a) z))) =α
        (m.permute (π'.trans (Equiv.swap (π' a) z))) := by
      apply ih
      intro x hx
      simp only [Equiv.trans_apply]
      by_cases hxa : x = a
      · simp_all
      · have hagree : π x = π' x := h (by simp [fv, hx, hxa])
        have hπxa : π x ≠ π a := fun he => hxa (π.injective he)
        have hπ'xa : π' x ≠ π' a := fun he => hxa (π'.injective he)
        have hπ'xπa : π' x ≠ π a := by simp_all
        have hπxz : π x ≠ z := by
          intro he
          apply hzπ
          rw [← he, vars_either_fv_or_bv]
          apply Finset.mem_union_left
          rw [permute_fv]
          exact Finset.mem_image.mpr ⟨x, hx, rfl⟩
        have hπ'xz : π' x ≠ z := by simp_all
        simp [Equiv.swap_apply_def, hπ'xa, hπ'xπa, hπ'xz, hagree]
    rw [← permute_trans, ← permute_trans, permute_swap, permute_swap] at hbody
    rw [swap_eq_rename_of_notMem_vars hzπ, swap_eq_rename_of_notMem_vars hzπ'] at hbody
    unfold permute
    apply AlphaEquiv.abs (y := z) (by simp_all [z]) hbody

/-- Lemma 6.2 part 2 [Crole2012] (specialized). -/
lemma swap_comp_alphaEquiv_of_notMem_fv {m : Term Var} {a u z : Var}
    (hu : u ∉ m.fv) (hz : z ∉ m.fv) :
    ((m.swap u a).swap z u) =α (m.swap z a) := by
  let π := (Equiv.swap u a).trans (Equiv.swap z u)
  let π' := Equiv.swap z a
  have h : Set.EqOn π π' m.fv := by
    intro x hx
    grind
  have h' := permute_alphaEquiv_of_eqOn_fv m π π' h
  rw [← permute_trans, permute_swap, permute_swap, permute_swap] at h'
  exact h'

end LambdaCalculus.Named.Untyped.Term

end Cslib
