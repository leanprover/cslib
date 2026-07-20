/-
Copyright (c) 2026 Chris Anto Fröschl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Anto Fröschl
-/

module

public import Cslib.Languages.LambdaCalculus.Named.Untyped.AlphaEquivDefs
public import Cslib.Languages.LambdaCalculus.Named.Untyped.Properties

/-! # Properties of the swap (transposition) operation on lambda terms

Helper lemmas for reasoning about `Term.swap` and its interaction with
`AlphaEquiv`, `rename`, `vars`, and `fv`.

The notion of *atom swapping* (transposition) as the basis for defining α-equivalence
originates from [Gabbay and Pitts, *A New Approach to Abstract Syntax with Variable
Binding*][Gabbay2002] (Section 2, page 3). The key observation is that α-equivalence can
be defined using the notion of atom swapping in lieu of the traditional
renaming/substitution approach.

The swap (transposition) operation `m.swap x y` implements the permutation action
`(x y) · E` from [Crole2012] (Section 2). It simultaneously replaces all occurrences
of `x` with `y` and vice versa throughout a term.

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

-- TODO explicit usage?
def agreementSet (f g : Var → Var) : Set Var := { x | f x = g x }
def disagreementSet (f g : Var → Var) : Set Var := { x | f x ≠ g x }

@[simp]
lemma swap_self {m : Term Var} {x : Var} : m.swap x x = m := by
  induction m <;> simp [swap] <;> grind

lemma swap_comm {m : Term Var} {x y : Var} : m.swap x y = m.swap y x := by
  induction m <;> simp [swap] <;> grind

@[simp]
lemma swap_involutive {m : Term Var} {x y : Var} :
    (m.swap x y).swap x y = m := by
  induction m <;> simp [swap] <;> grind

@[simp]
lemma swap_preserves_sizeOf {m : Term Var} {x y : Var} :
    sizeOf (m.swap x y) = sizeOf m := by
  induction m <;> simp [swap] <;> grind

@[simp]
lemma swap_unused {m : Term Var} {x y : Var} :
    x ∉ m.vars → y ∉ m.vars → m.swap x y = m := by
  induction m <;> grind [swap, vars]

/-- When `y ∉ m.vars`, `swap x y` and `rename x y` coincide.

This is because `rename x y` only changes `x` to `y` (not `y` to `x`), and when `y` does
not occur in `m`, swapping and renaming produce the same result. -/
lemma swap_eq_rename_of_not_mem_vars {m : Term Var} {x y : Var}
    (hy : y ∉ m.vars) : m.swap x y = m.rename x y := by
  induction m with
  | var z =>
    unfold swap rename
    grind [Term.vars]
  | abs z m ih =>
    simp_all +decide [Term.swap, Term.rename, Term.vars]
    grind
  | app n1 n2 ih1 ih2 =>
    simp_all +decide [Term.swap, Term.rename, Term.vars]

/-- The set of free variables after a swap. -/
lemma swap_fv {m : Term Var} {x y : Var} :
      (m.swap x y).fv = m.fv.image fun z => if z = x then y else if z = y then x else z := by
    induction m with
    | var z => aesop
    | abs z m ih =>
      simp_all +decide [Term.swap, Term.fv, Finset.ext_iff, Finset.mem_image, Finset.mem_sdiff]
      grind
    | app m n ih1 ih2 =>
      simp_all +decide only [Term.swap, Term.fv]
      rw [Finset.image_union]

/-- Swapping preserves non-membership in `fv`. -/
lemma fresh_swap {m : Term Var} {x y z : Var} (hzx : z ≠ x) (hzy : z ≠ y) (hzm : z ∉ m.fv) :
    z ∉ (m.swap x y).fv := by
  rw [swap_fv]
  grind

/-- The set of vars after a swap. -/
lemma swap_vars {m : Term Var} {x y z : Var} (hzm : z ∉ m.vars) :
    (m.swap x y).vars = m.vars.image fun z => if z = x then y else if z = y then x else z := by
  induction m with
  | var w => aesop
  | abs w m ih => simp_all +decide [Term.swap, Term.vars]
  | app m n ih1 ih2 =>
    simp_all +decide only [Term.swap, Term.vars, Finset.image_union]
    grind

/-- Swapping preserves non-membership in `vars`. -/
lemma not_mem_vars_swap {m : Term Var} {x y z : Var}
    (hzx : z ≠ x) (hzy : z ≠ y) (hzm : z ∉ m.vars) :
    z ∉ (m.swap x y).vars := by
  rw [swap_vars hzm]
  grind

/-- Helper function: the action of the transposition `(u v)` on a single variable `z`. -/
@[simp]
def swapVar (u v z : Var) : Var :=
  if z = u then v else if z = v then u else z

/-- `swapVar` is a fixed point for variables outside `{u, v}`. -/
@[simp]
lemma swapVar_fixed {u v z : Var} (hzu : z ≠ u) (hzv : z ≠ v) :
    swapVar u v z = z := by simp_all

/-- `swapVar` is injective (permutations are bijections). -/
lemma swapVar_injective (u v : Var) : Function.Injective (swapVar u v) := by
  unfold Function.Injective
  aesop

/-- `swap` and `rename` commute (modulo the permutation action on the variable arguments). -/
lemma swap_rename_comm {m : Term Var} {u v x y : Var} :
    (m.swap u v).rename (swapVar u v x) (swapVar u v y) = (m.rename x y).swap u v := by
  induction m with
  | var z =>
    simp_all +decide [Term.swap, Term.rename, swapVar]
    grind
  | abs z m ih =>
    simp_all +decide [Term.swap, Term.rename, swapVar]
    grind
  | app m n ih1 ih2 =>
    simp_all +decide [Term.swap, Term.rename, swapVar]

lemma swap_rename_comm' {m : Term Var} {u v x z : Var} (hzu : z ≠ u) (hzv : z ≠ v) :
    (m.swap u v).rename (swapVar u v x) z = (m.rename x z).swap u v := by
  rw [← @swap_rename_comm _ _ m u v x z]
  simp_all

lemma swap_comp_eq_of_not_mem_vars {m : Term Var} {a u z : Var}
    (hu : u ∉ m.vars) (hz : z ∉ m.vars) :
    (m.swap u a).swap z u = m.swap z a := by
  induction m
  · simp_all +decide [Term.swap, Term.vars]
    grind
  · simp_all +decide [Term.swap, Term.vars]
    grind
  · simp_all +decide [Term.swap, Term.vars]

/-- Pointwise version of the transposition-conjugation identity
`(u v) ∘ (u a) = (v a) ∘ (u v)` for `a ∉ {u, v}` -/
lemma swapVar_conj {a u v w : Var} (huv : u ≠ v) (hau : a ≠ u) (hav : a ≠ v) :
    swapVar v a (swapVar u v w) = swapVar u v (swapVar u a w) := by
  unfold swapVar
  grind

/-- Term-level conjugation identity: `(m.swap u v).swap v a = (m.swap u a).swap u v`
when `a ∉ {u, v}`.

Unlike `swap_comp_eq_of_not_mem_vars`, this holds unconditionally (no freshness needed). -/
lemma swap_comp_eq_of_ne {m : Term Var} {a u v : Var} (hau : a ≠ u) (hav : a ≠ v) :
    (m.swap u v).swap v a = (m.swap u a).swap u v := by
  induction m with
  | var x => simp_all +decide [Term.swap]; grind
  | app m n ihm ihn => simp [Term.swap, ihm, ihn]
  | abs x m ih => simp [Term.swap, ih]; grind

/-- If `u` is not among `m`'s variables, then `v` cannot appear in `m.swap u v`
(the only way `v` could show up is as the image of `u`). -/
lemma not_mem_swap_target {m : Term Var} {u v : Var} (hu : u ∉ m.vars) :
    v ∉ (m.swap u v).vars := by
  rw [swap_vars hu]
  grind

-- First 4 case examination
lemma desired_condition_cases_z_ne_u_or_v {E E' : Term Var} {a b u v z : Var}
  (hm1 : z ∉ E.vars ∪ E'.vars ∪ {a, b})
  (h2 : ((E.rename a z).swap u v) =α ((E'.rename b z).swap u v))
  (hzu : z ≠ u)
  (hzv : z ≠ v)
  : ((E.swap u v).swap (swapVar u v a) z) =α ((E'.swap u v).swap (swapVar u v b) z) := by
    have hzb : z ≠ b := by simp_all
    have hza : z ≠ a := by simp_all
    have z_h1 : z ∉ (E.swap u v).vars := by exact not_mem_vars_swap hzu hzv (by simp_all)
    have z_h2 : z ∉ (E'.swap u v).vars := by exact not_mem_vars_swap hzu hzv (by simp_all)
    rw [swap_eq_rename_of_not_mem_vars z_h1]
    rw [swap_eq_rename_of_not_mem_vars z_h2]
    rw [← swap_rename_comm' (by grind) (by grind)] at h2
    rw [← swap_rename_comm' (by grind) (by grind)] at h2
    unfold swapVar at h2
    have ha : a = u ∨ a = v ∨ (a ≠ u ∧ a ≠ v) := by grind
    have hb : b = u ∨ b = v ∨ (b ≠ u ∧ b ≠ v) := by grind
    rcases ha with h' | h' | ⟨hau, hav⟩
    · rcases hb with h'' | h'' | ⟨hbu, hbv⟩ <;> simp_all +decide
    · rcases hb with h'' | h'' | ⟨hbu, hbv⟩ <;> simp_all +decide
    · rcases hb with h'' | h'' | ⟨hbu, hbv⟩ <;> simp_all +decide

-- example 1: use z as witness
lemma alphaEquiv_swap_preserve_abs_fresh {E E' : Term Var} {a b u v z : Var}
  (hm : z ∉ E.vars ∪ E'.vars ∪ {a, b})
  (hbody : ((E.rename a z).swap u v) =α ((E'.rename b z).swap u v))
  (hzu : z ≠ u) (hzv : z ≠ v) :
  ((Term.abs a E).swap u v) =α ((Term.abs b E').swap u v) := by
    have hzE : z ∉ (E.swap u v).vars := not_mem_vars_swap hzu hzv (by simp_all)
    have hzE' : z ∉ (E'.swap u v).vars := not_mem_vars_swap hzu hzv (by simp_all)
    have hren := desired_condition_cases_z_ne_u_or_v hm hbody hzu hzv
    rw [swap_eq_rename_of_not_mem_vars hzE, swap_eq_rename_of_not_mem_vars hzE'] at hren
    simp only [Term.swap]
    apply AlphaEquiv.abs (y := z)
    · simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
      grind
    · simpa [swapVar] using hren

-- example 2: use v as witness
lemma alphaEquiv_swap_preserve_abs_fresh_z_eq_u {E E' : Term Var} {a b u v : Var}
  (hm : u ∉ E.vars ∪ E'.vars ∪ {a, b})
  (hbody : ((E.rename a u).swap u v) =α ((E'.rename b u).swap u v))
  (hau : a ≠ u) (hav : a ≠ v) (hbu : b ≠ u) (hbv : b ≠ v) :
  ((Term.abs a E).swap u v) =α ((Term.abs b E').swap u v) := by
    have huE : u ∉ E.vars := by simp_all
    have huE' : u ∉ E'.vars := by simp_all
    rw [← swap_eq_rename_of_not_mem_vars huE, ← swap_eq_rename_of_not_mem_vars huE'] at hbody
    rw [swap_comm (m := E) (x := a) (y := u), swap_comm (m := E') (x := b) (y := u)] at hbody
    rw [← swap_comp_eq_of_ne hau hav, ← swap_comp_eq_of_ne hbu hbv] at hbody
    rw [swap_comm (m := E.swap u v) (x := v) (y := a),
        swap_comm (m := E'.swap u v) (x := v) (y := b)] at hbody
    have hvE : v ∉ (E.swap u v).vars := not_mem_swap_target huE
    have hvE' : v ∉ (E'.swap u v).vars := not_mem_swap_target huE'
    rw [swap_eq_rename_of_not_mem_vars hvE, swap_eq_rename_of_not_mem_vars hvE'] at hbody
    simp only [Term.swap]
    apply AlphaEquiv.abs (y := v) <;> (simp_all +decide; grind)

-- example 3
lemma alphaEquiv_swap_preserve_abs_b_eq_u {E E' : Term Var} {a u v : Var}
    (hm : v ∉ E.vars ∪ E'.vars ∪ {a})
    (hbody : ((E.rename a v).swap u v) =α ((E'.rename u v).swap u v))
    (hau : a ≠ u) (hav : a ≠ v) (huv : u ≠ v) :
    ((Term.abs a E).swap u v) =α ((Term.abs u E').swap u v) := by
  have hvE : v ∉ E.vars := by simp_all
  have hvE' : v ∉ E'.vars := by simp_all
  have huE : u ∉ (E.swap u v).vars := by rw [swap_comm]; exact not_mem_swap_target hvE
  have huE' : u ∉ (E'.swap u v).vars := by rw [swap_comm]; exact not_mem_swap_target hvE'
  have hL : (E.swap u v).rename a u = (E.rename a v).swap u v := by
    have h := @swap_rename_comm _ _ E u v a v
    simpa [swapVar, hau, hav, huv, huv.symm] using h
  have hR : (E'.swap u v).rename v u = (E'.rename u v).swap u v := by
    have h := @swap_rename_comm _ _ E' u v u v
    simpa [swapVar, huv, huv.symm] using h
  have hbody' : ((E.swap u v).rename a u) =α ((E'.swap u v).rename v u) := by
    rw [hL, hR]; exact hbody
  apply AlphaEquiv.abs (y := u)
  · simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
    grind
  · simp_all +decide only [Finset.union_singleton, Finset.mem_insert, Finset.mem_union,
      or_self, or_false, ne_eq, reduceIte]
    exact hbody

-- example 4
lemma alphaEquiv_swap_preserve_abs_a_eq_b_eq_u {E E' : Term Var} {u v : Var}
  (hm : v ∉ E.vars ∪ E'.vars ∪ {u})
  (ih : ((E.rename u v).swap u v) =α ((E'.rename u v).swap u v)) (huv : u ≠ v) :
  ((Term.abs u E).swap u v) =α ((Term.abs u E').swap u v) := by
    have hvE : v ∉ E.vars := by simp_all
    have hvE' : v ∉ E'.vars := by simp_all
    rw [← swap_eq_rename_of_not_mem_vars hvE, ← swap_eq_rename_of_not_mem_vars hvE'] at ih
    rw [swap_involutive, swap_involutive] at ih
    -- now have ih : E =α E'
    have huE : u ∉ (E.swap u v).vars := by
      have h := not_mem_swap_target (u := v) (v := u) hvE
      rwa [swap_comm] at h
    have huE' : u ∉ (E'.swap u v).vars := by
      have h := not_mem_swap_target (u := v) (v := u) hvE'
      rw [swap_comm] at h
      exact h
    apply AlphaEquiv.abs (y := u)
    · simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
      grind
    · rw [← swap_eq_rename_of_not_mem_vars huE, ← swap_eq_rename_of_not_mem_vars huE']
      simp_all +decide only [Finset.union_singleton, Finset.mem_insert, Finset.mem_union, or_self,
        reduceIte, swap_comm, swap_involutive]
      exact ih

variable [HasFresh Var]

lemma AlphaEquiv.abs_congr {m m' : Term Var} {x : Var} :
    m =α m' → (Term.abs x m) =α (Term.abs x m') := by
  intro h
  obtain ⟨y, hy⟩ := HasFresh.fresh_exists (m.vars ∪ m'.vars ∪ {x})
  apply AlphaEquiv.abs (y := y)
  · grind
  · apply AlphaEquiv.rename_preserve <;> grind

/-- Lemma 6.1 [Crole2012]: Swap (transposition) preserves α-equivalence. -/
lemma AlphaEquiv.swap_preserve {m m' : Term Var} {u v : Var} :
  m =α m' → (m.swap u v) =α (m'.swap u v) := by
    intro h1
    by_cases h2 : u = v
    · simp_all
    · change u ≠ v at h2
      induction h1 with
      | var => simp_all +decide [AlphaEquiv.refl]
      | abs hm1 hm2 ih =>
        rename_i z a b E E'
        have z_h1 : z ≠ a := by simp_all
        have z_h2 : z ≠ b := by simp_all
        have h3 : a = u ∨ a = v ∨ (a ≠ u ∧ a ≠ v) := by grind
        have h4 : b = u ∨ b = v ∨ (b ≠ u ∧ b ≠ v) := by grind
        have h5 : z = u ∨ z = v ∨ (z ≠ u ∧ z ≠ v) := by grind
        rcases h3 with ha | ha | ⟨hau, hav⟩
        · rcases h4 with hb | hb | ⟨hbu, hbv⟩
          · rcases h5 with hz | hz | ⟨hzu, hzv⟩
            · simp_all
            -- representative example 4 case of: a = u; b = u; z = v
            · subst ha; subst hb; subst hz
              exact alphaEquiv_swap_preserve_abs_a_eq_b_eq_u (by simp_all) ih h2
            -- example 1 reuse
            · exact alphaEquiv_swap_preserve_abs_fresh hm1 ih hzu hzv
          · rcases h5 with hz | hz | ⟨hzu, hzv⟩
            · simp_all
            · simp_all
            -- example 1 reuse
            · exact alphaEquiv_swap_preserve_abs_fresh hm1 ih hzu hzv
          · rcases h5 with hz | hz | ⟨hzu, hzv⟩
            · simp_all
            -- example 3 reuse
            · subst ha; subst hz
              apply AlphaEquiv.symm
              exact (alphaEquiv_swap_preserve_abs_b_eq_u (by grind) (AlphaEquiv.symm ih) hbu hbv h2)
            -- example 1 reuse
            · exact alphaEquiv_swap_preserve_abs_fresh hm1 ih hzu hzv
        · rcases h4 with hb | hb | ⟨hbu, hbv⟩
          · rcases h5 with hz | hz | ⟨hzu, hzv⟩
            · simp_all
            · simp_all
            -- example 1 reuse
            · exact alphaEquiv_swap_preserve_abs_fresh hm1 ih hzu hzv
          · rcases h5 with hz | hz | ⟨hzu, hzv⟩
            -- example 4 reuse
            · subst ha; subst hb; subst hz
              nth_rw 1 [swap_comm]
              nth_rw 2 [swap_comm]
              symm at z_h2
              nth_rw 1 [swap_comm] at ih
              nth_rw 2 [swap_comm] at ih
              apply alphaEquiv_swap_preserve_abs_a_eq_b_eq_u (by simp_all) ih z_h2
            · simp_all
            -- example 1 reuse
            · exact alphaEquiv_swap_preserve_abs_fresh hm1 ih hzu hzv
          · rcases h5 with hz | hz | ⟨hzu, hzv⟩
            -- example 3 reuse
            · subst ha; subst hz
              nth_rw 1 [swap_comm]
              nth_rw 2 [swap_comm]
              apply AlphaEquiv.symm
              symm at h2
              apply alphaEquiv_swap_preserve_abs_b_eq_u (by simp_all) _ hbv hbu h2
              apply AlphaEquiv.symm
              nth_rw 1 [swap_comm]
              nth_rw 2 [swap_comm]
              exact ih
            · simp_all
            -- example 1 reuse
            · exact alphaEquiv_swap_preserve_abs_fresh hm1 ih hzu hzv
        · rcases h4 with hb | hb | ⟨hbu, hbv⟩
          · rcases h5 with hz | hz | ⟨hzu, hzv⟩
            · simp_all
            -- representative example 3 case of: a ≠ u, v; b = u; z = v
            · subst hb; subst hz
              exact alphaEquiv_swap_preserve_abs_b_eq_u (by simp_all) ih hau hav h2
            -- example 1 reuse
            · exact alphaEquiv_swap_preserve_abs_fresh hm1 ih hzu hzv
          · rcases h5 with hz | hz | ⟨hzu, hzv⟩
            -- example 3 reuse
            · subst hb; subst hz
              nth_rw 1 [swap_comm]
              nth_rw 2 [swap_comm]
              symm at h2
              apply alphaEquiv_swap_preserve_abs_b_eq_u (by simp_all) _ hav hau h2
              nth_rw 1 [swap_comm]
              nth_rw 2 [swap_comm]
              exact ih
            · simp_all
            -- example 1 reuse
            · exact alphaEquiv_swap_preserve_abs_fresh hm1 ih hzu hzv
          · rcases h5 with hz | hz | ⟨hzu, hzv⟩
            -- representative example 2 case of: a ≠ u, v; b ≠ u, v; z = u
            -- use z' = v
            · subst hz
              exact alphaEquiv_swap_preserve_abs_fresh_z_eq_u hm1 ih hau hav hbu hbv
            -- example 2 reuse after adjusting via swap commutativity and choosing z' = u
            · rw [swap_comm (m := Term.abs a E) (x := u) (y := v),
                  swap_comm (m := Term.abs b E') (x := u) (y := v)]
              subst hz
              nth_rw 1 [swap_comm] at ih
              nth_rw 2 [swap_comm] at ih
              exact alphaEquiv_swap_preserve_abs_fresh_z_eq_u hm1 ih hav hau hbv hbu
            -- representative example 1 case of: z ≠ u, v
            -- use z' = z
            · exact alphaEquiv_swap_preserve_abs_fresh hm1 ih hzu hzv
      | app hm1 hm2 ih1 ih2 => exact AlphaEquiv.app ih1 ih2

-- TODO part 1
/-! ### Lemma 6.2 part 2 (α-equivalence version) -/

/-- Helper: if `y1 ∉ fv(m)` and `y2 ∉ fv(m)`, there exists `m'` α-equivalent to `m`
with both `y1 ∉ vars(m')` and `y2 ∉ vars(m')`. -/
lemma exists_alphaEquiv_not_mem_vars_pair {m : Term Var} {y1 y2 : Var}
    (h1 : y1 ∉ m.fv) (h2 : y2 ∉ m.fv) :
    ∃ m', m =α m' ∧ y1 ∉ m'.vars ∧ y2 ∉ m'.vars := by
  -- Step 1: Rename y1 to a fresh variable, avoiding both y1 and y2.
  let f1 := HasFresh.fresh (m.vars ∪ {y1, y2})
  have hf1 : f1 ∉ m.vars ∪ {y1, y2} := HasFresh.fresh_notMem _
  let m1 := m.rename y1 f1
  have hf1_ne_y1 : f1 ≠ y1 := by intro h; exact hf1 (by simp [h])
  have hf1_ne_y2 : f1 ≠ y2 := by intro h; exact hf1 (by simp [h])
  have hf1_vars : f1 ∉ m.vars := by intro h; exact hf1 (Finset.mem_union_left _ h)
  have hm1_alpha : m =α m1 := AlphaEquiv.rename_non_fv h1 hf1_vars
  have hy1_m1 : y1 ∉ m1.vars := rename_remove hf1_ne_y1.symm
  -- y2 ∉ fv(m1) since fv is preserved by α-equivalence.
  have hy2_fv_m1 : y2 ∉ m1.fv :=
    AlphaEquiv.same_fv hm1_alpha ▸ h2
  -- Step 2: Rename y2 to a fresh variable, avoiding both y1 and y2.
  let f2 := HasFresh.fresh (m1.vars ∪ {y1, y2})
  have hf2 : f2 ∉ m1.vars ∪ {y1, y2} := HasFresh.fresh_notMem _
  let m2 := m1.rename y2 f2
  have hf2_ne_y1 : f2 ≠ y1 := by intro h; exact hf2 (by simp [h])
  have hf2_ne_y2 : f2 ≠ y2 := by intro h; exact hf2 (by simp [h])
  have hf2_vars : f2 ∉ m1.vars := by intro h; exact hf2 (Finset.mem_union_left _ h)
  have hm2_alpha : m1 =α m2 := AlphaEquiv.rename_non_fv hy2_fv_m1 hf2_vars
  have hy2_m2 : y2 ∉ m2.vars := rename_remove hf2_ne_y2.symm
  -- y1 ∉ vars(m2): by rename_vars, vars(m2) ⊆ (vars(m1) \ {y2}) ∪ {f2}.
  -- Since y1 ∉ vars(m1) and f2 ≠ y1, we conclude y1 ∉ vars(m2).
  have hy1_m2 : y1 ∉ m2.vars := by
    simp only [m2, rename_vars, Finset.mem_union, Finset.mem_sdiff,
      Finset.mem_singleton]
    intro h
    cases h with
    | inl h => exact hy1_m1 h.1
    | inr h => split_ifs at h <;> simp_all [Ne.symm hf2_ne_y1]
  exact ⟨m2, AlphaEquiv.trans hm1_alpha hm2_alpha, hy1_m2, hy2_m2⟩

/-- **Lemma 6.2 part 2** [Crole2012] (specialized): If two composed transpositions
agree on all free variables, their actions are α-equivalent.

Specialized form: if `u, z ∉ fv(m)`, then `(m.swap u a).swap z u =α m.swap z a`.

This follows from the general statement of Lemma 6.2 part 2: since `u, z # E` (i.e.,
`u, z ∉ free(E)`), we have `free(E) ⊆ AS((z u) ∘ (u a), (z a))`, and therefore
`(z u) · (u a) · E ∼p (z a) · E`.

The agreement set computation is: for any `x ∈ free(E)`, since `x ≠ u` and `x ≠ z`,
we have `swapVar z u (swapVar u a x) = swapVar z a x`
(by `swap_comp_eq_swap_of_not_eq`).

The proof reduces to Lemma 6.2 part 1 via `exists_alphaEquiv_not_mem_vars_pair`
and `AlphaEquiv.swap_preserve`. -/
lemma swap_comp_alphaEquiv_of_not_mem_fv {m : Term Var} {a u z : Var}
    (hu : u ∉ m.fv) (hz : z ∉ m.fv) :
    ((m.swap u a).swap z u) =α (m.swap z a) := by
  -- By exists_alphaEquiv_not_mem_vars_pair, get m' with m =α m' and
  -- u, z ∉ vars(m').
  obtain ⟨m', hm', hm'u, hm'z⟩ := exists_alphaEquiv_not_mem_vars_pair hu hz
  -- By Lemma 6.2 part 1 (swap_comp_eq_of_not_mem_vars):
  -- (m'.swap u a).swap z u = m'.swap z a (syntactic equality!)
  have h_eq : (m'.swap u a).swap z u = m'.swap z a :=
    swap_comp_eq_of_not_mem_vars hm'u hm'z
  -- By Lemma 6.1 (swap_preserve) applied twice to m =α m':
  have h1 : ((m.swap u a).swap z u) =α ((m'.swap u a).swap z u) :=
    AlphaEquiv.swap_preserve (AlphaEquiv.swap_preserve hm')
  -- Rewrite using the syntactic equality:
  rw [h_eq] at h1
  -- By Lemma 6.1 (swap_preserve) applied to the symmetric direction:
  have h2 : (m'.swap z a) =α (m.swap z a) :=
    AlphaEquiv.swap_preserve (AlphaEquiv.symm hm')
  -- Chain: (m.swap u a).swap z u =α (m'.swap u a).swap z u
  --         = m'.swap z a =α m.swap z a
  exact AlphaEquiv.trans h1 h2

end LambdaCalculus.Named.Untyped.Term

end Cslib
