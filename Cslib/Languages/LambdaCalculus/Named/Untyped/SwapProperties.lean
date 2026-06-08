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

## References

* [Roy L. Crole, *Alpha equivalence equalities*][Crole2012], Section 6
-/

@[expose] public section

namespace Cslib

universe u

variable {Var : Type u} [DecidableEq Var]

namespace LambdaCalculus.Named.Untyped.Term

/-! ### Basic properties of swap -/

@[simp]
lemma swap_self {m : Term Var} {x : Var} : m.swap x x = m := by
  induction m <;> simp [swap] <;> grind

lemma swap_comm {m : Term Var} {x y : Var} : m.swap x y = m.swap y x := by
  induction m <;> simp [swap] <;> grind

@[simp]
lemma swap_involutive {m : Term Var} {x y : Var} : (m.swap x y).swap x y = m := by
  induction m <;> simp [swap] <;> grind

@[simp]
lemma swap_preserves_sizeOf {m : Term Var} {x y : Var} : sizeOf (m.swap x y) = sizeOf m := by
  induction m <;> simp [swap] <;> grind

@[simp]
lemma swap_unused {m : Term Var} {x y : Var} : x ∉ m.vars → y ∉ m.vars → m.swap x y = m := by
  induction m <;> grind [swap, vars]

/-- When `y ∉ m.vars`, `swap x y` and `rename x y` coincide. -/
lemma swap_eq_rename_of_not_mem_vars {m : Term Var} {x y : Var} (hy : y ∉ m.vars)
  : m.swap x y = m.rename x y := by
  induction m with
  | var z =>
    unfold swap rename
    grind [Term.vars]
  | abs z m ih =>
    simp_all +decide [Term.swap, Term.rename, Term.vars];
    grind
  | app n1 n2 ih1 ih2 =>
    simp_all +decide [Term.swap, Term.rename, Term.vars]

/-- The set of free variables after a swap. -/
lemma swap_fv {m : Term Var} {x y : Var} :
    (m.swap x y).fv = m.fv.image (fun z => if z = x then y else if z = y then x else z) := by
  induction m with
  | var z =>
    unfold fv
    aesop
  | abs z m ih =>
    simp_all +decide only [Term.swap, Term.fv]
    simp [Finset.ext_iff, Finset.mem_image, Finset.mem_sdiff]
    grind
  | app m n ih1 ih2 =>
    simp_all +decide only [Term.swap, Term.fv]
    rw [Finset.image_union]

/-- Swapping preserves non-membership in fv. -/
lemma fresh_swap {m : Term Var} {x y z : Var} (hzx : z ≠ x) (hzy : z ≠ y) (hzm : z ∉ m.fv)
  : z ∉ (m.swap x y).fv := by
  rw [swap_fv]
  grind

/-- The set of vars after a swap. -/
lemma swap_vars {m : Term Var} {x y z : Var} (hzm : z ∉ m.vars)
  : (m.swap x y).vars = m.vars.image (fun z => if z = x then y else if z = y then x else z) := by
    induction m with
    | var w =>
      simp +decide [Term.swap, Term.vars]
    | abs w m ih => simp_all +decide [Term.swap, Term.vars]
    | app m n ih1 ih2 =>
      simp_all +decide only [Term.swap, Term.vars]
      rw [Finset.image_union]
      grind

/-- Swapping preserves non-membership in vars. -/
lemma not_mem_vars_swap {m : Term Var} {x y z : Var} (hzx : z ≠ x) (hzy : z ≠ y) (hzm : z ∉ m.vars)
  : z ∉ (m.swap x y).vars := by
  rw [swap_vars hzm]
  grind

/-! ### Swap-rename commutation -/

/-- Helper function: the action of swap on a single variable. -/
@[simp]
def swapVar (u v z : Var) : Var := if z = u then v else if z = v then u else z

/-- swapVar is a fixed point for variables outside {u, v}. -/
@[simp]
lemma swapVar_fixed {u v z : Var} (hzu : z ≠ u) (hzv : z ≠ v) : swapVar u v z = z := by simp_all

/- `swapVar` is injective. -/
lemma swapVar_injective (u v : Var) : Function.Injective (swapVar u v) := by
  unfold Function.Injective
  intro a b
  unfold swapVar
  aesop

/-- `swap` and `rename` commute. -/
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

variable [HasFresh Var]

/-! ### Lemma 6.1: Swap preserves α-equivalence -/

-- TODO cleanup below proofs

/- Lemma 6.1 from [Crole2012]. -/
lemma AlphaEquiv.swap_preserve {m m' : Term Var} {u v : Var} :
    m =α m' → (m.swap u v) =α (m'.swap u v) := by
  by_contra h;
  -- Let's choose any $m$ and $m'$ such that $m =α m'$ but $(m.swap u v) ≠α (m'.swap u v)$.
  obtain ⟨m, m', h_eq, h_neq⟩ : ∃ m m' : Term Var, m =α m' ∧ ¬(m.swap u v) =α (m'.swap u v) := by
    grind;
  obtain ⟨m, m', h_eq, h_neq, h_min⟩ : ∃ m m' : Term Var, m =α m' ∧ ¬(m.swap u v) =α (m'.swap u v) ∧ ∀ n n' : Term Var, n =α n' → sizeOf n < sizeOf m → (n.swap u v) =α (n'.swap u v) := by
    have h_wf : WellFounded (fun m n : ℕ => m < n) := by
      exact wellFounded_lt;
    have := h_wf.has_min { n : ℕ | ∃ m m' : Term Var, m =α m' ∧ ¬ ( m.swap u v ) =α ( m'.swap u v ) ∧ n = sizeOf m } ⟨ _, ⟨ m, m', h_eq, h_neq, rfl ⟩ ⟩;
    obtain ⟨ a, ⟨ m, m', h_eq, h_neq, rfl ⟩, ha ⟩ := this; exact ⟨ m, m', h_eq, h_neq, fun n n' h_eq' h_lt => Classical.not_not.1 fun h_neq' => ha _ ⟨ n, n', h_eq', h_neq', rfl ⟩ h_lt ⟩ ;
  obtain ⟨x1, x2, m1, m2, h_eq⟩ : ∃ x1 x2 : Var, ∃ m1 m2 : Term Var, m = Term.abs x1 m1 ∧ m' = Term.abs x2 m2 ∧ ∃ y : Var, y ∉ m1.vars ∪ m2.vars ∪ {x1, x2} ∧ (m1.rename x1 y) =α (m2.rename x2 y) := by
    all_goals rcases h_eq with ⟨ ⟩;
    · exact False.elim <| h_neq <| AlphaEquiv.refl _;
    · grind;
    · exact False.elim <| h_neq <| AlphaEquiv.app ( h_min _ _ ‹_› <| by simp +arith +decide ) ( h_min _ _ ‹_› <| by simp +arith +decide );
  obtain ⟨y, hy₁, hy₂⟩ := h_eq.2.2;
  -- Pick z fresh for m1.vars ∪ m2.vars ∪ {x1, x2, u, v}.
  obtain ⟨z, hz⟩ : ∃ z : Var, z ∉ m1.vars ∪ m2.vars ∪ {x1, x2, u, v} := by
    exact?;
  -- By AlphaEquiv.abs_elim with z: m1.rename x1 z =α m2.rename x2 z.
  have hz_eq : (m1.rename x1 z) =α (m2.rename x2 z) := by
    apply AlphaEquiv.abs_elim; all_goals grind;
  -- By swap_rename_comm' (z ≠ u, z ≠ v): (m1.swap u v).rename (sv x1) z =α (m2.swap u v).rename (sv x2) z.
  have hz_swap : ((m1.swap u v).rename (swapVar u v x1) z) =α ((m2.swap u v).rename (swapVar u v x2) z) := by
    have hz_swap : ((m1.swap u v).rename (swapVar u v x1) z) = ((m1.rename x1 z).swap u v) ∧ ((m2.swap u v).rename (swapVar u v x2) z) = ((m2.rename x2 z).swap u v) := by
      apply And.intro;
      · apply swap_rename_comm'; all_goals grind;
      · apply swap_rename_comm'; all_goals grind;
    grind +suggestions;
  -- Apply AlphaEquiv.abs with witness z.
  have hz_abs : (Term.abs (swapVar u v x1) (m1.swap u v)) =α (Term.abs (swapVar u v x2) (m2.swap u v)) := by
    apply AlphaEquiv.abs;
    any_goals assumption;
    simp_all +decide [ Finset.mem_union, Finset.mem_singleton ];
    grind +suggestions;
  exact h_neq ( by simpa [ h_eq ] using hz_abs )

/-! ### Lemma 6.2: Agreement on free variables implies α-equivalence -/

/-
Helper: the composition (z u) ∘ (u a) agrees with (z a) on variables
    outside {u, z}.
-/
omit [HasFresh Var] in
lemma swap_comp_eq_swap_of_not_eq {x a u z : Var}
    (hxu : x ≠ u) (hxz : x ≠ z) :
    swapVar z u (swapVar u a x) = swapVar z a x := by
  unfold swapVar; aesop;

/-
Lemma 6.2 part 1 from [Crole2012]: If two permutations agree on all occurring
    variables, their actions are syntactically equal.

    Specialized: if `u, z ∉ vars(m)`, then `(m.swap u a).swap z u = m.swap z a`.
    TODO do unspecialized format
-/
omit [HasFresh Var] in
lemma swap_comp_eq_of_not_mem_vars {m : Term Var} {a u z : Var}
    (hu : u ∉ m.vars) (hz : z ∉ m.vars) :
    (m.swap u a).swap z u = m.swap z a := by
  induction m;
  · simp_all +decide [ Term.swap, Term.vars ];
    grind;
  · simp_all +decide [ Term.swap, Term.vars ];
    split_ifs <;> simp_all +decide [ eq_comm ];
  · simp_all +decide [ Term.swap, Term.vars ]

/-
Lemma 6.6 from [Crole2012] (Barendregt variable convention):
    For any term `m` and variable `y` with `y ∉ fv(m)`,
    there exists `m'` alpha-equivalent to `m` with `y ∉ vars(m')`.
-/
lemma exists_alphaEquiv_not_mem_vars {m : Term Var} {y : Var}
    (hy : y ∉ m.fv) : ∃ m', m =α m' ∧ y ∉ m'.vars := by
  by_contra h;
  convert Classical.byContradiction fun h' => ?_;
  convert h';
  convert Classical.not_not;
  simp_all only [not_exists, not_and, Decidable.not_not, not_false_eq_true, not_true_eq_false]
  convert h ( m.rename y ( HasFresh.fresh ( m.vars ∪ { y } ) ) ) ( by
    grind +suggestions ) using 1
  simp +decide [rename_vars]
  grind

end LambdaCalculus.Named.Untyped.Term

end Cslib
