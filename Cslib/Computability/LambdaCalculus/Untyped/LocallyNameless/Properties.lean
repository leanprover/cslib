/-
Copyright (c) 2025 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

import Cslib.Computability.LambdaCalculus.Untyped.LocallyNameless.Basic

universe u

variable {Var : Type u}

namespace LambdaCalculus.LocallyNameless.Term

lemma open_app_inj : app l r = (app l r)⟦i ↝ s⟧ ↔ l = l⟦i ↝ s⟧ ∧ r = r⟦i ↝ s⟧ := by
  simp [openRec]

lemma open_abs_inj : M.abs = M⟦i + 1 ↝ s⟧.abs ↔ M = M⟦i + 1 ↝ s⟧ := by
  simp

/-- An opening appearing in both sides of an equality of terms can be removed. -/
lemma open_lc_aux (e : Term Var) : ∀ (j v i u),
  i ≠ j →
  e ⟦j ↝ v⟧ = (e ⟦j ↝ v⟧) ⟦i ↝ u⟧ →
  e = e ⟦i ↝ u⟧ := by
  induction' e <;> intros j v i u neq h 
  case app l r ih_l ih_r => 
    obtain ⟨hl, hr⟩ := open_app_inj.mp h
    simp only [open_app_inj]
    exact ⟨ih_l j v i u neq hl, ih_r j v i u neq hr⟩
  case abs ih =>
    simp only [openRec_abs, open_abs_inj] at *
    exact ih (j+1) v (i+1) u (by aesop) h
  all_goals aesop

/-- Opening is associative for nonclashing free variables. -/
lemma swap_open_fvars (k n : ℕ) (x y : Var) (m : Term Var) : 
    k ≠ n → x ≠ y → m⟦n ↝ fvar y⟧⟦k ↝ fvar x⟧ = m⟦k ↝ fvar x⟧⟦n ↝ fvar y⟧ := by
  revert k n
  induction' m <;> aesop

variable [DecidableEq Var]

/-- Substitution of a free variable not present in a term leaves it unchanged. -/
theorem subst_fresh (x : Var) (t sub : Term Var) : x ∉ t.fv → (t [x := sub]) = t := by
  induction t <;> aesop

/- Opening and closing are inverses. -/
lemma open_close (x : Var) (t : Term Var) (k : ℕ) : x ∉ t.fv → t⟦k ↝ fvar x⟧⟦k ↜ x⟧ = t := by
  revert k
  induction t <;> aesop

/-- Opening is injective. -/
lemma open_injective (x : Var) (M M' : Term Var) : x ∉ M.fv → x ∉ M'.fv → M ^ fvar x = M' ^ fvar x → M = M' := by
  intros free_M free_M' eq
  rw [←open_close x M 0 free_M, ←open_close x M' 0 free_M']
  exact congrArg (closeRec 0 x) eq

/-- Opening and closing are associative for nonclashing free variables. -/
lemma swap_open_fvar_close (k n: ℕ) (x y : Var) (m : Term Var) : 
    k ≠ n → x ≠ y → m⟦n ↝ fvar y⟧⟦k ↜ x⟧ = m⟦k ↜ x⟧⟦n ↝ fvar y⟧ := by
  revert k n
  induction' m <;> aesop

/-- Closing preserves free variables. -/
lemma close_preserve_not_fvar {k x y} (m : Term Var) : x ∉ m.fv → x ∉ (m⟦k ↜ y⟧).fv := by
  revert k
  induction m <;> aesop

/-- Opening to a fresh free variable preserves free variables. -/
lemma open_fresh_preserve_not_fvar {k x y} (m : Term Var) : x ∉ m.fv → x ≠ y → x ∉ (m⟦k ↝ fvar y⟧).fv := by
  revert k
  induction m <;> aesop

/-- Substitution preserves free variables. -/
lemma subst_preserve_not_fvar {x y : Var} (m n : Term Var) : x ∉ m.fv ∪ n.fv → x ∉ (m [y := n]).fv := by
  induction m
  all_goals aesop

/-- Closing removes a free variable. -/
lemma close_var_not_fvar_rec (x) (k) (t : Term Var) : x ∉ (t⟦k ↜ x⟧).fv := by
  revert k
  induction t <;> aesop

/-- Specializes `close_var_not_fvar_rec` to first closing. -/
lemma close_var_not_fvar (x) (t : Term Var) : x ∉ (t ^* x).fv := close_var_not_fvar_rec x 0 t

variable [HasFresh Var] 

omit [DecidableEq Var] in
/-- A locally closed term is unchanged by opening. -/
@[aesop safe (rule_sets := [LambdaCalculus.LocallyNameless.ruleSet])]
lemma open_lc (k t) (e : Term Var) : e.LC → e = e⟦k ↝ t⟧ := by
  intros e_lc
  revert k
  induction e_lc
  case abs xs e _ ih => 
    intros k
    simp only [openRec_abs, abs.injEq]
    refine open_lc_aux e 0 (fvar (fresh xs)) (k+1) t ?_ ?_ <;> aesop
  all_goals aesop

/-- Substitution of a locally closed term distributes with opening. -/
lemma subst_open (x : Var) (t : Term Var) (k : ℕ) (u e) :
  LC t → 
  (e ⟦ k ↝ u ⟧) [ x := t ] = (e [ x := t ]) ⟦k ↝  u [ x := t ]⟧ := by
  revert k
  induction' e <;> aesop

/-- Specialize `subst_open` to the first opening. -/
theorem subst_open_var (x y : Var) (u e : Term Var) : y ≠ x → LC u → (e [y := u]) ^ fvar x = (e ^ fvar x) [y := u] := by
  intros neq u_lc
  have h : (e ^ fvar x)[y:=u] = e[y:=u] ^ (fvar x)[y:=u] := subst_open y u 0 (fvar x) e u_lc
  aesop

/-- Substitution of locally closed terms is locally closed. -/
theorem subst_lc {x : Var} {e u : Term Var} : LC e → LC u → LC (e [x := u]) := by
  intros lc_e lc_u
  induction lc_e 
  case abs xs e _ ih =>
    refine LC.abs ({x} ∪ xs) _ (?_ : ∀ y ∉ {x} ∪ xs, (e[x := u] ^ fvar y).LC)
    intros y mem
    rw [subst_open_var y x u e ?_ lc_u]
    all_goals aesop
  all_goals aesop

/-- Opening to a term `t` is equivalent to opening to a free variable and substituting it for `t`. -/
lemma subst_intro (x : Var) (t e : Term Var) : x ∉ e.fv → LC t → e ^ t = (e ^ fvar x) [ x := t ] := by
  intros mem t_lc
  simp only [open']
  rw [subst_open x t 0 (fvar x) e t_lc, subst_fresh _ _ t mem]
  aesop

/-- Opening of locally closed terms is locally closed. -/
theorem beta_lc {M N : Term Var} : LC (abs M) → LC N → LC (M ^ N) := by
  intros m_lc
  cases m_lc
  case abs xs mem =>
    intros n_lc
    have ⟨y, ymem⟩ := fresh_exists (xs ∪ M.fv)
    simp only [Finset.mem_union, not_or] at ymem
    cases ymem
    rw [subst_intro y N M]
    apply subst_lc
    apply mem
    all_goals aesop

/-- Opening then closing is equivalent to substitution. -/
lemma open_close_to_subst (m : Term Var) (x y : Var) (k : ℕ) : LC m → m ⟦k ↜ x⟧⟦k ↝ fvar y⟧ = m [x := fvar y] := by
  intros m_lc
  revert k
  induction' m_lc 
  case abs xs t x_mem ih =>
    intros k
    have ⟨x', x'_mem⟩ := fresh_exists ({x} ∪ {y} ∪ t.fv ∪ xs)
    have s := subst_open_var x' x (fvar y) t ?_ (by constructor)
    simp only [closeRec_abs, openRec_abs, subst_abs]
    rw [←open_close x' (t⟦k+1 ↜ x⟧⟦k+1 ↝ fvar y⟧) 0 ?f₁, ←open_close x' (t[x := fvar y]) 0 ?f₂]
    simp only [open'] at *
    rw [swap_open_fvars, ←swap_open_fvar_close, s, ih]
    case f₁ =>
      apply open_fresh_preserve_not_fvar
      apply close_preserve_not_fvar
      all_goals aesop
    case f₂ =>
      apply subst_preserve_not_fvar
      aesop
    all_goals aesop
  all_goals aesop

/-- Closing and opening are inverses. -/
lemma close_open (x : Var) (t : Term Var) (k : ℕ) : LC t → t⟦k ↜ x⟧⟦k ↝ fvar x⟧ = t := by
  intros lc_t
  revert k
  induction lc_t
  case abs xs t t_open_lc ih => 
    intros k
    simp only [closeRec_abs, openRec_abs, abs.injEq]
    have ⟨y, hy⟩ := fresh_exists (xs ∪ t.fv ∪ (t⟦k + 1 ↜ x⟧⟦k + 1 ↝ fvar x⟧).fv ∪ {x})
    simp only [Finset.union_assoc, Finset.mem_union, Finset.mem_singleton, not_or] at hy
    obtain ⟨q1, q2, q3, q4⟩ := hy
    refine open_injective y _ _ q3 q2 ?_
    rw [←ih y q1 (k+1)]
    simp only [open']
    rw [swap_open_fvar_close, swap_open_fvars]
    all_goals aesop
  all_goals aesop
