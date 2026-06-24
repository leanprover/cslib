/-
Copyright (c) 2025 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.LcAt

/-! General properties of opening and substitution in untyped lambda calculus terms. -/

public section

namespace Cslib

universe u

variable {Var : Type u}

namespace LambdaCalculus.LocallyNameless.Untyped.Term

attribute [grind =] Finset.union_singleton

variable [DecidableEq Var]

/-- Substitution of a free variable not present in a term leaves it unchanged. -/
theorem subst_fresh (x : Var) (t sub : Term Var) (nmem : x ∉ t.fv) : t [x := sub] = t := by
  induction t <;> grind

/- Opening and closing are inverses. -/
lemma open_close (x : Var) (t : Term Var) (k : ℕ) (nmem : x ∉ t.fv) : t = t⟦k ↝ fvar x⟧⟦k ↜ x⟧ := by
  induction t generalizing k <;> grind

/-- Specializes `open_close` to the first closing. -/
lemma open_close_var (x : Var) (t : Term Var) (nmem : x ∉ t.fv) : t = (t ^ fvar x) ^* x :=
  open_close x t 0 nmem

/-- Opening is injective. -/
lemma open_injective (x : Var) (M M') (free_M : x ∉ M.fv) (free_M' : x ∉ M'.fv)
    (eq : M ^ fvar x = M' ^ fvar x) : M = M' := by
  grind [open_close x M 0 free_M, open_close x M' 0 free_M']

/-- Opening and closing are associative for nonclashing free variables. -/
lemma swap_open_fvar_close (k n : ℕ) (x y : Var) (m : Term Var) (neq₁ : k ≠ n) (neq₂ : x ≠ y) :
    m⟦n ↝ fvar y⟧⟦k ↜ x⟧ = m⟦k ↜ x⟧⟦n ↝ fvar y⟧ := by
  induction m generalizing k n <;> grind

/-- Closing preserves free variables. -/
@[scoped grind =]
lemma close_rec_fv {k y} (m : Term Var) : (m⟦k ↜ y⟧).fv = m.fv.erase y := by
  induction m generalizing k <;> grind

/-- Specializes `close_var_not_fvar_rec` to first closing. -/
@[scoped grind =]
lemma close_var_not_fvar (x) (t : Term Var) : (t ^* x).fv = t.fv.erase x := close_rec_fv t

set_option linter.tacticAnalysis.verifyGrindOnly false in
/-- Opening preserves free variables. -/
theorem open_preserve_not_fvar (k) (m n : Term Var) :
    m⟦k ↝ n⟧.fv = m.fv ∪ n.fv ∨ m⟦k ↝ n⟧.fv = m.fv := by
  induction m generalizing k with
  | app => grind only [= openRec, = fv]
  | _ => grind

set_option linter.tacticAnalysis.verifyGrindOnly false in
/-- Substitution preserves free variables. -/
lemma subst_preserve_not_fvar {y : Var} (m n : Term Var) :
    m [y := n].fv = m.fv.erase y ∨ m [y := n].fv = m.fv.erase y ∪ n.fv:= by
  induction m with
  | app => grind only [fv, = subst_app, = Finset.mem_union, = Finset.mem_erase]
  | _ => grind

lemma subst_refl (m : Term Var) (x : Var) : m[x := fvar x] = m := by
  induction m <;> grind

lemma subst_intro_openRec {x} {t e : Term Var} (mem : x ∉ e.fv) {k : ℕ} :
    e ⟦k ↝ t⟧ = (e ⟦ k ↝ fvar x⟧)[ x := t ] := by
  induction e generalizing k with grind

/-- Opening to a term `t` is equivalent to opening to a free variable and substituting for `t`. -/
lemma subst_intro (x : Var) (t e : Term Var) (mem : x ∉ e.fv) :
    e ^ t = (e ^ fvar x) [ x := t ] := subst_intro_openRec mem

scoped grind_pattern subst_intro => open' e t, open' e (fvar x)

variable [HasFresh Var]

omit [DecidableEq Var] in
/-- A locally closed term is unchanged by opening. -/
@[scoped grind =]
lemma open_lc (k t) (e : Term Var) (e_lc : e.LC) : e⟦k ↝ t⟧ = e :=
  lcAt_openRec_above_lcAt e t 0 k k.zero_le ((lcAt_iff_LC e).mpr e_lc)

omit [DecidableEq Var] in
/-- Opening is associative for nonclashing locally closed terms. -/
lemma swap_open (k n : ℕ) (t₁ t₂ m : Term Var) (neq : k ≠ n) (h1 : t₁.LC) (h2 : t₂.LC) :
    m⟦n ↝ t₂⟧⟦k ↝ t₁⟧ = m⟦k ↝ t₁⟧⟦n ↝ t₂⟧ := by
  induction m generalizing k n with grind

/- If opening yields `app m x`, the original term was `app m (bvar 0)`. -/
lemma open_eq_app {x : Var} {m n : Term Var} (hw_n : x ∉ n.fv) (hw_m : x ∉ m.fv) (lc_m : LC m)
    (h : n ^ fvar x = app m (fvar x)) : n = app m (bvar 0) := by
  apply open_injective x n _ hw_n (by grind)
  grind [open_lc 0 (fvar x) m lc_m]

/-- Substitution of a locally closed term distributes with opening. -/
@[scoped grind =]
lemma subst_openRec (x : Var) (t : Term Var) (k : ℕ) (u e : Term Var) (lc : LC t) :
    (e⟦ k ↝ u ⟧)[x := t] = e[x := t]⟦k ↝ u [ x := t ]⟧ := by
  induction e generalizing k with grind

/-- Specialize `subst_openRec` to the first opening. -/
lemma subst_open (x : Var) (t : Term Var) (u e : Term Var) (lc : LC t) :
    (e ^ u)[x := t] = e[x := t] ^ u [ x := t ] := by grind

/-- Specialize `subst_open` to the free variables. -/
theorem subst_open_var (x y : Var) (u e : Term Var) (neq : y ≠ x) (u_lc : LC u) :
    (e ^ fvar x)[y := u] = e[y := u] ^ fvar x := by grind

/-- Substitution of locally closed terms is locally closed. -/
@[scoped grind ←]
theorem subst_lc {x : Var} {e u : Term Var} (e_lc : LC e) (u_lc : LC u) : LC (e [x := u]) := by
  induction e_lc
  case' abs => apply LC.abs (free_union Var)
  all_goals grind

set_option linter.unusedDecidableInType false in
/-- Opening of locally closed terms is locally closed. -/
@[scoped grind ←]
theorem beta_lc {M N : Term Var} (m_lc : M.abs.LC) (n_lc : LC N) : LC (M ^ N) := by
  cases m_lc with
  | abs => grind [fresh_exists <| free_union [fv] Var]

/-- Closing then opening is equivalent to substitution. -/
@[scoped grind =]
lemma close_openRec_to_subst (m n : Term Var) (x : Var) (k : ℕ) (m_lc : LC m) (n_lc : LC n) :
    m ⟦k ↜ x⟧⟦k ↝ n⟧ = m [x := n] := by
  induction m_lc generalizing k with
  | abs xs t =>
    have ⟨x', _⟩ := fresh_exists <| free_union [fv] Var
    simp only [closeRec_abs, openRec_abs, subst_abs]
    rw [open_close x' (t⟦k+1 ↜ x⟧⟦k+1 ↝ n⟧) 0, open_close x' (t[x := n]) 0]
    · grind [swap_open, =_ swap_open_fvar_close]
    · grind [subst_preserve_not_fvar]
    · grind [open_preserve_not_fvar]
  | _ => grind

@[scoped grind =]
lemma close_open_to_subst (m n : Term Var) (x : Var) (m_lc : LC m) (n_lc : LC n) :
    (m ^* x) ^ n = m [x := n] := close_openRec_to_subst m n x 0 m_lc n_lc

/-- Closing and opening are inverses. -/
lemma close_openRec (x : Var) (t : Term Var) (k : ℕ) (t_lc : LC t) : t⟦k ↜ x⟧⟦k ↝ fvar x⟧ = t := by
  grind [subst_refl]

/-- Closing and opening are inverses. -/
lemma close_open (x : Var) (t : Term Var) (t_lc : LC t) : (t ^* x) ^ fvar x = t :=
  close_openRec x t 0 t_lc

end LambdaCalculus.LocallyNameless.Untyped.Term

end Cslib
