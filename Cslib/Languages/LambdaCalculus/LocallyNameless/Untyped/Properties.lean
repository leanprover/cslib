/-
Copyright (c) 2025 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.Basic

public section

namespace Cslib

universe u

variable {Var : Type u}

namespace LambdaCalculus.LocallyNameless.Untyped.Term

attribute [grind =] Finset.union_singleton

/-- An opening appearing in both sides of an equality of terms can be removed. -/
lemma open_lc_aux (e : Term Var) (j v i u) (neq : i ≠ j) (eq : e⟦j ↝ v⟧ = e⟦j ↝ v⟧⟦i ↝ u⟧) :
    e = e ⟦i ↝ u⟧ := by
  induction e generalizing j i <;> grind

/-- Opening is associative for nonclashing free variables. -/
lemma swap_open_fvars (k n : ℕ) (x y : Var) (m : Term Var) (neq : k ≠ n) :
    m⟦n ↝ fvar y⟧⟦k ↝ fvar x⟧ = m⟦k ↝ fvar x⟧⟦n ↝ fvar y⟧ := by
  induction m generalizing k n <;> grind

variable [DecidableEq Var]

/-- Substitution of a free variable not present in a term leaves it unchanged. -/
theorem subst_fresh (x : Var) (t sub : Term Var) (nmem : x ∉ t.fv) : t [x := sub] = t := by
  induction t <;> grind

/- Opening and closing are inverses. -/
lemma open_close (x : Var) (t : Term Var) (k : ℕ) (nmem : x ∉ t.fv) : t = t⟦k ↝ fvar x⟧⟦k ↜ x⟧ := by
  induction t generalizing k <;> grind

/-- Opening is injective. -/
lemma open_injective (x : Var) (M M') (free_M : x ∉ M.fv) (free_M' : x ∉ M'.fv)
    (eq : M ^ fvar x = M' ^ fvar x) : M = M' := by
  grind [open_close x M 0 free_M, open_close x M' 0 free_M']

/-- Opening and closing are associative for nonclashing free variables. -/
lemma swap_open_fvar_close (k n : ℕ) (x y : Var) (m : Term Var) (neq₁ : k ≠ n) (neq₂ : x ≠ y) :
    m⟦n ↝ fvar y⟧⟦k ↜ x⟧ = m⟦k ↜ x⟧⟦n ↝ fvar y⟧ := by
  induction m generalizing k n <;> grind

/-- Closing preserves free variables. -/
lemma close_preserve_not_fvar {k x y} (m : Term Var) (nmem : x ∉ m.fv) : x ∉ (m⟦k ↜ y⟧).fv := by
  induction m generalizing k <;> grind

/-- Opening to a fresh free variable preserves free variables. -/
lemma open_fresh_preserve_not_fvar {k x y} (m : Term Var) (nmem : x ∉ m.fv) (neq : x ≠ y) :
    x ∉ (m⟦k ↝ fvar y⟧).fv := by
  induction m generalizing k <;> grind

/-- Substitution preserves free variables. -/
lemma subst_preserve_not_fvar {x y : Var} (m n : Term Var) (nmem : x ∉ m.fv ∪ n.fv) :
    x ∉ (m [y := n]).fv := by
  induction m <;> grind

/-- Closing removes a free variable. -/
@[scoped grind ←]
lemma close_var_not_fvar_rec (x) (k) (t : Term Var) : x ∉ (t⟦k ↜ x⟧).fv := by
  induction t generalizing k <;> grind

/-- Specializes `close_var_not_fvar_rec` to first closing. -/
lemma close_var_not_fvar (x) (t : Term Var) : x ∉ (t ^* x).fv := close_var_not_fvar_rec x 0 t

variable [HasFresh Var]

omit [DecidableEq Var] in
/-- A locally closed term is unchanged by opening. -/
@[scoped grind =_]
lemma open_lc (k t) (e : Term Var) (e_lc : e.LC) : e = e⟦k ↝ t⟧ := by
  induction e_lc generalizing k with
  | abs xs e _ _ => grind [open_lc_aux e 0 (fvar (fresh xs)) (k+1) t]
  | _ => grind

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

/-- Opening to a term `t` is equivalent to opening to a free variable and substituting for `t`. -/
lemma subst_intro (x : Var) (t e : Term Var) (mem : x ∉ e.fv) (t_lc : LC t) :
    e ^ t = (e ^ fvar x) [ x := t ] := by grind [subst_fresh]

scoped grind_pattern subst_intro => open' e t, open' e (fvar x)

set_option linter.unusedDecidableInType false in
/-- Opening of locally closed terms is locally closed. -/
@[scoped grind ←]
theorem beta_lc {M N : Term Var} (m_lc : M.abs.LC) (n_lc : LC N) : LC (M ^ N) := by
  cases m_lc with
  | abs => grind [fresh_exists <| free_union [fv] Var]

/-- Opening then closing is equivalent to substitution. -/
@[scoped grind =]
lemma open_close_to_subst (m : Term Var) (x y : Var) (k : ℕ) (m_lc : LC m) :
    m ⟦k ↜ x⟧⟦k ↝ fvar y⟧ = m [x := fvar y] := by
  induction m_lc generalizing k with
  | abs xs t =>
    have ⟨x', _⟩ := fresh_exists <| free_union [fv] Var
    grind [
      swap_open_fvars, =_ swap_open_fvar_close,
      open_close x' (t⟦k+1 ↜ x⟧⟦k+1 ↝ fvar y⟧) 0, open_close x' (t[x := fvar y]) 0,
      open_fresh_preserve_not_fvar, close_preserve_not_fvar, subst_preserve_not_fvar]
  | _ => grind

/-- Closing and opening are inverses. -/
lemma close_open (x : Var) (t : Term Var) (k : ℕ) (t_lc : LC t) : t⟦k ↜ x⟧⟦k ↝ fvar x⟧ = t := by
  induction t_lc generalizing k with
  | abs _ t _ ih =>
    let z := t⟦k + 1 ↜ x⟧⟦k + 1 ↝ fvar x⟧
    have ⟨y, _⟩ := fresh_exists <| free_union [fv] Var
    grind [ih y ?_ (k+1), open_injective, swap_open_fvar_close, swap_open_fvars]
  | _ => grind

end LambdaCalculus.LocallyNameless.Untyped.Term

end Cslib
