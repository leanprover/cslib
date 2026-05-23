/-
Copyright (c) 2025 David Wegmann. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Opus 4.7 (via Claude Code), David Wegmann
-/


module

public import Cslib.Foundations.Data.HasFresh
public import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.Properties
public import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.ParallelSubst

/-! # Substitution environments for untyped lambda calculus

A substitution *environment* is a **finitely-supported assignment** `Var → Term Var`:
the assignment itself, together with a `Finset` of variables outside which it acts as
the identity. "Applying an environment" is just the parallel substitution
`Term.psubst E.toAssignment` — there is no separate multi-substitution operation.

The finite support is what lets the strong-normalization proof pick variables fresh
for the substitution. Because the support is carried in the structure, the
domain/free-variable lemmas are immediate (no induction).
-/

@[expose] public section

namespace Cslib

universe u

namespace LambdaCalculus.LocallyNameless.Untyped.Term

variable {Var : Type u}

/-- A substitution environment: a finitely-supported assignment of terms to variables.
`support` over-approximates the set of variables the assignment moves. -/
structure Env (Var : Type u) where
  /-- The underlying assignment. -/
  toAssignment : Var → Term Var
  /-- A finite superset of the variables actually moved by the assignment. -/
  support : Finset Var
  /-- Outside the support, the assignment is the identity. -/
  mem_support : ∀ {x : Var}, toAssignment x ≠ fvar x → x ∈ support

namespace Env

/-- The domain of an environment: the variables it (potentially) moves. -/
def dom (E : Env Var) : Finset Var := E.support

/-- The free variables occurring in the terms the environment substitutes. -/
def fv [DecidableEq Var] (E : Env Var) : Finset Var :=
  E.support.biUnion (fun x => (E.toAssignment x).fv)

/-- The identity environment, leaving every variable untouched. -/
def empty : Env Var := ⟨fvar, ∅, fun h => absurd rfl h⟩

@[simp] lemma empty_toAssignment : (empty : Env Var).toAssignment = fvar := rfl

/-- Extend an environment with a new binding `x ↦ s`. -/
def update [DecidableEq Var] (E : Env Var) (x : Var) (s : Term Var) : Env Var where
  toAssignment := Function.update E.toAssignment x s
  support := insert x E.support
  mem_support := by
    intro y hy
    by_cases h : y = x
    · subst h; exact Finset.mem_insert_self _ _
    · rw [Function.update_of_ne h] at hy
      exact Finset.mem_insert_of_mem (E.mem_support hy)

@[simp] lemma update_toAssignment [DecidableEq Var] (E : Env Var) (x : Var) (s : Term Var) :
    (E.update x s).toAssignment = Function.update E.toAssignment x s := rfl

end Env

/-- An environment is locally closed if every variable maps to a locally closed term. -/
def env_LC (E : Env Var) : Prop := ∀ x, (E.toAssignment x).LC

lemma env_LC_empty : env_LC (Env.empty : Env Var) := fun x => by simpa using LC.fvar x

lemma env_LC_update [DecidableEq Var] {E : Env Var} {x : Var} {s : Term Var}
    (lc_s : LC s) (lc_E : env_LC E) : env_LC (E.update x s) := by
  intro y
  rw [Env.update_toAssignment]
  by_cases h : y = x
  · subst h; rwa [Function.update_self]
  · rw [Function.update_of_ne h]; exact lc_E y

/-! ## Assignment lemmas -/

/-- Outside its domain, the assignment is the identity. Immediate from `mem_support`. -/
lemma toAssignment_fresh {E : Env Var} {x : Var} (h : x ∉ E.dom) : E.toAssignment x = fvar x := by
  by_contra hc
  exact h (E.mem_support hc)

/-- A locally closed environment maps every variable to a locally closed term. -/
lemma toAssignment_lc {E : Env Var} (h : env_LC E) (x : Var) : LC (E.toAssignment x) := h x

/-- If `x` is fresh for the environment and distinct from `y`, then it does not occur
free in the term `y` maps to. -/
lemma toAssignment_not_fvar [DecidableEq Var] {E : Env Var} {x y : Var}
    (hx : x ∉ E.fv) (hxy : x ≠ y) : x ∉ (E.toAssignment y).fv := by
  by_cases hy : y ∈ E.support
  · exact fun hc => hx (Finset.mem_biUnion.mpr ⟨y, hy, hc⟩)
  · rw [toAssignment_fresh hy]; simpa using hxy

/-! ## Substitution lemmas -/

/-- Parallel substitution by an assignment of locally closed terms commutes with
opening. -/
lemma psubst_openRec [HasFresh Var] (σ : Var → Term Var) (lc : ∀ y, LC (σ y)) :
    ∀ (k : ℕ) (u e : Term Var), psubst σ (e⟦k ↝ u⟧) = (psubst σ e)⟦k ↝ psubst σ u⟧ := by
  intro k u e
  induction e generalizing k with
    grind [openRec_bvar, openRec_fvar, openRec_app, openRec_abs,
      psubst_bvar, psubst_fvar, psubst_app, psubst_abs]

/-- Applying an environment commutes with opening by a fresh variable, provided the
environment is locally closed. -/
lemma psubst_open_var [HasFresh Var] (M : Term Var) (E : Env Var) (x : Var)
    (h_ndom : x ∉ E.dom) (h_lc : env_LC E) :
    psubst E.toAssignment (M ^ fvar x) = psubst E.toAssignment M ^ fvar x := by
  simp only [open']
  rw [psubst_openRec E.toAssignment h_lc, psubst_fvar, toAssignment_fresh h_ndom]

/-- Extending with a binding `x ↦ s` fresh for the environment is the same as applying
the environment and then substituting `x` by `s`. -/
lemma psubst_update [DecidableEq Var] {x : Var} (s : Term Var) (E : Env Var) (M : Term Var)
    (hd : x ∉ E.dom) (hf : x ∉ E.fv) :
    psubst (E.update x s).toAssignment M = (psubst E.toAssignment M)[x := s] := by
  simp only [Env.update_toAssignment]
  induction M with
    grind [subst_fresh, Function.update_self, Function.update_of_ne,
      toAssignment_fresh, toAssignment_not_fvar]

end LambdaCalculus.LocallyNameless.Untyped.Term

end Cslib
