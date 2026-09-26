/-
Copyright (c) 2026 Elimia (Sehun Kim). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elimia (Sehun Kim)
-/

module

public import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.Basic

/-!
Depth of locally nameless terms

This module defines the `depth` of an untyped lambda term in the locally nameless representation.
`depth` measures the maximum nesting of abstractions surrounding any variable.

We also provide a custom induction principle `ind_on_depth` that is convenient when reasoning by
induction on depth, together with basic lemmas showing that opening a term with a free variable
does not change its depth.
-/


@[expose] public section

namespace Cslib.LambdaCalculus.LocallyNameless.Untyped.Term

universe u

variable {Var : Type u}

/-- `depth` counts the maximum number of the lambdas that are enclosing variables. -/
@[simp, scoped grind =]
def depth : Term Var → ℕ
| bvar _ => 0
| fvar _ => 0
| app t₁ t₂ => max (depth t₁) (depth t₂)
| abs t => depth t + 1

set_option linter.tacticAnalysis.verifyGrindOnly false in
@[elab_as_elim]
protected lemma ind_on_depth (P : Term Var → Prop) (bvar : ∀ i, P (bvar i)) (fvar : ∀ x, P (fvar x))
    (app : ∀ M N, P M → P N → P (app M N))
    (abs : ∀ M, P M → (∀ N, N.depth ≤ M.depth → P N) → P M.abs)
    (M : Term Var) : P M := by
  induction h : M.depth using Nat.strong_induction_on generalizing M with | _ n ih
  induction M with
  | abs M' => apply abs M' <;> grind
  | bvar | fvar => grind
  | app => apply app <;> grind only [depth, = max_def]

/-- The depth of the lambda expression doesn't change by opening at i-th bound variable
 for some free variable. -/
 @[simp, scoped grind =]
lemma depth_openRec_fvar_eq_depth (M : Term Var) (x : Var) (i : ℕ) :
    (M⟦i ↝ fvar x⟧).depth = M.depth := by
  induction M generalizing i <;> grind

/-- The depth of the lambda expression doesn't change by opening for some free variable. -/
theorem depth_open_fvar_eq_depth (M : Term Var) (x : Var) : depth (M ^ fvar x) = depth M :=
  depth_openRec_fvar_eq_depth M x 0

end Cslib.LambdaCalculus.LocallyNameless.Untyped.Term
