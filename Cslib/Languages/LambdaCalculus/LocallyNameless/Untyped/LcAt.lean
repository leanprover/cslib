/-
Copyright (c) 2026 Elimia (Sehun Kim). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elimia (Sehun Kim)
-/

module

public import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.Basic

@[expose] public section

/-!

Alternative Definitions for LC:

This module defines `LcAt k M`, a more general definition of local closure. When k = 0, this is
equivalent to `LC`, as shown in `lcAt_iff_LC`.

-/

namespace Cslib.LambdaCalculus.LocallyNameless.Untyped.Term

universe u

variable {Var : Type u}

/-- `LcAt k M` is satisfied when all bound indices of M are smaller than `k`. -/
@[simp, scoped grind =]
def LcAt (k : ℕ) : Term Var → Prop
| bvar i => i < k
| fvar _ => True
| app t₁ t₂ => LcAt k t₁ ∧ LcAt k t₂
| abs t => LcAt (k + 1) t

/-- `depth` counts the maximum number of the lambdas that are enclosing variables. -/
@[simp, scoped grind =]
def depth : Term Var → ℕ
| bvar _ => 0
| fvar _ => 0
| app t₁ t₂ => max (depth t₁) (depth t₂)
| abs t => depth t + 1

@[elab_as_elim]
protected lemma ind_on_depth (P : Term Var → Prop) (bvar : ∀ i, P (bvar i)) (fvar : ∀ x, P (fvar x))
  (app : ∀ M N, P M → P N → P (app M N)) (abs : ∀ M, P M → (∀ N, N.depth ≤ M.depth → P N) → P M.abs)
  (M : Term Var) : P M := by
  have h {d : ℕ} {M : Term Var} (p : M.depth ≤ d) : P M := by
    induction d generalizing M with
    | zero => induction M <;> grind
    | succ =>
      induction M with
      | abs M' => apply abs M' <;> grind
      | _ => grind [sup_le_iff]
  exact h M.depth.le_refl

/-- The depth of the lambda expression doesn't change by opening at i-th bound variable
 for some free variable. -/
 @[simp, scoped grind =]
lemma depth_openRec_fvar_eq_depth (M : Term Var) (x : Var) (i : ℕ) :
    (M⟦i ↝ fvar x⟧).depth = M.depth := by
  induction M generalizing i <;> grind

/-- The depth of the lambda expression doesn't change by opening for some free variable. -/
theorem depth_open_fvar_eq_depth (M : Term Var) (x : Var) : depth (M ^ fvar x) = depth M :=
  depth_openRec_fvar_eq_depth M x 0

/-- Opening for some free variable at i-th bound variable, increments `LcAt`. -/
@[simp, scoped grind =]
theorem lcAt_openRec_fvar_iff_lcAt (M : Term Var) (x : Var) (i : ℕ) :
    LcAt i (M⟦i ↝ fvar x⟧) ↔ LcAt (i + 1) M := by
  induction M generalizing i <;> grind

/-- Opening for some free variable is locally closed if and only if `M` is `LcAt 1`. -/
theorem lcAt_open_fvar_iff_lcAt (M : Term Var) (x : Var) : LcAt 0 (M ^ fvar x) ↔ LcAt 1 M :=
  lcAt_openRec_fvar_iff_lcAt M x 0

/-- `M` is `LcAt 0` if and only if `M` is locally closed. -/
theorem lcAt_iff_LC (M : Term Var) [HasFresh Var] : LcAt 0 M ↔ M.LC := by
  induction M using LambdaCalculus.LocallyNameless.Untyped.Term.ind_on_depth with
    | abs =>
      constructor
      · grind [LC.abs ∅]
      · intros h2
        rcases h2 with ⟨⟩|⟨L,_,_⟩
        grind [fresh_exists L]
    | _ => grind [cases LC]

end Cslib.LambdaCalculus.LocallyNameless.Untyped.Term
