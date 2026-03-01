/-
Copyright (c) 2025 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.Data.Relation
public import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.Properties
public import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.LcAt

public section

set_option linter.unusedDecidableInType false

/-! # β-reduction for the λ-calculus

## References

* [A. Chargueraud, *The Locally Nameless Representation*] [Chargueraud2012]
* See also https://www.cis.upenn.edu/~plclub/popl08-tutorial/code/, from which
  this is partially adapted

-/

namespace Cslib

universe u

variable {Var : Type u}

namespace LambdaCalculus.LocallyNameless.Untyped.Term

/-- A single β-reduction step. -/
@[reduction_sys "βᶠ"]
inductive FullBeta : Term Var → Term Var → Prop
/-- Reduce an application to a lambda term. -/
| beta : LC (abs M)→ LC N → FullBeta (app (abs M) N) (M ^ N)
/-- Left congruence rule for application. -/
| appL: LC Z → FullBeta M N → FullBeta (app Z M) (app Z N)
/-- Right congruence rule for application. -/
| appR : LC Z → FullBeta M N → FullBeta (app M Z) (app N Z)
/-- Congruence rule for lambda terms. -/
| abs (xs : Finset Var) : (∀ x ∉ xs, FullBeta (M ^ fvar x) (N ^ fvar x)) → FullBeta (abs M) (abs N)

namespace FullBeta

attribute [scoped grind .] appL appR

variable {M M' N N' : Term Var}

/-- The left side of a reduction is locally closed. -/
@[scoped grind →]
lemma step_lc_l (step : M ⭢βᶠ M') : LC M := by
  induction step <;> constructor
  all_goals assumption



/-- Left congruence rule for application in multiple reduction. -/
@[scoped grind ←]
theorem redex_app_l_cong (redex : M ↠βᶠ M') (lc_N : LC N) : app M N ↠βᶠ app M' N := by
  induction redex <;> grind

/-- Right congruence rule for application in multiple reduction. -/
@[scoped grind ←]
theorem redex_app_r_cong (redex : M ↠βᶠ M') (lc_N : LC N) : app N M ↠βᶠ app N M' := by
  induction redex <;> grind

variable [HasFresh Var] [DecidableEq Var]

/-- The right side of a reduction is locally closed. -/
@[scoped grind →]
lemma step_lc_r (step : M ⭢βᶠ M') : LC M' := by
  induction step
  case' abs => constructor; assumption
  all_goals grind

lemma steps_lc_or_rfl {M M' : Term Var} (redex : M ↠βᶠ M') : (LC M ∧ LC M') ∨ M = M' := by
  grind

/-- Substitution respects a single reduction step. -/
lemma redex_subst_cong (s s' : Term Var) (x y : Var) (step : s ⭢βᶠ s') :
    s [ x := fvar y ] ⭢βᶠ s' [ x := fvar y ] := by
  induction step
  case beta m n abs_lc n_lc =>
    cases abs_lc with | abs xs _ mem =>
      rw [subst_open x (fvar y) n m (by grind)]
      refine beta ?_ (by grind)
      exact subst_lc (LC.abs xs m mem) (LC.fvar y)
  case abs => grind [abs <| free_union Var]
  all_goals grind

/-- Substitution respects a single reduction step. -/
lemma redex_subst_cong_lc (s s' t : Term Var) (x : Var) (step : s ⭢βᶠ s') (h_lc : LC t) :
    s [ x := t ] ⭢βᶠ s' [ x := t ] := by
  induction step with
  | beta => grind [subst_open, beta]
  | abs  => grind [abs <| free_union Var]
  | _ => grind







/-- Abstracting then closing preserves a single reduction. -/
lemma step_abs_close {x : Var} (step : M ⭢βᶠ M') : M⟦0 ↜ x⟧.abs ⭢βᶠ M'⟦0 ↜ x⟧.abs := by
  grind [abs ∅, redex_subst_cong]

/-- Abstracting then closing preserves multiple reductions. -/
lemma redex_abs_close {x : Var} (step : M ↠βᶠ M') : (M⟦0 ↜ x⟧.abs ↠βᶠ M'⟦0 ↜ x⟧.abs) :=  by
  induction step using Relation.ReflTransGen.trans_induction_on
  case refl => rfl
  case single ih => exact Relation.ReflTransGen.single (step_abs_close ih)
  case trans l r => exact Relation.ReflTransGen.trans l r

/-- Multiple reduction of opening implies multiple reduction of abstraction. -/
theorem step_abs_cong (xs : Finset Var) (cofin : ∀ x ∉ xs, (M ^ fvar x) ⭢βᶠ (M' ^ fvar x)) :
    M.abs ⭢βᶠ M'.abs := by
  have ⟨fresh, _⟩ := fresh_exists <| free_union [fv] Var
  rw [open_close fresh M 0 ?_, open_close fresh M' 0 ?_]
  all_goals grind [step_abs_close]

/-- Multiple reduction of opening implies multiple reduction of abstraction. -/
theorem redex_abs_cong (xs : Finset Var) (cofin : ∀ x ∉ xs, (M ^ fvar x) ↠βᶠ (M' ^ fvar x)) :
    M.abs ↠βᶠ M'.abs := by
  have ⟨fresh, _⟩ := fresh_exists <| free_union [fv] Var
  rw [open_close fresh M 0 ?_, open_close fresh M' 0 ?_]
  all_goals grind [redex_abs_close]

theorem redex_abs_fvar_finset_exists (xs : Finset Var)
  (M M' : Term Var)
  (step : M.abs ⭢βᶠ M'.abs) :
  ∃ (L : Finset Var), ∀ x ∉ L, (M ^ fvar x) ⭢βᶠ (M' ^ fvar x) := by
  cases step
  case abs L cofin => exists L


lemma step_open_cong
  (s s' t) (L : Finset Var) (step : ∀ x ∉ L, (s ^ fvar x) ⭢βᶠ (s' ^ fvar x)) (h_lc : LC t) :
    (s ^ t) ⭢βᶠ (s' ^ t) := by
  have ⟨x, _⟩ := fresh_exists <| free_union [fv] Var
  grind [subst_intro, redex_subst_cong_lc]

lemma invert_steps_abs {s t : Term Var} (step : s.abs ↠βᶠ t) :
    ∃ (s' : Term Var), s.abs ↠βᶠ s'.abs ∧ t = s'.abs := by
  induction step
  · case refl => aesop
  · case tail steps step ih =>
      match ih with
      | ⟨ s', step_s, eq⟩ =>
        rw[eq] at step
        cases step
        · case abs s'' L step =>
          apply step_abs_cong at step
          grind



lemma steps_open_l_abs (s s' t : Term Var)
  (steps : s.abs ↠βᶠ s'.abs) (lc_s : LC s.abs) (lc_t : LC t) :
  (s ^ t) ↠βᶠ (s' ^ t) := by
  generalize eq : s.abs = s_abs at steps
  generalize eq' : s'.abs = s'_abs at steps
  revert s s'
  induction steps
  · case refl => grind
  · case tail steps step ih =>
    intro s s'' lc_sabs eq1 eq2
    rw[←eq1] at steps
    match (invert_steps_abs steps) with
    | ⟨s', step_s, eq⟩ =>
      specialize (ih s s' lc_sabs eq1 eq.symm)
      transitivity
      · apply ih
      · rw[eq,←eq2] at step
        apply Relation.ReflTransGen.single
        have ⟨ L, cofin⟩ := redex_abs_fvar_finset_exists (free_union [fv] Var) s' s'' step
        apply step_open_cong1
        · assumption
        · assumption

lemma step_subst_r {x : Var} (s t t' : Term Var) (step : t ⭢βᶠ t') (h_lc : LC s) :
    (s [ x := t ]) ↠βᶠ (s [ x := t' ]) := by
  induction h_lc
  · case fvar y =>
      rw[Term.subst_fvar, Term.subst_fvar]
      grind
  · case abs L N h_lc ih =>
      simp[subst_abs]
      apply FullBeta.redex_abs_cong (L ∪ {x})
      intro y h_fresh
      rw[←Term.subst_open_var, ←Term.subst_open_var] <;> try grind[FullBeta.step_lc_r, FullBeta.step_lc_l]
  · case app l r ih_l ih_r =>
    transitivity
    · apply FullBeta.redex_app_r_cong
      · apply ih_r
      · grind[Term.subst_lc, FullBeta.step_lc_l]
    · apply FullBeta.redex_app_l_cong
      · apply ih_l
      · grind[Term.subst_lc, FullBeta.step_lc_r]

lemma steps_subst_cong2 {x : Var} (s t t' : Term Var) (step : t ↠βᶠ t') (h_lc : LC s) :
    (s [ x := t ]) ↠βᶠ (s [ x := t' ]) := by
  induction step
  · case refl => rfl
  · case tail t' t'' steps step ih =>
    transitivity
    · apply ih
    · apply step_subst_r <;> assumption

lemma steps_open_cong_abs (s s' t t' : Term Var)
    (step1 : t ↠βᶠ t')
    (step2 : s.abs ↠βᶠ s'.abs)
    (lc_t : LC t)
    (lc_s : LC s.abs) :
    (s ^ t) ↠βᶠ (s' ^ t') := by
    have lcsabs := lc_s
    cases lc_s
    · case abs _ L h_lc =>
      let x := fresh (L ∪ s.fv ∪ s'.fv ∪ t.fv ∪ t'.fv)
      have H : x ∉ (L ∪ s.fv ∪ s'.fv ∪ t.fv ∪ t'.fv) := fresh_notMem _
      rw[subst_intro x t s, subst_intro x t' s'] <;> try grind[FullBeta.steps_lc]
      · transitivity
        · apply steps_subst_cong2
          · assumption
          · grind
        · rw[←subst_intro, ←subst_intro] <;> try grind[FullBeta.steps_lc]
          · apply FullBeta.steps_open_l_abs <;> try grind[FullBeta.steps_lc]

end LambdaCalculus.LocallyNameless.Untyped.Term.FullBeta

end Cslib
