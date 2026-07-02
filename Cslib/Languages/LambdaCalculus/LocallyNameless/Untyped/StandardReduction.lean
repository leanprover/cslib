/-
Copyright (c) 2026 Maximiliano Onofre Martínez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maximiliano Onofre Martínez
-/

module

public import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.CallByName

/-! # Standard Reduction and the Standardization Theorem

## Reference

* [B. Calisto, *Formalization in Coq of the Standardization Theorem for λ-calculus*][Calisto2022]

-/

@[expose] public section

set_option linter.unusedDecidableInType false

namespace Cslib

universe u

variable {Var : Type u}

namespace LambdaCalculus.LocallyNameless.Untyped.Term

/-- The Standard reduction relation. -/
@[reduction_sys "ₛ"]
inductive Standard : Term Var → Term Var → Prop
/-- Free variables standardly reduce to themselves. -/
| fvar (x : Var) : Standard (fvar x) (fvar x)
/-- Congruence rule for application. -/
| app  : Standard L L' → Standard M M' → Standard (app L M) (app L' M')
/-- Congruence rule for lambda terms. -/
| abs (xs : Finset Var) :
    (∀ x ∉ xs, Standard (m ^ fvar x) (m' ^ fvar x)) → Standard (abs m) (abs m')
/-- Standard reduction of a head redex. -/
| rdx : LC m → LC n → m ↠ₙ (abs m') → Standard (m' ^ n) p → Standard (app m n) p

variable {M N P M' N' : Term Var}

/-- The left side of a standard reduction is locally closed. -/
lemma Standard.lc_l (step : M ⭢ₛ N) : LC M := by
  induction step
  case abs xs _ ih => exact LC.abs xs _ ih
  all_goals grind

/-- Standard reduction is reflexive for locally closed terms. -/
lemma Standard.lc_refl (M : Term Var) (lc : LC M) : M ⭢ₛ M := by
  induction lc
  all_goals constructor <;> assumption

/-- The right side of a standard reduction is locally closed. -/
lemma Standard.lc_r (step : M ⭢ₛ N) : LC N := by
  induction step
  case abs xs _ ih => exact LC.abs xs _ ih
  all_goals grind

/-- A single Call-by-Name step is a standard reduction. -/
lemma Standard.of_cbn_step (step : M ⭢ₙ N) (lc_N : LC N) : M ⭢ₛ N := by
  induction step
  case base h_beta =>
    cases h_beta
    exact rdx (by assumption) (by assumption) .refl (lc_refl _ lc_N)
  case app L _ _ lc_L _ ih =>
    exact app (ih (by cases lc_N; assumption)) (lc_refl L lc_L)

/-- A Call-by-Name step followed by a standard reduction is a standard reduction. -/
lemma Standard.cbn_step_trans (step : M ⭢ₙ P) (std : P ⭢ₛ N) : M ⭢ₛ N := by
  induction step generalizing N
  case base h_beta =>
    cases h_beta
    exact rdx (by assumption) (by assumption) .refl std
  case app step_M ih =>
    cases std with
    | app std_L' std_M => exact app (ih std_L') std_M
    | rdx _ lc_Z cbn_m std_body =>
      exact rdx (CBN.lc_l step_M) lc_Z (.head step_M cbn_m) std_body

/-- A Call-by-Name reduction followed by a standard reduction is a standard reduction. -/
lemma Standard.cbn_trans (h1 : M ↠ₙ P) (h2 : P ⭢ₛ N) : M ⭢ₛ N := by
  induction h1 with
  | refl => exact h2
  | tail _ h_step ih => exact ih (cbn_step_trans h_step h2)

/-- Call-by-Name reduction is contained in standard reduction. -/
lemma Standard.of_cbn (step : M ↠ₙ N) (lc_N : LC N) : M ⭢ₛ N :=
  cbn_trans step (lc_refl N lc_N)

variable [DecidableEq Var] [HasFresh Var]

/-- Standard reduction is preserved by substitution. -/
lemma Standard.subst (hM : M ⭢ₛ M') (hN : N ⭢ₛ N') (x : Var) (lc_N : LC N) (lc_N' : LC N') :
    (M [ x := N ]) ⭢ₛ (M' [ x := N' ]) := by
  induction hM generalizing N N'
  case fvar =>
    simp only [Term.subst_fvar]
    split
    · exact hN
    · exact fvar _
  case app ihL ihM =>
    rw [Term.subst_app]
    exact app (ihL hN lc_N lc_N') (ihM hN lc_N lc_N')
  case abs m m' _ _ ih =>
    simp only [Term.subst_abs]
    apply abs <| free_union [fv] Var
    intro y hy
    have h_neq : x ≠ y := by aesop
    rw [← Term.subst_open_var y x N m h_neq lc_N, ← Term.subst_open_var y x N' m' h_neq lc_N']
    exact ih y (by aesop) hN lc_N lc_N'
  case rdx n m' _ lc_m lc_n cbn_m std_p ih =>
    rw [Term.subst_app]
    have std_p_subst := ih hN lc_N lc_N'
    rw [Term.subst_open x N n m' lc_N] at std_p_subst
    exact rdx (Term.subst_lc (x := x) lc_m lc_N) (Term.subst_lc (x := x) lc_n lc_N)
      (CBN.steps_subst x cbn_m lc_N) std_p_subst

/-- A single full β-step is a standard reduction. -/
lemma Standard.of_beta_step (step : M ⭢βᶠ N) (lc_M : LC M) : M ⭢ₛ N := by
  induction step
  case base h_beta =>
    cases h_beta
    exact rdx (by assumption) (by assumption) .refl
      (lc_refl _ (Term.beta_lc (by assumption) (by assumption)))
  case appL A B _ _ _ =>
    have : LC A := by cases lc_M; assumption
    apply Standard.app <;> grind [lc_refl]
  case appR A _ _ _ _ =>
    have : LC A := by cases lc_M; assumption
    apply Standard.app <;> grind [lc_refl]
  case abs ih =>
    apply Standard.abs <| free_union [fv] Var
    intro x hx
    exact ih x (by aesop) (Term.beta_lc lc_M (by constructor))

/-- Standard reduction is contained in full β-reduction. -/
lemma Standard.to_redex (step : M ⭢ₛ N) : M ↠βᶠ N := by
  induction step
  case fvar => rfl
  case app step_L step_M ih_L ih_M =>
    exact .trans (FullBeta.redex_app_l_cong ih_L (Standard.lc_l step_M))
      (FullBeta.redex_app_r_cong ih_M (Standard.lc_r step_L))
  case abs xs _ ih => exact FullBeta.redex_abs_cong xs ih
  case rdx n m' _ lc_m lc_n cbn_m std_p ih =>
    have step1 := FullBeta.redex_app_l_cong (CBN.to_redex cbn_m) lc_n
    have step2 : Term.app (Term.abs m') n ↠βᶠ (m' ^ n) :=
      .single (Xi.base (Beta.beta (CBN.steps_lc_r lc_m cbn_m) lc_n))
    exact .trans step1 (.trans step2 ih)

/-- If a standard reduction reaches an abstraction, then its leading Call-by-Name
    reduction reaches an abstraction that standardly reduces to the same target. -/
lemma Standard.abs_inv (h : M ⭢ₛ N) (M' : Term Var) (eq : N = Term.abs M') :
    ∃ M'', M ↠ₙ Term.abs M'' ∧ Term.abs M'' ⭢ₛ Term.abs M' := by
  induction h generalizing M'
  case fvar => trivial
  case app => trivial
  case abs m_body m_target xs h_body ih =>
    cases eq
    exact ⟨m_body, .refl, Standard.abs xs h_body⟩
  case rdx m1 n1 m1' p1 lc_m1 lc_n1 cbn_m1 _ ih =>
    have ⟨p'', cbn_body, std_p''⟩ := ih M' eq
    have step1 : Term.app m1 n1 ↠ₙ Term.app (Term.abs m1') n1 := CBN.steps_app_l_cong cbn_m1 lc_n1
    have step2 : Term.app (Term.abs m1') n1 ⭢ₙ (m1' ^ n1) :=
      CBN.base (Beta.beta (CBN.steps_lc_r lc_m1 cbn_m1) lc_n1)
    exact ⟨p'', .trans step1 (.head step2 cbn_body), std_p''⟩

/-- Standard reduction of abstractions is preserved by opening. -/
lemma Standard.abs_subst
    (h_abs : Term.abs M ⭢ₛ Term.abs M') (hN : N ⭢ₛ N') (lc_N : LC N) (lc_N' : LC N') :
    (M ^ N) ⭢ₛ (M' ^ N') := by
  cases h_abs
  case abs h_body =>
    have ⟨y, _⟩ := fresh_exists <| free_union [fv] Var
    have h_subst := Standard.subst (h_body y (by aesop)) hN y lc_N lc_N'
    rw [← Term.subst_intro y N M (by aesop), ← Term.subst_intro y N' M' (by aesop)] at h_subst
    exact h_subst

/-- A standard reduction followed by a full β-step is a standard reduction. -/
lemma Standard.trans_step (h1 : M ⭢ₛ P) (h2 : P ⭢βᶠ N) : M ⭢ₛ N := by
  induction h1 generalizing N
  case fvar => contradiction
  case rdx lc_L lc_M cbn _ ih => exact Standard.rdx lc_L lc_M cbn (ih h2)
  case abs p_body ih =>
    cases h2
    case abs ih_beta =>
      apply Standard.abs <| free_union [fv] Var
      intro y hy
      exact ih y (by aesop) (ih_beta y (by aesop))
    · grind
  case app L1 _ M1 _ std_L std_M ih_L ih_M =>
    cases h2
    case appL step_M => exact Standard.app std_L (ih_M step_M)
    case appR step_L _ => exact Standard.app (ih_L step_L) std_M
    case base h_beta =>
      cases h_beta
      have ⟨L1', cbn_L1, std_abs⟩ := Standard.abs_inv std_L _ rfl
      have std_subst := Standard.abs_subst std_abs std_M (Standard.lc_l std_M) (Standard.lc_r std_M)
      have step1 : Term.app L1 M1 ↠ₙ Term.app (Term.abs L1') M1 :=
        CBN.steps_app_l_cong cbn_L1 (Standard.lc_l std_M)
      have step2 : Term.app (Term.abs L1') M1 ⭢ₙ (L1' ^ M1) :=
        CBN.base (Beta.beta (CBN.steps_lc_r (Standard.lc_l std_L) cbn_L1) (Standard.lc_l std_M))
      exact Standard.cbn_trans (.trans step1 (.single step2)) std_subst

/-- A standard reduction followed by a full β-reduction is a standard reduction. -/
lemma Standard.trans_redex (h1 : M ⭢ₛ P) (h2 : P ↠βᶠ N) : M ⭢ₛ N := by
  induction h2 with
  | refl => exact h1
  | tail _ step ih => exact Standard.trans_step ih step

/-- Standard reduction is transitive. -/
lemma Standard.trans (h1 : M ⭢ₛ P) (h2 : P ⭢ₛ N) : M ⭢ₛ N :=
  trans_redex h1 (to_redex h2)

/-- The standardization theorem: every full β-reduction is a standard reduction. -/
theorem Standard.standardization (lc_M : LC M) (step : M ↠βᶠ N) : M ⭢ₛ N := by
  induction step with
  | refl => exact Standard.lc_refl M lc_M
  | tail _ h_step ih => exact ih.trans (Standard.of_beta_step h_step (FullBeta.step_lc_l h_step))

/-- Standard reduction coincides with full β-reduction on locally closed terms. -/
theorem Standard.iff_redex (lc_M : LC M) : M ⭢ₛ N ↔ M ↠βᶠ N :=
  ⟨to_redex, standardization lc_M⟩

end LambdaCalculus.LocallyNameless.Untyped.Term

end Cslib
