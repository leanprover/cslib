/-
Copyright (c) 2025 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

import Cslib.Computability.LambdaCalculus.STLC.LocallyNameless.Basic
import Cslib.Computability.LambdaCalculus.Untyped.LocallyNameless.Basic
import Cslib.Computability.LambdaCalculus.Untyped.LocallyNameless.Properties
import Cslib.Computability.LambdaCalculus.Untyped.LocallyNameless.FullBetaConfluence

/-! # λ-calculus

Typing safety of the simply typed λ-calculus, with a locally nameless representation of syntax.

## References

* [A. Chargueraud, *The Locally Nameless Representation*] [Chargueraud2012]
* See also https://www.cis.upenn.edu/~plclub/popl08-tutorial/code/, from which
  this is partially adapted

-/

universe u

variable {Var : Type u} [DecidableEq Var]

namespace LambdaCalculus.LocallyNameless.STLC.Typing

variable {Γ Δ Φ : Ctx Var Ty}

/-- Typing is preserved on permuting a context. -/
theorem perm : Γ.Perm Δ → Γ ⊢ t ∶ τ → Δ ⊢ t ∶ τ := by 
  intros _ der
  revert Δ
  induction der <;> intros Δ p
  case app => aesop
  case var => 
    have := @p.mem_iff
    aesop
  case abs ih => 
    constructor
    intros x mem
    exact ih x mem (by aesop)

/-- Weakening of a typing derivation with an appended context. -/
lemma weakening_strengthened : 
    Γ ++ Δ ⊢ t ∶ τ → (Γ ++ Φ ++ Δ).Ok → (Γ ++ Φ ++ Δ) ⊢ t ∶ τ := by
  generalize eq : Γ ++ Δ = Γ_Δ
  intros h
  revert Γ Δ Φ
  induction h <;> intros Γ Δ Φ eq ok_Γ_Φ_Δ
  case var => aesop
  case app => aesop
  case abs σ Γ' τ t xs ext ih =>
    apply Typing.abs (xs ∪ (Γ ++ Φ ++ Δ).dom)
    intros x _
    have h : (x, σ) :: Γ ++ Δ = (x, σ) :: Γ' := by aesop
    refine @ih x (by aesop) _ _ Φ h ?_
    constructor <;> aesop

/-- Weakening of a typing derivation by an additional context. -/
lemma weakening : Γ ⊢ t ∶ τ → (Γ ++ Δ).Ok → Γ ++ Δ ⊢ t ∶ τ := by
  intros der ok
  rw [←List.append_nil (Γ ++ Δ)] at *
  exact weakening_strengthened (by simp_all) ok

/-- Typing derivations exist only for locally closed terms. -/
lemma lc : Γ ⊢ t ∶ τ → t.LC := by
  intros h
  induction h <;> constructor
  case abs ih => exact ih
  all_goals aesop

variable [HasFresh Var]

open Term

/-- Substitution for a context weakened by a single type between appended contexts. -/
lemma subst_strengthened :
    (Δ ++ (x, σ) :: Γ) ⊢ t ∶ τ →
    Γ ⊢ s ∶ σ → 
    (Δ ++ Γ) ⊢ (t [x := s]) ∶ τ := by
  generalize  eq : Δ ++ (x, σ) :: Γ = Φ
  intros h
  revert Γ Δ
  induction h <;> intros Γ Δ eq der
  case app => aesop
  case var x' τ ok mem => 
    simp only [subst_fvar]
    rw [←eq] at mem
    rw [←eq] at ok
    cases (Ctx.perm (by aesop) ok : @Ctx.Ok Var Ty _ ((x, σ) :: Δ ++ Γ))
    case cons ok_weak _ =>
    observe perm : (Γ ++ Δ).Perm (Δ ++ Γ)
    by_cases h : x = x' <;> simp only [h]
    · rw [show τ = σ by aesop]
      refine Typing.perm perm (weakening der ?_)
      exact Ctx.perm (id (List.Perm.symm perm)) ok_weak
    · aesop
  case abs σ Γ' t T2 xs ih' ih =>
    apply Typing.abs (xs ∪ {x} ∪ (Δ ++ Γ).dom)
    intros x _
    rw [
      subst_def, 
      subst_open_var _ _ _ _ _ der.lc,
      show (x, σ) :: (Δ ++ Γ) = ((x, σ) :: Δ) ++ Γ by aesop
      ]
    apply ih 
    all_goals aesop  

/-- Substitution for a context weakened by a single type. -/
lemma typing_subst : 
    (x, σ) :: Γ ⊢ t ∶ τ  → Γ ⊢ s ∶ σ → Γ ⊢ (t [x := s]) ∶ τ := by
  intros weak der
  rw [←List.nil_append Γ]
  exact subst_strengthened weak der

/-- Typing preservation for opening. -/
@[aesop safe forward (rule_sets := [LambdaCalculus.LocallyNameless.ruleSet])]
theorem preservation_opening {xs : Finset Var} :
  (∀ x ∉ xs, (x, σ) :: Γ ⊢ m ^ fvar x ∶ τ) → 
  Γ ⊢ n ∶ σ → Γ ⊢ m ^ n ∶ τ
  := by
  intros mem der
  have ⟨fresh, free⟩ := fresh_exists (xs ∪ m.fv)
  rw [subst_intro fresh n m (by aesop) der.lc]
  refine typing_subst (mem fresh (by aesop)) der

end STLC.Typing

namespace Term.FullBeta

open STLC Typing

variable [HasFresh Var] {Γ : Ctx Var Ty}

/-- Typing preservation for full beta reduction. -/
@[aesop safe forward (rule_sets := [LambdaCalculus.LocallyNameless.ruleSet])]
theorem preservation : Γ ⊢ t ∶ τ → (t ⭢βᶠt') → Γ ⊢ t' ∶ τ := by
  intros der
  revert t'
  induction der <;> intros t' step <;> cases step
  case' abs.abs xs _ _ _ xs' _=> apply Typing.abs (xs ∪ xs')
  case' app.beta der_l _ _ => cases der_l
  all_goals aesop

/-- Typing preservation for multiple steps of full beta reduction. -/
theorem preservation_redex : Γ ⊢ t ∶ τ → (t ↠βᶠ t') → Γ ⊢ t' ∶ τ := by
  intros der redex
  induction redex using Relation.ReflTransGen.trans_induction_on <;> aesop

/-- Typing preservation for full beta confluence. -/
theorem preservation_confluence :
    Γ ⊢ a ∶ τ → (a ↠βᶠ b) → (a ↠βᶠ c) → 
    ∃ d, (b ↠βᶠ d) ∧ (c ↠βᶠ d) ∧ Γ ⊢ d ∶ τ := by
  intros der ab ac
  have ⟨d, bd, cd⟩ := confluence_beta ab ac
  refine ⟨d, bd, cd, preservation_redex der ?_⟩
  trans
  exact ab
  exact bd

omit [HasFresh Var] in
/-- A typed term either full beta reduces or is a value. -/
theorem progress : ([] : Ctx Var Ty) ⊢ t ∶ τ → t.Value ∨ ∃ t', t ⭢βᶠ t' := by
  intros der
  generalize eq : [] = Γ at der
  induction der
  case var => aesop
  case abs xs mem ih =>
    left
    constructor
    apply Term.LC.abs xs
    intros _ mem'
    exact (mem _ mem').lc
  case app Γ M σ τ N der_l der_r ih_l ih_r => 
    simp only [eq, forall_const] at *
    right
    cases ih_l
    -- if the lhs is a value, beta reduce the application
    next val =>
      cases val
      next M M_abs_lc => exact ⟨M ^ N, FullBeta.beta M_abs_lc der_r.lc⟩
    -- otherwise, propogate the step to the lhs of the application
    next step =>
      obtain ⟨M', stepM⟩ := step
      exact ⟨M'.app N, FullBeta.appR der_r.lc stepM⟩ 

end Term.FullBeta
