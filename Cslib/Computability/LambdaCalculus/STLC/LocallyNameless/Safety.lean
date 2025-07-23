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

Type safety of the simply typed λ-calculus, with a locally nameless representation of syntax.
Theorems in this file are namespaced by their respective reductions.

## References

* [A. Chargueraud, *The Locally Nameless Representation*] [Chargueraud2012]
* See also https://www.cis.upenn.edu/~plclub/popl08-tutorial/code/, from which
  this is partially adapted

-/

universe u

namespace LambdaCalculus.LocallyNameless

open STLC Typing

variable {Var : Type u} [DecidableEq Var] {R : Term Var → Term Var → Prop}

def preserves (R : Term Var → Term Var → Prop) := ∀ {Γ t t' τ}, Γ ⊢ t ∶ τ → R t t' → Γ ⊢ t' ∶ τ

/-- If a reduction preserves types, so does its reflexive transitive closure. -/
@[aesop safe forward (rule_sets := [LambdaCalculus.LocallyNameless.ruleSet])]
theorem preservation_redex : preserves R → preserves (Relation.ReflTransGen R) := by
  intros _ _ _ _ _ _ redex
  induction redex <;> aesop

open Relation in
/-- Confluence preserves type preservation. -/
theorem preservation_confluence : 
    Confluence R → preserves R → Γ ⊢ a ∶ τ → 
    (ReflTransGen R) a b → (ReflTransGen R) a c →
    ∃ d, (ReflTransGen R) b d ∧ (ReflTransGen R) c d ∧ Γ ⊢ d ∶ τ := by
  intros con p der ab ac
  have ⟨d, bd, cd⟩ := con ab ac
  exact ⟨d, bd, cd, preservation_redex p der (ab.trans bd)⟩
 
variable [HasFresh Var] {Γ : Ctx Var Ty}

namespace Term.FullBeta

/-- Typing preservation for full beta reduction. -/
@[aesop safe forward (rule_sets := [LambdaCalculus.LocallyNameless.ruleSet])]
theorem preservation : Γ ⊢ t ∶ τ → (t ⭢βᶠt') → Γ ⊢ t' ∶ τ := by
  intros der
  revert t'
  induction der <;> intros t' step <;> cases step
  case' abs.abs xs _ _ _ xs' _=> apply Typing.abs (xs ∪ xs')
  case' app.beta der_l _ _ => cases der_l
  all_goals aesop

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
