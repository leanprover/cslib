/-
Copyright (c) 2025 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Languages.LambdaCalculus.LocallyNameless.Stlc.Basic
public import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.FullBeta

@[expose] public section

/-! # λ-calculus

Type safety of the simply typed λ-calculus, with a locally nameless representation of syntax.
Theorems in this file are namespaced by their respective reductions.

## References

* [A. Chargueraud, *The Locally Nameless Representation*][Chargueraud2012]
* See also <https://www.cis.upenn.edu/~plclub/popl08-tutorial/code/>, from which
  this is partially adapted

-/

namespace Cslib

universe u v

namespace LambdaCalculus.LocallyNameless.Stlc

open Untyped Typing

variable {Var : Type u} {Base : Type v} {R : Term Var → Term Var → Prop}

/-- A relation on terms preserves typing if all related terms have the same type. -/
def PreservesTyping (R : Term Var → Term Var → Prop) (Base : Type v) :=
  ∀ {Γ t t'} {τ : Ty Base}, Γ ⊢ t ∶ τ → R t t' → Γ ⊢ t' ∶ τ

/-- If a reduction preserves types, so does its reflexive transitive closure. -/
@[scoped grind →]
theorem redex_preservesTyping :
    PreservesTyping R Base → PreservesTyping (Relation.ReflTransGen R) Base := by
  intros _ _ _ _ _ _ redex
  induction redex <;> [grind; aesop]


open _root_.Relation in
/-- Confluence preserves type preservation. -/
theorem confluence_preservesTyping {τ : Ty Base}
    (con : Confluent R) (p : PreservesTyping R Base) (der : Γ ⊢ a ∶ τ)
    (ab : ReflTransGen R a b) (ac : ReflTransGen R a c) :
    ∃ d, ReflTransGen R b d ∧ ReflTransGen R c d ∧ Γ ⊢ d ∶ τ := by
  have ⟨d, bd, cd⟩ := con ab ac
  exact ⟨d, bd, cd, redex_preservesTyping p der (ab.trans bd)⟩

variable [HasFresh Var] [DecidableEq Var] {Γ : Context Var (Ty Base)}

namespace FullBeta

open LambdaCalculus.LocallyNameless.Untyped.Term FullBeta

set_option linter.unusedDecidableInType false in
/-- Typing preservation for full beta reduction. -/
@[scoped grind →]
theorem preservation (der : Γ ⊢ t ∶ τ) (step : t ⭢βᶠ t') : Γ ⊢ t' ∶ τ := by
  induction der generalizing t' <;> cases step
  case abs.abs xs _ _ _ xs' _ => apply Typing.abs (free_union Var); grind
  case app.beta der _ _ _ der_l _ _ =>
    -- TODO: this is a regression from aesop, where `preservation_open` was a forward rule
    cases der_l with | abs _ cofin => simp [preservation_open cofin der]
  all_goals grind

open scoped Term in
omit [HasFresh Var] [DecidableEq Var] in
/-- A typed term either full beta reduces or is a value. -/
theorem progress {t : Term Var} {τ : Ty Base} (ht : [] ⊢ t ∶ τ) : t.Value ∨ ∃ t', t ⭢βᶠ t' := by
  generalize eq : [] = Γ at ht
  induction ht
  case var => simp_all
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
      next M M_abs_lc => exact ⟨M ^ N, Term.FullBeta.beta M_abs_lc der_r.lc⟩
    -- otherwise, propogate the step to the lhs of the application
    next step =>
      obtain ⟨M', stepM⟩ := step
      exact ⟨M'.app N, Term.FullBeta.appR der_r.lc stepM⟩

end FullBeta

end LambdaCalculus.LocallyNameless.Stlc

end Cslib
