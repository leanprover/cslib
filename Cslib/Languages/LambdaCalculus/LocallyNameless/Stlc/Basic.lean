/-
Copyright (c) 2025 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

import Cslib.Languages.LambdaCalculus.LocallyNameless.Context
import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.Properties

/-! # λ-calculus

The simply typed λ-calculus, with a locally nameless representation of syntax.

## References

* [A. Chargueraud, *The Locally Nameless Representation*][Chargueraud2012]
* See also <https://www.cis.upenn.edu/~plclub/popl08-tutorial/code/>, from which
  this is partially adapted

-/

namespace Cslib

universe u v

variable {Var : Type u} {Base : Type v} [DecidableEq Var]

open LambdaCalculus.LocallyNameless.Untyped Term

namespace LambdaCalculus.LocallyNameless.Stlc

/-- Types of the simply typed lambda calculus. -/
inductive Ty (Base : Type v)
  /-- A base type, from a typing context. -/
  | base : Base → Ty Base
  /-- A function type. -/
  | arrow : Ty Base → Ty Base → Ty Base

@[inherit_doc]
scoped infixr:70 " ⤳ " => Ty.arrow

open Ty Context

/-- An extrinsic typing derivation for locally nameless terms. -/
inductive Typing : Context Var (Ty Base) → Term Var → Ty Base → Prop
  /-- Free variables, from a context judgement. -/
  | var : Γ✓ → ⟨x,σ⟩ ∈ Γ → Typing Γ (fvar x) σ
  /-- Lambda abstraction. -/
  | abs (L : Finset Var) : (∀ x ∉ L, Typing (⟨x,σ⟩ :: Γ) (t ^ fvar x) τ) → Typing Γ t.abs (σ ⤳ τ)
  /-- Function application. -/
  | app : Typing Γ t (σ ⤳ τ) → Typing Γ t' σ → Typing Γ (app t t') τ

attribute [scoped grind .] Typing.var Typing.app

@[inherit_doc]
scoped notation:50 Γ " ⊢ " t " ∶ " τ:arg => Typing Γ t τ

namespace Typing

variable {Γ Δ Θ : Context Var (Ty Base)}

omit [DecidableEq Var] in
/-- Typing is preserved on permuting a context. -/
theorem perm (ht : Γ ⊢ t ∶ τ) (hperm : Γ.Perm Δ) : Δ ⊢ t ∶ τ := by
  induction ht generalizing Δ
  case abs ih =>
    constructor
    intros x mem
    exact ih x mem (by simp_all)
  all_goals grind

/-- Weakening of a typing derivation with an appended context. -/
lemma weaken_aux (der : Γ ++ Δ ⊢ t ∶ τ) : (Γ ++ Θ ++ Δ)✓ → (Γ ++ Θ ++ Δ) ⊢ t ∶ τ := by
  generalize eq : Γ ++ Δ = Γ_Δ at der
  induction der generalizing Γ Δ Θ <;> intros ok_Γ_Θ_Δ
  case abs σ Γ' τ t xs ext ih =>
    apply Typing.abs (xs ∪ (Γ ++ Θ ++ Δ).dom)
    intros x _
    have h : ⟨x, σ⟩ :: Γ ++ Δ = ⟨x, σ⟩ :: Γ' := by grind
    refine @ih x (by grind) _ _ Θ h ?_
    simp_all [HasWellFormed.wf]
  all_goals grind

/-- Weakening of a typing derivation by an additional context. -/
lemma weaken (der : Γ ⊢ t ∶ τ) (ok : (Γ ++ Δ)✓) : Γ ++ Δ ⊢ t ∶ τ := by
  rw [←List.append_nil (Γ ++ Δ)] at *
  exact weaken_aux (by simp_all) ok

omit [DecidableEq Var] in
/-- Typing derivations exist only for locally closed terms. -/
lemma lc (der : Γ ⊢ t ∶ τ) : t.LC := by
  induction der <;> constructor
  case abs ih => exact ih
  all_goals grind

variable [HasFresh Var]

open Term

/-- Substitution for a context weakened by a single type between appended contexts. -/
lemma subst_aux (h : Δ ++ ⟨x, σ⟩ :: Γ ⊢ t ∶ τ) (der : Γ ⊢ s ∶ σ) :
    Δ ++ Γ ⊢ t[x := s] ∶ τ := by
  generalize eq : Δ ++ ⟨x, σ⟩ :: Γ = Θ at h
  induction h generalizing Γ Δ der
  case app => grind
  case var x' τ ok mem =>
    simp only [subst_fvar]
    subst eq
    cases ((List.perm_nodupKeys (by simp)).mp ok : (⟨x, σ⟩ :: Δ ++ Γ)✓)
    case cons ok_weak _ =>
    observe perm : (Γ ++ Δ).Perm (Δ ++ Γ)
    by_cases h : x = x' <;> simp only [h]
    case neg => grind
    case pos nmem =>
      subst h
      have nmem_Γ : ∀ γ, ⟨x, γ⟩ ∉ Γ := by
        intros γ _
        exact nmem x (List.mem_keys.mpr ⟨γ, by simp_all⟩) rfl
      have nmem_Δ : ∀ γ, ⟨x, γ⟩ ∉ Δ := by
        intros γ _
        exact nmem x (List.mem_keys.mpr ⟨γ, by simp_all⟩) rfl
      have eq' : τ = σ := by
        simp only [List.mem_append, List.mem_cons, Sigma.mk.injEq, heq_eq_eq] at mem
        match mem with | _ => simp_all
      rw [eq']
      refine (weaken der ?_).perm perm
      grind
  case abs σ Γ' t T2 xs ih' ih =>
    apply Typing.abs (free_union Var)
    intros
    rw [subst_def, ←subst_open_var _ _ _ _ ?_ der.lc] <;> grind

/-- Substitution for a context weakened by a single type. -/
lemma typing_subst_head (weak : ⟨x, σ⟩ :: Γ ⊢ t ∶ τ) (der : Γ ⊢ s ∶ σ) :
    Γ ⊢ (t [x := s]) ∶ τ := by
  rw [←List.nil_append Γ]
  exact subst_aux weak der

/-- Typing preservation for opening. -/
theorem preservation_open {xs : Finset Var}
  (cofin : ∀ x ∉ xs, ⟨x, σ⟩ :: Γ ⊢ m ^ fvar x ∶ τ) (der : Γ ⊢ n ∶ σ) :
    Γ ⊢ m ^ n ∶ τ := by
  have ⟨fresh, _⟩ := fresh_exists <| free_union [Term.fv] Var
  rw [subst_intro fresh n m (by grind) der.lc]
  exact typing_subst_head (by grind) der

end LambdaCalculus.LocallyNameless.Stlc.Typing

end Cslib
