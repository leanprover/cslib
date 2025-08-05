/-
Copyright (c) 2025 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

import Cslib.Computability.LambdaCalculus.LocallyNameless.Stlc.Context
import Cslib.Computability.LambdaCalculus.LocallyNameless.Untyped.Properties

/-! # λ-calculus

The simply typed λ-calculus, with a locally nameless representation of syntax.

## References

* [A. Chargueraud, *The Locally Nameless Representation*][Chargueraud2012]
* See also <https://www.cis.upenn.edu/~plclub/popl08-tutorial/code/>, from which
  this is partially adapted

-/

universe u v

variable {Var : Type u} {Base : Type v} [DecidableEq Var]

namespace LambdaCalculus.LocallyNameless.Stlc

/-- Types of the simply typed lambda calculus. -/
inductive Ty (Base : Type v)
  /-- A base type, from a typing context. -/
  | base : Base → Ty Base
  /-- A function type. -/
  | arrow : Ty Base → Ty Base → Ty Base

scoped infixr:70 " ⤳ " => Ty.arrow

open Term Ty

/-- An extrinsic typing derivation for locally nameless terms. -/
@[aesop unsafe [constructors (rule_sets := [LambdaCalculus.LocallyNameless.ruleSet])]]
inductive Typing : Context Var (Ty Base) → Term Var → Ty Base → Prop
  /-- Free variables, from a context judgement. -/
  | var : Γ✓ → ⟨x,σ⟩ ∈ Γ → Typing Γ (fvar x) σ
  /-- Lambda abstraction. -/
  | abs (L : Finset Var) : (∀ x ∉ L, Typing (⟨x,σ⟩ :: Γ) (t ^ fvar x) τ) → Typing Γ t.abs (σ ⤳ τ) 
  /-- Function application. -/
  | app : Typing Γ t (σ ⤳ τ) → Typing Γ t' σ → Typing Γ (app t t') τ

scoped notation:50 Γ " ⊢ " t " ∶" τ:arg => Typing Γ t τ

namespace Typing

variable {Γ Δ Θ : Context Var (Ty Base)}

omit [DecidableEq Var] in
/-- Typing is preserved on permuting a context. -/
theorem perm (ht : Γ ⊢ t ∶τ) (hperm : Γ.Perm Δ) : Δ ⊢ t ∶ τ := by 
  revert Δ
  induction ht <;> intros Δ p
  case app => aesop
  case var => 
    have := @p.mem_iff
    aesop
  case abs ih => 
    constructor
    intros x mem
    exact ih x mem (by aesop)

/-- Weakening of a typing derivation with an appended context. -/
lemma weaken_aux : 
    Γ ++ Δ ⊢ t ∶ τ → (Γ ++ Θ ++ Δ)✓ → (Γ ++ Θ ++ Δ) ⊢ t ∶ τ := by
  generalize eq : Γ ++ Δ = Γ_Δ
  intros h
  revert Γ Δ Θ
  induction h <;> intros Γ Δ Θ eq ok_Γ_Θ_Δ
  case var => aesop
  case app => aesop
  case abs σ Γ' τ t xs ext ih =>
    apply Typing.abs (xs ∪ (Γ ++ Θ ++ Δ).dom)
    intros x _
    have h : ⟨x, σ⟩ :: Γ ++ Δ = ⟨x, σ⟩ :: Γ' := by aesop
    refine @ih x (by aesop) _ _ Θ h ?_
    simp only [HasWellFormed.wf]
    aesop

/-- Weakening of a typing derivation by an additional context. -/
lemma weaken : Γ ⊢ t ∶ τ → (Γ ++ Δ)✓ → Γ ++ Δ ⊢ t ∶ τ := by
  intros der ok
  rw [←List.append_nil (Γ ++ Δ)] at *
  exact weaken_aux (by simp_all) ok

omit [DecidableEq Var] in
/-- Typing derivations exist only for locally closed terms. -/
lemma lc : Γ ⊢ t ∶ τ → t.LC := by
  intros h
  induction h <;> constructor
  case abs ih => exact ih
  all_goals aesop

variable [HasFresh Var]

open Term

/-- Substitution for a context weakened by a single type between appended contexts. -/
lemma subst_aux :
    (Δ ++ ⟨x, σ⟩ :: Γ) ⊢ t ∶ τ →
    Γ ⊢ s ∶ σ → 
    (Δ ++ Γ) ⊢ (t [x := s]) ∶ τ := by
  generalize  eq : Δ ++ ⟨x, σ⟩ :: Γ = Θ
  intros h
  revert Γ Δ
  induction h <;> intros Γ Δ eq der
  case app => aesop
  case var x' τ ok mem => 
    simp only [subst_fvar]
    rw [←eq] at mem
    rw [←eq] at ok
    cases (Context.wf_perm (by aesop) ok : (⟨x, σ⟩ :: Δ ++ Γ)✓)
    case cons ok_weak _ =>
    observe perm : (Γ ++ Δ).Perm (Δ ++ Γ)
    by_cases h : x = x' <;> simp only [h]
    case neg => aesop
    case pos nmem =>
      subst h eq
      have nmem_Γ : ∀ γ, ⟨x, γ⟩ ∉ Γ := by
        intros γ _
        exact nmem x (List.mem_keys.mpr ⟨γ, by aesop⟩) rfl
      have nmem_Δ : ∀ γ, ⟨x, γ⟩ ∉ Δ := by
        intros γ _
        exact nmem x (List.mem_keys.mpr ⟨γ, by aesop⟩) rfl
      have eq' : τ = σ := by
        simp only [List.mem_append, List.mem_cons, Sigma.mk.injEq, heq_eq_eq] at mem
        match mem with | _ => aesop
      rw [eq']
      refine (weaken der ?_).perm perm
      exact Context.wf_perm (id (List.Perm.symm perm)) ok_weak
  case abs σ Γ' t T2 xs ih' ih =>
    apply Typing.abs (xs ∪ {x} ∪ (Δ ++ Γ).dom)
    intros x _
    rw [
      subst_def, 
      subst_open_var _ _ _ _ _ der.lc,
      show ⟨x, σ⟩ :: (Δ ++ Γ) = (⟨x, σ⟩ :: Δ) ++ Γ by aesop
      ]
    apply ih 
    all_goals aesop  

/-- Substitution for a context weakened by a single type. -/
lemma typing_subst_head : 
    ⟨x, σ⟩ :: Γ ⊢ t ∶ τ  → Γ ⊢ s ∶ σ → Γ ⊢ (t [x := s]) ∶ τ := by
  intros weak der
  rw [←List.nil_append Γ]
  exact subst_aux weak der

/-- Typing preservation for opening. -/
@[aesop safe forward (rule_sets := [LambdaCalculus.LocallyNameless.ruleSet])]
theorem preservation_open {xs : Finset Var} :
  (∀ x ∉ xs, ⟨x, σ⟩ :: Γ ⊢ m ^ fvar x ∶ τ) → 
  Γ ⊢ n ∶ σ → Γ ⊢ m ^ n ∶ τ
  := by
  intros mem der
  have ⟨fresh, free⟩ := fresh_exists (xs ∪ m.fv)
  rw [subst_intro fresh n m (by aesop) der.lc]
  exact typing_subst_head (mem fresh (by aesop)) der
