/-
Copyright (c) 2025 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

import Cslib.Computability.LambdaCalculus.Untyped.LocallyNameless.Basic
import Cslib.Computability.LambdaCalculus.Untyped.LocallyNameless.Properties
import Cslib.Computability.LambdaCalculus.Untyped.LocallyNameless.FullBetaConfluence

/-! # λ-calculus

The simply typed λ-calculus, with a locally nameless representation of syntax.

## References

* [A. Chargueraud, *The Locally Nameless Representation*] [Chargueraud2012]
* See also https://www.cis.upenn.edu/~plclub/popl08-tutorial/code/, from which
  this is partially adapted

-/

universe u

variable {Var : Type u} [DecidableEq Var]

namespace LambdaCalculus.LocallyNameless

/-- Types of the simply typed lambda calculus. -/
inductive Ty
/-- A base type, from a typing context. -/
| base : Ty
/-- A function type. -/
| arrow : Ty → Ty → Ty

scoped infixr:70 " ⤳ " => Ty.arrow
scoped prefix:90 "~ " => Ty.base

/-- A typing context is a list of free variables and corresponding types. -/
abbrev Ctx (Var : Type u) := List (Var × Ty)

/-- The domain of a context is the finite set of free variables it uses. -/
@[simp]
def Ctx.dom : Ctx Var → Finset Var := λ Γ ↦ Γ.map Prod.fst |>.toFinset

/-- A well-formed context. -/
inductive Ok : Ctx Var → Prop
| nil : Ok []
| cons : Ok Γ → x ∉ Γ.dom → Ok ((x,σ) :: Γ)

/-- Context membership is preserved on permuting a context. -/
theorem Ctx.dom_perm_mem_iff {Γ Δ : Ctx Var} (h : Γ.Perm Δ) {x : Var} : 
    x ∈ Γ.dom ↔ x ∈ Δ.dom := by
  induction h <;> aesop

theorem Ctx.dom_perm_nmem {Γ Δ : Ctx Var} (h : Γ.Perm Δ) {x : Var} : 
    x ∉ Γ.dom → x ∉ Δ.dom := by
  intros Γ_nmem Δ_mem
  apply Γ_nmem
  exact (dom_perm_mem_iff h).mpr Δ_mem

/-- Context well-formedness is preserved on permuting a context. -/
@[aesop safe forward (rule_sets := [LambdaCalculus.LocallyNameless.ruleSet])]
theorem Ok.perm {Γ Δ : Ctx Var} (h : Γ.Perm Δ) : Ok Γ → Ok Δ := by
  induction h <;> intro Γ_ok
  case cons perm ih =>
    cases Γ_ok
    case cons ok_Γ mem => exact Ok.cons (ih ok_Γ) (Ctx.dom_perm_nmem perm mem)
  case nil => constructor
  case trans => simp_all
  case swap =>
    cases Γ_ok
    case cons ok _ =>
    cases ok
    case cons ok _ =>
      constructor
      constructor
      all_goals aesop

open Term Ty

/-- An extrinsic typing derivation for locally nameless terms. -/
@[aesop unsafe [constructors (rule_sets := [LambdaCalculus.LocallyNameless.ruleSet])]]
inductive Typing : Ctx Var → Term Var → Ty → Prop
| var : Ok Γ → (x,σ) ∈ Γ → Typing Γ (fvar x) σ
| abs (L : Finset Var) : (∀ x ∉ L, Typing ((x,σ) :: Γ) (t ^ fvar x) τ) → Typing Γ t.abs (σ ⤳ τ) 
| app : Typing Γ t (σ ⤳ τ) → Typing Γ t' σ → Typing Γ (app t t') τ

scoped notation:50 Γ " ⊢ " t " ∶" τ:arg => Typing Γ t τ

variable {Γ Δ Φ : Ctx Var}

/-- Typing is preserved on permuting a context. -/
theorem Typing.perm : Γ.Perm Δ → Γ ⊢ t ∶ τ → Δ ⊢ t ∶ τ := by 
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

open List Finset in
private lemma weakening_strengthened_eq (eq : Γ_Δ  = Γ ++ Δ) : 
    Γ_Δ  ⊢ t ∶ τ → Ok (Γ ++ Φ ++ Δ) → (Γ ++ Φ ++ Δ) ⊢ t ∶ τ := by
  intros h
  revert Γ Δ Φ
  induction h <;> intros Γ Δ Φ eq ok_Γ_Φ_Δ
  case var => aesop
  case app => aesop
  case abs σ Γ' τ t xs ext ih =>
    apply Typing.abs (xs ∪ (Γ ++ Φ ++ Δ).dom)
    intros x _
    have h : (x, σ) :: Γ' = (x, σ) :: Γ ++ Δ := by aesop
    refine @ih x (by aesop) _ _ Φ h ?_
    constructor <;> aesop

/-- Weakening of a typing derivation with an appended context. -/
lemma weakening_strengthened : 
    Γ ++ Δ ⊢ t ∶ τ → Ok (Γ ++ Φ ++ Δ) → (Γ ++ Φ ++ Δ) ⊢ t ∶ τ :=
  weakening_strengthened_eq rfl

/-- Weakening of a typing derivation by an additional context. -/
lemma weakening : Γ ⊢ t ∶ T → Ok (Γ ++ Δ) → Γ ++ Δ ⊢ t ∶ T := by
  intros der ok
  rw [←List.append_nil (Γ ++ Δ)] at *
  exact weakening_strengthened (by simp_all) ok

/-- Typing derivations exist only for locally closed terms. -/
lemma typing_lc : Γ ⊢ t ∶ τ → t.LC := by
  intros h
  induction h <;> constructor
  case abs ih => exact ih
  all_goals aesop

variable [HasFresh Var]

private lemma typing_subst_strengthened_eq (eq : Φ = Δ ++ (x, σ) :: Γ) :
    Φ ⊢ t ∶ τ →
    Γ ⊢ s ∶ σ → 
    (Δ ++ Γ) ⊢ (t [x := s]) ∶ τ := by
  intros h
  revert Γ Δ
  induction h <;> intros Γ Δ eq der
  case app => aesop
  case var x' τ ok mem => 
    simp only [subst_fvar]
    rw [eq] at mem
    rw [eq] at ok
    cases (Ok.perm (by aesop) ok : Ok ((x, σ) :: Δ ++ Γ))
    case cons ok_weak _ =>
    observe perm : (Γ ++ Δ).Perm (Δ ++ Γ)
    by_cases h : x = x' <;> simp only [h]
    · rw [show τ = σ by aesop]
      refine Typing.perm perm (weakening der ?_)
      exact Ok.perm (id (List.Perm.symm perm)) ok_weak
    · aesop
  case abs σ Γ' t T2 xs ih' ih =>
    apply Typing.abs (xs ∪ {x} ∪ (Δ ++ Γ).dom)
    intros x _
    rw [
      subst_def, 
      subst_open_var _ _ _ _ _ (typing_lc der),
      show (x, σ) :: (Δ ++ Γ) = ((x, σ) :: Δ) ++ Γ by aesop
      ]
    apply ih 
    all_goals aesop  

/-- Substitution for a context weakened by a single type between appended contexts. -/
lemma typing_subst_strengthened :
  (Δ ++ (z, S) :: Γ) ⊢ t ∶ T →
  Γ ⊢ s ∶ S → 
  (Δ ++ Γ) ⊢ (t [z := s]) ∶ T
  := typing_subst_strengthened_eq rfl

/-- Substitution for a context weakened by a single type. -/
lemma typing_subst : 
    (x, σ) :: Γ ⊢ t ∶ τ  → Γ ⊢ s ∶ σ → Γ ⊢ (t [x := s]) ∶ τ := by
  intros weak der
  rw [←List.nil_append Γ]
  exact typing_subst_strengthened weak der

/-- Typing preservation for opening. -/
@[aesop safe forward (rule_sets := [LambdaCalculus.LocallyNameless.ruleSet])]
theorem preservation_opening {xs : Finset Var} :
  (∀ x ∉ xs, (x, σ) :: Γ ⊢ m ^ fvar x ∶ τ) → 
  Γ ⊢ n ∶ σ → Γ ⊢ m ^ n ∶ τ
  := by
  intros mem der
  have ⟨fresh, free⟩ := fresh_exists (xs ∪ m.fv)
  rw [subst_intro fresh n m (by aesop) (typing_lc der)]
  refine typing_subst (mem fresh (by aesop)) der

/-- Typing preservation. -/
@[aesop safe forward (rule_sets := [LambdaCalculus.LocallyNameless.ruleSet])]
theorem preservation : Γ ⊢ t ∶ τ → (t ⭢βᶠt') → Γ ⊢ t' ∶ τ := by
  intros der
  revert t'
  induction der <;> intros t' step <;> cases step
  case' abs.abs xs _ _ _ xs' _=> apply Typing.abs (xs ∪ xs')
  case' app.beta der_l _ _ => cases der_l
  all_goals aesop

/-- Typing preservation for multiple steps of reduction. -/
theorem preservation_redex : Γ ⊢ t ∶ T → (t ↠βᶠ t') → Γ ⊢ t' ∶ T := by
  intros der redex
  induction redex using Relation.ReflTransGen.trans_induction_on <;> aesop

/-- Typing preservation for confluence. -/
theorem preservation_confluence :
    Γ ⊢ a ∶ τ → (a ↠βᶠ b) → (a ↠βᶠ c) → 
    ∃ d, (b ↠βᶠ d) ∧ (c ↠βᶠ d) ∧ Γ ⊢ d ∶ τ := by
  intros der ab ac
  have ⟨d, bd, cd⟩ := confluence_beta ab ac
  refine ⟨d, bd, cd, preservation_redex der ?_⟩
  trans
  exact ab
  exact bd
