/-
Copyright (c) 2025 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Languages.LambdaCalculus.LocallyNameless.Context
public import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.Properties

@[expose] public section

set_option linter.unusedDecidableInType false

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
  induction der generalizing Γ Δ Θ with
  | abs xs => grind [Typing.abs (xs ∪ (Γ ++ Θ ++ Δ).dom), List.nodupKeys_cons]
  | _ => grind

/-- Weakening of a typing derivation by an additional context. -/
lemma weaken (der : Γ ⊢ t ∶ τ) (ok : (Γ ++ Δ)✓) : Γ ++ Δ ⊢ t ∶ τ := by
  grind [List.append_nil (Γ ++ Δ), weaken_aux]

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
  case var x' _ ok _ =>
    subst eq
    cases ((List.perm_nodupKeys (by simp)).mp ok : (⟨x, σ⟩ :: Δ ++ Γ)✓)
    case cons =>
    observe perm : (Γ ++ Δ).Perm (Δ ++ Γ)
    by_cases h : x = x'
    case neg => grind
    case pos => grind [(weaken der ?_).perm perm]
  case abs =>
    grind [Typing.abs <| free_union Var, subst_open_var _ _ _ _ ?_ der.lc]

/-- Substitution for a context weakened by a single type. -/
lemma typing_subst_head (weak : ⟨x, σ⟩ :: Γ ⊢ t ∶ τ) (der : Γ ⊢ s ∶ σ) :
    Γ ⊢ (t [x := s]) ∶ τ := by
  grind [subst_aux]

/-- Typing preservation for opening. -/
theorem preservation_open {xs : Finset Var}
  (cofin : ∀ x ∉ xs, ⟨x, σ⟩ :: Γ ⊢ m ^ fvar x ∶ τ) (der : Γ ⊢ n ∶ σ) :
    Γ ⊢ m ^ n ∶ τ := by
  have ⟨fresh, _⟩ := fresh_exists <| free_union [Term.fv] Var
  grind [subst_intro fresh _ _ ?_ der.lc, typing_subst_head]

end LambdaCalculus.LocallyNameless.Stlc.Typing

end Cslib
