/-
Copyright (c) 2025 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

import Cslib.Foundations.Data.HasFresh
import Cslib.Languages.LambdaCalculus.LocallyNameless.Context

/-! # λ-calculus

The λ-calculus with polymorphism and subtyping, with a locally nameless representation of syntax.

## References

* [A. Chargueraud, *The Locally Nameless Representation*][Chargueraud2012]
* See also <https://www.cis.upenn.edu/~plclub/popl08-tutorial/code/>, from which
  this is adapted

-/

namespace Cslib

variable {Var : Type*} [HasFresh Var] [DecidableEq Var]

namespace LambdaCalculus.LocallyNameless.Fsub

/-- Types of the polymorphic lambda calculus. -/
inductive Ty (Var : Type*)
  /-- The type ⊤, with a single inhabitant. -/
  | top : Ty Var
  /-- Bound variables that appear in a type, using a de-Bruijn index. -/
  | bvar : ℕ → Ty Var
  /-- Free type variables. -/
  | fvar : Var → Ty Var
  /-- A function type. -/
  | arrow : Ty Var → Ty Var → Ty Var
  /-- A universal quantification. -/
  | all : Ty Var → Ty Var → Ty Var
  /-- A sum type. -/
  | sum : Ty Var → Ty Var → Ty Var
  deriving Inhabited

/-- Syntax of locally nameless lambda terms, with free variables over `Var`. -/
inductive Term (Var : Type*)
  /-- Bound term variables that appear under a lambda abstraction, using a de-Bruijn index. -/
  | bvar : ℕ → Term Var
  /-- Free term variables. -/
  | fvar : Var → Term Var
  /-- Lambda abstraction, introducing a new bound term variable. -/
  | abs : Ty Var → Term Var → Term Var
  /-- Function application. -/
  | app : Term Var → Term Var → Term Var
  /-- Type abstraction, introducing a new bound type variable. -/
  | tabs : Ty Var → Term Var → Term Var
  /-- Type application. -/
  | tapp : Term Var → Ty Var → Term Var
  /-- Binding of a term. -/
  | let' : Term Var → Term Var → Term Var
  /-- Left constructor of a sum. -/
  | inl : Term Var → Term Var
  /-- Right constructor of a sum. -/
  | inr : Term Var → Term Var
  /-- Case matching on a sum. -/
  | case : Term Var → Term Var → Term Var → Term Var

/-- A context binding. -/
inductive Binding (Var : Type*)
  /-- Subtype binding. -/
  | sub : Ty Var → Binding Var
  /-- Type binding. -/
  | ty : Ty Var → Binding Var
  deriving Inhabited

/-- Free variables of a type. -/
@[scoped grind =]
def Ty.fv : Ty Var → Finset Var
| top | bvar _ => {}
| fvar X => {X}
| arrow σ τ | all σ τ | sum σ τ => σ.fv ∪ τ.fv

/-- Free variables of a binding. -/
@[scoped grind =]
def Binding.fv : Binding Var → Finset Var
| sub σ | ty σ => σ.fv

/-- Free type variables of a term. -/
@[scoped grind =]
def Term.fv_ty : Term Var → Finset Var
| bvar _ | fvar _ => {}
| abs σ t₁ | tabs σ t₁ | tapp t₁ σ => σ.fv ∪ t₁.fv_ty
| inl t₁ | inr t₁ => t₁.fv_ty
| app t₁ t₂ | let' t₁ t₂ => t₁.fv_ty ∪ t₂.fv_ty
| case t₁ t₂ t₃ => t₁.fv_ty ∪ t₂.fv_ty ∪ t₃.fv_ty

/-- Free term variables of a term. -/
@[scoped grind =]
def Term.fv_tm : Term Var → Finset Var
| bvar _ => {}
| fvar x => {x}
| abs _ t₁ | tabs _ t₁ | tapp t₁ _ | inl t₁ | inr t₁ => t₁.fv_tm
| app t₁ t₂ | let' t₁ t₂ => t₁.fv_tm ∪ t₂.fv_tm
| case t₁ t₂ t₃ => t₁.fv_tm ∪ t₂.fv_tm ∪ t₃.fv_tm

/-- A context of bindings. -/
abbrev Env (Var : Type*) := Context Var (Binding Var)

end LambdaCalculus.LocallyNameless.Fsub

end Cslib
