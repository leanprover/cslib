/-
Copyright (c) 2025 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

import Cslib.Computability.LambdaCalculus.LocallyNameless.Untyped.AesopRuleset
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Dedup

/-! # λ-calculus

Contexts as pairs of free variables and types.

-/

universe u v

variable {Var : Type u} {Ty : Type v} [DecidableEq Var]

namespace LambdaCalculus.LocallyNameless.STLC

/-- A typing context is a list of free variables and corresponding types. -/
abbrev Ctx (Var : Type u) (Ty : Type v) := List (Var × Ty)

namespace Ctx

/-- The domain of a context is the finite set of free variables it uses. -/
@[simp]
def dom : Ctx Var Ty → Finset Var := λ Γ ↦ Γ.map Prod.fst |>.toFinset

/-- A well-formed context. -/
inductive Ok : Ctx Var Ty → Prop
| nil : Ok []
| cons : Ok Γ → x ∉ Γ.dom → Ok ((x,σ) :: Γ)

variable {Γ Δ : Ctx Var Ty}

/-- Context membership is preserved on permuting a context. -/
theorem dom_perm_mem_iff (h : Γ.Perm Δ) {x : Var} : 
    x ∈ Γ.dom ↔ x ∈ Δ.dom := by
  induction h <;> aesop

/-- Context well-formedness is preserved on permuting a context. -/
@[aesop safe forward (rule_sets := [LambdaCalculus.LocallyNameless.ruleSet])]
theorem perm (h : Γ.Perm Δ) : Ok Γ → Ok Δ := by
  induction h <;> intro Γ_ok
  case cons perm ih =>
    cases Γ_ok
    case cons ok_Γ nmem => exact Ok.cons (ih ok_Γ) $ (dom_perm_mem_iff perm).not.mp nmem
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
