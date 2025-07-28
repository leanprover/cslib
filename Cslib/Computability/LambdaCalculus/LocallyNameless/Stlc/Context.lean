/-
Copyright (c) 2025 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

import Cslib.Computability.LambdaCalculus.LocallyNameless.Untyped.AesopRuleset
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Dedup
import Mathlib.Data.List.Sigma

/-! # λ-calculus

Contexts as pairs of free variables and types.

-/

universe u v

variable {Var : Type u} {Ty : Type v} [DecidableEq Var]

namespace LambdaCalculus.LocallyNameless.Stlc

/-- A typing context is a list of free variables and corresponding types. -/
abbrev Ctx (Var : Type u) (Ty : Type v) := List ((_ : Var) × Ty)

namespace Ctx

/-- The domain of a context is the finite set of free variables it uses. -/
@[simp]
def dom : Ctx Var Ty → Finset Var := List.toFinset ∘ List.keys

/-- A well-formed context. -/
abbrev Ok : Ctx Var Ty → Prop := List.NodupKeys

variable {Γ Δ : Ctx Var Ty}

/-- Context membership is preserved on permuting a context. -/
theorem dom_perm_mem_iff (h : Γ.Perm Δ) {x : Var} : 
    x ∈ Γ.dom ↔ x ∈ Δ.dom := by
  induction h <;> aesop

omit [DecidableEq Var] in
/-- Context well-formedness is preserved on permuting a context. -/
@[aesop safe forward (rule_sets := [LambdaCalculus.LocallyNameless.ruleSet])]
theorem perm (h : Γ.Perm Δ) : Ok Γ → Ok Δ := (List.perm_nodupKeys h).mp

omit [DecidableEq Var] in
@[aesop safe forward (rule_sets := [LambdaCalculus.LocallyNameless.ruleSet])]
theorem strengthen : (Δ ++ ⟨x, σ⟩ :: Γ).Ok → (Δ ++ Γ).Ok := by
  intros ok
  have sl : List.Sublist (Δ ++ Γ) (Δ ++ ⟨x, σ⟩ :: Γ) := by simp
  exact List.NodupKeys.sublist sl ok
