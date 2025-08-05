/-
Copyright (c) 2025 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

import Cslib.Computability.LambdaCalculus.LocallyNameless.Untyped.AesopRuleset
import Cslib.Syntax.HasWellFormed
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
abbrev Context (Var : Type u) (Ty : Type v) := List ((_ : Var) × Ty)

namespace Context

/-- The domain of a context is the finite set of free variables it uses. -/
@[simp]
def dom : Context Var Ty → Finset Var := List.toFinset ∘ List.keys

/-- A well-formed context. -/
abbrev Ok : Context Var Ty → Prop := List.NodupKeys

instance : HasWellFormed (Context Var Ty) :=
  ⟨Ok⟩

variable {Γ Δ : Context Var Ty}

/-- Context membership is preserved on permuting a context. -/
theorem dom_perm_mem_iff (h : Γ.Perm Δ) {x : Var} : 
    x ∈ Γ.dom ↔ x ∈ Δ.dom := by
  induction h <;> aesop

omit [DecidableEq Var] in
/-- Context well-formedness is preserved on permuting a context. -/
@[aesop safe forward (rule_sets := [LambdaCalculus.LocallyNameless.ruleSet])]
theorem wf_perm (h : Γ.Perm Δ) : Γ✓ → Δ✓ := (List.perm_nodupKeys h).mp

omit [DecidableEq Var] in
@[aesop safe forward (rule_sets := [LambdaCalculus.LocallyNameless.ruleSet])]
theorem wf_strengthen : (Δ ++ ⟨x, σ⟩ :: Γ)✓ → (Δ ++ Γ)✓ := by
  intros ok
  have sl : List.Sublist (Δ ++ Γ) (Δ ++ ⟨x, σ⟩ :: Γ) := by simp
  exact List.NodupKeys.sublist sl ok
