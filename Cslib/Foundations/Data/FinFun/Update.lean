/-
Copyright (c) 2026 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi
-/

module

public import Cslib.Foundations.Data.FinFun.Basic
public import Mathlib.Data.Finset.SDiff

@[expose] public section

/-! # Update for finite functions

This module defines the update operation for finite functions, that is, the equivalent of
`Function.update` for `FinFun`.
-/

namespace Cslib.FinFun

/-- `FinFun` equivalent of `Function.update`. -/
def update [Zero β] [DecidableEq α] [∀ b : β, Decidable (b = 0)] (f : α →₀ β) (a : α) (b : β) :
    α →₀ β where
  fn := Function.update f.fn a b
  support := if b = 0 then f.support \ {a} else f.support ∪ {a}
  mem_support_fn := by grind

/-- `FinFun.update` is consistent with `Function.update`. -/
@[simp]
theorem update_coe [Zero β] [DecidableEq α] [∀ b : β, Decidable (b = 0)] (f : α →₀ β) :
    ((f.update a b) : α → β) = Function.update f a b := by
  grind [update]

/-- Conditional characterisation of the functional interface of `FinFun.update`. -/
theorem update_apply [Zero β] [DecidableEq α] [∀ b : β, Decidable (b = 0)] (f : α →₀ β) :
    ((f.update a' b) a) = if a = a' then b else f a := by
  simp only [update_coe, Function.update_apply]

/-- Conditional characterisation of the support of an updated `FinFun`. -/
@[scoped grind =]
theorem update_support [Zero β] [DecidableEq α] [∀ b : β, Decidable (b = 0)] (f : α →₀ β) :
    (f.update a b).support = if b = 0 then f.support \ {a} else f.support ∪ {a} := by
  simp only [update]

/-- Updating a finite function on the same key is the same as doing the last update. -/
@[scoped grind =, simp]
theorem update_idem [Zero β] [DecidableEq α] [∀ b : β, Decidable (b = 0)] (f : α →₀ β) :
    (f.update a b).update a b' = f.update a b' := by grind

/-- Updates on different keys commute. -/
@[scoped grind =]
theorem update_comm [Zero β] [DecidableEq α] [∀ b : β, Decidable (b = 0)] (f : α →₀ β)
    (h : a ≠ a') : (f.update a b).update a' b' = (f.update a' b').update a b := by grind

/-- Updates that do not change mappings are redundant. -/
@[scoped grind =]
theorem update_self [Zero β] [DecidableEq α] [∀ b : β, Decidable (b = 0)] (f : α →₀ β) :
    (f.update a (f a)) = f := by grind

/-- Updating a function never grows its support more than adding the key. -/
@[scoped grind .]
theorem update_support_subseteq [Zero β] [DecidableEq α] [∀ b : β, Decidable (b = 0)] (f : α →₀ β) :
    (f.update a b).support ⊆ f.support ∪ {a} := by grind

/-- Updating a function with a nonempty element yields the same support with, possibly, the addition
of the key. -/
@[scoped grind .]
theorem update_neq_zero_support_eq_union [Zero β] [DecidableEq α] [∀ b : β, Decidable (b = 0)]
    (f : α →₀ β) (h : b ≠ 0) :
    (f.update a b).support = f.support ∪ {a} := by grind

/-- Updating a key in the support with a nonempty element preserves the support. -/
theorem update_neq_zero_support_eq [Zero β] [DecidableEq α] [∀ b : β, Decidable (b = 0)]
    (f : α →₀ β) (h₁ : f a ≠ 0) (h₂ : b ≠ 0) : (f.update a b).support = f.support := by grind

end Cslib.FinFun
