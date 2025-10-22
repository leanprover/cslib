/-
Copyright (c) 2025 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi, Xueying Qin
-/

import Mathlib.Data.Finset.Basic

/-! # Finite functions

Given types `α` and `β`, and assuming that `β` has a `Zero` element,
a `FinFun α β` is a function from `α` to `β` where only a finite number of elements
in `α` are mapped to non-zero elements.
-/

namespace Cslib

/-- A `FinFun` is a function `fn` with a finite `support`.

This is similar to `Finsupp` in Mathlib, but definitions are computable. -/
structure FinFun (α : Type _) (β : Type _) [Zero β] where
  fn : α → β
  support : Finset α
  mem_support_fn {a : α} : a ∈ support ↔ fn a ≠ 0

attribute [grind _=_] FinFun.mem_support_fn

namespace FinFun

scoped notation:50 α " →₀ " β => FinFun α β

/-- Constructs a `FinFun` from any function and a given support, filtering out all elements not
mapped to 0 in the support. -/
def mkRestrictFn {α β : Type _} [Zero β] [DecidableEq α] [hdec : ∀ y : β, Decidable (y = 0)]
  (fn : α → β) (support : Finset α) : α →₀ β where
  fn := (fun a => if a ∈ support then fn a else 0)
  support := support.filter (fn · ≠ 0)
  mem_support_fn := by grind

scoped notation:50 f "↾" support => FinFun.mkRestrictFn f support

instance instFunLike [Zero β] : FunLike (α →₀ β) α β where
  coe f := f.fn
  coe_injective' := by
    rintro ⟨f1, support1, mem_support_fn1⟩ ⟨f2, support2, mem_support_fn2⟩
    simp only
    intro heq
    simp only [heq, mk.injEq, true_and]
    ext a
    grind

@[grind =]
theorem coe_fn [Zero β] {f : α →₀ β} : (f : α → β) = f.fn := by simp [DFunLike.coe]

@[grind =]
theorem coe_eq_fn [Zero β] {f : α →₀ β} : f a = f.fn a := by
  rcases f with ⟨f, support, mem_support_fn⟩
  simp [DFunLike.coe]

/-- Extensional equality for `FinFun`. -/
@[grind ←=]
theorem ext [Zero β] {f g : α →₀ β} (h : ∀ (a : α), f a = g a) :
  f = g := by
  apply DFunLike.ext
  exact h

@[grind _=_]
theorem mem_support_not_zero [Zero β] {f : α →₀ β} : a ∈ f.support ↔ f a ≠ 0 := by
  apply Iff.intro <;> intro h
  case mp =>
    simp only [coe_eq_fn]
    rw [← FinFun.mem_support_fn]
    simp only [Membership.mem] at h
    simp only [Membership.mem]
    exact h
  case mpr =>
    have hmem := f.mem_support_fn (a := a)
    simp only [Membership.mem] at hmem
    simp only [Membership.mem]
    grind

@[grind _=_]
theorem not_mem_support_zero [Zero β] {f : α →₀ β} : a ∉ f.support ↔ f a = 0 := by
  grind

/-- Two `FinFun`s are equal if their internal functions and supports are equal. -/
@[grind]
theorem eq_char [DecidableEq α] [Zero β] {f g : α →₀ β} :
  f = g ↔ (f.fn = g.fn ∧ f.support = g.support) := by
  apply Iff.intro <;> intro h
  · grind
  · obtain ⟨h1, h2⟩ := h
    apply DFunLike.ext
    intro x
    rw [coe_fn]
    rw [coe_fn]
    rw [h1]

end FinFun

end Cslib
