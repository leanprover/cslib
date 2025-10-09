/-
Copyright (c) 2025 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi, Xueying Qin
-/

import Mathlib.Data.Finset.Basic

/-! # Finitely-representable functions

Given types `α` and `β`, and assuming that `β` has a `Zero` element,
a `FinFun α β` is a function from `α` to `β` with finite support.
-/

/-- A finite function FinFun is a function `f` with a finite `support`.

This is similar to `Finsupp` in Mathlib, but definitions are computable. -/
structure FinFun (α : Type _) (β : Type _) [Zero β] where
  fn : α → β
  support : Finset α
  support_exact (a : α) : a ∈ support ↔ fn a ≠ 0

namespace FinFun

scoped notation:50 α " →₀ " β => FinFun α β

/-- Constructs a `FinFun` from any function and a given support, filtering out all elements not
mapped to 0 in the support. -/
def mkRestrictFn {α β : Type _} [Zero β] [DecidableEq α] [hdec : ∀ y : β, Decidable (y = 0)]
  (fn : α → β) (support : Finset α) : α →₀ β where
  fn := (fun a => if a ∈ support then fn a else 0)
  support := support.filter (fn · ≠ 0)
  support_exact := by grind

scoped notation:50 f "↾" support => FinFun.mkRestrictFn f support

instance [Zero β] : Membership α (α →₀ β) where
  mem f a := a ∈ f.support

instance instFunLike [Zero β] : FunLike (α →₀ β) α β where
  coe f := f.fn
  coe_injective' := by
    rintro ⟨f1, support1, support_exact1⟩ ⟨f2, support2, support_exact2⟩
    simp only
    intro heq
    simp only [heq, mk.injEq, true_and]
    ext a
    grind

@[grind =]
theorem coe_fn [Zero β] {f : α →₀ β} : (f : α → β) = f.fn := by simp [DFunLike.coe]

@[grind =]
theorem coe_eq_fn [Zero β] {f : α →₀ β} : f a = f.fn a := by
  rcases f with ⟨f, support, support_exact⟩
  simp [DFunLike.coe]

/-- Extensional equality for `FinFun`. -/
@[grind ←=]
theorem ext [Zero β] {f g : α →₀ β} (h : ∀ (a : α), f a = g a) :
  f = g := by
  apply DFunLike.ext
  exact h



/-
def mapBin [Zero β] [DecidableEq α] (f g : α →₀ β) (op : Option β → Option β → Option β) :
    Option (α →₀ β) :=
  if h : f.support = g.support ∧ ∀ a ∈ f.support, (op (some (f.fn a)) (some (g.fn a))).isSome then
    some {
      fn := fun a =>
        match op (some (f.fn a)) (some (g.fn a)) with
          | some y => y
          | none => f.fn a
      support := f.support
      support_exact := by
        intro a
        obtain ⟨h1, h2⟩ := h
        specialize h2 a

    }
  else
    none

theorem FinFun.mapBin_dom [DecidableEq α] (f g : α ⇀ β)
    (op : Option β → Option β → Option β) (h : FinFun.mapBin f g op = some fg) :
    fg.dom = f.dom ∧ fg.dom = g.dom := by grind [mapBin]

theorem FinFun.mapBin_char₁ [DecidableEq α] (f g : α ⇀ β)
    (op : Option β → Option β → Option β) (h : FinFun.mapBin f g op = some fg) :
    ∀ x ∈ fg.dom, fg.apply x = y ↔ (op (some (f.f x)) (some (g.f x))) = some y := by
  intro x hxdom
  constructor
  <;> simp only [mapBin, Option.ite_none_right_eq_some] at h
  <;> rcases h with ⟨_, _, _, _⟩
  <;> grind

theorem FinFun.mapBin_char₂ [DecidableEq α] (f g : α ⇀ β)
    (op : Option β → Option β → Option β) (hdom : f.dom = g.dom)
    (hop : ∀ x ∈ f.dom, (op (some (f.f x)) (some (g.f x))).isSome)
    : (FinFun.mapBin f g op).isSome := by grind [mapBin]

-/

/-- Two `FinFun`s are equal if their internal functions and supports are equal. -/
theorem eq_char [DecidableEq α] [Zero β] {f g : α →₀ β} :
  f = g ↔ f.fn = g.fn ∧ f.support = g.support := by
  apply Iff.intro <;> intro h
  · grind
  · obtain ⟨h1, h2⟩ := h
    apply DFunLike.ext
    intro x
    rw [coe_fn]
    rw [coe_fn]
    rw [h1]

end FinFun
