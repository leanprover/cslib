/-
Copyright (c) 2025 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi, Xueying Qin
-/

import Mathlib.Data.Finset.Basic

/-! # Finite Functions

*Note:* the API and notation of `FinFun` is still unstable.

A `FinFun α β` is a function from `α` to `β` with a finite domain of definition.
-/

namespace Cslib

/-- A finite function FinFun is a function `f` equipped with a domain of definition `dom`. -/
structure FinFun (α : Type u) (β : Type v) where
  f : α → β
  dom : Finset α

notation:50 α " ⇀ " β => FinFun α β
notation:50 f "↾" dom => FinFun.mk f dom

abbrev CompleteDom [Zero β] (f : α ⇀ β) := ∀ x, x ∉ f.dom → f.f x = 0

def FinFun.defined (f : α ⇀ β) (x : α) : Prop := x ∈ f.dom

@[simp]
abbrev FinFun.apply (f : α ⇀ β) (x : α) : β := f.f x

/- Conversion from FinFun to a function. -/
@[coe] def FinFun.toFun [DecidableEq α] [Zero β] (f : α ⇀ β) : (α → β) :=
  fun x => if x ∈ f.dom then f.f x else Zero.zero

instance [DecidableEq α] [Zero β] : Coe (α ⇀ β) (α → β) where
  coe := FinFun.toFun

theorem FinFun.toFun_char [DecidableEq α] [Zero β]
    {f g : α ⇀ β} (h : (f : α → β) = (g : α → β)) (x) :
    (x ∈ (f.dom ∩ g.dom) →
    f.apply x = g.apply x) ∧ (x ∈ (f.dom \ g.dom) →
    f.apply x = Zero.zero) ∧ (x ∈ (g.dom \ f.dom) → g.apply x = Zero.zero) := by
  have happlyx : f.toFun x = g.toFun x := by simp [h]
  grind [FinFun.toFun]

theorem FinFun.toFun_dom [DecidableEq α] [Zero β] {f : α ⇀ β}
    (h : ∀ x, x ∉ f.dom → f.apply x = Zero.zero) : (f : α → β) = f.f := by
  grind [FinFun.toFun]

def FinFun.mapBin [DecidableEq α] (f g : α ⇀ β) (op : Option β → Option β → Option β) :
    Option (α ⇀ β) :=
  if f.dom = g.dom ∧ ∀ x ∈ f.dom, (op (some (f.f x)) (some (g.f x))).isSome then
    some {
      f := fun x =>
        match op (some (f.f x)) (some (g.f x)) with
          | some y => y
          | none => f.f x
      dom := f.dom
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

-- Fun to FinFun
def Function.toFinFun [DecidableEq α] (f : α → β) (dom : Finset α) : α ⇀ β := FinFun.mk f dom

lemma Function.toFinFun_eq [DecidableEq α] [Zero β] (f : α → β) (dom : Finset α)
    (h : ∀ x, x ∉ dom → f x = 0) : f = (Function.toFinFun f dom) := by
  funext p
  by_cases hp : p ∈ dom <;> simp only [toFinFun, FinFun.toFun, hp, reduceIte]
  exact h p hp

@[coe] def FinFun.toDomFun (f : α ⇀ β) : {x // x ∈ f.dom} → β :=
  fun x => f.f x

theorem FinFun.toDomFun_char (f : α ⇀ β) (h : x ∈ f.dom) : f.toDomFun ⟨ x, h ⟩ = f.f x := by
  simp [FinFun.toDomFun]

theorem FinFun.congrFinFun [DecidableEq α] [Zero β] {f g : α ⇀ β} (h : f = g) (a : α) :
    f.apply a = g.apply a := congrFun (congrArg apply h) a

theorem FinFun.eq_char₁ [DecidableEq α] [Zero β] {f g : α ⇀ β} (h : f = g) :
    f.f = g.f ∧ f.dom = g.dom := ⟨congrArg FinFun.f h, congrArg dom h⟩

theorem FinFun.eq_char₂ [DecidableEq α] [Zero β] {f g : α ⇀ β} (heq : f.f = g.f ∧ f.dom = g.dom) :
    f = g := by
  cases f
  cases g
  grind

theorem FinFun.eq_char [DecidableEq α] [Zero β] {f g : α ⇀ β} :
    f = g ↔ f.f = g.f ∧ f.dom = g.dom := by grind [FinFun.eq_char₁, FinFun.eq_char₂]

end Cslib
