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
  rename_i hdec hzero
  have happlyx : f.toFun x = g.toFun x := by simp [h]
  constructorm* _ ∧ _
  case left =>
    intro hx
    simp only [FinFun.apply]
    simp only [Finset.mem_inter] at hx
    simp [toFun, hx] at happlyx
    exact happlyx
  case right.left =>
    intro hx
    simp only [Finset.mem_sdiff] at hx
    simp [toFun, hx] at happlyx
    exact happlyx
  case right.right =>
    intro hx
    simp only [Finset.mem_sdiff] at hx
    simp [toFun, hx] at happlyx
    simp only [happlyx]

theorem FinFun.toFun_dom [DecidableEq α] [Zero β] {f : α ⇀ β}
    (h : ∀ x, x ∉ f.dom → f.apply x = Zero.zero) : (f : α → β) = f.f := by
  rename_i hdec hzero
  funext x
  by_cases hx : x ∈ f.dom
  · simp only [FinFun.toFun]
    simp [hx]
  · simp only [FinFun.toFun]
    simp [hx]
    specialize h x
    simp only [h hx]

-- /- A function with a finite domain of definition is a FinFun. -/
-- @[simp]
-- def FinFun.mk [Zero β] (f : α → β) (dom : Finset α) (h : ∀ x, x ∉ dom → f ) : α ⇀ β := {
--   f := f
--   dom := dom
-- }

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
    fg.dom = f.dom ∧ fg.dom = g.dom := by
  rename_i hdec
  simp [mapBin] at h
  constructor
  · simp only [← h]
  · simp only [← h]

theorem FinFun.mapBin_char₁ [DecidableEq α] (f g : α ⇀ β)
    (op : Option β → Option β → Option β) (h : FinFun.mapBin f g op = some fg) :
    ∀ x ∈ fg.dom, fg.apply x = y ↔ (op (some (f.f x)) (some (g.f x))) = some y := by
  rename_i hdec
  intro x hxdom
  constructor
  · intro happ
    simp only [FinFun.apply] at happ
    simp [mapBin] at h
    rcases h with ⟨⟨ h_fg_dom_eq, hxsome ⟩, ⟨fgf, what⟩⟩
    specialize hxsome x hxdom
    simp at happ
    match hsome? : op (some (f.f x)) (some (g.f x)) with
    | some z =>
      simp [hsome?] at happ
      simp only [happ]
    | none =>
      simp [hsome?] at hxsome
  · intro hop
    simp [mapBin] at h
    rcases h with ⟨⟨ h_fg_dom_eq, hxsome ⟩, ⟨fgf, what⟩⟩
    simp
    simp [hop]

theorem FinFun.mapBin_char₂ [DecidableEq α] (f g : α ⇀ β)
    (op : Option β → Option β → Option β) (hdom : f.dom = g.dom)
    (hop : ∀ x ∈ f.dom, (op (some (f.f x)) (some (g.f x))).isSome)
    : (FinFun.mapBin f g op).isSome := by
  rename_i hdec
  simp [mapBin]
  simp [hdom]
  rw [← hdom]
  intro x
  intro hxdom
  specialize hop x hxdom
  simp [hop]

-- Fun to FinFun
def Function.toFinFun [DecidableEq α] (f : α → β) (dom : Finset α) : α ⇀ β := FinFun.mk f dom

lemma Function.toFinFun_eq [DecidableEq α] [Zero β] (f : α → β) (dom : Finset α)
    (h : ∀ x, x ∉ dom → f x = 0) : f = (Function.toFinFun f dom) := by
  funext p
  by_cases hp : p ∈ dom
  · simp [Function.toFinFun, FinFun.toFun]
    simp [hp]
  · simp [Function.toFinFun, FinFun.toFun]
    simp [hp]
    specialize h p hp
    exact h

@[coe] def FinFun.toDomFun (f : α ⇀ β) : {x // x ∈ f.dom} → β :=
  fun x => f.f x

theorem FinFun.toDomFun_char (f : α ⇀ β) (h : x ∈ f.dom) : f.toDomFun ⟨ x, h ⟩ = f.f x := by
  simp [FinFun.toDomFun]

theorem FinFun.congrFinFun [DecidableEq α] [Zero β] {f g : α ⇀ β} (h : f = g) (a : α) : 
    f.apply a = g.apply a := by
  simp [FinFun.apply]
  cases f
  rename_i ff fdom
  cases g
  rename_i gf gdom
  simp at h
  obtain ⟨ h1, h2⟩ := h
  exact congrFun h1 a

theorem FinFun.eq_char₁ [DecidableEq α] [Zero β] {f g : α ⇀ β} (h : f = g) : 
    f.f = g.f ∧ f.dom = g.dom := by
  cases f
  rename_i ff fdom
  cases g
  rename_i gf gdom
  simp at h
  assumption

theorem FinFun.eq_char₂ [DecidableEq α] [Zero β] {f g : α ⇀ β} (heq : f.f = g.f ∧ f.dom = g.dom) : 
    f = g := by
  cases f
  rename_i ff fdom
  cases g
  rename_i gf gdom
  simp at heq
  simp
  assumption

theorem FinFun.eq_char [DecidableEq α] [Zero β] {f g : α ⇀ β} : 
    f = g ↔ f.f = g.f ∧ f.dom = g.dom := by
  apply Iff.intro
  · apply FinFun.eq_char₁
  · apply FinFun.eq_char₂
