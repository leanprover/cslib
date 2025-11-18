/-
Copyright (c) 2025 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi, Xueying Qin
-/

import Cslib.Init
import Mathlib.Data.Finset.Filter
import Mathlib.Data.Finset.Lattice.Basic

/-! # Finite functions

Given types `α` and `β`, and assuming that `β` has a `Zero` element,
a `FinFun α β` is a function from `α` to `β` where only a finite number of elements
in `α` are mapped to non-zero elements.
-/

namespace Cslib

/-- A `FinFun` is a function `fn` with a finite `support`.

This is similar to `Finsupp` in Mathlib, but definitions are computable. -/
structure FinFun (α : Type _) (β : Type _) [Zero β] where
  /-- The underlying function. -/
  fn : α → β
  /-- The finite support of the function. -/
  support : Finset α
  /-- Proof that `support` is the support of the underlying function. -/
  mem_support_fn {a : α} : a ∈ support ↔ fn a ≠ 0

attribute [scoped grind _=_] FinFun.mem_support_fn

namespace FinFun

@[inherit_doc]
scoped infixr:25 " →₀ " => FinFun

/-- Constructs a `FinFun` by restricting a function to a given support, filtering out all elements
not mapped to 0 in the support. -/
@[scoped grind .]
private def fromFun {α β : Type _} [Zero β] [DecidableEq α]
  [∀ y : β, Decidable (y = 0)] (fn : α → β) (support : Finset α) : α →₀ β where
  fn := (fun a => if a ∈ support then fn a else 0)
  support := support.filter (fn · ≠ 0)
  mem_support_fn := by grind

@[inherit_doc]
scoped notation f:25 "↾₀" support:51 => FinFun.fromFun f support

instance instFunLike [Zero β] : FunLike (α →₀ β) α β where
  coe f := f.fn
  coe_injective' := by
    rintro ⟨_, _⟩ ⟨_, _⟩
    simp_all [Finset.ext_iff]

@[scoped grind =]
theorem coe_fn [Zero β] {f : α →₀ β} : (f : α → β) = f.fn := by simp [DFunLike.coe]

@[scoped grind =]
theorem coe_eq_fn [Zero β] {f : α →₀ β} : f a = f.fn a := by
  simp [DFunLike.coe]

/-- Extensional equality for `FinFun`. -/
@[scoped grind ←=]
theorem ext [Zero β] {f g : α →₀ β} (h : ∀ (a : α), f a = g a) : f = g :=
  DFunLike.ext (f := f) (g := g) h

@[scoped grind _=_]
theorem mem_support_not_zero [Zero β] {f : α →₀ β} : a ∈ f.support ↔ f a ≠ 0 := by
  grind

@[scoped grind _=_]
theorem not_mem_support_zero [Zero β] {f : α →₀ β} : a ∉ f.support ↔ f a = 0 := by
  grind

/-- If two `FinFun`s are equal, their underlying functions and supports are equal. -/
@[scoped grind .]
theorem eq_fields_eq [Zero β] {f g : α →₀ β} : f = g → f.fn = g.fn ∧ f.support = g.support :=
  by grind

/-- If two functions are equal, two `FinFun`s respectively using them as underlying functions
are equal. -/
@[scoped grind .]
theorem fn_eq_eq [Zero β] {f g : α →₀ β} (h : f.fn = g.fn) : f = g :=
  ext (congrFun h)

@[scoped grind =>]
theorem congrFinFun [Zero β] {f g : α →₀ β} (h : f = g) (a : α) : f a = g a := 
  by grind

@[scoped grind =]
theorem fromFun_eq [Zero β] [DecidableEq α] [∀ y : β, Decidable (y = 0)]
    (f : α → β) (support : Finset α) (h : ∀ a, a ∉ support → f a = 0) :
    (f ↾₀ support) = f := by grind

@[scoped grind =]
theorem fromFun_fn [Zero β] [DecidableEq α] [∀ y : β, Decidable (y = 0)]
    (f : α → β) (support : Finset α) :
    (f ↾₀ support).fn = (fun a => if a ∈ support then f a else 0) := by
  grind

@[scoped grind =]
theorem fromFun_support [Zero β] [DecidableEq α] [∀ y : β, Decidable (y = 0)]
    (f : α → β) (support : Finset α) :
    (f ↾₀ support).support = support.filter (f · ≠ 0) := by
  grind

/-- Restricting a function twice to the same support is idempotent. -/
@[scoped grind =]
theorem fromFun_idem [Zero β] [DecidableEq α]
    [∀ y : β, Decidable (y = 0)] {f : α → β} {support : Finset α} :
    (f ↾₀ support) ↾₀ support = f ↾₀ support := by grind

/-- Restricting a `FinFun` to its own support is the identity. -/
@[scoped grind =]
theorem coe_fromFun_id [Zero β] [DecidableEq α] [∀ y : β, Decidable (y = 0)] {f : α →₀ β} :
    (f ↾₀ f.support) = f := by grind

/-- Restricting a function twice to two supports is equal to restricting to their intersection. -/
@[scoped grind =]
theorem fromFun_inter [Zero β] [DecidableEq α]
    [∀ y : β, Decidable (y = 0)] {f : α → β} {support1 support2 : Finset α} :
    (f ↾₀ support1) ↾₀ support2 = f ↾₀ (support1 ∩ support2) := by grind

/-- Restricting a function is commutative. -/
@[scoped grind =]
theorem fromFun_comm [Zero β] [DecidableEq α]
    [∀ y : β, Decidable (y = 0)] {f : α → β} {support1 support2 : Finset α} :
    (f ↾₀ support1) ↾₀ support2 = (f ↾₀ support2) ↾₀ support1 := by grind

end FinFun

end Cslib
