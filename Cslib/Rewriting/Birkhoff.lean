/-
Copyright (c) 2025 Cody Roux, Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Mathlib.ModelTheory.Basic
public import Mathlib.ModelTheory.Syntax
public import Cslib.Foundations.Data.Relation
public import Cslib.Init

@[expose] public section

namespace Cslib

open FirstOrder Language Term

universe u v u'

variable (L : Language.{u, v}) {α : Type u'}

inductive Derives (Γ : Term L α → Term L α → Prop) : Term L α → Term L α → Prop
| ax : Γ t₁ t₂ → Derives Γ t₁ t₂
| subst (σ : α → Term L α) : Γ t₁ t₂ → Derives Γ (t₁.subst σ) (t₂.subst σ)
| congr (f : L.Functions n) (ts₁ ts₂ : Fin n → Term L α) :
    (∀ m, Γ (ts₁ m) (ts₂ m)) → Derives Γ (func f ts₁) (func f ts₂)

notation:50 Γ " ⊢ " t₁ " ≅ " t₂:arg => Relation.EqvGen Derives Γ t₁ t₂

end Cslib
