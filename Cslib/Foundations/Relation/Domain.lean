/-
Copyright (c) 2025 Fabrizio Montesi and Thomas Waring. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi, Thomas Waring, Chris Henson
-/

module

public import Cslib.Foundations.Relation.Defs
public import Mathlib.Data.Set.Basic

/-! # Relations: Domain and Codomain

This module proves basic properties of the domain and codomain of relations.

## References

* [*Simple Laws about Nonprominent Properties of Binary Relations*][Burghardt2018]

-/

@[expose] public section

namespace Relation

@[simp, grind =]
theorem emptyHRelation_emptyRelation : (emptyHRelation : α → α → Prop) = emptyRelation := rfl

@[simp, grind =]
theorem emptyHrelation_apply (a : α) (b : β) : emptyHRelation a b ↔ False := .rfl

variable {β : Type*} {r : α → β → Prop}

@[simp, grind =] lemma mem_dom : a ∈ dom r ↔ ∃ b, r a b := .rfl
@[simp, grind =] lemma mem_cod : b ∈ cod r ↔ ∃ a, r a b := .rfl

@[gcongr] lemma dom_mono (h : r₁ ≤ r₂) : dom r₁ ⊆ dom r₂ := fun a ⟨b, hab⟩ => ⟨b, h a b hab⟩
@[gcongr] lemma cod_mono (h : r₁ ≤ r₂) : cod r₁ ⊆ cod r₂ := fun b ⟨a, hab⟩ => ⟨a, h a b hab⟩

@[simp, grind =]
lemma dom_empty : dom (emptyHRelation : α → β → Prop) = ∅ := by grind

@[simp, grind =]
lemma cod_empty : cod (emptyHRelation : α → β → Prop) = ∅ := by grind

@[simp, grind =]
lemma dom_eq_empty_iff : dom r = ∅ ↔ r = emptyHRelation where
  mp h := by
    ext a b
    simp
    grind => have : a ∈ dom r; finish
  mpr := by grind

@[simp, grind =]
lemma cod_eq_empty_iff : cod r = ∅ ↔ r = emptyHRelation where
  mp h := by
    ext a b
    simp
    grind => have : b ∈ cod r; finish
  mpr h := by grind

@[simp]
lemma cod_inv : cod (fun a b => r b a) = dom r := rfl

@[simp]
lemma dom_inv : dom (fun a b => r b a) = cod r := rfl

theorem _root_.Std.Trichotomous.subsingleton_cod (r : α → α → Prop) [Std.Trichotomous r] :
    Subsingleton ((cod r)ᶜ : Set α) := by
  constructor
  rintro ⟨b₁, _⟩ ⟨b₂, _⟩
  have := @Std.Trichotomous.rel_or_eq_or_rel_swap _ r _ b₁ b₂
  grind

theorem _root_.Std.Trichotomous.subsingleton_dom (r : α → α → Prop) [Std.Trichotomous r] :
    Subsingleton ((dom r)ᶜ : Set α) := by
  constructor
  rintro ⟨a₁, _⟩ ⟨a₂, _⟩
  have := @Std.Trichotomous.rel_or_eq_or_rel_swap _ r _ a₁ a₂
  grind

end Relation
