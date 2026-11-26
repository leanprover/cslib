/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.Relation.Domain

/-! # Relations: Properties on set restrictions

## References

* [*Simple Laws about Nonprominent Properties of Binary Relations*][Burghardt2018]

-/

@[expose] public section

open Relation

namespace Set

variable (r : α → α → Prop) (s : Set α)

@[simp, grind .]
theorem refl_iff_reflOn : Std.Refl (α := s) r ↔ s.ReflOn r := by
  constructor
  · exact fun ⟨h⟩ a ha ↦ h ⟨a, ha⟩
  · exact fun h ↦ ⟨fun ⟨a, ha⟩ ↦ h a ha⟩

@[simp, grind .]
theorem symm_iff_symmOn : Std.Symm (α := s) r ↔ s.SymmOn r := by
  constructor
  · exact fun ⟨h⟩ a ha b hb ab ↦ h ⟨a, ha⟩ ⟨b, hb⟩ ab
  · exact fun h ↦ ⟨fun ⟨a, ha⟩ ⟨b, hb⟩ ab ↦ h a ha b hb ab⟩

-- for special cases of (co)domain, we provide constructive shortcut lemmas

theorem ReflOn.of_dom {r} : (dom r).ReflOn r → r a b → r a a
| h, hab => h a (Relation.of_dom hab)

theorem ReflOn.of_cod {r} : (cod r).ReflOn r → r a b → r b b
| h, hab => h b (Relation.of_cod hab)

theorem SymmOn.of_dom {r} : (dom r).SymmOn r → r a b → r b c → r b a
| h, hab, hbc => h a (Relation.of_dom hab) b (Relation.of_dom hbc) hab

theorem SymmOn.of_cod {r} : (cod r).SymmOn r → r a b → r c a → r b a
| h, hab, hca => h a (Relation.of_cod hca) b (Relation.of_cod hab) hab

variable {r} in
lemma _root_.Relation.rfl_of_rel [Std.Symm r] [IsTrans α r] (h : r x y) : r x x :=
    _root_.trans h (symm h)

lemma leftQuasiRefl_of_per [Std.Symm r] [IsTrans α r] : Set.LeftQuasiRefl r :=
  fun _ ⟨_, h⟩ ↦ rfl_of_rel h

lemma rightQuasiRefl_of_per [Std.Symm r] [IsTrans α r] : Set.RightQuasiRefl r :=
  fun _ ⟨_, h⟩ ↦ rfl_of_rel (symm h)

end Set

namespace Relation

variable {α : Type*} {r : α → α → Prop} {s : Set α} {x x' y y' : α}

instance [Std.Refl r] (s : Set α) : Std.Refl (α := s) r where
  refl a := refl (a : α)

instance [Std.Symm r] (s : Set α) : Std.Symm (α := s) r where
  symm _ _ h := symm (α := α) h

instance [Std.Symm r] [IsTrans α r] : Std.Refl (α := dom r) r where
  refl := fun ⟨_, _, h⟩ ↦ rfl_of_rel h

instance [IsTrans α r] (s : Set α) : IsTrans s r where
  trans _ _ _ h h' := _root_.trans (α := α) h h'

instance [Std.Symm r] [IsTrans α r] : IsEquiv (α := dom r) r where

instance [Std.Symm r] [IsTrans α r] : Std.Refl (α := cod r) r where
  refl := fun ⟨_, _, h⟩ ↦ rfl_of_rel (symm h)

instance [Std.Symm r] [IsTrans α r] : IsEquiv (α := cod r) r where

lemma dom_restrict_of_cod_subset (h : cod r ⊆ s) :
    dom (r : s → s → Prop) = Subtype.val ⁻¹' dom r := by
  ext ⟨x, hx⟩
  grind

lemma cod_restrict_of_dom_subset (h : dom r ⊆ s) :
    cod (r : s → s → Prop) = Subtype.val ⁻¹' cod r := by
  ext ⟨x, hx⟩
  grind

end Relation
