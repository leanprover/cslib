/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.Relation.Defs
public import Cslib.Foundations.Relation.Domain

/-! # Relations: Properties on set restrictions

## References

* [*Simple Laws about Nonprominent Properties of Binary Relations*][Burghardt2018]

-/

@[expose] public section

namespace Relation

variable (r : α → α → Prop) (s : Set α)

@[simp, grind .]
theorem refl_iff_reflOn : Std.Refl (α := s) r ↔ ReflOn r s := by
  constructor
  · exact fun ⟨h⟩ a ha ↦ h ⟨a, ha⟩
  · exact fun h ↦ ⟨fun ⟨a, ha⟩ ↦ h a ha⟩

@[simp, grind .]
theorem symm_iff_symmOn : Std.Symm (α := s) r ↔ SymmOn r s := by
  constructor
  · exact fun ⟨h⟩ a ha b hb ab ↦ h ⟨a, ha⟩ ⟨b, hb⟩ ab
  · exact fun h ↦ ⟨fun ⟨a, ha⟩ ⟨b, hb⟩ ab ↦ h a ha b hb ab⟩

-- for special cases of (co)domain, we provide constructive shortcut lemmas

theorem ReflOn.of_dom {r} : ReflOn r (dom r) → r a b → r a a
| h, hab => h a (dom_of hab)

theorem ReflOn.of_cod {r} : ReflOn r (cod r) → r a b → r b b
| h, hab => h b (cod_of hab)

theorem SymmOn.of_dom {r} : SymmOn r (dom r) → r a b → r b c → r b a
| h, hab, hbc => h a (dom_of hab) b (dom_of hbc) hab

theorem SymmOn.of_cod {r} : SymmOn r (cod r) → r a b → r c a → r b a
| h, hab, hca => h a (cod_of hca) b (cod_of hab) hab

end Relation
